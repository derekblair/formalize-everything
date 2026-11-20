#!/usr/bin/env python3
"""Persistent, single-document Lean LSP checking; Python standard library only.

Run from any directory (no Lean process starts until the first `check` command):
  python3 work/lean_lsp_driver.py --project /absolute/lean/project \
    --source /absolute/work/Combined.lean --evidence /absolute/evidence

Interactive stdin accepts JSON objects, one per line:
  {"cmd":"check", "label":"combined-01"}
  {"cmd":"check", "label":"combined-02", "line_map":"/absolute/map.json"}
  {"cmd":"status"}
  {"cmd":"quit"}
`check`, `status`, and `quit` are also accepted as bare lines. `check` can override
`path` before the first check. Later checks must use the same resolved path and
unchanged module/prelude/import declarations. Checks are serialized. A positive
`timeout` sets seconds for that request; the default 0 waits without a deadline.

The process cwd is --project. `lake env` supplies the pinned Lean environment.
Optional repeated --lean-path directories are prepended AFTER `lake env` has set
LEAN_PATH, by a tiny Python exec wrapper. The server runs with -j1, forwarded by
Lean to its one file worker. didOpen uses dependencyBuildMode="never", which in
Lean4.34.1 invokes lake setup-file with --no-build --no-cache. The driver does not
install, build dependencies, remove files, or create .olean output.

Keep a fixed union-of-imports header in the generated source. Each check sends the
complete document text (didOpen once, didChange afterward); Lean reuses the
unchanged import/header snapshot and unchanged command prefix. A barrier request
textDocument/waitForDiagnostics synchronizes each version. The LSP result is
development evidence only: a successful final CLI clean build is still required.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import subprocess
import sys
import threading
import time
from typing import Any, BinaryIO


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def emit(event: str, **values: Any) -> None:
    print(json.dumps({"event": event, **values}, ensure_ascii=False), flush=True)


def encode_message(message: dict[str, Any]) -> bytes:
    body = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body


def read_message(stream: BinaryIO) -> dict[str, Any]:
    headers: dict[bytes, bytes] = {}
    while True:
        line = stream.readline()
        if not line:
            raise EOFError("Lean LSP stdout closed")
        if line in (b"\r\n", b"\n"):
            break
        key, sep, value = line.partition(b":")
        if not sep:
            raise ValueError(f"Invalid LSP header: {line!r}")
        headers[key.strip().lower()] = value.strip()
    size = int(headers[b"content-length"])
    if not 0 <= size <= 256 * 1024 * 1024:
        raise ValueError(f"Unexpected LSP frame size: {size}")
    chunks: list[bytes] = []
    remaining = size
    while remaining:
        chunk = stream.read(remaining)
        if not chunk:
            raise EOFError("Lean LSP stdout closed inside a message")
        chunks.append(chunk)
        remaining -= len(chunk)
    result = json.loads(b"".join(chunks))
    if not isinstance(result, dict):
        raise ValueError("LSP message is not an object")
    return result


def import_signature(text: str) -> list[str]:
    """Conservative guard for the generated file's fixed import declarations.

    The coordinator generates one-line imports. We remove comments (including
    nested block comments) before examining lines, so component documentation
    containing the word `import` cannot spuriously become a dependency.
    """
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                break
            out.append("\n")
            i = end + 1
        else:
            out.append(text[i])
            i += 1
    declarations: list[str] = []
    for line in "".join(out).splitlines():
        line = " ".join(line.split())
        if not line:
            continue
        if re.fullmatch(r"(?:module|prelude)", line) or re.match(
            r"(?:(?:public|private) )?import ", line
        ):
            declarations.append(line)
        else:
            break
    return declarations


class LeanSession:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.project = args.project.resolve()
        self.evidence = args.evidence.resolve()
        self.evidence.mkdir(parents=True, exist_ok=True)
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        self.session_id = f"lean-lsp-{stamp}-{os.getpid()}"
        self.proc: subprocess.Popen[bytes] | None = None
        self.stderr_file: BinaryIO | None = None
        self.raw_file = None
        self.log_lock = threading.Lock()
        self.incoming: queue.Queue[dict[str, Any] | BaseException] = queue.Queue()
        self.next_id = 1
        self.source: Path | None = None
        self.uri: str | None = None
        self.signature: list[str] | None = None
        self.version = 0
        self.diagnostics: dict[tuple[str, int | None], list[dict[str, Any]]] = {}
        self.last_summary: dict[str, Any] | None = None

    def _log(self, direction: str, message: dict[str, Any]) -> None:
        if self.raw_file is None:
            return
        with self.log_lock:
            self.raw_file.write(json.dumps(
                {"time": utc_now(), "direction": direction, "message": message},
                ensure_ascii=False,
            ) + "\n")
            self.raw_file.flush()

    def _read_loop(self) -> None:
        assert self.proc is not None and self.proc.stdout is not None
        try:
            while True:
                message = read_message(self.proc.stdout)
                self._log("from_server", message)
                self.incoming.put(message)
        except BaseException as exc:
            self.incoming.put(exc)

    def send(self, method: str, params: Any = None, *, request: bool = False) -> int | None:
        assert self.proc is not None and self.proc.stdin is not None
        message: dict[str, Any] = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            message["params"] = params
        req_id = None
        if request:
            req_id = self.next_id
            self.next_id += 1
            message["id"] = req_id
        self._log("to_server", message)
        self.proc.stdin.write(encode_message(message))
        self.proc.stdin.flush()
        return req_id

    def _consume(self, message: dict[str, Any]) -> None:
        if "method" in message and "id" in message:
            # Lean requests refreshes even for a client that does not display
            # these views. Acknowledge them to avoid needless retry traffic.
            if message["method"] in {
                "workspace/semanticTokens/refresh", "workspace/inlayHint/refresh",
                "workspace/codeLens/refresh", "workspace/diagnostic/refresh",
            }:
                reply = {"jsonrpc": "2.0", "id": message["id"], "result": None}
            else:
                reply = {"jsonrpc": "2.0", "id": message["id"], "error": {
                    "code": -32601, "message": "Optional client method not implemented"}}
            assert self.proc is not None and self.proc.stdin is not None
            self._log("to_server", reply)
            self.proc.stdin.write(encode_message(reply))
            self.proc.stdin.flush()
        if message.get("method") == "textDocument/publishDiagnostics":
            p = message["params"]
            key = (p["uri"], p.get("version"))
            previous = self.diagnostics.get(key, []) if p.get("isIncremental", False) else []
            self.diagnostics[key] = previous + p.get("diagnostics", [])

    def wait_response(self, request_id: int, timeout: float = 0) -> Any:
        started = time.monotonic()
        last_progress = started
        while True:
            elapsed = time.monotonic() - started
            if timeout > 0 and elapsed >= timeout:
                self.send("$/cancelRequest", {"id": request_id})
                raise TimeoutError(f"LSP request {request_id} exceeded {timeout}s")
            wait = min(1.0, timeout - elapsed) if timeout > 0 else 1.0
            try:
                message = self.incoming.get(timeout=max(wait, 0.001))
            except queue.Empty:
                if time.monotonic() - last_progress >= 30:
                    emit("waiting", request_id=request_id, version=self.version,
                         elapsed_seconds=round(elapsed, 1), server_pid=self.proc.pid if self.proc else None)
                    last_progress = time.monotonic()
                continue
            if isinstance(message, BaseException):
                raise RuntimeError(f"LSP reader failed: {message}") from message
            self._consume(message)
            if message.get("id") == request_id and "method" not in message:
                if "error" in message:
                    raise RuntimeError(f"LSP request {request_id}: {message['error']}")
                return message.get("result")

    def start(self) -> None:
        if self.proc is not None:
            return
        bootstrap = (
            "import json,os,sys; e=os.environ.copy(); p=json.loads(sys.argv[1]); "
            "e['LEAN_PATH']=os.pathsep.join(p+([e['LEAN_PATH']] if e.get('LEAN_PATH') else [])); "
            "os.execvpe('lean',['lean','--server','-j1'],e)"
        )
        command = ["lake", "env", sys.executable, "-c", bootstrap,
                   json.dumps([str(p.resolve()) for p in self.args.lean_path])]
        self.raw_file = (self.evidence / f"{self.session_id}.protocol.jsonl").open("x", encoding="utf-8")
        self.stderr_file = (self.evidence / f"{self.session_id}.stderr.log").open("xb")
        self.proc = subprocess.Popen(command, cwd=self.project, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=self.stderr_file, start_new_session=True)
        threading.Thread(target=self._read_loop, daemon=True).start()
        request_id = self.send("initialize", {
            "processId": os.getpid(),
            "clientInfo": {"name": "stdlib-lean-checker", "version": "1"},
            "rootUri": self.project.as_uri(),
            "capabilities": {"lean": {
                "incrementalDiagnosticSupport": False, "silentDiagnosticSupport": True}},
            "initializationOptions": {"hasWidgets": False},
        }, request=True)
        assert request_id is not None
        self.wait_response(request_id, self.args.initialize_timeout)
        self.send("initialized", {})
        emit("server_started", server_pid=self.proc.pid, session=self.session_id,
             project=str(self.project), dependency_build_mode="never", threads=1)

    def check(self, command: dict[str, Any]) -> dict[str, Any]:
        path_value = command.get("path") or self.args.source
        if path_value is None:
            raise ValueError("A source path is required (--source or check.path)")
        source = Path(path_value).resolve(strict=True)
        raw = source.read_bytes()
        text = raw.decode("utf-8")
        signature = import_signature(text)
        if self.source is not None and source != self.source:
            raise ValueError("A session opens exactly one resolved source path; restart for a new path")
        if self.signature is not None and signature != self.signature:
            raise ValueError("Import/module/prelude header changed; preserve the fixed union header or restart")
        label = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(command.get("label", "check")))
        new_version = self.version + 1
        prefix = self.evidence / f"{self.session_id}.v{new_version:04d}.{label}"
        snapshot = Path(f"{prefix}.lean")
        with snapshot.open("xb") as out:
            out.write(raw)
        source_hash = hashlib.sha256(raw).hexdigest()
        summary: dict[str, Any] = {
            "session": self.session_id, "version": new_version, "source": str(source),
            "source_snapshot": str(snapshot), "source_sha256": source_hash,
            "import_signature": signature,
            "import_sha256": hashlib.sha256("\n".join(signature).encode()).hexdigest(),
            "started_utc": utc_now(), "project": str(self.project), "label": label,
            "completion_barrier": False, "status": "incomplete",
            "validation_kind": "Lean LSP development check; not a CLI clean build",
        }
        line_map = command.get("line_map")
        if line_map:
            map_data = Path(line_map).resolve(strict=True).read_bytes()
            map_snapshot = Path(f"{prefix}.line-map.json")
            with map_snapshot.open("xb") as out:
                out.write(map_data)
            summary["line_map_snapshot"] = str(map_snapshot)
            summary["line_map_sha256"] = hashlib.sha256(map_data).hexdigest()
        started = time.monotonic()
        try:
            self.start()
            self.source, self.signature, self.uri = source, signature, source.as_uri()
            first = self.version == 0
            self.version = new_version
            if first:
                self.send("textDocument/didOpen", {
                    "textDocument": {"uri": self.uri, "languageId": "lean4",
                                     "version": self.version, "text": text},
                    "dependencyBuildMode": "never",
                })
            else:
                self.send("textDocument/didChange", {
                    "textDocument": {"uri": self.uri, "version": self.version},
                    "contentChanges": [{"text": text}],
                })
            request_id = self.send("textDocument/waitForDiagnostics", {
                "uri": self.uri, "version": self.version}, request=True)
            assert request_id is not None
            self.wait_response(request_id, float(command.get("timeout", self.args.timeout)))
            summary["completion_barrier"] = True
        except Exception as exc:
            summary["failure"] = f"{type(exc).__name__}: {exc}"
        finally:
            diagnostics = self.diagnostics.get((source.as_uri(), new_version), [])
            diagnostics_path = Path(f"{prefix}.diagnostics.json")
            diagnostics_path.write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            rendered: list[str] = []
            for d in diagnostics:
                pos = d.get("range", {}).get("start", {})
                severity = {1: "error", 2: "warning", 3: "info", 4: "hint"}.get(d.get("severity"), "diagnostic")
                rendered.append(f"{source}:{pos.get('line', 0)+1}:{pos.get('character', 0)+1}: {severity}: {d.get('message', '')}")
            Path(f"{prefix}.diagnostics.txt").write_text("\n\n".join(rendered) + "\n", encoding="utf-8")
            axiom_messages = [d.get("message", "") for d in diagnostics if
                              "depends on axioms:" in d.get("message", "") or
                              "does not depend on any axioms" in d.get("message", "")]
            Path(f"{prefix}.axioms.txt").write_text("\n".join(axiom_messages) + "\n", encoding="utf-8")
            summary.update({
                "finished_utc": utc_now(), "elapsed_seconds": round(time.monotonic() - started, 3),
                "server_pid": self.proc.pid if self.proc else None,
                "diagnostics_file": str(diagnostics_path),
                "errors": sum(d.get("severity") == 1 for d in diagnostics),
                "warnings": sum(d.get("severity") == 2 for d in diagnostics),
                "information": sum(d.get("severity") == 3 for d in diagnostics),
                "axiom_messages": len(axiom_messages),
                "sorry_axiom_reported": any("sorryAx" in m for m in axiom_messages),
            })
            if summary["completion_barrier"]:
                summary["status"] = "errors" if summary["errors"] else "checked"
            summary_path = Path(f"{prefix}.summary.json")
            summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            self.last_summary = summary
            emit("check_complete", summary_file=str(summary_path), **summary)
        return summary

    def close(self) -> None:
        if self.proc is None:
            return
        try:
            if self.proc.poll() is None:
                if self.uri:
                    self.send("textDocument/didClose", {"textDocument": {"uri": self.uri}})
                request_id = self.send("shutdown", request=True)
                assert request_id is not None
                self.wait_response(request_id, 20)
                self.send("exit")
                self.proc.wait(timeout=10)
        except Exception as exc:
            emit("shutdown_problem", message=str(exc), server_pid=self.proc.pid)
            # Never kill broad process groups. Only the process spawned by this driver.
            if self.proc.poll() is None:
                self.proc.terminate()
        finally:
            if self.stderr_file:
                self.stderr_file.close()
            if self.raw_file:
                with self.log_lock:
                    self.raw_file.close()
                    self.raw_file = None
            emit("closed", session=self.session_id, server_pid=self.proc.pid)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--lean-path", action="append", type=Path, default=[])
    parser.add_argument("--timeout", type=float, default=0)
    parser.add_argument("--initialize-timeout", type=float, default=300)
    args = parser.parse_args()
    if not args.project.is_dir():
        parser.error("--project must be an existing project directory")
    session = LeanSession(args)
    emit("ready", session=session.session_id, server_started=False,
         commands=["check", "status", "quit"])
    try:
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            try:
                command = json.loads(line) if line.startswith("{") else {"cmd": line}
                name = command.get("cmd")
                if name == "check":
                    session.check(command)
                elif name == "status":
                    emit("status", session=session.session_id, version=session.version,
                         server_pid=session.proc.pid if session.proc else None,
                         last_summary=session.last_summary)
                elif name in ("quit", "exit"):
                    break
                else:
                    raise ValueError(f"Unknown command: {name!r}")
            except Exception as exc:
                emit("command_error", error=f"{type(exc).__name__}: {exc}")
    except KeyboardInterrupt:
        emit("interrupted")
    finally:
        session.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
