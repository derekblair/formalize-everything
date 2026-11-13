#!/usr/bin/env python3
"""One-document persistent Lean LSP driver; Python standard library only.

Start only when the serialized Lean slot is released. The driver never builds
dependencies: didOpen explicitly requests dependencyBuildMode="never". It keeps
one document open and refuses header changes or overlapping versions. Completion
uses Lean's documented waitForDiagnostics barrier, exact-version diagnostics,
and exact-version fileProgress; an initial empty diagnostic is never completion.

Examples (paths should be absolute):
  python3 lean_lsp_driver.py start --book BOOK --file FILE --evidence NEW_DIR
  python3 lean_lsp_driver.py status --evidence NEW_DIR
  python3 lean_lsp_driver.py update --evidence NEW_DIR
  python3 lean_lsp_driver.py shutdown --evidence NEW_DIR

This is an incremental repair aid, not a substitute for lake build or the
clean-slate build and axiom-audit gates.
"""
import argparse
import asyncio
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import struct
import time


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def header_of(text):
    return re.findall(r"^(?:(?:public|meta)\s+)?import\s+.*$|^(?:module|prelude)\s*$", text, re.M)


class Driver:
    def __init__(self, book, target, evidence):
        self.book = book.resolve()
        self.target = target.resolve()
        self.target.relative_to(self.book)
        self.evidence = evidence.resolve()
        self.evidence.mkdir(parents=True, exist_ok=False)
        self.uri = self.target.as_uri()
        self.header = header_of(self.target.read_text())
        self.version = 0
        self.counter = 0
        self.waiters = {}
        self.pending = None
        self.proc = None
        self.stopping = asyncio.Event()
        self.send_lock = asyncio.Lock()
        self.raw_in = (self.evidence / "server.stdin.lsp").open("wb")
        self.raw_out = (self.evidence / "server.stdout.lsp").open("wb")
        self.stderr = (self.evidence / "server.stderr.log").open("wb")
        self.messages = (self.evidence / "messages.jsonl").open("w")
        self.state = {"status": "starting", "target": str(self.target), "uri": self.uri,
                      "book": str(self.book), "started": now(), "version": 0,
                      "dependencyBuildMode": "never", "command": ["lake", "serve", "--", "-j1"]}
        self.persist()

    def persist(self):
        (self.evidence / "status.json").write_text(json.dumps(self.state, indent=2) + "\n")

    def log(self, direction, message):
        self.messages.write(json.dumps({"at": now(), "direction": direction, "message": message},
                                      ensure_ascii=False) + "\n")
        self.messages.flush()

    async def send(self, message):
        body = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode()
        frame = f"Content-Length: {len(body)}\r\n\r\n".encode() + body
        async with self.send_lock:
            self.raw_in.write(frame)
            self.raw_in.flush()
            self.log("client", message)
            self.proc.stdin.write(frame)
            await self.proc.stdin.drain()

    async def notify(self, method, params):
        await self.send({"jsonrpc": "2.0", "method": method, "params": params})

    async def request(self, method, params):
        self.counter += 1
        ident = self.counter
        future = asyncio.get_running_loop().create_future()
        self.waiters[ident] = future
        await self.send({"jsonrpc": "2.0", "id": ident, "method": method, "params": params})
        return await future

    async def read_stdout(self):
        try:
            while True:
                headers = {}
                raw_header = b""
                while True:
                    line = await self.proc.stdout.readline()
                    if not line:
                        raise EOFError("Lean server stdout closed")
                    raw_header += line
                    if line in (b"\r\n", b"\n"):
                        break
                    key, value = line.decode("ascii").split(":", 1)
                    headers[key.lower()] = value.strip()
                body = await self.proc.stdout.readexactly(int(headers["content-length"]))
                self.raw_out.write(raw_header + body)
                self.raw_out.flush()
                message = json.loads(body)
                self.log("server", message)
                if "id" in message and "method" not in message:
                    future = self.waiters.pop(message["id"], None)
                    if future and not future.done():
                        if "error" in message:
                            future.set_exception(RuntimeError(json.dumps(message["error"])))
                        else:
                            future.set_result(message.get("result"))
                elif "id" in message:
                    # No workspace edits or server-triggered commands are accepted.
                    await self.send({"jsonrpc": "2.0", "id": message["id"],
                                     "error": {"code": -32601, "message": "Unsupported client request"}})
                else:
                    self.handle_notification(message)
        except (EOFError, asyncio.IncompleteReadError, Exception) as error:
            for future in list(self.waiters.values()):
                if not future.done():
                    future.set_exception(RuntimeError(str(error)))
            self.waiters.clear()
            if not self.stopping.is_set():
                self.state.update(status="server_closed", error=str(error), closed=now())
                self.persist()
                self.stopping.set()

    async def read_stderr(self):
        while data := await self.proc.stderr.read(8192):
            self.stderr.write(data)
            self.stderr.flush()

    def handle_notification(self, message):
        pending = self.pending
        if pending is None:
            return
        params = message.get("params") or {}
        method = message.get("method")
        if method == "textDocument/publishDiagnostics":
            if params.get("uri") != self.uri or params.get("version") != pending["version"]:
                pending["ignored_diagnostics"] += 1
                return
            diagnostics = params.get("diagnostics", [])
            if params.get("isIncremental", False):
                pending["diagnostics"].extend(diagnostics)
            else:
                pending["diagnostics"] = diagnostics
            pending["diagnostic_notifications"] += 1
        elif method == "$/lean/fileProgress":
            document = params.get("textDocument") or {}
            if document.get("uri") != self.uri or document.get("version") != pending["version"]:
                return
            progress = params.get("processing", [])
            pending["progress_notifications"] += 1
            pending["processing"] = progress
            pending["progress_done"] = not progress
            pending["fatal_progress"] = any(item.get("kind") == 2 for item in progress)
        else:
            return
        self.state["current"] = pending
        self.persist()

    async def begin_version(self, initial=False):
        if self.pending is not None:
            raise RuntimeError("Current version is still processing; overlapping updates are disabled")
        data = self.target.read_bytes()
        text = data.decode("utf-8")
        if header_of(text) != self.header:
            raise RuntimeError("Fixed import header changed; keep header stable or shut down and start a new session")
        self.version += 1
        version = self.version
        (self.evidence / f"version-{version:04d}.lean").write_bytes(data)
        pending = {"version": version, "sha256": hashlib.sha256(data).hexdigest(),
                   "started": now(), "started_monotonic": time.monotonic(),
                   "diagnostics": [], "diagnostic_notifications": 0, "ignored_diagnostics": 0,
                   "progress_notifications": 0, "progress_done": False, "processing": [],
                   "fatal_progress": False, "barrier_replied": False}
        self.pending = pending
        self.state.update(status="processing", version=version, current=pending)
        self.persist()
        if initial:
            await self.notify("textDocument/didOpen", {
                "textDocument": {"uri": self.uri, "languageId": "lean4", "version": version, "text": text},
                "dependencyBuildMode": "never"})
        else:
            await self.notify("textDocument/didChange", {
                "textDocument": {"uri": self.uri, "version": version},
                "contentChanges": [{"text": text}]})
        asyncio.create_task(self.finish_version(pending))
        return {"accepted": True, "version": version, "sha256": pending["sha256"]}

    async def finish_version(self, pending):
        try:
            await self.request("textDocument/waitForDiagnostics", {"uri": self.uri, "version": pending["version"]})
            pending["barrier_replied"] = True
            pending["finished"] = now()
            pending["elapsed_seconds"] = time.monotonic() - pending.pop("started_monotonic")
            pending["error_count"] = sum(d.get("severity") == 1 for d in pending["diagnostics"])
            pending["warning_count"] = sum(d.get("severity") == 2 for d in pending["diagnostics"])
            pending["audit_messages"] = [d.get("message", "") for d in pending["diagnostics"]
                                         if "depends on axioms" in d.get("message", "")]
            pending["sorry_ax_seen"] = any("sorryAx" in d.get("message", "") for d in pending["diagnostics"])
            fresh = pending["diagnostic_notifications"] > 0 and pending["progress_notifications"] > 0
            finished = pending["progress_done"] or pending["fatal_progress"]
            if not (fresh and finished):
                status = "incomplete_protocol_evidence"
            elif pending["error_count"] or pending["fatal_progress"] or pending["sorry_ax_seen"]:
                status = "lsp_errors"
            else:
                status = "lsp_clean"
            pending["status"] = status
            (self.evidence / f"version-{pending['version']:04d}.json").write_text(json.dumps(pending, indent=2) + "\n")
            self.state.update(status=status, current=pending)
            self.persist()
            self.pending = None
            print(json.dumps({"status": status, "version": pending["version"],
                              "errors": pending["error_count"], "seconds": pending["elapsed_seconds"]}), flush=True)
        except Exception as error:
            self.state.update(status="barrier_failed", error=str(error))
            self.persist()
            self.pending = None

    async def control(self, reader, writer):
        try:
            peer = writer.get_extra_info("socket")
            if hasattr(socket, "SO_PEERCRED"):
                _, uid, _ = struct.unpack("3i", peer.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
                if uid != os.getuid():
                    raise PermissionError("Control accepts only the same Unix user")
            request = json.loads(await reader.readline())
            command = request.get("command")
            if command == "status":
                result = self.state
            elif command == "update":
                if self.state["status"] in ("starting", "initializing", "server_closed", "barrier_failed"):
                    raise RuntimeError("Server is not ready for updates")
                result = await self.begin_version()
            elif command == "shutdown":
                result = {"accepted": True, "pending_version_abandoned": self.pending is not None}
                asyncio.create_task(self.shutdown())
            else:
                raise ValueError("Expected status, update, or shutdown")
            writer.write((json.dumps(result, ensure_ascii=False) + "\n").encode())
        except Exception as error:
            writer.write((json.dumps({"error": str(error)}) + "\n").encode())
        await writer.drain()
        writer.close()
        await writer.wait_closed()

    async def shutdown(self):
        if self.stopping.is_set():
            return
        self.state.update(status="shutting_down", shutdown_requested=now())
        self.persist()
        try:
            await asyncio.wait_for(self.request("shutdown", None), 15)
            await self.notify("exit", None)
        except Exception as error:
            self.state["shutdown_error"] = str(error)
            self.proc.terminate()
        self.stopping.set()

    async def run(self):
        abstract = "lean-lane-" + hashlib.sha256((str(self.evidence) + str(os.getpid())).encode()).hexdigest()[:24]
        server = await asyncio.start_unix_server(self.control, path="\0" + abstract)
        (self.evidence / "control.json").write_text(json.dumps({"abstractSocket": abstract, "pid": os.getpid()}, indent=2) + "\n")
        self.proc = await asyncio.create_subprocess_exec("lake", "serve", "--", "-j1", cwd=self.book,
                                                       stdin=asyncio.subprocess.PIPE,
                                                       stdout=asyncio.subprocess.PIPE,
                                                       stderr=asyncio.subprocess.PIPE)
        self.state.update(status="initializing", lake_pid=self.proc.pid)
        self.persist()
        tasks = [asyncio.create_task(self.read_stdout()), asyncio.create_task(self.read_stderr())]
        try:
            await self.request("initialize", {"processId": os.getpid(), "rootUri": self.book.as_uri(),
                                              "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
                                              "clientInfo": {"name": "lane-lean-lsp", "version": "1"}})
            await self.notify("initialized", {})
            print(json.dumps(await self.begin_version(initial=True)), flush=True)
            await self.stopping.wait()
            try:
                await asyncio.wait_for(self.proc.wait(), 15)
            except asyncio.TimeoutError:
                self.proc.kill()
                await self.proc.wait()
            self.state.update(status="stopped", server_exit_code=self.proc.returncode, stopped=now())
            self.persist()
        finally:
            server.close()
            await server.wait_closed()
            for task in tasks:
                task.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)
            for stream in (self.raw_in, self.raw_out, self.stderr, self.messages):
                stream.close()


async def client(command, evidence):
    info = json.loads((evidence / "control.json").read_text())
    reader, writer = await asyncio.open_unix_connection(path="\0" + info["abstractSocket"])
    writer.write((json.dumps({"command": command}) + "\n").encode())
    await writer.drain()
    response = json.loads(await reader.readline())
    print(json.dumps(response, ensure_ascii=False, indent=2))
    writer.close()
    await writer.wait_closed()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["start", "status", "update", "shutdown"])
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--book", type=Path)
    parser.add_argument("--file", type=Path)
    args = parser.parse_args()
    if args.command == "start":
        if args.book is None or args.file is None:
            parser.error("start requires --book and --file")
        asyncio.run(Driver(args.book, args.file, args.evidence).run())
    else:
        asyncio.run(client(args.command, args.evidence.resolve()))


if __name__ == "__main__":
    main()
