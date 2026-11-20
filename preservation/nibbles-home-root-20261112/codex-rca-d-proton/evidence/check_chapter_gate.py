#!/usr/bin/env python3
"""Capture commands and mechanically validate a pinned Lean chapter's evidence.

This does not inspect mathematical fidelity or independently establish the completeness
of the supplied expected-name inventory. It never invokes Lean unless explicitly used
with the `capture` subcommand and a Lean/Lake command after `--`.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import unicodedata

EXPECTED_LEAN = "leanprover/lean4:v4.34.1"
EXPECTED_MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EVIDENCE = Path(__file__).resolve().parent
BOOK = EVIDENCE.parent / "formalize-everything/books/rudin-real-and-complex-analysis"
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
AUDIT_RESULT = re.compile(
    r"'(?P<name>[^\r\n]+?)'\s+(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|(?P<empty>does not depend on any axioms))"
)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def artifact(path):
    path = Path(path).resolve()
    return {"path": str(path), "sha256": sha256(path), "bytes": path.stat().st_size}


def git_head(path):
    p = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                       capture_output=True, text=True, check=False)
    if p.returncode:
        raise ValueError(f"Cannot read Git HEAD at {path}: {p.stderr.strip()}")
    return p.stdout.strip()


def pins(book):
    book = Path(book).resolve()
    manifest = json.loads((book / "lake-manifest.json").read_text())
    mathlib = [p for p in manifest["packages"] if p.get("name") == "mathlib"]
    if len(mathlib) != 1:
        raise ValueError("Manifest must contain exactly one Mathlib package")
    return {
        "lean_toolchain": (book / "lean-toolchain").read_text().strip(),
        "mathlib_manifest_rev": mathlib[0]["rev"],
        "mathlib_checkout_rev": git_head(book / ".lake/packages/mathlib"),
        "repository_head": git_head(book),
        "toolchain_file": artifact(book / "lean-toolchain"),
        "manifest_file": artifact(book / "lake-manifest.json"),
    }


def pin_errors(p):
    errors = []
    for key, expected in (("lean_toolchain", EXPECTED_LEAN),
                          ("mathlib_manifest_rev", EXPECTED_MATHLIB),
                          ("mathlib_checkout_rev", EXPECTED_MATHLIB)):
        if p.get(key) != expected:
            errors.append(f"{key}: expected {expected}, found {p.get(key)!r}")
    return errors


def ident_start(c):
    return c == "_" or unicodedata.category(c).startswith("L")


def ident_continue(c):
    return c in "_'" or unicodedata.category(c)[0] in "LNM"


def lean_tokens(text):
    """Lex the safety-relevant fragment, retaining line/column information.

    Nested block comments, line comments, escaped/plain/raw strings, character
    literals and escaped identifiers are skipped. Interpolated strings are rejected
    conservatively because they can contain executable antiquotations. This is not
    a general Lean parser; successful compiler evidence remains mandatory.
    """
    tokens, errors = [], []
    i, n = 0, len(text)

    def location(pos):
        return {"line": text.count("\n", 0, pos) + 1,
                "column": pos - text.rfind("\n", 0, pos)}

    def problem(message, pos):
        errors.append({"message": message, **location(pos)})

    def ident_end(pos):
        j = pos + 1
        while j < n and ident_continue(text[j]):
            j += 1
        while j + 1 < n and text[j] == "." and ident_start(text[j + 1]):
            j += 2
            while j < n and ident_continue(text[j]):
                j += 1
        return j

    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i + 2)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                problem("Unterminated nested block comment", start)
        elif text[i] == "«":
            j = text.find("»", i + 1)
            if j < 0:
                problem("Unterminated escaped identifier", i)
                i = n
            else:
                i = j + 1
        elif text[i] == "r" and (m := re.match(r'r(#+)?"', text[i:])):
            start = i
            hashes = m.group(1) or ""
            j = text.find('"' + hashes, i + m.end())
            if j < 0:
                problem("Unterminated raw string", start)
                i = n
            else:
                i = j + 1 + len(hashes)
        elif text[i] == '"':
            start = i
            if i > 0 and text[i - 1] == "!":
                problem("Interpolated strings require explicit lexer support; refusing to skip antiquotations", i)
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                problem("Unterminated string", start)
        elif text[i] == "'" and (m := re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\r\n])'", text[i:])):
            i += m.end()
        elif text[i] == "`" and i + 1 < n and ident_start(text[i + 1]):
            # A quoted Name such as `sorry is data. Syntax quotations `(term|...) are scanned.
            i = ident_end(i + 1)
        elif text[i] == "#":
            tokens.append({"token": "#", **location(i)})
            i += 1
        elif ident_start(text[i]):
            j = ident_end(i)
            tokens.append({"token": text[i:j], **location(i)})
            i = j
        else:
            i += 1
    return tokens, errors


def scan_source(text):
    tokens, errors = lean_tokens(text)
    forbidden = [t for i, t in enumerate(tokens)
                 if t["token"] in {"sorry", "admit", "axiom", "axioms", "sorryAx"}
                 and not (t["token"] == "axioms" and i >= 2
                          and tokens[i - 2]["token"] == "#"
                          and tokens[i - 1]["token"] == "print")]
    return {"forbidden_tokens": forbidden, "lexical_errors": errors,
            "method": "nested-comment/string-aware conservative lexical scan"}


def parse_audit(text, expected):
    text = ANSI.sub("", text)
    results = []
    for m in AUDIT_RESULT.finditer(text):
        axioms = [] if m.group("empty") else [x.strip() for x in m.group("axioms").split(",") if x.strip()]
        results.append({"name": m.group("name"), "axioms": axioms,
                        "line": text.count("\n", 0, m.start()) + 1})
    counts = Counter(r["name"] for r in results)
    unparsed = AUDIT_RESULT.sub("", text)
    return {
        "expected_count": len(expected), "result_count": len(results),
        "missing": sorted(set(expected) - set(counts)),
        "unexpected": sorted(set(counts) - set(expected)),
        "duplicates": sorted(k for k, v in counts.items() if v != 1),
        "disallowed_axioms": [r for r in results if set(r["axioms"]) - ALLOWED_AXIOMS],
        "unparsed_axiom_messages": bool(re.search(r"depends on axioms|does not depend on any axioms", unparsed)),
        "results": results,
    }


def log_errors(text):
    text = ANSI.sub("", text)
    return [{"line": i, "text": line} for i, line in enumerate(text.splitlines(), 1)
            if re.search(r"\berror(?:\([^\r\n()]*\))?:", line, re.I)
            or re.search(r"declaration uses\s+['`]?sorry", line, re.I)
            or re.search(r"Some required targets logged failures|build failed", line, re.I)]


def capture(args):
    command = list(args.command)
    if command and command[0] == "--":
        command.pop(0)
    if not command:
        raise ValueError("capture requires an argv command after --")
    source, log, receipt = map(lambda p: Path(p).resolve(), (args.source, args.log, args.receipt))
    inputs = [Path(p).resolve() for p in args.input]
    if len({source, log, receipt}) != 3 or any(p in {log, receipt} for p in inputs):
        raise ValueError("Source, log, receipt, and tracked inputs must not overwrite each other")
    initial_pins = pins(args.book_root)
    errors = pin_errors(initial_pins)
    absent = [{"path": str(Path(p).resolve()), "absent_before": not Path(p).exists()}
              for p in args.require_absent]
    errors += [f"Required-absent path already exists: {p['path']}" for p in absent if not p["absent_before"]]
    record = {
        "schema": "lean-chapter-command-receipt-v1", "started_at": utc_now(),
        "command": command, "cwd": str(Path(args.cwd).resolve()),
        "source_before": artifact(source), "inputs_before": [artifact(p) for p in inputs],
        "pins_before": initial_pins, "required_absent": absent,
        "precondition_errors": errors, "command_exit_status": None,
    }
    if errors:
        record["capture_ok"] = False
    else:
        log.parent.mkdir(parents=True, exist_ok=True)
        try:
            with log.open("wb") as output:
                result = subprocess.run(command, cwd=args.cwd, stdout=output,
                                        stderr=subprocess.STDOUT, check=False)
            record["command_exit_status"] = result.returncode
        except OSError as exc:
            record["execution_error"] = str(exc)
        record["log"] = artifact(log)
        record["source_after"] = artifact(source)
        record["inputs_after"] = [artifact(p) for p in inputs]
        record["pins_after"] = pins(args.book_root)
        record["capture_ok"] = (
            record["command_exit_status"] == 0
            and record["source_before"] == record["source_after"]
            and record["inputs_before"] == record["inputs_after"]
            and record["pins_before"] == record["pins_after"]
        )
    record["finished_at"] = utc_now()
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"receipt": str(receipt), "command_exit_status": record["command_exit_status"],
                      "capture_ok": record["capture_ok"]}))
    return 0 if record["capture_ok"] else 1


def validate_receipt(record, source, log, current_pins, required_inputs=()):
    errors = []
    if record.get("schema") != "lean-chapter-command-receipt-v1":
        errors.append("Missing or unsupported receipt schema")
    if record.get("command_exit_status") != 0 or not record.get("capture_ok"):
        errors.append("Captured command did not finish successfully with unchanged inputs")
    for key in ("source_before", "source_after"):
        if record.get(key) != artifact(source):
            errors.append(f"{key} does not match the current source")
    if record.get("log") != artifact(log):
        errors.append("Log hash/path/size does not match the captured log")
    for key in ("pins_before", "pins_after"):
        recorded_pins = record.get(key, {})
        checked_keys = ("lean_toolchain", "mathlib_manifest_rev", "mathlib_checkout_rev",
                        "toolchain_file", "manifest_file")
        if any(recorded_pins.get(k) != current_pins.get(k) for k in checked_keys):
            errors.append(f"{key} does not match current pins and pin-file hashes")
    for p in required_inputs:
        for key in ("inputs_before", "inputs_after"):
            if artifact(p) not in record.get(key, []):
                errors.append(f"{key} does not bind required input {p}")
    if not record.get("command") or not record.get("started_at") or not record.get("finished_at"):
        errors.append("Receipt omits command or timing metadata")
    return errors


def check(args):
    source, names, build_log, audit_log, build_receipt, audit_receipt, audit_source = (
        Path(p).resolve() for p in (args.source, args.names, args.build_log, args.audit_log,
        args.build_receipt, args.audit_receipt, args.audit_source))
    expected = json.loads(names.read_text())
    if not isinstance(expected, list) or not expected or any(not isinstance(n, str) or not n or re.search(r"\s", n) for n in expected):
        raise ValueError("Expected-name inventory must be a nonempty JSON list of names")
    errors = []
    if len(expected) != len(set(expected)):
        errors.append("Expected-name inventory contains duplicates")
    current_pins = pins(args.book_root)
    errors.extend(pin_errors(current_pins))
    source_scan = scan_source(source.read_text())
    if source_scan["forbidden_tokens"] or source_scan["lexical_errors"]:
        errors.append("Source scan found forbidden terms/declarations or unsupported malformed lexical constructs")
    audit_scan = scan_source(audit_source.read_text())
    if audit_scan["forbidden_tokens"] or audit_scan["lexical_errors"]:
        errors.append("Audit-command source failed the lexical scan")
    # Only actual, un-commented commands are accepted. The source uses one command per line.
    audit_tokens, _ = lean_tokens(audit_source.read_text())
    actual_commands = [audit_tokens[i + 1]["token"] for i, t in enumerate(audit_tokens[:-1])
                       if t["token"] == "axioms" and i >= 2
                       and audit_tokens[i - 2]["token"] == "#"
                       and audit_tokens[i - 1]["token"] == "print"]
    if actual_commands != expected:
        errors.append("Audit #print axioms commands do not exactly match the ordered expected-name inventory")
    build_text, audit_text = build_log.read_text(), audit_log.read_text()
    audit = parse_audit(audit_text, expected)
    for key in ("missing", "unexpected", "duplicates", "disallowed_axioms", "unparsed_axiom_messages"):
        if audit[key]:
            errors.append(f"Axiom audit failed: {key}")
    diagnostics = {"build": log_errors(build_text), "audit": log_errors(audit_text)}
    if diagnostics["build"] or diagnostics["audit"]:
        errors.append("Build/audit logs contain Lean errors, build failure, or sorry diagnostics")
    if "Build completed successfully" not in ANSI.sub("", build_text):
        errors.append("Build log has no Lake success marker")
    if not re.search(r"\bBuilt\s+" + re.escape(args.module) + r"(?:\s|$)", ANSI.sub("", build_text)):
        errors.append("Build log does not show a fresh build of the target module")
    records = {"build": json.loads(build_receipt.read_text()), "audit": json.loads(audit_receipt.read_text())}
    receipt_errors = {
        "build": validate_receipt(records["build"], source, build_log, current_pins),
        "audit": validate_receipt(records["audit"], source, audit_log, current_pins, (names, audit_source)),
    }
    olean = Path(args.book_root).resolve() / ".lake/build/lib/lean" / (args.module.replace(".", "/") + ".olean")
    if not any(r.get("path") == str(olean) and r.get("absent_before") is True
               for r in records["build"].get("required_absent", [])):
        receipt_errors["build"].append("Receipt does not establish target .olean absence before the fresh build")
    if any(receipt_errors.values()):
        errors.append("Command receipts failed validation")
    report = {
        "schema": "lean-chapter-mechanical-gate-v1", "generated_at": utc_now(),
        "passed": not errors, "errors": errors, "module": args.module,
        "scope": "Mechanical source, pin, fresh-target-build and expected-name axiom validation; no mathematical fidelity or inventory-completeness judgment.",
        "pins": current_pins, "source": artifact(source), "expected_names": artifact(names),
        "audit_source": artifact(audit_source), "build_log": artifact(build_log), "audit_log": artifact(audit_log),
        "build_receipt": artifact(build_receipt), "audit_receipt": artifact(audit_receipt),
        "exit_statuses": {k: v.get("command_exit_status") for k, v in records.items()},
        "source_scan": source_scan, "audit_source_scan": audit_scan,
        "diagnostics": diagnostics, "receipt_errors": receipt_errors,
        "allowed_axioms": sorted(ALLOWED_AXIOMS), "audit": audit,
    }
    prefix = Path(args.output_prefix).resolve()
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    lines = [f"# {args.module}: mechanical validation {'PASS' if report['passed'] else 'FAIL'}", "",
             report["scope"], "", f"Generated: {report['generated_at']}", "",
             f"- Source: `{source}`", f"- Source SHA256: `{report['source']['sha256']}`",
             f"- Lean: `{current_pins['lean_toolchain']}`", f"- Mathlib: `{current_pins['mathlib_checkout_rev']}`",
             f"- Build / audit exit statuses: {report['exit_statuses']['build']} / {report['exit_statuses']['audit']}",
             f"- Expected / observed audit entries: {len(expected)} / {audit['result_count']}",
             f"- Allowed axioms: {', '.join(sorted(ALLOWED_AXIOMS))}", ""]
    if errors:
        lines += ["Failures:", ""] + [f"- {e}" for e in errors] + [""]
        for kind, entries in receipt_errors.items():
            lines += [f"- {kind} receipt: {e}" for e in entries]
    lines += ["", "| Declaration | Axioms |", "| --- | --- |"]
    by_name = {r["name"]: r for r in audit["results"]}
    for name in expected:
        r = by_name.get(name)
        lines.append(f"| `{name}` | {', '.join(r['axioms']) if r and r['axioms'] else ('none' if r else '**MISSING**')} |")
    lines += ["", f"Complete evidence, hashes and diagnostics: `{prefix.with_suffix('.json')}`", ""]
    prefix.with_suffix(".md").write_text("\n".join(lines))
    print(json.dumps({"passed": report["passed"], "report": str(prefix.with_suffix('.json')), "errors": errors}))
    return 0 if report["passed"] else 1


def parser():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="action", required=True)
    c = sub.add_parser("capture", help="Capture a command's real status and immutable input/output evidence")
    c.add_argument("--source", required=True)
    c.add_argument("--log", required=True)
    c.add_argument("--receipt", required=True)
    c.add_argument("--book-root", default=str(BOOK))
    c.add_argument("--cwd", default=str(BOOK))
    c.add_argument("--input", action="append", default=[])
    c.add_argument("--require-absent", action="append", default=[])
    c.add_argument("command", nargs=argparse.REMAINDER)
    g = sub.add_parser("check", help="Validate final build/audit receipts and write JSON/Markdown evidence")
    g.add_argument("--book-root", default=str(BOOK))
    g.add_argument("--source", default=str(BOOK / "RudinRCA/Chapter08.lean"))
    g.add_argument("--names", default=str(EVIDENCE / "Ch08Audit.names.json"))
    g.add_argument("--audit-source", default=str(EVIDENCE / "Ch08Audit.lean"))
    g.add_argument("--module", default="RudinRCA.Chapter08")
    for key in ("build-log", "audit-log", "build-receipt", "audit-receipt"):
        g.add_argument("--" + key, required=True)
    g.add_argument("--output-prefix", default=str(EVIDENCE / "Ch08Gate"))
    return p


def main():
    args = parser().parse_args()
    try:
        return capture(args) if args.action == "capture" else check(args)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({"passed": False, "fatal_error": str(exc)}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
