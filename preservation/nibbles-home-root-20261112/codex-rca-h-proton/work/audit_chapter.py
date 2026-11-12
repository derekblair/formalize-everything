#!/usr/bin/env python3
"""Audit a captured CLI Lean run; does not invoke Lean or modify chapter source.

Example:
  python3 work/audit_chapter.py --source work/Chapter18All.lean \
    --log evidence/final-cli.log --run-record evidence/final-cli.json \
    --family RudinRCA.Chapter18 --expect RudinRCA.Chapter18.theorem18_21 \
    --output evidence/final-audit.json

The trusted run record must contain integer exit_code and source sha256. This
checks only the declarations actually printed, plus explicit --expect names;
it does not establish that an external coverage inventory is exhaustive.
Unsupported interpolation, unclosed comments/strings, and malformed reports fail
closed. Apostrophes also occur in Lean notation; unrecognized apostrophes are
scanned as punctuation without hiding subsequent tokens. CLI validates syntax.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import unicodedata


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN = frozenset({"sorry", "admit", "axiom", "sorryAx"})
REPORT = re.compile(
    r"(?m)^[ \t]*'(?P<name>[^\r\n]+?)'\s+"
    r"(?:depends\s+on\s+axioms\s*:\s*\[(?P<axioms>[^\]]*)\]"
    r"|does\s+not\s+depend\s+on\s+any\s+axioms)"
)
MARKER = re.compile(r"depends\s+on\s+axioms\s*:|does\s+not\s+depend\s+on\s+any\s+axioms")
ERROR = re.compile(r"(?m)(?:^|\s)error(?:\([^\r\n)]*\))?\s*:")
RAW_STRING = re.compile(r'r(#+)?"')
CHARACTER = re.compile(r"'(?:[^'\\\r\n]|\\(?:[nrt0\\'\"]|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|u\{[0-9A-Fa-f]+\}))'")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_scan(text):
    """Return prohibited tokens and lexical errors, with nested Lean comments."""
    findings, errors, tokens = [], [], []
    i, size = 0, len(text)

    def location(pos):
        return {"line": text.count("\n", 0, pos) + 1,
                "column": pos - text.rfind("\n", 0, pos)}

    def error(message, pos):
        errors.append({"message": message, **location(pos)})

    def ident_rest(char):
        return char in "_'" or unicodedata.category(char)[0] in "LMN"

    while i < size:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i + 2)
            i = size if end < 0 else end
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < size and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                error("unterminated block comment", start)
        elif text.startswith("-/", i):
            error("unmatched block-comment terminator", i)
            i += 2
        elif text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                error("unterminated quoted identifier", i)
                break
            tokens.append(("QUOTED_IDENTIFIER", i))
            i = end + 1
        elif (raw := RAW_STRING.match(text, i)) is not None:
            start = i
            if tokens and tokens[-1][0] == "!":
                error("interpolated raw string requires manual lexical review", start)
            ending = '"' + (raw.group(1) or "")
            i = raw.end()
            end = text.find(ending, i)
            if end < 0:
                error("unterminated raw string", start)
                break
            tokens.append(("STRING", start))
            i = end + len(ending)
        elif text[i] == '"':
            start = i
            if tokens and tokens[-1][0] == "!":
                error("interpolated string requires manual lexical review", start)
            i += 1
            while i < size and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= size:
                error("unterminated string", start)
                break
            tokens.append(("STRING", start))
            i += 1
        elif text.startswith("''", i) or text.startswith("⁻¹'", i):
            operator = "''" if text.startswith("''", i) else "⁻¹'"
            tokens.append((operator, i))
            i += len(operator)
        elif text[i] == "'":
            start = i
            # Character literals contain one scalar or one escaped scalar.
            literal = CHARACTER.match(text, i)
            if literal is None:
                # For example ∑', ∏', or another notation token. Do not skip text.
                tokens.append(("'", start))
                i += 1
            else:
                tokens.append(("CHARACTER", start))
                i = literal.end()
        elif text[i] == "_" or text[i].isalpha():
            start = i
            i += 1
            while i < size and ident_rest(text[i]):
                i += 1
            token = text[start:i]
            if token in FORBIDDEN:
                findings.append({"token": token, **location(start)})
            if token == "axioms" and [x[0] for x in tokens[-2:]] != ["#", "print"]:
                findings.append({"token": token, **location(start)})
            tokens.append((token, start))
        else:
            tokens.append((text[i], i))
            i += 1
    return findings, errors


def parse_reports(log):
    """Parse both Lean print formats, allowing whitespace and wrapped axiom lists."""
    declarations, errors, spans = {}, [], []
    for match in REPORT.finditer(log):
        spans.append(match.span())
        name = match.group("name").strip()
        body = match.group("axioms")
        axioms = [] if body is None or not body.strip() else [x.strip() for x in body.split(",")]
        if not name or any(not x for x in axioms):
            errors.append("empty declaration or malformed axiom list")
            continue
        axioms = sorted(set(axioms))
        if name in declarations and declarations[name] != axioms:
            errors.append("inconsistent repeated axiom report: " + name)
        declarations[name] = axioms
    for marker in MARKER.finditer(log):
        if not any(start <= marker.start() < end for start, end in spans):
            errors.append("unparsed/truncated axiom report at offset " + str(marker.start()))
    return declarations, errors


def audit(source_bytes, log_bytes, record, family, expected=(), minimum=1):
    source, log = source_bytes.decode("utf-8"), log_bytes.decode("utf-8")
    findings, lexical_errors = source_scan(source)
    declarations, report_errors = parse_reports(log)
    errors = []
    if not isinstance(record, dict):
        record = {}
        errors.append("run record must be a JSON object")
    if type(record.get("exit_code")) is not int or record["exit_code"] != 0:
        errors.append("CLI exit_code must be the integer 0")
    if record.get("sha256") != digest(source_bytes):
        errors.append("run-record source hash is absent or mismatched")
    if "log_sha256" in record and record["log_sha256"] != digest(log_bytes):
        errors.append("run-record log hash is mismatched")
    if not family or minimum < 1:
        errors.append("a nonempty family and positive minimum count are required")
    family_names = sorted(n for n in declarations if n.startswith(family + "."))
    if len(family_names) < max(1, minimum):
        errors.append("insufficient declarations from the requested family")
    missing = sorted(set(expected) - declarations.keys())
    if missing:
        errors.append("expected declarations missing from the axiom output")
    unexpected = {name: sorted(set(axioms) - ALLOWED_AXIOMS)
                  for name, axioms in declarations.items() if set(axioms) - ALLOWED_AXIOMS}
    cli_errors = len(ERROR.findall(log))
    passed = not (errors or findings or lexical_errors or report_errors or unexpected or cli_errors)
    return {
        "passed": passed, "source_sha256": digest(source_bytes), "log_sha256": digest(log_bytes),
        "cli_exit_code": record.get("exit_code"), "family": family,
        "family_count": len(family_names), "family_declarations": family_names,
        "audited_declarations": len(declarations), "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "unexpected_axioms": unexpected, "missing_expected_declarations": missing,
        "prohibited_source_tokens": findings, "lexical_errors": lexical_errors,
        "report_parse_errors": report_errors, "cli_error_markers": cli_errors,
        "errors": errors,
        "scope": "source lexical scan and captured CLI axiom reports; not a coverage proof",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--run-record", type=Path, required=True)
    parser.add_argument("--family", required=True)
    parser.add_argument("--expect", action="append", default=[])
    parser.add_argument("--min-family-count", type=int, default=1)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = audit(args.source.read_bytes(), args.log.read_bytes(),
                       json.loads(args.run_record.read_text()), args.family,
                       args.expect, args.min_family_count)
        result.update(source=str(args.source), log=str(args.log), run_record=str(args.run_record))
    except (OSError, UnicodeError, ValueError, TypeError) as exc:
        result = {"passed": False, "errors": [str(exc)]}
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
