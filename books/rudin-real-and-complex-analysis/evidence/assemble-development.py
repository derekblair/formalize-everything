#!/usr/bin/env python3
"""Snapshot independent proof drafts into one Lean check, with source mapping.

Only Mathlib imports are retained. Local scratch-file dependencies must be
listed earlier in the explicit source order. The generated file is development
evidence, not the delivered chapter module.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("pass_name")
parser.add_argument("sources", nargs="+")
args = parser.parse_args()
book = Path(__file__).resolve().parent.parent
imports, bodies = [], []
for name in args.sources:
    raw = (book / name).read_text()
    body = []
    for line in raw.splitlines():
        if line.startswith("import "):
            if line.startswith("import Mathlib.") and line not in imports:
                imports.append(line)
            body.append("")
        else:
            body.append(line)
    bodies.append((name, body, hashlib.sha256(raw.encode()).hexdigest()))
lines, mapping = imports + [""], []
for name, body, sha in bodies:
    lines.append("-- BEGIN SOURCE " + name)
    start = len(lines) + 1
    lines += body
    mapping.append({"source": name, "start": start, "end": len(lines), "sha256": sha})
    lines += ["-- END SOURCE " + name, ""]
(book / "DevelopmentAggregate.lean").write_text("\n".join(lines) + "\n")
(book / "evidence" / (args.pass_name + "-source-map.json")).write_text(
    json.dumps(mapping, indent=2) + "\n"
)
print(f"Snapshot: {len(lines)} lines, {len(bodies)} sources, {len(imports)} imports")
