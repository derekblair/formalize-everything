"""Assemble isolated 15.12/15.13 drafts against Chapter15 through checked 15.11.

This script only writes the named scratch target and its source manifest. It
does not modify Chapter15, launch Lean, or claim validation.
"""
from pathlib import Path
import hashlib
import json
import re

book = Path(__file__).resolve().parent
sources = [
    "MeromorphicQuotientWork.lean",
    "MeromorphicPoleDataWork.lean",
    "MeromorphicQuotientAssemblyWork.lean",
    "MittagLefflerKernelWork.lean",
    "MittagLefflerSeriesWork.lean",
    "MittagLefflerInfinityWork.lean",
    "MittagLefflerSetWork.lean",
    "InterpolationLocalWork.lean",
    "NormalizedInterpolationWork.lean",
    "InterpolationWork.lean",
]
imports = {"import RudinRCA.Chapter15"}
bodies = []
manifest = []
seen = set()
for name in sources:
    data = (book / name).read_bytes()
    source = data.decode()
    names = re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\S+)", source, re.M)
    audits = set(re.findall(r"^#print axioms (\S+)", source, re.M))
    missing = set(names) - audits
    repeated = seen.intersection(names)
    if missing or repeated:
        raise RuntimeError(f"{name}: missing audits {missing}; duplicate names {repeated}")
    seen.update(names)
    for line in source.splitlines():
        if line.startswith("import Mathlib."):
            imports.add(line)
    body = "\n".join(line for line in source.splitlines() if not line.startswith("import "))
    bodies.append(f"-- Source draft: {name}\n{body}\n")
    manifest.append({"file": name, "sha256": hashlib.sha256(data).hexdigest(), "families": names})

target = book / "Chapter15QuotientInterpolationWork.lean"
text = "\n".join(sorted(imports)) + "\n\n"
text += "/- Generated scratch assembly; requires Chapter15 through 15.11.\n"
text += "Uncompiled source is not a Stage 2 result. -/\n\n"
text += "\n".join(bodies)
target.write_text(text)
record = {
    "target": target.name,
    "sha256": hashlib.sha256(text.encode()).hexdigest(),
    "lines": len(text.splitlines()),
    "theorem_family_count": len(seen),
    "status": "draft; no Lean check launched",
    "required_base": "RudinRCA.Chapter15 with all 15.11 sphere construction declarations",
    "sources": manifest,
}
(book / "Chapter15QuotientInterpolationWork.manifest.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({k: v for k, v in record.items() if k != "sources"}, indent=2))
