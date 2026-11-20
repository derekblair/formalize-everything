"""Summarize actual Lean axiom output; fail on any nonstandard dependency."""
import json
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
text = path.read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
audits = []
for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    names = [x.strip() for x in match.group(2).split(',') if x.strip()]
    audits.append({"declaration": match.group(1), "axioms": names})
for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
    audits.append({"declaration": match.group(1), "axioms": []})
unexpected = sorted({a for row in audits for a in row['axioms']} - allowed)
result = {
    "log": str(path),
    "audited_declarations": len(audits),
    "allowed_axioms": sorted(allowed),
    "unexpected_axioms": unexpected,
    "audits": audits,
}
print(json.dumps(result, indent=2))
if not audits or unexpected or re.search(r"\berror(?:\(|:)", text):
    raise SystemExit(1)
