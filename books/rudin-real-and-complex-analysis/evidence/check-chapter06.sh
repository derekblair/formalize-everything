#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
expected_lean='Lean (version 4.34.1'
expected_mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'
lean --version | tee evidence/lean-version.log
[[ "$(lean --version)" == "$expected_lean"* ]]
[[ "$(git -C .lake/packages/mathlib rev-parse HEAD)" == "$expected_mathlib" ]]
# The chapter's #print axioms output is part of the build log.
lake build RudinRCA.Chapter06 2>&1 | tee evidence/ch06-build.log
if rg -n '\b(sorry|admit|axiom)\b' RudinRCA/Chapter06.lean; then
  echo 'Forbidden proof placeholder or declared axiom found.' >&2
  exit 1
fi
python3 - <<'PY'
from pathlib import Path
import re
log=Path('evidence/ch06-build.log').read_text()
allowed={'propext','Classical.choice','Quot.sound'}
audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
no_axioms=re.findall(r"'([^']+)' does not depend on any axioms",log)
expected=re.findall(r'^#print axioms (\S+)',Path('RudinRCA/Chapter06.lean').read_text(),re.M)
expected_basenames=[name.split('.')[-1] for name in expected]
if len(expected_basenames) != len(set(expected_basenames)):
    raise SystemExit('Audit names are not unique; use fully qualified matching before accepting.')
seen={name.split('.')[-1] for name,_ in audits}|{name.split('.')[-1] for name in no_axioms}
missing=set(expected_basenames)-seen
if not expected or missing:
    raise SystemExit(f'Missing axiom audits: {sorted(missing)}')
for name, raw in audits:
    actual={a.strip() for a in raw.split(',') if a.strip()}
    if not actual <= allowed:
        raise SystemExit(f'{name}: unexpected axioms {sorted(actual - allowed)}')
print(f'PASS: {len(seen)} declarations audited; only the three permitted axioms.')
PY
