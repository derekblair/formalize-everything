#!/usr/bin/env python3
"""Assemble the lane's scratch fragments; this does not publish a chapter."""
from pathlib import Path
import hashlib
import json

base = Path(__file__).resolve().parent.parent
names = [
    'Chapter18Core.lean', 'Chapter18Ideals.lean', 'Chapter18Disc.lean',
    'Chapter18Fejer.lean', 'Chapter18Maximality.lean',
    'Chapter18BoundaryCharacterization.lean', 'Chapter18Wiener.lean',
]
imports = {'import Mathlib.Tactic.FunProp'}
components = []
for name in names:
    path = base / 'work' / name
    data = path.read_bytes()
    lines = data.decode().splitlines()
    imports.update(line for line in lines if line.startswith('import Mathlib.'))
    components.append((name, data, lines))
header = '\n'.join(sorted(imports)) + '\n'
output = header.splitlines() + ['', '/- Scratch integration: validation in progress. -/', '']
records = []
for name, data, lines in components:
    output.append(f'/- BEGIN {name} -/')
    start = len(output) + 1
    output.extend('' if line.startswith('import ') else line for line in lines)
    end = len(output)
    output.extend([f'/- END {name} -/', ''])
    records.append({
        'file': 'work/' + name, 'sha256': hashlib.sha256(data).hexdigest(),
        'first_line': start, 'last_line': end,
    })
text = '\n'.join(output) + '\n'
target = base / 'work/Chapter18All.lean'
target.write_text(text)
record = {'combined': str(target), 'sha256': hashlib.sha256(text.encode()).hexdigest(),
          'header_sha256': hashlib.sha256(header.encode()).hexdigest(),
          'components': records}
(base / 'evidence/combined-current-sources.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'sha256': record['sha256'], 'header_sha256': record['header_sha256'],
                  'lines': len(output), 'imports': len(imports)}))
