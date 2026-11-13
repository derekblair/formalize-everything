#!/usr/bin/env python3
"""Extract in-progress diagnostics without mistaking them for completion."""
from pathlib import Path
import json, subprocess, sys

prefix = Path(sys.argv[1])
session = str(prefix).split('.v', 1)[0]
version = int(str(prefix).split('.v', 1)[1].split('.', 1)[0])
rows = []
for line in Path(session + '.protocol.jsonl').open():
    try:
        message = json.loads(line)['message']
    except (json.JSONDecodeError, KeyError):
        continue
    if message.get('method') != 'textDocument/publishDiagnostics':
        continue
    p = message['params']
    if p.get('version') != version:
        continue
    if not p.get('isIncremental', False):
        rows = []
    rows.extend(p.get('diagnostics', []))
output = str(prefix) + '.partial'
Path(output + '.diagnostics.json').write_text(json.dumps(rows, indent=2) + '\n')
summary = {'completion_barrier': False, 'status': 'in progress; not validation evidence',
           'diagnostics_file': output + '.diagnostics.json',
           'line_map_snapshot': str(prefix) + '.line-map.json'}
Path(output + '.summary.json').write_text(json.dumps(summary, indent=2) + '\n')
subprocess.run([sys.executable, str(Path(__file__).with_name('map_lsp_diagnostics.py')),
                output + '.summary.json'], check=True)
