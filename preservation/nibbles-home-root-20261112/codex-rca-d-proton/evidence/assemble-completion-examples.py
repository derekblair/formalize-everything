from pathlib import Path
import json
root = Path(__file__).resolve().parent
files = [root / x for x in ['Ch08Completion.lean', 'Ch08FubiniCompletion.lean', 'Ch08CounterexampleCount.lean', 'Ch08ProductExample.lean', 'Ch08Vitali.lean', 'Ch08Sierpinski.lean', 'Ch08PowersetCount.lean']]
imports = []
for path in files:
    for line in path.read_text().splitlines():
        if line.startswith('public import ') and line not in imports:
            imports.append(line)
parts = ['module', '', *imports, '', '@[expose] public section', '']
line_map = []
for path in files:
    lines = path.read_text().splitlines()
    parts.append('/- BEGIN ' + path.name + ' -/')
    if 'noncomputable section' in lines:
        start = lines.index('noncomputable section')
    else:
        start = lines.index('public section') + 1
        parts.append('noncomputable section')
    begin = len(parts) + 1
    body = [line for line in lines[start:] if not line.startswith('#print axioms ')]
    parts.extend(body)
    parts.extend(['end', '/- END ' + path.name + ' -/', ''])
    line_map.append({'file': path.name, 'combined_first_line': begin, 'source_first_line': start + 1, 'body_length': len(body)})
(root / 'Ch08CompletionAndExamples.lean').write_text('\n'.join(parts) + '\n')
(root / 'Ch08CompletionAndExamples.line-map.json').write_text(json.dumps(line_map, indent=2) + '\n')
print(json.dumps(line_map))
