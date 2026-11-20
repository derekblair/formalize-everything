from pathlib import Path
import json, re
root = Path(__file__).resolve().parent
book = root.parent / 'formalize-everything/books/rudin-real-and-complex-analysis'
files = [root / name for name in [
    'Ch08FirstEight.lean', 'Ch08Completion.lean', 'Ch08FubiniCompletion.lean',
    'Ch08CounterexampleCount.lean', 'Ch08ProductExample.lean', 'Ch08Vitali.lean',
    'Ch08Sierpinski.lean', 'Ch08PowersetCount.lean', 'Ch08BumpExample.lean',
    'Ch08Later.lean', 'Ch08LayerCake.lean', 'Ch08Phi.lean', 'Ch08Maximal.lean',
    'Ch08WeakMaximal.lean', 'Ch08PowerLayerCake.lean', 'Ch08StrongMaximal.lean',
    'Ch08MaximalConstant.lean', 'Ch08ParameterizedMaximal.lean', 'Ch08MaximalNorm.lean',
]]
imports = list(dict.fromkeys(line for path in files for line in path.read_text().splitlines()
                            if line.startswith('public import ')))
header = '''/-!
# Rudin, Real and Complex Analysis, Chapter 8

The printed nodes and their statement mapping are recorded in `SCOPING-D.md`.
Positive integrals take values in `ℝ≥0∞`. Completed measurable spaces are represented
explicitly by `NullMeasurableSpace`, so completion is not conflated with Borel measure.
-/'''
parts = ['module', '', *imports, '', header, '', '@[expose] public section', '']
line_map = []
for path in files:
    lines = path.read_text().splitlines()
    start = next(i for i, line in enumerate(lines)
                 if line in ('public section', '@[expose] public section')) + 1
    body = [line for line in lines[start:] if not line.startswith('#print axioms ')]
    while body and not body[0].strip(): body.pop(0); start += 1
    parts.append('/- ' + path.stem + ' -/')
    if not any(line == 'noncomputable section' for line in body):
        parts.append('noncomputable section')
    line_map.append({'source': path.name, 'first_line': len(parts) + 1,
                     'source_first_line': start + 1, 'length': len(body)})
    parts.extend(body)
    parts.extend(['end', ''])
text = '\n'.join(parts) + '\n'
(root / 'Ch08IntegratedCandidate.lean').write_text(text)
(root / 'Ch08IntegratedCandidate.line-map.json').write_text(json.dumps(line_map, indent=2) + '\n')
# The proof audits are independent from the source elaboration pass.
ns = []
names = []
for line in text.splitlines():
    m = re.match(r'^namespace (\S+)$', line)
    if m: ns.append(m.group(1)); continue
    m = re.match(r'^end (\S+)$', line)
    if m and ns and m.group(1) == ns[-1]: ns.pop(); continue
    m = re.match(r'^(?:noncomputable )?(?:theorem|lemma|def|abbrev|structure|inductive|instance) ([\w\u0080-\uffff]+)', line)
    if m: names.append('.'.join(ns + [m.group(1)]))
(root / 'Ch08Audit.lean').write_text('module\nimport RudinRCA.Chapter08\n\n' +
    '\n'.join('#print axioms ' + name for name in dict.fromkeys(names)) + '\n')
(root / 'Ch08Audit.names.json').write_text(json.dumps(list(dict.fromkeys(names)), indent=2) + '\n')
print(json.dumps({'candidate_lines': len(text.splitlines()), 'public_declarations': len(set(names)),
                  'source_fragments': len(files)}))
