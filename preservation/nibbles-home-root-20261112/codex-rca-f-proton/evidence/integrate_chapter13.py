from pathlib import Path
import re, hashlib, json
base=Path('/home/derekblair/lane-work/codex-rca-f-proton')
book=base/'formalize-everything/books/rudin-real-and-complex-analysis'
# Only compiler-verified files are listed here. Append new files after a successful check.
files=['SphereCombined.lean','InfinityRemovable.lean','InfinityPrincipalPart.lean','InfinityPolynomial.lean','LogModulus.lean']
imports=[]
sections=[]
source_hashes={}
for filename in files:
    p=base/'evidence'/filename
    s=p.read_text()
    source_hashes[filename]=hashlib.sha256(s.encode()).hexdigest()
    lines=[]
    for line in s.splitlines():
        if line.startswith('import '):
            if line not in imports and line != 'import RudinRCA.Chapter13': imports.append(line)
        elif line.startswith('#print axioms') or line.startswith('namespace RudinRCA.Chapter13') or line.startswith('end RudinRCA.Chapter13') or line == 'noncomputable section':
            continue
        else: lines.append(line)
    sections.append('\n'.join(lines).strip())
# Named infinity definitions appear after their proved construction lemmas.
fragment=(base/'evidence/InfinityDefinitions.fragment').read_text()
source_hashes['InfinityDefinitions.fragment']=hashlib.sha256(fragment.encode()).hexdigest()
sections.append('\n'.join(l for l in fragment.splitlines() if not l.startswith('#print axioms')))
body='\n\n'.join(sections)
names=re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_]+)',body,re.M)
header='''/-!
# Rudin RCA, Chapter 13 — Approximation by Rational Functions

Working development for issue #42 at the fixed Lean/Mathlib pins.
Printed scope and exact remaining obligations: `SCOPING-F.md` and `PROGRESS.md`.
A proof of one assertion is not counted as an entire numbered node.
Exercises are excluded. No chapter completion is claimed here.
-/'''
result='\n'.join(imports)+'\n\n'+header+'\n\nset_option autoImplicit false\n\nnoncomputable section\nnamespace RudinRCA.Chapter13\n\n'+body+'\n\n/-! Axiom audit for every declaration introduced in this module. -/\n'+'\n'.join('#print axioms '+n for n in names)+'\n\nend RudinRCA.Chapter13\n'
(book/'RudinRCA/Chapter13.lean').write_text(result)
(base/'evidence/integrated-sources.json').write_text(json.dumps(source_hashes,indent=2)+'\n')
print(f'Integrated {len(files)} verified sources, {len(names)} audited declarations.')
