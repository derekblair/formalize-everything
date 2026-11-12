#!/usr/bin/env python3
"""Freeze sources and capture actual pinned build/audit evidence for this lane."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, shutil, subprocess, sys
lane=Path('/home/derekblair/lane-work/codex-rca-g-proton')
book=lane/'formalize-everything/books/rudin-real-and-complex-analysis'
evidence=lane/'evidence'
tag=sys.argv[1]
if not re.fullmatch(r'[a-z0-9-]+',tag):
    raise SystemExit('Evidence tag must contain only lowercase letters, digits, and hyphens')
jsonpath=evidence/f'{tag}.json'
if jsonpath.exists():
    raise SystemExit('Evidence tag already exists; choose a new tag')
assert (book/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
pin=subprocess.check_output(['git','-C',str(book/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
assert pin=='d13f23b723b8a846827a245b89c10fc7d3f11612',pin
source=book/'RudinRCA/Chapter15.lean'
text=source.read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
metadata={'started':datetime.now(timezone.utc).isoformat(),'command':['lake','build','RudinRCA'],
          'mathlib':pin,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
          'exit_code':None,'clean_slate':False}
jsonpath.write_text(json.dumps(metadata,indent=2)+'\n')
shutil.copy2(source,evidence/f'{tag}.lean')
shutil.copy2(book/'RudinRCA.lean',evidence/f'{tag}-umbrella.lean')
with (evidence/f'{tag}.log').open('w') as log:
    proc=subprocess.run(metadata['command'],cwd=book,env={**os.environ,'LEAN_NUM_THREADS':'1'},stdout=log,stderr=subprocess.STDOUT)
metadata['exit_code']=proc.returncode
metadata['finished']=datetime.now(timezone.utc).isoformat()
logtext=(evidence/f'{tag}.log').read_text()
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",logtext,re.S)
allowed={'propext','Classical.choice','Quot.sound'}
metadata['audited_families']={name:[a.strip() for a in axioms.split(',') if a.strip()] for name,axioms in audits}
metadata['unexpected_axioms']={name:sorted(set(axioms)-allowed) for name,axioms in metadata['audited_families'].items() if set(axioms)-allowed}
expected={'RudinRCA.Chapter15.'+name for name in re.findall(r'^#print axioms ([\w.]+)',text,re.M)}
metadata['missing_audits']=sorted(expected-set(metadata['audited_families']))
metadata['source_unchanged']=hashlib.sha256(source.read_bytes()).hexdigest()==metadata['source_sha256']
jsonpath.write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps({k:v for k,v in metadata.items() if k!='audited_families'},indent=2))
print(f'Audited families: {len(audits)}')
print(logtext)
raise SystemExit(proc.returncode or bool(metadata['unexpected_axioms']) or bool(metadata['missing_audits']) or not metadata['source_unchanged'])
