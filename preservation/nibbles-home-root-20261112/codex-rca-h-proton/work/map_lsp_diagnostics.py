#!/usr/bin/env python3
"""Map the persistent combined Lean document's diagnostics to source fragments."""
from pathlib import Path
import json,re,sys

summary_path=Path(sys.argv[1])
summary=json.loads(summary_path.read_text())
rows=json.loads(Path(summary['diagnostics_file']).read_text())
line_map=json.loads(Path(summary['line_map_snapshot']).read_text())
components=line_map['components']
grouped={c['file']:[] for c in components}
grouped['imports']=[]
for d in rows:
    line=d.get('range',{}).get('start',{}).get('line',0)+1
    col=d.get('range',{}).get('start',{}).get('character',0)+1
    owner=next((c for c in components if c['first_line']<=line<=c['last_line']),None)
    name=owner['file'] if owner else 'imports'
    local=line-owner['first_line']+1 if owner else line
    record=dict(d)
    record.update({'component':name,'source_line':local,'source_column':col,
                   'combined_line':line,'source_sha256':owner['sha256'] if owner else None})
    grouped[name].append(record)
prefix=str(summary_path).removesuffix('.summary.json')
result=[]
allowed={'propext','Classical.choice','Quot.sound'}
for name,ds in grouped.items():
    stem=Path(name).stem
    output=Path(prefix+'.'+stem+'.diagnostics.txt')
    rendered=[]
    for d in ds:
        severity={1:'error',2:'warning',3:'info',4:'hint'}.get(d.get('severity'),'diagnostic')
        rendered.append(f"{name}:{d['source_line']}:{d['source_column']}: {severity}: {d.get('message','')}")
    output.write_text('\n\n'.join(rendered)+'\n')
    bad={}
    for d in ds:
        message=d.get('message','')
        for decl,items in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",message):
            axioms=set(re.split(r'\s*,\s*',items.strip()))
            unexpected=axioms-allowed
            if unexpected:bad[decl]=sorted(unexpected)
    result.append({'component':name,'errors':sum(d.get('severity')==1 for d in ds),
                   'warnings':sum(d.get('severity')==2 for d in ds),
                   'diagnostics':len(ds),'unexpected_axioms':bad,'output':str(output)})
Path(prefix+'.mapped-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'completion_barrier':summary.get('completion_barrier'),
                  'status':summary.get('status'),'components':result},indent=2))
