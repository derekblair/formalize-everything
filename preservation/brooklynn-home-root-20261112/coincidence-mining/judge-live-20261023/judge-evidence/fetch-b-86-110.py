import concurrent.futures,subprocess,json,re,pathlib,datetime,hashlib
base=pathlib.Path('.')
cs=[c for c in json.loads((base/'judge-evidence/candidates.json').read_text()) if 86<=c['rank']<=110]
ids=[]
for c in cs:
 for aid in [c['a'],c['b']]:
  text=(base/f'judge-evidence/records/{aid}.seq').read_text()
  if f'/{aid}/b{aid[1:]}.txt' in text: ids.append(aid)
def run(aid):
 out=base/f'.firecrawl/{aid}-b.md'; url=f'https://oeis.org/{aid}/b{aid[1:]}.txt'
 if not out.exists():
  p=subprocess.run(['firecrawl','scrape',url,'-o',str(out)],capture_output=True,text=True,timeout=150)
 else: p=None
 if not out.exists(): return {'id':aid,'url':url,'error':(p.stdout+p.stderr)[-1000:]}
 s=out.read_text(); vals={int(m[1]):int(m[2]) for m in re.finditer(r'^(-?\d+)\s+(-?\d+)\s*$',s,re.M)}
 return {'id':aid,'url':url,'rows':len(vals),'first_index':min(vals) if vals else None,'last_index':max(vals) if vals else None,'sha256':hashlib.sha256(s.encode()).hexdigest(),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=10) as pool:
 for f in concurrent.futures.as_completed([pool.submit(run,aid) for aid in ids]):
  try: result=f.result()
  except Exception as exc: result={'error':str(exc)}
  print(json.dumps(result),flush=True);results.append(result)
(base/'judge-evidence/reviews/86-110-b-retrieval.json').write_text(json.dumps(results,indent=2))
