import concurrent.futures, datetime, hashlib, json, pathlib, subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
cs = json.loads((ROOT / 'judge-evidence/candidates.json').read_text())
ids = sorted({c[k] for c in cs for k in ('a', 'b')})

def fetch(aid):
    url = f'https://raw.githubusercontent.com/oeis/oeisdata/main/seq/{aid[:4]}/{aid}.seq'
    out = ROOT / f'.firecrawl/{aid}.md'
    result = {'id': aid, 'url': url}
    if not out.exists():
        p = subprocess.run(['firecrawl', 'scrape', url, '-o', str(out)], capture_output=True, text=True, timeout=150)
        result.update(returncode=p.returncode, log=(p.stdout+p.stderr)[-1000:])
    if out.exists():
        s = out.read_text()
        valid = all(f'%{tag} {aid} ' in s for tag in ('I', 'S', 'N', 'O'))
        result['valid'] = valid
        if valid:
            (ROOT / f'judge-evidence/records/{aid}.seq').write_text(s)
            result.update(sha256=hashlib.sha256(s.encode()).hexdigest(), bytes=len(s.encode()),
                          staged_equal=s.strip()==(ROOT / f'judge-evidence/records/{aid}.staged.seq').read_text().strip())
    result['retrieved_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    return result

results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=20) as pool:
    for f in concurrent.futures.as_completed([pool.submit(fetch, aid) for aid in ids]):
        try: r=f.result()
        except Exception as e: r={'error':str(e)}
        results.append(r)
        print(json.dumps({k:v for k,v in r.items() if k in ('id','valid','staged_equal','error')}),flush=True)
(ROOT/'judge-evidence/retrieval-manifest.json').write_text(json.dumps(results,indent=2))
