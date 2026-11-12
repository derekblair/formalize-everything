import json,pathlib,re
root=pathlib.Path(__file__).resolve().parent
cs=json.loads((root/'candidates.json').read_text())
def record(aid):
    s=(root/f'records/{aid}.seq').read_text()
    terms=[]
    for tag in 'STU':
        for v in re.findall(r'^%'+tag+' '+aid+r' (.*)$',s,re.M):
            terms.extend(int(x.strip()) for x in v.split(',') if x.strip())
    offset=int(re.search(r'^%O '+aid+r' (-?\d+)',s,re.M)[1])
    return offset,terms
def compare(a,b,oa,ob,da=0,db=0,ab=False):
    aa,bb=a[da:],b[db:]
    size=min(len(aa),len(bb)); count=0
    for x,y in zip(aa,bb):
        if (abs(x) if ab else x)!=(abs(y) if ab else y): break
        count+=1
    d=dict(count=count,available=size,a_start=oa+da,b_start=ob+db,absolute=ab)
    if count<size: d['mismatch']=dict(a_index=oa+da+count,b_index=ob+db+count,a=aa[count],b=bb[count])
    else: d['censored_by_listing']=True
    return d
out=[]
for c in cs:
    oa,a=record(c['a']); ob,b=record(c['b']); start=max(oa,ob)
    d=dict(c,offset_a=oa,offset_b=ob,length_a=len(a),length_b=len(b))
    d['native']=compare(a,b,oa,ob,start-oa,start-ob)
    d['ordinal']=compare(a,b,oa,ob)
    v=c['variant']; drop=int(v[-1]) if v.startswith('drop') else 0
    d['packet_variant']=compare(a,b,oa,ob,drop,drop,v=='abs')
    d['best_small_shift']=sorted([compare(a,b,oa,ob,i,j,v=='abs') for i in range(4) for j in range(4)],key=lambda t:-t['count'])[:3]
    out.append(d)
(root/'agreement.json').write_text(json.dumps(out,indent=2))
for d in out:
    print(d['rank'], d['a'],d['b'], 'offsets',d['offset_a'],d['offset_b'],'lengths',d['length_a'],d['length_b'],'native',d['native'],'variant',d['variant'],d['packet_variant'])
