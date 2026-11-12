"""Independent finite computations from the cited OEIS definitions; no external packages."""
from functools import lru_cache
from math import gcd, isqrt, prod
from pathlib import Path
import json, re

ROOT = Path(__file__).resolve().parent.parent

@lru_cache(None)
def factor(n):
    out=[]
    p=2
    while p*p<=n:
        e=0
        while n%p==0:
            n//=p; e+=1
        if e: out.append((p,e))
        p+=1
    if n>1: out.append((n,1))
    return tuple(out)

def divisors(n):
    ds=[1]
    for p,e in factor(n):
        ds=[d*p**j for d in ds for j in range(e+1)]
    return sorted(ds)

def listed(aid):
    s=(ROOT/'records'/f'{aid}.seq').read_text()
    off=int(re.search(r'^%O \S+ (\d+)',s,re.M)[1])
    vals=[int(n) for l in s.splitlines() if l[:2] in ['%S','%T','%U'] for n in l.split(' ',2)[2].strip(',').split(',')]
    return dict(enumerate(vals,off))

def rgs(values):
    seen={}
    return [seen.setdefault(x,len(seen)+1) for x in values]

def checked_pair(aid,bid,a,b,start):
    for sid,vals in [(aid,a),(bid,b)]:
        ls=listed(sid)
        assert all(ls[n]==v for n,v in enumerate(vals,start) if n in ls),sid
    k=next((i for i,(x,y) in enumerate(zip(a,b)) if x!=y),min(len(a),len(b)))
    return {'agreement':k,'start':start,'first_mismatch':None if k==min(len(a),len(b)) else {'index':start+k,'a':a[k],'b':b[k]},'listed_terms_reproduced':True}

@lru_cache(None)
def max_power(n):
    return gcd(*(e for p,e in factor(n)))

@lru_cache(None)
def steps(n):
    if n==1:return 0
    d=max(d for d in divisors(n) if d==1 or max_power(d)==1)
    return 1+steps(n//d)

out={}
out['136']=checked_pair('A052409','A327503',[max_power(n) for n in range(1,217)],[steps(n) for n in range(1,217)],1)

def stern(n):
    a,b=1,0
    while n:
        if n&1:b+=a
        else:a+=b
        n//=2
    return b

def nextprime(p):
    p+=1
    while factor(p)!=((p,1),):p+=1
    return p

def doudna(n):
    n-=1
    p,t=2,1
    while True:
        if n%2:t*=p
        else:p=nextprime(p)
        n//=2
        if not n:return t

def a163511(n):
    return 1 if n==0 else doudna((3<<(n//2).bit_length())-n)

def a103391(n):
    if n==1:return 1
    m=n-1
    while m%2==0:m//=2
    return (m+3)//2

a=[a103391(n) for n in range(1,193)]
b=rgs((stern(n),stern(a163511(n))) for n in range(192))
assert all(listed('A103391')[n]==a[n-1] for n in listed('A103391'))
assert all(listed('A331743')[n]==b[n] for n in listed('A331743'))
k=next(i for i,(x,y) in enumerate(zip(a,b)) if x!=y)
out['143']={'agreement':k,'a_start':1,'b_start':0,'first_mismatch':{'a_index':k+1,'b_index':k,'a':a[k],'b':b[k]},'listed_terms_reproduced':True}

def pattern(n):
    ps=[p for p,e in factor(n)]
    return tuple(tuple(dict(factor(d)).get(p,0) for p in ps) for d in divisors(n))

def signatures(n):
    return tuple(tuple(sorted(e for p,e in factor(d))) for d in divisors(n))

out['156']=checked_pair('A290110','A300250',rgs(pattern(n) for n in range(1,859)),rgs(signatures(n) for n in range(1,859)),1)

def fermi(n):
    f=factor(n)
    return len(f)==1 and f[0][1]&(f[0][1]-1)==0

def a334870(n):
    if isqrt(n)**2==n:return isqrt(n)
    core=prod(p for p,e in factor(n) if e%2)
    m,p=n,2
    while True:
        if core%p==0:return m//p
        m*=p
        p=nextprime(p)

a=[];count=2
for n in range(1,106):
    if n==1:a.append(1)
    elif fermi(n):a.append(2)
    else:count+=1;a.append(count)
b=rgs(0 if n==1 else -1 if fermi(n) else a334870(n) for n in range(1,106))
out['157']=checked_pair('A305979','A334868',a,b,1)

def lpf(n):return 1 if n==1 else factor(n)[-1][0]

@lru_cache(None)
def minus_steps(n):
    return 0 if n&(n-1)==0 else 1+minus_steps(n-n//lpf(n))

@lru_cache(None)
def plus_steps(n):
    return 0 if n&(n-1)==0 else 1+plus_steps(n+n//lpf(n))

a=rgs((lpf(n),minus_steps(n),plus_steps(n)) for n in range(1,122))
b=rgs((lpf(n),prod(p+1 for p,e in factor(n) if p>2),prod(p**(e-1) for p,e in factor(n) if p>2)) for n in range(1,122))
out['158']=checked_pair('A351454','A351460',a,b,1)

# Literal A143064 first formula: the product exponent incorrectly uses k, not j.
# At x^2, k=0 contributes 1 and k=2 contributes 1, giving 2 vs a(1)=1.
out['150_formula_contradiction']={'formula':'sum_{k>=0} x^k/(1+x^(2*k+1))^(k+1), expanded in powers of x^2','n':1,'literal_coefficient':2,'listed':listed('A143064')[1]}
# A199918 bilateral series has k=1 and k=-1 at degree zero, with opposite Kronecker signs.
out['149_formula_contradictions']={'bilateral_constant':0,'listed_a0':listed('A199918')[0],'ambiguous_prime29_prediction':-1,'listed_a35':listed('A199918')[35]}
(ROOT/'reviews'/'verification-136-160.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
