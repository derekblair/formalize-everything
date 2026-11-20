import json,math,pathlib,functools
R=pathlib.Path(__file__).resolve().parent
@functools.cache
def factor(n):
 r={};p=2
 while p*p<=n:
  while n%p==0:r[p]=r.get(p,0)+1;n//=p
  p+=1
 if n>1:r[n]=r.get(n,0)+1
 return r
@functools.cache
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def sigma(n):return math.prod((p**(e+1)-1)//(p-1) for p,e in factor(n).items())
def tau(n):return math.prod(e+1 for e in factor(n).values())
def f61(n):return int(sigma(n)%4==2)
def g61(n):return int(sum(e for p,e in factor(n).items() if p%4==1)==1 and all(e%2==0 for p,e in factor(n).items() if p%4==3))
def f63(n):return sum(e>3 for e in factor(n).values())
def g63(n):return sum(math.gcd(d,n//d)>1 and round(d**(1/3))**3==d for d in divisors(n))
def f64(n):
 for _ in range(5):n=tau(n)
 return n
@functools.cache
def g66(n):return 0 if n==0 else g66(n//10)+(n%10)*(n//10+1)
def f67(n):
 s=1;n//=10
 while n:s*=n+1;n//=10
 return s
p67=[1]+[0]*200
for c in (1,10,100):
 for j in range(c,201):p67[j]+=p67[j-c]
def f69(n):
 k=0
 while len(divisors(n))>2:n-=divisors(n)[-2];k+=1
 return k
ps=[n for n in range(2,200) if len(factor(n))==1 and factor(n).get(n)==1]
def g69(n):
 fs=factor(n)
 return sum((ps.index(p)+1)*e for p,e in fs.items())-(ps.index(max(fs))+1 if fs else 0)
def bell(n):
 b=[1]
 for k in range(n):b.append(sum(math.comb(k,j)*b[j] for j in range(k+1)))
 return b[n]
def pow12(n):
 r=0
 while n:n//=12;r+=n
 return r
gol=[0,1,2]
for n in range(3,220):gol.append(1+gol[n-gol[gol[n-1]]])
v=[1,2,2];k=3
while len(v)<220:
 ds=''.join(map(str,v));v.extend([k]*int(ds[k-1]));k+=1
f70=[n for n in range(1,301) if '0' not in str(n)]
g70=[n for n in range(1,301) if all('0' not in str(d) for d in divisors(n))]
f76=[n for n in range(1,301) if len(set(str(n)))==2]
g76=[n for n in range(1,301) if len(set(str(n))) in (2,3,5,7)]
def greedy(nozero):
 a=[1];used={1}
 while len(a)<110:
  first=10-a[-1]%10
  for n in range(1,2000):
   if n not in used and n%10!=0 and str(n)[0]==str(first) and (not nozero or '0' not in str(n)):
    a.append(n);used.add(n);break
 return a
def inv(char):
 out={1:1}
 for n in range(2,129):out[n]=-sum(char(n//d)*out[d] for d in divisors(n) if d<n)
 return out
inv1=inv(lambda n:int(all(e&(e-1)==0 for e in factor(n).values())))
inv2=inv(lambda n:int(all(e.bit_count()%2 for e in factor(n).values())))
def f81(n):
 x=0
 for e in factor(n).values():x^=e
 return int(x==1)
def g81(n):return sum(factor(n).values())%2 * (sum(e.bit_count() for e in factor(n).values())%2)
def restrictedpart(e,p):
 a=[1]+[0]*e
 for k in range(1,p):
  for j in range(k,e+1):a[j]+=a[j-k]
 return a[e]
def f82(n):return math.prod(e//2+1 for p,e in factor(n).items() if p>2)
def g82(n):return math.prod(restrictedpart(e,p) for p,e in factor(n).items())
def f84(n):return int(sum(e>=2 for e in factor(n).values())==1)
def g84(n):return int((n%4==0 and all(e==1 for p,e in factor(n).items() if p!=2)) or (n%4!=0 and any(e>=2 for e in factor(n).values())))
out={}
def check(rank,f,g,start,end):
 for n in range(start,end+1):
  if f(n)!=g(n):out[rank]={'start':start,'first_mismatch':n,'agreement':n-start,'a':f(n),'b':g(n)};return
 out[rank]={'start':start,'through':end,'agreement':end-start+1}
check(61,f61,g61,1,325)
check(63,f63,g63,1,128)
check(64,f64,lambda n:2 if n>1 else 1,1,5040)
check(65,lambda n:int(all(sigma(n)%d==0 for d in divisors(n) if d<n)),lambda n:int(tau(n)==2 or sigma(n)==2*n),2,120)
check(66,lambda n:math.prod(int(d)+1 for d in str(n))-1,g66,0,101)
check(67,f67,lambda n:p67[n],0,100)
check(69,f69,g69,1,169)
check(70,lambda n:f70[n-1],lambda n:g70[n-1],1,173)
check(71,lambda n:int(n%2 and sigma(n)%4==2),lambda n:int(n%4==1 and sum(factor(n).values())%2),1,105)
check(73,lambda n:bell(len(factor(n)))-1,lambda n:2**len(factor(n))-len(factor(n))-1,2,210)
check(74,pow12,lambda n:n//12,0,144)
check(75,lambda n:gol[n],lambda n:v[n-1],1,169)
check(76,lambda n:f76[n-1],lambda n:g76[n-1],1,90)
a78,b78=greedy(False),greedy(True)
check(78,lambda n:a78[n-1],lambda n:b78[n-1],1,91)
check(80,lambda n:inv1[n],lambda n:inv2[n],1,128)
check(81,f81,g81,1,128)
check(82,f82,g82,1,125)
check(84,f84,g84,1,225)
(R/'computed-61-85.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
