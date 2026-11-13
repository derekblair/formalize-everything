import math,re,json,itertools
from decimal import Decimal, getcontext
from functools import lru_cache
from pathlib import Path

def factor(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out

def divisors(n):
 out=[1]
 for p,e in factor(n).items():out=[d*p**i for d in out for i in range(e+1)]
 return sorted(out)
def sigma(n):return sum(divisors(n))
def omega(n):return sum(factor(n).values())
def lpf(n):return max(factor(n),default=1)
def derivative(n):return sum(n//p*e for p,e in factor(n).items())
def pp(n):return any(e>=p for p,e in factor(n).items())
def firstdiff(f,g,start,end):
 for n in range(start,end+1):
  a,b=f(n),g(n)
  if a!=b:return {'n':n,'a':a,'b':b,'preceding_agreement':n-start}
def runs(s):return [''.join(g) for k,g in itertools.groupby(s)]
def short(n):return int('0'+''.join(x[:-1] for x in runs(str(n))))
def long(n):return int(''.join(x+x[0] for x in runs(str(n))))
def keep(n):return int('0'+''.join(x for x in runs(str(n)) if len(x)>1))
def splits(n):
 s=str(n); out=set()
 for mask in range(1<<(len(s)-1)):
  total=0;start=0
  for i in range(len(s)-1):
   if mask&(1<<i):total+=int(s[start:i+1]);start=i+1
  out.add(total+int(s[start:]))
 return out
@lru_cache(None)
def facts(n,lo=2):
 if n==1:return ((),)
 return tuple((d,)+f for d in divisors(n) if d>=lo for f in facts(n//d,d))
def countfact(n,proper=False):
 pairs=[]
 for a,b in itertools.combinations(facts(n),2):
  if all((proper and x==y) or (x%y and y%x) for x in a for y in b):pairs.append((a,b))
 return pairs
def clmul(a,b):
 out=0
 while b:
  if b&1:out^=a
  a<<=1;b>>=1
 return out
def gfmod(n,d):
 while n and n.bit_length()>=d.bit_length():n^=d<<(n.bit_length()-d.bit_length())
 return n
out={}
out[87]=firstdiff(lambda n:long(short(n)),keep,0,11011)
out[91]=firstdiff(lambda n:int(n%4==3 and omega(n)%2==0),lambda n:int(n>1 and not pp(n) and pp(derivative(n))),1,158)
out[91]['135']={'factor':factor(135),'derivative':derivative(135),'divisible_by_3_cubed':135%27==0}
out[93]=firstdiff(lambda n:math.lcm(*factor(n).values()) if n>1 else 1,lambda n:math.prod(set(factor(n).values())),1,144)
primes=[n for n in range(2,626) if len(factor(n))==1 and omega(n)==1];primepi={p:i+1 for i,p in enumerate(primes)}
out[94]=firstdiff(lambda n:sum(e>=p for p,e in factor(n).items()),lambda n:sum(e>=1+primepi[p] for p,e in factor(n).items()),1,625)
zum=[]
for d in divisors(748):
 bits=1;ds=divisors(d)
 for x in ds:bits|=bits<<x
 if sum(ds)%2==0 and (bits>>(sum(ds)//2))&1:zum.append(d)
out[95]={'n':748,'sigma':sigma(748),'zumkeller_divisors':zum,'divisors':divisors(748)}
out[96]=firstdiff(lambda n:int(n%2 and len(factor(n))%2==0),lambda n:int(n%2 and len(factor(n))==2),2,1155)
out[97]=firstdiff(lambda n:len(str(n)),lambda n:len(splits(n)),0,120);out[97]['split_sums_120']=sorted(splits(120))
getcontext().prec=70;r=(1+Decimal(5).sqrt())/2
out[99]=firstdiff(lambda n:int((Decimal(n)+Decimal(1)/5)*r),lambda n:int(Decimal(n)*r+Decimal(1)/3),1,137)
out[100]={'n':144,'strict':countfact(144),'proper':countfact(144,True),'additional':list(set(countfact(144,True))-set(countfact(144)))}
out[101]=firstdiff(lambda n:int(lpf(sum(d for d in divisors(n) if d%2))>=lpf(n)),lambda n:int(any(p%2 and e>1 for p,e in factor(n).items())),2,153)
f={n:int(n%2 and omega(n)%2==0) for n in range(1,136)};g={1:1}
for n in range(2,136):g[n]=-sum(f[d]*g[n//d] for d in divisors(n) if d>1)
out[102]=firstdiff(lambda n:int(n%2 and omega(n)==2),lambda n:g[n]%2,2,135);out[102]['g135']=g[135]
out[103]=firstdiff(lambda n:math.prod(len(x) for x in bin(n)[2:].split('0') if x),lambda n:__import__('functools').reduce(clmul,(len(x) for x in bin(n)[2:].split('0') if x),1),0,119)
out[105]={'n':128,'exponent_binary':'111','alternating_sum':4-2+1,'a':2**(4-2+1),'b':1}
poly=[int(c) for c in bin(555)[2:][::-1]]; factorpoly=[1,-1,1]; rem=poly[:];quot=[0]*(len(poly)-2)
for i in range(len(poly)-1,1,-1):
 q=rem[i];quot[i-2]=q
 for j,v in enumerate(factorpoly):rem[i-2+j]-=q*v
out[106]={'n':555,'proper_divisors':divisors(555)[1:-1],'gf2_divisors':[d for d in divisors(555) if gfmod(555,d)==0],'factor_x_squared_minus_x_plus_1':all(v==0 for v in rem),'quotient_coefficients_low_to_high':quot}
out[107]={'k':225,'factor':factor(225),'sigma':sigma(225),'powerful_part':225,'a_membership':True,'b_membership':False}
out[108]={'k':256,'square_divisors':len([d for d in divisors(256) if math.isqrt(d)**2==d]),'exponent_base4':'20','b_membership':False}
def ua(n):return math.prod(1+p**e for p,e in factor(n).items())+math.prod(1+p for p in factor(n))>=2*n
def ub(n):
 ps=factor(n);q=next(p for p in primes if p not in ps)
 return n//math.prod(ps)<q
lista=[n for n in range(1,500) if ua(n)];listb=[n for n in range(1,500) if ub(n)]
out[109]=firstdiff(lambda n:lista[n-1],lambda n:listb[n-1],1,min(len(lista),len(listb)));out[109]['240']={'unitary_sigma':math.prod(1+p**e for p,e in factor(240).items()),'squarefree_sigma':math.prod(1+p for p in factor(240)),'m':8,'q':7}
getcontext().prec=170;x=(1+Decimal(101).sqrt())/10;y=Decimal(101).sqrt();xs=str(x).replace('.','');ys=str(y).replace('.','')
out[110]={'x':str(x)[:30],'y':str(y)[:30],'first_130_digits_match_after_two':xs[2:130]==ys[2:130],'relation':'10*x-1=y'}
Path('judge-evidence/reviews/86-110-independent-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
