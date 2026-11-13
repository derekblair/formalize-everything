# Coincidence-mining finalist packet
Top 60 candidate pairs from pass-2 scoring (agreement length x definition distance). Each entry: the two OEIS records. The sequences agree on every term in the OEIS listing.

## Candidate 1: A056594 vs A166698 (score 108.1, agree 94, variant abs, family size 9)
Terms: 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0

### A056594
```
%N A056594 Period 4: repeat [1,0,-1,0]; expansion of 1/(1 + x^2).
%C A056594 G.f. is inverse of cyclotomic(4,x). Unsigned: A000035(n+1).
%C A056594 Real part of i^n and imaginary part of i^(n+1), i=sqrt(-1). - _Reinhard Zumkeller_, Jul 22 2007
%C A056594 The BINOMIAL transform generates A009116(n); the inverse BINOMIAL transform generates (-1)^n*A009116(n). - _R. J. Mathar_, Apr 07 2008
%C A056594 a(n-1), n >= 1, is the nontrivial Dirichlet character modulo 4, called Chi_2(4;n) (the trivial one is Chi_1(4;n) given by periodic(1,0) = A000035(n)). See the Apostol reference, p. 139, the k = 4, phi(k) = 2 table. - _Wolfdieter Lang_, Jun 21 2011
%C A056594 a(n-1), n >= 1, is the character of the Dirichlet beta function. - _Daniel Forgues_, Sep 15 2012
%C A056594 a(n-1), n >= 1, is also the (strongly) multiplicative function h(n) of Theorem 5.12, p. 150, of the Niven-Zuckerman reference. See the formula section. This function h(n) can be employed to count the integer solutions to n = x^2 + y^2. See A002654 for a comment with the formula. - _Wolfdieter Lang_, Apr 19 2013
%C A056594 This sequence is duplicated in A101455 but with offset 1. - _Gary Detlefs_, Oct 04 2013
%C A056594 For n >= 2 this gives the determinant of the bipartite graph with 2*n nodes and the adjacency matrix A(n) with elements A(n;1,2) = 1 = A(n;n,n-1), and for 1 < i < n  A(n;i,i+1) = 1 = A(n;i,i-1), otherwise 0. - _Wolfdieter Lang_, Jun 25 2023
%F A056594 G.f.: 1/(1+x^2).
%F A056594 E.g.f.: cos(x).
%F A056594 a(n) = (1/2)*((-i)^n + i^n), where i = sqrt(-1). - _Mitch Harris_, Apr 19 2005
%F A056594 a(n) = (1/2)*((-1)^(n+floor(n/2)) + (-1)^floor(n/2)).
%F A056594 Recurrence: a(n)=a(n-4), a(0)=1, a(1)=0, a(2)=-1, a(3)=0.
%F A056594 a(n) = T(n, 0) = A053120(n, 0); T(n, x) Chebyshev polynomials of the first kind. - _Wolfdieter Lang_, Aug 21 2009
%F A056594 a(n) = S(n, 0) = A049310(n, 0); S(n, x) := U(n, x/2), Chebyshev polynomials of 2nd kind.
%F A056594 Sum_{k>=0} a(k)/(k+1) = Pi/4. - _Jaume Oliver Lafont_, Mar 30 2010
%F A056594 a(n) = Sum_{k=0..n} A101950(n,k)*(-1)^k. - _Philippe Deléham_, Feb 10 2012
%F A056594 a(n) = (1/2)*(1 + (-1)^n)*(-1)^(n/2). - _Bruno Berselli_, Mar 13 2012
%F A056594 a(0) = 1, a(n-1) = 0 if n is even, a(n-1) = Product_{j=1..m} (-1)^(e_j*(p_j-1)/2) if the odd n-1 = p_1^(e_1)*p_2^(e_2)*...*p_m^(e_m) with distinct odd primes p_j, j=1..m. See the function h(n) of Theorem 5.12 of the Niven-Zuckerman reference. - _Wolfdieter Lang_, Apr 19 2013
%F A056594 a(n) = (-4/(n+1)), n >= 0, where (k/n) is the Kronecker symbol. See the Eric Weisstein and Wikipedia links. Thanks to Wesley Ivan Hurt. - _Wolfdieter Lang_, May 31 2013
%F A056594 a(n) = R(n,0)/2 with the row polynomials R of A127672. This follows from the product of the zeros of R, and the formula Product_{k=0..n-1} 2*cos((2*k+1)*Pi/(2*n)) = (1 + (-1)^n)*(-1)^(n/2), n >= 1 (see the Gradstein and Ryshik reference, p. 63, 1.396 4., with x = sqrt(-1)). - _Wolfdieter Lang_, Oct 21 2013
%F A056594 a(n) = Sum_{k=0..n} i^(k*(k+1)), where i=sqrt(-1). - _Bruno Berselli_, Mar 11 2015
%F A056594 Dirichlet g.f. of a(n) shifted right: L(chi_2(4),s) = beta(s) = (1-2^(-s))*(d.g.f. of A034947), see comments by Lang and Forgues. - _Ralf Stephan_, Mar 27 2015
%F A056594 a(n) = cos(n*Pi/2). - _Ridouane Oudra_, Sep 29 2024
%F A056594 Additive with a(2) = -1, a(2^e) = 1 for e >= 2, and a(p^e) = 0 for an odd prime p. - _Amiram Eldar_, Oct 20 2026
%Y A056594 Cf. A049310, A131852, A002654, A146559 (binomial transform).
%K A056594 sign,easy,changed
%O A056594 0,1
```
### A166698
```
%N A166698 Totally multiplicative sequence with a(p) = a(p-1) - 1 for prime p.
%C A166698 From _Antti Karttunen_, Dec 30 2022: (Start)
%C A166698 Note the correspondences between four sequences:
%C A166698   A087003 --- abs ---> A323239
%C A166698      ^                    ^
%C A166698      |                    |
%C A166698     inv                  inv
%C A166698      |                    |
%C A166698      v                    v
%C A166698   A000035 <--- abs --- A166698 (this sequence)
%C A166698 Here inv means that the sequences are Dirichlet Inverses of each other, and abs means taking absolute values. (End)
%F A166698 Multiplicative with a(p^e) = (a(p-1)-1)^e.
%F A166698 If n = Product p(k)^e(k) then a(n) = Product (a(p(k)-1)-1)^e(k).
%F A166698 Multiplicative with a(p^e) = 0 if p = 2, with a(p^e) = 1 if p > 2 and e is even, with a(p^e) = -1 if p > 2 and e is odd.
%F A166698 a(p) = -1 for prime p > 2.
%F A166698 a(1) = 1, for k >= 1: a(2k) = 0, a(2k - 1) = 1 if A001222(2k - 1) is even, a(2k - 1) = -1 if A001222(2k - 1) is odd, where A001222(n) = bigomega(n).
%F A166698 Sum_{d|n} a(d) * A000012(d) = Sum_{d|n} a(d) * A000012(d/n) = A053866(n) = A093709(n) for n>= 1.
%F A166698 a(n) = A000035(n) * A008836(n). - _Antti Karttunen_, Sep 14 2017
%F A166698 From _Antti Karttunen_, Dec 19 & Dec 30 2022: (Start)
%F A166698 a(A003961(n)) = A008836(n).
%F A166698 a(n) = A353557(n) - A353558(n). (End)
%Y A166698 Cf. A000035 (absolute values), A001222, A003961, A008836, A323239 (Dirichlet inverse).
%Y A166698 Cf. A046337 (positions of positive terms), A067019 (of negative terms), A353557, A353558.
%Y A166698 Cf. also A358839, A359378.
%K A166698 sign,mult
%O A166698 1,1
```

## Candidate 2: A071936 vs A355437 (score 80.0, agree 116, variant abs, family size 233)
Terms: 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1

### A071936
```
%N A071936 K(n+1,n) where K(x,y) is the Kronecker symbol (x/y).
%F A071936 If n==2 (mod(8)) a(n)=-1 a(n)=1 otherwise
%K A071936 easy,sign
%O A071936 1,1
```
### A355437
```
%N A355437 a(n) is the sign of Maslanka's constant A(n).
%C A355437 In 1997 Krzysztof Maslanka published a rapidly converging series giving values of the zeta function which uses coefficients A(k), involving even powers of Pi.
%C A355437 The sum of all positive A(n) equals B=2.143505674422168409234504232295468835062643090089323...
%C A355437 The sum of all negative A(n) equals C=-1.643505674422168409234504232295468835062643090089323...
%C A355437 B+C = 1/2.
%F A355437 a(n) = sign(Sum_{j=0..n} (-1)^j*binomial(n, j)*(2*j + 1)*zeta(2*j + 2)).
%Y A355437 Cf. A114523, A114524, A354835.
%K A355437 sign
%O A355437 0
```

## Candidate 3: A307423 vs A355683 (score 74.5, agree 108, variant abs, family size 3)
Terms: 1, 0, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0

### A307423
```
%N A307423 Dirichlet g.f.: zeta(2*s) / zeta(3*s).
%C A307423 Dirichlet convolution of A212793 and A008836.
%F A307423 Multiplicative with a(p) = 0, and a(p^e) = (-1)^e for e >= 2. - _Amiram Eldar_, Dec 25 2022
%Y A307423 Cf. A008836, A010052, A056624, A212793, A307424.
%Y A307423 Cf. A112526 (absolute values).
%K A307423 sign,mult
%O A307423 1
```
### A355683
```
%N A355683 Multiplicative with a(p^e) = 0 if e=1 and a(p^e)= -1 if e>1.
%F A355683 a(n) = A076479(n) * A112526(n).
%Y A355683 Cf. A076479, A112526 (absolute values).
%K A355683 sign,mult
%O A355683 1
```

## Candidate 4: A116921 vs A173989 (score 74.0, agree 74, variant drop2, family size 2)
Terms: 0, 1, 1, 1, 2, 1, 3, 3, 4, 3, 5, 5, 6, 5, 7, 7, 8, 7, 9, 9, 10, 9, 11, 11, 12, 11, 13, 13, 14, 13

### A116921
```
%N A116921 a(n) = largest integer <= n/2 which is coprime to n.
%C A116921 a(n) + A116922(n) = n. For n>= 3, A116922(n) - a(n) is 1 if n is odd, is 2 if n is a multiple of 4 and is 4 if n is congruent to 2 (mod 4).
%C A116921 The arithmetic function v+-(n,2) as defined in A290988. - _Robert Price_, Aug 22 2017
%F A116921 For n >= 3, a(n) = (n-1)/2 if n is odd, a(n) = n/2 - 1 if n is a multiple of 4 and a(n) = n/2 - 2 if n is congruent to 2 (mod 4).
%F A116921 a(n) = (2*n-4-2*(-1)^n+(-1)^(n/2)+(-1)^(3*n/2))/4, n>2. - _Wesley Ivan Hurt_, May 26 2015
%F A116921 For n > 2, a(n) = (n-2+cos(n*Pi/2)-cos(n*Pi))/2. - _Wesley Ivan Hurt_, Oct 02 2017
%F A116921 G.f.: t^2*(1+t^3-2*t^4+2*t^5)/((1-t)*(1-t^4)). - _Mamuka Jibladze_, Aug 22 2019
%Y A116921 Cf. A116922, A290988.
%K A116921 easy,nonn
%O A116921 1,5
```
### A173989
```
%N A173989 a(n) is the 2-adic valuation of A173300(n).
%C A173989 Conjecture: always follows the pattern A, A, A+1, A, where A is an odd number.
%F A173989 a(n) = log(A173300(n))/log(2).
%F A173989 a(n) = A102302(n) for n >= 7. - conjectured by _Hugo Pfoertner_, Oct 10 2018; proved by _Max Alekseyev_, Mar 16 2026
%F A173989 a(n) = A116921(n) for n>=3. - conjectured by _R. J. Mathar_, Aug 29 2025; proved by _Max Alekseyev_, Mar 16 2026
%F A173989 Conjectured by _Colin Barker_, Oct 10 2018; proved by _Max Alekseyev_, Mar 16 2026: (Start)
%F A173989 G.f.: x^3*(1 + x^2 - x^3 + x^4) / ((1 - x)^2*(1 + x)*(1 + x^2)).
%F A173989 a(n) = a(n-1) + a(n-4) - a(n-5) for n > 7. (End)
%Y A173989 Cf. A102302, A173300.
%K A173989 nonn,easy
%O A173989 1,5
```

## Candidate 5: A107820 vs A242963 (score 73.6, agree 64, variant drop2, family size 5)
Terms: 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35

### A107820
```
%N A107820 a(1)=3, a(2)=5; thereafter a(n) = n+5.
%C A107820 The old definition (which does not fit the sequence) was "Slowest increasing sequence where a(n)-n is prime".
%F A107820 G.f.: -x*(2*x^3 - x^2 + x - 3)/(x - 1)^2. - _Jinyuan Wang_, Apr 10 2020
%K A107820 nonn,easy,less
%O A107820 1,1
```
### A242963
```
%N A242963 Numbers n such that A242962(n) = sigma(n) = A000203(n).
%C A242963 A242962(n) = (n*(n+1)/2) mod antisigma(n) = A000217(n) mod A024816(n).
%C A242963 Union of number 5 and numbers >= 7.
%C A242963 Conjecture: this sequence lists all the positive integers n such that, for some integer k, (sin(k*Pi/n))^2 is irrational. - _Lorenzo Sauras Altuzarra_, Jan 27 2020
%Y A242963 Cf. A000203, A000217, A002961, A024816, A242962, A243117, A243118, A217290, A009005.
%K A242963 nonn
%O A242963 1,1
```

## Candidate 6: A326801 vs A326802 (score 72.6, agree 121, variant abs, family size 2)
Terms: 1, -1, -1, 0, 1, 0, 0, 1, 0, -1, 0, 8, 8, 0, -1, 0, 1, 0, -24, 0, 0, -24, 0, 1, 0, -1, 0, 48, 0, -576

### A326801
```
%N A326801 Consider the e.g.f. C(x,y) = sqrt(1/2) * Sum_{n>=0} Sum_{k=0..2*n} T(n,k) * x^(2*n-k) * y^k / ((2*n-k)!*k!) and related functions S(x,y) and D(x,y), as defined in the Formula section. Sequence gives the triangular array of coefficients T(n,k) (n>=0, 0<=k<=2*n) of C(x,y).
%F A326801 The e.g.f. Cx = C(x,y) and related functions Sx = S(x,y), Dx = D(x,y), Sy = S(y,x), Cy = C(y,x), and Dy = D(y,x) satisfy the following relations.
%F A326801 DEFINITION.
%F A326801 (1a) Sx =             Integral Cx*Dy + Cy*Dx dx,
%F A326801 (1b) Cx = sqrt(1/2) - Integral Sx*Dy + Sy*Dx dx,
%F A326801 (1c) Dx = sqrt(1/2) - Integral Sx*Cy - Sy*Cx dx,
%F A326801 (2a) Sy =             Integral Cy*Dx + Cx*Dy dy,
%F A326801 (2b) Cy = sqrt(1/2) - Integral Sy*Dx + Sx*Dy dy,
%F A326801 (2c) Dy = sqrt(1/2) - Integral Sy*Cx - Sx*Cy dy.
%F A326801 IDENTITIES.
%F A326801 (3a) Dx^2 + Cx^2 + Sx^2 = 1.
%F A326801 (3b) Dy^2 + Cy^2 + Sy^2 = 1.
%F A326801 (4a) Dx*(d/dx Dx) + Cx*(d/dx Cx) + Sx*(d/dx Sx) = 0.
%F A326801 (4b) Dy*(d/dy Dy) + Cy*(d/dy Cy) + Sy*(d/dy Sy) = 0.
%F A326801 (4c) Dy*(d/dx Dx) - Cy*(d/dx Cx) - Sy*(d/dx Sx) = 0.
%F A326801 (4d) Dx*(d/dy Dy) - Cx*(d/dy Cy) - Sx*(d/dy Sy) = 0.
%F A326801 (5a) (Dx*Dy - Cx*Cy - Sx*Sy)^2 + (d/dx Dx)^2 + (d/dx Cx)^2 + (d/dx Sx)^2 = 1.
%F A326801 (5b) (Dx*Dy - Cx*Cy - Sx*Sy)^2 + (d/dy Dy)^2 + (d/dy Cy)^2 + (d/dy Sy)^2 = 1.
%F A326801 RELATED FUNCTIONS.
%F A326801 (6a) SS(x*y) = Dx*Dy - Cx*Cy - Sx*Sy.
%F A326801 (6b) d/dx SS(x*y) = Dx*(d/dx Dy) - Cx*(d/dx Cy) - Sx*(d/dx Sy).
%F A326801 (6c) d/dy SS(x*y) = Dy*(d/dy Dx) - Cy*(d/dy Cx) - Sy*(d/dy Sx).
%F A326801 (7a) CC(x*y)^2 = (Cx*Dy + Cy*Dx)^2 + (Sx*Dy + Sy*Dx)^2 + (Sx*Cy - Sy*Cx)^2.
%F A326801 (7b) CC(x*y)^2 = (d/dx Dx)^2 + (d/dx Cx)^2 + (d/dx Sx)^2.
%F A326801 (7c) CC(x*y)^2 = (d/dy Dy)^2 + (d/dy Cy)^2 + (d/dy Sy)^2.
%F A326801 In the above, CC(x) and SS(x) are the e.g.f.s of A326551 and A326552 defined by
%F A326801 (8a) CC(x*y)^2 + SS(x*y)^2 = 1,
%F A326801 (8b) SS(x*y) =     Integral CC(x*y) * (Integral CC(x*y) dy) dx,
%F A326801 (8c) CC(x*y) = 1 - Integral SS(x*y) * (Integral CC(x*y) dy) dx,
%F A326801 (8d) SS(x*y) = sin( Integral Integral CC(x*y) dx dy ),
%F A326801 (8e) CC(x*y) = cos( Integral Integral CC(x*y) dx dy ).
%F A326801 DERIVATIVES.
%F A326801 (9a) d/dx Sx =  Cx*Dy + Cy*Dx.
%F A326801 (9b) d/dx Cx = -Sx*Dy - Sy*Dx.
%F A326801 (9c) d/dx Dx = -Sx*Cy + Sy*Cx.
%F A326801 (9d) d/dy Sy =  Sy*Dx + Sx*Dy.
%F A326801 (9e) d/dy Cy = -Sy*Dx - Sx*Dy.
%F A326801 (9f) d/dy Dy = -Sy*Cx + Sx*Cy.
%Y A326801 Cf. A326800 (Sx), A326802 (Dx), A326551 (CC), A326552 (SS).
%K A326801 sign,tabf
%O A326801 0,12
```
### A326802
```
%N A326802 Consider the e.g.f. D(x,y) = sqrt(1/2) * Sum_{n>=0} Sum_{k=0..2*n} T(n,k) * x^(2*n-k) * y^k / ((2*n-k)!*k!) and related functions S(x,y) and C(x,y), as defined in the Formula section. Sequence gives the triangular array of coefficients T(n,k) (n>=0, 0<=k<=2*n) of D(x,y).
%F A326802 The e.g.f. Dx = D(x,y) and related functions Sx = S(x,y), Cx = C(x,y), Sy = S(y,x), Cy = C(y,x), and Dy = D(y,x) satisfy the following relations.
%F A326802 DEFINITION.
%F A326802 (1a) Sx =             Integral Cx*Dy + Cy*Dx dx,
%F A326802 (1b) Cx = sqrt(1/2) - Integral Sx*Dy + Sy*Dx dx,
%F A326802 (1c) Dx = sqrt(1/2) - Integral Sx*Cy - Sy*Cx dx,
%F A326802 (2a) Sy =             Integral Cy*Dx + Cx*Dy dy,
%F A326802 (2b) Cy = sqrt(1/2) - Integral Sy*Dx + Sx*Dy dy,
%F A326802 (2c) Dy = sqrt(1/2) - Integral Sy*Cx - Sx*Cy dy.
%F A326802 IDENTITIES.
%F A326802 (3a) Dx^2 + Cx^2 + Sx^2 = 1.
%F A326802 (3b) Dy^2 + Cy^2 + Sy^2 = 1.
%F A326802 (4a) Dx*(d/dx Dx) + Cx*(d/dx Cx) + Sx*(d/dx Sx) = 0.
%F A326802 (4b) Dy*(d/dy Dy) + Cy*(d/dy Cy) + Sy*(d/dy Sy) = 0.
%F A326802 (4c) Dy*(d/dx Dx) - Cy*(d/dx Cx) - Sy*(d/dx Sx) = 0.
%F A326802 (4d) Dx*(d/dy Dy) - Cx*(d/dy Cy) - Sx*(d/dy Sy) = 0.
%F A326802 (5a) (Dx*Dy - Cx*Cy - Sx*Sy)^2 + (d/dx Dx)^2 + (d/dx Cx)^2 + (d/dx Sx)^2 = 1.
%F A326802 (5b) (Dx*Dy - Cx*Cy - Sx*Sy)^2 + (d/dy Dy)^2 + (d/dy Cy)^2 + (d/dy Sy)^2 = 1.
%F A326802 RELATED FUNCTIONS.
%F A326802 (6a) SS(x*y) = Dx*Dy - Cx*Cy - Sx*Sy.
%F A326802 (6b) d/dx SS(x*y) = Dx*(d/dx Dy) - Cx*(d/dx Cy) - Sx*(d/dx Sy).
%F A326802 (6c) d/dy SS(x*y) = Dy*(d/dy Dx) - Cy*(d/dy Cx) - Sy*(d/dy Sx).
%F A326802 (7a) CC(x*y)^2 = (Cx*Dy + Cy*Dx)^2 + (Sx*Dy + Sy*Dx)^2 + (Sx*Cy - Sy*Cx)^2.
%F A326802 (7b) CC(x*y)^2 = (d/dx Dx)^2 + (d/dx Cx)^2 + (d/dx Sx)^2.
%F A326802 (7c) CC(x*y)^2 = (d/dy Dy)^2 + (d/dy Cy)^2 + (d/dy Sy)^2.
%F A326802 In the above, CC(x) and SS(x) are the e.g.f.s of A326551 and A326552 defined by
%F A326802 (8a) CC(x*y)^2 + SS(x*y)^2 = 1,
%F A326802 (8b) SS(x*y) =     Integral CC(x*y) * (Integral CC(x*y) dy) dx,
%F A326802 (8c) CC(x*y) = 1 - Integral SS(x*y) * (Integral CC(x*y) dy) dx,
%F A326802 (8d) SS(x*y) = sin( Integral Integral CC(x*y) dx dy ),
%F A326802 (8e) CC(x*y) = cos( Integral Integral CC(x*y) dx dy ).
%F A326802 DERIVATIVES.
%F A326802 (9a) d/dx Sx =  Cx*Dy + Cy*Dx.
%F A326802 (9b) d/dx Cx = -Sx*Dy - Sy*Dx.
%F A326802 (9c) d/dx Dx = -Sx*Cy + Sy*Cx.
%F A326802 (9d) d/dy Sy =  Sy*Dx + Sx*Dy.
%F A326802 (9e) d/dy Cy = -Sy*Dx - Sx*Dy.
%F A326802 (9f) d/dy Dy = -Sy*Cx + Sx*Cy.
%Y A326802 Cf. A326800 (Sx), A326801 (Cx), A326551 (CC), A326552 (SS).
%K A326802 sign,tabf
%O A326802 0,12
```

## Candidate 7: A156752 vs A165020 (score 71.8, agree 104, variant drop1, family size 4)
Terms: 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3

### A156752
```
%N A156752 a(n) = floor(Catalan(n+1)/Catalan(n)).
%C A156752 Decimal expansion of 3667/30000. - _Elmo R. Oliveira_, May 05 2024
%F A156752 a(n) = floor(A000108(n+1)/A000108(n)).
%F A156752 G.f.: (1+x+x^4)/(1-x).
%F A156752 a(0)=1, a(1) = a(2) = a(3) = 2, a(n) = 3 for n>3.
%F A156752 E.g.f.: 3*exp(x) - 2 - x - x^2/2 - x^3/6. - _Elmo R. Oliveira_, Aug 09 2024
%F A156752 a(n) = floor(4^(n/(n+1))). - _Aaron J Grech_, Aug 30 2024
%Y A156752 Cf. A000108, A010701.
%K A156752 nonn,easy
%O A156752 0,2
```
### A165020
```
%N A165020 Length of cycle mentioned in A165019.
%Y A165020 Cf. A165012, A165019, A165018, A165022, A165024, A165031.
%Y A165020 In other bases: Empty (base 2), A165001 (base 3), A165040 (base 5), A165059 (base 6), A165079 (base 7), A165098 (base 8), A165118 (base 9), A164715 (base 10).
%K A165020 base,nonn
%O A165020 1,1
```

## Candidate 8: A001222 vs A086436 (score 69.7, agree 101, variant drop1, family size 33)
Terms: 0, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2, 1, 4, 2, 2, 3, 3, 1, 3

### A001222
```
%N A001222 Number of prime divisors of n counted with multiplicity (also called big omega of n, bigomega(n) or Omega(n)).
%C A001222 Maximal number of terms in any factorization of n.
%C A001222 Number of prime powers (not including 1) that divide n.
%C A001222 Sum of exponents in prime-power factorization of n. - _Daniel Forgues_, Mar 29 2009
%C A001222 Sum_{d|n} 2^(-A001221(d) - a(n/d)) = Sum_{d|n} 2^(-a(d) - A001221(n/d)) = 1 (see Dressler and van de Lune link). - _Michel Marcus_, Dec 18 2012
%C A001222 Row sums in A067255. - _Reinhard Zumkeller_, Jun 11 2013
%C A001222 Conjecture: Let f(n) = (x+y)^a(n), and g(n) = x^a(n), and h(n) = (x+y)^A046660(n) * y^A001221(n) with x, y complex numbers and 0^0 = 1. Then f(n) = Sum_{d|n} g(d)*h(n/d). This is proved for x = 1-y (see Dressler and van de Lune link). - _Werner Schulte_, Feb 10 2018
%C A001222 Let r, s be some fixed integers. Then we have:
%C A001222   (1) The sequence b(n) = Dirichlet convolution of r^bigomega(n) and s^bigomega(n) is multiplicative with b(p^e) = (r^(e+1)-s^(e+1))/(r-s) for prime p and e >= 0. The case r = s leads to b(p^e) = (e+1)*r^e.
%C A001222   (2) The sequence c(n) = Dirichlet convolution of r^bigomega(n) and mu(n)*s^bigomega(n) is multiplicative with c(p^e) = (r-s)*r^(e-1) and c(1) = 1 for prime p and e > 0 where mu(n) = A008683(n). - _Werner Schulte_, Feb 20 2019
%C A001222 a(n) is also the length of the composition series for every solvable group of order n. - _Miles Englezou_, Apr 25 2024
%F A001222 n = Product_(p_j^k_j) -> a(n) = Sum_(k_j).
%F A001222 Dirichlet g.f.: ppzeta(s)*zeta(s). Here ppzeta(s) = Sum_{p prime} Sum_{k>=1} 1/(p^k)^s. Note that ppzeta(s) = Sum_{p prime} 1/(p^s-1) and ppzeta(s) = Sum_{k>=1} primezeta(k*s). - _Franklin T. Adams-Watters_, Sep 11 2005
%F A001222 Totally additive with a(p) = 1.
%F A001222 a(n) = if n=1 then 0 else a(n/A020639(n)) + 1. - _Reinhard Zumkeller_, Feb 25 2008
%F A001222 a(n) = Sum_{k=1..A001221(n)} A124010(n,k). - _Reinhard Zumkeller_, Aug 27 2011
%F A001222 a(n) = A022559(n) - A022559(n-1).
%F A001222 G.f.: Sum_{p prime, k>=1} x^(p^k)/(1 - x^(p^k)). - _Ilya Gutkovskiy_, Jan 25 2017
%F A001222 a(n) = A091222(A091202(n)) = A000120(A156552(n)). - _Antti Karttunen_, circa 2004 and Mar 06 2017
%F A001222 a(n) >= A267116(n) >= A268387(n). - _Antti Karttunen_, Apr 12 2017
%F A001222 Sum_{k=1..n} 2^(-A001221(gcd(n,k)) - a(n/gcd(n,k)))/phi(n/gcd(n,k)) = Sum_{k=1..n} 2^(-a(gcd(n,k)) - A001221(n/gcd(n,k)))/phi(n/gcd(n,k)) = 1, where phi = A000010. - _Richard L. Ollerton_, May 13 2021
%F A001222 a(n) = a(A046523(n)) = A007814(A108951(n)) = A061395(A122111(n)) = A056239(A181819(n)) = A048675(A293442(n)). - _Antti Karttunen_, Apr 30 2022
%Y A001222 Cf. A001221 (omega, primes counted without multiplicity), A008836 (Liouville's lambda, equal to (-1)^a(n)), A046660, A144494, A074946, A134334.
%Y A001222 Bisections give A091304 and A073093. A086436 is essentially the same sequence. Cf. A022559 (partial sums), A066829 (parity), A092248 (parity of omega).
%Y A001222 Sequences listing n such that a(n) = r: A000040 (r = 1), A001358 (r = 2), A014612 (r = 3), A014613 (r = 4), A014614 (r = 5), A046306 (r = 6), A046308 (r = 7), A046310 (r = 8), A046312 (r = 9), A046314 (r = 10), A069272 (r = 11), A069273 (r = 12), A069274 (r = 13),  A069275 (r = 14),  A069276 (r = 15),  A069277 (r = 16),  A069278 (r = 17),  A069279 (r = 18),  A069280 (r = 19),  A069281 (r = 20). - _Jason Kimberley_, Oct 02 2011
%Y A001222 Cf. A079149 (primes adj. to integers with at most 2 prime factors, a(n)<=2).
%Y A001222 Cf. A000120, A020639, A091202, A091222, A156552, A267116, A268387.
%Y A001222 Cf. A027748 (without repetition).
%Y A001222 Cf. A000010.
%K A001222 nonn,easy,nice,core,changed
%O A001222 1,4
```
### A086436
```
%N A086436 Maximum number of parts possible in a factorization of n; a(1) = 1, and for n > 1, a(n) = A001222(n) = bigomega(n).
%C A086436 Incorrect (a(1)=0, not 1 as given here) duplicate of A001222. - _Joerg Arndt_, Jul 22 2017
%Y A086436 Essentially the same as A001222.
%K A086436 nonn
%O A086436 1,4
```

## Candidate 9: A069159 vs A306389 (score 69.0, agree 69, variant abs, family size 2)
Terms: 3, 2, 6, 5, 10, 1, 3, -3, 2, -1, 4, -4, 5, -2, 7, 4, 6, 3, 11, 7, 13, 11, 17, 13, 16, 13, 21, 18, 20, 13

### A069159
```
%N A069159 a(n) = d(1) - d(2) + d(3) - d(4) + ... + (-1)^(n+1) d(n), where d(k) denotes the k-th term of the digit sequence 3, 1, 4, 1, 5, 9,.... of Pi.
%F A069159 a(1) = d(1) = 3; a(n) = a(n-1) + (-1)^(n+1) d(n) for n > 1.
%Y A069159 Cf. A000796 (Pi).
%K A069159 base,easy,sign
%O A069159 1,1
```
### A306389
```
%N A306389 Partial sums of (k-th digit of decimal expansion of Pi multiplied by (-1)^k).
%C A306389 a(n) > 0 for n = 8, 10, 12, 14, 16124, 16126, ... and a(n) = 0 for n = 16120, 16161, 16937, ... - _Michel Marcus_, Feb 13 2019
%F A306389 a(n) = Sum_{k=1..n} (-1)^k*A000796(k).
%F A306389 a(n) = Sum_{k=1..floor(n/2)} A099817(k) - Sum_{k=1..floor((n+1)/2)} A099816(k). - _Michel Marcus_, Feb 16 2019
%Y A306389 Cf. A000796, A046974, A099816, A099817.
%K A306389 sign,base,easy
%O A306389 1,1
```

## Candidate 10: A053139 vs A127705 (score 67.0, agree 67, variant drop1, family size 2)
Terms: 0, 2, 3, 2, 5, 1, 7, 4, 6, 3, 11, 4, 13, 5, 7, 8, 17, 6, 19, 8, 11, 9, 23, 8, 20, 11, 18, 12, 29, 9

### A053139
```
%N A053139 a(n) = phi(n) - mu(n).
%F A053139 a(n) = n if and only if n is a prime.
%F A053139 Product_{n>=1} (1 - 1/phi^n)^(-a(n)/n) = e, where phi is the golden ratio (A001622) (Schneider, 2014). - _Amiram Eldar_, Jun 11 2022
%Y A053139 Cf. A000010, A008683.
%Y A053139 Cf. A001113, A001622.
%K A053139 nonn
%O A053139 1,2
```
### A127705
```
%N A127705 a(n) = mu(n) + Sum_{k|n, k>1} (k+1)*mu(n/k), where mu = A008683.
%C A127705 Previous name: Row sums of A127704.
%C A127705 From _Robert Israel_, Dec 29 2016: (Start)
%C A127705 a(n) = n if and only if n is in A008578.
%C A127705 a(p^j) = p^j - p^(j-1) if p is prime and j >= 2.
%C A127705 a(Product_{i=1..k} p_i) = Product_{i=1..k} (p_i-1) - (-1)^k if p_1, ..., p_k are distinct primes. (End)
%F A127705 a(n) = mu(n) + Sum_{k|n,k>1} (k+1)*mu(n/k), where mu = A008683. - _Robert Israel_, Dec 29 2016
%F A127705 a(n) = A053139(n) if n>1. - _R. J. Mathar_, May 17 2026
%Y A127705 Cf. A008578, A008683, A054525, A127701, A127704.
%K A127705 nonn
%O A127705 1,2
```

## Candidate 11: A171905 vs A179184 (score 66.9, agree 97, variant drop2, family size 4)
Terms: 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1

### A171905
```
%N A171905 a(1) = 1 and a(2) = 2, a(n) = |(sum of previous terms) - n|.
%K A171905 easy,nonn
%O A171905 1,2
```
### A179184
```
%N A179184 Number of connected 2-regular simple graphs with n vertices.
%C A179184 All simple graphs have girth at least 3. Acyclic graphs have infinite girth.
%C A179184 Decimal expansion of 901/9000. - _Elmo R. Oliveira_, May 28 2024
%F A179184 a(0)=1; for 0 < n < 3 a(n)=0; for n >= 3, a(n)=1.
%F A179184 Proof: The null graph is vacuously 2-regular. There are no 2-regular simple graphs with 1 or 2 vertices. The n-cycle has girth n. QED.
%F A179184 G.f.: (x^3-x+1)/(1-x). - _Elmo R. Oliveira_, May 28 2024
%Y A179184 2-regular simple graphs (with girth at least 3): this sequence (connected), A165652 (disconnected), A008483 (not necessarily connected).
%Y A179184 2-regular connected: this sequence (simple graphs), A000012 (multigraphs with loops allowed).
%Y A179184 Connected regular simple graphs: A005177 (any degree), A068934 (triangular array), specified degree k: this sequence (k=2), A002851 (k=3), A006820 (k=4),A006821 (k=5), A006822 (k=6), A014377 (k=7), A014378 (k=8), A014381 (k=9), A014382 (k=10), A014384 (k=11).
%Y A179184 Connected 2-regular simple graphs with girth at least g: this sequence (g=3), A185115 (g=4), A185115 (g=5), A185116 (g=6), A185117 (g=7), A185118 (g=8), A185119 (g=9).
%Y A179184 Connected 2-regular simple graphs with girth exactly g: A185013 (g=3), A185014 (g=4), A185015 (g=5), A185016 (g=6), A185017 (g=7), A185018 (g=8).
%K A179184 nonn,easy
%O A179184 0
```

## Candidate 12: A317788 vs A370046 (score 65.0, agree 65, variant drop2, family size 2)
Terms: 2, 1, 3, 6, 4, 8, 12, 9, 5, 18, 17, 10, 7, 19, 14, 16, 11, 20, 13, 24, 22, 15, 32, 36, 34, 25, 23, 37, 27, 21

### A317788
```
%N A317788 Lexicographically earliest infinite sequence of distinct positive terms such that for any n > 1, the binary representation of a(n) appears as a substring in the binary representation of Sum_{k=1..n-1} a(k).
%C A317788 The sequence must start with a(1) = 2 in order to be infinite, and for any n > 1, a(n) <= Sum_{k=1..n-1} a(k).
%C A317788 This sequence has similarities with A160855.
%Y A317788 Cf. A160855.
%K A317788 nonn,base
%O A317788 1,1
```
### A370046
```
%N A370046 a(1) = 1, a(2) = 2; for n > 2, a(n) is the smallest unused positive number whose binary value is a substring of the binary value of the sum of all previous terms.
%C A370046 The fixed points begin 1, 2, 3, 16, 39, 42, 50, 79, 120, 361, although it is likely there are infinitely more. The sequence is conjectured to be a permutation of the positive numbers.
%F A370046 a(n) = A317788(n) for any n >= 3. - _Rémy Sigrist_, Feb 09 2024
%Y A370046 Cf. A317788, A369899 (base 10), A363186, A333410.
%K A370046 nonn,base
%O A370046 1,2
```

## Candidate 13: A112299 vs A358839 (score 63.0, agree 105, variant abs, family size 2)
Terms: 1, -1, -1, 0, 1, 1, -1, 0, 1, -1, -1, 0, 1, 1, -1, 0, 1, -1, -1, 0, 1, 1, -1, 0, 1, -1, -1, 0, 1, 1

### A112299
```
%N A112299 Expansion of x * (1 - x) * (1 - x^2) * (1 - x^3) / (1 - x^8) in powers of x.
%C A112299 Periodic with period length 8.
%C A112299 Sum_{k>=1} a(k)/k = Pi/8. - _Jaume Oliver Lafont_, Oct 20 2009
%F A112299 Euler transform of length 8 sequence [-1, -1, -1, 0, 0, 0, 0, 1].
%F A112299 Multiplicative with a(2) = -1, a(2^e) = 0 if e>1, a(p^e) = 1 if p == 1 (mod 4), a(p^e) = (-1)^e if p == 3 (mod 4).
%F A112299 G.f.: x * (1 + x + x^2) * (1 - x)^2 / ((1 + x^2) * (1 + x^4)).
%F A112299 G.f.: f(x) - f(x^2) where f(x) := x / (1 + x^2). - _Michael Somos_, Jun 19 2015
%F A112299 a(n) = -a(4 - n) = a(n + 8) for all n in Z. a(4*n) = 0.
%F A112299 a(2*n) = - A056594(n-1). a(2*n + 1) = A033999(n). a(4*n + 1) = 1. a(4*n + 3) = -1. a(4*n + 2) = - A033999(n). - _Michael Somos_, Jun 19 2015
%F A112299 a(n) = A257196(n) unless n=0. - _Michael Somos_, Sep 01 2015
%Y A112299 Cf. A033999, A056594, A257196.
%K A112299 sign,mult,easy
%O A112299 1,1
```
### A358839
```
%N A358839 Dirichlet inverse of A353627, the characteristic function of the squarefree numbers multiplied by binary powers.
%C A358839 Note the correspondences between four sequences:
%C A358839   A355689 --- abs ---> A353627
%C A358839      ^                    ^
%C A358839      |                    |
%C A358839     inv                  inv
%C A358839      |                    |
%C A358839      v                    v
%C A358839   A166486 <--- abs --- A358839 (this sequence)
%C A358839 Here inv means that the sequences are Dirichlet Inverses of each other, and abs means taking absolute values.
%F A358839 Multiplicative with a(p^e) = (-1)^e for odd primes p, and a(2^e) = -1 if e = 1, otherwise 0.
%F A358839 For all e >= 0, a(2^e) = A008683(2^e).
%F A358839 For all n >= 0, a(2n+1) = A008836(2n+1).
%F A358839 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A353627(n/d) * a(d).
%F A358839 a(n) = A359370(n) - A359372(n).
%F A358839 Dirichlet g.f.: (1-1/4^s)*zeta(2*s)/zeta(s). - _Amiram Eldar_, Jan 01 2023
%Y A358839 Cf. A008683, A008836.
%Y A358839 Cf. A166486 (absolute values), A353627 (Dirichlet inverse), A355689 (Dirichlet inverse of the absolute values).
%Y A358839 Cf. A008586 (after its initial term gives the positions of 0's), A359371 (positive terms), A359373 (negative terms), A359370, A359372.
%Y A358839 Cf. also A166698, A359378.
%K A358839 sign,mult
%O A358839 1
```

## Candidate 14: A029883 vs A089045 (score 63.0, agree 105, variant abs, family size 2)
Terms: 1, 0, -1, 1, -1, 0, 1, 0, -1, 0, 1, -1, 1, 0, -1, 1, -1, 0, 1, -1, 1, 0, -1, 0, 1, 0, -1, 1, -1, 0

### A029883
```
%N A029883 First differences of Thue-Morse sequence A001285.
%C A029883 Also first differences of {0,1} Thue-Morse sequence A010060.- _N. J. A. Sloane_, Jan 05 2021
%C A029883 Fixed point of the morphism a->abc, b->ac, c->b, with a = 1, b = 0, c = -1, starting with a(1) = 1. - _Philippe Deléham_
%C A029883 From _Thomas Anton_, Sep 22 2020: (Start)
%C A029883 This sequence, interpreted as an infinite word, is squarefree.
%C A029883 Let & represent concatenation. For a word w of integers, let -w be the same word with each symbol negated. Then, starting with the empty word, this sequence can be obtained by iteratively applying the transformation T(w) = w & 1 & -w & 0 & -w & -1 & w. (End)
%F A029883 Recurrence: a(4*n) = a(n), a(4*n+1) = a(2*n+1), a(4*n+2) = 0, a(4*n+3) = -a(2*n+1), starting a(1) = 1.
%F A029883 a(n) = 2 - A007413(n). a(A036554(n)) = 0; a(A091785(n)) = -1; a(A091855(n)) = 1. - _Philippe Deléham_, Mar 20 2004
%F A029883 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^4)) where f(u, v, w) = -v+w+u^2-v^2+2*w^2-2*u*w. - _Michael Somos_, Jul 08 2004
%Y A029883 Apart from signs, same as A035263. Cf. A001285, A010060, A036554, A091785, A091855.
%Y A029883 a(n+1) = A036577(n) - 1 = A036585(n) - 2.
%K A029883 sign,easy
%O A029883 1,1
```
### A089045
```
%N A089045 a(n) = a(n-1) + (-1)^floor(n/2)*a(floor(n/2)) with a(1) = 1.
%F A089045 abs(a(n)) = A035263(n).
%Y A089045 Cf. A001511, A035263.
%K A089045 sign
%O A089045 1,1
```

## Candidate 15: A159684 vs A188037 (score 62.4, agree 104, variant stripz, family size 2)
Terms: 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0

### A159684
```
%N A159684 Sturmian word: limit S(infinity) where S(0) = 0, S(1) = 0,1 and for n>=1, S(n+1) = S(n)S(n)S(n-1).
%C A159684 Fixed point of morphism 0 -> 0,1; 1 -> 0,1,0.
%C A159684 This sequence corresponds to the case k = 1 of the Sturmian word S_k(infinity) as defined in A080764. See A171588 for the case k = 2. - _Peter Bala_, Nov 22 2013
%C A159684 This sequence is the {1->01}-transform of the Sturmian word A080764.  - _Clark Kimberling_, May 17 2017
%C A159684 Also, sequence (1 if x/sqrt(2) is integer, 0 else) as x runs over the elements of N U N*sqrt(2) in increasing order, N = {0, 1, 2, ...}. See A144612 for the sqrt(3) analog. - _M. F. Hasler_, Feb 06 2025
%F A159684 From _Peter Bala_, Nov 22 2013: (Start)
%F A159684 a(n) = floor((n + 2)*(sqrt(2) - 1)) - floor((n + 1)*(sqrt(2) - 1)).
%F A159684 If we read the sequence as the decimal constant C = 0.01010 01010 01010 10010 10010 ... then C = sum {n >= 1} 1/10^floor(n*(1 + sqrt(2))).
%F A159684 The real number 9*C has the simple continued fraction expansion [0; 11, 1010, 10000100, 100000000000100000, 100000000000000000000000000001000000000000, ...], the partial quotients having the form 10^Pell(n)*(1 + 10^Pell(n+1)) = 10^A001333(n+1) + 10^A000129(n) (see Adams and Davison).
%F A159684 A rapidly converging series for C is C = 9*sum {n >= 1} 10^Pell(2*n-1)*(1 + 10^Pell(2*n))/( (10^Pell(2*n-1) - 1)*(10^Pell(2*n+1) - 1) ): for example, the first 10 terms of the series give a rational approximation to C accurate to more than 130 million decimal places. Compare with the Fibonacci words A005614 and A221150. (End)
%Y A159684 See A188037 for another version of this sequence. - _N. J. A. Sloane_, Mar 22 2011
%Y A159684 Cf. A000129, A001333, A005614, A080764, A119812, A171588, A221150, A221151, A221152, A096270.
%Y A159684 The following sequences are all essentially the same, in the sense that they are simple transformations of each other, with A003151 as the parent: A003151, A001951, A001952, A003152, A006337, A080763, A082844 (conjectured), A097509, A159684, A188037, A245219 (conjectured), A276862. - _N. J. A. Sloane_, Mar 09 2021
%K A159684 nonn,easy
%O A159684 0,1
```
### A188037
```
%N A188037 a(n) = floor(n*r) - 1 - floor((n-1)*r), where r = sqrt(2).
%C A188037 Is this A159684 with an additional 0 in front? - _R. J. Mathar_, Mar 20 2011
%C A188037 The answer is yes, since it follows right from the definitions of the sequences that (a(n)) is equal to A159684 with a different offset. - _Michel Dekking_, Jan 31 2017
%C A188037 Sturmian word of slope sqrt(2)-1. - _Philippe Schnoebelen_, Aug 25 2025
%F A188037 a(n) = floor(n*r) - floor(r) - floor(n*r - r), where r = sqrt(2).
%Y A188037 Cf. A080754, A083088, A188014, A188037, A188038.
%Y A188037 A159684 is an essentially identical sequence.
%Y A188037 The following sequences are all essentially the same, in the sense that they are simple transformations of each other, with A003151 as the parent: A003151, A001951, A001952, A003152, A006337, A080763, A082844 (conjectured), A097509, A159684, A188037, A245219 (conjectured), A276862. - _N. J. A. Sloane_, Mar 09 2021
%K A188037 nonn,easy
%O A188037 1
```

## Candidate 16: A088568 vs A294448 (score 62.1, agree 90, variant abs, family size 5)
Terms: 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, -2, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0

### A088568
```
%N A088568 3*n - 2*(partial sums of Kolakoski sequence A000002).
%C A088568 It is conjectured that a(n) = o(n).
%C A088568 It is conjectured that the density of 1's and that of 2's in the Kolakoski sequence A000002 are equal to 1/2. The deficit of 2's in the Kolakoski sequence at rank n being defined as n/2 - number of 2's in the Kolakoski word of length n, a(n) is equal to twice the deficit of 2's (or twice the excess of 1's). Equivalently, the number of 2's up to rank n in the Kolakoski sequence is (n - a(n))/2. - _Jean-Christophe Hervé_, Oct 05 2014
%C A088568 The conjecture about the densities of 1's and 2's is equivalent to a(n) = o(n). The graph shows that a(n) seems to oscillate around 0 with a pseudo-periodic and fractal pattern. - _Jean-Christophe Hervé_, Oct 05 2014
%C A088568 It is conjectured that a(n) = O(log(n)) (see PlanetMath link). Note that for a random sequence of 1's and -1's, we would have O(sqrt(n)). - _Daniel Forgues_, Jul 10 2015
%C A088568 The linked PlanetMath text mentions 0.5*n + O(log(n)) only in respect of an empirical observation, apparently to support the density conjecture (the conjecture described above in the first comment dated Oct 05 2014). - _Peter Munn_, Aug 03 2022
%C A088568 The conjecture that a(n) = O(log(n)) seems incorrect as |a(n)| seems to grow as fast as sqrt(n), see A289323 and note that a(2^n) = -A289323(n), so for example a(2^64) = -A289323(64) = -836086974 which is much larger in absolute value than log(2^64), but about 0.19*2^32. - _Richard P. Brent_, Jul 07 2017
%C A088568 For n = 124 to 147, we have the same 24 values as for n = 42 to 65: {0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 2, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1}, and for n = 173 to 200, we have the same 28 values as for n = 11 to 38: {-1, -2, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0}. - _Daniel Forgues_, Jul 11 2015
%F A088568 a(n) = 3*n - 2*A054353(n) by definition. - _Jean-Christophe Hervé_, Oct 05 2014
%F A088568 a(n) = 2*A156077(n) - n. - _Jean-Christophe Hervé_, Oct 05 2014
%Y A088568 Cf. A000002 (Kolakoski sequence), A054353 (partial sums of Kolakoski sequence), A156077 (number of 1's in the Kolakoski sequence).
%Y A088568 For the discrepancy of the Kolakoski sequence see A294448 (this is simply the negation of the present sequence).
%Y A088568 For records see A294449.
%K A088568 sign,look
%O A088568 1,12
```
### A294448
```
%N A294448 Discrepancy of the Kolakoski sequence A000002.
%C A294448 The discrepancy is defined by a(n) = Sum_{i=1..n} (-1)^k(i), where k(i) = A000002(i). The negative of this sequence is A088568, which is the main entry for this sequence.
%Y A294448 Cf. A000002, A088568.
%Y A294448 For records see A294449.
%K A294448 sign,look
%O A294448 1,12
```

## Candidate 17: A033324 vs A329678 (score 62.1, agree 90, variant drop2, family size 3)
Terms: 4, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A033324
```
%N A033324 a(n) = floor(4/n).
%Y A033324 Cf. A010766.
%K A033324 easy,nonn
%O A033324 1,1
```
### A329678
```
%N A329678 Number of excursions of length n with Motzkin-steps consisting only of consecutive steps UD and DH.
%C A329678 The Motzkin step set is U=(1,1), H=(1,0) and D=(1,-1). An excursion is a path starting at (0,0), ending on the x-axis and never crossing the x-axis, i.e., staying at nonnegative altitude.
%F A329678 G.f.: 1 + t + t^2 + t^3.
%Y A329678 Cf. A329670, A329677, A329679 (other Motzkin excursions avoiding certain consecutive steps such that the sequence counting them has growth rate zero).
%K A329678 nonn,walk,easy
%O A329678 0
```

## Candidate 18: A109720 vs A115789 (score 61.8, agree 103, variant drop2, family size 2)
Terms: 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1

### A109720
```
%N A109720 Periodic sequence {0,1,1,1,1,1,1} or n^6 mod 7.
%C A109720 This sequence also represents n^12 mod 7; n^18 mod 7; (exponents are = 0 mod 6).
%C A109720 Characteristic sequence for numbers n>=1 to be relatively prime to 7. - _Wolfdieter Lang_, Oct 29 2008
%C A109720 a(n+4), n>=0, (periodic 1,1,1,0,1,1,1) is also the characteristic sequence for mod m reduced positive odd numbers (i.e., gcd(2*n+1,m)=1, n>=0) for each modulus m from 7*A003591 = [7,14,28,49,56,98,112,196,...]. - _Wolfdieter Lang_, Feb 04 2012
%F A109720 a(n) = 0 if n=0 mod 7; a(n) = 1 else.
%F A109720 G.f.: (x+x^2+x^3+x^4+x^5+x^6)/(1-x^7) = -x*(1+x)*(1+x+x^2)*(x^2-x+1) / ( (x-1)*(1+x+x^2+x^3+x^4+x^5+x^6) ).
%F A109720 a(n) = 1-A082784(n); a(A047304(n)) = 1; a(A008589(n)) = 0; A033439(n) = Sum_{k=0..n} a(k)*(n-k). - _Reinhard Zumkeller_, Nov 30 2009
%F A109720 Multiplicative with a(p) = (if p=7 then 0 else 1), p prime. - _Reinhard Zumkeller_, Nov 30 2009
%F A109720 Dirichlet g.f. (1-7^(-s))*zeta(s). - _R. J. Mathar_, Mar 06 2011
%F A109720 For the general case: the characteristic function of numbers that are not multiples of m is a(n)=floor((n-1)/m)-floor(n/m)+1, m,n > 0. - _Boris Putievskiy_, May 08 2013
%Y A109720 Cf. A010876 = n mod 7; A053879 = n^2 mod 7; A070472 = m^3 mod 7; A070512 = n^4 mod 7; A070593 = n^5 mod 7.
%Y A109720 Cf. A168185, A145568, A168184, A168182, A168181, A097325, A011558, A166486, A011655, A000035, A014016 (first differences).
%K A109720 easy,mult,nonn
%O A109720 0,1
```
### A115789
```
%N A115789 a(n) = (floor((n+1)*Pi) - floor(n*Pi)) mod 2.
%C A115789 The arithmetic mean (1/(n+1))*Sum_{k=0..n} a(k) converges to 4 - Pi. What is effectively the same: the Cesaro limit (C1) of a(n) is 4 - Pi.
%F A115789 a(n) = (floor((n+1)*Pi) - floor(n*Pi)) mod 2.
%F A115789 a(n) = A063438(n) mod 2.
%F A115789 a(n) = 1 - A115790(n).
%Y A115789 Cf. A000796, A022844, A063438, A115788, A115790.
%K A115789 nonn,less
%O A115789 0,1
```

## Candidate 19: A048669 vs A049298 (score 61.8, agree 103, variant drop2, family size 2)
Terms: 1, 2, 2, 2, 2, 4, 2, 2, 2, 4, 2, 4, 2, 4, 3, 2, 2, 4, 2, 4, 3, 4, 2, 4, 2, 4, 2, 4, 2, 6

### A048669
```
%N A048669 The Jacobsthal function g(n): maximal gap in a list of all the integers relatively prime to n.
%C A048669 Equivalently, g(n) is the least integer such that among any g(n) consecutive integers i, i+1, ..., i+g(n)-1 there is at least one which is relatively prime to n.
%C A048669 The definition refers to all integers, not just those in the range 1..n-1.
%C A048669 Differs from A070194 by 1 at the primes. - _T. D. Noe_, Mar 21 2007
%C A048669 Jacobsthal's function is used in the proofs of Recamán's and Pomerance's conjectures on P-integers--see A192224. - _Jonathan Sondow_, Jun 14 2014
%F A048669 From _N. J. A. Sloane_, Apr 19 2017 (Start):
%F A048669 g(n) = g(Rad(n)) (cf. A007947). So in studying g(n) we may focus on the case when n is a product of w (say) distinct primes.
%F A048669 g(n) <= 2^w for all w [Kanold].
%F A048669 g(n) <= 2^(1/w) for all w >= e^50 [Kanold].
%F A048669 For some unknown X, g(n) <= X*(w*log(w))^2 for all w [Iwaniec].
%F A048669 (End)
%F A048669 g(n) << (log(n))^2, as proved by Iwaniec. - _Charles R Greathouse IV_, Sep 08 2012.
%F A048669 a(prime(n)#) = A048670(n), where prime(n)# = A002110(n). - _Jianing Song_, Feb 01 2026
%Y A048669 Essentially same as A049298. See A132468 for another version.
%Y A048669 Cf. A048670, A070971, A007947, A038566, A192224, A285183.
%K A048669 nonn,easy,nice
%O A048669 1,2
```
### A049298
```
%N A049298 Take reduced residue systems of n, generate its first differences, dRRS(n); sequence gives maximal value of dRSSS(n).
%C A049298 Greatest values occur at primorial numbers (A002110).
%Y A049298 Cf. A048670. Essentially same as A048669.
%K A049298 nonn
%O A049298 1,3
```

## Candidate 20: A112207 vs A112208 (score 61.2, agree 102, variant abs, family size 2)
Terms: 1, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0

### A112207
```
%N A112207 McKay-Thompson series of class 72c for the Monster group.
%F A112207 Expansion of A - q/A, where A = q^(1/2)*(eta(q^12)*eta(q^18)/(eta(q^6)* eta(q^36))), in powers of q. - _G. C. Greubel_, Jul 02 2018
%K A112207 sign
%O A112207 0,31
```
### A112208
```
%N A112208 McKay-Thompson series of class 72d for the Monster group.
%F A112208 Expansion of A + q/A, where A = q^(1/2)*(eta(q^12)*eta(q^18)/(eta(q^6)* eta(q^36))), in powers of q. - _G. C. Greubel_, Jul 02 2018
%K A112208 sign
%O A112208 0,31
```

## Candidate 21: A093085 vs A112171 (score 60.7, agree 88, variant abs, family size 4)
Terms: 1, -2, 0, 0, 1, 2, 0, 0, -1, -4, 0, 0, 0, 6, 0, 0, 1, -8, 0, 0, 0, 12, 0, 0, -1, -18, 0, 0, -1, 24

### A093085
```
%N A093085 Expansion of phi(-x) / psi(x^4) in powers of x where phi(), psi() are Ramanujan theta functions.
%C A093085 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A093085 eta(q^2) * eta(q^8)^6 = eta(q)^2 * eta(q^4)^2 * eta(q^8) * eta(q^16)^2 + 2 * eta(q^2) * eta(q^4)^2 * eta(q^16)^4 is equivalent to the a(4*n), ..., a(4*n + 3) results.
%F A093085 Expansion of q^(1/2) * eta(q)^2 * eta(q^4) / (eta(q^2) * eta(q^8)^2) in powers of q.
%F A093085 Euler transform of period 8 sequence [ -2, -1, -2, -2, -2, -1, -2, 0, ...].
%F A093085 Given g.f. A(x), then B(q) = A(q)^2 / q satisfies 0 = f(B(q), B(q^2)) where f(u, v) = u * (u + 8) * (v + 4) - v^2.
%F A093085 G.f. is a period 1 Fourier series which satisfies f(-1 / (32 t)) = 32^(1/2) g(t) where q = exp(2 Pi i t) and g() is the g.f. for A187154.
%F A093085 G.f.: Product_{k>0} (1 - x^k)^2 / ((1 - x^(4*k - 2)) * (1 - x^(8*k))^2).
%F A093085 a(4*n + 2) = a(4*n + 3) = 0. a(4*n) = A029838(n). a(4*n + 1) =  -2 * A083365(n). Convolution square is A131124. Convolution inverse is A187154.
%F A093085 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = 2 * exp(-Pi / 2) * 2^(1/4) * (2+sqrt(2))^(1/2) = A388480. - _Simon Plouffe_, Sep 17 2025
%Y A093085 Cf. A029838, A029839, A083365, A131124, A187154.
%K A093085 sign
%O A093085 0,2
```
### A112171
```
%N A112171 McKay-Thompson series of class 32c for the Monster group.
%F A112171 Expansion of A + 2*q/A, where A = q^(1/2)*(eta(q^4)/eta(q^16)), in powers of q. - _G. C. Greubel_, Jun 26 2018
%K A112171 sign
%O A112171 0,2
```

## Candidate 22: A082784 vs A115790 (score 58.6, agree 85, variant drop1, family size 6)
Terms: 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0

### A082784
```
%N A082784 Characteristic function of multiples of 7.
%C A082784 This sequence is the Euler transformation of A185017. - _Jason Kimberley_, Oct 14 2011
%F A082784 a(n) = 0^(n mod 7).
%F A082784 a(0)=1, a(n)=0 for 1<=n<7, a(n+7)=a(n).
%F A082784 a(n) = 1 - (n^6 mod 7). - _Paolo P. Lava_, Oct 02 2006
%F A082784 a(n) = 1 - A109720(n); a(A008589(n)) = 1; a(A047304(n)) = 0. - _Reinhard Zumkeller_, Nov 30 2009
%F A082784 a(n) = floor(n/7)-floor((n-1)/7). - _Tani Akinari_, Oct 26 2012
%F A082784 a(n) = C(n-1,6) mod 7. - _Wesley Ivan Hurt_, Oct 07 2014
%F A082784 From _Wesley Ivan Hurt_, Jul 11 2016: (Start)
%F A082784 G.f.: 1/(1-x^7).
%F A082784 a(n) = a(n-7) for n>6.
%F A082784 a(n) = (gcd(n,7) - 1)/6. (End)
%F A082784 Additive with a(p^e) = 1 if p = 7, 0 otherwise. - _Amiram Eldar_, Oct 20 2026
%Y A082784 Cf. A008589, A076309.
%Y A082784 Characteristic function of multiples of g: A000007 (g=0), A000012 (g=1), A059841 (g=2), A079978 (g=3), A121262 (g=4), A079998 (g=5), A079979 (g=6), this sequence (g=7). - _Jason Kimberley_, Oct 14 2011
%Y A082784 Cf. A000007, A047304, A109720, A185017, A014016 (first differences).
%K A082784 nonn,easy,changed
%O A082784 0,1
```
### A115790
```
%N A115790 a(n) = 1 - (floor((n+1)*Pi) - floor(n*Pi)) mod 2.
%C A115790 The arithmetic mean 1/(n+1)*sum(a(k)|k=0...n) converges to Pi-3. What is effectively the same: the Cesaro limit (C1) of a(n) is Pi-3.
%F A115790 a(n) = 1 - (floor((n+1)*Pi) - floor(n*Pi)) mod 2.
%F A115790 a(n) = 1 - A115789(n). - _Michel Marcus_, Jul 15 2013
%Y A115790 Cf. A000796, A022844, A063438, A115788, A115789.
%K A115790 nonn,less
%O A115790 0,1
```

## Candidate 23: A018837 vs A187180 (score 56.6, agree 82, variant drop2, family size 3)
Terms: 0, 3, 2, 3, 2, 3, 4, 5, 4, 5, 6, 7, 6, 7, 8, 9, 8, 9, 10, 11, 10, 11, 12, 13, 12, 13, 14, 15, 14, 15

### A018837
```
%N A018837 Number of steps for knight to reach (n,0) on infinite chessboard.
%C A018837 The knight starts at (0,0) and we count the least number of steps. Row 1 of the array at A065775. - _Clark Kimberling_, Dec 20 2010
%C A018837 Apparently also the minimum number of steps of the (1,3)-leaper to reach (n,n) starting at (0,0). - _R. J. Mathar_, Jan 05 2018
%F A018837 a(n) = 2[ (n+2)/4 ] if n even, 2[ (n+1)/4 ]+1 if n odd (n >= 8).
%F A018837 G.f.: x*(3-x+x^2-x^3-2*x^4+2*x^5)/((1-x)^2*(1+x)*(1+x^2)). a(n)=A083219(n), n<>1. - _R. J. Mathar_, Dec 15 2008
%F A018837 T(0,0)=0, T(1,0)=3, and for m>=1, T(4m-2,0)=2m, T(4m-1,0)=2m+1, T(4m,0)=2m, T(4m+1,0)=2m+1 where T(.,.) = A065775(.,.). - _Clark Kimberling_, Dec 20 2010
%F A018837 Sum_{n>=1} (-1)^n/a(n) = 5/3 - 2*log(2). - _Amiram Eldar_, Sep 10 2023
%Y A018837 Cf. A065775, A183041-A183053, A083219 (essentially the same).
%Y A018837 Cf. A018840 for the (2,3)-leaper.
%K A018837 nonn,easy
%O A018837 0,2
```
### A187180
```
%N A187180 Parse the infinite string 0101010101... into distinct phrases 0, 1, 01, 010, 10, ...; a(n) = length of n-th phrase.
%F A187180 Consider more generally the string 012...k012...k012...k012...k01... with an alphabet of size B, where k = B-1. The sequence begins with B 1's, and thereafter is quasi-periodic with period B^2, and increases by B in each period.
%F A187180 For the present example, where B=2, the sequence begins with two 1's and thereafter increases by 2 in each block of 4: (1,1) (2,3,2,3), (4,5,4,5), (6,7,6,7), ...
%F A187180 From _Colin Barker_, Oct 15 2015: (Start)
%F A187180 a(n) = (1+(-1)^n+(1-i)*(-i)^n+(1+i)*i^n+2*n)/4 for n>1, where i = sqrt(-1).
%F A187180 G.f.: x*(x^5-2*x^4+x^3+x^2+1) / ((x-1)^2*(x+1)*(x^2+1)). (End)
%F A187180 From _Wesley Ivan Hurt_, May 03 2021: (Start)
%F A187180 a(n) = a(n-1)+a(n-4)-a(n-5).
%F A187180 a(n) = floor((n+1+(-1)^floor((n+1)/2))/2) for n > 1. (End)
%Y A187180 See A187180-A187188 for alphabets of size 2 through 10.
%Y A187180 See also A109337, A187199, A187200, A106249, A083219, A018837.
%Y A187180 Essentially the same as A106249 and A018837.
%K A187180 nonn,easy
%O A187180 1,3
```

## Candidate 24: A068717 vs A344617 (score 55.8, agree 93, variant abs, family size 2)
Terms: 0, -1, 1, 0, -1, 1, 1, 1, 0, -1, 1, 1, -1, 1, 1, 0, -1, 1, 1, 1, 1, 1, 1, 1, 0, -1, 1, 1, -1, 1

### A068717
```
%N A068717 a(n) = -1 if A067280(n) == 0 (mod 2), otherwise a(n) = A049240(n).
%C A068717 Previous name was: x*x - n*y*y = +-1 has infinitely many solutions in integers (x,y).
%F A068717 a(n) = -1 if A067280(n) == 0 (mod 2), otherwise a(n) = A049240(n).
%Y A068717 Cf. A068716, A068718, A067280, A049240, A006702, A006703.
%K A068717 sign,easy
%O A068717 1,1
```
### A344617
```
%N A344617 Sign of the alternating sum of the prime indices of n.
%C A344617 Also the sign of the reverse-alternating sum of the partition with Heinz number n.
%C A344617 The alternating sum of a reversed partition (y_1,...,y_k) is Sum_i (-1)^(k-i) y_i. This is equal to (-1)^(k-1) times the number of odd parts in the conjugate partition. The alternating sum of the prime indices of n is given by A316524(n).
%C A344617 A prime index of n is a number m such that prime(m) divides n. The multiset of prime indices of n is row n of A112798.
%F A344617 a(n) = 0 if n is a square (A000290); otherwise a(n) = (-1)^(k-1), where k = A001222(n).
%F A344617 a(n) = a(A046523(n)). - _Antti Karttunen_, May 06 2022
%Y A344617 Positions of nonzeros are A000037.
%Y A344617 Positions of 0's are A000290.
%Y A344617 Positions of 1's are A026424.
%Y A344617 The absolute value is A049240.
%Y A344617 Positions of -1's are A119899.
%Y A344617 a(n) is the sign of A316524(n).
%Y A344617 A000041 counts partitions of 2n with alternating sum 0.
%Y A344617 A056239 adds up prime indices, row sums of A112798.
%Y A344617 A071321 is the alternating sum of prime factors.
%Y A344617 A071322 is the reverse-alternating sum of prime factors.
%Y A344617 A103919 counts partitions by sum and alternating sum.
%Y A344617 A316523 is the alternating sum of prime multiplicities.
%Y A344617 A335433 ranks separable partitions.
%Y A344617 A335448 ranks inseparable partitions.
%Y A344617 A344606 counts wiggly permutations of prime indices with twins.
%Y A344617 A344610 counts partitions by sum and positive reverse-alternating sum.
%Y A344617 A344612 counts partitions by sum and reverse-alternating sum.
%Y A344617 A344616 is the alternating sum of the reversed prime indices of n.
%Y A344617 A344618 gives reverse-alternating sum of standard compositions.
%Y A344617 Cf. A000070, A001222, A046523, A028260, A116406, A124754, A239829, A343938, A344607, A344608, A344609, A344653, A344739.
%K A344617 sign
%O A344617 1
```

## Candidate 25: A112166 vs A112167 (score 54.6, agree 91, variant abs, family size 2)
Terms: 1, 2, 0, 0, 0, 0, -2, 4, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, -2, 12, 0, 0, 0, 0, 4, 18, 0, 0, 0, 0

### A112166
```
%N A112166 McKay-Thompson series of class 24i for the Monster group.
%F A112166 Expansion of A + 2*q/A, where A = q^(1/2)*(eta(q^6)/eta(q^12))^2, in powers of q. - _G. C. Greubel_, Jun 25 2018
%K A112166 sign
%O A112166 0,2
```
### A112167
```
%N A112167 McKay-Thompson series of class 24j for the Monster group.
%F A112167 Expansion of A - 2*q/A, where A = q^(1/2)*(eta(q^6)/eta(q^12))^2, in powers of q. - _G. C. Greubel_, Jun 25 2018
%K A112167 sign
%O A112167 0,2
```

## Candidate 26: A112201 vs A112203 (score 54.6, agree 91, variant abs, family size 2)
Terms: 1, -1, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0, 2, -1, 0, 2, 0, 0, 3, 0, 0, 4, 1, 0, 4, -1, 0, 6, 1, 0

### A112201
```
%N A112201 McKay-Thompson series of class 60c for the Monster group.
%F A112201 Expansion of A - q/A, where A = q^(1/2)*(eta(q^6)*eta(q^15)/( eta(q^3)* eta(q^30))), in powers of q. - _G. C. Greubel_, Jun 28 2018
%K A112201 sign
%O A112201 0,10
```
### A112203
```
%N A112203 McKay-Thompson series of class 60e for the Monster group.
%F A112203 Expansion of A + q/A, where A = q^(1/2)*(eta(q^6)*eta(q^15)/( eta(q^3)* eta(q^30))), in powers of q. - _G. C. Greubel_, Jun 28 2018
%K A112203 sign
%O A112203 0,10
```

## Candidate 27: A033416 vs A033417 (score 54.6, agree 91, variant drop1, family size 2)
Terms: 96, 48, 32, 24, 19, 16, 13, 12, 10, 9, 8, 8, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3

### A033416
```
%N A033416 a(n) = floor(96/n).
%K A033416 easy,nonn
%O A033416 1,1
```
### A033417
```
%N A033417 a(n) = floor(97/n).
%K A033417 easy,nonn
%O A033417 1,1
```

## Candidate 28: A128999 vs A168092 (score 54.0, agree 90, variant drop1, family size 2)
Terms: 1, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5

### A128999
```
%N A128999 Start with an integer (in this case 1). First, add 5 or 6 if the integer is odd or even, respectively. Then divide by 2.
%C A128999 Note that any a(1) <= 5 converges to 5 and any a(1) >= 6 converges to 6.
%C A128999 Decimal expansion of 1211/900. - _Elmo R. Oliveira_, May 05 2024
%F A128999 a(n) = [a(n-1) + b]/d, if a(n) even = [a(n-1) + c]/d, if a(n) odd (starting a(1)=1 with b=5, c=6, d=2).
%F A128999 a(n) = 5 for n >= 4. - _R. J. Mathar_, Oct 31 2007
%F A128999 G.f.: x*(1+2*x+x^2+x^3)/(1-x). - _Elmo R. Oliveira_, May 05 2024
%Y A128999 Cf. A085600.
%K A128999 easy,nonn
%O A128999 1,2
```
### A168092
```
%N A168092 a(n) = number of natural numbers m such that n - 2 <= m <= n + 2.
%C A168092 Generalization: If a(n,k) = number of natural numbers m such that n - k <= m <= n + k (k >= 1) then a(n,k) = a(n-1,k) + 1 = n + k for 0 <= n <= k, a(n,k) = a(n-1,k) = 2k + 1 for n >= k + 1 (see, e.g., A158799). a(n) = (2 + n) for 0 <= n <= 2, a(n) = 5 for n >= 3.
%F A168092 G.f.: (2+x+x^2+x^3)/(1-x) = 1/(1-x)+(1-x^4)/(1-x)^2. - _Jaume Oliver Lafont_, Nov 29 2009
%Y A168092 Cf. A158411. - _Jaume Oliver Lafont_, Nov 29 2009
%K A168092 nonn,less
%O A168092 0,1
```

## Candidate 29: A037860 vs A037878 (score 52.8, agree 88, variant drop2, family size 2)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3

### A037860
```
%N A037860 Sum{d(i)-d(i-1): d(i)>d(i-1), i=1,...,m}, where Sum{d(i)*10^i: i=0,1,...,m} is base 10 representation of n.
%C A037860 This is the base-10 down-variation sequence; see A297330.
%Y A037860 Cf. A297330, A037851.
%K A037860 nonn,base
%O A037860 1,20
```
### A037878
```
%N A037878 (1/2)*Sum{|d(i)-e(i)|}, where Sum{d(i)*10^i} is base 10 representation of n and e(i) are digits d(i) in nonincreasing order, for i=0,1,...,m.
%K A037878 nonn,base
%O A037878 1,20
```

## Candidate 30: A028903 vs A081599 (score 51.1, agree 74, variant raw, family size 3)
Terms: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25

### A028903
```
%N A028903 Map n = Sum c_i 10^i to a(n) = Sum c_i 8^i.
%K A028903 nonn,base
%O A028903 0,3
```
### A081599
```
%N A081599 Let n = 10x + y where 0 <= y <= 9, x >= 0. Then a(n) = 8x+y.
%F A081599 G.f.: -x*(x^9 -x^8 -x^7 -x^6 -x^5 -x^4 -x^3 -x^2 -x -1) / ((x -1)^2*(x +1)*(x^4 -x^3 +x^2 -x +1)*(x^4 +x^3 +x^2 +x +1)). - _Colin Barker_, Jun 24 2014
%F A081599 a(n) = n - 2*floor(n/10). - _Bruno Berselli_, Jun 24 2014
%Y A081599 Cf. A081502. Different from A028898.
%K A081599 nonn,easy
%O A081599 0,3
```

## Candidate 31: A203568 vs A257628 (score 51.0, agree 85, variant abs, family size 2)
Terms: 0, 1, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0

### A203568
```
%N A203568 a(n) = A026837(n) - A026838(n).
%F A203568 G.f.: Sum_{k in Z} sign(k) * x^(k * (3*k - 1) / 2).
%F A203568 G.f.: Sum_{k>0} x^(k * (3*k - 1) / 2) * (1 - x^k). - _Michael Somos_, Jul 12 2015
%F A203568 G.f.: x - x^2 * (1 + x) + x^3 * (1 + x) * (1 + x^2) - x^4 * (1 + x) * (1 + x^2) * (1 + x^3) + .... - _Michael Somos_, Jul 12 2015
%F A203568 G.f.: x / (1 + x) - x^3 / ((1 + x) * (1 + x^2)) + x^6 / ((1 + x) * (1 + x^2) * (1 + x^3)) - .... - _Michael Somos_, Jul 12 2015
%F A203568 G.f.: x / (1 + x^2) - x^2 / ((1 + x^2) * (1 + x^4)) + x^3 / ((1 + x^2 ) * (1 + x^4) * (1 + x^6)) - .... - _Michael Somos_, Jul 12 2015
%F A203568 a(n) = - A143062(n) unless n=0. - _Michael Somos_, Jul 12 2015
%F A203568 For k >= 1, a((3*k^2 - k)/2) = 1, a((3*k^2 + k)/2) = -1.  a(n) = 0 otherwise. - _Robert Israel_, Nov 24 2015
%F A203568 From _Peter Bala_, Feb 11 2021: (Start)
%F A203568 G.f.: A(x) = Sum_{n >= 1} x^(n*(2*n-1))/Product_{k = 1..2*n} 1 + x^k = x - x^2 + x^5 - x^7 + x^12 - x^15 + - ..., follows by adding terms in pairs in the above g.f. Sum_{n >= 1} (-1)^(n+1)*x^(n*(n+1)/2)/Product_{k = 1..n} 1 + x^k of Somos, dated Jul 12 2015.
%F A203568 G.f.: A(x) = 1/2 + (1/2)*Sum_{n >= 1} (-1)^n*x^(n*(n-1)/2)/Product_{k = 1..n} 1 + x^k.
%F A203568 A(x) = Sum_{n >= 0} (-1)^n * x^(n+1)*Product_{k = 1..n} 1 + x^k. (Set x = -1 in Andrews, equation 8. For similar results see the Examples below.)
%F A203568 Conjectural g.f: A(x) = Sum_{n >= 1} (-1)^(n+1) * x^(2*n-1)/Product_{k = 1..n} 1 + x^(2*k-1)  = x - x^2 + x^5 - x^7 + x^12 - x^15 + - ....
%F A203568 More generally, for positive integer N, we appear to have the identity
%F A203568 A(x) = Product_{j = 1..N-1} 1/(1 + x^(2*j)) * ( P(N,x) + Sum_{n >= 1} (-1)^(n+N) * x^(2*N*n-N)/Product_{k = 1..n} 1 + x^(2*k-1) ), where P(N,x) is a polynomial in x of degree N^2 - N - 1 for N > 1, with the first few values given empirically by P(1,x) = 0, P(2,x) = x, P(3,x) = x - x^2 + x^5 and P(4,x) = x - x^2 + x^3 + x^5 + x^7 - x^8 + x^11. Cf. A186424. (End)
%Y A203568 Cf. A003406, A010815, A026837, A026838, A143062.
%K A203568 sign
%O A203568 0,1
```
### A257628
```
%N A257628 Expansion of 1 - f(-x) in powers of x where f() is a Ramanujan theta function.
%C A257628 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%F A257628 G.f.: x + x^2 * (1 - x) + x^3 * (1 - x) * (1 - x^2) + ....
%F A257628 G.f.: Sum_{k>0} -(-1)^k * (x^((3*k^2 - k)/2) + x^((3*k^2 + k)/2)).
%F A257628 G.f.: Sum_{k>0} -(-1)^k * x^((k^2 + k) / 2) / ((1 - x) * (1 - x^2) * ... * (1 - x^k)).
%F A257628 G.f.: -(Product_{j>=1}(1-x^j) - 1), from Euler's Pentagonal Theorem. - _Wolfdieter Lang_, Feb 16 2021
%F A257628 a(n) = - A010815(n) unless n=0, a(0) = 0.
%Y A257628 Cf. A001318, A010815, A341418 (convolution triangle).
%K A257628 sign,easy
%O A257628 0
```

## Candidate 32: A248107 vs A352561 (score 51.0, agree 85, variant raw, family size 2)
Terms: 1, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0, 1, 2, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 3, 2, 0, 0

### A248107
```
%N A248107 Number of isomorphism classes of affine Mendelsohn triple systems of order n.
%C A248107 A Mendelsohn triple system is affine if the associated quasigroup is affine, i.e, given by x*y=(1-f)(x)+f(y) over an abelian group (A,+) with an automorphism f.
%C A248107 For Steiner triple systems, the enumeration is settled by the following observation: a Steiner triple system is affine if and only if A=Z_3^n and f(x)=-x.
%C A248107 The existence spectrum (i.e., n such that a(n)>0) is A003136.
%C A248107 Comment from _David Stanovsky_, Mar 19 2022, added by _N. J. A. Sloane_, Mar 20 2022 (Start)
%C A248107 This is the sequence a(n) defined in the Donovan et al. paper.
%C A248107 The b(n) sequence defined there gives the number of non-affine systems.
%C A248107 The first 728 values of b(n) are now known: they are all zeros, except b(81) = 2, b(243) = 6, b(324) = 2, b(567)=4. We do not know b(729).
%C A248107 The reason is the following: it follows from the Galkin-Fischer-Smith theorem that, for n = m * 3^d, m not divisible by 3, we have b(n) = a(m) * b(3^d).
%C A248107 At the time of writing the paper, we could use known data about commutative Moufang loops to determine b(1) = b(3) = b(9) = b(27) = 0, and b(81) = 2. Later we managed to develop smarter enumeration methods that allowed us to determine b(243)=6: see Jedlička et al. (2007).
%C A248107 Since so many of the initial values of b(n), this does not have its own OEIS entry. (End)
%C A248107 Conjecture: This is the same sequences as A352561.(Note that A352561 has an explicit Dirichlet generating function.) - _N. J. A. Sloane_, Mar 21 2022
%Y A248107 Cf. A003136, A352550, A352561.
%K A248107 nonn,mult
%O A248107 1,7
```
### A352561
```
%N A352561 a(n) = number of modules with n elements over the ring of integers in the imaginary quadratic field of discriminant -3.
%C A352561 See A352550 for comments and PARI code.
%C A352561 Appears to be the same sequence as A248107.
%Y A352561 Cf. A038540, A038541, A248107, A352550-A352567.
%K A352561 nonn,mult
%O A352561 1,7
```

## Candidate 33: A043545 vs A267442 (score 51.0, agree 85, variant drop1, family size 2)
Terms: 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1

### A043545
```
%N A043545 (Maximal base-2 digit of n) - (minimal base-2 digit of n).
%C A043545 Characteristic function of A062289 (non-Mersenne numbers A000225). - _Omar E. Pol_, Sep 05 2021
%F A043545 0 followed by a string of 2^k - 1 1's. Also a(n)=0 iff n = 2^m - 1.
%F A043545 G.f.: 1/(1-x) - Sum_{k>=0} x^(2^k-1). - _Michael Somos_, Aug 25 2003
%F A043545 a(n) = 1 - A036987(n). 1's complement of Fredhold-Rueppel sequence. - _Michael Somos_, Aug 25 2003
%F A043545 a(n) = (1 + (-1)^binomial(n, floor(n/2)))/2. - _Paul Barry_, Jun 07 2006
%F A043545 Ignoring first zero and beginning instead with offset 2, a(n) = A006530(n) mod 2. - _Rick L. Shepherd_, Jun 09 2008
%F A043545 a(n) = A000777(n) mod 2, for n > 0. - _John M. Campbell_, Jul 16 2016
%Y A043545 Cf. A000225, A036987, A062289.
%Y A043545 Column k=0 of A347519.
%K A043545 nonn,base
%O A043545 0,1
```
### A267442
```
%N A267442 Middle column of the "Rule 129" elementary cellular automaton starting with a single ON (black) cell.
%F A267442 Conjecture: a(n) = A043545(n), n>0. - _R. J. Mathar_, Jan 17 2016
%Y A267442 Cf. A267417.
%K A267442 nonn,easy
%O A267442 0
```

## Candidate 34: A189664 vs A284817 (score 50.4, agree 84, variant stripz, family size 2)
Terms: 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0

### A189664
```
%N A189664 Fixed point of the morphism 0->010, 1->001.
%C A189664 a(n) is the parity of the number of ternary 1-digits below the lowest 0-digit in the ternary expansion of n-1. All fixed-width morphisms have a similar digital interpretation. - _Kevin Ryde_, Apr 26 2017
%F A189664 a(3*k-2) = 0, a(3*k-1) = 1 - a(k), a(3*k) = a(k) for k >= 1, a(0) = 0.
%F A189664 2*a(n) = A284794(n) for n >= 1. - _Clark Kimberling_, Apr 14 2017
%F A189664 This formula cannot be correct, it belongs to A189665. - _Michel Dekking_, Oct 15 2019
%F A189664 a(n) = A284777(n) - 2n. - _Clark Kimberling_, Apr 15 2017
%Y A189664 Cf. A189628, A189665, A189666, A189667.
%K A189664 nonn
%O A189664 1
```
### A284817
```
%N A284817 a(n) = 2n - 1 - A284776(n).
%F A284817 a(n) = 2n - 1 - A284776.
%F A284817 Conjecture: a(n) = A189664(n-1). - _R. J. Mathar_, Jun 21 2025
%Y A284817 Cf. A284776, A284818, A284819.
%K A284817 nonn,easy
%O A284817 1
```

## Candidate 35: A209635 vs A355689 (score 50.4, agree 73, variant abs, family size 3)
Terms: 1, 1, -1, 1, -1, -1, -1, 1, 0, -1, -1, -1, -1, -1, 1, 1, -1, 0, -1, -1, 1, -1, -1, -1, 0, -1, 0, -1, -1, 1

### A209635
```
%N A209635 Möbius mu-function applied to the odd part of n: a(n) = A008683(A000265(n)).
%C A209635 The sequence is the Moebius function applied to n after all powers of 2 have been cast out, thus it tells whether n is divisible by a square of any odd prime. Multiplicative with a(p^e) = 1 if p = 2, -1 if p > 2 and e = 1; 0 if p > 2 and e > 1.
%C A209635 There seems to be an interesting connection between this sequence and the reduction of the sequence A001001 modulo 2. We have that |a(n)| = A001001(n) mod 2 for n = 1, 2, ..., 80. This equality does not hold for n in {81, 2*81, 3*81, ..., 7*81, 625, 8*81, 10*81, ...}. - _John M. Campbell_, Jul 17 2016
%C A209635 a(n) = 0 iff there is a prime p > 2 such that p^2 | n. A001001(n) is even iff there exist a prime p > 2 and e = 4k+2 or 4k+3 such that p^e || n. Therefore, |a(n)| differs from A001001(n) mod 2 iff a(n) = 0 and A001001(n) is odd. That happens iff there is a prime p > 2 such that p^e || n, with e > 1, but every such prime-power factor satisfies e mod 4 in {0, 1}. - _Álvar Ibeas_, Nov 28 2017
%C A209635 Note added May 03 2022: The absolute values of the terms is now given by A353627, while the parity of the sequence A001001 is given by A353628, and the positions of their differences by A353456, where a PARI-program implements Álvar's above insight.
%C A209635 The average order of Sum_{k=1..n} a(k) ~ (-log(n/Pi)^2 - gamma^2 - 2*sg1 + Pi^2/12) / log(2)^2 + 1/6, where gamma is the Euler-Mascheroni constant A001620 and sg1 is the first Stieltjes constant (see A082633). - _Vaclav Kotesovec_, Feb 03 2019
%F A209635 Dirichlet g.f.: 1/( zeta(s)*(1-1/2^s)^2). - _R. J. Mathar_, Mar 12 2012
%F A209635 Moebius transform of A104117. - _R. J. Mathar_, Mar 12 2012
%F A209635 Dirichlet convolution of A087003 and A209229. - _Andrew Howroyd_, Aug 04 2018
%Y A209635 Cf. A353627 gives the absolute values and is the characteristic function of A122132, whose complement A038838 gives the position of zeros here.
%Y A209635 Cf. A001001, A087003, A099990, A131729 (Dirichlet inverse), A209229.
%Y A209635 Cf. also A353456, A353628.
%K A209635 mult,sign
%O A209635 1
```
### A355689
```
%N A355689 Dirichlet inverse of A166486, characteristic function of numbers that are not multiples of 4.
%C A355689 From _Antti Karttunen_, Dec 31 2022: (Start)
%C A355689 Note the correspondences between four sequences:
%C A355689   A355689 --- abs ---> A353627
%C A355689      ^                    ^
%C A355689      |                    |
%C A355689     inv                  inv
%C A355689      |                    |
%C A355689      v                    v
%C A355689   A166486 <--- abs --- A358839
%C A355689 Here inv means that the sequences are Dirichlet Inverses of each other, and abs means taking absolute values.
%C A355689 (End)
%F A355689 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A166486(n/d) * a(d).
%F A355689 From _Antti Karttunen_, Dec 22, Dec 31 2022: (Start)
%F A355689 Multiplicative with a(2^e) = (-1)^e, and for odd primes p, a(p^e) = -1 if e = 1, otherwise 0.
%F A355689 For all e >= 0, a(2^e) = A008836(2^e).
%F A355689 For all n >= 0, a(2n+1) = A008683(2n+1).
%F A355689 a(n) = A359156(n) - A359158(n).
%F A355689 (End)
%F A355689 Dirichlet g.f.: 4^s/((4^s-1)*zeta(s)). - _Amiram Eldar_, Dec 30 2022
%Y A355689 Cf. A008683, A008836, A166486 (Dirichlet inverse), A353627 (absolute values), A358839 (their Dirichlet inverse), A359157 (positions of the positive terms), A359159 (of the negative terms), A359156, A359158.
%Y A355689 Cf. also A087003, A355688, A355690.
%K A355689 sign,mult
%O A355689 1
```

## Candidate 36: A267579 vs A347523 (score 50.4, agree 84, variant drop2, family size 2)
Terms: 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1

### A267579
```
%N A267579 Middle column of the "Rule 167" elementary cellular automaton starting with a single ON (black) cell.
%Y A267579 Cf. A267576, A043545.
%K A267579 nonn,easy
%O A267579 0
```
### A347523
```
%N A347523 Characteristic function of nonpowers of 2.
%F A347523 a(n) = 1 - A209229(n).
%F A347523 a(A000079(n)) = 0; a(A057716(n)) = 1.
%Y A347523 1 together with A043545. Cf. A267442.
%Y A347523 Cf. A000079, A057716, A209229.
%K A347523 nonn,easy
%O A347523 0
```

## Candidate 37: A288132 vs A288381 (score 49.8, agree 83, variant stripz, family size 2)
Terms: 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1

### A288132
```
%N A288132 Fixed point of the mapping 00->0010, 1->11, starting with 00.
%C A288132 From _Michel Dekking_, Feb 18 2021: (Start)
%C A288132 This is a morphic sequence, i.e., the letter to letter image of a fixed point of a morphism. Let nu be the morphism on {0,1,2} given by
%C A288132       nu(0) = 0, nu(1) = 11, nu(2) = 210.
%C A288132 Let lambda be the letter to letter substitution given by
%C A288132        lambda(0) = 0, lambda(1) =1, lambda(2) = 0.
%C A288132 Let SR be the StringReplace procedure SR(00) = 0010, SR(1) = 11.
%C A288132 CLAIM 1: 0^{-1}SR^n(00) = lambda(nu^n(2)).
%C A288132 Proof: By induction. For n=1:
%C A288132  0^{-1}SR(00) = 0^{-1}0010 = 010 = lambda(nu(2)).
%C A288132 Suppose true for n. Then
%C A288132      0^{-1} SR^{n+1}(10) = 0^{-1}SR^n(0010) =
%C A288132        0^{-1}SR^n(00) [11]^{2n} 0 =
%C A288132      lambda(mu^n(2)) [11]^{2n} 0 =
%C A288132        lambda(nu^n(210))= lambda(nu{n+1}(2)).
%C A288132 Note that we proved that 0^{-1}SR^n(00) = (a(n+1)) is a morphic sequence, but it is general knowledge that x morphic => 0x morphic.
%C A288132 Let N_i(w) denote the number of letters i in the word w.
%C A288132 CLAIM 2: N_0(nu^n(2))=n, N_1(nu^n(2))=2^n-1, N_2(nu^n(2))=1, for n>0.
%C A288132 Proof: This follows directly from the same result for the morphism mu in A288381, since nu has the same incidence matrix as mu in A288381.
%C A288132 It follows from CLAIM 2 that the length |nu^n(2)| of nu^n(2) is equal to 2^n+n, and so by CLAIM 1, the length of  SR^n(00) is equal to
%C A288132       |SR^n(00)| = 2^n + n + 1 = A005126(n).
%C A288132 This proves Kimberling's (corrected) conjecture in the MATHEMATICA program.
%C A288132 Next, let z(n) = A288133(n) be the positions of 0 in (a(n)). So z = 1, 2, 4, 7, 12, 21, 38, 71, 136, 265, 522, 1035,....
%C A288132 Observe that the (n+2)-th 0 occurs in lambda( mu^n(2)) at the end of  mu^n(2) for n>1. It follows that
%C A288132       z(n+2) = 1+|mu^n(2)| =  2^n + n +1.
%C A288132 So z(n) = 2^{n-2} + n - 1 = A005126(n-2) for n>3.
%C A288132 (End)
%F A288132 a(n) = A103354(n) - A103354(n-1) for n > 1. - _Alan Michael Gómez Calderón_, Jul 27 2024
%Y A288132 Cf. A103354, A288133, A288134, A078038.
%K A288132 nonn,easy
%O A288132 1
```
### A288381
```
%N A288381 Fixed point of the mapping 00->0001, 1->11, starting with 00.
%C A288381 Apparently this is A288132 shifted by one place (or index). - _R. J. Mathar_, Jun 14 2017
%C A288381 From _Michel Dekking_, Feb 18 2021: (Start)
%C A288381 Proof of Mathar's conjecture: obviously, a(2) = A288132(1), and we know that (a(n): n>1) is generated by a morphism mu (see below), and  (A288132(n): n>1) is generated by a morphism nu (see A288132), given by nu(0)=0, nu(1)=11, nu(2)=210, both followed by replacing the letter 2 with the letter 0. Mathar's conjecture will therefore be a consequence of the following claim. Note that the shifting by one place occurs via the prefix 20 2^{-1} on the right side.
%C A288381 CLAIM: for all n one has mu^n(2) 0 = 20 2^{-1} nu^n(2).
%C A288381 Proof: By induction. For n=1:
%C A288381       mu(2)0 = 2010 = 20 2^{-1}210 = 20 2^{-1}nu(2).
%C A288381 Suppose true for n. Then
%C A288381       mu^{n+1}(2) 0 = mu^n(201) 0 =
%C A288381       mu^n(2) mu^n(0) mu^n(1) 0 =
%C A288381       20 2^{-1} nu^n(2) nu^n(1) 0 =
%C A288381       20 2^{-1} nu^n(210) = 20 2^{-1} nu^{n+1}(2).
%C A288381 (End)
%C A288381 From _Michel Dekking_, Feb 18 2021: (Start)
%C A288381 This is a morphic sequence, i.e., the letter-to-letter image of a fixed point of a morphism. Let mu be the morphism on {0,1,2} given by
%C A288381       m(0) = 0, mu(1) = 11, mu(2) = 201.
%C A288381 Let lambda be the letter-to-letter substitution given by lambda(0) = 0, lambda(1) =1, lambda(2) = 0.
%C A288381 Let SR be the StringReplace procedure SR(00) = 0001, SR(1) = 11.
%C A288381 CLAIM 1: 0^{-1}SR^n(00) = lambda(mu^n(2)).
%C A288381 Proof: By induction. For n=1:
%C A288381 0^{-1}SR(00) = 0^{-1}0001 = 001 = lambda(mu(2)).
%C A288381 Suppose true for n. Then
%C A288381      0^{-1} SR^{n+1}(00) = 0^{-1}SR^n(0001) =
%C A288381        0^{-1}SR^n(00) 0 [11]^{2n} =
%C A288381      lambda(mu^n(2)) 0 [11]^{2n} =
%C A288381        lambda(mu^n(201)) = lambda(mu{n+1}(2)).
%C A288381 Note that we proved that 0^{-1}SR^n(00) = (a(n): n>1) is a morphic sequence, but it is general knowledge that x morphic => 0x morphic.
%C A288381 Let N_i(w) denote the number of letters i in the word w.
%C A288381 CLAIM 2: N_0(mu^n(2))=n, N_1(mu^n(2))=2^n-1, N_2(mu^n(2))=1, for n>0.
%C A288381 Proof: Here N_2(mu^n(2)) = 1 for all n>0, is obvious. For 0 and 1 we use induction. For n=1: N_0(mu(2)) = 1, N_1(mu(2)) = 1.
%C A288381 Suppose true for n. Then
%C A288381       N_0(mu^{n+1}(2)) = N_0(mu^n(201)) = n + 1, and
%C A288381       N_1(mu^{n+1}(2)) = N_1(mu^n(201)) = 2^n - 1 + 2^n =2^{n+1} - 1.
%C A288381 It follows from CLAIM 2 that the length |mu^n(2)| of mu^n(2) is equal to 2^n+n, and so by CLAIM 1, the length of SR^n(00) is equal to
%C A288381       |SR^n(00)| = 2^n + n + 1 = A005126(n).
%C A288381 This proves Kimberling's conjecture in the MATHEMATICA program.
%C A288381 Next, let z(n) = A288382(n) be the positions of 0 in (a(n)). So z = 1, 2, 3, 5, 8, 13, 22, 39, ....
%C A288381 Observe that the (n+2)-th 0 occurs in lambda(mu^n(2)) right before the suffix [11]^{n-1} for n>1. It follows that
%C A288381    z(n+2) = 1+|mu^n(2)| - 2^{n-1} = 1+ 2^n+n-2^{n-1} = 2^{n-1}+n+1.
%C A288381 So z(n) = 2^{n-3} + n - 1 = A052968(n-2) for n>3.
%C A288381 This proves Mathar's June 14, 2017 conjecture in A288382.
%C A288381 (End)
%Y A288381 Cf. A288382, A288383, A005126.
%K A288381 nonn,easy
%O A288381 1
```

## Candidate 38: A065475 vs A114637 (score 49.7, agree 72, variant drop1, family size 36)
Terms: 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31

### A065475
```
%N A065475 Natural numbers excluding 2.
%C A065475 From the following 4 disjoint subsets of natural numbers A = {1}, B = {2}, OP = {odd primes}, C = {composites}, 16 sets are derivable: A000027 versus empty set, A002808 vs A008578, A065091 vs A065090, A000040 vs A018252, A006005 vs {{2} with A002808}, {1} vs {A000027 excluding 1}, {2} versus this sequence, {1, 2} versus Union[OP, C].
%C A065475 a(n) is the sum of the obvious divisors of n, which are 1 and n.
%C A065475 The natural numbers excluding 2 are the order numbers of magic squares. Order 2 magic squares do not exist. - _William Walkington_, Mar 12 2016
%C A065475 The numbers occurring at least twice in Pascal's triangle (A007318, A003016). - _Rick L. Shepherd_, Jun 05 2016
%C A065475 From _Enrique Navarrete_, Mar 03 2025: (Start)
%C A065475 a(n) is the number of binary strings of length n with at most one 0 and at least one 1. For example, the a(1)=1 string is 1 and the a(2)=3 strings are 01, 10, 11.
%C A065475 a(n) is also the number of ordered set partitions of an n-set into 2 sets such that the first set has at most one element and the second set has at least one element. (End)
%F A065475 G.f.: x*(1+x-x^2)/(1-x)^2. - _Paul Barry_, Aug 05 2004
%F A065475 a(n) = A000203(n) - A048050(n).
%F A065475 a(n) = n+1 for n>1, a(n) = a(n-1)+1 for n>2. - _Wesley Ivan Hurt_, Mar 13 2016
%F A065475 E.g.f.: (x + 1)*(exp(x) - 1). - _Ilya Gutkovskiy_, Jun 05 2016
%F A065475 a(n) = n + [n>1], a(n) = 1+n-floor(1/n). - _Alan Michael Gómez Calderón_, May 12 2023
%Y A065475 Cf. A000027, A000040, A000203, A002808, A006005, A008578, A018252, A048050, A065090, A065091, A097330. A003016, A007318.
%K A065475 nonn,easy
%O A065475 1,2
```
### A114637
```
%N A114637 Nonnegative numbers excluding 1 and 2.
%F A114637 G.f.: -x^2*(-3+2*x)/(x-1)^2 . - _R. J. Mathar_, May 25 2026
%Y A114637 Cf. A087156.
%K A114637 nonn,easy
%O A114637 1,2
```

## Candidate 39: A270657 vs A270658 (score 49.2, agree 82, variant abs, family size 2)
Terms: 0, 1, 1, 1, 0, 2, 1, 0, 2, 1, -1, 1, 0, 2, 2, 2, -1, 3, 1, -1, 1, 0, 2, 2, 2, -1, 3, 1, -2, 0

### A270657
```
%N A270657 a(3n)=a(n), a(3n+1)=a(3(n+1))-a(3n), a(3n+2)=a(3n)+a(3(n+1)); a(0)=0, a(1)=1.
%C A270657 Maxima a(<3^n)=A029744(n).
%F A270657 a(3n)=a(n), a(3n+1)=a(3(n+1))-a(3n), a(3n+2)=a(3n)+a(3(n+1)); a(0)=0, a(1)=1.
%K A270657 sign,look
%O A270657 0,6
```
### A270658
```
%N A270658 a(3n)=a(n), a(3n+1)=a(3n)+a(3(n+1)), a(3n+2)=a(3n)-a(3(n+1)); a(0)=0, a(1)=1.
%C A270658 Maxima a(<3^n)=A029744(n).
%F A270658 a(3n)=a(n), a(3n+1)=a(3n)+a(3(n+1)), a(3n+2)=a(3n)-a(3(n+1)); a(0)=0, a(1)=1.
%K A270658 sign,look
%O A270658 0,6
```

## Candidate 40: A171970 vs A172475 (score 49.0, agree 71, variant stripz, family size 9)
Terms: 0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 23, 24, 25, 25

### A171970
```
%N A171970 Integer part of the height of an equilateral triangle with side length n.
%F A171970 a(n) = floor(n*sqrt(3)/2).
%F A171970 a(n) = floor(A022838(n)/2).
%F A171970 a(n)*A004526(n) <= A171971(n)
%F A171970 a(n)*A005843(n) <= A171972(n).
%Y A171970 Beatty sequence of A010527.
%Y A171970 Cf. A022838, A004526, A005843, A171971, A171972.
%K A171970 nonn,easy
%O A171970 1,3
```
### A172475
```
%N A172475 a(n) = floor(n*sqrt(3)/2).
%F A172475 a(n) = A171970(n). [_R. J. Mathar_, Feb 05 2010]
%K A172475 nonn,easy
%O A172475 0,4
```

## Candidate 41: A061019 vs A119972 (score 48.3, agree 70, variant abs, family size 4)
Terms: 1, -2, -3, 4, -5, 6, -7, -8, 9, 10, -11, -12, -13, 14, 15, 16, -17, -18, -19, -20, 21, 22, -23, 24, 25, 26, -27, -28, -29, -30

### A061019
```
%N A061019 Negate primes in factorization of n.
%C A061019 Inverse Moebius transform of A158523. - Corrected by _Antti Karttunen_, Nov 26 2024
%F A061019 a(n) = n*lambda(n), where lambda is Liouville's function: A008836.
%F A061019 a(n) = (-1)^(number of primes dividing n)*n = n * (-1)^A001222(n) = n*A008836(n).
%F A061019 Totally multiplicative with a(p) = -p for prime p. [_Jaroslav Krizek_, Nov 01 2009]
%F A061019 Dirichlet g.f.: zeta(2*s-2)/zeta(s-1). Dirichlet inverse of A055615, all terms turned positive there. - _R. J. Mathar_, Apr 16 2011
%F A061019 a(n) = Sum_{d|n} lambda(d)*psi(d) = sum_{d|n} A008836(d)* A001615(d) = n/lambda(n). - _Enrique Pérez Herrero_, Sep 18 2012
%Y A061019 Cf. A000027, A001222, A061020, A001615, A158523 (Möbius transform).
%Y A061019 Cf. A027746.
%Y A061019 Cf. A239122 (partial sums).
%K A061019 easy,nice,sign,mult
%O A061019 1,2
```
### A119972
```
%N A119972 a(n) = n * A034947(n).
%C A119972 Previous name was: Flag n when the first difference of the decimal encoding of the Gray code is negative. (With "flag" meaning negate n when the difference is negative.)
%C A119972 Merge A091072 with minus A091067 maintaining increasing absolute value.
%F A119972 a(n) = n*Kronecker(-1, n) = n * A034947(n). - _Andrew Howroyd_, Aug 06 2018
%Y A119972 Cf. A034947, A003188, A055975, A091067, A091072.
%K A119972 easy,sign,mult
%O A119972 1,2
```

## Candidate 42: A058650 vs A112177 (score 48.0, agree 80, variant abs, family size 2)
Terms: 1, 2, 0, -1, 2, 0, 0, 2, 0, -2, 6, 0, 2, 6, 0, -1, 8, 0, 2, 14, 0, -2, 16, 0, 3, 20, 0, -4, 32, 0

### A058650
```
%N A058650 McKay-Thompson series of class 36c for Monster.
%F A058650 Expansion of A + 2*q/A, where A = q^(1/2)*(eta(q^3)*eta(q^9)/(eta(q^6)* eta(q^18))), in powers of q. - _G. C. Greubel_, Jun 23 2018
%Y A058650 Cf. A000521, A007240, A014708, A007241, A007267, A045478, etc.
%K A058650 sign
%O A058650 -1,2
```
### A112177
```
%N A112177 McKay-Thompson series of class 36h for the Monster group.
%F A112177 Expansion of A - 2*q/A, where A = q^(1/2)*(eta(q^3)*eta(q^9)/(eta(q^6)* eta(q^18))), in powers of q. - _G. C. Greubel_, Jun 26 2018
%K A112177 sign
%O A112177 0,2
```

## Candidate 43: A009005 vs A074764 (score 47.6, agree 69, variant drop2, family size 9)
Terms: 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33

### A009005
```
%N A009005 All natural numbers except 1, 2 and 4.
%C A009005 Short legs of Pythagorean triangles.
%C A009005 Also the natural numbers n such that there is an open knight's tour of the 4 X n chessboard. - Sharon Sela (sharonsela(AT)hotmail.com), Jan 02 2002
%C A009005 Also perimeters of integral triangles; equivalently, numbers n = a + b + c, where a + b > c, a + c > b, b + c > a, and a, b, c are integers (necessarily a, b, c, and n are positive). - _Rick L. Shepherd_, Aug 04 2013
%C A009005 Along with 0, possible scores in rugby union, where points can be scored with a penalty goal or drop goal (3 points), try (5 points) and converted try (7 points). - _Charles R Greathouse IV_, Sep 10 2016
%C A009005 Also the positive integers n such that floor(t(n+2)/(t(n+2) - sigma(n+2))) = 1, where t(n) = n*(n+1)/2 = A000217(n) and sigma(n) = A000203(n) (see A242963). - _Lorenzo Sauras Altuzarra_, Jan 29 2020
%F A009005 O.g.f.: x(3-x-x^2)/(1-x)^2. a(n)=A009056(n), n>1. - _R. J. Mathar_, May 26 2008
%Y A009005 Cf. A000203 (sigma function), A000217 (triangular numbers), A242963.
%K A009005 nonn,easy
%O A009005 1,1
```
### A074764
```
%N A074764 Numbers of smaller squares into which a square may be dissected.
%C A074764 All even k > 2 are present by generalizing this corner+border construction, all odd k > 5 are present because k+3 can be obtained from k by splitting any single square into four, 1 is trivially present and k = 2, 3 & 5 are then fairly easily eliminated.
%C A074764 Also number of smaller similar triangles into which a triangle may be dissected. - _Lekraj Beedassy_, Nov 25 2003 [This isn't true; for example, an isosceles right triangle can be dissected in 2 and therefore into any positive integer number of smaller similar triangles. - _M. F. Hasler_, May 24 2024]
%C A074764 Also positive integers k such that there exist k integers x_1, x_2, ..., x_k, distinct or not, satisfying 1 = 1/(x_1)^2 + 1/(x_2)^2 + ... + 1/(x_k)^2. For example, the unique solution for k = 4 is 1 = 1/2^2 + 1/2^2 + 1/2^2 + 1/2^2 (see Hassan Tarfaoui link, Concours Général 1990). - _Bernard Schott_, Oct 05 2021
%C A074764 With the current definition, one could argue that the initial 1 is wrong and should be 0 instead: One cannot dissect a square into 1 smaller square: not dissecting it yields a(1) = 0 smaller squares. - _M. F. Hasler_, May 24 2024
%F A074764 {k : k != 2, 3, or 5}.
%F A074764 G.f. of characteristic function: x*(1 - x + x^3 - x^4 + x^5)/(1-x).
%F A074764 G.f.: x*(1 + 2*x -x^2 - x^3)/(1 - x)^2. - _Georg Fischer_, Aug 17 2021
%F A074764 a(n) = n + 3 for all n > 2. - _M. F. Hasler_, May 24 2024
%F A074764 E.g.f.: exp(x)*(3 + x) - x^2/2 - 3*(x + 1). - _Stefano Spezia_, Sep 17 2024
%Y A074764 Cf. A005792, A014544 (cubes).
%K A074764 nonn,easy
%O A074764 1,2
```

## Candidate 44: A171893 vs A355497 (score 46.9, agree 68, variant drop2, family size 5)
Terms: 1, 2, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37

### A171893
```
%N A171893 1, 2 and all numbers >= 10.
%C A171893 Used to illustrate Besicovitch's density theorem.
%C A171893 Equals A171891 + A171892, where + denotes the usual sum of two sequences.
%Y A171893 Cf. A171891, A171892.
%K A171893 nonn,easy
%O A171893 1,2
```
### A355497
```
%N A355497 Numbers k such that x^2 - s*x + p has only integer roots, where s and p denote the sum and product of the digits of k respectively.
%C A355497 All 2-digit numbers are terms.
%C A355497 All numbers having 0 as a digit (A011540) are terms, because p = 0, x^2 - s*x + p = x*(x-s) and the roots 0 and s are integers.
%F A355497 a(n) = n + O(n^k) where k = log(9)/log(10) = 0.95424.... - _Charles R Greathouse IV_, Jul 07 2022
%Y A355497 Complement of A355547. A011540 is a subsequence.
%Y A355497 Cf. A007953, A007954, A355574 (number of n-digit terms).
%K A355497 nonn,base
%O A355497 1,2
```

## Candidate 45: A058648 vs A112174 (score 46.8, agree 78, variant abs, family size 2)
Terms: 1, -1, 0, 2, 2, 0, 3, -1, 0, 4, 0, 0, 5, 0, 0, 8, 2, 0, 11, -4, 0, 16, 4, 0, 21, -4, 0, 26, 2, 0

### A058648
```
%N A058648 McKay-Thompson series of class 36a for Monster.
%F A058648 Expansion of A - q/A, where A = q^(1/2)*(eta(q^6)*eta(q^9)/( eta(q^3)* eta(q^18)))^2, in powers of q. - _G. C. Greubel_, Jun 23 2018
%Y A058648 Cf. A000521, A007240, A014708, A007241, A007267, A045478, etc.
%K A058648 sign
%O A058648 -1,4
```
### A112174
```
%N A112174 McKay-Thompson series of class 36d for the Monster group.
%F A112174 Expansion of A + q/A, where A = q^(1/2)*(eta(q^6)*eta(q^9)/( eta(q^3)* eta(q^18)))^2, in powers of q. - _G. C. Greubel_, Jun 26 2018
%K A112174 sign
%O A112174 0,4
```

## Candidate 46: A112197 vs A112198 (score 46.2, agree 77, variant abs, family size 2)
Terms: 1, 1, 1, -1, 1, 0, 2, -1, 2, 1, 3, -1, 4, 1, 4, 0, 5, 1, 7, -2, 8, 1, 10, -1, 12, 2, 14, -2, 17, 3

### A112197
```
%N A112197 McKay-Thompson series of class 56b for the Monster group.
%F A112197 Expansion of A + q/A, where A = q^(1/2)*eta(q^4)*eta(q^14)/(eta(q^2)* eta(q^28)), in powers of q. - _G. C. Greubel_, Jul 01 2018
%K A112197 sign
%O A112197 0,7
```
### A112198
```
%N A112198 McKay-Thompson series of class 56c for the Monster group.
%F A112198 Expansion of A - q/A, where A = q^(1/2)*(eta(q^4)*eta(q^14)/(eta(q^2)* eta(q^28))), in powers of q. - _G. C. Greubel_, Jul 01 2018
%K A112198 sign
%O A112198 0,7
```

## Candidate 47: A284676 vs A284679 (score 44.8, agree 65, variant drop1, family size 3)
Terms: 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 18, 20, 21, 22, 24, 25, 26, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39

### A284676
```
%N A284676 Positions of 1 in A284674; complement of A284675.
%C A284676 Conjecture: -1 < n*r - a(n) < 4 for n >= 1, where r = (-1+sqrt(13))/2.
%Y A284676 Cf. A284674, A284675, A284679.
%K A284676 nonn,easy
%O A284676 1,1
```
### A284679
```
%N A284679 Positions of 1 in A284677; complement of A284678.
%C A284679 Conjecture: -1 < n*r - a(n) < 1 for n >= 1, where r = (-1+sqrt(13))/2.
%C A284679 Appears to differ from A284676 only at a(1). - _R. J. Mathar_, Apr 24 2017
%Y A284679 Cf. A284677, A284678.
%K A284679 nonn,easy
%O A284679 1,2
```

## Candidate 48: A163300 vs A272651 (score 44.8, agree 65, variant drop1, family size 17)
Terms: 0, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60

### A163300
```
%N A163300 Even numbers without 2.
%C A163300 Union of A163300 and A014076 = A141468.
%C A163300 From _Omar E. Pol_, Aug 04 2009: (Start)
%C A163300 Zero together with the even nonprimes.
%C A163300 The nonprime numbers (A018252) begin: 1,4,6,8,9,10,12,14,15,... So the words "prime" and "nonprime" normally refer to the natural numbers or positive integers: 1,2,3,4,5,6,... (Zero is not a member of A018252. See also the definition of A141468). (End)
%F A163300 a(n) = 2*A087156(n).
%F A163300 From _Elmo R. Oliveira_, May 20 2026: (Start)
%F A163300 G.f.: 2*x^2*(2 - x)/(1 - x)^2.
%F A163300 E.g.f.: 2*x*(exp(x) - 1).
%F A163300 a(n) = 2*a(n-1) - a(n-2) for n >= 4. (End)
%Y A163300 Cf. A014076, A018252, A087156, A141468, A163300.
%K A163300 nonn,easy
%O A163300 1,2
```
### A272651
```
%N A272651 The no-3-in-line problem: maximal number of points from an n X n square grid so that no three lie on a line.
%C A272651 It is conjectured that a(n) < 2*n for all sufficiently large n.
%C A272651 A000769 has an extensive list of references and links.
%C A272651 2*n is a trivial upper bound, because if you pick 2*n+1 points, then some three must lie on a horizontal line. - _Warren D. Smith_, May 10 2015
%C A272651 Apart from the offset this may be the same as A103517. - _R. J. Mathar_, May 13 2016
%C A272651 For all 1 < n <= 66, it is known that a(n) = 2n. Solutions with 2n points are also known for n = 68 and n = 70. No value n > 1 for which a(n) < 2*n is currently known. - _Donghwi Park_, Jun 20 2026
%Y A272651 Cf. A000769, A103517.
%K A272651 nonn,more
%O A272651 1,2
```

## Candidate 49: A020914 vs A204399 (score 44.8, agree 65, variant drop1, family size 5)
Terms: 1, 2, 4, 5, 7, 8, 10, 12, 13, 15, 16, 18, 20, 21, 23, 24, 26, 27, 29, 31, 32, 34, 35, 37, 39, 40, 42, 43, 45, 46

### A020914
```
%N A020914 Number of digits in the base-2 representation of 3^n.
%C A020914 Also, numbers k such that the first digit in the ternary expansion of 2^k is 1. - Mohammed Bouayoun (Mohammed.bouayoun(AT)sanef.com), Apr 24 2006
%C A020914 a(n) is the smallest integer such that n/a(n) < log_2(3). - Trevor G. Hyde (thyde12(AT)amherst.edu), Jul 31 2008
%C A020914 This sequence represents allowable values of the "dropping time" in the Collatz (3x+1) problem when iterated according to the function f(n) := n/2 if n is even, (3n+1)/2 otherwise, as tabulated in A126241. There is one exception, A126241(1), which has been set to zero by convention. - _K. Spage_, Oct 22 2009
%C A020914 An integer k is a term of A020914 if and only if floor(k*(1 + log(2)/log(3))) - abs(k-1)*(1 + log(2)/log(3)) - 1 >= 0. - _K. Spage_, Oct 22 2009
%C A020914 Also smallest k such that ceiling(2^k / 3^n) = 2. - _Michel Lagneau_, Jan 31 2012
%C A020914 For n > 0, first differences of A022330. - _Michel Marcus_, Oct 03 2013
%C A020914 Also the number of powers of two less than or equal to 3^n. - _Robert G. Wilson v_, May 25 2014
%C A020914 Except for 1, A020914 is the complement of A054414 and therefore these two form a pair of Beatty sequences. - _Robert G. Wilson v_, May 25 2014
%F A020914 a(n) = floor(1 + n*log(3)/log(2)). - _K. Spage_, Oct 22 2009
%F A020914 a(0) = 1, a(n+1) = a(n) + A022921(n). - _K. Spage_, Oct 23 2009
%F A020914 a(n) = A122437(n-1) - n. - _K. Spage_, Oct 23 2009
%F A020914 A098294(n) = a(n) + n for n > 0. - _Mike Winkler_, Dec 31 2010
%F A020914 a(n) = A070939(A000244(n)) = length of n-th row in triangle A227048. - _Reinhard Zumkeller_, Jun 30 2013
%F A020914 a(n) = 1 + floor(n*log_2(3)) = 1 + A056576(n) = 1 + floor(n*A020857). - _L. Edson Jeffery_, Dec 12 2014
%F A020914 A020915(a(n)) = n + 1. - _Reinhard Zumkeller_, Mar 28 2015
%Y A020914 Cf. A056576, A054414, A070939, A000244, A227048, A022330, A022921 (first differences), A126241.
%Y A020914 Cf. A020857 (decimal expansion of log_2(3)).
%Y A020914 Cf. A020915.
%Y A020914 Cf. A204399 (essentially the same).
%K A020914 nonn,base,easy
%O A020914 0,2
```
### A204399
```
%N A204399 Numbers k such that floor(2^k / 3^n) = 1.
%C A204399 Presumably a(n) ~ 3*n - floor(n*sqrt(2)) = A195176(n). In the first hundred, a(n) = A195176(n) except for n = 41, 70, 82, 94 where a(n) = A195176(n) - 1.
%C A204399 The conjecture is false; A195176(n) - a(n) increases without bound (though not monotonically) since log_2(3) < 3 - sqrt(2). - _Charles R Greathouse IV_, Jan 15 2012
%C A204399 Basically a duplicate of A020914. - _R. J. Mathar_, Jan 16 2012
%F A204399 a(n) = ceiling( n * log_2(3) ). - _Charles R Greathouse IV_, Jan 15 2012
%Y A204399 Cf. A020914, A056576.
%K A204399 nonn
%O A204399 0,2
```

## Candidate 50: A224067 vs A224165 (score 44.4, agree 74, variant drop1, family size 2)
Terms: 1, 5, 5, 13, 9, 5, 13, 5, 9, 5, 17, 9, 13, 13, 5, 9, 21, 9, 9, 17, 0, 5, 9, 5, 13, 13, 13, 13, 17, 5

### A224067
```
%N A224067 Number of cycles the reduced complex Collatz function using 1 + (2n-1)i takes to hit 1 + i, or 0 if this never happens.
%C A224067 The complex Collatz function takes a complex number z to 3iz + (1+i). The resulting real part is divided by 2 until it's odd, and the same for the imaginary part.
%C A224067 The effect here is that say 4 + 14i is reduced to 1 + 7i.
%C A224067 The reduced complex Collatz function does all this in the same cycle.
%C A224067 Equals 0 for n = 21, 33, 52, 64, 65, 81, 82, 101, 103, 127, 129, 130, 163, 201, 204, 206, 253, 254, 256, 258, 259, 313...
%C A224067 This is conjectured to be infinite and the same as in A224165.
%C A224067 For example, 1 + 41i yields -61 + 1i, -1 + -91i, 137 + -1i, 1 + 103i, -77 + 1i, -1 + -115i, 173 + -1i, 1 + 65i, -97 + 1i, -1 + -145i, 109 + -1i, 1 + 41i - cyclic period 12.
%C A224067 From _Robert G. Wilson v_, Apr 04 2013: (Start)
%C A224067 If n>0 a(n) is odd, if n<1 a(n) is even. In fact, for n>0, a(n) is of the form 4k-3 and for n<1, a(n) is of the form 4k-2.
%C A224067 For a(k)=0 for k: 21, 33, 52, 64, 65, 81, 82, 101, 103, 127, 129, 130, 163, 201, 204, 206, 253, 254, 256, 258, 259, 313, 317, 320, 322, 324, 326, 396, 400, 401, 402, 404, 405, 407, 408, 409, 410, 501, 505, 506, 508, 511, 512, 514, 515, 518, 625, 635, 639, 641, 643, 645, 647, 648, 650, 791, 799, 800, 802, 803, 807, 811, 812, 814, 815, 816, 819, 822, 988, 989, 1003, ... .
%C A224067 Amongst the first 100000 positive terms, 6.726% are 0.
%C A224067 The first occurrence of 4k-3 occurs at: 1, 2, 5, 4, 11, 17, 49, 77, 61, 96, 76, 476, 377, 301, 509, 804, 587, 941, 1585, 1669, 1348, 533, 1683, 333, 132, 208, 656, 260, 820, 2585, 4091, 3229, 5101, 8068, 6381, 1261, 3980, 3148, 2485, 15684, 12409, 4907, 15473, 6125, 9681, 3825, 6044, 19100, 60235, 23797, 37605, 59425, 23477, 37099, 29313, 23161, ... .
%C A224067 The first negative terms beginning at 0: {2, 6, 2, 10, 6, 14, 6, 10, 6, 6, 2, 14, 6, 10, 10, 14, 6, 6, 6, 22, 10, 14, 14, 14, 14, 6, 6, 10, 0, 10, 10, 6, 14, 6, 6, 0, 18, 18, 6, 10, 10, 10, 2, 14, 10, 0, 14, 14, 14, 14, 6, 18, 10, 34, 10, 10, 6, 0, 10, 34, 22, 10, 14, 14, 14, 14, 6, 18, 18, 18, 6, ... .
%C A224067 For a(-k)=0 for k: {28, 35, 45, 57, 72, 112, 114, 142, 143, 144, 145, 175, 179, 180, 182, 224, 225, 228, 229, 230, 277, 283, 285, 287, 288, 289, 290, 356, 361, 363, 444, 448, 449, 450, 453, 456, 457, 458, 563, 567, 570, 572, 574, 575, 577, 578, 582, 702, 709, 711, 712, 713, 716, 718, 722, 724, 727, 728, 730, 877, 889, 896, 897, 898, 900, 901, 902, 907, 908, 909, 911, 912, 913, 914, 916, 918, 919, 920, 922, 1110, ... .
%C A224067 Amongst the first 100000 negative terms, 7.256% are 0.
%C A224067 The first occurrence of 4k-2, beginning with n=0, occurs at: 0, 1, 3, 5, 36, 19, 95, 75, 53, 84, 133, 211, 668, 571, 451, 659, 1043, 892, 1876, 1515, 1171, 1892, 747, 147, 116, 368, 291, 460, 1453, 2300, 3635, 2869, 4533, 14341, 2835, 2240, 3540, 2797, 4416, 6979, 5519, 17427, 6891, 10887, 8604, 1699, 5371, 33955, 53541, 42304, 66851, 52821, 41735, 65952, 13027, 82347, ... .
%C A224067 (End)
%Y A224067 Cf. A224165.
%K A224067 nonn,less
%O A224067 1,2
```
### A224165
```
%N A224165 Number of cycles the reduced complex Collatz function using 3 + (2n-1)i takes to hit 1 + i, or 0 if this never happens.
%C A224165 The complex Collatz function takes a complex number z to 3iz + (1+i). The resulting real part is divided by 2 until it's odd, and the same for the imaginary part.
%C A224165 The effect here is that say 4 + 14i is reduced to 1 + 7i.
%C A224165 The reduced complex Collatz function does all this in the same cycle.
%C A224165 Equals 0 for n = 21, 33, 52, 64, 65, 81, 82, 101, 103, 127, 129, 130, 163, 201, 204, 206, 253, 254...
%C A224165 This is conjectured to be infinite and the same as in A224067.
%C A224165 For example, 3 + 41i yields -61 + 5i, -7 + -91i, 137 + -5i, 1 + 103i, -77 + 1i, -1 + -115i, 173 + -1i, 1 + 65i, -97 + 1i, -1 + -145i, 109 + -1i, 1 + 41i, -61 + 1i, -1 + -91i, 137 + -1i, 1 + 103i, -77 + 1i, -1 + -115i, 173 + -1i, 1 + 65i, -97 + 1i, -1 + -145i, 109 + -1i, 1 + 41i, which becomes cyclic about 1 + 41i.
%Y A224165 Cf. A224067.
%K A224165 nonn,less
%O A224165 1,1
```

## Candidate 51: A288708 vs A288712 (score 44.2, agree 64, variant drop2, family size 3)
Terms: 1, 2, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 34, 35, 36, 37

### A288708
```
%N A288708 Positions of 0 in A288707; complement of A288709.
%C A288708 Conjecture:  a(n)/n -> -1 + sqrt(5), and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
%C A288708 Proof of this conjecture. One follows the same strategy as in the proof of the conjecture in A288709. We have a(n)/n -> -1 + sqrt(5) if and only if n/a(n) -> (1+sqrt(5))/4, which is the frequency of 0's in A288707. If alpha = (3-sqrt(5))/2 is the frequency of 1's in y = A189661 = 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, ... then (2*(1-alpha)+alpha)/2 is the frequency of 0's in A288707, since every 0 in y produces 2 zeros in A288707, and every 1 just 1 zero (and one 1). One computes (2*(1-alpha)+alpha)/2 = (1+sqrt(5))/4. The bounds follow from the exponential convergence of the frequencies of 0 and 1 in y. - _Michel Dekking_, Oct 19 2018
%Y A288708 Cf. A288707, A288709.
%K A288708 nonn,easy
%O A288708 1,2
```
### A288712
```
%N A288712 Positions of 0 in A288711; complement of A288713.
%C A288712 Conjecture: a(n)/n -> -1 + sqrt(5), and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
%C A288712 Appears to differ from A288708 only at a(1). - _R. J. Mathar_, Jun 19 2017
%Y A288712 Cf. A288711, A288713.
%K A288712 nonn,easy
%O A288712 1,1
```

## Candidate 52: A065620 vs A104895 (score 43.8, agree 73, variant abs, family size 2)
Terms: 0, 1, 2, -1, 4, -3, -2, 3, 8, -7, -6, 7, -4, 5, 6, -5, 16, -15, -14, 15, -12, 13, 14, -13, -8, 9, 10, -9, 12, -11

### A065620
```
%N A065620 a(0)=0; thereafter a(2n) = 2a(n), a(2n+1) = -2a(n) + 1.
%C A065620 Reversing binary value of n: convert sum of powers of 2 in binary representation of n to alternating sum.
%C A065620 The alternation is applied only to the nonzero bits and does not depend on the exponent of 2. All integers have a unique reversing binary representation (see cited Knuth exercise for proof).
%F A065620 a(n) = if n<2 then n else b+2*(1-2*b)*a((n-b)/2) where b is the least significant bit in n.
%F A065620 From _Antti Karttunen_, Aug 18 2014: (Start)
%F A065620 a(n) = A246160(n) - A246159(n).
%F A065620 a(A065621(n)) = n.
%F A065620 a(A048724(n)) = -n. (End)
%F A065620 a(n) = -A104895(n). - _M. F. Hasler_, Apr 16 2018
%F A065620 a(n) = (2*A265263(n) - n) * (2*A010060(n) - 1). - _Alan Michael Gómez Calderón_, Jul 01 2025
%Y A065620 Cf. A010060, A048724, A065621, A246159, A246160, A265263.
%Y A065620 The negative of entry A104895.
%K A065620 base,easy,sign,look
%O A065620 0,3
```
### A104895
```
%N A104895 a(0)=0; thereafter a(2n) = -2*a(n), a(2n+1) = 2*a(n) - 1.
%C A104895 Columns of table in A104894 written in base 10.
%C A104895 Conjecture: the positions where 0, 1, 2, 3, ... appear are given by A048724; the positions where -1, -2, -3, ... appear are given by A065621.
%F A104895 a(0) = 0 and for k>=0, 0<= j <2^k, a(2^k + j) = a(j) + 2^k if a(j)<0, a(2^k + j) = a(j) - 2^k if a(j)>=0.
%F A104895 Sum_{0 <= n <= 2^k - 1} a(n) = - 2^(k-1).
%F A104895 Sum_{0 <= n <= 2^k - 1} |a(n)| = 4^(k-1).
%F A104895 a(n) = -A065620(n). - _M. F. Hasler_, Apr 16 2018
%Y A104895 Cf. A048724, A065621, A104894.
%Y A104895 The negative of entry A065620.
%K A104895 sign,look,nice
%O A104895 0,3
```

## Candidate 53: A285074 vs A285077 (score 43.5, agree 63, variant drop1, family size 7)
Terms: 1, 3, 5, 7, 8, 10, 12, 13, 15, 17, 19, 20, 22, 24, 25, 27, 29, 31, 32, 34, 36, 37, 39, 41, 42, 44, 46, 48, 49, 51

### A285074
```
%N A285074 Positions of 0 in A285073; complement of A285075.
%C A285074 Conjecture: -1 < n*r - a(n) < 1 for n>=1, where r = 1 + sqrt(1/2).
%C A285074 From _Michel Dekking_, May 30 2017: (Start)
%C A285074 Proof of a stronger form of the conjecture: the sequence d:=A285073 can be written as d=01c, where c is the homogeneous Sturmian sequence with slope alpha = sqrt(2)-1 (see comments of A285073). Changing from alpha to 1-alpha = 2-sqrt(2) turns c into its mirror image, so we have to find the positions of 1 in this new sequence.
%C A285074 In general, a homogeneous Sturmian sequence (floor((n+1)*r)-floor(n*r)) gives the positions of 1 in the Beatty sequence b=(floor((n+1)*s)), where s=1/r.
%C A285074 In our case s = 1/(2-sqrt(2)) = 1+sqrt(1/2). It follows that for n=0,1,... one has a(n+2) = floor((n+1)*(1+sqrt(1/2))) + 2, which directly implies that sqrt(1/2)-1 < n*r - a(n) < sqrt(1/2), which is a strengthening of the conjecture (actually there is no strict inequality for n=1: r-a(1) = sqrt(1/2)). (End)
%Y A285074 Cf. A285073, A285075, A285076.
%K A285074 nonn,easy
%O A285074 1,2
```
### A285077
```
%N A285077 Positions of 0 in A285076; complement of A285078.
%C A285077 Conjecture: -1 < n*r - a(n) < 1 for n>=1, where r = 1 + sqrt(1/2).
%C A285077 This conjecture can be proved in the same way as the conjecture on A285074. - _Michel Dekking_, May 30 2017
%C A285077 Appears to differ from A285074 only at a(1). - _R. J. Mathar_, Apr 24 2017
%C A285077 This is correct, and follows from the fact that A285073 and A285076 are equal except for the first two terms which are respectively 0,1 and 1,0. (See Comments for A285073.) - _Michel Dekking_, May 30 2017
%Y A285077 Cf. A285074, A285076, A285078.
%K A285077 nonn,easy
%O A285077 1,1
```

## Candidate 54: A171463 vs A243427 (score 43.5, agree 63, variant drop1, family size 13)
Terms: 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32

### A171463
```
%N A171463 The natural numbers excluding 2 and 3.
%C A171463 Numbers k > 0 such that k*(k+1)/2 - 1 is nonprime. - _Juri-Stepan Gerasimov_, May 04 2010
%F A171463 a(n) = n + [n>1]*2.
%K A171463 nonn,easy
%O A171463 1,2
```
### A243427
```
%N A243427 Floored (rational) values of sqrt(xy) such that sqrt(x) + sqrt(y) = sqrt(xy).
%C A243427 (n + 1)^2/n = (n + 2 + 1/n) so for n>1 yields n+2 under the floor operation.
%C A243427 Consider sqrt(x) + sqrt(y) = sqrt(xy). If we let y=d^2*x, then the LHS becomes (1+d)sqrt(x) and the RHS becomes dx. Divide both sides by sqrt(x), take the d from the RHS to the LHS and square giving x=((1+d)/d)^2, and so y is (1+d)^2 and the original RHS is now (1+d)^2/d. This sequence is concerned with d being an integer.
%C A243427 Has solutions for all x<>1.
%F A243427 a(n) = floor((n + 1)^2/n).
%F A243427 a(n) = n + 2 for n>1.
%K A243427 nonn,easy
%O A243427 1,1
```

## Candidate 55: A072872 vs A135359 (score 43.2, agree 72, variant drop1, family size 2)
Terms: 1, 2, 4, 4, 3, 4, 11, 8, 5, 14, 7, 4, 10, 16, 16, 16, 30, 16, 30, 16, 11, 58, 75, 16, 34, 10, 5, 16, 6, 16

### A072872
```
%N A072872 a(n) is the smallest positive number k such that n divides 2^k - k.
%C A072872 If n is a power of 2, a(n) = n. Conjecture : if n > 47, a(n) < prime(n).
%Y A072872 See A135359 for another version.
%Y A072872 Cf. A247248.
%K A072872 nonn,easy
%O A072872 1,2
```
### A135359
```
%N A135359 a(n) is the smallest nonnegative number k such that n divides 2^k-k.
%Y A135359 See A072872 for another version.
%K A135359 nonn
%O A135359 1,2
```

## Candidate 56: A019425 vs A265722 (score 42.0, agree 70, variant drop2, family size 2)
Terms: 0, 1, 1, 4, 1, 8, 1, 12, 1, 16, 1, 20, 1, 24, 1, 28, 1, 32, 1, 36, 1, 40, 1, 44, 1, 48, 1, 52, 1, 56

### A019425
```
%N A019425 Continued fraction for tan(1/2).
%C A019425 From _Peter Bala_, Nov 17 2019: (Start)
%C A019425 The simple continued fraction expansion for tan(1/2) may be derived by setting z = 1/2 in Lambert's continued fraction tan(z) = z/(1 - z^2/(3 - z^2/(5 - ... ))) and, after using an equivalence transformation, making repeated use of the identity 1/(n - 1/m) = 1/((n - 1) + 1/(1 + 1/(m - 1))).
%C A019425 The same approach produces the simple continued fraction expansions for the numbers tan(1/n), n*tan(1/n) and 1/n*tan(1/n) for n = 1,2,3,.... [added Oct 03 2023: and, even more generally, the simple continued fraction expansions for the numbers d*tan(1/n) and 1/d*tan(1/n), where d divides n. See A019429 for an example]. (End)
%F A019425 a(n) = n - 1/2 - (n-3/2)*(-1)^n + binomial(1,n) - 2*binomial(0,n). - _Paul Barry_, Oct 25 2007
%F A019425 From _Philippe Deléham_, Feb 10 2009: (Start)
%F A019425 a(n) = 2*a(n-2) - a(n-4), n>=6.
%F A019425 G.f.: (x + x^2 + 2*x^3 - x^4 + x^5)/(1-x^2)^2. (End)
%F A019425 From _Peter Bala_, Nov 17 2019; (Start)
%F A019425 Related simple continued fraction expansions:
%F A019425 2*tan(1/2) = [1, 10, 1, 3, 1, 26, 1, 7, 1, 42, 1, 11, 1, 58, 1, 15, 1, 74, 1, 19, 1, 90, ...]
%F A019425 (1/2)*tan(1/2) = [0; 3, 1, 1, 1, 18, 1, 5, 1, 34, 1, 9, 1, 50, 1, 13, 1, 66, 1, 17, 1, 82, ...]. (End)
%Y A019425 Cf. A161011 (decimal expansion). Cf. A019426 through A019433.
%K A019425 nonn,cofr
%O A019425 0,4
```
### A265722
```
%N A265722 Number of ON (black) cells in the n-th iteration of the "Rule 1" elementary cellular automaton starting with a single ON (black) cell.
%F A265722 Conjectures from _Colin Barker_, Dec 14 2015 and Apr 16 2019: (Start)
%F A265722 a(n) = 1/2*(-2*(-1)^n*n+2*n+3*(-1)^n-1).
%F A265722 a(n) = 2*a(n-2) - a(n-4) for n>3.
%F A265722 G.f.: (1-x^2+4*x^3) / ((1-x)^2*(1+x)^2).
%F A265722 (End)
%F A265722 a(n) = A019425(n), n>1. - _R. J. Mathar_, Jan 10 2016
%Y A265722 Cf. A265718, A265720, A265721.
%K A265722 nonn,easy
%O A265722 0,4
```

## Candidate 57: A071051 vs A267447 (score 42.0, agree 70, variant drop1, family size 2)
Terms: 1, 3, 4, 7, 4, 8, 8, 15, 4, 8, 8, 16, 8, 16, 16, 31, 4, 8, 8, 16, 8, 16, 16, 32, 8, 16, 16, 32, 16, 32

### A071051
```
%N A071051 Number of 1's in n-th row of triangle in A071035.
%C A071051 Number of ON cells at generation n of 1-D CA defined by Rule 126, starting with a single ON cell. - _N. J. A. Sloane_, Aug 09 2014
%F A071051 a(2n) = a(n)+A036987(n); a(2n+1) = a(n)+2*2^A000120(n). - _Benoit Cloitre_, Sep 22 2003
%F A071051 a(n) = 2^(1+wt(n)) unless n is of the form 2^i-1 in which case we must subtract 1, where wt = A000120. - _N. J. A. Sloane_, Aug 09 2014
%F A071051 G.f.: 2*Product_{k>=0} (1+2*x^(2^k)) - Sum_{k>=0} x^(2^k-1). - _N. J. A. Sloane_, Aug 09 2014
%Y A071051 Cf. A001316, A000120, A036987, A000225.
%K A071051 nonn
%O A071051 0,2
```
### A267447
```
%N A267447 Number of OFF (white) cells in the n-th iteration of the "Rule 129" elementary cellular automaton starting with a single ON (black) cell.
%F A267447 Conjecture: a(n) = A071051(n), n>0. - _R. J. Mathar_, Jan 17 2016
%Y A267447 Cf. A267417.
%K A267447 nonn,easy
%O A267447 0,2
```

## Candidate 58: A266256 vs A266662 (score 42.0, agree 70, variant drop2, family size 2)
Terms: 1, 1, 2, 5, 2, 9, 2, 13, 2, 17, 2, 21, 2, 25, 2, 29, 2, 33, 2, 37, 2, 41, 2, 45, 2, 49, 2, 53, 2, 57

### A266256
```
%N A266256 Number of ON (black) cells in the n-th iteration of the "Rule 11" elementary cellular automaton starting with a single ON (black) cell.
%F A266256 Conjectures from _Colin Barker_, Dec 27 2015 and Apr 14 2019: (Start)
%F A266256 a(n) = (-2*((-1)^n-1)*n+3*(-1)^n+1)/2 for n>0.
%F A266256 a(n) = 2*a(n-2)-a(n-4) for n>4.
%F A266256 G.f.: (1+x+3*x^3-x^4) / ((1-x)^2*(1+x)^2).
%F A266256 (End)
%Y A266256 Cf. A266253.
%K A266256 nonn,easy
%O A266256 0,3
```
### A266662
```
%N A266662 Number of ON (black) cells in the n-th iteration of the "Rule 47" elementary cellular automaton starting with a single ON (black) cell.
%F A266662 Conjectures from _Colin Barker_, Jan 03 2016 and Apr 18 2019: (Start)
%F A266662 a(n) = (-2*(-1)^n*n+2*n+3*(-1)^n+1)/2 for n>1.
%F A266662 a(n) = 2*a(n-2)-a(n-4) for n>5.
%F A266662 G.f.: (1+2*x+x^3-x^4+x^5) / ((1-x)^2*(1+x)^2).
%F A266662 (End)
%F A266662 a(n) = A266256(n), n>1. - _R. J. Mathar_, Jan 10 2016
%Y A266662 Cf. A266659.
%K A266662 nonn,easy
%O A266662 0,2
```

## Candidate 59: A266258 vs A266664 (score 42.0, agree 70, variant drop2, family size 2)
Terms: 0, 2, 3, 2, 7, 2, 11, 2, 15, 2, 19, 2, 23, 2, 27, 2, 31, 2, 35, 2, 39, 2, 43, 2, 47, 2, 51, 2, 55, 2

### A266258
```
%N A266258 Number of OFF (white) cells in the n-th iteration of the "Rule 11" elementary cellular automaton starting with a single ON (black) cell.
%F A266258 Conjectures from _Colin Barker_, Dec 27 2015 and Apr 14 2019: (Start)
%F A266258 a(n) = (2*(-1)^n*n+2*n-3*(-1)^n+1)/2 for n>0
%F A266258 a(n) = 2*a(n-2)-a(n-4) for n>4.
%F A266258 G.f.: x*(2+3*x-2*x^2+x^3) / ((1-x)^2*(1+x)^2).
%F A266258 (End)
%Y A266258 Cf. A266253.
%K A266258 nonn,easy
%O A266258 0,2
```
### A266664
```
%N A266664 Number of OFF (white) cells in the n-th iteration of the "Rule 47" elementary cellular automaton starting with a single ON (black) cell.
%F A266664 Conjectures from _Colin Barker_, Jan 03 2016 and Apr 18 2019: (Start)
%F A266664 a(n) = (2*(-1)^n*n+2*n-3*(-1)^n+1)/2 for n>1.
%F A266664 a(n) = 2*a(n-2)-a(n-4) for n>5.
%F A266664 G.f.: x*(1+3*x+x^3-x^4) / ((1-x)^2*(1+x)^2).
%F A266664 (End)
%F A266664 a(n) = A266258(n), n>1. - _R. J. Mathar_, Jan 10 2016
%Y A266664 Cf. A266659.
%K A266664 nonn,easy
%O A266664 0,3
```

## Candidate 60: A266222 vs A266439 (score 42.0, agree 70, variant drop2, family size 2)
Terms: 0, 1, 5, 0, 9, 0, 13, 0, 17, 0, 21, 0, 25, 0, 29, 0, 33, 0, 37, 0, 41, 0, 45, 0, 49, 0, 53, 0, 57, 0

### A266222
```
%N A266222 Number of OFF (white) cells in the n-th iteration of the "Rule 7" elementary cellular automaton starting with a single ON (black) cell.
%F A266222 Conjectures from _Colin Barker_, Dec 26 2015 and Apr 13 2019: (Start)
%F A266222 a(n) = 1/2*(1+(-1)^n)*(1+2*n) for n>1.
%F A266222 a(n) = 2*a(n-2) - a(n-4) for n>5.
%F A266222 G.f.: x*(1+5*x-2*x^2-x^3+x^4) / ((1-x)^2*(1+x)^2).
%F A266222 (End)
%Y A266222 Cf. A266216.
%K A266222 nonn,easy
%O A266222 0,3
```
### A266439
```
%N A266439 Number of OFF (white) cells in the n-th iteration of the "Rule 23" elementary cellular automaton starting with a single ON (black) cell.
%F A266439 Conjectures from _Colin Barker_, Dec 30 2015 and Apr 15 2019: (Start)
%F A266439 a(n) = ((-1)^n+1)*(2*n+1)/2 for n>0.
%F A266439 a(n) = 2*a(n-2)-a(n-4) for n>4.
%F A266439 G.f.: x^2*(5-x^2) / ((1-x)^2*(1+x)^2).
%F A266439 (End)
%F A266439 a(n) = A266222(n), n>1. - _R. J. Mathar_, Jan 10 2016
%Y A266439 Cf. A266434.
%K A266439 nonn,easy
%O A266439 0,3
```
