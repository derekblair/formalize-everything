## Candidate 61: A353812 vs A353813 (score 125.0, agree 125, variant raw, family size 2)
Terms: 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0

### A353812
```
%I A353812 #11 May 15 2022 17:21:19
%S A353812 0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,1,
%T A353812 0,0,1,0,0,1,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,1,
%U A353812 0,0,0,0,1,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,0,1,0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,0,0,1,0,0,0
%N A353812 a(n) = 1 if sigma(n) is of the form 4m+2, otherwise 0.
%H A353812 Antti Karttunen, <a href="/A353812/b353812.txt">Table of n, a(n) for n = 1..100000</a>
%H A353812 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%H A353812 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>
%F A353812 a(n) = A347870(n) - A353811(n).
%F A353812 a(n) >= A353813(n).
%t A353812 a[n_] := If[Mod[DivisorSigma[1, n], 4] == 2, 1, 0]; Array[a, 100] (* _Amiram Eldar_, May 13 2022 *)
%o A353812 (PARI) A353812(n) = (2==(sigma(n)%4));
%Y A353812 Characteristic function of A191217.
%Y A353812 Cf. A000203, A347870, A353811.
%Y A353812 Differs from A353813 for the first time at n=325, where a(325) = 1, while A353813(325) = 0.
%K A353812 nonn
%O A353812 1
%A A353812 _Antti Karttunen_, May 13 2022
```
### A353813
```
%I A353813 #11 May 16 2022 10:04:13
%S A353813 0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,1,
%T A353813 0,0,1,0,0,1,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,1,
%U A353813 0,0,0,0,1,1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,0,1,0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,0,0,1,0,0,0
%N A353813 a(n) = 1 if n has exactly one prime factor of form 4*k+1 (when counted with multiplicity) and no prime factor 4*k+3 with odd multiplicity, otherwise 0.
%H A353813 Antti Karttunen, <a href="/A353813/b353813.txt">Table of n, a(n) for n = 1..100000</a>
%H A353813 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A353813 a(n) = [A004018(n) == 8], where [ ] is the Iverson bracket.
%F A353813 a(n) <= A353812(n), a(n) <= A353814(n).
%o A353813 (PARI) A353813(n) = { my(f = factor(n), nb1 = 0, p, ep); for(i=1, #f~, p = f[i, 1]; ep = f[i, 2]; if(1==(p%4), nb1++; if((ep>1)||(nb1>1), return(0))); if((3==(p%4)) && (ep%2), return(0))); return(1==nb1); }; \\ After "isok" function in A230779
%o A353813 (PARI)
%o A353813 A004018(n) = if(n<1, n==0, 4 * sumdiv( n, d, (d%4==1) - (d%4==3))); \\ From A004018
%o A353813 A353813(n) = (8==A004018(n));
%Y A353813 Characteristic function of A230779.
%Y A353813 Cf. A004018, A353814.
%Y A353813 Differs from A353812 for the first time at n=325, where a(325) = 0, while A353812(325) = 1.
%K A353813 nonn
%O A353813 1
%A A353813 _Antti Karttunen_, May 14 2022
```


## Candidate 62: A118822 vs A230075 (score 124.2, agree 108, variant abs, family size 3)
Terms: 2, -1, 0, -1, -2, 1, 0, 1, 2, -1, 0, -1, -2, 1, 0, 1, 2, -1, 0, -1, -2, 1, 0, 1, 2, -1, 0, -1, -2, 1

### A118822
```
%I A118822 #25 Jun 07 2025 05:22:09
%S A118822 2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,
%T A118822 -2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,
%U A118822 -1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1,-2,1,0,1,2,-1,0,-1
%N A118822 Numerators of the convergents of the 2-adic continued fraction of zero given by A118821.
%H A118822 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,-1).
%F A118822 Period 8 sequence: [2,-1,0,-1,-2,1,0,1].
%F A118822 G.f.: -x*(x-1)*(x^2+x+2) / ( 1+x^4 ).
%F A118822 a(n) = sqrt((n+1)^2 mod 8)(-1)^floor((n+2)/4). - _Wesley Ivan Hurt_, Jan 01 2014
%e A118822 For n>=1, convergents A118822(k)/A118823(k) are:
%e A118822   at k = 4*n: -1/A080277(n);
%e A118822   at k = 4*n+1: -2/(2*A080277(n)-1);
%e A118822   at k = 4*n+2: -1/(A080277(n)-1);
%e A118822   at k = 4*n-1: 0/(-1)^n.
%e A118822 Convergents begin:
%e A118822   2/1, -1/-1, 0/-1, -1/1, -2/1, 1/0, 0/1, 1/-4,
%e A118822   2/-7, -1/3, 0/-1, -1/5, -2/9, 1/-4, 0/1, 1/-12,
%e A118822   2/-23, -1/11, 0/-1, -1/13, -2/25, 1/-12, 0/1, 1/-16,
%e A118822   2/-31, -1/15, 0/-1, -1/17, -2/33, 1/-16, 0/1, 1/-32, ...
%p A118822 A118822:=n->sqrt((n+1)^2 mod 8)*(-1)^floor((n+2)/4); seq(A118822(n), n=1..100); # _Wesley Ivan Hurt_, Jan 01 2014
%t A118822 Table[Sqrt[Mod[(n+1)^2, 8]](-1)^Floor[(n+2)/4], {n, 100}] (* _Wesley Ivan Hurt_, Jan 01 2014 *)
%o A118822 (PARI) {a(n)=local(p=+2,q=-1,v=vector(n,i,if(i%2==1,p,q*2^valuation(i/2,2)))); contfracpnqn(v)[1,1]}
%o A118822 for(n=0,80,print1(a(n),", "))
%o A118822 (PARI) {a(n) = [2,-1,0,-1,-2,1,0,1][(n-1)%8+1];} \\ _Joerg Arndt_, Jan 02 2014
%Y A118822 Cf. A118821 (partial quotients), A118823 (denominators).
%K A118822 frac,sign,easy
%O A118822 1,1
%A A118822 _Paul D. Hanna_, May 01 2006
```
### A230075
```
%I A230075 #32 Sep 08 2022 08:46:06
%S A230075 2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,
%T A230075 -1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,
%U A230075 0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1,0,-1,2,1,0,1,-2,-1
%N A230075 Period 8: repeat [2, 1, 0, 1, -2, -1, 0, -1].
%C A230075 This is A118825(n+5), n >= 0. (The g.f. given there is not quite correct, because then a(0) = 0  but it should be 1.)
%C A230075 This sequence a(n), n >= 2, is product(2*cos((2*l+1)*Pi/2), l=0..floor((n-2)/2)). This is the unrestricted product which appears in the formula for C(n, 0) with the minimal polynomial C of rho(n):=2*cos(Pi/n) (see A187360), the length ratio (smallest diagonal)/side in the regular n-gon. The restriction gcd(2*l+1, n) = 1 is ineffective for n = 2^k, k>=1, and for n = odd prime p. Therefore norm(rho(n)) = (-1)^delta(n)*C(n, 0) with delta(n) (see A055034) the degree of C, can be computed from the present sequence for these two cases.
%H A230075 Muniru A Asiru, <a href="/A230075/b230075.txt">Table of n, a(n) for n = 0..2000</a>
%H A230075 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,-1).
%F A230075 O.g.f.: (2 + x + x^3) / (1 + x^4).
%F A230075 a(n) = 2*(-1)^(n/4) if n == 0 (mod 4); a(n) == 0 if n == 2 (mod 4); a(n) = (-1)^((n-1)/4) if n == 1 (mod 4); a(n) == (-1)^((n-3)/4) if n == 3 (mod 4).
%F A230075 a(n) = Product_{l=0..floor((n-2)/2)} 2*cos((2*l+1)*Pi/2). Proof via the product formulas for the four (mod 4) cases; see the comments for subsequences like A033999, and the product of the zeros of Chebyshev S-polynomials (A049310) from S(n-1, 0) which is known.
%F A230075 a(n) = sqrt((n+2)^2 mod 8)*(-1)^floor(n/4). - _Wesley Ivan Hurt_, Jan 01 2014
%F A230075 a(n) = (cos(Pi*(2*n+q-r-s)/8)-cos(Pi*(-2*n+q+r-s)/8)+sin(Pi*(-2*n+q-r+s)/8)+3*sin(Pi*(2*n+q+r+s)/8))/2 where q = 1+(-1)^n, r = 2*sin(n*Pi/2) and s = 2*cos(n*Pi/2). - _Wesley Ivan Hurt_, Oct 06 2018
%p A230075 A230075:=n->sqrt((n+2)^2 mod 8)*(-1)^floor(n/4); seq(A230075(n), n=0..100); # _Wesley Ivan Hurt_, Jan 01 2014
%t A230075 Table[Sqrt[Mod[(n+2)^2, 8]](-1)^Floor[n/4], {n, 0, 100}] (* _Wesley Ivan Hurt_, Jan 01 2014 *)
%o A230075 (PARI) a(n)=[2, 1, 0, 1, -2, -1, 0, -1][n%8+1] \\ _Charles R Greathouse IV_, Jul 17 2016
%o A230075 (GAP) Flat(List([1..15],n->[2,1,0,1,-2,-1,0,-1])); # _Muniru A Asiru_, Oct 07 2018
%o A230075 (Magma) &cat [[2, 1, 0, 1, -2, -1, 0, -1]^^20]; // _Wesley Ivan Hurt_, Oct 10 2018
%Y A230075 Cf. A118825, A187360.
%K A230075 sign,easy
%O A230075 0,1
%A A230075 _Wolfdieter Lang_, Oct 23 2013
```


## Candidate 63: A295884 vs A380397 (score 119.6, agree 104, variant drop1, family size 6)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A295884
```
%I A295884 #21 Sep 11 2025 18:36:28
%S A295884 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,
%T A295884 0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,
%U A295884 0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0
%N A295884 Number of exponents larger than 3 in the prime factorization of n.
%C A295884 a(1296) is the first term greater than 1, and a(810000) is the first term greater than 2. - _Harvey P. Dale_, Dec 22 2017
%H A295884 Antti Karttunen, <a href="/A295884/b295884.txt">Table of n, a(n) for n = 1..65537</a>
%H A295884 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A295884 Additive with a(p^e) = 1 when e > 3, 0 otherwise.
%F A295884 a(n) = A295659(n) - A295883(n).
%F A295884 a(n) = A056170(A062378(n)) = A056170(A003557(A003557(n))) = A001221(A003557^3(n)).
%F A295884 a(n) = A001221(A053164(n)) = A001221(A008835(n)).
%F A295884 Asymptotic mean: lim_{n->oo} (1/n) * Sum_{k=1..n} a(k) = Sum_{p prime} 1/p^4 = 0.076993... (A085964). - _Amiram Eldar_, Nov 01 2020
%e A295884 For n = 16 = 2^4, there is one exponent and it is larger than 3, thus a(16) = 1.
%e A295884 For n = 96 = 2^5 * 3^1, there are two exponents, and the other one is larger than 3, thus a(96) = 1.
%e A295884 For n = 1296 = 2^4 * 3^4, there are two exponents larger than 3, thus a(1296) = 2.
%t A295884 Array[Total@ Map[Boole[# > 3] &, FactorInteger[#][[All, -1]]] &, 120] (* _Michael De Vlieger_, Nov 29 2017 *)
%t A295884 Table[Count[FactorInteger[n][[All,2]],_?(#>3&)],{n,130}] (* _Harvey P. Dale_, Dec 22 2017 *)
%o A295884 (Scheme) ;; With memoization-macro definec.
%o A295884 (definec (A295884 n) (if (= 1 n) 0 (+ (if (> (A067029 n) 3) 1 0) (A295884 (A028234 n)))))
%Y A295884 Cf. A000188, A001221, A003557, A008835, A053164, A056170, A062378, A085964, A295659, A295883.
%K A295884 nonn
%O A295884 1,1296
%A A295884 _Antti Karttunen_, Nov 29 2017
```
### A380397
```
%I A380397 #10 Jan 25 2025 08:29:36
%S A380397 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,
%T A380397 0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,
%U A380397 0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0
%N A380397 The number of nonunitary divisors of n that are cubes.
%C A380397 First differs from A295884 at n = 128.
%H A380397 Amiram Eldar, <a href="/A380397/b380397.txt">Table of n, a(n) for n = 1..10000</a>
%F A380397 a(n) = Sum_{d|n, gcd(d, n/d) > 1} [d is cube], where [] is the Iverson bracket.
%F A380397 a(n) = A061704(n) - A380395(n).
%F A380397 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = zeta(3)*(1 - 1/zeta(4)) = 0.091430367833446168224... .
%e A380397 a(16) = 1 since 16 has 1 nonunitary divisor that is a cube, 8 = 2^3.
%e A380397 a(128) = 2 since 128 has 2 nonunitary divisors that are cubes, 8 = 2^3 and 64 = 4^3.
%t A380397 f1[p_, e_] := 1 + Floor[e/3]; f2[p_, e_] := 2^If[Divisible[e, 3], 1, 0]; a[1] = 0; a[n_] := Times @@ f1 @@@ (fct = FactorInteger[n])- Times @@ f2 @@@ fct; Array[a, 100]
%o A380397 (PARI) a(n) = {my(f = factor(n)); prod(i = 1, #f~, 1 + f[i, 2]\3) - prod(i = 1, #f~, 2^if(f[i, 2]%3, 0, 1));}
%Y A380397 Cf. A000578, A048105, A056626, A061704, A295884, A380395, A380396.
%Y A380397 Cf. A002117, A013662.
%K A380397 nonn,easy
%O A380397 1
%A A380397 _Amiram Eldar_, Jan 23 2025
```


## Candidate 64: A036453 vs A040000 (score 118.4, agree 103, variant drop2, family size 11)
Terms: 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2

### A036453
```
%I A036453 #25 Apr 16 2022 21:33:01
%S A036453 1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%T A036453 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%U A036453 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2
%N A036453 a(n) = d(d(d(d(d(n))))), the 5th iterate of the number-of-divisors function d = A000005, with initial value n.
%C A036453 The iterated d function rapidly converges to fixed point 2. In the 5th iterated d-sequence, the first term different from the fixed point 2 appears at n = 5040. The 6th and further iterated sequences have very long initial segment of 2's. In the 6th one the first non-stationary term is a(293318625600) = 3. In such sequences any large value occurs infinite many times and constructible.
%C A036453 Differs from A007395 for n = 1, 5040, 7920, 8400, 9360, 10080, 10800, etc. - _R. J. Mathar_, Oct 20 2008
%H A036453 Charles R Greathouse IV, <a href="/A036453/b036453.txt">Table of n, a(n) for n = 1..10000</a>
%e A036453 E.g., n = 96 and its successive iterates are 12, 6, 4, 3 and 2. The 5th term is a(96) = 2 is stationary (fixed).
%t A036453 Table[Nest[DivisorSigma[0,#]&,n,5],{n,110}] (* _Harvey P. Dale_, Jun 18 2021 *)
%o A036453 (PARI) a(n)=my(d=numdiv);d(d(d(d(d(n))))) \\ _Charles R Greathouse IV_, Apr 07 2012
%Y A036453 Cf. A000005, A010553, A036450, A036452.
%K A036453 nonn
%O A036453 1,2
%A A036453 _Labos Elemer_
%E A036453 Previous Mathematica program replaced by _Harvey P. Dale_, Jun 18 2021
```
### A040000
```
%I A040000 #208 Oct 13 2026 09:24:46
%S A040000 1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%T A040000 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%U A040000 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2
%N A040000 a(0)=1; a(n)=2 for n >= 1.
%C A040000 Continued fraction expansion of sqrt(2) is 1 + 1/(2 + 1/(2 + 1/(2 + ...))).
%C A040000 Inverse binomial transform of Mersenne numbers A000225(n+1) = 2^(n+1) - 1. - _Paul Barry_, Feb 28 2003
%C A040000 A Chebyshev transform of 2^n: if A(x) is the g.f. of a sequence, map it to ((1-x^2)/(1+x^2))A(x/(1+x^2)). - _Paul Barry_, Oct 31 2004
%C A040000 An inverse Catalan transform of A068875 under the mapping g(x)->g(x(1-x)). A068875 can be retrieved using the mapping g(x)->g(xc(x)), where c(x) is the g.f. of A000108. A040000 and A068875 may be described as a Catalan pair. - _Paul Barry_, Nov 14 2004
%C A040000 Sequence of electron arrangement in the 1s 2s and 3s atomic subshells. Cf. A001105, A016825. - _Jeremy Gardiner_, Dec 19 2004
%C A040000 Binomial transform of A165326. - _Philippe Deléham_, Sep 16 2009
%C A040000 Let m=2. We observe that a(n) = Sum_{k=0..floor(n/2)} binomial(m,n-2*k). Then there is a link with A113311 and A115291: it is the same formula with respectively m=3 and m=4. We can generalize this result with the sequence whose g.f. is given by (1+z)^(m-1)/(1-z). - _Richard Choulet_, Dec 08 2009
%C A040000 With offset 1: number of permutations where |p(i) - p(i+1)| <= 1 for n=1,2,...,n-1. This is the identical permutation and (for n>1) its reversal.
%C A040000 Equals INVERT transform of bar(1, 1, -1, -1, ...).
%C A040000 Eventual period is (2). - _Zak Seidov_, Mar 05 2011
%C A040000 Also decimal expansion of 11/90. - _Vincenzo Librandi_, Sep 24 2011
%C A040000 a(n) = 3 - A054977(n); right edge of the triangle in A182579. - _Reinhard Zumkeller_, May 07 2012
%C A040000 With offset 1: minimum cardinality of the range of a periodic sequence with (least) period n. Of course the range's maximum cardinality for a purely periodic sequence with (least) period n is n. - _Rick L. Shepherd_, Dec 08 2014
%C A040000 With offset 1: n*a(1) + (n-1)*a(2) + ... + 2*a(n-1) + a(n) = n^2. - _Warren Breslow_, Dec 12 2014
%C A040000 With offset 1: decimal expansion of gamma(4) = 11/9 where gamma(n) = Cp(n)/Cv(n) is the n-th Poisson's constant. For the definition of Cp and Cv see A272002. - _Natan Arie Consigli_, Sep 11 2016
%C A040000 a(n) equals the number of binary sequences of length n where no two consecutive terms differ. Also equals the number of binary sequences of length n where no two consecutive terms are the same. - _David Nacin_, May 31 2017
%C A040000 a(n) is the period of the continued fractions for sqrt((n+2)/(n+1)) and sqrt((n+1)/(n+2)). - _A.H.M. Smeets_, Dec 05 2017
%C A040000 Also, number of self-avoiding walks and coordination sequence for the one-dimensional lattice Z. - _Sean A. Irvine_, Jul 27 2020
%C A040000 For n >= 2, a(n) is the size of the largest complete subgraph (clique number) and chromatic number of a tree with n vertices. - _Igor Blokhin_, Feb 25 2026
%D A040000 Edward J. Barbeau, Pell's Equation, New York: Springer-Verlag, 2003, p. 3, Exercise 1.2.
%D A040000 A. Beiser, Concepts of Modern Physics, 2nd Ed., McGraw-Hill, 1973.
%D A040000 John H. Conway and Richard K. Guy, The Book of Numbers, New York: Springer-Verlag, 1996. See p. 186.
%D A040000 Harold Davenport, The Higher Arithmetic, Cambridge University Press, 8th ed., 2008, pp. 84-85, 97.
%D A040000 Elena Deza and Michel Marie Deza, Figurate numbers, World Scientific Publishing (2012), page 24.
%D A040000 Jan Gullberg, Mathematics from the Birth of Numbers, W. W. Norton & Co., NY & London, 1997, §4.4 Powers and Roots, p. 144.
%D A040000 James J. Tattersall, Elementary Number Theory in Nine Chapters, Cambridge University Press, 1999, pages 276-278.
%H A040000 Harry J. Smith, <a href="/A040000/b040000.txt">Table of n, a(n) for n = 0..20000</a>
%H A040000 Paul Barry, <a href="https://cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.html">A Catalan Transform and Related Transformations on Integer Sequences</a>, Journal of Integer Sequences, Vol. 8 (2005), Article 05.4.5.
%H A040000 Bruce Fang, Pamela E. Harris, Brian M. Kamau, and David Wang, <a href="https://arxiv.org/abs/2402.02538">Vacillating parking functions</a>, arXiv:2402.02538 [math.CO], 2024.
%H A040000 Kshitij Education, <a href="https://web.archive.org/web/20171219234500/http://www.kshitij-iitjee.com/molar-specific-heat-of-an-ideal-gas">Molar specific heat</a>.
%H A040000 MathPath, <a href="https://web.archive.org/web/20150911210941/http://www.mathpath.org/Algor/squareroot/algor.square.root.contfrac.htm">Square-roots via Continued Fractions</a>.
%H A040000 Narad Rampersad and Max Wiebe, <a href="https://arxiv.org/abs/2309.04012">Sums of products of binomial coefficients mod 2 and 2-regular sequences</a>, arXiv:2309.04012 [math.NT], 2023.
%H A040000 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/PythagorassConstant.html">Pythagoras's Constant</a>.
%H A040000 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/SquareRoot.html">Square root</a>.
%H A040000 Wikipedia, <a href="https://en.wikipedia.org/wiki/Heat_capacity_ratio">Poisson's constant</a>.
%H A040000 G. Xiao, <a href="https://wims.univ-cotedazur.fr/~wims/en_tool~number~contfrac.en.html">Contfrac</a>.
%H A040000 <a href="/index/Con#confC">Index entries for continued fractions for constants</a>.
%H A040000 <a href="/index/Con#constant">Index entries for eventually constant sequences</a>.
%H A040000 <a href="/index/Di#divseq">Index to divisibility sequences</a>.
%H A040000 <a href="/index/Rec#order_01">Index entries for linear recurrences with constant coefficients</a>, signature (1).
%F A040000 G.f.: (1+x)/(1-x). - _Paul Barry_, Feb 28 2003
%F A040000 a(n) = 2 - 0^n; a(n) = Sum_{k=0..n} binomial(1, k). - _Paul Barry_, Oct 16 2004
%F A040000 For n >= 1, a(n) = n*Sum_{k=0..floor(n/2)} (-1)^k*binomial(n-k, k)*2^(n-2*k)/(n-k). - _Paul Barry_, Oct 31 2004
%F A040000 A040000(n) = Sum_{k=0..floor(n/2)} binomial(n-k, k)*(-1)^k*A068875(n-k). - _Paul Barry_, Nov 14 2004
%F A040000 From _Michael Somos_, Apr 16 2007: (Start)
%F A040000 Euler transform of length 2 sequence [2, -1].
%F A040000 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^4)) where f(u, v, w) = (u-v)*(u+v) - 2*v*(u-w).
%F A040000 E.g.f.: 2*exp(x) - 1.
%F A040000 a(n) = a(-n) for all n in Z (one possible extension to n<0). (End)
%F A040000 G.f.: (1-x^2)/(1-x)^2. - _Jaume Oliver Lafont_, Mar 26 2009
%F A040000 G.f.: exp(2*atanh(x)). - _Jaume Oliver Lafont_, Oct 20 2009
%F A040000 a(n) = Sum_{k=0..n} A108561(n,k)*(-1)^k. - _Philippe Deléham_, Nov 17 2013
%F A040000 a(n) = 1 + sign(n). - _Wesley Ivan Hurt_, Apr 16 2014
%F A040000 10 * 11/90 = 11/9 = (11/2 R)/(9/2 R) = Cp(4)/Cv(4) = A272005/A272004, with R = A081822 (or A070064). - _Natan Arie Consigli_, Sep 11 2016
%F A040000 a(n) = A001227(A000040(n+1)). - _Omar E. Pol_, Feb 28 2018
%e A040000 sqrt(2) = 1.41421356237309504... = 1 + 1/(2 + 1/(2 + 1/(2 + 1/(2 + ...)))). - _Harry J. Smith_, Apr 21 2009
%e A040000 G.f. = 1 + 2*x + 2*x^2 + 2*x^3 + 2*x^4 + 2*x^5 + 2*x^6 + 2*x^7 + 2*x^8 + ...
%e A040000 11/90 = 0.1222222222222222222... - _Natan Arie Consigli_, Sep 11 2016
%p A040000 Digits := 100: convert(evalf(sqrt(2)),confrac,90,'cvgts'):
%t A040000 ContinuedFraction[Sqrt[2],300] (* _Vladimir Joseph Stephan Orlovsky_, Mar 04 2011 *)
%t A040000 a[ n_] := 2 - Boole[n == 0]; (* _Michael Somos_, Dec 28 2014 *)
%t A040000 PadRight[{1},120,2] (* or *) RealDigits[11/90, 10, 120][[1]] (* _Harvey P. Dale_, Jul 12 2025 *)
%o A040000 (PARI) {a(n) = 2-!n}; /* _Michael Somos_, Apr 16 2007 */
%o A040000 (PARI) a(n)=1+sign(n)  \\ _Jaume Oliver Lafont_, Mar 26 2009
%o A040000 (PARI)  allocatemem(932245000); default(realprecision, 21000); x=contfrac(sqrt(2)); for (n=0, 20000, write("b040000.txt", n, " ", x[n+1]));  \\ _Harry J. Smith_, Apr 21 2009
%o A040000 (Haskell)
%o A040000 a040000 0 = 1; a040000 n = 2
%o A040000 a040000_list = 1 : repeat 2  -- _Reinhard Zumkeller_, May 07 2012
%Y A040000 Convolution square is A008574.
%Y A040000 See A003945 etc. for (1+x)/(1-k*x).
%Y A040000 From _Jaume Oliver Lafont_, Mar 26 2009: (Start)
%Y A040000 Sum_{0<=k<=n} a(k) = A005408(n).
%Y A040000 Prod_{0<=k<=n} a(k) = A000079(n). (End)
%Y A040000 Cf. A113311, A115291, A171418, A171440, A171441, A171442, A171443.
%Y A040000 Cf. A000674 (boustrophedon transform).
%Y A040000 Cf. A001333/A000129 (continued fraction convergents).
%Y A040000 Cf. A000122, A002193 (sqrt(2) decimal expansion), A006487 (Egyptian fraction).
%Y A040000 Cf. Other continued fractions for sqrt(a^2+1) = (a, 2a, 2a, 2a....): A040002 (contfrac(sqrt(5)) = (2,4,4,...)), A040006, A040012, A040020, A040030, A040042, A040056, A040072, A040090, A040110 (contfrac(sqrt(122)) = (11,22,22,...)), A040132, A040156, A040182, A040210, A040240, A040272, A040306, A040342, A040380, A040420 (contfrac(sqrt(442)) = (21,42,42,...)), A040462, A040506, A040552, A040600, A040650, A040702, A040756, A040812, A040870, A040930 (contfrac(sqrt(962)) = (31,62,62,...)).
%K A040000 nonn,cofr,easy,cons,changed
%O A040000 0,2
%A A040000 _N. J. A. Sloane_, Dec 11 1999
```


## Candidate 65: A323152 vs A323153 (score 118.0, agree 118, variant drop1, family size 2)
Terms: 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0

### A323152
```
%I A323152 #9 Mar 06 2023 11:19:56
%S A323152 1,1,1,0,1,1,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,1,1,0,1,0,0,0,
%T A323152 0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,
%U A323152 0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,1
%N A323152 a(n) = 1 if sigma(n) is divisible by all proper divisors of n, 0 otherwise.
%C A323152 Characteristic function of A166070.
%C A323152 Differs from A323153 at positions n = 1, 120, 672, 30240, 32760, ...
%H A323152 Antti Karttunen, <a href="/A323152/b323152.txt">Table of n, a(n) for n = 1..65537</a>
%H A323152 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%t A323152 Table[If[AllTrue[DivisorSigma[1,n]/Most[Divisors[n]],IntegerQ],1,0],{n,150}] (* _Harvey P. Dale_, Mar 06 2023 *)
%o A323152 (PARI) A323152(n) = { my(s=sigma(n)); fordiv(n,d,if((d<n)&&(s%d),return(0))); (1); };
%Y A323152 Cf. A166070, A323153.
%K A323152 nonn
%O A323152 1
%A A323152 _Antti Karttunen_, Jan 09 2019
```
### A323153
```
%I A323153 #9 Jan 09 2019 21:21:42
%S A323153 0,1,1,0,1,1,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,1,1,0,1,0,0,0,
%T A323153 0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,
%U A323153 0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0
%N A323153 a(n) = 1 if n is either a prime or a perfect number, 0 otherwise.
%C A323153 Characteristic function of A053813.
%C A323153 Differs from A323152 at positions n = 1, 120, 672, 30240, 32760, ...
%H A323153 Antti Karttunen, <a href="/A323153/b323153.txt">Table of n, a(n) for n = 1..65537</a>
%H A323153 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%o A323153 (PARI) A323153(n) = ((n>1)&&!(n%sumdiv(n,d,(d<n)*d)));
%Y A323153 Cf. A000040, A000396, A053813, A053814, A323152.
%K A323153 nonn
%O A323153 1
%A A323153 _Antti Karttunen_, Jan 09 2019
```


## Candidate 66: A061486 vs A264600 (score 116.1, agree 101, variant raw, family size 4)
Terms: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 5, 8, 11, 14, 17, 20, 23, 26, 29

### A061486
```
%I A061486 #19 Feb 16 2025 08:32:44
%S A061486 0,1,2,3,4,5,6,7,8,9,1,3,5,7,9,11,13,15,17,19,2,5,8,11,14,17,20,23,26,
%T A061486 29,3,7,11,15,19,23,27,31,35,39,4,9,14,19,24,29,34,39,44,49,5,11,17,
%U A061486 23,29,35,41,47,53,59,6,13,20,27,34,41,48,55,62,69,7,15,23,31,39,47,55,63,71,79,8,17,26,35,44,53,62,71,80,89,9,19,29,39,49,59,69,79,89,99,1,3
%N A061486 Let the number of digits in n be k; a(n) = sum of the products of the digits of n taken r at a time where r ranges from 1 to k.
%C A061486 Differs from A264600 first at n=101: a(101) = 3 != A264600(101) = 12. - _Alois P. Heinz_, Nov 20 2015
%H A061486 Alois P. Heinz, <a href="/A061486/b061486.txt">Table of n, a(n) for n = 0..20000</a>
%H A061486 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/SymmetricPolynomial.html">Symmetric polynomial</a>.
%H A061486 Wikipedia, <a href="https://en.wikipedia.org/wiki/Elementary_symmetric_polynomial">Elementary symmetric polynomial</a>.
%e A061486 a(34) = 3 + 4 + 3*4 = 19, a(124) = (1+2+4)+(1*2+2*4+1*4)+(1*2*4) = 29.
%p A061486 with(combinat):
%p A061486 a:= n-> (l-> add(mul(l[i], i=w), w=choose(
%p A061486          nops(l)))-1)(convert(n, base, 10)):
%p A061486 seq(a(n), n=0..101);  # _Alois P. Heinz_, Nov 20 2015
%o A061486 (PARI) sympol(X, n)=my(s=0); forvec(i=vector(n, j, [1, #X]), s+=prod(k=1, n, X[i[k]]), 2); s ;
%o A061486 a(n) = my(d=digits(n)); sum(k=1, #d, sympol(d, k)); \\ _Michel Marcus_, Apr 06 2021
%Y A061486 Cf. A264600, A264668.
%K A061486 nonn,base,look,easy
%O A061486 0,3
%A A061486 _Amarnath Murthy_, May 06 2001
%E A061486 More terms from _Erich Friedman_, Jun 03 2001
%E A061486 a(0)=0 prepended by _Alois P. Heinz_, Nov 20 2015
```
### A264600
```
%I A264600 #35 Nov 05 2023 09:04:08
%S A264600 0,1,2,3,4,5,6,7,8,9,1,3,5,7,9,11,13,15,17,19,2,5,8,11,14,17,20,23,26,
%T A264600 29,3,7,11,15,19,23,27,31,35,39,4,9,14,19,24,29,34,39,44,49,5,11,17,
%U A264600 23,29,35,41,47,53,59,6,13,20,27,34,41,48,55,62,69,7,15,23,31,39,47,55,63,71,79,8,17,26,35,44,53,62,71,80,89,9,19,29,39,49,59,69,79,89,99,1,12
%N A264600 Let S_n denote the list of decimal numbers 0 to n, written backwards (allowing leading zeros) and arranged in lexicographic order; a(n) = position where backwards-n appears, starting indexing at 0.
%H A264600 Alois P. Heinz, <a href="/A264600/b264600.txt">Table of n, a(n) for n = 0..20000</a> (first 10000 terms from Chai Wah Wu)
%F A264600 a(0) = 0, a(10n+m) = a(n) + m*(n+1) for m in {0,...,9}. - _Alois P. Heinz_, Nov 20 2015
%e A264600 S_0 = [0], so a(0)=0,
%e A264600 ...
%e A264600 S_9 = [0,1,2,3,4,5,6,7,8,9], so a(9) = 9,
%e A264600 S_10 = [0,01,1,2,3,4,5,6,7,8,9], so a(10) = 1,
%e A264600 S_11 = [0,01,1,11,2,3,4,5,6,7,8,9], so a(11) = 3,
%e A264600 ...
%e A264600 S_20 = [0,01,02,1,11,2,21,3,31,4,41,5,51,6,61,7,71,8,81,9,91], so a(20) = 2, and so on
%p A264600 a:= proc(n) option remember; `if`(n=0, 0,
%p A264600       irem(n, 10, 'r')*(r+1)+a(r))
%p A264600     end:
%p A264600 seq(a(n), n=0..101);  # _Alois P. Heinz_, Nov 20 2015
%t A264600 A264600[0]=0;A264600[n_]:=A264600[n]=Mod[n,10](Floor[n/10]+1)+A264600[Floor[n/10]];Array[A264600,100,0] (* _Paolo Xausa_, Nov 04 2023, after _Alois P. Heinz_ *)
%o A264600 (Python)
%o A264600 def A264600(n):
%o A264600     return sorted(str(i)[::-1] for i in range(n+1)).index(str(n)[::-1]) # _Chai Wah Wu_, Nov 20 2015
%Y A264600 Decimal analog of A264596.
%Y A264600 Has same beginning as A061486 but is ultimately different: see A264668.
%K A264600 nonn,base
%O A264600 0,3
%A A264600 _N. J. A. Sloane_, Nov 20 2015
%E A264600 More terms from _Alois P. Heinz_, Nov 20 2015
```


## Candidate 67: A132272 vs A179051 (score 113.8, agree 99, variant drop1, family size 5)
Terms: 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3

### A132272
```
%I A132272 #16 Jun 13 2025 10:50:49
%S A132272 1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,4,4,4,4,
%T A132272 4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,
%U A132272 7,7,8,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,10,10
%N A132272 a(n) = Product_{k>0} (1 + floor(n/10^k)).
%C A132272 If n is written in base-10 as n=d(m)d(m-1)d(m-2)...d(2)d(1)d(0) (where d(k) is the digit at position k) then a(n) is also the product (1+d(m)d(m-1)d(m-2)...d(2)d(1))*(1+d(m)d(m-1)d(m-2)...d(2))*...*(1+d(m)d(m-1)d(m-2))*(1+d(m)d(m-1))*(1+d(m)).
%C A132272 a(n) = A179051(n) for n < 100. [From _Reinhard Zumkeller_, Jun 27 2010]
%H A132272 R. J. Mathar, <a href="/A132272/b132272.txt">Table of n, a(n) for n = 0..500</a>
%F A132272 The following formulas are given for a general parameter p considering the product of terms 1+floor(n/p^k) for 0<k<=floor(log_p(n)), where p=10 for this sequence.
%F A132272 Recurrence: a(n)=(1+floor(n/p))*a(floor(n/p)); a(pn)=(1+n)*a(n); a(n*p^m)=product{0<=k<m, 1+n*p^k}*a(n).
%F A132272 a(k*p^m-j)=k^m*p^(m(m-1)/2), for 0<k<p, 0<j<p, m>=1. a(p^m)=p^(m(m-1)/2)*product{0<=k<m, 1+1/p^k}
%F A132272 a(n)=A132271(floor(n/p))=A132271(n)/(1+n).
%F A132272 Asymptotic behavior: a(n)=O(n^((log_p(n)-1)/p)); this follows from the inequalities below.
%F A132272 a(n)<=A067080(n)/(n+1)*product{0<=k<=floor(log_p(n)), 1+1/p^k}.
%F A132272 a(n)>=A067080(n)/((n+1)*product{0<k<=floor(log_p(n)), 1-1/p^k}).
%F A132272 a(n)<c*n^((1+log_p(n))/2)/(n+1)=c*2^A000217(log_p(n))/(n+1), where c=product{k>0, 1+1/p^k}=2.2244691382741012... (for p=10 see constant A132325).
%F A132272 a(n)>n^((1+log_p(n))/2)/(n+1)=p^A000217(log_p(n))/(n+1).
%F A132272 lim sup n*a(n)/A067080(n)=2*product{k>0, 1+1/p^k}=2.2244691382741012..., for n-->oo (for p=10 see constant A132325).
%F A132272 lim inf n*a(n)/A067080(n)=1/product{k>0, 1-1/p^k}=1/0.8900100999989990000001000..., for n-->oo (for p=10 s. constant A132038).
%F A132272 lim inf a(n)/n^((1+log_p(n))/2)=1, for n-->oo.
%F A132272 lim sup a(n)/n^((1+log_p(n))/2)=2*product{k>0, 1+1/p^k}=2.2244691382741012..., for n-->oo (for p=10 see constant A132325).
%F A132272 lim inf a(n+1)/a(n)=2*product{k>0, 1+1/p^k}=2.2244691382741012... for n-->oo (for p=10 see constant A132325).
%e A132272 a(121)=(1+floor(121/10^1))*(1+floor(121/10^2))=13*2=26; a(132)=28 since 132=132(base-10) and so
%e A132272 a(132)=(1+13)*(1+1)(base-10)=14*2=28.
%p A132272 A132272 := proc(n)
%p A132272     a := 1;
%p A132272     for k from 1 do
%p A132272         f := floor(n/10^k) ;
%p A132272         if f <=0 then
%p A132272             return a;
%p A132272         else
%p A132272             a := a*(1+f) ;
%p A132272         end if;
%p A132272     end do:
%p A132272 end proc:
%p A132272 seq(A132272(n),n=1..120) ; # _R. J. Mathar_, Jun 13 2025
%t A132272 Table[Product[1+Floor[n/10^k],{k,n}],{n,0,100}] (* _Harvey P. Dale_, Jul 20 2024 *)
%Y A132272 Cf. A132038, A132270(p=2), A132271, A132325, A132328(p=3), A132271.
%Y A132272 For the product of terms floor(n/p^k) see A098844, A067080, A132027-A132033, A132263, A132264.
%K A132272 nonn,base
%O A132272 0,11
%A A132272 _Hieronymus Fischer_, Aug 20 2007
```
### A179051
```
%I A179051 #18 Dec 12 2021 15:59:24
%S A179051 1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,4,4,4,4,
%T A179051 4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,
%U A179051 7,7,8,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,10,10
%N A179051 Number of partitions of n into powers of 10 (cf. A011557).
%C A179051 A179052 and A008592 give record values and where they occur.
%H A179051 Reinhard Zumkeller, <a href="/A179051/b179051.txt">Table of n, a(n) for n = 0..10000</a>
%H A179051 <a href="/index/Par#partN">Index entries for related partition-counting sequences</a>
%F A179051 a(n) = A133880(n) for n < 90; a(n) = A132272(n) for n < 100.
%F A179051 a(10^n) = A145513(n).
%F A179051 a(10*n) = A179052(n).
%F A179051 A179052(n) = a(A008592(n));
%F A179051 a(n) = p(n,1) where p(n,k) = if k<=n then p(10*[(n-k)/10],k)+p(n,10*k) else 0^n.
%F A179051 G.f.: Product_{k>=0} 1/(1 - x^(10^k)). - _Ilya Gutkovskiy_, Jul 26 2017
%e A179051 a(19) = #{10 + 9x1, 19x1} = 2;
%e A179051 a(20) = #{10 + 10, 10 + 10x1, 20x1} = 3;
%e A179051 a(21) = #{10 + 10 + 1, 10 + 11x1, 21x1} = 3.
%t A179051 terms = 10001;
%t A179051 CoefficientList[Product[1/(1 - x^(10^k)) + O[x]^terms,
%t A179051      {k, 0, Log[10, terms] // Ceiling}], x]
%t A179051 (* _Jean-François Alcover_, Dec 12 2021, after _Ilya Gutkovskiy_ *)
%o A179051 (Haskell)
%o A179051 a179051 = p 1 where
%o A179051    p _ 0 = 1
%o A179051    p k m = if m < k then 0 else p k (m - k) + p (k * 10) m
%o A179051 -- _Reinhard Zumkeller_, Feb 05 2012
%Y A179051 Number of partitions of n into powers of b: A018819 (b=2), A062051 (b=3).
%Y A179051 Cf. A206245, A000041, A179051.
%Y A179051 Cf. A133880, A132272.
%Y A179051 Cf. A008592, A179052.
%K A179051 nonn
%O A179051 0,11
%A A179051 _Reinhard Zumkeller_, Jun 27 2010
```


## Candidate 68: A305900 vs A374478 (score 108.1, agree 94, variant raw, family size 4)
Terms: 1, 2, 3, 4, 5, 6, 5, 7, 8, 9, 5, 10, 5, 11, 12, 13, 5, 14, 5, 15, 16, 17, 5, 18, 19, 20, 21, 22, 5, 23

### A305900
```
%I A305900 #12 Jul 29 2026 15:25:41
%S A305900 1,2,3,4,5,6,5,7,8,9,5,10,5,11,12,13,5,14,5,15,16,17,5,18,19,20,21,22,
%T A305900 5,23,5,24,25,26,27,28,5,29,30,31,5,32,5,33,34,35,5,36,37,38,39,40,5,
%U A305900 41,42,43,44,45,5,46,5,47,48,49,50,51,5,52,53,54,5,55,5,56,57,58,59,60,5,61,62,63,5,64,65,66,67,68,5,69,70,71,72,73,74,75,5,76
%N A305900 Filter sequence for a(primes > 3) = constant sequences.
%C A305900 For all i, j:
%C A305900   a(i) = a(j) => A305801(i) = A305801(j) => A305800(i) = A305800(j).
%C A305900   a(i) = a(j) => A007949(i) = A007949(j).
%C A305900   a(i) = a(j) => A305893(i) = A305893(j).
%H A305900 Antti Karttunen, <a href="/A305900/b305900.txt">Table of n, a(n) for n = 1..100000</a>
%F A305900 For n <= 5, a(n) = n, for >= 5, a(n) = 5 when n is a prime, and a(n) = 3+n-A000720(n) when n is a composite.
%t A305900 A305900[n_] := Which[n <= 6, n, PrimeQ[n], 5, True, 3 + n - PrimePi[n]];
%t A305900 Array[A305900, 100] (* _Paolo Xausa_, Jul 29 2026 *)
%o A305900 (PARI) A305900(n) = if(n<=5,n,if(isprime(n),5,3+n-primepi(n)));
%Y A305900 Cf. A305800, A305801, A305893.
%Y A305900 Cf. also A305901, A305902, A305903 (this filter applied to various permutations of N).
%K A305900 nonn
%O A305900 1,2
%A A305900 _Antti Karttunen_, Jun 14 2018
```
### A374478
```
%I A374478 #13 Aug 07 2024 15:11:43
%S A374478 1,2,3,4,5,6,5,7,8,9,5,10,5,11,12,13,5,14,5,15,16,17,5,18,19,20,21,22,
%T A374478 5,23,5,24,25,26,27,28,5,29,30,31,5,32,5,33,34,35,5,36,37,38,39,40,5,
%U A374478 41,42,43,44,45,5,46,5,47,48,49,50,51,5,52,53,54,5,55,5,56,57,58,59,60,5,61,62,63,5,64,65,66,67,68,5,69,70,71,72,73,39,74,5,75,76,77,5
%N A374478 Lexicographically earliest infinite sequence such that a(i) = a(j) => A348717(i) = A348717(j) and A364255(i) = A364255(j), for all i, j >= 1.
%C A374478 Restricted growth sequence transform of the ordered pair [A348717(n), A364255(n)].
%C A374478 For all i, j >= 1:
%C A374478   A305900(i) = A305900(j) => a(i) = a(j),
%C A374478   a(i) = a(j) => A305891(i) = A305891(j),
%C A374478   a(i) = a(j) => A374477(i) = A374477(j).
%H A374478 Antti Karttunen, <a href="/A374478/b374478.txt">Table of n, a(n) for n = 1..65537</a>
%H A374478 <a href="/index/Pri#prime_indices">Index entries for sequences computed from indices in prime factorization</a>
%o A374478 (PARI)
%o A374478 up_to = 65537;
%o A374478 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A374478 A348717(n) = if(1==n, 1, my(f = factor(n), k = primepi(f[1, 1])-1); for (i=1, #f~, f[i, 1] = prime(primepi(f[i, 1])-k)); factorback(f));
%o A374478 A163511(n) = if(!n, 1, my(p=2, t=1); while(n>1, if(!(n%2), (t*=p), p=nextprime(1+p)); n >>= 1); (t*p));
%o A374478 A364255(n) = gcd(n, A163511(n));
%o A374478 Aux374478(n) = [A348717(n), A364255(n)];
%o A374478 v374478 = rgs_transform(vector(up_to, n, Aux374478(n)));
%o A374478 A374478(n) = v374478[n];
%Y A374478 Cf. A163511, A348717, A364255.
%Y A374478 Cf. also A305891, A305897, A364297, A364949, A365392, A365423, A374477.
%Y A374478 Differs from A374040 first at n=77, where a(77) = 59, while A374040(77) = 50.
%Y A374478 Differs from A305900 first at n=95, where a(95) = 39, while A305900(95) = 74.
%K A374478 nonn
%O A374478 1,2
%A A374478 _Antti Karttunen_, Aug 07 2024
```


## Candidate 69: A323077 vs A334201 (score 105.0, agree 105, variant raw, family size 2)
Terms: 0, 0, 0, 1, 0, 1, 0, 2, 2, 1, 0, 2, 0, 1, 2, 3, 0, 3, 0, 2, 2, 1, 0, 3, 3, 1, 4, 2, 0, 3

### A323077
```
%I A323077 #30 Feb 28 2024 10:50:09
%S A323077 0,0,0,1,0,1,0,2,2,1,0,2,0,1,2,3,0,3,0,2,2,1,0,3,3,1,4,2,0,3,0,4,2,1,
%T A323077 3,4,0,1,2,3,0,3,0,2,4,1,0,4,4,4,2,2,0,5,3,3,2,1,0,4,0,1,4,5,3,3,0,2,
%U A323077 2,4,0,5,0,1,5,2,4,3,0,4,6,1,0,4,3,1,2,3,0,5,4,2,2,1,3,5,0,5,4,5,0,3,0,3,5
%N A323077 Number of iterations of map x -> (x - (largest divisor d < x)) needed to reach 1 or a prime, when starting at x = n.
%C A323077 When iteration is started from n, the first noncomposite reached is A006530(n), from which follows the new formula a(n) = A064097(A052126(n)) = A064097(n/A006530(n)), as A064097 is completely additive sequence. - _Antti Karttunen_, May 15 2020
%H A323077 Antti Karttunen, <a href="/A323077/b323077.txt">Table of n, a(n) for n = 1..12005</a>
%H A323077 Antti Karttunen, <a href="/A323077/a323077.txt">Data supplement: n, a(n) computed for n = 1..65537</a>
%F A323077 If A001222(n) <= 1 [when n is 1 or a prime], a(n) = 0, otherwise a(n) = 1 + a(A060681(n)).
%F A323077 a(n) <= A064097(n).
%F A323077 a(n) = A064097(n) - A334202(n) = A064097(A052126(n)). - _Antti Karttunen_, May 13 2020
%F A323077 a(A334198(n)) = n for all n >= 0. - _Antti Karttunen_, May 19 2020
%t A323077 Nest[Append[#1, If[PrimeOmega[#2] <= 1, 0, 1 + #1[[Max@ Differences@ Divisors[#2] ]] ]] & @@ {#, Length@ # + 1} &, {}, 105] (* _Michael De Vlieger_, May 26 2020 *)
%o A323077 (PARI)
%o A323077 A060681(n) = (n-if(1==n,n,n/vecmin(factor(n)[,1])));
%o A323077 A323077(n) = if(1>=bigomega(n),0,1+A323077(A060681(n)));
%Y A323077 Cf. A006530, A032742, A052126, A060681, A064097, A323076, A334202, A334203.
%Y A323077 Cf. A334198 (positions of the records, also the first occurrence of each n).
%Y A323077 Differs from A334201 for the first time at n=169, where a(169) = 5, while A334201(169) = 6.
%K A323077 nonn
%O A323077 1,8
%A A323077 _Antti Karttunen_, Jan 04 2019
```
### A334201
```
%I A334201 #23 Jan 01 2021 11:41:12
%S A334201 0,0,0,1,0,1,0,2,2,1,0,2,0,1,2,3,0,3,0,2,2,1,0,3,3,1,4,2,0,3,0,4,2,1,
%T A334201 3,4,0,1,2,3,0,3,0,2,4,1,0,4,4,4,2,2,0,5,3,3,2,1,0,4,0,1,4,5,3,3,0,2,
%U A334201 2,4,0,5,0,1,5,2,4,3,0,4,6,1,0,4,3,1,2,3,0,5,4,2,2,1,3,5,0,5,4,5,0,3,0,3,5
%N A334201 a(n) = A056239(n) - A061395(n).
%C A334201 a(n) is the sum of all other parts of the partition having Heinz number n except one instance of the largest part.
%H A334201 Antti Karttunen, <a href="/A334201/b334201.txt">Table of n, a(n) for n = 1..65537</a>
%H A334201 <a href="/index/Pri#prime_indices">Index entries for sequences computed from indices in prime factorization</a>
%F A334201 a(n) = A056239(n) - A061395(n) = A056239(A052126(n)).
%F A334201 a(n) = A318995(A122111(n)).
%F A334201 a(n) = a(A064989(n)) + A001222(n) - 1.
%F A334201 a(n) = A339895(n) + A339896(n). - _Antti Karttunen_, Dec 31 2020
%t A334201 Array[Total[# /. {p_, c_} /; p > 0 :> PrimePi[p] c] - PrimePi@ #[[-1, 1]] &@ FactorInteger[#] &, 105] (* _Michael De Vlieger_, May 14 2020 *)
%o A334201 (PARI)
%o A334201 A064989(n) = {my(f); f = factor(n); if((n>1 && f[1,1]==2), f[1,2] = 0); for (i=1, #f~, f[i,1] = precprime(f[i,1]-1)); factorback(f)};
%o A334201 A334201(n) = if(1==n,0,(bigomega(n)-1)+A334201(A064989(n)));
%Y A334201 Cf. A001222, A052126, A056239, A061395, A122111, A318995.
%Y A334201 Sum of A339895 and A339896.
%Y A334201 Differs from A323077 for the first time at n=169, where a(169) = 6, while A323077(169) = 5.
%Y A334201 Cf. also A334107.
%K A334201 nonn
%O A334201 1,8
%A A334201 _Antti Karttunen_, May 11 2020
```


## Candidate 70: A052382 vs A209931 (score 104.6, agree 91, variant raw, family size 43)
Terms: 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33

### A052382
```
%I A052382 #168 Jun 28 2025 00:57:48
%S A052382 1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,27,28,
%T A052382 29,31,32,33,34,35,36,37,38,39,41,42,43,44,45,46,47,48,49,51,52,53,54,
%U A052382 55,56,57,58,59,61,62,63,64,65,66,67,68,69,71,72,73,74,75,76,77,78,79,81,82,83,84,85,86,87,88,89,91,92,93,94,95,96,97,98,99,111,112,113
%N A052382 Numbers without 0 in the decimal expansion, colloquial 'zeroless numbers'.
%C A052382 The entries 1 to 79 match the corresponding subsequence of A043095, but then 81, 91-98, 100, 102, etc. are only in one of the two sequences. - _R. J. Mathar_, Oct 13 2008
%C A052382 Complement of A011540; A168046(a(n)) = 1; A054054(a(n)) > 0; A007602, A038186, A038618, A052041, A052043, and A052045 are subsequences. - _Reinhard Zumkeller_, Apr 25 2012, Apr 07 2011, Dec 01 2009
%C A052382 a(n) = n written in base 9 where zeros are not allowed but nines are. The nine distinct digits used are 1, 2, 3, ..., 9 instead of 0, 1, 2, ..., 8. To obtain this sequence from the "canonical" base 9 sequence with zeros allowed, just replace any 0 with a 9 and then subtract one from the group of digits situated on the left. For example, 9^3 = 729 (10) (in base 10) = 1000 (9) (in base 9) = 889 (9-{0}) (in base 9 without zeros) because 100 (9) = [9-1]9 = 89 (9-{0}) and thus 1000 (9) = [89-1]9 = 889 (9-{0}). - _Robin Garcia_, Jan 15 2014
%C A052382 From _Hieronymus Fischer_, May 28 2014: (Start)
%C A052382 Inversion: Given a term m, the index n such that a(n) = m can be calculated by A052382_inverse(m) = m - sum_{1<=j<=k} floor(m/10^j)*9^(j-1), where k := floor(log_10(m)) [see Prog section for an implementation in Smalltalk].
%C A052382 Example 1: A052382_inverse(137) = 137 - (floor(137/10) + floor(137/100)*9) = 137 - (13*1 + 1*9) = 137 - 22 = 115.
%C A052382 Example 2: A052382_inverse(4321) = 4321 - (floor(4321/10) + floor(4321/100)*9 + floor(4321/1000)*81) = 4321 - (432*1 + 43*9 + 4*81) = 4321 - (432 + 387 + 324) = 3178. (End)
%C A052382 The sum of the reciprocals of these numbers from a(1)=1 to infinity, called the Kempner series, is convergent towards a limit: 23.103447... whose decimal expansion is in A082839. - _Bernard Schott_, Feb 23 2019
%C A052382 Integer n > 0 is encoded using bijective base-9 numeration, see Wikipedia link below. - _Alois P. Heinz_, Feb 16 2020
%D A052382 Paul Halmos, "Problems for Mathematicians, Young and Old", Dolciani Mathematical Expositions, 1991, p. 258.
%H A052382 Reinhard Zumkeller, <a href="/A052382/b052382.txt">Table of n, a(n) for n = 1..10000</a>
%H A052382 K. Mahler, <a href="http://carmaweb.newcastle.edu.au/mahler/docs/115.pdf">On the generating function of the integers with a missing digit</a>, J. Indian Math. Soc. 15A (1951), 34-40.
%H A052382 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/KempnerSeries.html">Kempner Series</a>.
%H A052382 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/Zerofree.html">Zerofree</a>
%H A052382 Wikipedia, <a href="https://en.wikipedia.org/wiki/Bijective_numeration">Bijective numeration</a>
%H A052382 <a href="/index/Ar#10-automatic">Index entries for 10-automatic sequences</a>.
%F A052382 a(n+1) = f(a(n)) with f(x) = 1 + if x mod 10 < 9 then x else 10*f([x/10]). - _Reinhard Zumkeller_, Nov 15 2009
%F A052382 From _Hieronymus Fischer_, Apr 30, May 30, Jun 08 2012, Feb 17 2019: (Start)
%F A052382 a(n) = Sum_{j=0..m-1} (1 + b(j) mod 9)*10^j, where m = floor(log_9(8*n + 1)), b(j) = floor((8*n + 1 - 9^m)/(8*9^j)).
%F A052382 Also: a(n) = Sum_{j=0..m-1} (1 + A010878(b(j)))*10^j.
%F A052382 a(9*n + k) = 10*a(n) + k, k=1..9.
%F A052382 Special values:
%F A052382 a(k*(9^n - 1)/8) = k*(10^n - 1)/9, k=1..9.
%F A052382 a((17*9^n - 9)/8) = 2*10^n - 1.
%F A052382 a((9^n - 1)/8 - 1) = 10^(n-1) - 1, n > 1.
%F A052382 Inequalities:
%F A052382 a(n) <= (1/9)*((8*n+1)^(1/log_10(9)) - 1), equality holds for n=(9^k-1)/8, k>0.
%F A052382 a(n) > (1/10)*((8*n+1)^(1/log_10(9)) - 1), n > 0.
%F A052382 Lower and upper limits:
%F A052382 lim inf a(n)/10^log_9(8*n) = 1/10, for n -> infinity.
%F A052382 lim inf a(n)/n^(1/log_10(9)) = 8^(1/log_10(9))/10, for n -> infinity.
%F A052382 lim sup a(n)/10^log_9(8*n) = 1/9, for n -> infinity.
%F A052382 lim sup a(n)/n^(1/log_10(9)) = 8^(1/log_10(9))/9, for n -> infinity.
%F A052382 G.f.: g(x) = (x^(1/8)*(1-x))^(-1) Sum_{j>=0} 10^j*z(j)^(9/8)*(1 - 10z(j)^9 + 9z(j)^10)/((1-z(j))(1-z(j)^9)), where z(j) = x^9^j.
%F A052382 Also: g(x) = (1/(1-x)) Sum_{j>=0} (1 - 10(x^9^j)^9 + 9(x^9^j)^10)*x^9^j*f_j(x)/(1-x^9^j), where f_j(x) = 10^j*x^((9^j-1)/8)/(1-(x^9^j)^9). Here, the f_j obey the recurrence f_0(x) = 1/(1-x^9), f_(j+1)(x) = 10x*f_j(x^9).
%F A052382 Also: g(x) = (1/(1-x))*((Sum{k=0..8} h_(9,k)(x)) - 9*h_(9,9)(x)), where h_(9,k)(x) = Sum_{j>=0} 10^j*x^((9^(j+1)-1)/8)*x^(k*9^j)/(1-x^9^(j+1)).
%F A052382 Generic formulas for analogous sequences with numbers expressed in base p and only using the digits 1, 2, 3, ... d, where 1 < d < p:
%F A052382 a(n) = Sum_{j=0..m-1} (1 + b(j) mod d)*p^j, where m = floor(log_d((d-1)*n+1)), b(j) = floor(((d-1)*n+1-d^m)/((d-1)*d^j)).
%F A052382 Special values:
%F A052382 a(k*(d^n-1)/(d-1)) = k*(10^n-1)/9, k=1..d.
%F A052382 a(d*((2d-1)*d^(n-1)-1)/(d-1)) = ((d+9)*10^n-d)/9 = 10^n + d*(10^n-1)/9.
%F A052382 a((d^n-1)/(d-1)-1) = d*(10^(n-1)-1)/9, n > 1.
%F A052382 Inequalities:
%F A052382 a(n) <= (10^log_d((d-1)*n+1)-1)/9, equality holds for n = (d^k-1)/(d-1), k > 0.
%F A052382 a(n) > (d/10)*(10^log_d((d-1)*n+1)-1)/9, n > 0.
%F A052382 Lower and upper limits:
%F A052382 lim inf a(n)/10^log_d((d-1)*n) = d/90, for n -> infinity.
%F A052382 lim sup a(n)/10^log_d((d-1)*n) = 1/9, for n -> infinity.
%F A052382 G.f.: g(x) = (1/(1-x)) Sum_{j>=0} (1 - (d+1)(x^d^j)^d + d(x^d^j)^(d+1))*x^d^j*f_j(x)/(1-x^d^j), where f_j(x) = p^j*x^((d^j-1)/(d-1))/(1-(x^d^j)^d). Here, the f_j obey the recursion f_0(x) = 1/(1-x^d), f_(j+1)(x) = px*f_j(x^d).
%F A052382 (End)
%F A052382 A052382 = { n | A054054(n) > 0 }. - _M. F. Hasler_, Jan 23 2013
%F A052382 From _Hieronymus Fischer_, Feb 20 2019: (Start)
%F A052382 Sum_{n>=1} (-1)^(n+1)/a(n) = 0.696899720...
%F A052382 Sum_{n>=1} 1/a(n)^2 = 1.6269683705819...
%F A052382 Sum_{n>=1} 1/a(n) = 23.1034479... = A082839. This so-called Kempner series converges very slowly. For the calculation of the sum, it is helpful to use the following fraction of partial sums, which converges rapidly:
%F A052382 lim_{n->infinity} (Sum_{k=p(n)..p(n+1)-1} 1/a(k)) / (Sum_{k=p(n-1)..p(n)-1} 1/a(k)) = 9/10, where p(n) = (9^n-1)/8, n > 1.
%F A052382 (End)
%e A052382 For k >= 0, a(10^k) = (1, 11, 121, 1331, 14641, 162151, 1783661, 19731371, ...) = A325203(k). - _Hieronymus Fischer_, May 30 2012 and Jun 06 2012; edited by _M. F. Hasler_, Jan 13 2020
%p A052382 a:= proc(n) local d, l, m; m:= n; l:= NULL;
%p A052382       while m>0 do d:= irem(m, 9, 'm');
%p A052382         if d=0 then d:=9; m:= m-1 fi;
%p A052382         l:= d, l
%p A052382       od; parse(cat(l))
%p A052382     end:
%p A052382 seq(a(n), n=1..100);  # _Alois P. Heinz_, Jan 11 2015
%p A052382 is_zeroless := n -> not is(0 in convert(n, base, 10)):
%p A052382 select(is_zeroless, [seq(1..113)]);  # _Peter Luschny_, Jun 20 2025
%t A052382 A052382 = Select[Range[100], DigitCount[#, 10, 0] == 0 &] (* _Alonso del Arte_, Mar 10 2011 *)
%o A052382 (Haskell)
%o A052382 a052382 n = a052382_list !! (n-1)
%o A052382 a052382_list = iterate f 1 where
%o A052382 f x = 1 + if r < 9 then x else 10 * f x' where (x', r) = divMod x 10
%o A052382 -- _Reinhard Zumkeller_, Mar 08 2015, Apr 07 2011
%o A052382 (Magma) [ n: n in [1..114] | not 0 in Intseq(n) ]; // _Bruno Berselli_, May 28 2011
%o A052382 (sh) seq 0 1000 | grep -v 0; # _Joerg Arndt_, May 29 2011
%o A052382 (PARI) select( {is_A052382(n)=n&&vecmin(digits(n))}, [0..111]) \\ actually: is_A052382 = (bool) A054054. - _M. F. Hasler_, Jan 23 2013, edited Jan 13 2020
%o A052382 (PARI) a(n) = for (w=0, oo, if (n >= 9^w, n -= 9^w, return ((10^w-1)/9 + fromdigits(digits(n, 9))))) \\ _Rémy Sigrist_, Jul 26 2017
%o A052382 (PARI)
%o A052382 apply( {A052382(n,L=logint(n,9))=fromdigits(digits(n-9^L>>3,9))+10^L\9}, [1..100])
%o A052382 next_A052382(n, d=digits(n+=1))={for(i=1, #d, d[i]|| return(n-n%(d=10^(#d-i+1))+d\9)); n} \\ least a(k) > n. Used in A038618.
%o A052382 ( {A052382_vec(n,M=1)=M--;vector(n, i, M=next_A052382(M))} )(99) \\ n terms >= M
%o A052382 \\ See OEIS Wiki page (cf. LINKS) for more programs. - _M. F. Hasler_, Jan 11 2020
%o A052382 (Smalltalk)
%o A052382 A052382
%o A052382 "Answers the n-th term of A052382, where n is the receiver."
%o A052382 ^self zerofree: 10
%o A052382 A052382_inverse
%o A052382 "Answers that index n which satisfy A052382(n) = m, where m is the receiver.”
%o A052382 ^self zerofree_inverse: 10
%o A052382 zerofree: base
%o A052382 "Answers the n-th zerofree number in base base, where n is the receiver. Valid for base > 2.
%o A052382 Usage: n zerofree: b [b = 10 for this sequence]
%o A052382 Answer: a(n)"
%o A052382 | n m s c bi ci d |
%o A052382 n := self.
%o A052382 c := base - 1.
%o A052382 m := (base - 2) * n + 1 integerFloorLog: c.
%o A052382 d := n - (((c raisedToInteger: m) - 1)//(base - 2)).
%o A052382 bi := 1.
%o A052382 ci := 1.
%o A052382 s := 0.
%o A052382 1 to: m
%o A052382 do:
%o A052382 [:i |
%o A052382 s := (d // ci \\ c + 1) * bi + s.
%o A052382 bi := base * bi.
%o A052382 ci := c * ci].
%o A052382 ^s
%o A052382 zerofree_inverse: base
%o A052382 "Answers the index n such that the n-th zerofree number in base base is = m, where m is the receiver. Valid for base > 2.
%o A052382 Usage: m zerofree_inverse: b [b = 10 for this sequence]
%o A052382 Answer: n"
%o A052382 | m p q s |
%o A052382 m := self.
%o A052382 s := 0.
%o A052382 p := base.
%o A052382 q := 1.
%o A052382 [p < m] whileTrue:
%o A052382 [s := m // p * q + s.
%o A052382 p := base * p.
%o A052382 q := (base - 1) * q].
%o A052382 ^m - s
%o A052382 "by _Hieronymus Fischer_, May 28 2014"
%o A052382 (Python)
%o A052382 A052382 = [n for n in range(1,10**5) if not str(n).count('0')]
%o A052382 # _Chai Wah Wu_, Aug 26 2014
%o A052382 (Python)
%o A052382 from sympy import integer_log
%o A052382 def A052382(n):
%o A052382     m = integer_log(k:=(n<<3)+1,9)[0]
%o A052382     return sum((1+(k-9**m)//(9**j<<3)%9)*10**j for j in range(m)) # _Chai Wah Wu_, Jun 27 2025
%Y A052382 Cf. A004719, A052040, different from A067251.
%Y A052382 Cf. A055640, A046034, A007931, A007932, A084544, A084545.
%Y A052382 Column k=9 of A214676.
%Y A052382 Cf. A011540 (complement), A043489, A054054, A168046.
%Y A052382 Cf. A052383 (without 1), A052404 (without 2), A052405 (without 3), A052406 (without 4), A052413 (without 5), A052414 (without 6), A052419 (without 7), A052421 (without 8), A007095 (without 9).
%Y A052382 Zeroless numbers in some other bases <= 10: A000042 (base 2), A032924 (base 3), A023705 (base 4), A248910 (base 6), A255805 (base 8), A255808 (base 9).
%Y A052382 Cf. A082839 (sum of reciprocals).
%Y A052382 Cf. A038618 (subset of primes)
%Y A052382 Subsequences: A007602, A038186, A052041, A052043, A052045, A059405, A066484, A099542.
%K A052382 base,easy,nonn
%O A052382 1,2
%A A052382 _Henry Bottomley_, Mar 13 2000
%E A052382 Typos in formula section corrected by _Hieronymus Fischer_, May 30 2012
%E A052382 Name clarified by _Peter Luschny_, Jun 20 2025
```
### A209931
```
%I A209931 #21 Jul 03 2025 02:37:24
%S A209931 1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,27,28,
%T A209931 29,31,32,33,34,35,36,37,38,39,41,42,43,44,45,46,47,48,49,51,52,53,54,
%U A209931 55,56,57,58,59,61,62,63,64,65,66,67,68,69,71,72,73,74,75,76,77,78,79,81,82,83,84,85,86,87,88,89,91,92,93,94,95,96,97,98,99,111
%N A209931 Numbers k such that smallest digit of all divisors of k is 1.
%C A209931 Also numbers k such that smallest digit of concatenation of all divisors of k (A037278 or A176558) is 1.
%C A209931 Sequence is not the same as A052382, first deviation is at a(173): A052382(173) = 212, a(173) = 213. [Corrected by _Michael S. Branicky_, Jul 01 2025.]
%C A209931 Sequence is not the same as A067251, first deviation is at a(91): A067251 (91) = 101, a(91) = 111.
%C A209931 Complement of A209932.
%H A209931 Michael S. Branicky, <a href="/A209931/b209931.txt">Table of n, a(n) for n = 1..10000</a>
%e A209931 Number 24 is in sequence because smallest digit of all divisors of 24 (1, 2, 4, 8, 3, 6, 12, 24) is 1.
%p A209931 isA209931 := proc(n)
%p A209931     digsdiv := {} ;
%p A209931     for d in numtheory[divisors](n) do
%p A209931         dgs := convert(convert(d,base,10),set) ;
%p A209931         digsdiv := digsdiv union dgs ;
%p A209931     end do:
%p A209931     if 0 in digsdiv then
%p A209931         false;
%p A209931     else
%p A209931         true ;
%p A209931     end if;
%p A209931 end proc:
%p A209931 A209931 := proc(n)
%p A209931     option remember;
%p A209931     if n =1 then
%p A209931         1;
%p A209931     else
%p A209931         for a from procname(n-1)+1 do
%p A209931             if isA209931(a) then
%p A209931                 return a;
%p A209931             end if;
%p A209931         end do;
%p A209931     end if;
%p A209931 end proc:
%p A209931 seq(A209931(n),n=1..120) ;# _R. J. Mathar_, Dec 28 2023
%t A209931 Select[Range[100], Min[IntegerDigits[Divisors[#]]] == 1 &] (* _Paolo Xausa_, Jul 03 2025 *)
%o A209931 (Python)
%o A209931 from sympy import divisors
%o A209931 def ok(n): return all('0' not in str(d) for d in divisors(n, generator=True))
%o A209931 print([k for k in range(1, 112) if ok(k)]) # _Michael S. Branicky_, Jul 01 2025
%Y A209931 Cf. A052382, A067251, A209929 (smallest digit of all divisors of n).
%K A209931 nonn,base
%O A209931 1,2
%A A209931 _Jaroslav Krizek_, Mar 20 2012
```


## Candidate 71: A358678 vs A359150 (score 103.0, agree 103, variant drop1, family size 2)
Terms: 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0

### A358678
```
%I A358678 #7 Dec 17 2022 22:53:31
%S A358678 0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
%T A358678 0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,
%U A358678 0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0
%N A358678 a(n) = 1 if n is odd and sigma(n) == 2 mod 4, otherwise 0.
%H A358678 Antti Karttunen, <a href="/A358678/b358678.txt">Table of n, a(n) for n = 1..100000</a>
%H A358678 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A358678 a(n) = A000035(n) * A353812(n).
%F A358678 a(n) <= A359150(n).
%o A358678 (PARI) A358678(n) = ((n%2)&&(2==(sigma(n)%4)));
%Y A358678 Characteristic function of A191218.
%Y A358678 Cf. A000035, A000203, A353812.
%Y A358678 Differs from A359150 for the first time at n=105, where a(105) = 0, while A359150(105) = 1.
%K A358678 nonn
%O A358678 1
%A A358678 _Antti Karttunen_, Dec 17 2022
```
### A359150
```
%I A359150 #11 Dec 17 2022 22:53:35
%S A359150 0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
%T A359150 0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,
%U A359150 0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0
%N A359150 a(n) = 1 if n is a number of the form 4u+1 with an odd number of prime factors (counted with multiplicity), otherwise 0.
%H A359150 Antti Karttunen, <a href="/A359150/b359150.txt">Table of n, a(n) for n = 1..100000</a>
%H A359150 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A359150 a(n) = A066829(n) * A121262(n-1).
%F A359150 a(n) = A353558(n) - A359152(n).
%F A359150 a(n) = A121262(n-1) - A359160(n).
%F A359150 a(n) >= A358678(n).
%o A359150 (PARI) A359150(n) = ((bigomega(n)%2)&&(1==(n%4)));
%Y A359150 Characteristic function of A359151.
%Y A359150 Cf. A066829, A121262, A353558, A359152, A359160.
%Y A359150 Differs from A358678 for the first time at n=105, where a(105) = 1, while A358678(105) = 0.
%K A359150 nonn
%O A359150 1
%A A359150 _Antti Karttunen_, Dec 17 2022
```


## Candidate 72: A256608 vs A279186 (score 98.9, agree 86, variant raw, family size 3)
Terms: 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4, 10, 1, 4, 2, 6, 2, 3, 1

### A256608
```
%I A256608 #27 Nov 05 2025 15:22:29
%S A256608 1,1,1,1,1,1,2,1,2,1,4,1,2,2,1,1,1,2,6,1,2,4,10,1,4,2,6,2,3,1,4,1,4,1,
%T A256608 2,2,6,6,2,1,4,2,6,4,2,10,11,1,6,4,1,2,12,6,4,2,6,3,28,1,4,4,2,1,2,4,
%U A256608 10,1,10,2,12,2,6,6,4,6,4,2,12,1,18,4,20,2,1,6
%N A256608 Longest eventual period of a^(2^k) mod n for all a.
%C A256608 a(n) is a divisor of phi(phi(n)) (A010554).
%H A256608 Ivan Neretin, <a href="/A256608/b256608.txt">Table of n, a(n) for n = 1..10000</a>
%H A256608 Haifeng Xu, <a href="https://arxiv.org/abs/1601.06509">The largest cycles consist by the quadratic residues and Fermat primes</a>, arXiv:1601.06509 [math.NT], 2016.
%F A256608 a(n) = A007733(A002322(n)).
%F A256608 a(prime(n)) = A037178(n). - _Michel Marcus_, Jan 27 2016
%e A256608 In other words, eventual period of {0..n-1} under the map x -> x^2 mod n.
%e A256608 For example, with n=10 the said map acts as follows. Read down the columns: the column headed 2 for example means that (repeatedly squaring mod 10), 2 goes to 4 goes to 16 = 6 (mod 10) goes to 36 = 6 mod 10 --- and has reached a fixed point.
%e A256608 0 1 2 3 4 5 6 7 8 9
%e A256608 0 1 4 9 6 5 6 9 4 1
%e A256608 0 1 6 1 6 5 6 1 6 1
%e A256608 0 1 6 1 6 5 6 1 6 1
%e A256608 and thus every number reaches a fixed point. This means the eventual common period is 1, hence a(10)=1.
%t A256608 a[n_] := With[{lambda = CarmichaelLambda[n]}, MultiplicativeOrder[2, lambda / (2^IntegerExponent[lambda, 2])]]; Table[a[n], {n, 1, 100}] (* _Jean-François Alcover_, Jan 28 2016 *)
%o A256608 (PARI) rpsi(n) = lcm(znstar(n)[2]); \\ A002322
%o A256608 pb(n) = znorder(Mod(2, n/2^valuation(n, 2))); \\ A007733
%o A256608 a(n) = pb(rpsi(n)); \\ _Michel Marcus_, Jan 28 2016
%Y A256608 Cf. A001146, A002322, A002326, A007733, A010554, A037178.
%Y A256608 First differs from A256607 at n=43.
%Y A256608 LCM of entries in row n of A279185.
%K A256608 nonn
%O A256608 1,7
%A A256608 _Ivan Neretin_, Apr 04 2015
%E A256608 Name changed by _Jianing Song_, Feb 02 2025
```
### A279186
```
%I A279186 #32 Oct 08 2026 09:22:14
%S A279186 1,1,1,1,1,1,2,1,2,1,4,1,2,2,1,1,1,2,6,1,2,4,10,1,4,2,6,2,3,1,4,1,4,1,
%T A279186 2,2,6,6,2,1,4,2,6,4,2,10,11,1,6,4,1,2,12,6,4,2,6,3,28,1,4,4,2,1,2,4,
%U A279186 10,1,10,2,12,2,6,6,4,6,4,2,12,1,18,4,20,2,1,6,3,4
%N A279186 Maximal entry in the n-th row of A279185.
%C A279186 See A256608 for LCM of entries in row n.
%C A279186 From _Robert Israel_, Dec 15 2016: (Start)
%C A279186 If m and k are coprime then a(m*k) = lcm(a(m), a(k)).
%C A279186 If n is in A061345 and r = A053575(n) is in A167791, then a(n) = A000010(r). (End)
%H A279186 R. J. Mathar, <a href="/A279186/b279186.txt">Table of n, a(n) for n = 1..1000</a>
%F A279186 a(n) = A007733(A002322(n)). - _Max Alekseyev_, Feb 02 2024
%p A279186 A279186 := proc(n)
%p A279186     local a,k ;
%p A279186     a := 1 ;
%p A279186     for k from 0 to n-1 do
%p A279186         a := max(a,A279185(k,n)) ;
%p A279186     end do:
%p A279186     a ;
%p A279186 end proc : # _R. J. Mathar_, Dec 15 2016
%t A279186 T[n_, k_] := Module[{g, y, r}, If[k == 0, Return[1]]; y = n; g = GCD[k, y]; While[g > 1, y = y/g; g = GCD[k, y]]; If[y == 1, Return[1]]; r = MultiplicativeOrder[k, y]; r = r/2^IntegerExponent[r, 2]; If[r == 1, Return[1]]; MultiplicativeOrder[2, r]];
%t A279186 a[n_] := Table[T[n, k], {k, 0, n - 1}] // Max;
%t A279186 Array[a, 90] (* _Jean-François Alcover_, Nov 27 2017, after _Robert Israel_ *)
%o A279186 (PARI) { A279186(n) = my(r=lcm(znstar(n)[2])); znorder(Mod(2,r>>valuation(r,2))); } \\ _Max Alekseyev_, Feb 02 2024
%Y A279186 Cf. A000010, A053575, A063145, A167791, A279185.
%Y A279186 Start is same as A256607 and A256608. However, all three are different.
%K A279186 nonn
%O A279186 1,7
%A A279186 _N. J. A. Sloane_, Dec 14 2016
```


## Candidate 73: A327517 vs A376504 (score 98.9, agree 86, variant drop1, family size 3)
Terms: 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 4

### A327517
```
%I A327517 #4 Sep 20 2019 08:58:10
%S A327517 1,0,0,0,0,1,0,0,0,1,0,1,0,1,1,0,0,1,0,1,1,1,0,1,0,1,0,1,0,4,0,0,1,1,
%T A327517 1,1,0,1,1,1,0,4,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,4,0,1,1,0,1,4,0,1,
%U A327517 1,4,0,1,0,1,1,1,1,4,0,1,0,1,0,4,1,1,1
%N A327517 Number of factorizations of n that are empty or have at least two factors, all of which are > 1 and pairwise coprime.
%H A327517 Gus Wiseman, <a href="https://docs.google.com/document/d/e/2PACX-1vSX9dPMGJhxB8rOknCGvOs6PiyhupdWNpqLsnphdgU6MEVqFBnWugAXidDhwHeKqZe_YnUqYeGOXsOk/pub">Sequences counting and encoding certain classes of multisets</a>
%F A327517 a(n > 1) = A259936(n) - 1 = A000110(A001221(n)) - 1.
%t A327517 facs[n_]:=If[n<=1,{{}},Join@@Table[Map[Prepend[#,d]&,Select[facs[n/d],Min@@#>=d&]],{d,Rest[Divisors[n]]}]];
%t A327517 Table[Length[Select[facs[n],#=={}||CoprimeQ@@#&]],{n,100}]
%Y A327517 See link for additional cross-references.
%Y A327517 Cf. A302569, A302696, A304711, A305079, A327076, A327392.
%K A327517 nonn
%O A327517 1,30
%A A327517 _Gus Wiseman_, Sep 19 2019
```
### A376504
```
%I A376504 #11 Sep 28 2024 12:58:23
%S A376504 0,0,0,0,0,1,0,0,0,1,0,1,0,1,1,0,0,1,0,1,1,1,0,1,0,1,0,1,0,4,0,0,1,1,
%T A376504 1,1,0,1,1,1,0,4,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,4,0,1,1,0,1,4,0,1,
%U A376504 1,4,0,1,0,1,1,1,1,4,0,1,0,1,0,4,1,1,1
%N A376504 Number of divisors of n that are both composite and squarefree.
%C A376504 Also number of composite and squarefree m <= n such that rad(m) | n, i.e., in row n of A162306, where rad = A007947.
%C A376504 This sequence is distinct from A327517; A327517(210) != a(210).
%C A376504 Record setters are primorials, a(6) = 1, a(30) = 4, a(210) = 11, etc., since primorials P(n) = A002110(n) are the smallest instance of omega(n) = A001221(n).
%H A376504 Michael De Vlieger, <a href="/A376504/b376504.txt">Table of n, a(n) for n = 1..10000</a>
%H A376504 Michael De Vlieger, <a href="/A376504/a376504.png">Hasse diagram of row 1440 of A162306</a> showing 4 squarefree composites in green, 3 primes in red, the empty product in gray, 17 perfect powers of primes in yellow, and 72 numbers that are neither squarefree nor prime powers in blue and purple, with purple additionally representing powerful numbers that are not prime powers.
%F A376504 a(n) = 2^omega(n) - omega(n) - 1 = A034444(n) - A001221(n) - 1.
%F A376504 a(n) = 0 for n = p^m, where p is prime and m >= 0, i.e., n in A000961.
%F A376504 a(n) = A000295(omega(n)) = A000295(A001221(n)).
%t A376504 Array[2^# - # - 1 &@ PrimeNu[#] &, 120]
%Y A376504 Cf. A000005, A000295, A000961, A001221, A002110, A007947, A034444, A120944, A162306, A327517, A361373 (number of prime powers in row n of A162306), A374514 (number of divisors of n that are neither squarefree nor prime powers).
%K A376504 nonn,easy
%O A376504 1,30
%A A376504 _Michael De Vlieger_, Sep 25 2024
```


## Candidate 74: A064459 vs A342696 (score 97.0, agree 97, variant raw, family size 2)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2

### A064459
```
%I A064459 #25 Sep 09 2026 11:18:31
%S A064459 0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,
%T A064459 2,2,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,
%U A064459 5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,8,8,8,8,8
%N A064459 a(n) = Sum_{k>=1} floor(n/12^k).
%C A064459 Original incorrect name was: "Highest power of 12 dividing n!": that sequence is A090619.  If p is prime, Legendre's formula says the highest power of p dividing n! is Sum_{k>=1} floor(n/p^k), but of course 12 is not prime. - _Robert Israel_, Mar 23 2018
%H A064459 Harry J. Smith, <a href="/A064459/b064459.txt">Table of n, a(n) for n=0..1000</a>
%H A064459 Wikipedia, <a href="https://en.wikipedia.org/wiki/Legendre%27s_formula">Legendre's formula</a>.
%F A064459 a(n) = floor(n/12) + floor(n/144) + floor(n/1728) + floor(n/20736) + ....
%p A064459 f:= proc(n) add(floor(n/12^k), k=1..floor(log[12](n))) end proc:
%p A064459 f(0):= 0:
%p A064459 map(f, [$0..100]); # _Robert Israel_, Mar 23 2018
%t A064459 Table[t = 0; p = 12; While[s = Floor[n/p]; t = t + s; s > 0, p *= 12]; t, {n, 0, 100} ]
%t A064459 Join[{0},Accumulate[Table[If[Divisible[n,12],1,0],{n,110}]]] (* _Harvey P. Dale_, Feb 14 2016 *)
%o A064459 (PARI) a(n) = { my(p=12, s=0); while (n>=p, s += n\p; p*=12); s } \\ _Harry J. Smith_, Sep 15 2009
%o A064459 (GAP) List([0..110],n->Sum([1..n],k->Int(n/(12^k)))); # _Muniru A Asiru_, Mar 24 2018
%Y A064459 Cf. A011371, A054861, A090619.
%K A064459 easy,nonn
%O A064459 0,25
%A A064459 _Robert G. Wilson v_, Oct 03 2001
%E A064459 Corrected by _Robert Israel_, Mar 23 2018
```
### A342696
```
%I A342696 #13 Oct 29 2022 22:19:07
%S A342696 0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,
%T A342696 2,2,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,
%U A342696 5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,8
%N A342696 a(n) = floor(n/12).
%C A342696 Agrees with A064459 for n < 144, but a(144) = 12 whereas A064459(144) = 13.
%H A342696 <a href="/index/Rec#order_13">Index entries for linear recurrences with constant coefficients</a>, signature (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1).
%F A342696 G.f.: x^12 / ( (1+x)*(1+x^2)*(x^4-x^2+1)*(x^2-x+1)*(1+x+x^2)*(x-1)^2 ). - _R. J. Mathar_, Jul 08 2021
%F A342696 a(n) = a(n-1) + a(n-12) - a(n-13). - _Wesley Ivan Hurt_, Oct 29 2022
%t A342696 Floor[Range[0, 200]/12]
%Y A342696 Cf. A064459, A221912 (partial sums), A344420 (floor n/11).
%K A342696 nonn,easy
%O A342696 0,25
%A A342696 _Wesley Ivan Hurt_, May 18 2021
```


## Candidate 75: A001462 vs A377862 (score 96.6, agree 84, variant raw, family size 3)
Terms: 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10

### A001462
```
%I A001462 M0257 N0091 #198 Aug 21 2026 16:20:15
%S A001462 1,2,2,3,3,4,4,4,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,9,9,10,10,10,10,
%T A001462 10,11,11,11,11,11,12,12,12,12,12,12,13,13,13,13,13,13,14,14,14,14,14,
%U A001462 14,15,15,15,15,15,15,16,16,16,16,16,16,16,17,17,17,17,17,17,17,18,18,18,18,18,18,18,19
%N A001462 Golomb's sequence: a(n) is the number of times n occurs in the sequence, starting with a(1) = 1.
%C A001462 It is understood that a(n) is taken to be the smallest number >= a(n-1) which is compatible with the description.
%C A001462 In other words, this is the lexicographically earliest nondecreasing sequence of positive numbers which is equal to its RUNS transform. - _N. J. A. Sloane_, Nov 07 2018
%C A001462 Also called Silverman's sequence.
%C A001462 Vardi gives several identities satisfied by A001463 and this sequence.
%C A001462 We can interpret this sequence as a triangle: start with 1; 2,2; 3,3; and proceed by letting the row sum of row m-1 be the number of elements of row m. The partial sums of the row sums give 1, 5, 11, 38, 272, ... Conjecture: this proceeds as Lionel Levine's sequence A014644. See also A113676. - _Floor van Lamoen_, Nov 06 2005
%C A001462 A Golomb-type sequence, that is, one with the property of being a sequence of run length of itself, can be built over any sequence with distinct terms by repeating each term a corresponding number of times, in the same manner as a(n) is built over natural numbers. See cross-references for more examples. - _Ivan Neretin_, Mar 29 2015
%C A001462 From _Amiram Eldar_, Jun 19 2021: (Start)
%C A001462 Named after the American mathematician Solomon Wolf Golomb (1932-2016).
%C A001462 Guy (2004) called it "Golomb's self-histogramming sequence", while in previous editions of his book (1981 and 1994) he called it "Silverman's sequence" after David Silverman. (End)
%C A001462 a(n) is also the number of numbers that occur n times. - _Leo Crabbe_, Feb 15 2025
%D A001462 Graham Everest, Alf van der Poorten, Igor Shparlinski and Thomas Ward, Recurrence Sequences, Amer. Math. Soc., 2003; p. 10.
%D A001462 Ronald L. Graham, Donald E. Knuth and Oren Patashnik, Concrete Mathematics. Addison-Wesley, Reading, MA, 1990, p. 66.
%D A001462 Richard K. Guy, Unsolved Problems in Number Theory, 3rd Edition, Springer, 2004, Section E25, p. 347-348.
%D A001462 N. J. A. Sloane, A Handbook of Integer Sequences, Academic Press, 1973 (includes this sequence).
%D A001462 N. J. A. Sloane, Seven Staggering Sequences, in Homage to a Pied Puzzler, E. Pegg Jr., A. H. Schoen and T. Rodgers (editors), A. K. Peters, Wellesley, MA, 2009, pp. 93-110.
%D A001462 N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence).
%H A001462 T. D. Noe, <a href="/A001462/b001462.txt">Table of n, a(n) for n = 1..10000</a>
%H A001462 Altug Alkan, <a href="https://doi.org//10.1155/2018/8517125">On a Generalization of Hofstadter's Q-Sequence: A Family of Chaotic Generational Structures</a>, Complexity (2018), Article ID 8517125.
%H A001462 Joaquim Bruna, <a href="https://mat.uab.cat/web/matmat/wp-content/uploads/sites/23/2023/11/v2023n04.pdf">The golden ratio from a calculus point of view</a>, Universitat Autònoma de Barcelona, Materials matemàtics (2023) Vol. 2023, No. 4.
%H A001462 Johan Claes and Roland Miyamoto, <a href="https://arxiv.org/abs/2602.10992">Golombic and Levine sequences</a>, arXiv:2602.10992 [math.CO], 2026. See pp. 1, 3, 19.
%H A001462 Benoit Cloitre, N. J. A. Sloane and Matthew J. Vandermast, <a href="http://www.cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.html">Numerical analogues of Aronson's sequence</a>, J. Integer Seq., Vol. 6 (2003), Article 03.2.2.
%H A001462 Benoit Cloitre, N. J. A. Sloane and Matthew J. Vandermast, <a href="https://arxiv.org/abs/math/0305308">Numerical analogues of Aronson's sequence</a>, arXiv:math/0305308 [math.NT], 2003.
%H A001462 Martin Gardner, <a href="/A005130/a005130_1.pdf">Letter to N. J. A. Sloane</a>, Jun 20 1991.
%H A001462 Solomon W. Golomb, <a href="https://www.jstor.org/stable/2314829">Problem 5407</a>, Amer. Math. Monthly, Vol. 73, No. 6 (1966), p. 674.
%H A001462 Jarosław Grytczuk, <a href="https://doi.org/10.1016/j.disc.2003.10.022">Another variation on Conway's recursive sequence</a>, Discr. Math., Vol. 282, No. 1-3 (2004), pp. 149-161.
%H A001462 Brady Haran and Tony Padilla, <a href="http://www.youtube.com/watch?v=VDD6FDhKCYA">Six Sequences</a>, Numberphile video (2013).
%H A001462 Brady Haran and N. J. A. Sloane, <a href="https://www.youtube.com/watch?v=R4OvBB9KHMA">Planing Sequences (Le Rabot)</a>, Numberphile video, June 2021.
%H A001462 Daniel Marcus and N. J. Fine, <a href="https://www.jstor.org/stable/2314296">Solutions to Problem 5407</a>, Amer. Math. Monthly, Vol. 74, No. 6 (1967), pp. 740-743.
%H A001462 Christian Perfect, <a href="http://aperiodical.com/2013/07/integer-sequence-reviews-on-numberphile-or-vice-versa/">Integer sequence reviews on Numberphile (or vice versa)</a>, 2013.
%H A001462 Y.-F. S. Petermann, <a href="https://doi.org/10.1006/jnth.1995.1076">On Golomb's self-describing sequence</a>, J. Number Theory, Vol. 53, No. 1 (1995), pp. 13-24.
%H A001462 Y.-F. S. Petermann, <a href="https://doi.org/10.1007/BF01270611">On Golomb's self-describing sequence, II</a>, Arch. Math. (Basel) 67 (1996), 473-477.
%H A001462 Y.-F. S. Petermann, <a href="https://doi.org/10.1524/anly.1998.18.3.245">Is the error term wild enough?</a>, Analysis (Munich), Vol. 18 (1998), pp. 245-256.
%H A001462 Y.-F. S. Pétermann and Jean-Luc Rémy, <a href="http://projecteuclid.org/euclid.ijm/1256044933">Golomb's self-described sequence and functional-differential equations</a>, Illinois J. Math., Vol. 42, No. 3 (1998), pp. 420-440.
%H A001462 Y.-F. S. Pétermann, Jean-Luc Rémy and Ilan Vardi, <a href="https://doi.org/10.1006/aama.2001.0750">Discrete derivatives of sequences</a>, Adv. in Appl. Math., Vol. 27 (2001), pp. 562-84.
%H A001462 Jean-Luc Rémy, <a href="https://doi.org/10.1006/jnth.1997.2154">Sur la suite autodécrite de Golomb</a>, J. Number Theory, Vo. 66, No. 1 (1997), pp. 1-28.
%H A001462 Jim Sauerberg and Linghsueh Shu, <a href="https://www.jstor.org/stable/2974579">The long and the short on counting sequences</a>, Amer. Math. Monthly, Vol. 104, No. 4 (1997), pp. 306-317.
%H A001462 N. J. A. Sloane, <a href="http://neilsloane.com/doc/sg.txt">My favorite integer sequences</a>, in Sequences and their Applications (Proceedings of SETA '98).
%H A001462 N. J. A. Sloane, <a href="http://neilsloane.com/doc/g4g7.pdf">Seven Staggering Sequences</a>.
%H A001462 N. J. A. Sloane, <a href="/A001149/a001149_1.pdf">Handwritten notes on Self-Generating Sequences, 1970</a>
%H A001462 N. J. A. Sloane, <a href="/transforms.txt">Transforms</a>.
%H A001462 N. J. A. Sloane, Coordination Sequences, Planing Numbers, and Other Recent Sequences (II), Experimental Mathematics Seminar, Rutgers University, Jan 31 2019, <a href="https://vimeo.com/314786942">Part I</a>, <a href="https://vimeo.com/314790822">Part 2</a>, <a href="https://oeis.org/A320487/a320487.pdf">Slides</a>. (Mentions this sequence)
%H A001462 Ilan Vardi, <a href="https://doi.org/10.1016/0022-314X(92)90024-J">The error term in Golomb's sequence</a>, J. Number Theory, Vol. 40 (1992), pp. 1-11. (See also the Math. Review, 93d:11103)
%H A001462 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/SilvermansSequence.html">Silverman's Sequence</a>.
%H A001462 <a href="/index/Cor#core">Index entries for "core" sequences</a>
%H A001462 <a href="/index/Aa#aan">Index entries for sequences of the a(a(n)) = 2n family</a>
%F A001462 a(n) = phi^(2-phi)*n^(phi-1) + E(n), where phi is the golden number (1+sqrt(5))/2 (Marcus and Fine) and E(n) is an error term which Vardi shows is O( n^(phi-1) / log n ).
%F A001462 a(1) = 1; a(n+1) = 1 + a(n+1-a(a(n))). - _Colin Mallows_
%F A001462 a(1)=1, a(2)=2 and for a(1) + a(2) + ... + a(n-1) < k <= a(1) + a(2) + ... + a(n) we have a(k)=n. - _Benoit Cloitre_, Oct 07 2003
%F A001462 G.f.: Sum_{n>0} a(n) x^n = Sum_{k>0} x^a(k). - _Michael Somos_, Oct 21 2006
%F A001462 a(A095114(n)) = n and a(m) < n for m < A095114(n). - _Reinhard Zumkeller_, Feb 09 2012 [First inequality corrected from a(m) < m by _Glen Whitney_, Oct 06 2015]
%F A001462 Conjecture: a(n) >= n^(phi-1) for all n. - _Jianing Song_, Aug 19 2021
%F A001462 a(n) = A095114(n+1) - A095114(n). - _Alan Michael Gómez Calderón_, Dec 21 2024 after _Ralf Stephan_
%e A001462 a(1) = 1, so 1 only appears once. The next term is therefore 2, which means 2 appears twice and so a(3) is also 2 but a(4) must be 3. And so on.
%e A001462 G.f. = x + 2*x^2 + 2*x^3 + 3*x^4 + 3*x^5 + 4*x^6 + 4*x^7 + 4*x^8 + ... - _Michael Somos_, Nov 07 2018
%p A001462 N:= 10000: A001462[1]:= 1: B[1]:= 1: A001462[2]:= 2:
%p A001462 for n from 2 while B[n-1] <= N do
%p A001462   B[n]:= B[n-1] + A001462[n];
%p A001462   for j from B[n-1]+1 to B[n] do A001462[j]:= n end do
%p A001462 end do:
%p A001462 seq(A001462[j],j=1..N); # _Robert Israel_, Oct 30 2012
%t A001462 a[1] = 1; a[n_] := a[n] = 1 + a[n - a[a[n - 1]]]; Table[ a[n], {n, 84}] (* _Robert G. Wilson v_, Aug 26 2005 *)
%t A001462 (* Alternative: *)
%t A001462 GolSeq[n_]:=Nest[(k = 0; Flatten[# /. m_Integer :> (ConstantArray[++k,m])]) &, {1, 2}, n]
%t A001462 GolList=Nest[(k = 0;Flatten[# /.m_Integer :> (ConstantArray[++k,m])]) &, {1, 2},7]; AGolList=Accumulate[GolList]; Golomb[n_]:=Which[ n <= Length[GolList], GolList[[n]], n <= Total[GolList],First[FirstPosition[AGolList, _?(# > n &)]], True, $Failed] (* _JungHwan Min_, Nov 29 2015 *)
%o A001462 (PARI) a = [1, 2, 2]; for(n=3, 20, for(i=1, a[n], a = concat(a, n))); a /* _Michael Somos_, Jul 16 1999 */
%o A001462 (PARI) {a(n) = my(A, t, i); if( n<3, max(0, n), A = vector(n); t = A[i=2] = 2; for(k=3, n, A[k] = A[k-1] + if( t--==0, t = A[i++]; 1)); A[n])}; /* _Michael Somos_, Oct 21 2006 */
%o A001462 (Magma) [ n eq 1 select 1 else 1+Self(n-Self(Self(n-1))) : n in [1..100] ]; // Sergei Haller (sergei(AT)sergei-haller.de), Dec 21 2006
%o A001462 (Haskell)
%o A001462 a001462 n = a001462_list !! (n-1)
%o A001462 a001462_list = 1 : 2 : 2 : g 3  where
%o A001462    g x = (replicate (a001462 x) x) ++ g (x + 1)
%o A001462 -- _Reinhard Zumkeller_, Feb 09 2012
%o A001462 (Python)
%o A001462 a=[0, 1, 2, 2]
%o A001462 for n in range(3, 21):a+=[n for i in range(1, a[n] + 1)]
%o A001462 a[1:] # _Indranil Ghosh_, Jul 05 2017
%Y A001462 Cf. A001463 (partial sums) and A262986 (start of first run of length n).
%Y A001462 First differences are A088517.
%Y A001462 Golomb-type sequences over various substrates (from _Glen Whitney_, Oct 12 2015):
%Y A001462 A000002 and references therein (over periodic sequences),
%Y A001462 A109167 (over nonnegative integers),
%Y A001462 A080605 (over odd numbers),
%Y A001462 A080606 (over even numbers),
%Y A001462 A080607 (over multiples of 3),
%Y A001462 A169682 (over primes),
%Y A001462 A013189 (over squares),
%Y A001462 A013322 (over triangular numbers),
%Y A001462 A250983 (over integral sums of itself).
%Y A001462 Applying "ee Rabot" to this sequence gives A319434.
%Y A001462 See also A095114.
%K A001462 easy,nonn,nice,core
%O A001462 1,2
%A A001462 _N. J. A. Sloane_
```
### A377862
```
%I A377862 #11 Nov 14 2024 11:03:41
%S A377862 1,2,2,3,3,4,4,4,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,9,9,10,10,10,10,
%T A377862 10,11,11,11,11,11,12,12,12,12,12,12,13,13,13,13,13,13,14,14,14,14,14,
%U A377862 14,15,15,15,15,15,15,16,16,16,16,16,16,16,17,17,17,17,17,17,17,18,18,18,18,18,18,18,19,19
%N A377862 A variant of Golomb's sequence (A001462): the n-th digit of the sequence gives the number of times n appears, with a(1) = 1 and a(2) = 2.
%C A377862 This sequence is a base-10 variant of A167500.
%C A377862 Numbers corresponding to positions of zeros do not appear in the sequence.
%C A377862 This sequence first differ from A001462 for n = 169: a(169) = 31 whereas A001462(169) = 29.
%H A377862 Rémy Sigrist, <a href="/A377862/b377862.txt">Table of n, a(n) for n = 1..10000</a>
%H A377862 Rémy Sigrist, <a href="/A377862/a377862.png">Scatterplot of the first 500 of this sequence and of A001462</a>
%H A377862 Rémy Sigrist, <a href="/A377862/a377862.gp.txt">PARI program</a>
%o A377862 (PARI) \\ See Links section.
%Y A377862 Cf. A001462, A087739, A167500, A377863 (missing numbers), A377896.
%K A377862 nonn,base
%O A377862 1,2
%A A377862 _Rémy Sigrist_, Nov 10 2024
```


## Candidate 76: A031955 vs A288040 (score 95.4, agree 83, variant raw, family size 7)
Terms: 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42

### A031955
```
%I A031955 #53 Oct 10 2025 15:29:59
%S A031955 10,12,13,14,15,16,17,18,19,20,21,23,24,25,26,27,28,29,30,31,32,34,35,
%T A031955 36,37,38,39,40,41,42,43,45,46,47,48,49,50,51,52,53,54,56,57,58,59,60,
%U A031955 61,62,63,64,65,67,68,69,70,71,72,73,74,75,76,78,79,80,81,82,83,84,85,86,87,89,90,91,92,93,94,95,96,97,98,100,101,110,112,113,114,115,116,117,118,119,121,122,131,133,141,144,151,155,161,166
%N A031955 Numbers with exactly two distinct base-10 digits.
%C A031955 The three-digit terms are given by A210666(1,...,244). For numbers with exactly two distinct (but unspecified) digits in other bases, see A031948-A031954. For numbers made of two *given* digits, see A007088 (digits 0 & 1), A007931 (digits 1 & 2), A032810 (digits 2 & 3), A032834 (digits 3 & 4), A256290 (digits 4 & 5), A256291 (digits 5 & 6), A256292 (digits 6 & 7), A256340 (digits 7 & 8), A256341 (digits 8 & 9), and A032804-A032816 (in other bases). - _M. F. Hasler_, Apr 04 2015
%C A031955 A235154 is a subsequence. - _Altug Alkan_, Dec 03 2015
%C A031955 A235717 is a subsequence. - _Robert Israel_, Dec 03 2015
%H A031955 Reinhard Zumkeller, <a href="/A031955/b031955.txt">Table of n, a(n) for n = 1..10000</a>
%H A031955 <a href="/index/Ar#10-automatic">Index entries for 10-automatic sequences</a>.
%F A031955 A043537(a(n)) = 2. - _Reinhard Zumkeller_, Dec 03 2009
%p A031955 M:= 5: # to get all terms < 10^M
%p A031955 sort([seq(seq(seq(seq(add(10^(m-j)*`if`(member(j,S2),d2,d1),j=1..m)  ,
%p A031955   S2 = combinat:-powerset({$2..m}) minus {{}}),
%p A031955   d2 = {$0..9} minus {d1}), d1 = 1..9), m=2..M)]); # _Robert Israel_, Dec 03 2015
%t A031955 Select[Range@ 166, Length@ Union@ IntegerDigits@ # == 2 &] (* _Michael De Vlieger_, Dec 03 2015 *)
%o A031955 (Haskell)
%o A031955 a031955 n = a031955_list !! (n-1)
%o A031955 a031955_list = filter ((== 2) . a043537) [0..]
%o A031955 -- _Reinhard Zumkeller_, Feb 05 2012
%o A031955 (PARI) is_A031955(n)=#Set(digits(n))==2 \\ _M. F. Hasler_, Apr 04 2015
%o A031955 (Python)
%o A031955 def ok(n): return len(set(str(n))) == 2
%o A031955 print(list(filter(ok, range(167)))) # _Michael S. Branicky_, Oct 12 2021
%o A031955 (Python)
%o A031955 from itertools import count, product, islice
%o A031955 def agen(): # generator of terms
%o A031955     for d in count(2): yield from sorted(int("".join(t)) for f in "123456789" for r in "0123456789" if f!=r for s in product(f+r, repeat=d-1) if len(set(t:=(f, )+s)) == 2)
%o A031955 print(list(islice(agen(), 102))) # _Michael S. Branicky_, Oct 10 2025
%Y A031955 Different from A029742.
%Y A031955 Cf. A043638, A101594, A031948, A031949, A031950, A031951, A031952, A031953, A031954, A235154, A235717.
%K A031955 nonn,base,easy
%O A031955 1,1
%A A031955 _Clark Kimberling_
%E A031955 Name edited by _Charles R Greathouse IV_, Feb 13 2017
```
### A288040
```
%I A288040 #27 May 10 2020 04:30:42
%S A288040 10,12,13,14,15,16,17,18,19,20,21,23,24,25,26,27,28,29,30,31,32,34,35,
%T A288040 36,37,38,39,40,41,42,43,45,46,47,48,49,50,51,52,53,54,56,57,58,59,60,
%U A288040 61,62,63,64,65,67,68,69,70,71,72,73,74,75,76,78,79,80,81,82,83,84,85,86,87,89,90,91,92,93,94,95,96,97,98,100,101
%N A288040 Integers whose number of distinct decimal digits is prime.
%C A288040 Differs from A139819 (which contains, for example, 1234, a number with 4 distinct decimal digits). - _R. J. Mathar_, Jun 14 2017
%t A288040 Select[Range@ 101, PrimeQ@ Count[DigitCount[#], _?(# != 0 &)] &] (* _Michael De Vlieger_, Jun 06 2017 *)
%o A288040 (Python)
%o A288040 from sympy import isprime
%o A288040 print([n for n in range(1, 100) if isprime(len(set(str(n))))])
%o A288040 (PARI) isok(m) = isprime(#Set(digits(m))); \\ _Michel Marcus_, May 10 2020
%Y A288040 Union of A031955 and A031962 and ....
%K A288040 base,nonn
%O A288040 1,1
%A A288040 _Jonathan Frech_, Jun 04 2017
```


## Candidate 77: A108045 vs A127672 (score 90.0, agree 90, variant drop1, family size 2)
Terms: 1, 0, 1, -2, 0, 1, 0, -3, 0, 1, 2, 0, -4, 0, 1, 0, 5, 0, -5, 0, 1, -2, 0, 9, 0, -6, 0, 1, 0, -7

### A108045
```
%I A108045 #66 May 28 2026 19:43:46
%S A108045 1,0,1,-2,0,1,0,-3,0,1,2,0,-4,0,1,0,5,0,-5,0,1,-2,0,9,0,-6,0,1,0,-7,0,
%T A108045 14,0,-7,0,1,2,0,-16,0,20,0,-8,0,1,0,9,0,-30,0,27,0,-9,0,1,-2,0,25,0,
%U A108045 -50,0,35,0,-10,0,1,0,-11,0,55,0,-77,0,44,0,-11,0,1,2,0,-36,0,105,0,-112,0,54,0,-12,0,1
%N A108045 Triangle read by rows: lower triangular matrix obtained by inverting the lower triangular matrix in A108044.
%C A108045 Signed version of A114525. - _Eric W. Weisstein_, Apr 07 2017
%C A108045 For n >= 3, also the coefficients of the matching polynomial for the n-cycle graph C_n. - _Eric W. Weisstein_, Apr 07 2017
%C A108045 This triangle describes the Chebyshev transform of A100047 and following. Chebyshev transform of sequence b is c(n) = Sum_{k=1..n} a(n,k)*b(k). - _Christian G. Bower_, Jun 12 2005
%H A108045 G. C. Greubel, <a href="/A108045/b108045.txt">Rows n=0..100 of triangle, flattened</a>
%H A108045 Paul Barry and Aoife Hennessy, <a href="https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.html">Meixner-Type Results for Riordan Arrays and Associated Integer Sequences</a>, J. Int. Seq. 13 (2010) # 10.9.4, section 5.
%H A108045 Alexander Burstein and Louis W. Shapiro, <a href="https://arxiv.org/abs/2502.13673">Pseudo-involutions in the Riordan group and Chebyshev polynomials</a>, arXiv:2502.13673 [math.CO], 2025.
%H A108045 Aoife Hennessy, <a href="http://repository.wit.ie/1693">A Study of Riordan Arrays with Applications to Continued Fractions, Orthogonal Polynomials and Lattice Paths</a>, Ph. D. Thesis, Waterford Institute of Technology, Oct. 2011.
%H A108045 P. Peart and W.-J. Woan, <a href="https://doi.org/10.1016/S0166-218X(99)00166-3">A divisibility property for a subgroup of Riordan matrices</a>, Discrete Applied Mathematics, Vol. 98, Issue 3, Jan 2000, 255-263.
%H A108045 L. W. Shapiro, S. Getu, Wen-Jin Woan and L. C. Woodson, <a href="https://doi.org/10.1016/0166-218X(91)90088-E">The Riordan Group</a>, Discrete Appl. Maths. 34 (1991) 229-239.
%H A108045 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/CycleGraph.html">Cycle Graph</a>
%H A108045 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/MatchingPolynomial.html">Matching Polynomial</a>
%F A108045 Riordan array ( (1-x^2)/(1+x^2), x/(1+x^2)).
%F A108045 G.f.: (1-x^2)/(1+x^2-tx). - _Emeric Deutsch_, Jun 06 2005
%F A108045 From _Peter Bala_, Jun 29 2015: (Start)
%F A108045 Riordan array has the form ( x*h'(x)/h(x), h(x) ) with h(x) = x/(1 + x^2) and so belongs to the hitting time subgroup H of the Riordan group (see Peart and Woan).
%F A108045 T(n,k) = [x^(n-k)] f(x)^n with f(x) = ( 1 + sqrt(1 - 4*x^2) )/2.
%F A108045 In general the (n,k)th entry of the hitting time array ( x*h'(x)/h(x), h(x) ) has the form [x^(n-k)] f(x)^n, where f(x) = x/( series reversion of h(x) ). (End)
%F A108045 T(n,k) = T(n-1,k-1)-T(n-2,k), with T(0,0)=T(1,1)=1, T(1,0)=0, T(2,0)=-2. - _Magus K. Chu_, May 08 2026
%e A108045 Triangle begins:
%e A108045    1;
%e A108045    0,  1;
%e A108045   -2,  0,  1;
%e A108045    0, -3,  0,  1;
%e A108045    2,  0, -4,  0,  1;
%p A108045 f:=(1-x^2)/(1+x^2): g:=x/(1+x^2): G:=simplify(f/(1-t*g)): Gser:=simplify(series(G,x=0,14)): P[0]:=1: for n from 1 to 12 do P[n]:=coeff(Gser,x^n) od: for n from 0 to 12 do seq(coeff(t*P[n],t^k),k=1..n+1) od; # yields sequence in triangular form # _Emeric Deutsch_, Jun 06 2005
%t A108045 a[n_, k_] := SeriesCoefficient[(1-x^2)/(1+x^2-t*x), {x, 0, n}, {t, 0, k}]; a[0, 0] = 1; Table[a[n, k], {n, 0, 12}, {k, 0, n}] // Flatten (* _Jean-François Alcover_, Jan 08 2014, after _Emeric Deutsch_ *)
%t A108045 (* Alternative: *)
%t A108045 Flatten[{{1}, CoefficientList[Table[I^n LucasL[n, -I x], {n, 12}], x]}] (* _Eric W. Weisstein_, Apr 07 2017 *)
%t A108045 (* Alternative: *)
%t A108045 Flatten[{{1}, CoefficientList[LinearRecurrence[{x, -1}, {x, -2 + x^2}, 12], x]}] (* _Eric W. Weisstein_, Apr 07 2017 *)
%Y A108045 Cf. A114525 (unsigned version).
%Y A108045 Cf. A007318, A108044.
%Y A108045 Cf. A127672.
%K A108045 sign,tabl,easy
%O A108045 0,4
%A A108045 _N. J. A. Sloane_, Jun 02 2005
%E A108045 More terms from _Emeric Deutsch_ and _Christian G. Bower_, Jun 06 2005
```
### A127672
```
%I A127672 #138 Nov 05 2025 15:22:05
%S A127672 2,0,1,-2,0,1,0,-3,0,1,2,0,-4,0,1,0,5,0,-5,0,1,-2,0,9,0,-6,0,1,0,-7,0,
%T A127672 14,0,-7,0,1,2,0,-16,0,20,0,-8,0,1,0,9,0,-30,0,27,0,-9,0,1,-2,0,25,0,
%U A127672 -50,0,35,0,-10,0,1,0,-11,0,55,0,-77,0,44,0,-11,0,1,2,0,-36,0,105,0,-112,0,54,0,-12,0,1,0,13,0,-91
%N A127672 Monic integer version of Chebyshev T-polynomials (increasing powers).
%C A127672 The row polynomials R(n,x) := Sum_{m=0..n} a(n,m)*x^m have been called Chebyshev C_n(x) polynomials in the Abramowitz-Stegun handbook, p. 778, 22.5.11 (see A049310 for the reference, and note that on p. 774 the S and C polynomials have been mixed up in older printings). - _Wolfdieter Lang_, Jun 03 2011
%C A127672 This is a signed version of triangle A114525.
%C A127672 The unsigned column sequences (without zeros) are, for m=1..11: A005408, A000290, A000330, A002415, A005585, A040977, A050486, A053347, A054333, A054334, A057788.
%C A127672 The row polynomials R(n,x) := Sum_{m=0..n} a(n,m)*x*m, give for n=2,3,...,floor(N/2) the positive zeros of the Chebyshev S(N-1,x)-polynomial (see A049310) in terms of its largest zero rho(N):= 2*cos(Pi/N) by putting x=rho(N). The order of the positive zeros is falling: n=1 corresponds to the largest zero rho(N) and n=floor(N/2) to the smallest positive zero. Example N=5: rho(5)=phi (golden section), R(2,phi)= phi^2-2 = phi-1, the second largest (and smallest) positive zero of S(4,x). - _Wolfdieter Lang_, Dec 01 2010
%C A127672 The row polynomial R(n,x), for n >= 1, factorizes into minimal polynomials of 2*cos(Pi/k), called C(k,x), with coefficients given in A187360, as follows.
%C A127672   R(n,x) = Product_{d|oddpart(n)} C(2*n/d,x)
%C A127672          = Product_{d|oddpart(n)} C(2^(k+1)*d,x),
%C A127672   with oddpart(n)=A000265(n), and 2^k is the largest power of 2 dividing n, where k=0,1,2,...
%C A127672 (Proof: R and C are monic, the degree on both sides coincides, and the zeros of R(n,x) appear all on the r.h.s.) - _Wolfdieter Lang_, Jul 31 2011 [Theorem 1B, eq. (43) in the W. Lang link. - _Wolfdieter Lang_, Apr 13 2018]
%C A127672 The zeros of the row polynomials R(n,x) are 2*cos(Pi*(2*k+1)/(2*n)), k=0,1, ..., n-1; n>=1 (from those of the Chebyshev T-polynomials). - _Wolfdieter Lang_, Sep 17 2011
%C A127672 The discriminants of the row polynomials R(n,x) are found under A193678. - _Wolfdieter Lang_, Aug 27 2011
%C A127672 The determinant of the N X N matrix M(N) with entries M(N;n,m) = R(m-1,x[n]), 1 <= n,m <= N, N>=1, and any x[n], is identical with twice the Vandermondian Det(V(N)) with matrix entries V(N;n,m) = x[n]^(m-1). This is an instance of the general theorem given in the Vein-Dale reference on p. 59. Note that R(0,x) = 2 (not 1). See also the comments from Aug 26 2013 under A049310 and from Aug 27 2013 under A000178. - _Wolfdieter Lang_, Aug 27 2013
%C A127672 This triangle a(n,m) is also used to express in the regular (2*(n+1))-gon, inscribed in a circle of radius R, the length ratio side/R, called s(2*(n+1)), as a polynomial in rho(2*(n+1)), the length ratio (smallest diagonal)/side. See the bisections ((-1)^(k-s))*A111125(k,s) and A127677 for comments and examples. - _Wolfdieter Lang_, Oct 05 2013
%C A127672 From _Tom Copeland_, Nov 08 2015: (Start)
%C A127672 These are the characteristic polynomials a_n(x) = 2*T_n(x/2) for the adjacency matrix of the Coxeter simple Lie algebra B_n, related to the Cheybshev polynomials of the first kind, T_n(x) = cos(n*q) with x = cos(q) (see p. 20 of Damianou). Given the polynomial (x - t)*(x - 1/t) = 1 - (t + 1/t)*x + x^2 = e2 - e1*x + x^2, the symmetric power sums p_n(t,1/t) = t^n + t^(-n) of the zeros of this polynomial may be expressed in terms of the elementary symmetric polynomials e1 = t + 1/t = y and e2 = t*1/t = 1 as p_n(t,1/t) = a_n(y) = F(n,-y,1,0,0,...), where F(n,b1,b2,...,bn) are the Faber polynomials of A263916.
%C A127672 The partial sum of the first n+1 rows given t and y = t + 1/t is PS(n,t) = Sum_{k=0..n} a_n(y) = (t^(n/2) + t^(-n/2))*(t^((n+1)/2) - t^(-(n+1)/2)) / (t^(1/2) - t^(-1/2)). (For n prime, this is related simply to the cyclotomic polynomials.)
%C A127672 Then a_n(y) = PS(n,t) - PS(n-1,t), and for t = e^(iq), y = 2*cos(q), and, therefore, a_n(2*cos(q)) = PS(n,e^(iq)) - PS(n-1,e^(iq)) = 2*cos(nq) = 2*T_n(cos(q)) with PS(n,e^(iq)) = 2*cos(nq/2)*sin((n+1)q/2) / sin(q/2).
%C A127672 (End)
%C A127672 R(45, x) is the famous polynomial used by Adriaan van Roomen (Adrianus Romanus) in his Ideae mathematicae from 1593 to pose four problems, solved by Viète. See, e.g., the Havil reference, pp. 69-74. - _Wolfdieter Lang_, Apr 28 2018
%C A127672 From _Wolfdieter Lang_, May 05 2018: (Start)
%C A127672 Some identities for the row polynomials R(n, x) following from the known ones for Chebyshev T-polynomials (A053120) are:
%C A127672 (1) R(-n, x) = R(n, x).
%C A127672 (2) R(n*m, x) = R(n, R(m, x)) = R(m, R(n, x)).
%C A127672 (3) R(2*k+1, x) = (-1)^k*x*S(2*k, sqrt(4-x^2)), k >= 0, with the S row polynomials of A049310.
%C A127672 (4) R(2*k, x) = R(k, x^2-2), k >= 0.
%C A127672 (End)
%C A127672 For y = z^n + z^(-n) and x = z + z^(-1), Hirzebruch notes that y(z) = R(n,x) for the row polynomial of this entry. - _Tom Copeland_, Nov 09 2019
%D A127672 Julian Havil, The Irrationals, A Story of the Numbers You Can't Count On, Princeton University Press, Princeton and Oxford, 2012, pp. 69-74.
%D A127672 F. Hirzebruch et al., Manifolds and Modular Forms, Vieweg 1994 pp. 77, 105.
%D A127672 R. Vein and P. Dale, Determinants and Their Applications in Mathematical Physics, Springer, 1999.
%H A127672 Robert Israel, <a href="/A127672/b127672.txt">Table of n, a(n) for n = 0..10010</a> (rows 0 to 140, flattened)
%H A127672 M. Abramowitz and I. A. Stegun, eds., <a href="http://www.convertit.com/Go/ConvertIt/Reference/AMS55.ASP">Handbook of Mathematical Functions</a>, National Bureau of Standards Applied Math.Series 55, Tenth Printing, 1972.
%H A127672 Tom Copeland, <a href="http://tcjpn.wordpress.com/2015/10/12/the-elliptic-lie-triad-kdv-and-ricattt-equations-infinigens-and-elliptic-genera/">Addendum to Elliptic Lie Triad</a>
%H A127672 P. Damianou, <a href="https://arxiv.org/abs/1110.6620">On the characteristic polynomials of Cartan matrices and Chebyshev polynomials</a>, arXiv preprint arXiv:1110.6620 [math.RT], 2011-2014.
%H A127672 Gary Detlefs and Wolfdieter Lang, <a href="https://arxiv.org/abs/2304.12937">Improved Formula for the Multi-Section of the Linear Three-Term Recurrence Sequence</a>, arXiv:2304.12937 [math.CO], 2023.
%H A127672 Wolfdieter Lang, <a href="/A127672/a127672.pdf">Row polynomials.</a>
%H A127672 Wolfdieter Lang, <a href="https://arxiv.org/abs/1210.1018">The field Q(2cos(pi/n)), its Galois group and length ratios in the regular n-gon</a>, arXiv:1210.1018 [math.GR], 2012-2017.
%H A127672 Wolfdieter Lang, <a href="https://arxiv.org/abs/2008.04300">On the Equivalence of Three Complete Cyclic Systems of Integers</a>, arXiv:2008.04300 [math.NT], 2020.
%H A127672 <a href="/index/Ch#Cheby">Index entries for sequences related to Chebyshev polynomials.</a>
%F A127672 a(n,0) = 0 if n is odd, a(n,0) = 2*(-1)^(n/2) if n is even, else a(n,m) = t(n,m)/2^(m-1) with t(n,m):=A053120(n,m) (coefficients of Chebyshev T-polynomials).
%F A127672 G.f. for m-th column (signed triangle): 2/(1+x^2) if m=0 else (x^m)*(1-x^2)/(1+x^2)^(m+1).
%F A127672 Riordan type matrix ((1-x^2)/(1+x^2),x/(1+x^2)) if one puts a(0,0)=1 (instead of 2).
%F A127672 O.g.f. for row polynomials: R(x,z) := Sum_{n>=0} R(n,x)*z^n = (2-x*z)*S(x,z), with the o.g.f. S(x,z) = 1/(1 - x*z + z^2) for the S-polynomials (see A049310).
%F A127672 Note that R(n,x) = R(2*n,sqrt(2+x)), n>=0 (from the o.g.f.s of both sides). - _Wolfdieter Lang_, Jun 03 2011
%F A127672 a(n,m) := 0 if n < m or n+m odd; a(n,0) = 2*(-1)^(n/2) (n even); else a(n,m) = ((-1)^((n+m)/2 + m))*n*binomial((n+m)/2-1,m-1)/m.
%F A127672 Recursion for n >= 2 and m >= 2: a(n,m) = a(n-1,m-1) - a(n-2,m), a(n,m) = 0 if n < m, a(2*k,1) = 0, a(2*k+1,1) = (2*k+1)*(-1)^k. In addition, for column m=0: a(2*k,0) = 2*(-1)^k, a(2*k+1,0) = 0, k>=0.
%F A127672 Chebyshev T(n,x) = Sum{m=0..n} a(n,m)*2^(m-1)*x^m. - _Wolfdieter Lang_, Jun 03 2011
%F A127672 R(n,x) = 2*T(n,x/2) = S(n,x) - S(n-2,x), n>=0, with Chebyshev's T- and S-polynomials, showing that they are integer and monic polynomials. - _Wolfdieter Lang_, Nov 08 2011
%F A127672 From _Tom Copeland_, Nov 08 2015: (Start)
%F A127672 a(n,x) = sqrt(2 + a(2n,x)), or 2 + a(2n,x) = a(n,x)^2, is a reflection of the relation of the Chebyshev polynomials of the first kind to the cosine and the half-angle formula, cos(q/2)^2 = (1 + cos(q))/2.
%F A127672 Examples: For n = 2, -2 + x^2 = sqrt(2 + 2 - 4*x^2 + x^4).
%F A127672 For n = 3, -3*x + x^3 = sqrt(2 - 2 + 9*x^2 - 6*x^4 + x^6).
%F A127672 (End)
%F A127672 L(x,h1,h2) = -log(1 - h1*x + h2*x^2) = Sum_{n>0} F(n,-h1,h2,0,...,0) x^n/n = h1*x + (-2*h2 + h1^2) x^2/2 + (-3*h1*h2 + h1^3) x^3/3 + ... is a log series generator of the bivariate row polynomials where T(0,0) = 0 and F(n,b1,b2,...,bn) are the Faber polynomials of A263916. exp(L(x,h1,h2)) = 1 / (1 - h1*x + h2*x^2) is the o.g.f. of A049310. - _Tom Copeland_, Feb 15 2016
%e A127672 Row n=4: [2,0,-4,0,1] stands for the polynomial 2*y^0 - 4*y^2 + 1*y^4. With y^m replaced by 2^(m-1)*x^m this becomes T(4,x) = 1 - 8*x^2 + 8*x^4.
%e A127672 Triangle begins:
%e A127672 n\m   0   1   2   3   4   5   6   7   8   9  10 ...
%e A127672 0:    2
%e A127672 1:    0   1
%e A127672 2:   -2   0   1
%e A127672 3:    0  -3   0   1
%e A127672 4:    2   0  -4   0   1
%e A127672 5:    0   5   0  -5   0   1
%e A127672 6:   -2   0   9   0  -6   0   1
%e A127672 7:    0  -7   0  14   0  -7   0   1
%e A127672 8:    2   0 -16   0  20   0  -8   0   1
%e A127672 9:    0   9   0 -30   0  27   0  -9   0   1
%e A127672 10:  -2   0  25   0 -50   0  35   0 -10   0   1 ...
%e A127672 Factorization into minimal C-polynomials:
%e A127672 R(12,x) = R((2^2)*3,x) = C(24,x)*C(8,x) = C((2^3)*1,x)*C((2^3)*3,x). - _Wolfdieter Lang_, Jul 31 2011
%p A127672 seq(seq(coeff(2*orthopoly[T](n,x/2),x,j),j=0..n),n=0..20); # _Robert Israel_, Aug 04 2015
%t A127672 a[n_, k_] := SeriesCoefficient[(2 - t*x)/(1 - t*x + x^2), {x, 0, n}, {t, 0, k}]; Flatten[Table[a[n, k], {n, 0, 12}, {k, 0, n}]] (* _L. Edson Jeffery_, Nov 02 2017 *)
%Y A127672 Row sums (signed): A057079(n-1). Row sums (unsigned): A000032(n) (Lucas numbers). Alternating row sums: A099837(n+3).
%Y A127672 Bisection: A127677 (even n triangle, without zero entries), ((-1)^(n-m))*A111125(n, m) (odd n triangle, without zero entries).
%Y A127672 Cf. A049310, A053120, A108045, A263916.
%K A127672 sign,tabl,easy
%O A127672 0,1
%A A127672 _Wolfdieter Lang_, Mar 07 2007
%E A127672 Name changed and table rewritten by _Wolfdieter Lang_, Nov 08 2011
```


## Candidate 78: A277998 vs A289288 (score 90.0, agree 90, variant raw, family size 2)
Terms: 1, 9, 11, 91, 92, 8, 2, 81, 93, 7, 3, 71, 94, 6, 4, 61, 95, 5, 51, 96, 41, 97, 31, 98, 21, 99, 12, 82, 83, 72

### A277998
```
%I A277998 #6 Nov 08 2016 07:37:04
%S A277998 1,9,11,91,92,8,2,81,93,7,3,71,94,6,4,61,95,5,51,96,41,97,31,98,21,99,
%T A277998 12,82,83,72,84,62,85,52,86,42,87,32,88,22,89,13,73,74,63,75,53,76,43,
%U A277998 77,33,78,23,79,14,64,65,54,66,44,67,34,68,24,69,15,55,56,45,57,35,58,25,59,16,46,47,36,48,26,49,17,37,38,27,39,18,28,29,19,101,901,902,801,903,701,904,601,905,501,906,401,907,301,908,201
%N A277998 Lexicographically first sequence (with no duplicates) where the last digit of a(n) added to the first digit of a(n+1) equals 10.
%C A277998 The sequence starts with a(1) = 1 and was always extended with the smallest integer not yet present that does not lead to a contradiction.
%H A277998 Jean-Marc Falcoz, <a href="/A277998/b277998.txt">Table of n, a(n) for n = 1..10001</a>
%e A277998 The sequence begins with 1, 9, 11, 91, 92, 8, 2, 81, 93, 71... The two digits that border the first comma are 1 and 9 that sum up to 10 as required; the 2nd comma is bordered by 9 and 1; the 3rd one by 1 and 9 again; the 4th one by 1 and 9 too; the 5th one by 2 and 8; the 6th one by 8 and 2; the 7th one by 2 and 8 again; the 8th one by 1 and 9; the 9th one by 3 and 7, etc.
%K A277998 nonn,base
%O A277998 1,2
%A A277998 _Eric Angelini_ and _Jean-Marc Falcoz_, Nov 08 2016
```
### A289288
```
%I A289288 #9 Jul 24 2017 12:54:42
%S A289288 1,9,11,91,92,8,2,81,93,7,3,71,94,6,4,61,95,5,51,96,41,97,31,98,21,99,
%T A289288 12,82,83,72,84,62,85,52,86,42,87,32,88,22,89,13,73,74,63,75,53,76,43,
%U A289288 77,33,78,23,79,14,64,65,54,66,44,67,34,68,24,69,15,55,56,45,57,35,58,25,59,16,46,47,36,48,26,49,17,37,38,27,39,18,28,29,19,111,911,912,811,913,711,914,611,915,511,916,411,917,311,918,211,919,112,812,813,712
%N A289288 Starting with a(1) = 1, a(n) = smallest nonnegative integer not yet in the sequence such that the last digit of a(n-1) plus the first digit of a(n) is equal to 10. The digit 0 is not allowed.
%C A289288 Unlike the sequences in A289283 - A289287, this sequence is infinite and does not seem to follow central polygonal numbers.
%t A289288 Module[{a = {1}, k, d = 10}, TimeConstrained[Do[k = 2; While[Or[MemberQ[a, k], MemberQ[IntegerDigits@ k, 0], # != d] &[Mod[a[[n - 1]], 10] + First@ IntegerDigits@ k], k++]; AppendTo[a, k], {n, 2, Infinity}], 2]; a] (* _Michael De Vlieger_, Jul 14 2017 *)
%Y A289288 Cf. A002061, A289283, A289284, A289285, A289286, A289287.
%K A289288 nonn,base
%O A289288 1,2
%A A289288 _Enrique Navarrete_, Jul 01 2017
```


## Candidate 79: A188734 vs A188941 (score 88.3, agree 128, variant drop2, family size 3)
Terms: 3, 7, 6, 5, 5, 6, 4, 4, 3, 7, 0, 7, 4, 6, 3, 7, 4, 1, 3, 0, 9, 1, 6, 5, 3, 3, 0, 7, 5, 7

### A188734
```
%I A188734 #26 Jun 01 2026 01:22:57
%S A188734 3,7,6,5,5,6,4,4,3,7,0,7,4,6,3,7,4,1,3,0,9,1,6,5,3,3,0,7,5,7,5,9,4,2,
%T A188734 7,8,2,7,8,3,5,9,9,0,7,6,4,0,2,1,4,3,3,4,6,9,8,4,1,4,8,0,9,7,3,1,5,9,
%U A188734 6,8,7,3,7,7,5,6,4,2,2,0,5,0,7,4,0,0,3,8,5,6,6,6,7,9,3,0,7,6,6,0,9,0,9,3,6,0,6,1,6,5,3,4,9,8,6,4,7,8,0,5,3,4,3,7,1,6,3,0,3,0
%N A188734 Decimal expansion of (7+sqrt(65))/4.
%C A188734 Apart from the second digit, the same as A171417. - _R. J. Mathar_, Apr 15 2011
%C A188734 Apart from the first two digits, the same as A188941. - _Joerg Arndt_, Apr 16 2011
%C A188734 Decimal expansion of the length/width ratio of a (7/2)-extension rectangle.  See A188640 for definitions of shape and r-extension rectangle.
%C A188734 A (7/2)-extension rectangle matches the continued fraction [3,1,3,3,1,3,3,1,3,3,1,3,3,...] for the shape L/W=(7+sqrt(65))/4.  This is analogous to the matching of a golden rectangle to the continued fraction [1,1,1,1,1,1,1,1,...].  Specifically, for the (7/2)-extension rectangle, 3 squares are removed first, then 1 square, then 3 squares, then 3 squares,..., so that the original rectangle of shape (7+sqrt(65))/4 is partitioned into an infinite collection of squares.
%H A188734 G. C. Greubel, <a href="/A188734/b188734.txt">Table of n, a(n) for n = 1..10000</a>
%H A188734 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%F A188734 Minimal polynomial: 2*x^2 - 7*x - 2. - _Amiram Eldar_, Jun 01 2026
%e A188734 3.7655644370746374130916533075759427827835990...
%p A188734 evalf((7+sqrt(65))/4,140); # _Muniru A Asiru_, Nov 01 2018
%t A188734 r = 7/2; t = (r + (4 + r^2)^(1/2))/2; FullSimplify[t]
%t A188734 N[t, 130]
%t A188734 RealDigits[N[t, 130]][[1]]
%o A188734 (PARI) default(realprecision, 100); (7+sqrt(65))/4 \\ _G. C. Greubel_, Nov 01 2018
%o A188734 (Magma) SetDefaultRealField(RealField(100)); (7+Sqrt(65))/4; // _G. C. Greubel_, Nov 01 2018
%Y A188734 Cf. A171417, A188640, A188941.
%K A188734 nonn,cons
%O A188734 1,1
%A A188734 _Clark Kimberling_, Apr 12 2011
```
### A188941
```
%I A188941 #22 May 30 2026 04:30:37
%S A188941 4,2,6,5,5,6,4,4,3,7,0,7,4,6,3,7,4,1,3,0,9,1,6,5,3,3,0,7,5,7,5,9,4,2,
%T A188941 7,8,2,7,8,3,5,9,9,0,7,6,4,0,2,1,4,3,3,4,6,9,8,4,1,4,8,0,9,7,3,1,5,9,
%U A188941 6,8,7,3,7,7,5,6,4,2,2,0,5,0,7,4,0,0,3,8,5,6,6,6,7,9,3,0,7,6,6,0,9,0,9,3,6,0,6,1,6,5,3,4,9,8,6,4,7,8,0,5,3,4,3,7,1,6,3,0,3,0
%N A188941 Decimal expansion of (9+sqrt(65))/4.
%C A188941 Apart from the first digit, the same as A171417. Apart from the first 2 digits, the same as A188734. - _R. J. Mathar_, Apr 15 2011
%C A188941 Decimal expansion of the shape (= length/width = (9+sqrt(65))/4) of the greater (9/2)-contraction rectangle.
%C A188941 See A188738 for an introduction to lesser and greater r-contraction rectangles, their shapes, and partitioning these rectangles into a sets of squares in a manner that matches the continued fractions of their shapes.
%D A188941 Minimal polynomial: 2*x^2 - 9*x + 2. - _Amiram Eldar_, May 30 2026
%H A188941 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%e A188941 4.2655644370746374130916533075759427827835990...
%t A188941 r = 9/2; t = (r + (-4 + r^2)^(1/2))/2; FullSimplify[t]
%t A188941 N[t, 130]
%t A188941 RealDigits[N[t, 130]][[1]]
%t A188941 (* Alternative: *)
%t A188941 RealDigits[(9+Sqrt[65])/4,10,150][[1]] (* _Harvey P. Dale_, Jan 31 2023 *)
%o A188941 (PARI) (9+sqrt(65))/4 \\ _Jinyuan Wang_, Apr 14 2020
%Y A188941 Cf. A171417, A188734, A188738, A188940.
%K A188941 nonn,cons
%O A188941 1,1
%A A188941 _Clark Kimberling_, Apr 14 2011
```


## Candidate 80: A355824 vs A355826 (score 87.6, agree 127, variant abs, family size 3)
Terms: 1, -1, -1, 0, -1, 1, -1, 1, 0, 1, -1, 0, -1, 1, 1, -2, -1, 0, -1, 0, 1, 1, -1, -1, 0, 1, 1, 0, -1, -1

### A355824
```
%I A355824 #11 Jul 20 2022 08:50:20
%S A355824 1,-1,-1,0,-1,1,-1,1,0,1,-1,0,-1,1,1,-2,-1,0,-1,0,1,1,-1,-1,0,1,1,0,
%T A355824 -1,-1,-1,2,1,1,1,0,-1,1,1,-1,-1,-1,-1,0,0,1,-1,2,0,0,1,0,-1,-1,1,-1,
%U A355824 1,1,-1,0,-1,1,0,0,1,-1,-1,0,1,-1,-1,0,-1,1,0,0,1,-1,-1,2,-2,1,-1,0,1,1,1,-1,-1,0,1,0,1,1,1,-2,-1,0,0,0,-1,-1,-1,-1,-1,1,-1,0,-1,-1,1,2,-1,-1,1,0,0,1,1,1,0,1,1,0,1,0,-1,-3
%N A355824 Dirichlet inverse of A355823, characteristic function of exponentially 2^n-numbers.
%C A355824 Multiplicative because A355823 is.
%H A355824 Antti Karttunen, <a href="/A355824/b355824.txt">Table of n, a(n) for n = 1..100000</a>
%H A355824 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A355824 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A355823(n/d) * a(d).
%t A355824 s[n_] := If[AllTrue[FactorInteger[n][[;; , 2]], # == 2^IntegerExponent[#, 2] &], 1, 0]; a[1] = 1; a[n_] := a[n] = -DivisorSum[n, s[n/#] * a[#] &, # < n &]; Array[a, 100] (* _Amiram Eldar_, Jul 19 2022 *)
%o A355824 (PARI)
%o A355824 A355823(n) = factorback(apply(e->!bitand(e,e-1),factor(n)[,2]));
%o A355824 memoA355824 = Map();
%o A355824 A355824(n) = if(1==n,1,my(v); if(mapisdefined(memoA355824,n,&v), v, v = -sumdiv(n,d,if(d<n,A355823(n/d)*A355824(d),0)); mapput(memoA355824,n,v); (v)));
%Y A355824 Cf. A138302, A355823.
%Y A355824 Differs from related A355826 for the first time at n=128, where a(128) = -3, while A355826(128) = -4.
%K A355824 sign,mult
%O A355824 1,16
%A A355824 _Antti Karttunen_, Jul 19 2022
```
### A355826
```
%I A355826 #12 Jul 20 2022 08:50:30
%S A355826 1,-1,-1,0,-1,1,-1,1,0,1,-1,0,-1,1,1,-2,-1,0,-1,0,1,1,-1,-1,0,1,1,0,
%T A355826 -1,-1,-1,2,1,1,1,0,-1,1,1,-1,-1,-1,-1,0,0,1,-1,2,0,0,1,0,-1,-1,1,-1,
%U A355826 1,1,-1,0,-1,1,0,0,1,-1,-1,0,1,-1,-1,0,-1,1,0,0,1,-1,-1,2,-2,1,-1,0,1,1,1,-1,-1,0,1,0,1,1,1,-2,-1,0,0,0,-1,-1,-1,-1,-1,1,-1,0,-1,-1,1,2,-1,-1,1,0,0,1,1,1,0,1,1,0,1,0,-1,-4
%N A355826 Dirichlet inverse of A355825, characteristic function of exponentially odious numbers.
%C A355826 Multiplicative because A355825 is.
%H A355826 Antti Karttunen, <a href="/A355826/b355826.txt">Table of n, a(n) for n = 1..100000</a>
%H A355826 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A355826 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A355825(n/d) * a(d).
%t A355826 s[n_] := If[AllTrue[FactorInteger[n][[;; , 2]], OddQ[DigitCount[#, 2, 1]] &], 1, 0]; a[1] = 1; a[n_] := a[n] = -DivisorSum[n, s[n/#]*a[#] &, # < n &]; Array[a, 100] (* _Amiram Eldar_, Jul 19 2022 *)
%o A355826 (PARI)
%o A355826 A355825(n) = factorback(apply(e->(hammingweight(e)%2),factor(n)[,2]));
%o A355826 memoA355826 = Map();
%o A355826 A355826(n) = if(1==n,1,my(v); if(mapisdefined(memoA355826,n,&v), v, v = -sumdiv(n,d,if(d<n,A355825(n/d)*A355826(d),0)); mapput(memoA355826,n,v); (v)));
%Y A355826 Cf. A270428, A355825.
%Y A355826 Differs from related A355824 for the first time at n=128, where a(128) = -4, while A355824(128) = -3.
%Y A355826 Cf. also A355819.
%K A355826 sign,mult
%O A355826 1,16
%A A355826 _Antti Karttunen_, Jul 19 2022
```


## Candidate 81: A374130 vs A374466 (score 87.6, agree 127, variant raw, family size 3)
Terms: 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1

### A374130
```
%I A374130 #17 Jul 16 2024 08:09:19
%S A374130 0,1,1,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,1,1,0,0,0,
%T A374130 0,0,1,0,0,0,1,1,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,1,1,0,
%U A374130 0,1,1,1,1,0,0,0,0,1,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,1,1,0,1,0,1,1,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0
%N A374130 a(n) = 1 if bitwise-XOR of the exponents of primes in the prime factorization of n is equal to 1, otherwise 0.
%H A374130 Antti Karttunen, <a href="/A374130/b374130.txt">Table of n, a(n) for n = 1..100000</a>
%H A374130 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%H A374130 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A374130 a(n) = [A268387(n) = 1], where [ ] is the Iverson bracket.
%F A374130 For k in A268390, a(A059897(n,k)) = a(n).
%t A374130 A374130[n_] := If[n == 1, 0, Boole[BitXor @@ FactorInteger[n][[All, 2]] == 1]];
%t A374130 Array[A374130, 100] (* _Paolo Xausa_, Jul 16 2024 *)
%o A374130 (PARI)
%o A374130 A268387(n) = { my(f=factor(n), b=0); for(k=1, #f~, b = bitxor(b, f[k, 2]); ); b; }; \\ From A268387
%o A374130 A374130(n) = (1==A268387(n));
%Y A374130 Characteristic function of A374595.
%Y A374130 Cf. A059897, A268387, A268390.
%Y A374130 Differs from A252233 first at n=72, where a(72) = 1, while A252233(72) = 0.
%Y A374130 Differs from A374466 first at n=128, where a(128) = 0, while A374466(128) = 1.
%K A374130 nonn
%O A374130 1
%A A374130 _Antti Karttunen_ and _Peter Munn_, Jul 14 2024
```
### A374466
```
%I A374466 #13 Jul 14 2024 08:42:19
%S A374466 0,1,1,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,1,1,0,0,0,
%T A374466 0,0,1,0,0,0,1,1,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,1,1,0,
%U A374466 0,1,1,1,1,0,0,0,0,1,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,1,1,0,1,0,1,1,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1
%N A374466 a(n) = 1 if n is the product of an odd number of primes and the total number of 1-bits in the exponents of its prime factorization is odd, otherwise 0.
%H A374466 Antti Karttunen, <a href="/A374466/b374466.txt">Table of n, a(n) for n = 1..100000</a>
%H A374466 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%H A374466 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A374466 a(n) = A066829(n) * (1-A359464(n)) = A000035(A001222(n)) * A000035(A064547(n)).
%o A374466 (PARI)
%o A374466 A064547(n) = { my(f = factor(n)[, 2]); sum(k=1, #f, hammingweight(f[k])); };
%o A374466 A066829(n) = (bigomega(n)%2);
%o A374466 A374466(n) = ((A064547(n)%2) * A066829(n));
%Y A374466 Characteristic function of A374467.
%Y A374466 Cf. A000035, A001222, A064547, A359464.
%Y A374466 Differs from A252233 first at n=72, where a(72) = 1, while A252233(72) = 0.
%Y A374466 Differs from A374130 first at n=128, where a(128) = 1, while A374130(128) = 0.
%K A374466 nonn
%O A374466 1
%A A374466 _Antti Karttunen_, Jul 14 2024
```


## Candidate 82: A298735 vs A384916 (score 87.0, agree 87, variant raw, family size 2)
Terms: 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1

### A298735
```
%I A298735 #38 Mar 21 2023 15:22:59
%S A298735 1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,
%T A298735 1,2,1,1,1,1,1,1,1,1,2,1,1,1,2,2,1,1,1,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,
%U A298735 1,1,1,2,1,1,2,1,1,1,1,1,3,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,2,2,2,1,1,1,1,1
%N A298735 Number of odd squares dividing n.
%C A298735 The smallest integer with exactly m odd square divisors is A357450(m). - _Bernard Schott_, Oct 03 2022
%H A298735 Antti Karttunen, <a href="/A298735/b298735.txt">Table of n, a(n) for n = 1..65537</a>
%F A298735 G.f.: Sum_{k>=1} x^((2*k-1)^2)/(1 - x^((2*k-1)^2)).
%F A298735 Multiplicative with a(2^e) = 1 and a(p^e) = floor(e/2) + 1 for p > 2. - _Amiram Eldar_, Sep 11 2020
%F A298735 a(n) = A046951(4*n) - A046951(n) = A046951(A000265(n)). - _Velin Yanev_, _Antti Karttunen_, Dec 06 2021
%F A298735 Asymptotic mean: lim_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi^2/8 (A111003). - _Amiram Eldar_, Sep 25 2022
%e A298735 a(81) = 3 because 81 has 5 divisors {1, 3, 9, 27, 81} among which 3 are odd squares {1, 9, 81}.
%t A298735 nmax = 105; Rest[CoefficientList[Series[Sum[x^(2 k - 1)^2/(1 - x^(2 k - 1)^2), {k, 1, nmax}], {x, 0, nmax}], x]]
%t A298735 a[n_] := Length[Select[Divisors[n], IntegerQ[Sqrt[#]] && OddQ[#] &]]; Table[a[n], {n, 1, 105}]
%t A298735 f[2, e_] := 1; f[p_, e_] := Floor[e/2] + 1; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Sep 11 2020 *)
%o A298735 (PARI) a(n)=factorback(apply(e->e\2+1, factor(n/2^valuation(n,2))[, 2])) \\ _Rémy Sigrist_, Jan 26 2018
%Y A298735 Cf. A000265, A001227, A016754, A046951, A056170, A071325, A111003, A122132 (positions of ones), A357450.
%K A298735 nonn,mult,easy
%O A298735 1,9
%A A298735 _Ilya Gutkovskiy_, Jan 25 2018
%E A298735 Keyword mult added by _Rémy Sigrist_, Jan 26 2018
```
### A384916
```
%I A384916 #11 Nov 23 2025 03:17:02
%S A384916 1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,
%T A384916 1,2,1,1,1,1,1,1,1,1,2,1,1,1,2,2,1,1,1,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,
%U A384916 1,1,1,2,1,1,2,1,1,1,1,1,3,1,1,1,1,1,1
%N A384916 The number of unordered factorizations of n into powers of primes of the form p^e where p is prime and 0 <= e < p.
%C A384916 First differs from A298735 at n = 125.
%H A384916 Amiram Eldar, <a href="/A384916/b384916.txt">Table of n, a(n) for n = 1..10000</a>
%F A384916 Multiplicative with a(p^e) = A026820(e, p-1).
%F A384916 a(n) <= A384915(n), with equality if and only if n is in A048103.
%e A384916 a(9) = 2 since 9 has 2 factorizations: 3^1 * 3^1 and 3^2, with exponents 1 and 2 that are < 3.
%t A384916 f[p_, e_] := Length[IntegerPartitions[e, p-1]]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100]
%o A384916 (PARI) T(n, k)=my(s); forpart(v=n, s++, , k); s \\ _Charles R Greathouse IV_ at A026820
%o A384916 a(n) = {my(f = factor(n)); prod(i = 1, #f~, T(f[i,2], f[i,1]-1));}
%Y A384916 Cf. A026820, A048103, A298735.
%Y A384916 Similar sequences: A000688, A046951, A050361, A050377, A188581, A188585, A322885, A370256, A384912, A384913, A384914, A384915.
%K A384916 nonn,easy,mult
%O A384916 1,9
%A A384916 _Amiram Eldar_, Jun 12 2025
```


## Candidate 83: A185014 vs A240467 (score 86.2, agree 75, variant drop1, family size 3)
Terms: 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A185014
```
%I A185014 #24 May 07 2026 00:58:02
%S A185014 0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A185014 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%U A185014 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
%N A185014 Characteristic function of four.
%C A185014 Number of connected 2-regular (simple) graphs with girth exactly 4.
%C A185014 The Euler transformation of this sequence is A121262.
%H A185014 <a href="/index/Rec#order_01">Index entries for linear recurrences with constant coefficients</a>, signature (1).
%F A185014 a(n) = A185114(n) - A185115(n).
%t A185014 PadRight[{0, 0, 0, 0, 1}, 100] (* _Paolo Xausa_, May 06 2026 *)
%o A185014 (Python)
%o A185014 def A185014(n): return int(n==4) # _Chai Wah Wu_, Feb 04 2022
%Y A185014 Characteristic function of g: A000007 (g=0), A063524 (g=1), A185012 (g=2), A185013 (g=3), this sequence (g=4), A185015 (g=5), A185016 (g=6), A185017 (g=7).
%K A185014 nonn,easy
%O A185014 0,1
%A A185014 _Jason Kimberley_, Sep 30 2011
```
### A240467
```
%I A240467 #25 Feb 28 2020 08:19:32
%S A240467 1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A240467 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%U A240467 0,0,0,0,0,0,0,0,-1,0,0,0,-1,0,0,0,0,0,0
%N A240467 Inverse of 152nd cyclotomic polynomial.
%C A240467 Periodic with period length 152. - _Ray Chandler_, Apr 03 2017
%C A240467 In general the expansion of 1/Phi(N) is N-periodic, but also satisfies a linear recurrence of lower order given by degree(Phi(N)) = phi(N) = A000010(N) < N. The signature is given by the coefficients of (1-Phi(N)). - _M. F. Hasler_, Feb 18 2018
%H A240467 Vincenzo Librandi, <a href="/A240467/b240467.txt">Table of n, a(n) for n = 0..1000</a>
%H A240467 <a href="/index/Rec#order_72">Index entries for linear recurrences with constant coefficients</a>, order 72, signature (0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1).
%H A240467 <a href="/index/Pol#poly_cyclo_inv">Index to sequences related to inverse of cyclotomic polynomials</a>
%t A240467 CoefficientList[Series[1/Cyclotomic[152, x], {x, 0, 200}], x]
%o A240467 (PARI) Vec(1/polcyclo(152) + O(x^99)) \\ _Jinyuan Wang_, Feb 28 2020
%Y A240467 Cf. similar sequences (namely 1/Phi(N), N <= 75) listed in A240328.
%Y A240467 Cf. also A240465 (76), A014086 (77), A014087 (78), A014093 (84), A014094 (85), A014096 (87), A014099 (90), A014100 (91), A014102 (93), A014104 (95), A014108 (99), A014111 (102), A014114 (105), A014119 (110), A014123 (114), A014124 (115), A014128 (119), A014129 (120), A014135 (126), A014139 (130), A014141 (132), A014142 (133), A014147 (138), A014149 (140), A014152 (143), A014154 (145), A014159 (150), A014163 (154) - A014165 (156), A014170 (161), A014174 (165), A014177 (168), A014179 (170), A014183 (174), A014184 (175), A014189 (180), A014191 (182), A014194 (185) - A014196 (187), A014199 (190), A014204 (195), A014207 (198), A014212 (203), A014218 (209), A014219 (210), A014226 (217), A014229 (220), A014230 (221), A014239 (230), A014240 (231), A014247 (238), A014256 (247), A014262 (253).
%K A240467 sign,easy
%O A240467 0
%A A240467 _Vincenzo Librandi_, Apr 06 2014
```


## Candidate 84: A359466 vs A359467 (score 86.2, agree 125, variant raw, family size 3)
Terms: 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0

### A359466
```
%I A359466 #18 Jan 05 2023 03:20:28
%S A359466 0,0,0,1,0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,
%T A359466 0,0,0,0,0,1,0,0,0,1,1,0,0,1,1,1,0,1,0,1,0,1,0,0,0,1,0,0,1,1,0,0,0,1,
%U A359466 0,0,0,0,0,0,1,1,0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1
%N A359466 a(n) = 1 if n has exactly one non-unitary prime factor, otherwise 0.
%H A359466 Antti Karttunen, <a href="/A359466/b359466.txt">Table of n, a(n) for n = 1..100000</a>
%H A359466 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%H A359466 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%F A359466 a(n) = [A056170(n) == 1], where [ ] is the Iverson bracket.
%F A359466 a(n) = A353670(A181819(n)).
%F A359466 a(n) >= A359472(n) and a(n) >= A359474(n).
%F A359466 Sum_{k=1..n} a(k) ~ c * n, where c = A059956 * A154945 = 0.335389... . - _Amiram Eldar_, Jan 05 2023
%t A359466 a[n_] := If[Count[(f = FactorInteger[n])[[;; , 2]], 1] == Length[f] - 1, 1, 0]; Array[a, 100] (* _Amiram Eldar_, Jan 05 2023 *)
%o A359466 (PARI) A359466(n) = { my(f=factor(n)); (1==#select(x->(x>1), f[, 2])); }; \\ After isok function in A190641
%Y A359466 Characteristic function of A190641.
%Y A359466 Cf. A056170, A181819, A353670, A359472, A359474.
%Y A359466 Differs from A359467 for the first time at n=225, where a(225) = 0, while A359467(225) = 1.
%Y A359466 Cf. A059956, A154945.
%K A359466 nonn
%O A359466 1
%A A359466 _Antti Karttunen_, Jan 02 2023
```
### A359467
```
%I A359467 #21 Jan 24 2023 02:50:51
%S A359467 0,0,0,1,0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,
%T A359467 0,0,0,0,0,1,0,0,0,1,1,0,0,1,1,1,0,1,0,1,0,1,0,0,0,1,0,0,1,1,0,0,0,1,
%U A359467 0,0,0,0,0,0,1,1,0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1
%N A359467 a(n) = (A166486(n)+A353627(n)) mod 2.
%H A359467 Antti Karttunen, <a href="/A359467/b359467.txt">Table of n, a(n) for n = 1..100000</a>
%H A359467 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%F A359467 a(n) = (A166486(n)+A355689(n)) mod 2 = (A353627(n)+A358839(n)) mod 2.
%F A359467 a(n) = A342419(n) mod 2.
%F A359467 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = 3/4 - 4/Pi^2 = 0.344715... . - _Amiram Eldar_, Jan 24 2023
%t A359467 a[n_] := Module[{e = IntegerExponent[n, 2], o}, o = n/2^e; sqf = SquareFreeQ[o]; If[(e > 1 && sqf) || (e < 2 && ! sqf), 1, 0]]; Array[a, 100] (* _Amiram Eldar_, Jan 24 2023 *)
%o A359467 (PARI) A359467(n) = (((!(n%4))&&issquarefree(n>>valuation(n, 2))) + ((n%4)&&!issquarefree(n)));
%o A359467 (PARI)
%o A359467 A166486(n) = !!(n%4);
%o A359467 A355689(n) = { my(f = factor(n)); prod(k=1, #f~, if(2==f[k,1], (-1)^f[k, 2], -(1==f[k, 2]))); };
%o A359467 A359467(n) = ((A166486(n)+A355689(n))%2);
%Y A359467 Characteristic function of A359468, numbers that are either multiples of 4 with their odd part squarefree, or that are not multiples of 4 and not squarefree.
%Y A359467 Cf. A166486,  A355689, A342419, A353627, A358839.
%Y A359467 Differs from A359466 for the first time at n=225, where a(225) = 1, while A359466(225) = 0.
%Y A359467 Differs from A359469 [= A353459(n) mod 2] for the first time at n=100. Here a(100) = 0.
%K A359467 nonn
%O A359467 1
%A A359467 _Antti Karttunen_, Jan 02 2023
```


## Candidate 85: A046951 vs A159631 (score 85.6, agree 124, variant raw, family size 13)
Terms: 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1

### A046951
```
%I A046951 #206 Mar 12 2026 01:51:25
%S A046951 1,1,1,2,1,1,1,2,2,1,1,2,1,1,1,3,1,2,1,2,1,1,1,2,2,1,2,2,1,1,1,3,1,1,
%T A046951 1,4,1,1,1,2,1,1,1,2,2,1,1,3,2,2,1,2,1,2,1,2,1,1,1,2,1,1,2,4,1,1,1,2,
%U A046951 1,1,1,4,1,1,2,2,1,1,1,3,3,1,1,2,1,1,1,2,1,2,1,2,1,1,1,3,1,2,2,4,1,1,1,2,1,1,1,4,1,1,1,3,1,1,1,2,2,1,1,2,2,1,1,2,2
%N A046951 a(n) is the number of squares dividing n.
%C A046951 Rediscovered by the HR automatic theory formation program.
%C A046951 a(n) depends only on prime signature of n (cf. A025487, A046523). So a(24) = a(375) since 24 = 2^3*3 and 375 = 3*5^3 both have prime signature (3, 1).
%C A046951 First differences of A013936. Average value tends towards Pi^2/6 = 1.644934... (A013661, A013679). - _Henry Bottomley_, Aug 16 2001
%C A046951 We have a(n) = A159631(n) for all n < 125, but a(125) = 2 < 3 = A159631(125). - _Steven Finch_, Apr 22 2009
%C A046951 Number of 2-generated Abelian groups of order n, if n > 1. - _Álvar Ibeas_, Dec 22 2014 [In other words, number of order-n abelian groups with rank <= 2. Proof: let b(n) be such number. A finite abelian group is the inner direct product of all Sylow-p subgroups, so {b(n)} is multiplicative. Obviously b(p^e) = floor(e/2)+1 (corresponding to the groups C_(p^r) X C_(p^(e-r)) for 0 <= r <= floor(e/2)), hence b(n) = a(n) for all n. - _Jianing Song_, Nov 05 2022]
%C A046951 Number of ways of writing n = r*s such that r|s. - _Eric M. Schmidt_, Jan 08 2015
%C A046951 The number of divisors of the square root of the largest square dividing n. - _Amiram Eldar_, Jul 07 2020
%C A046951 The number of unordered factorizations of n into cubefree powers of primes (1, primes and squares of primes, A166684). - _Amiram Eldar_, Jun 12 2025
%H A046951 Reinhard Zumkeller, <a href="/A046951/b046951.txt">Table of n, a(n) for n = 1..10000</a>
%H A046951 Antonio Amariti, Claudius Klare, Domenico Orlando and Susanne Reffert, <a href="https://doi.org/10.1016/j.nuclphysb.2015.10.011">The M-theory origin of global properties of gauge theories</a>, Nuclear Physics B, Vol. 901 (2015), pp. 318-337, <a href="https://arxiv.org/abs/1507.04743">arXiv preprint</a>, arXiv:1507.04743 [hep-th], 2015 (see (A.13)).
%H A046951 Simon Colton, <a href="http://www.cs.uwaterloo.ca/journals/JIS/colton/joisol.html">Refactorable Numbers - A Machine Invention</a>, J. Integer Sequences, Vol. 2 (1999), Article 99.1.2.
%H A046951 Simon Colton, <a href="https://web.archive.org/web/20070831060523/http://www.dai.ed.ac.uk/homes/simonco/research/hr">HR - Automatic Theory Formation in Pure Mathematics</a>. [Wayback Machine link]
%H A046951 Ian G. Connell, <a href="https://doi.org/10.4153/CMB-1964-002-1">A number theory problem concerning finite groups and rings</a>, Canad. Math. Bull, 7 (1964), 23-34. See delta(n).
%H A046951 Andrew V. Lelechenko, <a href="https://arxiv.org/abs/1407.1222">Average number of squares dividing mn</a>, arXiv preprint arXiv:1407.1222 [math.NT], 2014.
%H A046951 Werner Georg Nowak and László Tóth, <a href="https://doi.org/10.1142/S179304211350098X">On the average number of subgroups of the group Z_m X Z_n</a>, International Journal of Number Theory, Vol. 10, No. 2 (2014), pp. 363-374, <a href="https://arxiv.org/abs/1307.1414">arXiv preprint</a>, arXiv:1307.1414 [math.NT], 2013.
%H A046951 N. J. A. Sloane, <a href="/transforms.txt">Transforms</a>.
%H A046951 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%F A046951 a(p^k) = A008619(k) = [k/2] + 1. a(A002110(n)) = 1 for all n. (This is true for any squarefree number, A005117). - Original notes clarified by _Antti Karttunen_, Nov 14 2016
%F A046951 a(n) = |{(i, j) : i*j = n AND i|j}| = |{(i, j) : i*j^2 = n}|. Also tau(A000188(n)), where tau = A000005.
%F A046951 Multiplicative with p^e --> floor(e/2) + 1, p prime. - _Reinhard Zumkeller_, May 20 2007
%F A046951 a(A130279(n)) = n and a(m) <> n for m < A130279(n); A008966(n)=0^(a(n) - 1). - _Reinhard Zumkeller_, May 20 2007
%F A046951 Inverse Moebius transform of characteristic function of squares (A010052). Dirichlet g.f.: zeta(s)*zeta(2s).
%F A046951 G.f.: Sum_{k > 0} x^(k^2)/(1 - x^(k^2)). - _Vladeta Jovovic_, Dec 13 2002
%F A046951 a(n) = Sum_{k=1..A000005(n)} A010052(A027750(n,k)). - _Reinhard Zumkeller_, Dec 16 2013
%F A046951 a(n) = Sum_{k = 1..n} ( floor(n/k^2) - floor((n-1)/k^2) ). - _Peter Bala_, Feb 17 2014
%F A046951 From _Antti Karttunen_, Nov 14 2016: (Start)
%F A046951 a(1) = 1; for n > 1, a(n) = A008619(A007814(n)) * a(A064989(n)).
%F A046951 a(n) = A278161(A156552(n)). (End)
%F A046951 G.f.: Sum_{k>0}(theta(q^k)-1)/2, where theta(q)=1+2q+2q^4+2q^9+2q^16+... - _Mamuka Jibladze_, Dec 04 2016
%F A046951 From  _Antti Karttunen_, Nov 12 2017: (Start)
%F A046951 a(n) = A000005(n) - A056595(n).
%F A046951 a(n) = 1 + A071325(n).
%F A046951 a(n) = 1 + A001222(A293515(n)). (End)
%F A046951 L.g.f.: -log(Product_{k>=1} (1 - x^(k^2))^(1/k^2)) = Sum_{n>=1} a(n)*x^n/n. - _Ilya Gutkovskiy_, Jul 30 2018
%F A046951 a(n) = Sum_{d|n} A000005(d) * A008836(n/d). - _Torlach Rush_, Jan 21 2020
%F A046951 a(n) = A000005(sqrt(A008833(n))). - _Amiram Eldar_, Jul 07 2020
%F A046951 a(n) = Sum_{d divides n} mu(core(d)^2), where core(n) = A007913(n). - _Peter Bala_, Jan 24 2024
%F A046951 a(n) = Sum_{d|n} A124315(d) * mu(n/d) (Moebius transform of A124315). - _Amiram Eldar_, Dec 20 2025
%e A046951 a(16) = 3 because the squares 1, 4, and 16 divide 16.
%e A046951 G.f. = x + x^2 + x^3 + 2*x^4 + x^5 + x^6 + x^7 + 2*x^8 + 2*x^9 + x^10 + ...
%p A046951 A046951 := proc(n)
%p A046951     local a,s;
%p A046951     a := 1 ;
%p A046951     for p in ifactors(n)[2] do
%p A046951         a := a*(1+floor(op(2,p)/2)) ;
%p A046951     end do:
%p A046951     a ;
%p A046951 end proc: # _R. J. Mathar_, Sep 17 2012
%p A046951 # Alternative:
%p A046951 isbidivisible := (n, d) -> igcd(n, d) = d and igcd(n/d, d) = d:
%p A046951 a := n -> nops(select(k -> isbidivisible(n, k), [seq(1..n)])): # _Peter Luschny_, Jun 13 2025
%t A046951 a[n_] := Length[ Select[ Divisors[n], IntegerQ[Sqrt[#]]& ] ]; Table[a[n], {n, 1, 105}] (* _Jean-François Alcover_, Jun 26 2012 *)
%t A046951 Table[Length[Intersection[Divisors[n], Range[10]^2]], {n, 100}] (* _Alonso del Arte_, Dec 10 2012 *)
%t A046951 a[ n_] := If[ n < 1, 0, Sum[ Mod[ DivisorSigma[ 0, d], 2], {d, Divisors @ n}]]; (* _Michael Somos_, Jun 13 2014 *)
%t A046951 a[ n_] := If[ n < 2, Boole[ n == 1], Times @@ (Quotient[ #[[2]], 2] + 1 & /@ FactorInteger @ n)]; (* _Michael Somos_, Jun 13 2014 *)
%t A046951 a[ n_] := If[ n < 0, 0, SeriesCoefficient[ Sum[ x^k^2 / (1 - x^k^2), {k, Sqrt @ n}], {x, 0, n}]]; (* _Michael Somos_, Jun 13 2014 *)
%t A046951 f[p_, e_] := 1 + Floor[e/2]; a[1] = 1; a[n_] := Times @@ (f @@@ FactorInteger[n]); Array[a, 100] (* _Amiram Eldar_, Sep 15 2020 *)
%o A046951 (PARI) a(n)=my(f=factor(n));for(i=1,#f[,1],f[i,2]\=2);numdiv(factorback(f)) \\ _Charles R Greathouse IV_, Dec 11 2012
%o A046951 (PARI) a(n) = direuler(p=2, n, 1/((1-X^2)*(1-X)))[n]; \\ _Michel Marcus_, Mar 08 2015
%o A046951 (PARI) a(n)=factorback(apply(e->e\2+1, factor(n)[,2])) \\ _Charles R Greathouse IV_, Sep 17 2015
%o A046951 (Haskell)
%o A046951 a046951 = sum . map a010052 . a027750_row
%o A046951 -- _Reinhard Zumkeller_, Dec 16 2013
%o A046951 (Scheme)
%o A046951 (definec (A046951 n) (if (= 1 n) 1 (* (A008619 (A007814 n)) (A046951 (A064989 n)))))
%o A046951 (define (A008619 n) (+ 1 (/ (- n (modulo n 2)) 2)))
%o A046951 ;; _Antti Karttunen_, Nov 14 2016
%o A046951 (Magma) [#[d: d in Divisors(n)|IsSquare(d)]:n in [1..120]]; // _Marius A. Burtea_, Jan 21 2020
%o A046951 (Python)
%o A046951 from math import prod
%o A046951 from sympy import factorint
%o A046951 def A046951(n): return prod((e>>1)+1 for e in factorint(n).values()) # _Chai Wah Wu_, Aug 04 2024
%o A046951 (Python)
%o A046951 def is_bidivisible(n, d) -> bool: return gcd(n, d) == d and gcd(n//d, d) == d
%o A046951 def aList(n) -> list[int]: return [k for k in range(1, n+1) if is_bidivisible(n, k)]
%o A046951 print([len(aList(n)) for n in range(1, 126)])  # _Peter Luschny_, Jun 13 2025
%Y A046951 Cf. A000005, A000188, A004101, A005117 (positions of 1's), A008619, A008833, A013936 (partial sums), A038538, A046952, A052304, A056595, A159631, A007814, A010052, A027750, A239930, A007862, A046523, A064989, A065704, A124315, A130279, A156552, A166684, A278161, A307445 (Dirichlet inverse).
%Y A046951 One more than A071325.
%Y A046951 Differs from A096309 for the first time at n=32, where a(32) = 3, while A096309(32) = 2 (and also A185102(32) = 2).
%Y A046951 Sum of the k-th powers of the square divisors of n for k=0..10: this sequence (k=0), A035316 (k=1), A351307 (k=2), A351308 (k=3), A351309 (k=4), A351310 (k=5), A351311 (k=6), A351313 (k=7), A351314 (k=8), A351315 (k=9), A351315 (k=10).
%Y A046951 Sequences of the form n^k * Sum_{d^2|n} 1/d^k for k = 0..10: this sequence (k=0), A340774 (k=1), A351600 (k=2), A351601 (k=3), A351602 (k=4), A351603 (k=5), A351604 (k=6), A351605 (k=7), A351606 (k=8), A351607 (k=9), A351608 (k=10).
%Y A046951 Cf. A082293 (a(n)==2), A082294 (a(n)==3).
%K A046951 nice,nonn,mult,easy
%O A046951 1,4
%A A046951 Simon Colton (simonco(AT)cs.york.ac.uk)
%E A046951 Data section filled up to 125 terms and wrong claim deleted from Crossrefs section by _Antti Karttunen_, Nov 14 2016
```
### A159631
```
%I A159631 #22 May 30 2026 16:40:33
%S A159631 1,1,1,2,1,1,1,2,2,1,1,2,1,1,1,3,1,2,1,2,1,1,1,2,2,1,2,2,1,1,1,3,1,1,
%T A159631 1,4,1,1,1,2,1,1,1,2,2,1,1,3,2,2,1,2,1,2,1,2,1,1,1,2,1,1,2,4,1,1,1,2,
%U A159631 1,1,1,4,1,1,2,2,1,1,1,3,3,1,1,2,1,1,1,2,1,2,1,2,1,1,1,3,1,2,2,4,1,1,1,2,1,1,1,4,1,1,1,3,1,1,1,2,2,1,1,2,2,1,1,2,3
%N A159631 Dimension of space of modular forms of weight 1/2, level 4*n and trivial character.
%C A159631 We have a(n) = A046951(n) for all n < 125, but a(125)=3 > 2=A046951(125).
%C A159631 Also, the first nonzero cusp form of weight 1/2 occurs at level 1728.
%H A159631 Antti Karttunen, <a href="/A159631/b159631.txt">Table of n, a(n) for n = 1..1200</a>
%H A159631 H. Cohen and J. Oesterle, <a href="https://doi.org/10.1007/BFb0065297">Dimensions des espaces de formes modulaires</a>, Modular Functions of One Variable. VI, Proc. 1976 Bonn conf., Lect. Notes in Math. 627, Springer-Verlag, 1977, pp. 69-78.
%H A159631 <a href="http://magma.maths.usyd.edu.au/calc/">MAGMA Calculator</a>.
%o A159631 (Magma) [[4*n,Dimension(HalfIntegralWeightForms(4*n,1/2))] : n in [1..125]];
%o A159631 (Magma) function a(n) return Dimension( ModularForms( Gamma0(4*n), 1/2)); end function; /* _Michael Somos_, Jun 13 2014 */
%Y A159631 Cf. A046951.
%K A159631 nonn
%O A159631 1,4
%A A159631 _Steven Finch_, Apr 17 2009
%E A159631 Data section filled up to 125 terms by _Antti Karttunen_, Jul 23 2017
```

