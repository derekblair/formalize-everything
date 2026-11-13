## Candidate 86: A296073 vs A305800 (score 85.6, agree 124, variant raw, family size 63)
Terms: 1, 2, 2, 3, 2, 4, 2, 5, 6, 7, 2, 8, 2, 9, 10, 11, 2, 12, 2, 13, 14, 15, 2, 16, 17, 18, 19, 20, 2, 21

### A296073
```
%I A296073 #30 Jul 20 2025 17:32:47
%S A296073 1,2,2,3,2,4,2,5,6,7,2,8,2,9,10,11,2,12,2,13,14,15,2,16,17,18,19,20,2,
%T A296073 21,2,22,23,24,25,26,2,27,28,29,2,30,2,31,32,33,2,34,35,36,37,38,2,39,
%U A296073 40,41,42,43,2,44,2,45,46,47,48,49,2,50,51,52,2,53,2,54,55,56,57,58,2,59,60,61,2,62,63,64,65,66,2,67,68,69,70,71,72,73,2,74,75,76,2,77,2,78,79,80,2,81,2,82,83,84,2,85,86,87,88,89,90,91,92,93,94,95,33
%N A296073 Filter combining A296071(n) and A296072(n), related to the deficiencies of proper divisors of n.
%C A296073 Construction: Pack the values of A296071(n) and A296072(n) to a single value with any injective N x N -> N packing function, like for example as f(n) = (1/2)*(2 + ((A296071(n)+A296072(n))^2) - A296071(n) - 3*A296072(n)) (the packing function here is the two-argument form of A000027). Then apply the restricted growth sequence transform to the sequence f(1), f(2), f(3), ... The transform assigns a unique increasing number for each newly encountered term of the sequence, and for any subsequent occurrences of the same term it gives the same number that term obtained for the first time.
%C A296073 For all i, j: a(i) = a(j) => A296074(i) = A296074(j).
%C A296073 Note that this is NOT restricted growth transform of A239968, which is A305800. Apart from 2's that occur at every prime, there are other duplicates also, first at a(125) = a(46) = 33.
%H A296073 Antti Karttunen, <a href="/A296073/b296073.txt">Table of n, a(n) for n = 1..65536</a>
%e A296073 To see that a(46) and a(125) have the same value (33), consider the proper divisors of 46 = 1, 2, 23 and of 125 = 1, 5, 25. Their deficiencies are 1, 1, 22 and 1, 4, 19 respectively. When we look at their balanced ternary representations [as here all elements are positive, it can be obtained as A007089(A117967(n)) with 2's standing for -1's]:
%e A296073    1 =    1
%e A296073    1 =    1
%e A296073   22 = 1211 (as 22 = 1*(3^3) + -1*(3^2) + 1*(3^1) + 1*(3^0))
%e A296073 and
%e A296073    1 =    1
%e A296073    4 =   11
%e A296073   19 = 1201 (as 19 = 1*(3^3) + -1*(3^2) + 0*(3^1) + 1*(3^0)).
%e A296073 we see that in each column there is an equal number of 1's and an equal number of 2's. Moreover, this then implies also that the sums of those two sequences of deficiencies {1, 1, 22} and {1, 4, 19} are equal, as A296074(n) is a function of (can be computed from) a(n).
%o A296073 (PARI)
%o A296073 up_to = 65536;
%o A296073 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A296073 write_to_bfile(start_offset,vec,bfilename) = { for(n=1, length(vec), write(bfilename, (n+start_offset)-1, " ", vec[n])); }
%o A296073 A019565(n) = {my(j,v); factorback(Mat(vector(if(n, #n=vecextract(binary(n), "-1..1")), j, [prime(j), n[j]])~))}; \\ This function from _M. F. Hasler_
%o A296073 A117967(n) = if(n<=1,n,if(!(n%3),3*A117967(n/3),if(1==(n%3),1+3*A117967((n-1)/3),2+3*A117967((n+1)/3))));
%o A296073 A117968(n) = if(1==n,2,if(!(n%3),3*A117968(n/3),if(1==(n%3),2+3*A117968((n-1)/3),1+3*A117968((n+1)/3))));
%o A296073 A289813(n) = { my (d=digits(n, 3)); from digits(vector(#d, i, if (d[i]==1, 1, 0)), 2); } \\ From _Rémy Sigrist_
%o A296073 A289814(n) = { my (d=digits(n, 3)); from digits(vector(#d, i, if (d[i]==2, 1, 0)), 2); } \\ From _Rémy Sigrist_
%o A296073 A295882(n) = { my(x = (2*n)-sigma(n)); if(x >= 0,A117967(x),A117968(-x)); };
%o A296073 A296071(n) = { my(m=1); fordiv(n,d,if(d < n,m *= A019565(A289813(A295882(d))))); m; };
%o A296073 A296072(n) = { my(m=1); fordiv(n,d,if(d < n,m *= A019565(A289814(A295882(d))))); m; };
%o A296073 Anotsubmitted3(n) = (1/2)*(2 + ((A296071(n)+A296072(n))^2) - A296071(n) - 3*A296072(n));
%o A296073 write_to_bfile(1,rgs_transform(vector(up_to,n,Anotsubmitted3(n))),"b296073.txt");
%Y A296073 Cf. A019565, A033879, A117967, A117968, A295882, A296071, A296072, A296074.
%Y A296073 Cf. also A293226.
%Y A296073 Differs from A305800 for the first time at n=125.
%K A296073 nonn
%O A296073 1,2
%A A296073 _Antti Karttunen_, Dec 04 2017
%E A296073 Data section extended up to a(125) by _Antti Karttunen_, Jun 14 2018
```
### A305800
```
%I A305800 #30 Jul 12 2019 14:07:10
%S A305800 1,2,2,3,2,4,2,5,6,7,2,8,2,9,10,11,2,12,2,13,14,15,2,16,17,18,19,20,2,
%T A305800 21,2,22,23,24,25,26,2,27,28,29,2,30,2,31,32,33,2,34,35,36,37,38,2,39,
%U A305800 40,41,42,43,2,44,2,45,46,47,48,49,2,50,51,52,2,53,2,54,55,56,57,58,2,59,60,61,2,62,63,64,65,66,2,67,68,69,70,71,72,73,2,74,75,76,2,77,2,78,79,80,2,81,2,82,83,84,2,85,86,87,88,89,90,91,92,93,94,95,96
%N A305800 Filter sequence for a(prime) = constant sequences.
%C A305800 Restricted growth sequence transform of A239968.
%C A305800 In the following, A stands for this sequence, A305800, and S -> T (where S and T are sequence A-numbers) indicates that for all i, j: S(i) = S(i) => T(i) = T(j).
%C A305800 For example, the following implications hold:
%C A305800   A -> A300247 -> A305897 -> A077462 -> A101296,
%C A305800   A -> A290110 -> A300250 -> A101296.
%H A305800 Antti Karttunen, <a href="/A305800/b305800.txt">Table of n, a(n) for n = 1..100000</a>
%F A305800 a(1) = 1; for n > 1, a(n) = 2 for prime n, and a(n) = 1+n-A000720(n) for composite n.
%t A305800 Join[{1},Table[If[PrimeQ[n],2,1+n-PrimePi[n]],{n,2,150}]] (* _Harvey P. Dale_, Jul 12 2019 *)
%o A305800 (PARI) A305800(n) = if(1==n,n,if(isprime(n),2,1+n-primepi(n)));
%Y A305800 Cf. A000720, A239968.
%Y A305800 Differs from A296073 for the first time at n=125, as a(125) = 96, while A296073(125) = 33.
%Y A305800 Cf. also A305900, A305801, A295300, A289626 for other "upper level" filters.
%K A305800 nonn
%O A305800 1,2
%A A305800 _Antti Karttunen_, Jun 14 2018
```


## Candidate 87: A321538 vs A321803 (score 85.6, agree 124, variant raw, family size 3)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0

### A321538
```
%I A321538 #16 Dec 16 2018 20:28:02
%S A321538 0,0,0,0,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,
%T A321538 33,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,55,0,0,0,0,0,0,0,0,0,0,
%U A321538 66,0,0,0,0,0,0,0,0,0,0,77,0,0,0,0,0,0,0,0,0,0,88,0,0,0,0,0,0,0,0,0,0,99,0,0,0,0,0,0,0,0,0,0,11,111,11,11,11,11,11,11,11,11,0,0,22,0
%N A321538 a(n) = A321536(A321537(n)).
%C A321538 More than the usual number of terms are shown in order to reach some interesting terms.
%C A321538 Fixed points correspond to 0 alongside A033023. - _Rémy Sigrist_, Nov 16 2018
%H A321538 Rémy Sigrist, <a href="/A321538/b321538.txt">Table of n, a(n) for n = 0..10000</a>
%F A321538 Delete a digit A in n if it either forms a run of length 1 or begins a substring AwAA, where w consists of runs of length 1. - _Charlie Neder_, Dec 16 2018
%Y A321538 Cf. A033023, A321536, A321537.
%Y A321538 A base-10 analog of A318925.
%K A321538 nonn,base,look
%O A321538 0,12
%A A321538 _N. J. A. Sloane_, Nov 13 2018
```
### A321803
```
%I A321803 #20 Dec 02 2018 15:06:51
%S A321803 0,0,0,0,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,0,0,0,
%T A321803 33,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,55,0,0,0,0,0,0,0,0,0,0,
%U A321803 66,0,0,0,0,0,0,0,0,0,0,77,0,0,0,0,0,0,0,0,0,0,88,0,0,0,0,0,0,0,0,0,0,99,0,0,0,0,0,0,0,0,0,0,11,111,11,11,11,11,11,11,11,11,0,0,22,0,0,0,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,55,0,0,0,0,0,0,0,0,0,0,66,0,0,0,0,0,0,0,0,0,0,77,0,0,0,0,0,0,0,0,0,0,88,0,0,0,0,0,0,0,0,0,0,99
%N A321803 Keep only consecutive identical decimal digits of n; write 0 if all digits disappear.
%C A321803 Consecutive identical digits of n are kept. Leading zeros are erased unless the result is 0. If all digits are erased, we write 0 for the result (A321804 is another version, which uses -1 for the empty string).
%C A321803 More than the usual number of terms are shown in order to reach some interesting examples. Agrees with A321797 for n < 121.
%C A321803 Differs from A321538 for the first time at n = 11011. - _Chai Wah Wu_, Nov 29 2018
%e A321803 123321 becomes 33, 1123 becomes 11, 112331 becomes 1133, and 100223 becomes 22 (as we don't accept leading zeros). Note that 12321 disappears immediately and we get 0.
%t A321803 Array[FromDigits[Join @@ Select[Split@ IntegerDigits@ #, Length@ # >= 2 &] /. {} -> {0}] &, 200, 0] (* _Michael De Vlieger_, Nov 20 2018 *)
%o A321803 (Python)
%o A321803 from re import split
%o A321803 def A321803(n):
%o A321803     return int('0'+''.join(d if len(d) != 1 else '' for d in split('(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)',str(n)) if d != '' and d != None))
%Y A321803 Cf. A320486, A321800, A321797, A321538.
%K A321803 nonn,base
%O A321803 0,12
%A A321803 _Chai Wah Wu_, Nov 19 2018
```


## Candidate 88: A373491 vs A373588 (score 85.6, agree 124, variant drop1, family size 3)
Terms: 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A373491
```
%I A373491 #7 Jun 10 2024 14:56:07
%S A373491 1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A373491 0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,
%U A373491 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1
%N A373491 a(n) = 1 if A059975(n) and A083345(n) are both multiples of 3, otherwise 0, where A059975 is fully additive with a(p) = p-1, and A083345 is the numerator of the fully additive function with a(p) = 1/p.
%H A373491 Antti Karttunen, <a href="/A373491/b373491.txt">Table of n, a(n) for n = 1..100000</a>
%H A373491 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A373491 a(n) = [A373377(n) == 0 (mod 3)], where [ ] is the Iverson bracket.
%F A373491 a(n) <= A373493(n).
%o A373491 (PARI)
%o A373491 A059975(n) = {my(f = factor(n)); sum(i = 1, #f~, f[i, 2]*(f[i, 1] - 1)); };
%o A373491 A083345(n) = { my(f=factor(n)); numerator(vecsum(vector(#f~, i, f[i, 2]/f[i, 1]))); };
%o A373491 A373491(n) = (!(A059975(n)%3) && !(A083345(n)%3));
%Y A373491 Characteristic function of A373492.
%Y A373491 Cf. A059975, A083345, A373377, A373493.
%K A373491 nonn
%O A373491 1
%A A373491 _Antti Karttunen_, Jun 10 2024
```
### A373588
```
%I A373588 #7 Jun 10 2024 17:44:40
%S A373588 1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A373588 0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,
%U A373588 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1
%N A373588 a(n) = 1 if the number of prime factors (with multiplicity) of n is a multiple of 3, and all of them are of the type 3m-1 (in A003627), otherwise 0.
%H A373588 Antti Karttunen, <a href="/A373588/b373588.txt">Table of n, a(n) for n = 1..100000</a>
%H A373588 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%o A373588 (PARI) A373588(n) = if(bigomega(n)%3, 0, my(f = factor(n)); for(i = 1, #f~, if((f[i, 1]%3) != 2, return(0))); (1));
%Y A373588 Characteristic function of A373589.
%Y A373588 Cf. A001222, A003627, A004612, A145784.
%Y A373588 Differs from A373491 for the first time at n=343, where a(343) = 0, while A373491(343) = 1.
%K A373588 nonn
%O A373588 1
%A A373588 _Antti Karttunen_, Jun 10 2024
```


## Candidate 89: A374134 vs A374136 (score 85.6, agree 124, variant drop1, family size 4)
Terms: 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0

### A374134
```
%I A374134 #25 Oct 28 2024 04:51:32
%S A374134 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,
%T A374134 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,
%U A374134 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1
%N A374134 a(n) = 1 if 2*phi(n) > n, otherwise 0, where phi is Euler's totient function phi, A000010.
%H A374134 Antti Karttunen, <a href="/A374134/b374134.txt">Table of n, a(n) for n = 1..100000</a>
%H A374134 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A374134 a(n) = [A083254(n) > 0], where [ ] is the Iverson bracket.
%F A374134 a(2*k) = 0 for k >= 1. - _Paolo Xausa_, Jul 08 2024
%t A374134 Array[Boole[2*EulerPhi[#] > #] &, 100] (* _Paolo Xausa_, Jul 08 2024 *)
%o A374134 (PARI) A374134(n) = ((2*eulerphi(n))>n);
%o A374134 (Python)
%o A374134 from sympy import totient
%o A374134 def A374134(n): return int(totient(n)<<1>n) # _Chai Wah Wu_, Oct 27 2024
%Y A374134 Characteristic function of A089684.
%Y A374134 Cf. A000010, A083254, A318874 (inverse Möbius transform), A323170.
%Y A374134 Differs from A000035 first at n=105, where a(105) = 0, while A000035(105) = 1.
%Y A374134 Differs from A374136 first at n=255, where a(255) = 1, while A374136(255) = 0.
%K A374134 nonn
%O A374134 1
%A A374134 _Antti Karttunen_, Jul 06 2024
```
### A374136
```
%I A374136 #9 Jul 07 2024 08:02:02
%S A374136 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,
%T A374136 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,
%U A374136 1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1
%N A374136 a(n) = 1 if n is odd and the cyclotomic polynomial Phi(k,x) has height 1, i.e., is flat, otherwise 0. Here flat means that the coefficients of a polynomial are all -1, 0, or 1.
%H A374136 Antti Karttunen, <a href="/A374136/b374136.txt">Table of n, a(n) for n = 1..100000</a>
%H A374136 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%o A374136 (PARI) A374136(n) = (n%2 && 1==vecmax(abs(Vec(polcyclo(n)))));
%Y A374136 Characteristic function of A374137.
%Y A374136 Differs from A000035 first at n=105, where a(105) = 0, while A000035(105) = 1.
%Y A374136 Differs from A374134 first at n=255, where a(255) = 0, while A374134(255) = 1.
%K A374136 nonn
%O A374136 1
%A A374136 _Antti Karttunen_, Jul 06 2024
```


## Candidate 90: A335324 vs A366245 (score 85.0, agree 85, variant raw, family size 2)
Terms: 1, 1, 1, 4, 1, 1, 1, 4, 9, 1, 1, 4, 1, 1, 1, 1, 1, 9, 1, 4, 1, 1, 1, 4, 25, 1, 9, 4, 1, 1

### A335324
```
%I A335324 #25 Feb 16 2025 08:34:00
%S A335324 1,1,1,4,1,1,1,4,9,1,1,4,1,1,1,1,1,9,1,4,1,1,1,4,25,1,9,4,1,1,1,1,1,1,
%T A335324 1,36,1,1,1,4,1,1,1,4,9,1,1,1,49,25,1,4,1,9,1,4,1,1,1,4,1,1,9,4,1,1,1,
%U A335324 4,1,1,1,36,1,1,25,4,1,1,1,1,1,1,1,4,1
%N A335324 Square part of 4th-power-free part of n.
%C A335324 Equivalently, biquadratefree (4th-power-free) part of square part of n.
%C A335324 Multiplicative. The terms are squares of squarefree numbers (A062503).
%C A335324 Every positive integer n is the product of a unique subset S_n of the terms of A050376 (sometimes called Fermi-Dirac primes). a(n) is the product of the members of S_n that are squares of prime numbers (A001248).
%H A335324 Michel Marcus, <a href="/A335324/b335324.txt">Table of n, a(n) for n = 1..10000</a>
%H A335324 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/Biquadratefree.html">Biquadratefree</a>.
%H A335324 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/SquarePart.html">Square part</a>.
%F A335324 a(n) = A053165(A008833(n)) = A008833(A053165(n)).
%F A335324 a(n) = A053165(n) / A007913(n).
%F A335324 a(n) = A008833(n) / A008835(n).
%F A335324 n = A007913(n) * a(n) * A008835(n).
%F A335324 a(n) = A225546(A038500(A225546(n))).
%F A335324 a(n^2) = A007913(n)^2.
%F A335324 a(A003961(n)) = A003961(a(n)).
%F A335324 a(A331590(n, k)) = A331590(a(n), a(k)).
%F A335324 a(p^e) = p^(2*floor(e/2) - 4*floor(e/4)). - _Amiram Eldar_, Jun 01 2020
%F A335324 From _Amiram Eldar_, Sep 21 2023: (Start)
%F A335324 Dirichlet g.f.: zeta(s) * zeta(2*s-2) * zeta(4*s)/(zeta(2*s) * zeta(4*s-4)).
%F A335324 Sum_{k=1..n} a(k) ~ (4*zeta(3/2)*zeta(4))/(21*zeta(3)) * n^(3/2). (End)
%e A335324 Removing the 4th powers from 192 = 2^6 * 3^1 gives 2^(6 - 4) * 3^1 = 2^2 * 3 = 12. So the 4th-power-free part of 192 is 12. The square part of 12 (largest square dividing 12) is 4. So a(192) = 4.
%t A335324 f[p_, e_] := p^(2*Floor[e/2] - 4*Floor[e/4]); a[n_] := Times @@ (f @@@ FactorInteger[n]); Array[a, 100] (* _Amiram Eldar_, Jun 01 2020 *)
%o A335324 (PARI) A053165(n)=my(f=factor(n)); f[, 2]=f[, 2]%4; factorback(f);
%o A335324 a(n) = my(m=A053165(n)); m/core(m); \\ _Michel Marcus_, Jun 01 2020
%o A335324 (Python)
%o A335324 from math import prod
%o A335324 from sympy import factorint
%o A335324 def A335324(n): return prod(p**(e&2) for p, e in factorint(n).items()) # _Chai Wah Wu_, Aug 07 2024
%Y A335324 A007913, A008833, A008835, A053165 are used in formulas defining the sequence.
%Y A335324 Column 1 of A352780.
%Y A335324 Range of values is A062503.
%Y A335324 Positions of 1's: A252895.
%Y A335324 Related to A038500 by A225546.
%Y A335324 The formula section details how the sequence maps the terms of A003961, A331590.
%Y A335324 Cf. A001248, A050376, A083730.
%Y A335324 Cf. A002117, A013662, A078434.
%K A335324 nonn,easy,mult
%O A335324 1,4
%A A335324 _Peter Munn_, May 31 2020
```
### A366245
```
%I A366245 #13 Jan 09 2025 15:44:26
%S A366245 1,1,1,4,1,1,1,4,9,1,1,4,1,1,1,1,1,9,1,4,1,1,1,4,25,1,9,4,1,1,1,1,1,1,
%T A366245 1,36,1,1,1,4,1,1,1,4,9,1,1,1,49,25,1,4,1,9,1,4,1,1,1,4,1,1,9,4,1,1,1,
%U A366245 4,1,1,1,36,1,1,25,4,1,1,1,1,1,1,1,4,1
%N A366245 The largest infinitary divisor of n that is a term of A366243.
%C A366245 First differs from A335324 at n = 256.
%H A366245 Amiram Eldar, <a href="/A366245/b366245.txt">Table of n, a(n) for n = 1..10000</a>
%F A366245 Multiplicative with a(p^e) = p^A063695(e).
%F A366245 a(n) = n / A366244(n).
%F A366245 a(n) >= 1, with equality if and only if n is a term of A366242.
%F A366245 a(n) <= n, with equality if and only if n is a term of A366243.
%F A366245 From _Peter Munn_, Jan 09 2025: (Start)
%F A366245 a(n) = max({k in A366243 : A059895(k, n) = k}).
%F A366245 a(n) = Product_{k >= 0} A352780(n, 2k+1).
%F A366245 Also defined by:
%F A366245 - for n in A046100, a(n) = A008833(n);
%F A366245 - a(n^4) = (a(n))^4;
%F A366245 - a(A059896(n,k)) = A059896(a(n), a(k)).
%F A366245 Other identities:
%F A366245 a(n) = sqrt(A366244(n^2)).
%F A366245 a(A059897(n,k)) = A059897(a(n), a(k)).
%F A366245 a(A225546(n)) = A225546(A248101(n)).
%F A366245 (End)
%t A366245 f[p_, e_] := p^BitAnd[e, Sum[2^k, {k, 1, Floor@ Log2[e], 2}]]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100]
%o A366245 (PARI) s(e) = -sum(k = 1, e, (-2)^k*floor(e/2^k));
%o A366245 a(n) = {my(f = factor(n)); prod(i = 1, #f~, f[i,1]^s(f[i,2]));}
%Y A366245 Cf. A063695, A335324, A366242, A366243, A366244.
%Y A366245 See the formula section for the relationships with A008833, A046100, A059895, A059896, A059897, A225546, A248101, A352780.
%K A366245 nonn,easy,mult
%O A366245 1,4
%A A366245 _Amiram Eldar_, Oct 05 2023
```


## Candidate 91: A359162 vs A360111 (score 84.2, agree 122, variant drop1, family size 4)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A359162
```
%I A359162 #16 Dec 17 2022 22:53:46
%S A359162 0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A359162 1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,
%U A359162 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1
%N A359162 a(n) = 1 if n is a number of the form 4u+3 with an even number of prime factors (counted with multiplicity), otherwise 0.
%H A359162 Antti Karttunen, <a href="/A359162/b359162.txt">Table of n, a(n) for n = 1..100000</a>
%H A359162 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A359162 a(n) = A065043(n) * A121262(1+n).
%F A359162 a(n) = A353557(n) - A359160(n).
%F A359162 a(n) = A121262(1+n) - A359152(n).
%F A359162 a(n) >= A353479(n).
%e A359162 135 = 3 * 3 * 3 * 5 has an even number of prime factors and is of the form 4u+3, therefore a(135) = 1.
%o A359162 (PARI) A359162(n) = (!(bigomega(n)%2)&&(3==(n%4)));
%Y A359162 Characteristic function of A359163.
%Y A359162 Cf. A065043, A121262, A353557, A359152, A359160.
%Y A359162 Differs from A353479 for the first time at n=135, where a(135) = 1, while A353479(135) = 0.
%K A359162 nonn
%O A359162 1
%A A359162 _Antti Karttunen_, Dec 17 2022
```
### A360111
```
%I A360111 #42 Feb 07 2024 20:39:10
%S A360111 0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A360111 1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,
%U A360111 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1
%N A360111 a(n) = 1 if there is no prime p such that p^p divides n, but for the arithmetic derivative of n such a prime exists, otherwise a(n) = 0; a(1) = 0 by convention.
%C A360111 Question: What is the asymptotic mean of this and sequences like A341996 and its complement A368915, and related A368916? - _Antti Karttunen_, Jan 11 2024
%C A360111 Question: Is the asymptotic mean of this sequence 1 - Product_{p prime} (1 - 1/p^(1+p)) = 0.13585792767780221591...? (I.e. complementary to that of A368916). But see also A368911. - _Antti Karttunen_, Jan 29 2024
%H A360111 Antti Karttunen, <a href="/A360111/b360111.txt">Table of n, a(n) for n = 1..100000</a>
%H A360111 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A360111 a(n) = A359550(n) * A341996(n).
%F A360111 a(n) = [-1 == A256750(n)], where [ ] is the Iverson bracket.
%F A360111 For n > 1, a(n) = A359550(n) - A368915(n). - _Antti Karttunen_, Jan 11 2024
%e A360111 a(12) = 0, because for both 12 and 12' = A003415(12) = 16 there is a prime p (in both cases p=2) such that p^p divides them.
%e A360111 a(15) = 1, because 15 = 3*5 has no such prime divisor p that p^p would divide it, while 15' = 8 is divisible by 2^2.
%t A360111 d[0] = d[1] = 0; d[n_] := n * Plus @@ ((Last[#]/First[#]) & /@ FactorInteger[n]); q[n_] := AllTrue[FactorInteger[n], Last[#] < First[#] &]; q[1] = True; a[1] = 0; a[n_] := If[q[n] && ! q[d[n]], 1, 0]; Array[a, 100] (* _Amiram Eldar_, Jan 31 2023 *)
%o A360111 (PARI)
%o A360111 A003415(n) = if(n<=1, 0, my(f=factor(n)); n*sum(i=1, #f~, f[i, 2]/f[i, 1]));
%o A360111 A359550(n) = { my(f = factor(n)); prod(k=1, #f~, (f[k, 2]<f[k, 1])); };
%o A360111 A360111(n) = ((n>1)&&A359550(n)&&!A359550(A003415(n)));
%Y A360111 Cf. A003415, A256750, A341996, A359550, A368911, A368915, A368916.
%Y A360111 Characteristic function of A327934.
%Y A360111 After n=1 differs from A360109 for the next time at n=81, where a(81) = 0, while A360109(81) = 1.
%Y A360111 Differs from A353479 for the first time at n=158, where a(158) = 1, while A353479(158) = 1.
%K A360111 nonn
%O A360111 1
%A A360111 _Antti Karttunen_, Jan 31 2023
```


## Candidate 92: A319707 vs A319717 (score 83.5, agree 121, variant raw, family size 6)
Terms: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 5, 11, 7, 12, 13, 14, 5, 15, 7, 16, 17, 18, 5, 19, 20, 21, 22, 23, 5, 24

### A319707
```
%I A319707 #8 Oct 05 2018 11:10:26
%S A319707 1,2,3,4,5,6,7,8,9,10,5,11,7,12,13,14,5,15,7,16,17,18,5,19,20,21,22,
%T A319707 23,5,24,7,25,26,27,28,29,7,30,31,32,5,33,7,34,35,36,5,37,38,39,40,41,
%U A319707 5,42,43,44,45,46,5,47,7,48,49,50,51,52,7,53,54,55,5,56,7,57,58,59,60,61,7,62,63,64,5,65,66,67,68,69,5,70,71,72,73,74,75,76,7,77,78,79,5,80,7,81,82,83,5,84,7,85,86,87,5,88,89,90,91,92,93,94,95
%N A319707 Filter sequence which records for primes their residue modulo 6, and for all other numbers assigns a unique number.
%C A319707 Restricted growth sequence transform of function f defined as f(n) = A010875(n) when n is a prime, otherwise -n.
%C A319707 Primes of the form 6k+5 (A007528) get value 5, and the primes of the form 6k+1 (A002476) get value 7, while for all other n, a(n) is assigned to a unique running count.
%C A319707 For all i, j:
%C A319707   a(i) = a(j) => A010875(i) = A010875(j),
%C A319707   a(i) = a(j) => A305900(i) = A305900(j),
%C A319707   a(i) = a(j) => A319717(i) = A319717(j) => A319716(i) = A319716(j).
%H A319707 Antti Karttunen, <a href="/A319707/b319707.txt">Table of n, a(n) for n = 1..100000</a>
%o A319707 (PARI)
%o A319707 up_to = 100000;
%o A319707 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A319707 A319707aux(n) = if(isprime(n),(n%6),-n);
%o A319707 v319707 = rgs_transform(vector(up_to,n,A319707aux(n)));
%o A319707 A319707(n) = v319707[n];
%Y A319707 Cf. A319716, A319717.
%Y A319707 Cf. A007528 (positions of 5's), A002476 (positions of 7's).
%Y A319707 Cf. also A319704.
%Y A319707 Differs from A319716 for the first time at n=121.
%K A319707 nonn
%O A319707 1,2
%A A319707 _Antti Karttunen_, Oct 04 2018
```
### A319717
```
%I A319717 #34 Jul 15 2022 06:48:00
%S A319717 1,2,3,4,5,6,7,8,9,10,5,11,7,12,13,14,5,15,7,16,17,18,5,19,20,21,22,
%T A319717 23,5,24,7,25,26,27,28,29,7,30,31,32,5,33,7,34,35,36,5,37,38,39,40,41,
%U A319717 5,42,43,44,45,46,5,47,7,48,49,50,51,52,7,53,54,55,5,56,7,57,58,59,60,61,7,62,63,64,5,65,66,67,68,69,5,70,71,72,73,74,75,76,7,77,78,79,5,80,7,81,82,83,5,84,7,85,86,87,5,88,89,90,91,92,93,94,95
%N A319717 Filter sequence combining the largest proper divisor of n (A032742) with modulo 6 residue of the smallest prime factor, A010875(A020639(n)), and a single bit A319710(n) telling whether the smallest prime factor is unitary.
%C A319717 Restricted growth sequence transform of triple [A010875(A020639(n)), A032742(n), A319710(n)] (with a separate value allotted for a(1)), or equally, of ordered pair [A319716(n), A319710(n)].
%C A319717 In addition to A319716, this filter sequence also records in the value of a(n) also the fact whether the smallest prime factor of n is unitary or not. This information is enough to determine the modulo 6 residues of all the divisors of n, thus sequences like A002324 are essentially functions of this sequence. Moreover, a lot of other information is immediately (and unavoidably) present, for example the exact prime signature of n, including also the relative order of exponents.
%C A319717 Any such filtering sequence can be perceived also in terms of what information it leaves out from a(n) that would be needed to reconstruct whole n from each a(n). If the whole n could be reconstructed from a(n) each time, then sequence a would be injective, and would be useless for filtering, because then it would match with any sequence. In this filter, what is left out is only the exact identity of the smallest prime factor, although its residue class mod 6 is retained. However, when the smallest prime factor is 2 or 3, this can be seen from that residue value, so for any number x in A047229, both A020639(x) and A032742(x) are known, and as x = A020639(x)*A032742(x), it means such numbers must occur in their own singleton equivalence classes.
%C A319717 Likewise, for any n in A283050, even if not divisible by 2 or 3, when we have A319710(n) stored in the triple as 1, this immediately gives away the exact identity of the smallest prime factor, which is equal to A014673(n) = A020639(A032742(n)) in these cases.
%C A319717 Thus there is a substantial subset of N (containing at least the union of A047229 and A283050) which is actually in the "blind sector" of this filter, "where anything goes", as this sequence obtains only unique values in that subdomain.
%C A319717 There is a related filter sequence A319996, which operates by "cleaving n from its high end" (by storing the residue class of the largest prime factor, A006530, instead of the smallest, together with n/A006530(n)), which has its own blind spots, but fortunately, they do not fully coincide with the blind spots of this filter. Naturally, any sequence like A002324 should match both to this sequence and A319996.
%C A319717 For all i, j:
%C A319717   a(i) = a(j) => A002324(i) = A002324(j),
%C A319717   a(i) = a(j) => A067029(i) = A067029(j),
%C A319717   a(i) = a(j) => A071178(i) = A071178(j),
%C A319717   a(i) = a(j) => A077462(i) = A077462(j) => A101296(i) = A101296(j),
%C A319717   a(i) = a(j) => A319716(i) = A319716(j) => A319690(i) = A319690(j).
%H A319717 Antti Karttunen, <a href="/A319717/b319717.txt">Table of n, a(n) for n = 1..100000</a>
%e A319717 For n = 65 = 5*13 and 143 = 11*13, the smallest prime factor is of the form 6k+5,  doesn't occur more than once in the factorization, and the largest proper divisor is the same number (13) in both cases, thus a(65) = a(143) (= 51, a running count value allotted by rgs-transform for this equivalence class).
%e A319717 For n = 1805 (5*19^2), 3971 (11*19^2), 6137 (17*19^2), it's like above, but the largest proper divisor is in all three cases 361 = 19^2, thus a(1805) = a(3971) = a(6137) (= 1405).
%e A319717 Note that such nontrivial equivalence classes may only contain numbers that are 5-rough, A007310, with no prime factors 2 or 3, and also, they may not contain numbers from A283050. See the comments section.
%o A319717 (PARI)
%o A319717 up_to = 100000;
%o A319717 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A319717 A032742(n) = if(1==n,n,n/vecmin(factor(n)[,1]));
%o A319717 A286476(n) = if(1==n,n,(6*A032742(n) + (n % 6)));
%o A319717 A319710(n) = ((n>1)&&(factor(n)[1,2]>1));
%o A319717 v319717 = rgs_transform(vector(up_to,n,[A286476(n),A319710(n)]));
%o A319717 A319717(n) = v319717[n];
%Y A319717 Cf. A101296, A319707, A319716, A319996.
%Y A319717 Cf. also A320004 (analogous sequence for modulo 4 residues).
%Y A319717 Differs from A319707 for the first time at n=143, where a(143) = 51, differs from A319716 for the first time at n=121, where a(121) = 95.
%K A319717 nonn
%O A319717 1,2
%A A319717 _Antti Karttunen_, Oct 04 2018
```


## Candidate 93: A072411 vs A290107 (score 82.8, agree 120, variant raw, family size 51)
Terms: 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1

### A072411
```
%I A072411 #63 Sep 11 2025 18:13:42
%S A072411 1,1,1,2,1,1,1,3,2,1,1,2,1,1,1,4,1,2,1,2,1,1,1,3,2,1,3,2,1,1,1,5,1,1,
%T A072411 1,2,1,1,1,3,1,1,1,2,2,1,1,4,2,2,1,2,1,3,1,3,1,1,1,2,1,1,2,6,1,1,1,2,
%U A072411 1,1,1,6,1,1,2,2,1,1,1,4,4,1,1,2,1,1,1,3,1,2,1,2,1,1,1,5,1,2,2,2,1,1,1,3,1,1,1,6,1,1,1,4,1,1,1,2,2,1,1,3
%N A072411 LCM of exponents in prime factorization of n, a(1) = 1.
%C A072411 The sums of the first 10^k terms, for k = 1, 2, ..., are 14, 168, 1779, 17959, 180665, 1808044, 18084622, 180856637, 1808585068, 18085891506, ... . Apparently, the asymptotic mean of this sequence is limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = 1.8085... . - _Amiram Eldar_, Sep 10 2022
%H A072411 Antti Karttunen, <a href="/A072411/b072411.txt">Table of n, a(n) for n = 1..10080</a>
%H A072411 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%H A072411 <a href="/index/Lc#lcm">Index entries for sequences related to lcm's</a>.
%F A072411 a(1) = 1; for n > 1, a(n) = lcm(A067029(n), a(A028234(n))). - _Antti Karttunen_, Aug 09 2016
%F A072411 From _Antti Karttunen_, Aug 22 2017: (Start)
%F A072411 a(n) = A284569(A156552(n)).
%F A072411 a(n) = A290103(A181819(n)).
%F A072411 a(A289625(n)) = A002322(n).
%F A072411 a(A290095(n)) = A055092(n).
%F A072411 a(A275725(n)) = A060131(n).
%F A072411 a(A260443(n)) = A277326(n).
%F A072411 a(A283477(n)) = A284002(n). (End)
%e A072411 n = 288 = 2*2*2*2*2*3*3; lcm(5,2) = 10; Product(5,2) = 10, max(5,2) = 5;
%e A072411 n = 180 = 2*2*3*3*5; lcm(2,2,1) = 2; Product(2,2,1) = 4; max(2,2,1) = 2; it deviates both from maximum of exponents (A051903, for the first time at n=72), and product of exponents (A005361, for the first time at n=36).
%e A072411 For n = 36 = 2*2*3*3 = 2^2 * 3^2 we have a(36) = lcm(2,2) = 2.
%e A072411 For n = 72 = 2*2*2*3*3 = 2^3 * 3^2 we have a(72) = lcm(2,3) = 6.
%e A072411 For n = 144 = 2^4 * 3^2 we have a(144) = lcm(2,4) = 4.
%e A072411 For n = 360 = 2^3 * 3^2 * 5^1 we have a(360) = lcm(1,2,3) = 6.
%t A072411 Table[LCM @@ Last /@ FactorInteger[n], {n, 2, 100}] (* _Ray Chandler_, Jan 24 2006 *)
%o A072411 (Scheme) ;; With memoization-macro definec.
%o A072411 (definec (A072411 n) (if (= 1 n) 1 (lcm (A067029 n) (A072411 (A028234 n))))) ;; _Antti Karttunen_, Aug 09 2016
%o A072411 (Python)
%o A072411 from sympy import lcm, factorint
%o A072411 def a(n):
%o A072411     l=[]
%o A072411     f=factorint(n)
%o A072411     for i in f: l+=[f[i],]
%o A072411     return lcm(l)
%o A072411 print([a(n) for n in range(1, 151)]) # _Indranil Ghosh_, Mar 25 2017
%o A072411 (PARI) a(n) = lcm(factor(n)[,2]); \\ _Michel Marcus_, Mar 25 2017
%Y A072411 Cf. A028234, A067029, A072412-A072414, A273058, A284569, A290103.
%Y A072411 Similar sequences: A001222 (sum of exponents), A005361 (product), A051903 (maximal exponent), A051904 (minimal exponent), A052409 (gcd of exponents), A267115 (bitwise-and), A267116 (bitwise-or), A268387 (bitwise-xor).
%Y A072411 Cf. also A055092, A060131.
%Y A072411 Differs from A290107 for the first time at n=144.
%Y A072411 After the initial term, differs from A157754 for the first time at n=360.
%K A072411 nonn,easy
%O A072411 1,4
%A A072411 _Labos Elemer_, Jun 17 2002
%E A072411 a(1) = 1 prepended and the data section filled up to 120 terms by _Antti Karttunen_, Aug 09 2016
```
### A290107
```
%I A290107 #15 Aug 15 2017 20:34:21
%S A290107 1,1,1,2,1,1,1,3,2,1,1,2,1,1,1,4,1,2,1,2,1,1,1,3,2,1,3,2,1,1,1,5,1,1,
%T A290107 1,2,1,1,1,3,1,1,1,2,2,1,1,4,2,2,1,2,1,3,1,3,1,1,1,2,1,1,2,6,1,1,1,2,
%U A290107 1,1,1,6,1,1,2,2,1,1,1,4,4,1,1,2,1,1,1,3,1,2,1,2,1,1,1,5,1,2,2,2,1,1,1,3,1,1,1,6,1,1,1,4,1,1,1,2,2,1,1,3
%N A290107 a(1) = 1; for n > 1, a(n) = product of distinct exponents in the prime factorization of n.
%H A290107 Antti Karttunen, <a href="/A290107/b290107.txt">Table of n, a(n) for n = 1..10000</a>
%H A290107 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A290107 a(n) = A156061(A181819(n)).
%e A290107 For n = 36 = 2^2 * 3^2, the only distinct exponent that occurs is 2, thus a(36) = 2.
%e A290107 For n = 144 = 2^4 * 3^2, the distinct exponents are 2 and 4, thus a(144) = 2*4 = 8.
%e A290107 For n = 4500 = 2^2 * 3^2 * 5^3, the distinct exponents are 2 and 3, thus a(4500) = 2*3 = 6.
%t A290107 Table[If[n == 1, 1, Apply[Times, Union[FactorInteger[n][[All, -1]] ]]], {n, 120}] (* _Michael De Vlieger_, Aug 14 2017 *)
%o A290107 (PARI) A290107(n) = factorback(vecsort((factor(n)[, 2]), ,8));
%o A290107 (Scheme) (define (A290107 n) (A156061 (A181819 n)))
%Y A290107 Cf. A156061, A181819.
%Y A290107 Differs from A005361 for the first time at n=36.
%Y A290107 Differs from A072411 for the first time at n=144, and also from A157754 for the second time (after the initial term).
%K A290107 nonn
%O A290107 1,4
%A A290107 _Antti Karttunen_, Aug 13 2017
```


## Candidate 94: A129251 vs A276077 (score 82.8, agree 120, variant raw, family size 4)
Terms: 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0

### A129251
```
%I A129251 #49 Sep 27 2026 00:10:13
%S A129251 0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,1,1,0,0,0,1,0,0,
%T A129251 0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,
%U A129251 0,0,0,1,0,0,0,1,0,0,0,1,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,1,0,0,0,1
%N A129251 Number of distinct prime factors p of n such that p^p is a divisor of n.
%C A129251 Average value is A094289 = 0.28735...; attains record values on A076265, in particular a(A076265(n)) = n.
%H A129251 Reinhard Zumkeller, <a href="/A129251/b129251.txt">Table of n, a(n) for n = 1..10000</a> (8 terms corrected by _Georg Fischer_, Sep 25 2026)
%H A129251 Horst Alzer and Man Kam Kwong, <a href="https://cs.uwaterloo.ca/journals/JIS/VOL26/Alzer/alzer15.html">On Sándor's Inequality for the Riemann Zeta Function</a>, J. Int. Seq. (2023) Vol. 26, Article 23.3.6.
%F A129251 a(A048103(n)) = 0, a(A100716(n)) > 0.
%F A129251 a(n) << sqrt(log n)/log log n. - _Charles R Greathouse IV_, Sep 14 2015
%F A129251 From _Antti Karttunen_, Aug 18 2016: (Start)
%F A129251 These formulas use Iverson bracket, which gives 1 as its value if the condition given inside [ ] is true and 0 otherwise:
%F A129251 a(1) = 0, for n > 1, a(n) = a(A028234(n)) + [A067029(n) >= A020639(n)].
%F A129251 Or, for n > 1, a(n) = a(A028234(n)) + [0 = n mod (A020639(n)^A020639(n))]. (End)
%F A129251 a(n) = Sum_{d|n} [rad(d) = Omega(d)*[omega(d) = 1]], where [ ] is the Iverson bracket. - _Wesley Ivan Hurt_, Feb 09 2022
%F A129251 Additive with a(p^e) = 1 if e >= p, and 0 otherwise. - _Amiram Eldar_, Nov 07 2022
%e A129251 Since 15 = 3^1 * 5^1, a(15) = 0. But 16 = 2^4 is divisible by 2^2, so a(16) = 1. - _Michael B. Porter_, Aug 18 2016
%t A129251 {0}~Join~Table[Count[FactorInteger[n][[All, 1]], _?(Mod[n, #^#] == 0 &)], {n, 2, 120}] (* _Michael De Vlieger_, Oct 30 2019 *)
%o A129251 (PARI) a(n)=my(s,t,v); forprime(p=2,, v=valuation(n,p); if(v, n/=p^v; if(v>=p, s++), if(p^p>n, return(s)))) \\ _Charles R Greathouse IV_, Sep 14 2015
%o A129251 (Scheme)
%o A129251 (define (A129251 n) (if (= 1 n) 0 (+ (A129251 (A028234 n)) (if (zero? (modulo n (expt (A020639 n) (A020639 n)))) 1 0))))
%o A129251 ;; _Antti Karttunen_, Aug 18 2016
%o A129251 (Scheme)
%o A129251 (define (A129251 n) (if (= 1 n) 0 (+ (A129251 (A028234 n)) (if (>= (A067029 n) (A020639 n)) 1 0))))
%o A129251 ;; _Antti Karttunen_, Aug 18 2016
%o A129251 (Python)
%o A129251 from sympy import factorint
%o A129251 def A129251(n): return sum(1 for p, e in factorint(n).items() if p<=e) # _Chai Wah Wu_, Sep 25 2026
%Y A129251 Cf. A129252, A020639, A028234, A001221, A051674, A067029, A094289.
%Y A129251 Cf. A048103 (indices of zeros), A100716 (nonzeros).
%Y A129251 Differs from A276077 for the first time at n=625, where a(625) = 0, while A276077(625) = 1.
%K A129251 nonn,easy
%O A129251 1,108
%A A129251 _Reinhard Zumkeller_, Apr 07 2007
%E A129251 Data section filled up to 120 terms by _Antti Karttunen_, Aug 18 2016
```
### A276077
```
%I A276077 #22 Jan 02 2024 04:41:22
%S A276077 0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,1,1,0,0,0,1,0,0,
%T A276077 0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,
%U A276077 0,0,0,1,0,0,0,1,0,0,0,1,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,1,0,0,0,1
%N A276077 Number of distinct prime factors p of n such that p^(1+A000720(p)) is a divisor of n, where A000720(p) gives the index of prime p, 1 for 2, 2 for 3, 3 for 5, and so on.
%H A276077 Antti Karttunen, <a href="/A276077/b276077.txt">Table of n, a(n) for n = 1..10000</a>
%F A276077 This formula uses Iverson bracket, which gives 1 as its value if the condition given inside [ ] is true and 0 otherwise:
%F A276077 a(1) = 0, for n > 1, a(n) = a(A028234(n)) + [A067029(n) > A055396(n)].
%F A276077 Other identities. For all n >= 1:
%F A276077 a(A276076(n)) = 0.
%F A276077 From _Amiram Eldar_, Sep 30 2023: (Start)
%F A276077 Additive with a(p^e) = 1 if primepi(p) < e, and 0 otherwise.
%F A276077 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Sum_{k>=1} 1/prime(k)^(k+1) = 0.2886971166123417096098... . (End)
%e A276077 For n = 2 (= prime(1)), 2 is not divisible by 2^(1+1), thus a(2) = 0.
%e A276077 For n = 3 (= prime(3)), 3 is not divisible by 3^(2+1), thus a(3) = 0.
%e A276077 For n = 4 (= prime(1)^2), 4 is divisible by 2^(1+1), and there are no other prime factors apart from 2, thus a(4) = 1.
%e A276077 For n = 108 = 2^2 * 3^3, it is divisible both by 2^(1+1) and 3^(2+1), thus a(108) = 2.
%e A276077 For n = 625 = prime(3)^4, it is divisible by 5^(3+1), thus a(625) = 1.
%t A276077 f[p_, e_] := If[PrimePi[p] < e, 1, 0]; a[1] = 0; a[n_] := Plus @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Sep 30 2023 *)
%o A276077 (Scheme) (define (A276077 n) (if (= 1 n) 0 (+ (A276077 (A028234 n)) (if (> (A067029 n) (A055396 n)) 1 0))))
%o A276077 (Python)
%o A276077 from sympy import primepi, isprime, primefactors, factorint
%o A276077 def a028234(n):
%o A276077     f=factorint(n)
%o A276077     return 1 if n==1 else n//(min(f)**f[min(f)])
%o A276077 def a067029(n):
%o A276077     f=factorint(n)
%o A276077     return 0 if n==1 else f[min(f)]
%o A276077 def a049084(n): return primepi(n)*(isprime(n))
%o A276077 def a055396(n): return 0 if n==1 else a049084(min(primefactors(n)))
%o A276077 def a(n):
%o A276077     if n==1: return 0
%o A276077     val = a(a028234(n))
%o A276077     if a067029(n) > a055396(n):
%o A276077         val += 1
%o A276077     return val
%o A276077 print([a(n) for n in range(1, 201)]) # _Indranil Ghosh_, Jun 21 2017
%o A276077 (PARI) a(n) = {my(f = factor(n)); sum(i = 1, #f~, primepi(f[i,1]) < f[i,2]);} \\ _Amiram Eldar_, Sep 30 2023
%Y A276077 Cf. A000720, A028234, A055396, A067029.
%Y A276077 Cf. A276078 (positions of zeros), A276079 (nonzeros), also A276076.
%Y A276077 Differs from A129251 for the first time at n=625, where a(625) = 1, while A129251(625) = 0.
%K A276077 nonn,easy
%O A276077 1,108
%A A276077 _Antti Karttunen_, Aug 18 2016
```


## Candidate 95: A294936 vs A378539 (score 82.8, agree 120, variant raw, family size 6)
Terms: 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1

### A294936
```
%I A294936 #28 Oct 13 2026 14:55:23
%S A294936 0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,
%T A294936 0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,0,0,
%U A294936 0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1
%N A294936 Characteristic function for nondeficient numbers (A023196): a(n) = 1 if A001065(n) >= n, 0 otherwise.
%C A294936 Differs from A210455 for the first time at n=70, and after that at n=836, 4030, 5830, 7192, 7912, 9272, etc., that is, at weird numbers, A006037.
%C A294936 Differs from A336835 for the first time at n=120. - _Antti Karttunen_, Apr 04 2022
%H A294936 Antti Karttunen, <a href="/A294936/b294936.txt">Table of n, a(n) for n = 1..100000</a>
%H A294936 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%H A294936 <a href="/index/Su#sums_of_divisors">Index entries for sequences related to sums of divisors</a>.
%F A294936 a(n) = 1 if A033880(n) >= 0, 0 otherwise.
%F A294936 a(n) = 1 - A294934(n).
%F A294936 a(n) >= A210455(n).
%F A294936 a(n) >= A341619(n). - _Antti Karttunen_, Apr 04 2022
%F A294936 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = A302991. - _Amiram Eldar_, Oct 13 2026
%e A294936 The proper divisors of 6 are 1, 2 and 3, and their sum is 6, and because 6 >= 6, a(6) = 1.
%e A294936 The proper divisors of 70 are 1, 2, 5, 7, 10, 14, and 35, and their sum is 74, and because 74 >= 70, a(70) = 1.
%t A294936 Table[If[DivisorSigma[1,n]>=2n,1,0],{n,120}] (* _Harvey P. Dale_, Mar 22 2020 *)
%o A294936 (PARI) a(n) = sigma(n, -1)>=2 \\ _Felix Fröhlich_, Nov 12 2017
%Y A294936 Cf. A001065, A006037, A033880, A210455, A294887, A294934, A294935, A294937, A336835.
%Y A294936 Cf. A023196 (positions of ones), A005100 (of zeros), A341620 (inverse Möbius transform), A294927 [= A341620(n)-a(n)], A302991, A341619.
%K A294936 nonn,changed
%O A294936 1
%A A294936 _Antti Karttunen_, Nov 12 2017
```
### A378539
```
%I A378539 #12 Dec 02 2024 16:02:11
%S A378539 0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,
%T A378539 0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,1,0,0,
%U A378539 0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,1
%N A378539 Characteristic function for numbers that have Zumkeller divisors.
%C A378539 Differs from A294936 at n=748, 7544, 10184, 56816, 61904, 62416, 66928, 69488, 73616, 102416, ..., that might be a subsequence of A378538.
%H A378539 Antti Karttunen, <a href="/A378539/b378539.txt">Table of n, a(n) for n = 1..108045</a>
%H A378539 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A378539 a(n) = [A378446(n) > 0], where [ ] is the Iverson bracket.
%F A378539 a(n) >= A378537(n).
%o A378539 (PARI)
%o A378539 A378446(n) = sumdiv(n,d,A083206(d));
%o A378539 A378539(n) = (A378446(n)>0);
%Y A378539 Characteristic function of A376880.
%Y A378539 Cf. A083206, A378446, A378537, A378538.
%Y A378539 Different from A294936.
%K A378539 nonn
%O A378539 1
%A A378539 _Antti Karttunen_, Dec 02 2024
```


## Candidate 96: A353675 vs A353676 (score 82.8, agree 120, variant drop1, family size 3)
Terms: 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A353675
```
%I A353675 #14 Feb 07 2024 16:20:40
%S A353675 1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,
%T A353675 1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,
%U A353675 1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,0
%N A353675 a(n) = 1 if n is an odd number with an even number of distinct prime factors, otherwise 0.
%H A353675 Antti Karttunen, <a href="/A353675/b353675.txt">Table of n, a(n) for n = 1..65537</a>
%H A353675 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A353675 a(n) = A000035(n) * (1-A092248(n)).
%F A353675 a(n) = A000035(n) - A353673(n).
%F A353675 a(n) >= A353676(n).
%e A353675 n = 45 = 3^2 * 5 is an odd number with two distinct prime factors, therefore a(45) = 1.
%e A353675 n = 1155 = 3*5*7*11 is an odd number with four distinct prime factors, therefore a(1155) = 1.
%t A353675 Table[If[OddQ[n]&&EvenQ[PrimeNu[n]],1,0],{n,130}] (* _Harvey P. Dale_, Feb 07 2024 *)
%o A353675 (PARI) A353675(n) = ((n%2) && !(omega(n)%2));
%Y A353675 Characteristic function of {1} UNION A098905.
%Y A353675 Cf. A000035, A001221, A092248, A353672, A353673, A353674.
%Y A353675 After n=1 differs from A353676 for the next time at n=1155, where a(1155)=1, while A353676(1155)=0.
%Y A353675 Cf. also A353557.
%K A353675 nonn
%O A353675 1
%A A353675 _Antti Karttunen_, May 03 2022
```
### A353676
```
%I A353676 #10 May 04 2022 08:29:56
%S A353676 0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,
%T A353676 1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,
%U A353676 1,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,0
%N A353676 a(n) = 1 if n is an odd number with exactly 2 distinct prime factors, otherwise 0.
%H A353676 Antti Karttunen, <a href="/A353676/b353676.txt">Table of n, a(n) for n = 1..65537</a>
%H A353676 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A353676 a(n) = A000035(n) * A215480(n).
%F A353676 A353675(n) >= a(n) >= A353677(n).
%e A353676 n = 45 = 3^2 * 5 is an odd number with two distinct prime factors, therefore a(45) = 1.
%o A353676 (PARI) A353676(n) = ((n%2) && (2==omega(n)));
%Y A353676 Characteristic function of A225375.
%Y A353676 Cf. A000035, A001221, A215480, A353677.
%Y A353676 After n=1 differs from A353675 for the next time at n=1155, where a(1155)=0, while A353675(1155)=1.
%K A353676 nonn
%O A353676 1
%A A353676 _Antti Karttunen_, May 03 2022
```


## Candidate 97: A055642 vs A348674 (score 82.1, agree 119, variant drop1, family size 8)
Terms: 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2

### A055642
```
%I A055642 #118 Jul 19 2026 19:56:37
%S A055642 1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%T A055642 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%U A055642 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3
%N A055642 Number of digits in the decimal expansion of n.
%C A055642 From _Hieronymus Fischer_, Jun 08 2012: (Start)
%C A055642 For n > 0 the first differences of A117804.
%C A055642 The total number of digits necessary to write down all the numbers 0, 1, 2, ..., n is A117804(n+1). (End)
%C A055642 Here a(0) = 1, but a different common convention is to consider that the expansion of 0 in any base b > 0 has 0 terms and digits. - _M. F. Hasler_, Dec 07 2018
%H A055642 Charles R Greathouse IV, <a href="/A055642/b055642.txt">Table of n, a(n) for n = 0..10000</a>
%F A055642 a(A046760(n)) < A050252(A046760(n)); a(A046759(n)) > A050252(A046759(n)). - _Reinhard Zumkeller_, Jun 21 2011
%F A055642 a(n) = A196563(n) + A196564(n).
%F A055642 a(n) = 1 + floor(log_10(n)) = 1 + A004216(n) = ceiling(log_10(n+1)) = A004218(n+1), if n >= 1. - _Daniel Forgues_, Mar 27 2014
%F A055642 a(A046758(n)) = A050252(A046758(n)). - _Reinhard Zumkeller_, Jun 21 2011
%F A055642 a(n) = A117804(n+1) - A117804(n), n > 0. - _Hieronymus Fischer_, Jun 08 2012
%F A055642 G.f.: g(x) = 1 + (1/(1-x))*Sum_{j>=0} x^(10^j). - _Hieronymus Fischer_, Jun 08 2012
%F A055642 a(n) = A262190(n) for n < 100; a(A262198(n)) != A262190(A262198(n)). - _Reinhard Zumkeller_, Sep 14 2015
%e A055642 Examples:
%e A055642 999: 1 + floor(log_10(999)) = 1 + floor(2.x) = 1 + 2 = 3 or
%e A055642       ceiling(log_10(999+1)) = ceiling(log_10(1000)) = ceiling(3) = 3;
%e A055642 1000: 1 + floor(log_10(1000)) = 1 + floor(3) = 1 + 3 = 4 or
%e A055642       ceiling(log_10(1000+1)) = ceiling(log_10(1001)) = ceiling(3.x) = 4;
%e A055642 1001: 1 + floor(log_10(1001)) = 1 + floor(3.x) = 1 + 3 = 4 or
%e A055642       ceiling(log_10(1001+1)) = ceiling(log_10(1002)) = ceiling(3.x) = 4;
%p A055642 A055642 := proc(n)
%p A055642         max(1,ilog10(n)+1) ;
%p A055642 end proc:  # _R. J. Mathar_, Nov 30 2011
%t A055642 Join[{1}, Array[ Floor[ Log[10, 10# ]] &, 104]] (* _Robert G. Wilson v_, Jan 04 2006 *)
%t A055642 (* Alternative: *)
%t A055642 Join[{1},Table[IntegerLength[n],{n,104}]] (* _Ray Chandler_, Dec 31 2010 *)
%t A055642 (* Alternative: *)
%t A055642 A055642[0] = 1;
%t A055642 A055642[n_] := IntegerLength[n];
%t A055642 Table[A055642[n],{n,0,120}]; (* _R. J. Mathar_, May 11 2026 *)
%o A055642 (PARI) a(n)=#Str(n) \\ _M. F. Hasler_, Nov 17 2008
%o A055642 (PARI) A055642(n)=logint(n+!n,10)+1 \\ Increasingly faster than the above, for larger n. (About twice as fast for n ~ 10^7.) - _M. F. Hasler_, Dec 07 2018
%o A055642 (Haskell)
%o A055642 a055642 :: Integer -> Int
%o A055642 a055642 = length . show  -- _Reinhard Zumkeller_, Feb 19 2012, Apr 26 2011
%o A055642 (Magma) [ #Intseq(n): n in [0..105] ];   //  _Bruno Berselli_, Jun 30 2011
%o A055642 (Common Lisp) (defun A055642 (n) (if (zerop n) 1 (floor (log n 10)))) ; _James Spahlinger_, Oct 13 2012
%o A055642 (Python)
%o A055642 def a(n): return len(str(n))
%o A055642 print([a(n) for n in range(121)]) # _Michael S. Branicky_, May 10 2022
%o A055642 (Python)
%o A055642 def A055642(n): # Faster than len(str(n)) from ~ 50 digits on
%o A055642     L = math.log10(n or 1)
%o A055642     if L.is_integer() and 10**int(L)>n: return int(L or 1)
%o A055642     return int(L)+1  # _M. F. Hasler_, Apr 08 2024
%Y A055642 Cf. A043537, A178788, A046034, A019546, A054899, A122840, A055640, A055641, A102669-A102685, A117804, A160093, A160094, A196563, A196564, A000120, A000788, A023416, A059015 (for base 2).
%Y A055642 Cf. A262190, A262198.
%Y A055642 Cf. A007953: sum of digits.
%K A055642 base,easy,nonn,nice
%O A055642 0,11
%A A055642 _Henry Bottomley_, Jun 06 2000
```
### A348674
```
%I A348674 #29 Dec 19 2021 12:51:29
%S A348674 1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%T A348674 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
%U A348674 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4
%N A348674 Number of distinct values that can be produced by splitting n and adding the parts.
%C A348674 Differs from A055642 first at n=120: a(120) = 4 != 3 = A055642(120).
%C A348674 The number of split positions can vary from 0 to length(n)-1.
%H A348674 Alois P. Heinz, <a href="/A348674/b348674.txt">Table of n, a(n) for n = 0..20000</a>
%F A348674 a(n) <= 2^floor(log_10(n)) = 2^A004216(n) for n>0.
%F A348674 a((10^n-1)/9) = a(A002275(n)) <= A000041(n) with equality only for n <= 23.
%F A348674 a(10^n) = a(A011557(n)) = n+1.
%e A348674 a(0) = 1: 0.
%e A348674 a(10) = 2: 1 = 1+0, 10.
%e A348674 a(100) = 3: 1 = 1+0+0, 10 = 10+0, 100.
%e A348674 a(120) = 4: 3 = 1+2+0, 12 = 12+0, 21 = 1+20, 120.
%e A348674 a(2493690) = 62 = |{33, 51, 60, 69, 78, 87, 96, 105, 114, 123, 132, 141, 150, 159, 168, 177, 186, 195, 213, 267, 294, 321, 348, 375, 384, 402, 420, 510, 564, 591, 618, 708, 726, 744, 789, 807, 942, 951, 969, 1032, 1050, 1185, 2508, 2562, 2589, 3183, 3705, 3723, 3741, 3939, 4947, 5028, 9375, 9393, 24945, 25026, 49371, 93696, 93714, 249369, 493692, 2493690}|.
%p A348674 b:= proc(s) option remember; (n-> {parse(s), seq(seq(seq(x+y,
%p A348674       y=b(s[i+1..n])), x=b(s[1..i])), i=1..n-1)})(length(s))
%p A348674     end:
%p A348674 a:= n-> nops(b(""||n)):
%p A348674 seq(a(n), n=0..120);
%Y A348674 Ordinal transform gives A349315.
%Y A348674 Where records occur: A349316.
%Y A348674 Cf. A000041, A002275, A004216, A007953, A011557, A055642, A089695.
%K A348674 nonn,base
%O A348674 0,11
%A A348674 _Alois P. Heinz_, Oct 29 2021
```


## Candidate 98: A131734 vs A134452 (score 82.1, agree 119, variant abs, family size 9)
Terms: 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1

### A131734
```
%I A131734 #19 Mar 19 2025 14:02:14
%S A131734 0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,
%T A131734 0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,
%U A131734 0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,-1,0,1,0,1,0
%N A131734 Period 6: repeat [0, 1, 0, 1, 0, -1].
%H A131734 <a href="/index/Rec#order_06">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,0,0,1).
%F A131734 From _Wesley Ivan Hurt_, Apr 06 2015: (Start)
%F A131734 G.f.: x*(1+x^2-x^4)/(1-x^6).
%F A131734 Recurrence: a(n) = a(n-6).
%F A131734 a(n) = (1-(-1)^n)*(-1)^floor(2n/3)/2.
%F A131734 abs(a(n)) = A000035(n). (End)
%e A131734 G.f. = x + x^3 - x^5 + x^7 + x^9 - x^11 + x^13 + x^15 - x^17 + x^19 + x^21 + ...
%p A131734 A131734:=n->(1-(-1)^n)*(-1)^floor(2*n/3)/2: seq(A131734(n), n=0..100); # _Wesley Ivan Hurt_, Apr 06 2015
%t A131734 CoefficientList[Series[x (1 + x^2 - x^4)/(1 - x^6), {x, 0, 100}], x] (* _Wesley Ivan Hurt_, Apr 06 2015 *)
%t A131734 PadRight[{},120,{0,1,0,1,0,-1}] (* _Harvey P. Dale_, Jun 09 2024 *)
%o A131734 (Magma) [(1-(-1)^n)*(-1)^Floor(2*n/3)/2 : n in [0..100]]; // _Wesley Ivan Hurt_, Apr 06 2015
%o A131734 (PARI) {a(n) = [ 0, 1, 0, 1, 0, -1, 0, 1][n%6 + 1]}; /* _Michael Somos_, Nov 11 2015 */
%Y A131734 Cf. A000035 (absolute value).
%K A131734 sign,easy
%O A131734 0,1
%A A131734 _Paul Curtz_, Sep 19 2007
```
### A134452
```
%I A134452 #15 Jun 28 2026 15:47:53
%S A134452 0,1,0,1,0,-1,0,1,0,1,0,1,0,1,0,-1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,1,0,1,
%T A134452 0,1,0,1,0,1,0,1,0,-1,0,-1,0,-1,0,-1,0,1,0,-1,0,-1,0,1,0,1,0,-1,0,1,0,
%U A134452 1,0,1,0,1,0,-1,0,-1,0,1,0,1,0,-1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,-1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0
%N A134452 Balanced ternary digital root of n.
%C A134452 a(A005843(n))=0; a(A134453(n))=-1; a(A134454(n))=1; abs(a(A005408(n)))=1;
%C A134452 abs(a(n)) = A000035(n).
%D A134452 D. E. Knuth, The Art of Computer Programming, Addison-Wesley, Reading, MA, Vol 2, pp 173-175.
%H A134452 R. Zumkeller, <a href="/A134452/b134452.txt">Table of n, a(n) for n = 0..10000</a>
%H A134452 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/DigitalRoot.html">Digital Root</a>
%H A134452 Wikipedia, <a href="https://en.wikipedia.org/wiki/Balanced_ternary">Balanced Ternary</a>
%F A134452 a(n) = f(n) where f(n) = if n<-1 then f(-A065363(-n)) else (if n>1 then f(A065363(n)) else n).
%e A134452 42 == '+---0' --> +1-1-2-1+0=-2 == '-+' --> -1+1=0;
%e A134452 43 == '+---+' --> +1-1-2-1+1=-1;
%Y A134452 Cf. A065363, A134453, A134454, A005843, A005408, A000035.
%Y A134452 Cf. A134451.
%K A134452 sign,base
%O A134452 0,1
%A A134452 _Reinhard Zumkeller_, Oct 27 2007
```


## Candidate 99: A184582 vs A184734 (score 82.1, agree 119, variant drop1, family size 3)
Terms: 1, 3, 5, 6, 8, 10, 11, 13, 14, 16, 18, 19, 21, 22, 24, 26, 27, 29, 31, 32, 34, 35, 37, 39, 40, 42, 44, 45, 47, 48

### A184582
```
%I A184582 #4 Mar 30 2012 18:57:16
%S A184582 1,3,5,6,8,10,11,13,14,16,18,19,21,22,24,26,27,29,31,32,34,35,37,39,
%T A184582 40,42,44,45,47,48,50,52,53,55,56,58,60,61,63,65,66,68,69,71,73,74,76,
%U A184582 77,79,81,82,84,86,87,89,90,92,94,95,97,99,100,102,103,105,107,108,110,111,113,115,116,118,120,121,123,124,126,128,129,131,133,134,136,137,139,141,142,144,145,147,149,150,152,154,155,157,158,160,162,163,165,166,168,170,171,173,175,176,178,179,181,183,184,186,188,189,191,192,194
%N A184582 floor[(n+1/5)r] where r=(1+sqrt(5))/2; complement of A184583.
%F A184582 a(n)=floor[(n+1/5)r] where r=(1+sqrt(5))/2.
%t A184582 r=(1+5^(1/2))/2;c=-1/5;s=r/(r-1);
%t A184582 Table[Floor[n*r-c*r],{n,1,120}]  (* A184582 *)
%t A184582 Table[Floor[n*s+c*s],{n,1,120}]  (* A184583 *)
%Y A184582 Cf. A184583.
%K A184582 nonn
%O A184582 1,2
%A A184582 _Clark Kimberling_, Jan 17 2011
```
### A184734
```
%I A184734 #11 Oct 12 2025 09:09:42
%S A184734 1,3,5,6,8,10,11,13,14,16,18,19,21,22,24,26,27,29,31,32,34,35,37,39,
%T A184734 40,42,44,45,47,48,50,52,53,55,56,58,60,61,63,65,66,68,69,71,73,74,76,
%U A184734 77,79,81,82,84,86,87,89,90,92,94,95,97,99,100,102,103,105,107,108,110,111,113,115,116,118,120,121,123,124,126,128,129,131,133,134,136,137,139,141,142,144,145,147,149,150,152,154,155,157,158,160,162,163,165,166,168,170,171,173,175,176,178,179,181,183,184,186,188,189,191,192,194
%N A184734 a(n)=floor(n*r+h), where r=(1+sqrt(5))/2, h=1/3; complement of A184735.
%C A184734 Differs from A184582 first at index n=137. - _R. J. Mathar_, Jan 29 2011
%F A184734 a(n)=floor(n*r+h), where r=(1+sqrt(5))/2, h=1/3.
%t A184734 r=(1+sqrt(5))/2, h=1/3; s=r/(r-1);
%t A184734 Table[Floor[n*r+h],{n,1,120}]  (* A184734 *)
%t A184734 Table[Floor[n*s+h-h*s],{n,1,120}]  (*A184735 *)
%Y A184734 Cf. A184735, A184658.
%K A184734 nonn
%O A184734 1,2
%A A184734 _Clark Kimberling_, Jan 20 2011
```


## Candidate 100: A322437 vs A322438 (score 82.1, agree 119, variant drop1, family size 186)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

### A322437
```
%I A322437 #31 May 28 2025 08:55:02
%S A322437 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A322437 0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,
%U A322437 0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2
%N A322437 Number of unordered pairs of factorizations of n into factors > 1 where no factor of one divides any factor of the other.
%C A322437 First differs from A322438 at a(144) = 3, A322438(144) = 4.
%C A322437 From _Antti Karttunen_, Dec 11 2020: (Start)
%C A322437 Zeros occur on numbers that are either of the form p^k, or q * p^k, or p*q*r, for some primes p, q, r, and exponent k >= 0. [Note also that in all these cases, when x > 1, A307408(x) = 2+A307409(x) = 2 + (A001222(x) - 1)*A001221(x) = A000005(x)].
%C A322437 Proof:
%C A322437   It is easy to see that for such numbers it is not possible to obtain two such distinct factorizations, that no factor of the other would not divide some factor of the other.
%C A322437   Conversely, the complement set of above is formed of such composites n that have at least one unitary divisor that is either of the form
%C A322437   (1) p^x * q^y, with x, y >= 2,
%C A322437   or
%C A322437   (2) p^x * q^y * r^z, with x >= 2, and y, z >= 1,
%C A322437   or
%C A322437   (3) p^x * q^y * r^z * s^w, with x, y, z, w >= 1,
%C A322437   where p, q, r, s are distinct primes. Let's indicate with C the remaining portion of k coprime to p, q, r and s (which could be also 1). Then in case (1) we can construct two factorizations, the first having factors (p*q*C) and (p^(x-1) * q^(y-1)), and the second having factors (p^x * C) and (q^y) that are guaranteed to satisfy the condition that no factor in the other factorization divides any of the factors of the other factorization. For case (2) pairs like {(p * q^y * C), (p^(x-1) * r^z)} and {(p^x * C), (q^y * r^z)}, and for case (3) pairs like {(p^x * q^y * C), (r^z * s^w)} and {(p^x * r^z * C), (q^y * s^w)} offer similar examples, therefore a(n) > 0 for all such cases.
%C A322437 (End)
%H A322437 Antti Karttunen, <a href="/A322437/b322437.txt">Table of n, a(n) for n = 1..65537</a>
%H A322437 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A322437 For n > 0, a(A002110(n)) = A322441(n)/2 = A339626(n). - _Antti Karttunen_, Dec 10 2020
%e A322437 The a(120) = 2 pairs of such factorizations:
%e A322437    (6*20)|(8*15)
%e A322437    (8*15)|(10*12)
%e A322437 The a(144) = 3 pairs of factorizations:
%e A322437    (6*24)|(9,16)
%e A322437    (8*18)|(12*12)
%e A322437    (9*16)|(12*12)
%e A322437 The a(210) = 3 pairs of factorizations:
%e A322437    (6*35)|(10*21)
%e A322437    (6*35)|(14*15)
%e A322437   (10*21)|(14*15)
%e A322437 [Note that 210 is the first squarefree number obtaining nonzero value]
%e A322437 The a(240) = 4 pairs of factorizations:
%e A322437    (6*40)|(15*16)
%e A322437    (8*30)|(12*20)
%e A322437   (10*24)|(15*16)
%e A322437   (12*20)|(15*16)
%e A322437 The a(1728) = 14 pairs of factorizations:
%e A322437     (6*6*48)|(27*64)
%e A322437    (6*12*24)|(27*64)
%e A322437      (6*288)|(27*64)
%e A322437     (8*8*27)|(12*12*12)
%e A322437   (12*12*12)|(27*64)
%e A322437   (12*12*12)|(32*54)
%e A322437     (12*144)|(27*64)
%e A322437     (12*144)|(32*54)
%e A322437     (16*108)|(24*72)
%e A322437      (18*96)|(27*64)
%e A322437      (24*72)|(27*64)
%e A322437      (24*72)|(32*54)
%e A322437      (27*64)|(36*48)
%e A322437      (32*54)|(36*48)
%t A322437 facs[n_]:=If[n<=1,{{}},Join@@Table[Map[Prepend[#,d]&,Select[facs[n/d],Min@@#>=d&]],{d,Rest[Divisors[n]]}]];
%t A322437 Table[Length[Select[Subsets[facs[n],{2}],And[!Or@@Divisible@@@Tuples[#],!Or@@Divisible@@@Reverse/@Tuples[#]]&]],{n,100}]
%o A322437 (PARI)
%o A322437 factorizations(n, m=n, f=List([]), z=List([])) = if(1==n, listput(z,Vec(f)); z, my(newf); fordiv(n, d, if((d>1)&&(d<=m), newf = List(f); listput(newf,d); z = factorizations(n/d, d, newf, z))); (z));
%o A322437 is_ndf_pair(fac1,fac2) = { for(i=1,#fac1,for(j=1,#fac2,if(!(fac1[i]%fac2[j])||!(fac2[j]%fac1[i]),return(0)))); (1); };
%o A322437 number_of_ndfpairs(z) = sum(i=1,#z,sum(j=i+1,#z,is_ndf_pair(z[i],z[j])));
%o A322437 A322437(n) = number_of_ndfpairs(Vec(factorizations(n))); \\ _Antti Karttunen_, Dec 10 2020
%Y A322437 Cf. A000688, A001055, A285572, A285573, A294068, A303362, A304713, A305149, A305150, A305193, A316476, A317144, A322435, A322436, A322441, A322442, A339626.
%Y A322437 Cf. also comments A307408 and A307409.
%K A322437 nonn
%O A322437 1,120
%A A322437 _Gus Wiseman_, Dec 08 2018
%E A322437 Data section extended up to a(120) and more examples added by _Antti Karttunen_, Dec 10 2020
```
### A322438
```
%I A322438 #16 Jan 24 2025 18:37:23
%S A322438 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
%T A322438 0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,
%U A322438 0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,4
%N A322438 Number of unordered pairs of factorizations of n into factors > 1 where no factor of one properly divides any factor of the other.
%C A322438 First differs from A322437 at a(144) = 4, A322437(144) = 3.
%C A322438 First differs from A379958 at a(120) = 2, A379958(120) = 1.
%H A322438 Antti Karttunen, <a href="/A322438/b322438.txt">Table of n, a(n) for n = 1..65537</a>
%H A322438 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%e A322438 The a(240) = 5 pairs of factorizations::
%e A322438   (4*4*15)|(4*6*10)
%e A322438     (6*40)|(15*16)
%e A322438     (8*30)|(12*20)
%e A322438    (10*24)|(15*16)
%e A322438    (12*20)|(15*16)
%t A322438 facs[n_]:=If[n<=1,{{}},Join@@Table[Map[Prepend[#,d]&,Select[facs[n/d],Min@@#>=d&]],{d,Rest[Divisors[n]]}]];
%t A322438 divpropQ[x_,y_]:=And[x!=y,Divisible[x,y]];
%t A322438 Table[Length[Select[Subsets[facs[n],{2}],And[!Or@@divpropQ@@@Tuples[#],!Or@@divpropQ@@@Reverse/@Tuples[#]]&]],{n,100}]
%o A322438 (PARI)
%o A322438 factorizations(n, m=n, f=List([]), z=List([])) = if(1==n, listput(z,Vec(f)); z, my(newf); fordiv(n, d, if((d>1)&&(d<=m), newf = List(f); listput(newf,d); z = factorizations(n/d, d, newf, z))); (z));
%o A322438 is_proper_ndf_pair(fac1,fac2) = { for(i=1,#fac1,for(j=1,#fac2,if((fac1[i]!=fac2[j]) && (!(fac1[i]%fac2[j]) || !(fac2[j]%fac1[i])),return(0)))); (1); };
%o A322438 number_of_proper_ndfpairs(z) = sum(i=1,#z,sum(j=i+1,#z,is_proper_ndf_pair(z[i],z[j])));
%o A322438 A322438(n) = number_of_proper_ndfpairs(Vec(factorizations(n))); \\ _Antti Karttunen_, Jan 24 2025
%Y A322438 Cf. A001055, A285572, A285573, A303362, A303386, A304713, A305149, A305150, A305193, A316476, A317144, A322435, A322436, A322437, A322442, A379958.
%K A322438 nonn
%O A322438 1,120
%A A322438 _Gus Wiseman_, Dec 08 2018
%E A322438 Data section extended up to a(144) by _Antti Karttunen_, Jan 24 2025
```


## Candidate 101: A347246 vs A353626 (score 82.1, agree 119, variant drop2, family size 4)
Terms: 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0

### A347246
```
%I A347246 #13 Jan 01 2026 18:19:16
%S A347246 1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,
%T A347246 0,1,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
%U A347246 0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,1
%N A347246 a(n) = 1 if the greatest prime factor of A000593(n) [sum of odd divisors of n] is at least as large as the greatest prime factor of n itself, otherwise a(n) = 0.
%H A347246 Antti Karttunen, <a href="/A347246/b347246.txt">Table of n, a(n) for n = 1..65537</a>
%H A347246 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%H A347246 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>
%F A347246 a(n) = [A006530(A000593(n)) >= A006530(n)], where [ ] is the Iverson bracket.
%F A347246 For n > 1, a(n) = 1 iff A347245(n) = 1.
%t A347246 A347246[n_] := Boole[FactorInteger[DivisorSum[n, # &, OddQ]][[-1, 1]] >= FactorInteger[n][[-1, 1]]];
%t A347246 Array[A347246, 100] (* _Paolo Xausa_, Jan 01 2026 *)
%o A347246 (PARI)
%o A347246 A006530(n) = if(1==n, n, my(f=factor(n)); f[#f~, 1]);
%o A347246 A000265(n) = (n >> valuation(n, 2));
%o A347246 A000593(n) = sigma(A000265(n));
%o A347246 A347246(n) = (A006530(A000593(n))>=A006530(n));
%Y A347246 Characteristic function of A347247. A347248 gives the positions of zeros.
%Y A347246 Cf. A000593, A006530, A347244, A347245.
%Y A347246 Cf. also A336352.
%K A347246 nonn
%O A347246 1
%A A347246 _Antti Karttunen_, Aug 28 2021
```
### A353626
```
%I A353626 #19 Jul 24 2022 03:55:48
%S A353626 0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,
%T A353626 0,1,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
%U A353626 0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1
%N A353626 a(n) = 1 if n is a multiple of the square of an odd prime (equally: if the odd part of n is not squarefree), otherwise 0.
%H A353626 Antti Karttunen, <a href="/A353626/b353626.txt">Table of n, a(n) for n = 1..65537</a>
%H A353626 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%F A353626 a(n) = A107078(A000265(n)).
%F A353626 a(n) = a(2n) = a(A000265(n)).
%F A353626 a(n) = 1 - A353627(n) = 1 - abs(A209635(n)).
%F A353626 For all n >= 1, a(n) >= A353625(n) and (1-a(n)) * A166486(n) = A008966(n).
%F A353626 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = 1 - 8/Pi^2 = 0.189430... . - _Amiram Eldar_, Jul 24 2022
%t A353626 a[n_] := If[AnyTrue[FactorInteger[n/2^IntegerExponent[n, 2]][[;;, 2]], # > 1 &], 1, 0]; Array[a, 100] (* _Amiram Eldar_, Jul 24 2022 *)
%o A353626 (PARI) A353626(n) = !issquarefree(n>>valuation(n,2));
%Y A353626 Cf. A000265, A008966, A107078, A166486, A209635, A353625.
%Y A353626 Characteristic function of A038838, binary complement of A353627.
%Y A353626 After n=1 differs from A347246 for the next time at n=153, where a(153) = 1, while A347246(153) = 0.
%K A353626 nonn
%O A353626 1
%A A353626 _Antti Karttunen_, May 02 2022
```


## Candidate 102: A353480 vs A359595 (score 82.1, agree 119, variant drop2, family size 3)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0

### A353480
```
%I A353480 #9 Apr 22 2022 10:41:06
%S A353480 0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,
%T A353480 1,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0,
%U A353480 1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,1
%N A353480 a(n) = 1 if n is an odd semiprime, otherwise 0.
%H A353480 Antti Karttunen, <a href="/A353480/b353480.txt">Table of n, a(n) for n = 1..65537</a>
%H A353480 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A353480 a(n) = A000035(n) * A064911(n).
%F A353480 a(n) = A353477(n) + A353479(n).
%F A353480 a(n) = A064911(n) - A353478(n).
%F A353480 For all n <> 4, a(n) = A302048(n) + A353481(n).
%e A353480 15 = 3*5 is an odd semiprime, thus a(15) = 1.
%e A353480 121 = 11*11 is an odd semiprime, thus a(121) = 1.
%o A353480 (PARI) A353480(n) = ((2==bigomega(n)) && (1==(n%2)));
%Y A353480 Characteristic function of A046315.
%Y A353480 Cf. A000035, A064911, A302048, A353477, A353478, A353479, A353481.
%K A353480 nonn
%O A353480 1
%A A353480 _Antti Karttunen_, Apr 22 2022
```
### A359595
```
%I A359595 #16 Jan 12 2023 18:43:51
%S A359595 1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,
%T A359595 1,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,0,0,
%U A359595 1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,1
%N A359595 Parity of A358777, where A358777 is Dirichlet inverse of the characteristic function of odd numbers with an even number of prime factors (counted with multiplicity).
%H A359595 Antti Karttunen, <a href="/A359595/b359595.txt">Table of n, a(n) for n = 1..100000</a>
%H A359595 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A359595 a(n) = A358777(n) mod 2 = A359589(n) mod 2.
%F A359595 A353480(n) <= a(n) <= A353557(n). [See comments in A358777]
%o A359595 (PARI)
%o A359595 A353557(n) = ((n%2)&&(!(bigomega(n)%2)));
%o A359595 memoA358777 = Map();
%o A359595 A358777(n) = if(1==n,1,my(v); if(mapisdefined(memoA358777,n,&v), v, v = -sumdiv(n,d,if(d<n,A353557(n/d)*A358777(d),0)); mapput(memoA358777,n,v); (v)));
%o A359595 A359595(n) = (A358777(n)%2);
%Y A359595 Characteristic function of A359596.
%Y A359595 Parity of A358777 and of A359589.
%Y A359595 Cf. A353557.
%Y A359595 Differs from A353480 at the positions given by A359597: after 1 for the next time at n=135, where a(135) = 1.
%K A359595 nonn
%O A359595 1
%A A359595 _Antti Karttunen_, Jan 09 2023
```


## Candidate 103: A227349 vs A284580 (score 81.4, agree 118, variant drop1, family size 7)
Terms: 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 3, 3

### A227349
```
%I A227349 #108 May 13 2026 17:33:20
%S A227349 1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2,3,2,2,2,4,3,3,4,5,1,1,
%T A227349 1,2,1,1,2,3,1,1,1,2,2,2,3,4,2,2,2,4,2,2,4,6,3,3,3,6,4,4,5,6,1,1,1,2,
%U A227349 1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2,3,2,2,2,4,3,3,4,5,2,2,2,4,2,2,4,6,2,2,2,4,4,4,6,8,3,3,3,6,3,3,6,9,4
%N A227349 Product of lengths of runs of 1-bits in binary representation of n.
%C A227349 This is the Run Length Transform of S(n) = {0, 1, 2, 3, 4, 5, 6, ...}. The Run Length Transform of a sequence {S(n), n >= 0} is defined to be the sequence {T(n), n >= 0} given by T(n) = Product_i S(i), where i runs through the lengths of runs of 1's in the binary expansion of n. E.g., 19 is 10011 in binary, which has two runs of 1's, of lengths 1 and 2. So T(19) = S(1)*S(2). T(0) = 1 (the empty product). - _N. J. A. Sloane_, Sep 05 2014
%C A227349 Like all run length transforms also this sequence satisfies for all i, j: A278222(i) = A278222(j) => a(i) = a(j). - _Antti Karttunen_, Apr 14 2017
%H A227349 Antti Karttunen, <a href="/A227349/b227349.txt">Table of n, a(n) for n = 0..8192</a>
%H A227349 N. J. A. Sloane, <a href="https://arxiv.org/abs/1503.01168">On the Number of ON Cells in Cellular Automata</a>, arXiv:1503.01168 [math.CO], 2015.
%H A227349 <a href="/index/Ru#rlt">Index entries for sequences computed with run length transform</a>
%F A227349 A167489(n) = a(n) * A227350(n).
%F A227349 A227193(n) = a(n) - A227350(n).
%F A227349 a(n) = Product_{i in row n of table A245562} i. - _N. J. A. Sloane_, Aug 10 2014
%F A227349 From _Antti Karttunen_, Apr 14 2017: (Start)
%F A227349 a(n) = A005361(A005940(1+n)).
%F A227349 a(n) = A284562(n) * A284569(n).
%F A227349 A283972(n) = n - a(n).
%F A227349 (End)
%F A227349 a(4n+1) = a(2n) = a(n). If n is odd, then a(4n+3) = 2*a(2n+1)-a(n). If n is even, then a(4n+3) = 2*a(2n+1) = 2*a(n/2). - _Chai Wah Wu_, Jul 17 2025
%e A227349 a(0) = 1, as zero has no runs of 1's, and an empty product is 1.
%e A227349 a(1) = 1, as 1 is "1" in binary, and the length of that only 1-run is 1.
%e A227349 a(2) = 1, as 2 is "10" in binary, and again there is only one run of 1-bits, of length 1.
%e A227349 a(3) = 2, as 3 is "11" in binary, and there is one run of two 1-bits.
%e A227349 a(55) = 6, as 55 is "110111" in binary, and 2 * 3 = 6.
%e A227349 a(119) = 9, as 119 is "1110111" in binary, and 3 * 3 = 9.
%e A227349 From _Omar E. Pol_, Feb 10 2015: (Start)
%e A227349 Written as an irregular triangle in which row lengths is A011782:
%e A227349   1;
%e A227349   1;
%e A227349   1,2;
%e A227349   1,1,2,3;
%e A227349   1,1,1,2,2,2,3,4;
%e A227349   1,1,1,2,1,1,2,3,2,2,2,4,3,3,4,5;
%e A227349   1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,2,2,2,4,2,2,4,6,3,3,3,6,4,4,5,6;
%e A227349   ...
%e A227349 Right border gives A028310: 1 together with the positive integers. (End)
%e A227349 From _Omar E. Pol_, Mar 19 2015: (Start)
%e A227349 Also, the sequence can be written as an irregular tetrahedron T(s, r, k) as shown below:
%e A227349   1;
%e A227349   ..
%e A227349   1;
%e A227349   ..
%e A227349   1;
%e A227349   2;
%e A227349   ....
%e A227349   1,1;
%e A227349   2;
%e A227349   3;
%e A227349   ........
%e A227349   1,1,1,2;
%e A227349   2,2;
%e A227349   3;
%e A227349   4;
%e A227349   ................
%e A227349   1,1,1,2,1,1,2,3;
%e A227349   2,2,2,4;
%e A227349   3,3;
%e A227349   4;
%e A227349   5;
%e A227349   ................................
%e A227349   1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4;
%e A227349   2,2,2,4,2,2,4,6;
%e A227349   3,3,3,6;
%e A227349   4,4;
%e A227349   5;
%e A227349   6;
%e A227349   ...
%e A227349 Apart from the initial 1, we have that T(s, r, k) = T(s+1, r, k). (End)
%p A227349 a:= proc(n) local i, m, r; m, r:= n, 1;
%p A227349       while m>0 do
%p A227349         while irem(m, 2, 'h')=0 do m:=h od;
%p A227349         for i from 0 while irem(m, 2, 'h')=1 do m:=h od;
%p A227349         r:= r*i
%p A227349       od; r
%p A227349     end:
%p A227349 seq(a(n), n=0..100);  # _Alois P. Heinz_, Jul 11 2013
%p A227349 # Alternative:
%p A227349 ans:=[];
%p A227349 for n from 0 to 100 do lis:=[]; t1:=convert(n, base, 2); L1:=nops(t1); out1:=1; c:=0;
%p A227349 for i from 1 to L1 do
%p A227349    if out1 = 1 and t1[i] = 1 then out1:=0; c:=c+1;
%p A227349    elif out1 = 0 and t1[i] = 1 then c:=c+1;
%p A227349    elif out1 = 1 and t1[i] = 0 then c:=c;
%p A227349    elif out1 = 0 and t1[i] = 0 then lis:=[c, op(lis)]; out1:=1; c:=0;
%p A227349    fi;
%p A227349    if i = L1 and c>0 then lis:=[c, op(lis)]; fi;
%p A227349                    od:
%p A227349 a:=mul(i, i in lis);
%p A227349 ans:=[op(ans), a];
%p A227349 od:
%p A227349 ans;  # _N. J. A. Sloane_, Sep 05 2014
%t A227349 onBitRunLenProd[n_] := Times @@ Length /@ Select[Split @ IntegerDigits[n, 2], #[[1]] == 1 & ]; Array[onBitRunLenProd, 100, 0] (* _Jean-François Alcover_, Mar 02 2016 *)
%o A227349 (Python)
%o A227349 from operator import mul
%o A227349 from functools import reduce
%o A227349 from re import split
%o A227349 def A227349(n):
%o A227349     return reduce(mul, (len(d) for d in split('0+',bin(n)[2:]) if d)) if n > 0 else 1 # _Chai Wah Wu_, Sep 07 2014
%o A227349 (SageMath) # uses[RLT from A246660]
%o A227349 A227349_list = lambda len: RLT(lambda n: n, len)
%o A227349 A227349_list(88) # _Peter Luschny_, Sep 07 2014
%o A227349 (Scheme)
%o A227349 (define (A227349 n) (apply * (bisect (reverse (binexp->runcount1list n)) (- 1 (modulo n 2)))))
%o A227349 (define (bisect lista parity) (let loop ((lista lista) (i 0) (z (list))) (cond ((null? lista) (reverse! z)) ((eq? i parity) (loop (cdr lista) (modulo (1+ i) 2) (cons (car lista) z))) (else (loop (cdr lista) (modulo (1+ i) 2) z)))))
%o A227349 (define (binexp->runcount1list n) (if (zero? n) (list) (let loop ((n n) (rc (list)) (count 0) (prev-bit (modulo n 2))) (if (zero? n) (cons count rc) (if (eq? (modulo n 2) prev-bit) (loop (floor->exact (/ n 2)) rc (1+ count) (modulo n 2)) (loop (floor->exact (/ n 2)) (cons count rc) 1 (modulo n 2)))))))
%Y A227349 Cf. A003714 (positions of ones), A005361, A005940.
%Y A227349 Cf. A000120 (sum of lengths of runs of 1-bits), A167489, A227350, A227193, A278222, A245562, A284562, A284569, A283972, A284582, A284583.
%Y A227349 Run Length Transforms of other sequences: A246588, A246595, A246596, A246660, A246661, A246674.
%Y A227349 Differs from similar A284580 for the first time at n=119, where a(119) = 9, while A284580(119) = 5.
%K A227349 nonn,base
%O A227349 0,4
%A A227349 _Antti Karttunen_, Jul 08 2013
%E A227349 Data section extended up to term a(120) by _Antti Karttunen_, Apr 14 2017
```
### A284580
```
%I A284580 #8 Apr 15 2017 09:17:45
%S A284580 1,1,1,2,1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2,3,2,2,2,4,3,3,4,5,1,1,
%T A284580 1,2,1,1,2,3,1,1,1,2,2,2,3,4,2,2,2,4,2,2,4,6,3,3,3,6,4,4,5,6,1,1,1,2,
%U A284580 1,1,2,3,1,1,1,2,2,2,3,4,1,1,1,2,1,1,2,3,2,2,2,4,3,3,4,5,2,2,2,4,2,2,4,6,2,2,2,4,4,4,6,8,3,3,3,6,3,3,6,5,4
%N A284580 Carryless base-2 product (A048720) of lengths of runs of 1-bits in binary representation of n.
%H A284580 Antti Karttunen, <a href="/A284580/b284580.txt">Table of n, a(n) for n = 0..10922</a>
%H A284580 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%e A284580 a(119) = 5, as 119 is "1110111" in binary, and A048720(3,3) = 5.
%o A284580 (Scheme) (define (A284580 n) (reduce A048720bi 1 (bisect (reverse (binexp->runcount1list n)) (- 1 (modulo n 2))))) ;; Where A048720bi is a two-argument function implementing carryless binary product, A048720. For bisect and binexp->runcount1list, see under A227349.
%Y A284580 Cf. A003714 (positions of ones).
%Y A284580 Cf. A048720, A284579.
%Y A284580 Differs from similar A227349 for the first time at n=119, where a(119) = 5, while A227349(119) = 9.
%K A284580 nonn,base
%O A284580 0,4
%A A284580 _Antti Karttunen_, Apr 14 2017
```


## Candidate 104: A103889 vs A114112 (score 80.5, agree 70, variant drop2, family size 4)
Terms: 2, 1, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 28, 27, 30, 29

### A103889
```
%I A103889 #68 Jun 11 2025 12:01:42
%S A103889 2,1,4,3,6,5,8,7,10,9,12,11,14,13,16,15,18,17,20,19,22,21,24,23,26,25,
%T A103889 28,27,30,29,32,31,34,33,36,35,38,37,40,39,42,41,44,43,46,45,48,47,50,
%U A103889 49,52,51,54,53,56,55,58,57,60,59,62,61,64,63,66,65,68,67,70,69,72,71
%N A103889 Odd and even positive integers swapped.
%C A103889 For n >= 5, also the number of (undirected) Hamiltonian cycles in the (n-2)-Moebius ladder. - _Eric W. Weisstein_, May 06 2019
%C A103889 For n >= 4, also the number of (undirected) Hamiltonian cycles in the (n-1)-prism graph. - _Eric W. Weisstein_, May 06 2019
%C A103889 The lexicographically first involution of the natural numbers with no fixed points. - _Alexander Fraebel_, Sep 08 2020
%H A103889 Eric Gottlieb, Matjaž Krnc, and Peter Muršič, <a href="https://arxiv.org/abs/2506.04991">Nim on Integer Partitions and Hyperrectangles</a>, arXiv:2506.04991 [math.CO], 2025. See p. 16.
%H A103889 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/HamiltonianCycle.html">Hamiltonian Cycle</a>
%H A103889 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/MoebiusLadder.html">Moebius Ladder</a>
%H A103889 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/PrismGraph.html">Prism Graph</a>
%H A103889 <a href="/index/Rec#order_03">Index entries for linear recurrences with constant coefficients</a>, signature (1,1,-1).
%F A103889 a(2k) = 2k-1 = A005408(k), a(2k-1) = 2k = A005843(k), k=1, 2, ...
%F A103889 O.g.f.: x*(x^2-x+2)/((x-1)^2*(1+x)). - _R. J. Mathar_, Apr 06 2008
%F A103889 a(n) = n-1+2*(n mod 2). - _Rolf Pleisch_, Apr 22 2008
%F A103889 a(n) = 2*n-a(n-1)-1 (with a(1)=2). - _Vincenzo Librandi_, Nov 16 2010
%F A103889 From _Bruno Berselli_, Nov 16 2010: (Start)
%F A103889 a(n) = n - (-1)^n.
%F A103889 a(n) - a(n-1) - a(n-2) + a(n-3) = 0 for n > 3.
%F A103889 (a(n) - 1)*(a(n-1) + 1) = 2*A176222(n+1) for n > 1.
%F A103889 (a(n) - 1)*(a(n-3) + 1) = 2*A176222(n) for n > 3. (End)
%F A103889 E.g.f.: 1 - exp(-x) + x*exp(x). - _Stefano Spezia_, May 03 2023
%t A103889 Table[{n + 1, n}, {n, 1, 100, 2}] // Flatten
%t A103889 Table[n - (-1)^n, {n, 25}] (* _Eric W. Weisstein_, May 06 2019 *)
%o A103889 (Magma) [n eq 1 select 2 else -Self(n-1)+2*n-1: n in [1..72]];
%o A103889 (Haskell)
%o A103889 import Data.List (transpose)
%o A103889 a103889 n = n - 1 + 2 * mod n 2
%o A103889 a103889_list = concat $ transpose [tail a005843_list, a005408_list]
%o A103889 -- _Reinhard Zumkeller_, Jun 23 2013, Feb 21 2011
%o A103889 (PARI) a(n)=n-1+if(n%2,2) \\ _Charles R Greathouse IV_, Feb 24 2011
%o A103889 (Python)
%o A103889 def a(n): return n+1 if n&1 else n-1
%o A103889 print([a(n) for n in range(1, 73)]) # _Michael S. Branicky_, May 03 2023
%Y A103889 Essentially the same as A014681.
%Y A103889 Odd numbers: A005408. Even numbers: A005843.
%Y A103889 Cf. A004442.
%K A103889 nonn,easy
%O A103889 1,1
%A A103889 _Zak Seidov_, Feb 20 2005
```
### A114112
```
%I A114112 #85 Jun 29 2025 02:14:29
%S A114112 1,2,4,3,6,5,8,7,10,9,12,11,14,13,16,15,18,17,20,19,22,21,24,23,26,25,
%T A114112 28,27,30,29,32,31,34,33,36,35,38,37,40,39,42,41,44,43,46,45,48,47,50,
%U A114112 49,52,51,54,53,56,55,58,57,60,59,62,61,64,63,66,65,68,67,70,69,72,71
%N A114112 a(1)=1, a(2)=2; thereafter a(n) = n+1 if n odd, n-1 if n even.
%C A114112 a(1)=1; for n>1, a(n) is the smallest positive integer not occurring earlier in the sequence such that a(n) does not divide Sum_{k=1..n-1} a(k). - _Leroy Quet_, Nov 13 2005 (This was the original definition. A simple induction argument shows that this is the same as the present definition. - _N. J. A. Sloane_, Mar 12 2018)
%C A114112 Define b(1)=2; for n>1, b(n) is the smallest number not yet in the sequence which shares a prime factor with the sum of all preceding terms. Then a simple induction argument shows that the b(n) sequence is the same as the present sequence with the first term omitted. - _David James Sycamore_, Feb 26 2018
%C A114112 Here are the details of the two induction arguments (Start)
%C A114112 For a(n), let A(n) = a(1)+...+a(n). The claim is that for n>2 a(n)=n+1 if n odd, n-1 if n even.
%C A114112 The induction hypotheses are: for i<n, a(2i)=2i+1, a(2i)=2i-1, A(2i)=i(2i+1), A(2i) = 2i^2+3i+2. This implies that when looking for a(2i), we have seen all the numbers 1 through 2i except 2i-1, so the two smallest candidates for a(2i) are 2i-1 and 2i+1. Since 2i-1 does not divide 2i^2-i-1, a(n)=2i-1. When looking for a(2i+1), we have seen all the numbers 1 through 2i already, so the two smallest candidates for a(2i+1) are 2i+1 and 2i+2. But 2i+1 does divide A(2i) and 2i+2 does not, so a(2i+1)=2i+2. QED
%C A114112 For b(n), the argument is very similar, except that the missing numbers when looking for b(n) are slightly different, and  (setting B(n) = b(1)+...b(n)), we have B(2i)=(i+1)(2i+1), B(2i+1)=(i+2)(2i+1). - _N. J. A. Sloane_, Mar 14 2018
%C A114112 When sequence a(n) is increasing, then the Cesàro means sequence c(n) = (a(1)+...+a(n))/n is also increasing, but the converse is false. This sequence is a such an example where c(n) is increasing, while a(n) is not increasing (Arnaudiès et al.). See proof in A354008. - _Bernard Schott_, May 11 2022
%D A114112 J. M. Arnaudiès, P. Delezoide et H. Fraysse, Exercices résolus d'Analyse du cours de mathématiques - 2, Dunod, Exercice 10, pp. 14-16.
%H A114112 Vincenzo Librandi, <a href="/A114112/b114112.txt">Table of n, a(n) for n = 1..2000</a>.
%H A114112 ProofWiki, <a href="https://proofwiki.org/wiki/Cesàro_Mean">Cesàro mean</a>.
%H A114112 Wikipedia, <a href="https://en.wikipedia.org/wiki/Ernesto_Cesàro">Ernesto Cesàro</a>.
%H A114112 Wikipédia, <a href="https://fr.wikipedia.org/wiki/Lemme_de_Cesàro">Lemme de Cesàro</a> (in French).
%H A114112 <a href="/index/Rec#order_03">Index entries for linear recurrences with constant coefficients</a>, signature (1,1,-1).
%F A114112 G.f.: x*(x^4-2*x^3+x^2+x+1)/((1-x)*(1-x^2)). - _N. J. A. Sloane_, Mar 12 2018
%F A114112 The g.f. for the b(n) sequence is x*(x^3-3*x^2+2*x+2)/((1-x)*(1-x^2)). - Conjectured (correctly) by _Colin Barker_, Mar 04 2018
%F A114112 E.g.f.: 1 - x + x^2/2 + (x - 1)*cosh(x) + (x + 1)*sinh(x). - _Stefano Spezia_, Sep 02 2022
%F A114112 Sum_{n>=1} (-1)^(n+1)/a(n) = 1 - log(2) (A244009). - _Amiram Eldar_, Jun 29 2025
%t A114112 a[1] = 1; a[n_] := a[n] = Block[{k = 1, s, t = Table[ a[i], {i, n - 1}]}, s = Plus @@ t; While[ Position[t, k] != {} || Mod[s, k] == 0, k++ ]; k]; Array[a, 72] (* _Robert G. Wilson v_, Nov 18 2005 *)
%o A114112 (PARI) a(n) = if (n<=2, n, if (n%2, n+1, n-1)); \\ _Michel Marcus_, May 16 2022
%o A114112 (Python)
%o A114112 def A114112(n): return n + (0 if n <= 2 else -1+2*(n%2)) # _Chai Wah Wu_, May 24 2022
%Y A114112 All of A014681, A103889, A113981, A114112, A114285 are essentially the same sequence. - _N. J. A. Sloane_, Mar 12 2018
%Y A114112 Cf. A114113 (partial sums).
%Y A114112 See A084265 for the partial sums of the b(n) sequence.
%Y A114112 About Cesàro mean theorem: A033999, A141310, A237420, A354008.
%Y A114112 Cf. A244009.
%K A114112 easy,nonn
%O A114112 1,2
%A A114112 _Leroy Quet_, Nov 13 2005
%E A114112 More terms from _Robert G. Wilson v_, Nov 18 2005
%E A114112 Entry edited (with simpler definition) by _N. J. A. Sloane_, Mar 12 2018
```


## Candidate 105: A270418 vs A367168 (score 80.5, agree 70, variant raw, family size 10)
Terms: 1, 2, 3, 4, 5, 6, 7, 1, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 3, 25, 26, 1, 28, 29, 30

### A270418
```
%I A270418 #32 Sep 11 2025 21:37:24
%S A270418 1,2,3,4,5,6,7,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,3,25,26,
%T A270418 1,28,29,30,31,1,33,34,35,36,37,38,39,5,41,42,43,44,45,46,47,48,49,50,
%U A270418 51,52,53,2,55,7,57,58,59,60,61,62,63,1,65,66,67,68,69,70,71,9,73,74,75,76,77,78,79,80,81
%N A270418 Numerator of the rational number obtained when exponents in prime factorization of n are reinterpreted as alternating binary sums (A065620).
%C A270418 Map n -> A270418(n)/A270419(n) is a bijection from N (1, 2, 3, ...) to the set of positive rationals.
%H A270418 Antti Karttunen, <a href="/A270418/b270418.txt">Table of n, a(n) for n = 1..12167</a>
%F A270418 Multiplicative with a(p^e) = p^A065620(e) for odious e, a(p^e)=1 for evil e, or equally, a(p^e) = p^(A010060(e)*A065620(e)).
%F A270418 a(1) = 1, for n > 1, a(n) = a(A028234(n)) * A020639(n)^( A010060(A067029(n)) * A065620(A067029(n)) ).
%F A270418 Other identities. For all n >= 1:
%F A270418 a(A270436(n)) = n, a(A270437(n)) = 1.
%t A270418 s[0] = 0; s[n_]:= s[n]= If[OddQ[n], 1 - 2*s[(n-1)/2], 2*s[n/2]]; f[p_, e_] := p^(ThueMorse[e] * s[e]); a[n_] := Times @@ f @@@ FactorInteger[n]; a[1] = 1; Array[a, 100] (* _Amiram Eldar_, Sep 05 2023 *)
%o A270418 (Scheme) ;; Two variants.
%o A270418 (definec (A270418 n) (cond ((= 1 n) 1) (else (* (expt (A020639 n) (* (A010060 (A067029 n)) (A065620 (A067029 n)))) (A270418 (A028234 n))))))
%o A270418 (define (A270418 n) (numerator (A270418perA270419 n)))
%o A270418 (definec (A270418perA270419 n) (cond ((= 1 n) 1) (else (* (expt (A020639 n) (A065620 (A067029 n))) (A270418perA270419 (A028234 n))))))
%o A270418 (PARI) A270418(n)={n=factor(n);n[,2]=apply(A065620,n[,2]);numerator(factorback(n))} \\ _M. F. Hasler_, Apr 16 2018
%Y A270418 Cf. A270419 (gives the denominators).
%Y A270418 Cf. A262675 (indices of ones).
%Y A270418 Cf. A000069, A001969, A010060, A020639, A028234, A065620, A067029.
%Y A270418 Cf. also A270420, A270421, A270436, A270437 and permutation pair A273671/A273672.
%Y A270418 Differs from A056192 for the first time at n=32, which here a(32)=1, while A056192(32)=4.
%K A270418 nonn,frac,easy,mult
%O A270418 1,2
%A A270418 _Antti Karttunen_, May 23 2016
```
### A367168
```
%I A367168 #14 Nov 10 2023 12:27:08
%S A367168 1,2,3,4,5,6,7,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,3,25,26,
%T A367168 1,28,29,30,31,1,33,34,35,36,37,38,39,5,41,42,43,44,45,46,47,48,49,50,
%U A367168 51,52,53,2,55,7,57,58,59,60,61,62,63,1,65,66,67,68,69,70
%N A367168 The largest unitary divisor of n that is a term of A138302.
%C A367168 First differs from A056192 at n = 32 and from A270418 at n = 128.
%H A367168 Amiram Eldar, <a href="/A367168/b367168.txt">Table of n, a(n) for n = 1..10000</a>
%F A367168 Multiplicative with a(p^e) = p^A048298(e).
%F A367168 a(n) <= n, with equality if and only if n is in A138302.
%F A367168 Sum_{k=1..n} a(k) ~ c * n^2 / 2, where c = 0.881513... (A065465).
%t A367168 f[p_, e_] := If[e == 2^IntegerExponent[e, 2], p^e, 1]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100]
%o A367168 (PARI) a(n) = {my(f = factor(n)); prod(i = 1, #f~, if(f[i, 2] == 1 << valuation(f[i, 2], 2), f[i, 1]^f[i, 2], 1));}
%o A367168 (Python)
%o A367168 from math import prod
%o A367168 from sympy import factorint
%o A367168 def A367168(n): return prod(p**e for p,e in factorint(n).items() if not(e&-e)^e) # _Chai Wah Wu_, Nov 10 2023
%Y A367168 Cf. A048298, A065465, A138302, A367169, A367170, A367171.
%Y A367168 Cf. A056192, A270418.
%Y A367168 Similar sequences: A350388, A350389, A360539.
%K A367168 nonn,easy,mult
%O A367168 1,2
%A A367168 _Amiram Eldar_, Nov 07 2023
```


## Candidate 106: A206074 vs A325559 (score 79.3, agree 69, variant raw, family size 6)
Terms: 2, 3, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 37, 41, 43, 47, 53, 55, 59, 61, 67, 69, 71, 73, 77, 79, 81, 83, 87, 89

### A206074
```
%I A206074 #35 May 30 2026 16:40:36
%S A206074 2,3,5,7,11,13,17,19,23,25,29,31,37,41,43,47,53,55,59,61,67,69,71,73,
%T A206074 77,79,81,83,87,89,91,97,101,103,107,109,113,115,117,121,127,131,137,
%U A206074 139,143,145,149,151,157,163,167,169,171,173,179,181,185,191,193,197,199,203,205,209,211,213,223,227,229
%N A206074 n-th irreducible polynomial over Q (with coefficients 0 or 1) evaluated at x=2.
%C A206074 Is every prime present?
%C A206074 Yes, see the Filaseta reference. - _Thomas Ordowski_, Feb 19 2014
%C A206074 Corresponding evaluation at x=10 is A206073. - _Michael Somos_, Feb 26 2014
%H A206074 Antti Karttunen, <a href="/A206074/b206074.txt">Table of n, a(n) for n = 1..21692</a>
%H A206074 John Brillhart, Michael Filaseta, Andrew Odlyzko, <a href="https://doi.org/10.4153/CJM-1981-080-0">On an irreducibility theorem of A. Cohn</a>, Canad. J. Math. 33(1981), pp. 1055-1059.
%H A206074 Michael Filaseta, <a href="https://doi.org/10.4153/CJM-1982-097-3">A further generalization of an irreducibility theorem of A. Cohn</a>, Canad J. Math. 34 (1982), pp. 1390-1395.
%F A206074 Other identities and observations. For all n >= 1:
%F A206074 A255574(a(n)) = n.
%e A206074 (See the example at A206073.)
%t A206074 t = Table[IntegerDigits[n, 2], {n, 1, 850}];
%t A206074 b[n_] := Reverse[Table[x^k, {k, 0, n}]]
%t A206074 p[n_, x_] := t[[n]].b[-1 + Length[t[[n]]]]
%t A206074 Table[p[n, x], {n, 1, 15}]
%t A206074 u = {}; Do[n++; If[IrreduciblePolynomialQ[p[n, x]],
%t A206074 AppendTo[u, n]], {n, 300}];
%t A206074 u                          (* A206074 *)
%t A206074 Complement[Range[200], u]  (* A205783 *)
%t A206074 b[n_] := FromDigits[IntegerDigits[u, 2][[n]]]
%t A206074 Table[b[n], {n, 1, 40}]    (* A206073 *)
%o A206074 (PARI) for(n=2, 10^3, if( polisirreducible( Pol(binary(n)) ), print1(n,", ") ) ); \\ _Joerg Arndt_, Feb 19 2014
%Y A206074 Cf. A206073, A205783 (complement), A206075 (nonprime terms), A014580 (irreducible over GF(2), a subsequence of this one), A000040 (primes, also a subsequence), A260427 (terms that are reducible over GF(2)).
%Y A206074 Cf. A255574 (left inverse).
%Y A206074 Cf. also permutations A260421 - A260426.
%Y A206074 Disjoint union of A257688 (without 1) and A260428.
%Y A206074 a(n) differs from A186891(n+1) for the first time at n=21, where a(21) = 67, while A186891(22) = 65, a term missing from here. There are several other sequences that do not diverge until after approx. the twentieth term from this one (see the context-links).
%K A206074 nonn
%O A206074 1,1
%A A206074 _Clark Kimberling_, Feb 03 2012
%E A206074 Clarified name, added more terms, _Joerg Arndt_, Feb 20 2014
```
### A325559
```
%I A325559 #19 May 11 2019 18:32:57
%S A325559 2,3,5,7,11,13,17,19,23,25,29,31,37,41,43,47,53,55,59,61,67,69,71,73,
%T A325559 77,79,81,83,87,89,91,97,101,103,107,109,113,115,117,121,127,131,137,
%U A325559 139,143,145,149,151,157,163,167,169,171,173,179,181,185,191,193,197,199,203,205,209,211,213,223,227,229,233
%N A325559 Numbers n such that for any divisor d of n, and some integer k, A048720(d,k) = n only for trivial cases d=1 and d=n.
%C A325559 These are numbers n such that there are only two divisor pairs (d, n/d) [namely, the trivial pairs (1, n) and (n, 1)] that satisfy the condition that when their binary expansions are converted to (0,1)-polynomials (e.g., 13=1101[2] encodes X^3 + X^2 + 1), then their product is the (0,1)-polynomial similarly converted from n, when the multiplication is done over field GF(2).
%C A325559 Differs from A206074 for the first time at n=173, where a(173) = 555, a value missing from A206074, while the first three terms of A206074 not present in this sequence are k = 689, 781 and 913, for all of which A325560(k) = 3, not 2.
%H A325559 Antti Karttunen, <a href="/A325559/b325559.txt">Table of n, a(n) for n = 1..25000</a>
%H A325559 <a href="/index/Ge#GF2X">Index entries for sequences related to polynomials in ring GF(2)[X]</a>
%o A325559 (PARI)
%o A325559 A325560(n) = { my(p = Pol(binary(n))*Mod(1, 2)); sumdiv(n,d,my(q = Pol(binary(d))*Mod(1, 2)); !(p%q)); };
%o A325559 isA325559(n) = (2 == A325560(n));
%Y A325559 Cf. A048720, A206074.
%Y A325559 Positions of 2's in A325560, positions of 1's in A325563 (after the initial 1), fixed points of A325643 (after the initial 1).
%Y A325559 Some subsequences: A257688 (after its initial 1), A325386 (the remaining terms).
%K A325559 nonn
%O A325559 1,1
%A A325559 _Antti Karttunen_, May 11 2019
```


## Candidate 107: A085971 vs A387421 (score 78.2, agree 68, variant raw, family size 14)
Terms: 2, 3, 5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38

### A085971
```
%I A085971 #20 Sep 13 2025 08:48:19
%S A085971 2,3,5,6,7,10,11,12,13,14,15,17,18,19,20,21,22,23,24,26,28,29,30,31,
%T A085971 33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,50,51,52,53,54,55,56,
%U A085971 57,58,59,60,61,62,63,65,66,67,68,69,70,71,72,73,74,75,76,77,78
%N A085971 Union of primes and numbers that are not prime powers (A000040, A024619).
%H A085971 Antti Karttunen, <a href="/A085971/b085971.txt">Table of n, a(n) for n = 1..10000</a>
%F A085971 For all n, A085818(a(n)) = A000040(n), A085972(n) = Max{k: a(k)<=n}.
%F A085971 a(n) = n + o(sqrt n). - _Charles R Greathouse IV_, Oct 19 2015
%t A085971 With[{nn=100},Union[Join[Prime[Range[PrimePi[nn]]],DeleteCases[Range[2,80], _?(PrimePowerQ[#]&)]]]] (* _Harvey P. Dale_, May 15 2019 *)
%o A085971 (PARI) is(n)=isprimepower(n)<2 && n>1 \\ _Charles R Greathouse IV_, Oct 19 2015
%o A085971 (Python)
%o A085971 from sympy import primepi, integer_nthroot
%o A085971 def A085971(n):
%o A085971     def f(x): return int(n+sum(primepi(integer_nthroot(x,k)[0]) for k in range(2,x.bit_length())))
%o A085971     kmin, kmax = 1,2
%o A085971     while f(kmax) >= kmax:
%o A085971         kmax <<= 1
%o A085971     while True:
%o A085971         kmid = kmax+kmin>>1
%o A085971         if f(kmid) < kmid:
%o A085971             kmax = kmid
%o A085971         else:
%o A085971             kmin = kmid
%o A085971         if kmax-kmin <= 1:
%o A085971             break
%o A085971     return kmax # _Chai Wah Wu_, Aug 20 2024
%Y A085971 Disjoint union of A000040 and A024619.
%Y A085971 Cf. A025475 (complement), A085501, A085818, A085972.
%Y A085971 Different from A007916 and A052485, as a(28) = 36, instead of 37.
%Y A085971 Differs from A387421 first at n=210, where a(210) = 225, while A387421(210) = 226.
%K A085971 nonn,easy
%O A085971 1,1
%A A085971 _Reinhard Zumkeller_, Jul 06 2003
```
### A387421
```
%I A387421 #16 Sep 13 2025 22:26:41
%S A387421 2,3,5,6,7,10,11,12,13,14,15,17,18,19,20,21,22,23,24,26,28,29,30,31,
%T A387421 33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,50,51,52,53,54,55,56,
%U A387421 57,58,59,60,61,62,63,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,82,83,84,85,86,87,88,89,90,91
%N A387421 Numbers k such that sigma(k) >= 2*A057521(k), where A057521(n) gives the powerful part of n, and sigma is the sum of divisors function.
%C A387421 Conjectured to be equal to numbers k for which sigma(k) > 2*A057521(k), which holds if there are no such k that sigma(k) = 2*A057521(k). See comments in A386428, A387719.
%H A387421 Antti Karttunen, <a href="/A387421/b387421.txt">Table of n, a(n) for n = 1..10000</a>
%H A387421 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>.
%F A387421 {k | A000203(k)/A057521(k) >= 2}.
%t A387421 A387421Q[k_] := DivisorSigma[1, k] >= 2*Times @@ Power @@@ Select[FactorInteger[k], Last[#] > 1 &];
%t A387421 Select[Range[100], A387421Q] (* _Paolo Xausa_, Sep 13 2025 *)
%o A387421 (PARI)
%o A387421 A057521(n) = { my(f=factor(n)); prod(i=1, #f~, if(f[i, 2]>1, f[i, 1]^f[i, 2], 1)); };
%o A387421 is_A387421(n) = (sigma(n) >= 2*A057521(n));
%Y A387421 Cf. A000203, A057521, A387420 (complement).
%Y A387421 Subsequences: A363169, A378859.
%Y A387421 Cf. also A386428, A387719.
%Y A387421 Differs from A085971 first at n=210, where a(210) = 226, while A085971(210) = 225.
%K A387421 nonn
%O A387421 1,1
%A A387421 _Antti Karttunen_, Sep 13 2025
```


## Candidate 108: A252895 vs A366242 (score 77.0, agree 67, variant raw, family size 13)
Terms: 1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 16, 17, 19, 21, 22, 23, 26, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 42

### A252895
```
%I A252895 #89 Nov 05 2025 15:22:28
%S A252895 1,2,3,5,6,7,10,11,13,14,15,16,17,19,21,22,23,26,29,30,31,32,33,34,35,
%T A252895 37,38,39,41,42,43,46,47,48,51,53,55,57,58,59,61,62,65,66,67,69,70,71,
%U A252895 73,74,77,78,79,80,81,82,83,85,86,87,89,91,93,94,95,96,97
%N A252895 Numbers with an odd number of square divisors.
%C A252895 Open lockers in the locker problem where the student numbers are the set of perfect squares.
%C A252895 The locker problem is a classic mathematical problem. Imagine a row containing an infinite number of lockers numbered from one to infinity. Also imagine an infinite number of students numbered from one to infinity. All of the lockers begin closed. The first student opens every locker that is a multiple of one, which is every locker. The second student closes every locker that is a multiple of two, so all of the even-numbered lockers are closed. The third student opens or closes every locker that is a multiple of three. This process continues for all of the students. [This is sometimes called the light switch problem - see A360845.]
%C A252895 A variant on the locker problem is when not all student numbers are considered; in the case of this sequence, only the square-numbered students open and close lockers. The sequence here is a list of the open lockers after all of the students have gone.
%C A252895 n is in the sequence if and only if it is the product of a squarefree number (A005117) and a fourth power (A000583). - _Robert Israel_, Apr 07 2015
%C A252895 Let D be the multiset containing d0(k), the divisor counting function, for each divisor k of n. n is in the sequence if and only if D admits a partition into two parts A and B such that the sum of the elements of A is exactly one more or less than the sum of the elements of B. For example, if n = 80, we have D = {1, 2, 2, 3, 4, 4, 5, 6, 8, 10}, and A = {1, 2, 3, 4, 4, 8} and B = {2, 5, 6, 10}. The sum of A is 22, and the sum of B is 23. - _Griffin N. Macris_, Oct 10 2016
%C A252895 From _Amiram Eldar_, Jul 07 2020: (Start)
%C A252895 Numbers k such that the largest square dividing k (A008833) is a fourth power.
%C A252895 The asymptotic density of this sequence is Pi^2/15 = A182448 = 0.657973... (Cesàro, 1885). (End)
%C A252895 Closed under the binary operation A059897(.,.), forming a subgroup of the positive integers under A059897. - _Peter Munn_, Aug 01 2020
%H A252895 Reinhard Zumkeller, <a href="/A252895/b252895.txt">Table of n, a(n) for n = 1..10000</a>
%H A252895 Ernest Cesàro, <a href="https://doi.org/10.1007/BF02420801">Le plus grand diviseur carré</a>, Annali di Matematica Pura ed Applicata, Vol. 13, No. 1 (1885), pp. 251-268, <a href="https://iris.univ-lille.fr/handle/1908/1932">entire volume</a>.
%H A252895 K. A. P. Dagal, <a href="https://arxiv.org/abs/1307.6455">Generalized Locker Problem</a>, arXiv:1307.6455 [math.NT], 2013.
%H A252895 B. Torrence and S. Wagon, <a href="https://cms.math.ca/crux/v33/n4/page232-236.pdf">The Locker Problem</a>, Crux Mathematicorum, 2007, 33(4), 232-236.
%e A252895 The set of divisors of 6 is {1,2,3,6}, which contains only one perfect square: 1; therefore 6 is a term.
%e A252895 The set of divisors of 16 is {1,2,4,8,16}, which contains three perfect squares: 1, 4, and 16; therefore 16 is a term.
%e A252895 The set of divisors of 4 is {1,2,4}, which contains two perfect squares: 1 and 4; therefore 4 is not a term.
%p A252895 N:= 1000: # to get all terms <= N
%p A252895 S:= select(numtheory:-issqrfree, {$1..N}):
%p A252895 map(s -> seq(s*i^4, i = 1 .. floor((N/s)^(1/4))), S);
%p A252895 # if using Maple 11 or earlier, uncomment the next line
%p A252895 # sort(convert(%,list)); # _Robert Israel_, Apr 07 2015
%t A252895 Position[Length@ Select[Divisors@ #, IntegerQ@ Sqrt@ # &] & /@ Range@ 70, _Integer?OddQ] // Flatten (* _Michael De Vlieger_, Mar 23 2015 *)
%t A252895 a[n_] := DivisorSigma[0, Total[EulerPhi/@Select[Sqrt[Divisors[n]], IntegerQ]]]; Flatten[Position[a/@Range@100,_?OddQ]] (* _Ivan N. Ianakiev_, Apr 07 2015 *)
%t A252895 Select[Range@ 100, OddQ@ Length@ DeleteCases[Divisors@ #, k_ /; ! IntegerQ@ Sqrt@ k] &] (* _Michael De Vlieger_, Oct 10 2016 *)
%o A252895 (C++)
%o A252895 #include <iostream>
%o A252895 using namespace std;
%o A252895 int main()
%o A252895 {
%o A252895 const int one_k = 1000;
%o A252895 //all numbers in sequence up to one_k are given
%o A252895 int lockers [one_k] = {};
%o A252895 int A = 0;
%o A252895 while (A < one_k) {
%o A252895   lockers [A] = A+1;
%o A252895   A = A + 1;
%o A252895 }
%o A252895 int B = 1;
%o A252895 while ( ((B) * (B)) <= one_k) {
%o A252895   int C = ((B) * (B));
%o A252895   int D = one_k/C;
%o A252895   int E = 1;
%o A252895   while (E <= D) {
%o A252895     lockers [(C*E)-1] = -1 * lockers [(C*E)-1];
%o A252895     E = E + 1;
%o A252895   }
%o A252895   B = B + 1;
%o A252895 }
%o A252895 int F = 0;
%o A252895 while (F < one_k) {
%o A252895   if (lockers [F] < 0) {
%o A252895     cout << (-1 * lockers [F]) << endl;
%o A252895   }
%o A252895 F = F + 1;
%o A252895 }
%o A252895 return 0;
%o A252895 } // _Walker Dewey Anderson_, Mar 22 2015
%o A252895 (PARI) isok(n) = sumdiv(n, d, issquare(d)) % 2; \\ _Michel Marcus_, Mar 22 2015
%o A252895 (SageMath) [n for n in [1..200] if len([x for x in divisors(n) if is_square(x)])%2==1] # _Tom Edgar_, Mar 22 2015
%o A252895 (Haskell)
%o A252895 a252895 n = a252895_list !! (n-1)
%o A252895 a252895_list = filter (odd . a046951) [1..]
%o A252895 -- _Reinhard Zumkeller_, Apr 06 2015
%Y A252895 Cf. A000290, A000583, A005117, A008833, A046951, A182448, A252849, A360845.
%Y A252895 Positions of ones in A335324.
%K A252895 nonn
%O A252895 1,2
%A A252895 _Walker Dewey Anderson_, Mar 22 2015
```
### A366242
```
%I A366242 #8 Oct 06 2023 10:55:29
%S A366242 1,2,3,5,6,7,10,11,13,14,15,16,17,19,21,22,23,26,29,30,31,32,33,34,35,
%T A366242 37,38,39,41,42,43,46,47,48,51,53,55,57,58,59,61,62,65,66,67,69,70,71,
%U A366242 73,74,77,78,79,80,81,82,83,85,86,87,89,91,93,94,95,96,97
%N A366242 Numbers that are products of "Fermi-Dirac primes" (A050376) that are powers of primes with exponents that are powers of 4.
%C A366242 A subsequence of A252895, and first differs from it at n = 172. A252895(172) = 256 = 2^(2^3) is not a term of this sequence.
%C A366242 Equivalently, numbers that are products of "Fermi-Dirac primes" that are powers of primes with exponents that are powers of 2 with even exponents.
%C A366242 Products of distinct numbers of the form p^(2^(2*k)), where p is prime and k >= 0.
%C A366242 Numbers whose prime factorization has exponents that are positive terms of the Moser-de Bruijn sequence (A000695).
%C A366242 Every integer k has a unique representation as a product of 2 numbers: one is in this sequence and the other is in A366243: k = A366244(k) * A366245(k).
%C A366242 The asymptotic density of this sequence is 1/c = 0.65531174251481086750..., where c is given in the formula section.
%H A366242 Amiram Eldar, <a href="/A366242/b366242.txt">Table of n, a(n) for n = 1..10000</a>
%F A366242 a(n) ~ c * n, where c = Product_{k>=0} zeta(2^(2*k+1))/zeta(2^(2*k+2)) = 1.52599127273749217982... .
%t A366242 mdQ[n_] := AllTrue[IntegerDigits[n, 4], # < 2 &]; Select[Range[100], AllTrue[FactorInteger[#][[;; , 2]], mdQ] &]
%o A366242 (PARI) ismd(n) = {my(d = digits(n, 4)); for(i = 1, #d, if(d[i] > 1, return(0))); 1;}
%o A366242 is(n) = {my(e = factor(n)[ ,2]); for(i = 1, #e, if(!ismd(e[i]), return(0))); 1;}
%Y A366242 Cf. A000695, A050376, A366243, A366244, A366245.
%Y A366242 Subsequence of A252895.
%K A366242 nonn,easy
%O A366242 1,2
%A A366242 _Amiram Eldar_, Oct 05 2023
```


## Candidate 109: A389215 vs A393981 (score 77.0, agree 67, variant raw, family size 7)
Terms: 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 29, 30, 31, 33, 34, 35, 37

### A389215
```
%I A389215 #13 Aug 31 2026 07:23:37
%S A389215 1,2,3,4,5,6,7,10,11,12,13,14,15,17,18,19,20,21,22,23,24,26,28,29,30,
%T A389215 31,33,34,35,37,38,39,41,42,43,44,46,47,51,52,53,55,57,58,59,60,61,62,
%U A389215 65,66,67,68,69,70,71,73,74,76,77,78,79,82,83,84,85,86,87,89,90,91,92,93,94,95,97,101,102,103,105,106
%N A389215 Numbers k such that {sum of unitary divisors of k} plus {sum of squarefree divisors of k} >= 2*k.
%C A389215 Numbers k for which A325973(k) >= k, or equally, A325977(k) >= 0.
%C A389215 {k | A034448(k)+A048250(k) >= 2*k}.
%H A389215 Antti Karttunen, <a href="/A389215/b389215.txt">Table of n, a(n) for n = 1..10000</a>
%t A389215 q[k_] := (Times @@ (1 + Power @@@ #) + Times @@ (1 + #[[;; , 1]]))& @ FactorInteger[k] >= 2*k; q[1] = True; Select[Range[106], q] (* _Amiram Eldar_, Aug 31 2026 *)
%o A389215 (PARI)
%o A389215 A325973(n) = (1/2)*sumdiv(n, d, d*(issquarefree(d) + (1==gcd(d, n/d))));
%o A389215 is_A389215(k) = (A325973(k) >= k);
%Y A389215 Cf. A034448, A048250, A325973, A388986 (complement).
%Y A389215 Positions of nonnegative terms in A325977.
%Y A389215 Subsequences: (A005117 U A389216), A325963, A389079.
%K A389215 nonn
%O A389215 1,2
%A A389215 _Antti Karttunen_, Sep 30 2025
```
### A393981
```
%I A393981 #10 Jun 15 2026 03:13:17
%S A393981 1,2,3,4,5,6,7,10,11,12,13,14,15,17,18,19,20,21,22,23,24,26,28,29,30,
%T A393981 31,33,34,35,37,38,39,41,42,43,44,46,47,51,52,53,55,57,58,59,60,61,62,
%U A393981 65,66,67,68,69,70,71,73,74,76,77,78,79,82,83,84,85,86,87
%N A393981 Numbers k such that A003557(k) < A053669(k).
%C A393981 Let q = A053669(k) be the smallest prime such that gcd(k,q) = 1. Let squarefree kernel rad = A007947 and let m = A003557(k) = k/rad(k). Then k is in this sequence if m < q.
%C A393981 Superset of A008578 and generally, of squarefree numbers k (in A005117), since A003557(k) = 1 and A053669(k) is a prime.
%C A393981 Intersection with A246547 is {4}. For p^j with odd prime p and j > 1, m = p and q = 2. For p = j = 2, m = 2 and q = 3, but for p = 2 and j > 2, m > 3.
%C A393981 Complement of A393869.
%C A393981 Union of A363082, A005117, and A246547 \ {4}.
%C A393981 A389215(185) = 240 is not a term, since A003557(240) = 240/30 = 8, but 7 is the smallest prime that does not divide 240.
%C A393981 Does not intersect A286708.
%H A393981 Michael De Vlieger, <a href="/A393981/b393981.txt">Table of n, a(n) for n = 1..10000</a>
%t A393981 rad[x_] := Times @@ FactorInteger[x][[All, 1]]; a053669[x_] := Module[{qx}, qx = 2; While[Divisible[x, qx], qx = NextPrime[qx]]; qx]; Select[Range[120], #/rad[#] < a053669[#] &]
%Y A393981 Cf. A003557, A005117, A008578, A053669, A286708, A363082 (intersection of {a(n)} and A126706), A389215, A393869.
%K A393981 nonn,easy
%O A393981 1,2
%A A393981 _Michael De Vlieger_, Jun 09 2026
```


## Candidate 110: A188658 vs A248803 (score 76.8, agree 128, variant drop2, family size 2)
Terms: 1, 1, 0, 4, 9, 8, 7, 5, 6, 2, 1, 1, 2, 0, 8, 9, 0, 2, 7, 0, 2, 1, 9, 2, 6, 4, 9, 1, 2, 7

### A188658
```
%I A188658 #31 Jun 03 2026 07:41:33
%S A188658 1,1,0,4,9,8,7,5,6,2,1,1,2,0,8,9,0,2,7,0,2,1,9,2,6,4,9,1,2,7,5,9,5,7,
%T A188658 6,1,8,6,9,4,5,0,2,3,4,7,0,0,2,6,3,7,7,2,9,0,5,7,2,8,2,8,2,9,7,3,2,8,
%U A188658 4,9,1,2,3,1,5,5,1,9,7,0,3,8,1,2,3,6,1,7,7,6,9,2,4,5,3,9,5,2,3,5,2,3,6,6,2,9,9,5,0,3,2,6,5,2,6,1,3,2,3,1,8,8,1,5,9,3,5,8,5,7
%N A188658 Decimal expansion of (1+sqrt(101))/10.
%C A188658 Decimal expansion of the shape of a (1/5)-extension rectangle; see A188640 for definitions of shape and r-extension rectangle.  Briefly, shape=length/width, and an r-extension rectangle is composed of two rectangles of shape 1/r when r<1.
%C A188658 The continued fraction is 1, 9, 1, 1, 9, 1, 1, 9, 1, 1, 9, 1, 1, 9, 1...
%H A188658 Clark Kimberling, <a href="https://www.jstor.org/stable/27963362">A Visual Euclidean Algorithm</a>, The Mathematics Teacher 76 (1983) 108-109.
%H A188658 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%F A188658 Equals exp(arcsinh(1/10)). - _Amiram Eldar_, Jul 04 2023
%F A188658 Minimal polynomial 5*x^2-x-5. - _R. J. Mathar_, Jun 03 2026
%e A188658 1.104987562112089027021926491275957618694502347002...
%t A188658 r = 1/5; t = (r + (4 + r^2)^(1/2))/2; FullSimplify[t]
%t A188658 N[t, 130]
%t A188658 RealDigits[N[t, 130]][[1]]
%t A188658 ContinuedFraction[t, 120]
%t A188658 RealDigits[(1+Sqrt[101])/10,10,150][[1]] (* _Harvey P. Dale_, Nov 29 2020 *)
%o A188658 (PARI) (1+sqrt(101))/10 \\ _Charles R Greathouse IV_, May 18 2026
%Y A188658 Cf. A188640.
%K A188658 nonn,cons
%O A188658 1,4
%A A188658 _Clark Kimberling_, Apr 10 2011
%E A188658 a(130) corrected by _Georg Fischer_, Apr 02 2020
```
### A248803
```
%I A248803 #35 Aug 14 2026 23:10:58
%S A248803 1,0,0,4,9,8,7,5,6,2,1,1,2,0,8,9,0,2,7,0,2,1,9,2,6,4,9,1,2,7,5,9,5,7,
%T A248803 6,1,8,6,9,4,5,0,2,3,4,7,0,0,2,6,3,7,7,2,9,0,5,7,2,8,2,8,2,9,7,3,2,8,
%U A248803 4,9,1,2,3,1,5,5,1,9,7,0,3,8,1,2,3,6,1,7,7,6,9,2,4,5,3,9,5,2,3,5,2,3,6,6,2,9,9,5,0,3,2,6,5,2,6,1,3,2,3,1,8,8,1,5,9,3,5,8,5,7,9,7,8,6,9
%N A248803 Decimal expansion of the square root of 101.
%C A248803 Differs from A188658 only in one digit.
%H A248803 NumberPlanet, <a href="http://www.numberplanet.com/number/square-root-of-101/index.html">Square Root of 101</a>
%H A248803 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%e A248803 10.0498756211208902702192649127595761869450234700263772905728282973284912315....
%t A248803 RealDigits[N[101^(1/2), 200]][[1]] (* _Jared Kish_, Oct 14 2014 *)
%o A248803 (PARI) sqrt(101) \\ _Charles R Greathouse IV_, Apr 20 2016
%Y A248803 Cf. A188658.
%K A248803 nonn,cons
%O A248803 2,4
%A A248803 _Jared Kish_, Oct 14 2014
%E A248803 a(131) corrected by _Georg Fischer_, Jul 15 2021
```

