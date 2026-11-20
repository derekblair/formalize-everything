# Coincidence-mining finalist packet
100 candidate pairs at reconstructed continuation ranks 61–160 from pass-2 families (agreement length x reconstructed definition distance, with a family-size bonus). Each entry contains the two complete OEIS internal-format records.

**Rank meaning.** These are reconstructed continuation ranks, not a verified recovery of the historical pass-2 ranks. The supplied 60 packet #1 entries remain positions 1–60 in their exact input order; all remaining family representatives are scored and sorted as specified below, and the first 100 become positions 61–160. This produces a concrete, reproducible next packet without repeating an already consumed pair. A separate global score rank is retained for every family in `pass2_reconstructed_ranking.json`; the rank crosswalk below distinguishes the two orders. The full continuation contains 10,262 pairs.

**Recovered evidence and uncertainty.** `gen_packet.py` selects `input[:n]` and does not score or filter. All 60 packet #1 pairs match their supplied family representatives; `agree = max_agree` and `family_size = size` hold for all 60. The arithmetic below reproduces all 60 stored scores, and the classifier reproduces all 120 stored domain sets when run on the staged packet #1 record excerpts. These fits do not identify a unique historical algorithm. The original eligibility rules, stress-selection results for other pairs, and tie order are absent. All 60 supplied entries have `SURVIVES_EXTENDED` status, and the generator defaults to `pass3_finalists.json`. No new stress or judging pass was performed.

**Reconstructed rule.** Use exactly the supplied `sample_pair` for each family, with agreement length `max_agree` and family size `size`. For unconsumed pairs compute `score = round(agree * distance * family_bonus, 1)` using Python rounding. `distance = 1.0` if both domain sets are nonempty and disjoint, otherwise `0.6`; `family_bonus = 1.15` if family size is greater than 2, otherwise `1.0`. Applying the 0.6 case to overlapping nonempty domain sets is an explicit extrapolation: no supplied calibration pair tests that case. No shared-reference adjustment is inferred. Sort by descending rounded score, then ascending normalized unordered pair `(min ID, max ID)`. Known packet #1 scores and domain tags remain the supplied values.

**Domain classifier.** Case-insensitive regular-expression matching on `%N` and `%C` lines only, with `%F` also included for `recurrence`; no DOTALL matching. The following minimal calibrated patterns are the complete classifier. Literal substring matches are intentional (for example, `graph` also matches `lexicographically`, as in the supplied labels). The treatment of unseen definitions is part of this reconstruction.

| Domain | Regular expression |
| --- | --- |
| primes | `prime` |
| graphs | `graph` |
| partitions | `partition` |
| permutations | `permutation` |
| binomial | `binomial\|catalan` |
| modular_forms | `theta` |
| divisor_arith | `divisor\|sigma\|phi\(` |
| digits | `decimal expansion\|base-\|continued fraction\|digits of` |
| recurrence | `a\(n\)\s*=.*a\(n-1\)` |

**Exclusions and counts.** Input: 10,262 families and 10,262 distinct unordered sample pairs, rather than the 4,650 scored finalists described in the original brief. Packet #1 exclusions: 60 distinct pairs. Remaining: 10,202. Duplicate sample-pair exclusions: 0. Explicit set-aside markers or stated reasons in the staged family data: 0; exclusions established from such markers: 0. The historical set-aside count is unknown, not zero. No additional trivial-transform or boring-pattern judgments are introduced. Consequently a new pair may score above a packet #1 pair, and may have been removed by an unavailable historical filter. Selected: 100 pairs / 200 records; no overlap with packet #1.

**Record retrieval.** All 20,524 sample-sequence records were fetched and validated from the official [OEIS data mirror](https://github.com/oeis/oeisdata), using `https://raw.githubusercontent.com/oeis/oeisdata/main/seq/{ID[:4]}/{ID}.seq`. Retrieval finished at 2026-10-23T14:54:45.812013+00:00. Candidates missing a complete record: none. Each selected record is included unabridged, including terms, references, links, programs, and metadata. This preserves packet #1's heading/terms/two-record structure while honoring the request for full records; the old generator retained only six record tags and at most 60 lines. The cache and SHA-256 manifest preserve the actual fetched snapshot of the moving `main` branch.

**Terms and agreement.** `Terms:` reproduces the first 30 supplied `sample_pair.terms` values, as the original generator did. `agree`, `variant`, and family size are staged pipeline metadata, not a new validation result. An `abs`, `drop1`, `drop2`, or `stripz` match need not be equality between the two unmodified listings. The full records are the fetched snapshot; no claim of mathematical equivalence or novelty is made.

**Snapshot calibration.** Comparing the classifier on the full fetched records with the supplied labels gives 0 domain-set differences and 0 score differences among the 60 known pairs. Exact differences, input hashes, all domain assignments, and both rank orders are recorded in `pass2_reconstructed_ranking.json`; the selected 100 and their record hashes are in `packet2_full_selection.json`. Rebuild offline with `python3 build_packet2_full.py` using the supplied cache and classifier module.

**Rank crosswalk.** Global score rank orders all 10,262 pairs by score and the declared tie rule, without preserving the consumed prefix. Candidate headings use continuation rank.

| Continuation rank | Global score rank | Pair |
| --- | --- | --- |
| 61 | 1 | A353812 vs A353813 |
| 62 | 2 | A118822 vs A230075 |
| 63 | 3 | A295884 vs A380397 |
| 64 | 4 | A036453 vs A040000 |
| 65 | 5 | A323152 vs A323153 |
| 66 | 6 | A061486 vs A264600 |
| 67 | 7 | A132272 vs A179051 |
| 68 | 9 | A305900 vs A374478 |
| 69 | 10 | A323077 vs A334201 |
| 70 | 11 | A052382 vs A209931 |
| 71 | 12 | A358678 vs A359150 |
| 72 | 13 | A256608 vs A279186 |
| 73 | 14 | A327517 vs A376504 |
| 74 | 15 | A064459 vs A342696 |
| 75 | 16 | A001462 vs A377862 |
| 76 | 17 | A031955 vs A288040 |
| 77 | 18 | A108045 vs A127672 |
| 78 | 19 | A277998 vs A289288 |
| 79 | 20 | A188734 vs A188941 |
| 80 | 21 | A355824 vs A355826 |
| 81 | 22 | A374130 vs A374466 |
| 82 | 23 | A298735 vs A384916 |
| 83 | 24 | A185014 vs A240467 |
| 84 | 25 | A359466 vs A359467 |
| 85 | 26 | A046951 vs A159631 |
| 86 | 27 | A296073 vs A305800 |
| 87 | 28 | A321538 vs A321803 |
| 88 | 29 | A373491 vs A373588 |
| 89 | 30 | A374134 vs A374136 |
| 90 | 31 | A335324 vs A366245 |
| 91 | 32 | A359162 vs A360111 |
| 92 | 33 | A319707 vs A319717 |
| 93 | 34 | A072411 vs A290107 |
| 94 | 35 | A129251 vs A276077 |
| 95 | 36 | A294936 vs A378539 |
| 96 | 37 | A353675 vs A353676 |
| 97 | 38 | A055642 vs A348674 |
| 98 | 39 | A131734 vs A134452 |
| 99 | 40 | A184582 vs A184734 |
| 100 | 41 | A322437 vs A322438 |
| 101 | 42 | A347246 vs A353626 |
| 102 | 43 | A353480 vs A359595 |
| 103 | 44 | A227349 vs A284580 |
| 104 | 45 | A103889 vs A114112 |
| 105 | 46 | A270418 vs A367168 |
| 106 | 48 | A206074 vs A325559 |
| 107 | 49 | A085971 vs A387421 |
| 108 | 50 | A252895 vs A366242 |
| 109 | 51 | A389215 vs A393981 |
| 110 | 52 | A188658 vs A248803 |
| 111 | 53 | A025446 vs A373972 |
| 112 | 54 | A004772 vs A319371 |
| 113 | 55 | A249407 vs A360305 |
| 114 | 56 | A355823 vs A355825 |
| 115 | 57 | A035930 vs A347470 |
| 116 | 58 | A087003 vs A091069 |
| 117 | 59 | A193304 vs A240370 |
| 118 | 61 | A052928 vs A346663 |
| 119 | 63 | A025657 vs A025686 |
| 120 | 64 | A038189 vs A089013 |
| 121 | 65 | A118828 vs A118831 |
| 122 | 66 | A344696 vs A389087 |
| 123 | 67 | A007094 vs A039155 |
| 124 | 68 | A088828 vs A348741 |
| 125 | 70 | A213222 vs A265283 |
| 126 | 71 | A099564 vs A276153 |
| 127 | 72 | A276150 vs A341513 |
| 128 | 73 | A292592 vs A332996 |
| 129 | 74 | A328482 vs A371091 |
| 130 | 75 | A133265 vs A275365 |
| 131 | 77 | A002324 vs A171774 |
| 132 | 78 | A004258 vs A029837 |
| 133 | 79 | A010476 vs A020762 |
| 134 | 80 | A025658 vs A025673 |
| 135 | 81 | A046978 vs A075553 |
| 136 | 82 | A052409 vs A327503 |
| 137 | 83 | A069158 vs A359155 |
| 138 | 84 | A077267 vs A081602 |
| 139 | 85 | A083650 vs A138514 |
| 140 | 86 | A093829 vs A113447 |
| 141 | 87 | A099443 vs A132342 |
| 142 | 88 | A101871 vs A101875 |
| 143 | 89 | A103391 vs A331743 |
| 144 | 90 | A106459 vs A143433 |
| 145 | 91 | A106510 vs A163804 |
| 146 | 92 | A109017 vs A110161 |
| 147 | 93 | A113446 vs A121450 |
| 148 | 94 | A113661 vs A113974 |
| 149 | 95 | A121373 vs A199918 |
| 150 | 96 | A143064 vs A185124 |
| 151 | 97 | A143259 vs A359818 |
| 152 | 98 | A156277 vs A365428 |
| 153 | 99 | A163812 vs A163818 |
| 154 | 100 | A164116 vs A164118 |
| 155 | 101 | A209927 vs A223139 |
| 156 | 102 | A290110 vs A300250 |
| 157 | 103 | A305979 vs A334868 |
| 158 | 104 | A351454 vs A351460 |
| 159 | 105 | A030205 vs A159817 |
| 160 | 106 | A115633 vs A115713 |

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

## Candidate 111: A025446 vs A373972 (score 76.2, agree 127, variant raw, family size 2)
Terms: 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0

### A025446
```
%I A025446 #27 Jun 24 2024 23:28:53
%S A025446 1,1,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,
%T A025446 0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,0,
%U A025446 0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1
%N A025446 Number of partitions of n into 2 nonnegative cubes.
%C A025446 a(1729) = 2, the first point where a value larger than 1 appears, and where this sequence differs from A373972. - _Antti Karttunen_, Jun 24 2024
%H A025446 Antti Karttunen, <a href="/A025446/b025446.txt">Table of n, a(n) for n = 0..100080</a>
%H A025446 Wikipedia, <a href="https://en.wikipedia.org/wiki/1729_(number)">1729 (number)</a>
%F A025446 a(n) = A010057(n) + A025455(n) = A010057(n) XOR A025455(n). [The latter by Fermat's Last Theorem] - _Antti Karttunen_, Jun 24 2024
%e A025446 From _Antti Karttunen_, Jun 24 2024: (Start)
%e A025446 8 = 0^3 + 2^3, and as there are no other partitions of 8 into 2 nonnegative cubes, a(8) = 1.
%e A025446 16 = 2^3 + 2^3, and as there are no other partitions of 16 into 2 nonnegative cubes, a(16) = 1.
%e A025446 1729 = 1^3 + 12^3 = 9^3 + 10^3, and as there are no other partitions of 1729 into 2 nonnegative cubes, a(1729) = 2.
%e A025446 (End)
%o A025446 (PARI) A025446(n) = if(n<=2, 1, my(s=0, x=sqrtnint(n,3)); forstep(i=x, 0, -1, my(x3=i^3, y3=n-x3); if(y3>x3, return(s), s += ispower(y3, 3)))); \\ _Antti Karttunen_, Jun 24 2024
%Y A025446 Cf. A010057, A025455, A004999 (indices of nonzero terms), A373972 (their characteristic function).
%K A025446 nonn
%O A025446 0,1730
%A A025446 _David W. Wilson_
%E A025446 Data section extended up to a(126) and the secondary offset added by _Antti Karttunen_, Jun 24 2024
```
### A373972
```
%I A373972 #11 Jun 24 2024 10:50:19
%S A373972 1,1,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,
%T A373972 0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,0,
%U A373972 0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1
%N A373972 a(n) = 1 if n can be represented as a sum of 2 nonnegative cubes, otherwise 0.
%C A373972 Differs from A025446 first at n=1729, where A025446(1729) = 2, while a(1729) = 1.
%H A373972 Antti Karttunen, <a href="/A373972/b373972.txt">Table of n, a(n) for n = 0..100080</a>
%H A373972 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%F A373972 a(n) = signum(A025446(n)) = [A025446(n) > 0], where [ ] is the Iverson bracket.
%F A373972 a(n) >= A373971(n).
%o A373972 (PARI) A373972(n) = if(0==n, 1, my(L=sqrtnint(n-1, 3)+1, U=sqrtnint(4*n, 3)); fordiv(n, m, if(L<=m && m<=U, my(ell=(m^2-n/m)/3); if(denominator(ell)==1 && issquare(m^2-4*ell), return(1)))); 0); \\ After _Charles R Greathouse IV_'s Apr 16 2013 program in A004999.
%Y A373972 Characteristic function of A004999.
%Y A373972 Cf. A010057, A025446, A373971.
%K A373972 nonn
%O A373972 0
%A A373972 _Antti Karttunen_, Jun 24 2024
```

## Candidate 112: A004772 vs A319371 (score 75.9, agree 66, variant drop1, family size 6)
Terms: 0, 2, 3, 4, 6, 7, 8, 10, 11, 12, 14, 15, 16, 18, 19, 20, 22, 23, 24, 26, 27, 28, 30, 31, 32, 34, 35, 36, 38, 39

### A004772
```
%I A004772 #93 Mar 04 2025 15:29:53
%S A004772 0,2,3,4,6,7,8,10,11,12,14,15,16,18,19,20,22,23,24,26,27,28,30,31,32,
%T A004772 34,35,36,38,39,40,42,43,44,46,47,48,50,51,52,54,55,56,58,59,60,62,63,
%U A004772 64,66,67,68,70,71,72,74,75,76,78,79,80,82,83,84,86,87,88,90
%N A004772 Numbers that are not congruent to 1 (mod 4).
%C A004772 Numbers whose binary expansion does not end in 01.
%C A004772 Equals partial sums of 0 together with 2, 1, 1, 2, 1, 1, ... (repeated, that is A131534 without the first term). - _Bruno Berselli_, Dec 06 2016
%C A004772 It seems that the numbers m = 3*(a(n)+1)= 1, 7, 10, 13, 19, 22, 25, 31, 34 ... are exactly the indices of Fibonacci numbers F_m that start 5 consecutive pairwise coprime F_m, F_{m+1}, ..., F_{m+4}. E.g. for m=13 the numbers {233,377,610,987,1597} are coprime. - _R. J. Mathar_, Mar 04 2025
%H A004772 Vincenzo Librandi, <a href="/A004772/b004772.txt">Table of n, a(n) for n = 1..1000</a>
%H A004772 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (1,0,1,-1).
%F A004772 G.f.: x^2*(2 + x + x^2)/((1 + x + x^2)*(x - 1)^2). - _R. J. Mathar_, Oct 08 2011
%F A004772 a(n) = floor((4*n-2)/3). - _Gary Detlefs_, Jan 02 2012
%F A004772 a(n) = n + ceiling((n-1)/3) - 1. - _Arkadiusz Wesolowski_, Sep 18 2012
%F A004772 From _Ant King_, Oct 19 2012: (Start)
%F A004772 a(n) = 4 + a(n-3).
%F A004772 a(n) = (12*n -9 - 3*cos(2*(n-1)*Pi/3) + sqrt(3)*sin(2*(n-1)*Pi/3))/9. (End)
%F A004772 a(n) = ceiling(4*(n-1)/3). - _Jean-François Alcover_, Mar 07 2014
%F A004772 Sum_{n>=2} (-1)^n/a(n) = log(sqrt(2)+2)/(2*sqrt(2)) + (2-sqrt(2))*log(2)/8 - (sqrt(2)-1)*Pi/8. - _Amiram Eldar_, Dec 05 2021
%F A004772 a(n) = A042965(n+1)-1. - _R. J. Mathar_, Mar 04 2025
%p A004772 seq(seq(4*i+j,j=[0,2,3]),i=0..100); # _Robert Israel_, Sep 01 2015
%t A004772 LinearRecurrence[{1,0,1,-1},{0,2,3,4},68] (* _Ant King_, Oct 19 2012 *)
%t A004772 DeleteCases[Range[0,90],_?(Mod[#,4]==1&)] (* _Harvey P. Dale_, Jun 11 2013 *)
%t A004772 CoefficientList[Series[x (2 + x + x^2)/((1 + x + x^2) (x - 1)^2), {x, 0, 100}], x] (* _Vincenzo Librandi_, Mar 08 2014 *)
%o A004772 (Magma) [n: n in [0..100] | not n  mod 4 eq 1 ]; // _Vincenzo Librandi_, Mar 09 2014
%o A004772 (Magma) [(4*n-2) div 3: n in [1..100]]; // _Bruno Berselli_, Dec 06 2016
%o A004772 (PARI) a(n) = (4*n-2)\3; \\ _Michel Marcus_, Sep 03 2015
%Y A004772 Cf. A016813 (complement), A042965, A131534.
%K A004772 nonn,easy
%O A004772 1,2
%A A004772 _N. J. A. Sloane_
%E A004772 Corrected by _Michael Somos_, Jun 08 2000
```
### A319371
```
%I A319371 #37 Sep 22 2025 16:01:30
%S A319371 1,2,3,4,6,7,8,10,11,12,14,15,16,18,19,20,22,23,24,26,27,28,30,31,32,
%T A319371 34,35,36,38,39,40,42,43,44,46,47,48,50,51,52,54,55,56,58,59,60,62,63,
%U A319371 64,66,67,68,70,71,72,74,75,76,78,79,80,82,83,84,86,87,88
%N A319371 Numbers k such that the characteristic polynomial of a wheel graph of k nodes has exactly one monomial with vanishing coefficient.
%C A319371 For the spectrum of W_n see, e.g., the Wikipedia link. - _Wolfdieter Lang_, Oct 30 2018
%H A319371 Wikipedia, <a href="https://en.wikipedia.org/wiki/Wheel_graph">Wheel graph</a>
%F A319371 Conjecture: a(n) = A004772(n) for n> 1. [clarified by _Michel Marcus_, Apr 16 2019]
%F A319371 Conjectures from _Colin Barker_, Nov 02 2020: (Start)
%F A319371 G.f.: x*(1 + x + x^2 + x^4) / ((1 - x)^2*(1 + x + x^2)).
%F A319371 a(n) = a(n-1) + a(n-3) - a(n-4) for n>5.
%F A319371 (End)
%e A319371 4 is a term as the characteristic polynomial of the wheel graph of 4 nodes is x^4 - 6*x^2 - 8*x - 3, in which the monomial of x^3 has null coefficient and no other ones, so this polynomial has exactly one monomial with vanishing coefficient.
%e A319371 5 is not member of this sequence because the eigenvalues of A(W_5) (the adjacency matrix of W_5) has eigenvalues 0, 0, 2, 1 + sqrt(5), 1 - sqrt(5), and the monic characteristic polynomial is x^5 - 8*x^3 - 8*x^2 with three missing monomials x^0, x^1 and x^4. - _Wolfdieter Lang_, Oct 30 2018
%o A319371 (SageMath)
%o A319371 def how_many_zeros(v):
%o A319371     t=0
%o A319371     for el in v:
%o A319371         if el==0: t += 1
%o A319371     return t
%o A319371 r=""
%o A319371 for i in range(1,100):
%o A319371         p = graphs.WheelGraph(i)
%o A319371         cp=p.characteristic_polynomial()
%o A319371         vcp=(cp.coefficients(sparse=False))
%o A319371         if how_many_zeros(vcp)==1:
%o A319371             r=r+","+str(i)
%o A319371 print(r)
%Y A319371 Cf. A004772.
%K A319371 nonn
%O A319371 1,2
%A A319371 _Pierandrea Formusa_, Sep 17 2018
```

## Candidate 113: A249407 vs A360305 (score 75.9, agree 66, variant raw, family size 10)
Terms: 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33

### A249407
```
%I A249407 #8 May 14 2017 11:56:06
%S A249407 2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,27,28,
%T A249407 29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,
%U A249407 52,53,54,55,57,58,59,60,61,62,63,64,65,66,67,68,69,70
%N A249407 Numbers not in A249406.
%C A249407 Primes are a subsequence, but semiprimes (cf. A001358) are not: first missing: A249406(1)=6=2*3, A249406(732)=2196323=1481*1483, A249406(1263)=6502499=2549*2551, A249406(1472)=8820899=2969*2971, A249406(1756)=12531599=3539*3541, ... ;
%C A249407 see A249411 for numbers of the form m*(m+1).
%o A249407 (Haskell)
%o A249407 import Data.List ((\\))
%o A249407 a249407 n = a249407_list !! (n-1)
%o A249407 a249407_list = f [2..] where
%o A249407    f ws@(u:v:_) = u : v : f (ws \\ [u, v, u * v])
%Y A249407 Cf. A249406 (complement), A000040 (subsequence), A001358.
%K A249407 nonn
%O A249407 1,1
%A A249407 _Reinhard Zumkeller_, Oct 31 2014
```
### A360305
```
%I A360305 #48 Mar 07 2023 07:42:23
%S A360305 2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,27,28,
%T A360305 29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,
%U A360305 52,53,54,55,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71
%N A360305 Lexicographically earliest sequence of integers > 1 such that the products Product_{i = 1+k*2^e..(k+1)*2^e} a(i) with k, e >= 0 are all distinct.
%C A360305 In other words, a(1), a(2), a(1)*a(2), a(3), a(4), a(3)*a(4), a(1)*a(2)*a(3)*a(4), a(5), a(6), a(5)*a(6), etc. are all distinct.
%C A360305 In particular, all terms are distinct (but not necessarily in increasing order).
%C A360305 We can arrange the terms of the sequence as the leaves of a perfect infinite binary tree, the products with e > 0 corresponding to parent nodes; each node will contain a different value and all values will appear in the tree (if n = 2^m+1 for some m > 0, then a(n) will equal the least value > 1 missing so far in the tree).
%C A360305 This sequence is a variant of A361144 where we use products instead of sums.
%C A360305 The data section matches that of A249407, however a(115) = 121 whereas A249407(115) = 120.
%H A360305 Rémy Sigrist, <a href="/A360305/a360305.gp.txt">PARI program</a>
%e A360305 The first terms (at the bottom of the tree) alongside the corresponding products are:
%e A360305                           1067062284288000
%e A360305                   ---------------------------------
%e A360305                604800                        1764322560
%e A360305           -----------------               -----------------
%e A360305          120            5040            24024           73440
%e A360305       ---------       ---------       ---------       ---------
%e A360305       6      20      56      90      132     182     240     306
%e A360305     -----   -----   -----   -----   -----   -----   -----   -----
%e A360305     2   3   4   5   7   8   9  10  11  12  13  14  15  16  17  18
%o A360305 (PARI) See Links section.
%Y A360305 Cf. A249407, A361144, A361234.
%K A360305 nonn
%O A360305 1,1
%A A360305 _Rémy Sigrist_, Mar 03 2023
```

## Candidate 114: A355823 vs A355825 (score 75.0, agree 125, variant drop2, family size 2)
Terms: 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1

### A355823
```
%I A355823 #21 Jul 23 2022 05:26:41
%S A355823 1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,0,1,1,1,1,0,1,1,
%T A355823 1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,
%U A355823 1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,0,1,1,0
%N A355823 a(n) = 1 if all exponents in prime factorization of n are powers of 2, otherwise 0.
%H A355823 Antti Karttunen, <a href="/A355823/b355823.txt">Table of n, a(n) for n = 1..100000</a>
%H A355823 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%H A355823 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%F A355823 Multiplicative with a(p^e) = A209229(e).
%F A355823 For all n >= 1, A302777(n) <= a(n) <= A355825(n).
%F A355823 a(n) = A091862(A225546(n)).
%F A355823 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = A271727. - _Amiram Eldar_, Jul 23 2022
%e A355823 For n = 8 = 2^3, a(8) = 0 as 3 is not a power of 2 (in A000079).
%t A355823 a[n_] := If[AllTrue[FactorInteger[n][[;; , 2]], # == 2^IntegerExponent[#, 2] &], 1, 0]; Array[a, 100] (* _Amiram Eldar_, Jul 19 2022 *)
%o A355823 (PARI) A355823(n) = factorback(apply(e->!bitand(e,e-1),factor(n)[,2]));
%Y A355823 Characteristic function of A138302, "Exponentially 2^n-numbers".
%Y A355823 Cf. A000079, A091862, A209229, A225546, A271727, A302777, A355824 (Dirichlet inverse).
%Y A355823 Differs from related A355825 for the first time at n=128, where a(128) = 0, while A355825(128) = 1.
%K A355823 nonn,mult
%O A355823 1
%A A355823 _Antti Karttunen_, Jul 19 2022
```
### A355825
```
%I A355825 #18 Oct 28 2023 03:45:47
%S A355825 1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,0,1,1,1,1,0,1,1,
%T A355825 1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,
%U A355825 1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,0,1,1,1
%N A355825 a(n) = 1 if all exponents in prime factorization of n have an odd binary weight, otherwise 0.
%H A355825 Antti Karttunen, <a href="/A355825/b355825.txt">Table of n, a(n) for n = 1..100000</a>
%H A355825 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>.
%H A355825 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>.
%F A355825 Multiplicative with a(p^e) = A010060(e).
%F A355825 For all n >= 1, a(n) >= A355823(n) >= A302777(n).
%F A355825 a(n) = A295316(A268385(n)).
%F A355825 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Product_{p prime} (1 + f(1/p)) = 0.87686263163054480657..., where f(x) = 1 - x + (1 - (1-x) * Product_{k>=0} (1-x^(2^k)))/2. - _Amiram Eldar_, Oct 27 2023
%t A355825 a[n_] := If[AllTrue[FactorInteger[n][[;; , 2]], OddQ[DigitCount[#, 2, 1]] &], 1, 0]; Array[a, 100] (* _Amiram Eldar_, Jul 19 2022 *)
%o A355825 (PARI) A355825(n) = factorback(apply(e->(hammingweight(e)%2),factor(n)[,2]));
%Y A355825 Characteristic function of A270428 (exponentially odious numbers).
%Y A355825 Cf. A000069, A010060, A268385, A295316, A302777, A355826 (Dirichlet inverse).
%Y A355825 Differs from related A355823 for the first time at n=128, where a(128) = 1, while A355823(128) = 0.
%Y A355825 Cf. also A270419.
%K A355825 nonn,easy,mult
%O A355825 1
%A A355825 _Antti Karttunen_, Jul 19 2022
```

## Candidate 115: A035930 vs A347470 (score 74.5, agree 108, variant raw, family size 15)
Terms: 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18

### A035930
```
%I A035930 #31 Oct 05 2021 22:00:42
%S A035930 0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,0,2,4,6,8,10,12,14,16,18,0,3,
%T A035930 6,9,12,15,18,21,24,27,0,4,8,12,16,20,24,28,32,36,0,5,10,15,20,25,30,
%U A035930 35,40,45,0,6,12,18,24,30,36,42,48,54,0,7,14,21,28,35,42,49,56,63,0,8,16,24,32,40,48,56,64,72,0,9,18,27,36,45,54,63,72,81,0,10,20,30,40,50,60,70
%N A035930 Maximal product of any two numbers whose concatenation is n.
%C A035930 Agrees up to a(100) = 0 with A088117, A171765 and A257297, but all of the four differ in a(101) and subsequent values. - _M. F. Hasler_, Sep 01 2021
%H A035930 Alois P. Heinz, <a href="/A035930/b035930.txt">Table of n, a(n) for n = 0..9999</a>
%H A035930 Eric Angelini, <a href="https://cinquantesignes.blogspot.com/2021/08/surface-of-number.html">Surface of a number</a>, Sep 01 2021.
%e A035930 a(341) = max(34*1,3*41) = 123.
%p A035930 a:= proc(n) local l, m; l:= convert(n, base, 10); m:= nops(l);
%p A035930       `if`(m<2, 0, max(seq(parse(cat(seq(l[m-i], i=0..j-1)))
%p A035930        *parse(cat(seq(l[m-i], i=j..m-1))), j=1..m)))
%p A035930     end:
%p A035930 seq(a(n), n=0..120);  # _Alois P. Heinz_, May 22 2009
%t A035930 Flatten[With[{c=Range[0,9]},Table[c*n,{n,0,10}]]] (* _Harvey P. Dale_, Jun 07 2012 *)
%o A035930 (Haskell)
%o A035930 a035930 n | n < 10    = 0
%o A035930           | otherwise = maximum $ zipWith (*)
%o A035930             (map read $ init $ tail $ inits $ show n)
%o A035930             (map read $ tail $ init $ tails $ show n)
%o A035930 -- _Reinhard Zumkeller_, Aug 14 2011
%o A035930 (PARI) apply( {A035930(n)=if(n>9,vecmax([vecprod(divrem( n,10^j))|j<-[1..logint(n,10)]]))}, [0..111]) \\ _M. F. Hasler_, Sep 01 2021
%o A035930 (Python)
%o A035930 def a(n):
%o A035930     s = str(n)
%o A035930     return max((int(s[:i])*int(s[i:]) for i in range(1, len(s))), default=0)
%o A035930 print([a(n) for n in range(108)]) # _Michael S. Branicky_, Sep 01 2021
%Y A035930 Different from A007954, A088117, A171765 and A257297. Cf. A035931-A035935.
%K A035930 nonn,base,nice,look
%O A035930 0,13
%A A035930 _Erich Friedman_
%E A035930 An erroneous formula was deleted by _N. J. A. Sloane_, Dec 23 2008
```
### A347470
```
%I A347470 #10 Oct 22 2021 23:45:23
%S A347470 0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,0,2,4,6,8,10,12,14,16,18,0,3,
%T A347470 6,9,12,15,18,21,24,27,0,4,8,12,16,20,24,28,32,36,0,5,10,15,20,25,30,
%U A347470 35,40,45,0,6,12,18,24,30,36,42,48,54,0,7,14,21,28,35,42,49,56,63,0,8,16,24,32,40,48,56,64,72,0,9,18,27,36,45,54,63,72,81,0,10,20,30,40,50,60,70,80,90,0,11,12
%N A347470 Least product of any two numbers whose concatenation is n, excluding 0*n for n > 9.
%C A347470 Leading zeros are not allowed: e.g., 101 = concat(10,1) but not concat(1,01). Although 0 is a valid number, we don't allow the trivial decomposition n = concat(0, n) except for the single-digit n < 10, otherwise the minimal product would always be 0.
%C A347470 For n < 111, this sequence coincides with A035930 (same with "largest"), because there is only one possible concatenation, but it differs for n > 111, cf. examples.
%H A347470 Eric Angelini, <a href="https://cinquantesignes.blogspot.com/2021/08/surface-of-number.html">Surface of a number</a>, Sep 01 2021.
%e A347470 The number n = 112 is the concatenation of 1 and 12, or of 11 and 2, with respective products 1*12 = 12 and 11*2 = 22. Hence, a(112) = 12, while A035930(112) = 22.
%o A347470 (PARI) apply( {A347470(x,t(b,c)=if(c\10<=b%c,b\c*(b%c),c>10,oo))= if(x>9,vecmin(vector(logint(x,10),j,t(x,10^j))))}, [0..112])
%Y A347470 Cf. A035930, A007954, A088117, A171765 and A257297.
%K A347470 nonn,base
%O A347470 0,13
%A A347470 _M. F. Hasler_, Sep 03 2021
```

## Candidate 116: A087003 vs A091069 (score 74.5, agree 108, variant abs, family size 5)
Terms: 1, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0

### A087003
```
%I A087003 #78 Apr 17 2026 00:40:31
%S A087003 1,0,-1,0,-1,0,-1,0,0,0,-1,0,-1,0,1,0,-1,0,-1,0,1,0,-1,0,0,0,0,0,-1,0,
%T A087003 -1,0,1,0,1,0,-1,0,1,0,-1,0,-1,0,0,0,-1,0,0,0,1,0,-1,0,1,0,1,0,-1,0,
%U A087003 -1,0,0,0,1,0,-1,0,1,0,-1,0,-1,0,0,0,1,0,-1,0,0,0,-1,0,1,0,1,0,-1,0,1,0,1,0,1,0,-1,0,0,0,-1,0,-1,0,-1,0,-1,0,-1,0,1,0,-1
%N A087003 a(2n) = 0 and a(2n+1) = mu(2n+1); also the sum of Mobius function values computed for terms of 3x+1 trajectory started at n, provided that Collatz conjecture is true.
%C A087003 Observe that (these summatory) terms are from {-1,0,1}, so behave like Mobius function values, not like Mertens function values. Moreover, empirically: a(n) deviates from mu(initial-value) = mu(n) only if iv = n is an even squarefree number (i.e., it is from A039956). - This comment, like also the next one, concerns the original Collatz-related definition of this sequence. - _Antti Karttunen_, Sep 18 2017
%C A087003 From _Marc LeBrun_, Feb 19 2004: (Start)
%C A087003 Absolute values are the same as those of A091069. First consider the descending parts of Collatz (or 3x+1) trajectories, those that begin with even numbers 2^p k, with k odd. These go 2^p*k, 2^(p-1)*k, ... 2k, k. All but 2k and k are divisible by 4, a (rational) square, hence their mu values are all 0 and so they contribute nothing to the sum.
%C A087003 Then at the end, since mu(2k) = -mu(k), the last two steps cancel each other out. So every descending chain in a trajectory contributes 0. Of course the full trajectory of every even number consists entirely of descending chains, so A087003 is 0 for all even n.
%C A087003 On the other hand, the trajectory of every odd number consists of just that number followed by the trajectory of an even number (which contributes nothing) so A087003 is indeed equal to mu(n) for odd n.
%C A087003 (End)
%C A087003 The sequence is multiplicative; it may be defined as the Dirichlet inverse of the integers modulo 2 (A000035). - _Gerard P. Michon_, Apr 29 2007
%C A087003 a(n) appears in the second column of A156241 at every second row. - _Mats Granvik_, Feb 07 2009
%H A087003 Antti Karttunen, <a href="/A087003/b087003.txt">Table of n, a(n) for n = 1..10000</a>
%H A087003 Gérard P. Michon, <a href="http://www.numericana.com/answer/open.htm#collatz">The Collatz problem</a>.
%H A087003 Gérard P. Michon, <a href="http://www.numericana.com/answer/numbers.htm#multiplicative">Multiplicative functions</a>.
%H A087003 Walter Moreira and Joe Stubbs, <a href="https://arxiv.org/abs/2601.11757">Sequencelib: A Computational Platform for Formalizing the OEIS in Lean</a>, arXiv:2601.11757 [cs.LO], 2026. See p. 11.
%H A087003 <a href="/index/3#3x1">Index entries for sequences related to 3x+1 (or Collatz) problem</a>
%F A087003 a(n) = A008683(n) + A292273(n). - _Antti Karttunen_, Sep 14 2017
%F A087003 Moebius transform of A209229. - _Andrew Howroyd_, Aug 04 2018
%F A087003 From _Jianing Song_, Aug 04 2018: (Start)
%F A087003 Multiplicative with a(2^e) = 0, a(p^e) = (-1 + (-1)^e)/2 for odd primes p.
%F A087003 Dirichlet g.f.: 1/((1 - 2^(-s))*zeta(s)). (End)
%F A087003 From _Antti Karttunen_, Sep 01 2018: (Start)
%F A087003 a(n) = A000035(n)*A008683(n).
%F A087003 Dirichlet convolution of A318657/A046644 with itself. (End)
%F A087003 Sum_{n>=1} a(n)/n^2 = A217739 . Sum_{n>=1} a(n)/n^3 = A233091. Sum_{n>=1} a(n)/n^4 = A300707. - _R. J. Mathar_, Dec 17 2024
%F A087003 a(n) = - A099991(n). - _Ridouane Oudra_, Apr 12 2026
%t A087003 c[x_] := (1-Mod[x, 2])*(x/2)+Mod[x, 2]*(3*x+1); c[1]=1; fpl[x_] := Delete[FixedPointList[c, x], -1] lf[x_] := Length[fpl[x]] Table[Apply[Plus, Table[MoebiusMu[Part[fpl[w], j]], {j, 1, lf[w]}]], {w, 1, 256}]
%t A087003 Riffle[MoebiusMu[Range[1,121,2]],0] (* _Harvey P. Dale_, Jan 24 2025 *)
%o A087003 (PARI)
%o A087003 A006370(n) = if(n%2, 3*n+1, n/2); \\ This function from _Michael B. Porter_, May 29 2010
%o A087003 A087003(n) = { my(s=1); while(n>1, s += moebius(n); n = A006370(n)); (s); }; \\ _Antti Karttunen_, Sep 14 2017
%o A087003 (PARI) a(n)={sumdiv(n, d, my(e=valuation(d, 2)); if(d==1<<e, moebius(n/d), 0))} \\ _Andrew Howroyd_, Aug 04 2018
%o A087003 (PARI) A087003(n) = ((n%2)*moebius(n)); \\ _Antti Karttunen_, Sep 01 2018
%Y A087003 Cf. A006370, A008683, A039956, A292273, A099990, A209229, A099991.
%Y A087003 Cf. A000035 (the Dirichlet inverse), A318657/A318658 (the "Dirichlet Square Root").
%K A087003 sign,mult,easy
%O A087003 1,1
%A A087003 _Labos Elemer_, Oct 02 2003
%E A087003 a(2n) = 0, a(2n+1) = mu(2n+1) added to the name as the new primary definition by _Antti Karttunen_, Sep 18 2017
```
### A091069
```
%I A091069 #34 Nov 18 2025 03:35:07
%S A091069 1,0,-1,0,-1,0,1,0,0,0,-1,0,-1,0,1,0,1,0,-1,0,-1,0,1,0,0,0,0,0,-1,0,1,
%T A091069 0,1,0,-1,0,-1,0,1,0,1,0,-1,0,0,0,1,0,0,0,-1,0,-1,0,1,0,1,0,-1,0,-1,0,
%U A091069 0,0,1,0,-1,0,-1,0,1,0,1,0,0,0,-1,0,1,0,0,0,-1,0,-1,0,1,0,1,0,-1,0,-1,0,1,0,1,0,0,0,-1,0,1,0,1,0,-1,0
%N A091069 Moebius mu sequence for real quadratic extension sqrt(2).
%C A091069 Analog of Moebius mu with sqrt(2) adjoined. Same as mu (A008683) except: 0 for even n (A005843) due to square (extended prime) factor (sqrt(2))^2 and rational primes of the form 8k+/-1 (A001132) factor into conjugate (extended prime) pairs (a + b*sqrt(2))(a - b*sqrt(2)), thus contributing +1 to the product instead of -1; e.g., 7 = (3 + sqrt(2))(3 - sqrt(2)).
%C A091069 For even n a(n) must be 0 because 2 is a square in the quadratic field and so the mu-analog is 0. Of course this coincidentally matches the 0's at even n in A087003. For odd n, from its definition as a product, |a(n)| MUST be the same as that of |mu(n)|. Since from the above we know that A087003(n) is the same as mu(n) at odd n, we can conclude that |a(n)| = |A087003(n)| for all n.
%D A091069 G. H. Hardy and E. M. Wright, An Introduction to the Theory of Numbers, 5th ed., Oxford Univ. Press, 1979, Theorem 256, p. 221.
%H A091069 Antti Karttunen, <a href="/A091069/b091069.txt">Table of n, a(n) for n = 1..20000</a>
%H A091069 Antti Karttunen, <a href="/A091069/a091069.txt">Data supplement: n, a(n) computed for n =  1..100000</a>
%F A091069 a(n) = 0 if n even or has a square prime factor, otherwise Product_{p divides n} (2 - |p mod 8|) where the product is taken over the primes.
%F A091069 From _Jianing Song_, Aug 30 2018: (Start)
%F A091069 Multiplicative with a(p^e) = 0 if p = 2 or e > 1, a(p) = 1 if p == +-1 (mod 8) and -1 if p == +-3 (mod 8).
%F A091069 For squarefree n, a(n) = Kronecker symbol (n, 2) (or (2, n)) = A091337(n). Also for these n, a(n) = A318608(n) if n even or n == 1 (mod 8), otherwise -A318608(n). (End)
%e A091069 a(21) = (-1)*(+1) = -1 because 21 = 3*7 where 3 and 7 are congruent to +3 and -1 mod 8 respectively.
%t A091069 f[2, e_] := 0; f[p_, e_] := If[e == 1, KroneckerSymbol[p, 8], 0]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Nov 18 2025 *)
%o A091069 (PARI)
%o A091069 a(n)=
%o A091069 {
%o A091069     my(r=1, f=factor(n));
%o A091069     for(j=1, #f[, 1], my(p=f[j, 1], e=f[j, 2]);
%o A091069         if(p==2||e>=2, r=0);
%o A091069         if((Mod(p,8)==3||Mod(p,8)==5)&e==1, r*=-1);
%o A091069     );
%o A091069     return(r);
%o A091069 } \\ _Jianing Song_, Aug 30 2018
%Y A091069 Absolute values are the same as those of A087003.
%Y A091069 Cf. A008683 (original Moebius function over the integers), A318608 (Moebius function over Z[sqrt(i)], also having the same absolute value as a(n)).
%Y A091069 Cf. A001132, A005843, A091337.
%K A091069 mult,easy,sign
%O A091069 1,1
%A A091069 _Marc LeBrun_, Dec 17 2003
```

## Candidate 117: A193304 vs A240370 (score 74.5, agree 108, variant raw, family size 27)
Terms: 1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 26, 29, 30, 31, 33, 34, 35, 37, 38, 39, 41, 42, 43

### A193304
```
%I A193304 #31 Mar 15 2025 02:42:41
%S A193304 1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,25,26,29,30,31,33,34,35,37,
%T A193304 38,39,41,42,43,46,47,50,51,53,55,57,58,59,61,62,65,66,67,69,70,71,73,
%U A193304 74,75,77,78,79,82,83,85,86,87,89,91,93,94,95,97,101,102,103,105,106,107,109,110,111,113,114,115,118,119,122,123,125,127,129,130,131,133,134,137,138,139,141,142,143,145,146,149,150,151,154,155,157,158,159,161,163,165,166,167,170
%N A193304 Squarefree numbers multiplied by powers of 5.
%C A193304 Numbers k such that A008683(A132739(k)) is not zero, where A008683 is the Moebius mu function. - _Antti Karttunen_, Jun 21 2014
%H A193304 Antti Karttunen, <a href="/A193304/b193304.txt">Table of n, a(n) for n = 1..10000</a>
%F A193304 a(n) ~ kn with k = 10*Pi^2/63. - _Charles R Greathouse IV_, Apr 16 2015
%p A193304 N:= 1000: # to get all terms <= N
%p A193304 sf:= select(numtheory:-issqrfree,{$1..N}):
%p A193304 map(t -> seq(t*5^i, i=0..floor(log[5](N/t))), sf);
%p A193304 # if using Maple 11 or earlier, uncomment the next line
%p A193304 # sort(convert(%,list)); # _Robert Israel_, Apr 16 2015
%t A193304 lim = 102; sf = Select[Range[lim], SquareFreeQ]; lim5 = 5^Range[0, Log[5, lim]]; Select[Union[Flatten[Outer[Times, sf, lim5]]], # <= lim &]
%o A193304 (PARI) is(n)=issquarefree(n/5^valuation(n,5)) \\ _Charles R Greathouse IV_, Jul 31 2011
%o A193304 (Scheme)
%o A193304 ;; With Antti Karttunen's IntSeq-library.
%o A193304 (define A193304 (NONZERO-POS 1 1 (COMPOSE A008683 A132739)))
%o A193304 ;; Reflecting essentially the above Pari-program, _Antti Karttunen_, Jun 21 2014
%Y A193304 Differs from A240370 for the first time at n=109, where A240370(109)=169, while here it is missing, and a(109)=170.
%Y A193304 Cf. A008683, A132739.
%K A193304 nonn
%O A193304 1,2
%A A193304 _José María Grau Ribas_, Jul 21 2011
```
### A240370
```
%I A240370 #43 Nov 05 2025 15:22:26
%S A240370 1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,25,26,29,30,31,33,34,35,37,
%T A240370 38,39,41,42,43,46,47,50,51,53,55,57,58,59,61,62,65,66,67,69,70,71,73,
%U A240370 74,75,77,78,79,82,83,85,86,87,89,91,93,94,95,97,101,102,103,105,106,107,109,110,111,113,114,115,118,119,122,123,125,127,129,130,131,133,134,137,138,139,141,142,143,145,146,149,150,151,154,155,157,158,159,161,163,165,166,167,169
%N A240370 Positive integers n such that every element in the ring of integers modulo n can be written as the sum of two squares modulo n.
%C A240370 Numbers n such that, if p^2 divides n for any prime p, then p = 1 mod 4.
%C A240370 Equivalently, squarefree numbers times A004613.
%C A240370 Thus, numbers k such that A065338(A057521(k)) = 1. - _Antti Karttunen_, Jun 21 2014
%C A240370 Different from A193304: terms 169, 289, 338, 507, 578, 841, 845, 867, ... are here but not in A193304. - _Michel Marcus_, Jun 20 2014
%C A240370 The asymptotic density of this sequence is 3/(8*K^2) = (3/4) * A243379 = 0.64208..., where K is the Landau-Ramanujan constant (A064533). - _Amiram Eldar_, Dec 19 2020
%H A240370 Antti Karttunen, <a href="/A240370/b240370.txt">Table of n, a(n) for n = 1..10000</a>
%H A240370 Joshua Harrington, Lenny Jones, and Alicia Lamarche, <a href="https://arxiv.org/abs/1404.0187">Representing Integers as the Sum of Two Squares in the Ring Z_n</a>, arXiv:1404.0187 [math.NT], Apr 01 2014 and, <a href="https://cs.uwaterloo.ca/journals/JIS/VOL17/Jones/jones14.html">J. Int. Seq. 17 (2014) # 14.7.4</a>.
%e A240370 In Z_7, 0^2 + 0^2 = 0, 1^2 + 0^2 = 1, 1^2 + 1^2 = 2, 3^2 + 1^2 = 3, 2^2 + 0^2 = 4, 2^2 + 1^2 = 5, 3^2 + 2^2 = 6. Therefore 7 is in the sequence.
%e A240370 In Z_8, there is no way to express 3 as a sum of two squares. Therefore 8 is not in the sequence.
%t A240370 rad[n_] := Times @@ First /@ FactorInteger[n];
%t A240370 a57521[n_] := n/Denominator[n/rad[n]^2];
%t A240370 a65338[n_] := a65338[n] = If[n==1, 1, Mod[p = FactorInteger[n][[1, 1]], 4]* a65338[n/p]];
%t A240370 Select[Range[200], a65338[a57521[#]] == 1&] (* _Jean-François Alcover_, Sep 22 2018, after _Antti Karttunen_ *)
%t A240370 Select[Range[200], AllTrue[FactorInteger[#], Mod[First[#1], 4] == 1 || Last[#1] == 1 &] &] (* _Amiram Eldar_, Dec 19 2020 *)
%o A240370 (PARI) is(n)=my(f=factor(n)); for(i=1,#f~,if(f[i,2]>1 && f[i,1]%4>1, return(0))); 1
%o A240370 (PARI) isok(n) = { if (n < 2, return (0)); if ((n % 4) == 0, return (0)); forprime(q = 2, n, if (((q % 4) == 3) && ((n % q) == 0) && ((n % q^2) == 0), return (0)); ); return (1); } \\ _Michel Marcus_, Jun 08 2014
%o A240370 (Scheme)
%o A240370 ;; With Antti Karttunen's IntSeq-library.
%o A240370 (define A240370 (MATCHING-POS 1 1 (lambda (k) (= 1 (A065338 (A057521 k))))))
%o A240370 ;; _Antti Karttunen_, Jun 21 2014
%Y A240370 The subsequence A240109 is a version not allowing 0.
%Y A240370 Different from A193304.
%Y A240370 Complement of A053443. Subsequence of A192450.
%Y A240370 Cf. A004613, A057521, A064533, A065338, A243379.
%K A240370 nonn
%O A240370 1,2
%A A240370 _Charles R Greathouse IV_, Apr 04 2014
```

## Candidate 118: A052928 vs A346663 (score 74.0, agree 74, variant raw, family size 2)
Terms: 0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22, 24, 24, 26, 26, 28, 28

### A052928
```
%I A052928 #182 Oct 19 2026 09:53:18
%S A052928 0,0,2,2,4,4,6,6,8,8,10,10,12,12,14,14,16,16,18,18,20,20,22,22,24,24,
%T A052928 26,26,28,28,30,30,32,32,34,34,36,36,38,38,40,40,42,42,44,44,46,46,48,
%U A052928 48,50,50,52,52,54,54,56,56,58,58,60,60,62,62,64,64,66,66,68,68,70,70,72,72
%N A052928 The even numbers repeated.
%C A052928 a(n) is also the binary rank of the complete graph K(n). - Alessandro Cosentino (cosenal(AT)gmail.com), Feb 07 2009
%C A052928 Let I=I_n be the n X n identity matrix and P=P_n be the incidence matrix of the cycle (1,2,3,...,n). Then, for n >= 6, a(n) is the number of (0,1) n X n matrices A <= P^(-1)+I+P having exactly two 1's in every row and column with perA=2. - _Vladimir Shevelev_, Apr 12 2010
%C A052928 a(n+2) is the number of symmetry allowed, linearly independent terms at n-th order in the series expansion of the (E+A)xe vibronic perturbation matrix, H(Q) (cf. Eisfeld & Viel). - _Bradley Klee_, Jul 21 2015
%C A052928 The arithmetic function v_2(n,1) as defined in A289187. - _Robert Price_, Aug 22 2017
%C A052928 For n > 1, also the chromatic number of the n X n white bishop graph. - _Eric W. Weisstein_, Nov 17 2017
%C A052928 For n > 2, also the maximum vertex degree of the n-polygon diagonal intersection graph. - _Eric W. Weisstein_, Mar 23 2018
%C A052928 For n >= 2, a(n+2) gives the minimum weight of a Boolean function of algebraic degree at most n-2 whose support contains n linearly independent elements. - _Christof Beierle_, Nov 25 2019
%C A052928 Computed by Wolfram's 1-state 2-symbol Turing machine numbers 5, 829, 924, 926 and others. - _Sean A. Irvine_, Feb 03 2026
%D A052928 C. D. Godsil and G. Royle, Algebraic Graph Theory, Springer, 2001, page 181. - Alessandro Cosentino (cosenal(AT)gmail.com), Feb 07 2009
%D A052928 V. S. Shevelyov (Shevelev), Extension of the Moser class of four-line Latin rectangles, DAN Ukrainy, 3(1992),15-19.
%H A052928 Vincenzo Librandi, <a href="/A052928/b052928.txt">Table of n, a(n) for n = 0..1000</a>
%H A052928 C. Beierle, A. Biryukov and A. Udovenko, <a href="https://doi.org/10.1007/s12095-019-00415-0">On degree-d zero-sum sets of full rank</a>, Cryptography and Communications, November 2019.
%H A052928 W. Eisfeld and A. Viel, <a href="https://doi.org/10.1063/1.1904594">Higher order (A+E)xe pseudo-Jahn-Teller coupling</a>, J. Chem. Phys., 122, 204317 (2005).
%H A052928 Nathan Fox, <a href="https://arxiv.org/abs/1609.06342">Finding Linear-Recurrent Solutions to Hofstadter-Like Recurrences Using Symbolic Computation</a>, arXiv:1609.06342 [math.NT], 2016.
%H A052928 INRIA Algorithms Project, <a href="http://ecs.inria.fr/services/structure?nbr=914">Encyclopedia of Combinatorial Structures 914</a>
%H A052928 J. Sondow and E. W. Weisstein, <a href="https://mathworld.wolfram.com/WallisFormula.html">MathWorld: Wallis Formula</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/ChromaticNumber.html">Chromatic Number</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/DominationNumber.html">Domination Number</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/IndependenceNumber.html">Independence Number</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/Legendre-GaussQuadrature.html">Legendre-Gauss Quadrature</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/MaximumVertexDegree.html">Maximum Vertex Degree</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/PolygonDiagonalIntersectionGraph.html">Polygon Diagonal Intersection Graph</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RandomMatrix.html">Random Matrix</a>.
%H A052928 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/WhiteBishopGraph.html">White Bishop Graph</a>.
%H A052928 Stephen Wolfram, <a href="https://writings.stephenwolfram.com/2026/01/p-vs-np-and-the-difficulty-of-computation-a-ruliological-approach/">P vs. NP and the Difficulty of Computation: A Ruliological Approach</a>, 2026.
%H A052928 <a href="/index/Rec#order_03">Index entries for linear recurrences with constant coefficients</a>, signature (1,1,-1)
%H A052928 <a href="/index/Mo#Molien">Index entries for Molien series</a>
%F A052928 a(n) = 2*floor(n/2).
%F A052928 G.f.: 2*x^2/((-1+x)^2*(1+x)).
%F A052928 a(n) + a(n+1) = 2*n. [Corrected by _Eric W. Weisstein_, Oct 19 2026]
%F A052928 a(n) = n - 1/2 + (-1)^n/2.
%F A052928 a(n) = n + Sum_{k=1..n} (-1)^k. - _William A. Tedeschi_, Mar 20 2008
%F A052928 a(n) = a(n-1) + a(n-2) - a(n-3). - _R. J. Mathar_, Feb 19 2010
%F A052928 a(n) = |A123684(n) - A064455(n)| = A032766(n) - A008619(n-1). - _Jaroslav Krizek_, Mar 22 2011
%F A052928 For n > 0, a(n) = floor(sqrt(n^2+(-1)^n)). - _Francesco Daddi_, Aug 02 2011
%F A052928 a(n) = Sum_{k>=0} A030308(n,k)*b(k) with b(0)=0 and b(k)=2^k for k>0. - _Philippe Deléham_, Oct 19 2011
%F A052928 a(n) = A109613(n) - 1. - _M. F. Hasler_, Oct 22 2012
%F A052928 a(n) = n - (n mod 2). - _Wesley Ivan Hurt_, Jun 29 2013
%F A052928 a(n) = a(a(n-1)) + a(n-a(n-1)) for n>2. - _Nathan Fox_, Jul 24 2016
%F A052928 a(n) = 2*A004526(n). - _Filip Zaludek_, Oct 28 2016
%F A052928 E.g.f.: x*exp(x) - sinh(x). - _Ilya Gutkovskiy_, Oct 28 2016
%F A052928 a(-n) = -a(n+1); a(n) = A005843(A004526(n)). - _Guenther Schrack_, Sep 11 2018
%F A052928 From _Guenther Schrack_, May 29 2019: (Start)
%F A052928 a(b(n)) = b(n) + ((-1)^b(n) - 1)/2 for any sequence b(n) of offset 0.
%F A052928 a(a(n)) = a(n), idempotent.
%F A052928 a(A086970(n)) = A124356(n-1) for n > 1.
%F A052928 a(A000124(n)) = A192447(n+1).
%F A052928 a(n)*a(n+1)/2 = A007590(n), also equals partial sums of a(n).
%F A052928 A007590(a(n)) = 2*A008794(n). (End)
%p A052928 spec := [S,{S=Union(Sequence(Prod(Z,Z)),Prod(Sequence(Z),Sequence(Z)))},unlabeled]: seq(combstruct[count](spec,size=n), n=0..20);
%t A052928 Flatten[Table[{2n, 2n}, {n, 0, 39}]] (* _Alonso del Arte_, Jun 24 2012 *)
%t A052928 (* Alternative: *)
%t A052928 With[{ev=2Range[0,40]},Riffle[ev,ev]] (* _Harvey P. Dale_, May 08 2021 *)
%t A052928 (* Alternative: *)
%t A052928 Table[Round[n + 1/2], {n, -1, 72}] (* _Ed Pegg Jr_, Jul 28 2025 *)
%o A052928 (PARI) a(n)=n\2*2 \\ _Charles R Greathouse IV_, Nov 20 2011
%o A052928 (Magma) [2*Floor(n/2) : n in [0..50]]; // _Wesley Ivan Hurt_, Sep 13 2014
%o A052928 (Haskell)
%o A052928 a052928 = (* 2) . flip div 2
%o A052928 a052928_list = 0 : 0 : map (+ 2) a052928_list
%o A052928 -- _Reinhard Zumkeller_, Jun 20 2015
%Y A052928 Cf. A000034, A000124, A004001, A004526, A005843, A007590, A008619, A008794, A032766, A064455, A099392, A109613, A118266, A123684, A124356, A192442, A289187, A342819.
%Y A052928 First differences: A010673; partial sums: A007590; partial sums of partial sums: A212964(n+1).
%Y A052928 Complement of A109613 with respect to universe A004526. - _Guenther Schrack_, Dec 07 2017
%Y A052928 Is first differences of A099392. Fixed point sequence: A005843. - _Guenther Schrack_, May 30 2019
%Y A052928 For n >= 3, A329822(n) gives the minimum weight of a Boolean function of algebraic degree at most n-3 whose support contains n linearly independent elements. - _Christof Beierle_, Nov 25 2019
%K A052928 nonn,easy,changed
%O A052928 0,3
%A A052928 _INRIA Encyclopedia of Combinatorial Structures_, Jan 25 2000
%E A052928 More terms from _James Sellers_, Jun 05 2000
%E A052928 Removed duplicate of recurrence; corrected original recurrence and g.f. against offset - _R. J. Mathar_, Feb 19 2010
```
### A346663
```
%I A346663 #16 Oct 17 2021 12:07:06
%S A346663 0,0,2,2,4,4,6,6,8,8,10,10,12,12,14,14,16,16,18,18,20,20,22,22,24,24,
%T A346663 26,26,28,28,30,30,32,32,34,34,36,36,38,38,40,40,42,42,44,44,46,46,48,
%U A346663 48,50,50,52,52,54,54,56,56,58,58,60,60,62,62,64,64,66,66,68,68,70,70,72,72
%N A346663 The number of nonreal roots of Sum_{k=0..n} prime(k+1)*x^k.
%C A346663 This agrees with A052928 until n = 2436. a(2436) = 2434 and A052928(2436) = 2436. For n >= 2436 we have a(n) = n-2 for n even and a(n) = n - 1 for n odd, for an as yet undetermined number of n. A052928(n) = n - (n mod 2) for all n. See the paper by W. Clark and M. Shattuck linked to below.
%H A346663 W. Edwin Clark and Mark Shattuck, <a href="https://arxiv.org/abs/2107.05572">The Integer Sequence Transform a --> b where b_n is the Number of Real Roots of the Polynomial a_0 + a_1 x + a_2 x^2 + ... + a_n x^n</a>, arXiv:2107.05572 [math.CO], 2021.
%H A346663 <a href="/index/Se#sequences_which_agree_for_a_long_time">Index entries for sequences which agree for a long time but are different</a>
%Y A346663 Cf. A052928, A346442, A346443, A346444, A346445.
%K A346663 nonn
%O A346663 0,3
%A A346663 _W. Edwin Clark_, Jul 27 2021
```

## Candidate 119: A025657 vs A025686 (score 73.8, agree 107, variant raw, family size 5)
Terms: 0, 0, 1, 0, 1, 0, 2, 1, 0, 2, 1, 3, 0, 2, 1, 3, 0, 2, 4, 1, 3, 0, 2, 4, 1, 3, 0, 5, 2, 4

### A025657
```
%I A025657 #22 Nov 08 2025 09:38:34
%S A025657 0,0,1,0,1,0,2,1,0,2,1,3,0,2,1,3,0,2,4,1,3,0,2,4,1,3,0,5,2,4,1,3,0,5,
%T A025657 2,4,1,6,3,0,5,2,4,1,6,3,0,5,2,7,4,1,6,3,0,5,2,7,4,1,6,3,0,8,5,2,7,4,
%U A025657 1,6,3,0,8,5,2,7,4,1,9,6,3,0,8,5,2,7,4,1,9,6,3,0,8,5,2,10,7,4,1,9,6,3,0,8,5,2,10
%N A025657 Exponent of 6 (value of j) in n-th number of form 3^i*6^j.
%C A025657 Differs from A025686 at a(114).
%H A025657 Amiram Eldar, <a href="/A025657/b025657.txt">Table of n, a(n) for n = 1..10000</a>
%F A025657 a(n) = A122841(A025614(n)). - _Amiram Eldar_, Nov 08 2025
%t A025657 seq[lim_] := SortBy[Flatten[Table[{i, j}, {i, 0, Log[3, lim]}, {j, 0, Log[6, lim/3^i]}], 1], 3^#[[1]]*6^#[[2]] &][[;; , 2]]; seq[10^9] (* _Amiram Eldar_, Nov 08 2025 *)
%Y A025657 Cf. A025614, A025686, A122841.
%Y A025657 A025641 is the exponent of 3 (value of i).
%K A025657 nonn,easy
%O A025657 1,7
%A A025657 _David W. Wilson_
```
### A025686
```
%I A025686 #15 Nov 09 2025 02:44:02
%S A025686 0,0,1,0,1,0,2,1,0,2,1,3,0,2,1,3,0,2,4,1,3,0,2,4,1,3,0,5,2,4,1,3,0,5,
%T A025686 2,4,1,6,3,0,5,2,4,1,6,3,0,5,2,7,4,1,6,3,0,5,2,7,4,1,6,3,0,8,5,2,7,4,
%U A025686 1,6,3,0,8,5,2,7,4,1,9,6,3,0,8,5,2,7,4,1,9,6,3,0,8,5,2,10,7,4,1,9,6,3,0,8,5,2,10
%N A025686 Exponent of 10 (value of j) in n-th number of form 4^i*10^j.
%H A025686 Amiram Eldar, <a href="/A025686/b025686.txt">Table of n, a(n) for n = 1..10000</a>
%F A025686 a(n) = A122840(A025621(n)). - _Amiram Eldar_, Nov 09 2025
%t A025686 seq[lim_] := SortBy[Flatten[Table[{i, j}, {i, 0, Log[4, lim]}, {j, 0, Log10[lim/4^i]}], 1], 4^#[[1]]*10^#[[2]] &][[;; , 2]]; seq[10^11] (* _Amiram Eldar_, Nov 09 2025 *)
%Y A025686 Cf. A025621, A122840.
%Y A025686 A025649 is the exponent of 4.
%Y A025686 Differs from A025657 at a(114).
%K A025686 nonn,easy
%O A025686 1,7
%A A025686 _David W. Wilson_
```

## Candidate 120: A038189 vs A089013 (score 73.8, agree 107, variant drop1, family size 3)
Terms: 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0

### A038189
```
%I A038189 #112 Feb 06 2025 23:08:27
%S A038189 0,0,0,1,0,0,1,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,0,0,
%T A038189 0,1,0,0,1,1,0,0,0,1,1,0,1,1,1,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,0,0,0,1,
%U A038189 0,0,1,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,1,0,0,1,0,0,1,1,0,0,0,1
%N A038189 Bit to left of least significant 1-bit in binary expansion of n.
%C A038189 Characteristic function of A091067.
%C A038189 Image, under the coding i -> floor(i/2), of the fixed point, starting with 0, of the morphism 0 -> 01, 1 -> 02, 2 -> 32, 3 -> 31. - _Jeffrey Shallit_, May 15 2016
%C A038189 Restricted to the positive integers, completely additive modulo 2. - _Peter Munn_, Jun 20 2022
%C A038189 If a(n) is defined as 1-a(-n) for all n<0, then a(n) = a(2*n), a(4*n+1) = 0, a(4*n+3) = 1 for all n in Z. - _Michael Somos_, Oct 05 2024
%D A038189 Jean-Paul Allouche and Jeffrey O. Shallit, Automatic sequences, Cambridge, 2003, sect. 5.1.6
%H A038189 Ivan Panchenko, <a href="/A038189/b038189.txt">Table of n, a(n) for n = 0..10000</a>
%H A038189 Michael Gilleland, <a href="/selfsimilar.html">Some Self-Similar Integer Sequences</a>
%H A038189 <a href="/index/Ch#char_fns">Index entries for characteristic functions</a>
%H A038189 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%H A038189 <a href="/index/Fo#fold">Index entries for sequences obtained by enumerating foldings</a>
%F A038189 a(0) = 0, a(2*n) = a(n) for n>0, a(4*n+1) = 0, a(4*n+3) = 1.
%F A038189 G.f.: Sum_{k>=0} t^3/(1-t^4), where t=x^2^k. Parity of A025480. For n >= 1, a(n) = 1/2 * (1 - (-1)^A025480(n-1)). - _Ralf Stephan_, Jan 04 2004 [index adjusted by _Peter Munn_, Jun 22 2022]
%F A038189 a(n) = 1 if Kronecker(-n,m)=Kronecker(m,n) for all m, otherwise a(n)=0. - _Michael Somos_, Sep 22 2005
%F A038189 a(n) = 1 iff A164677(n) < 0. - _M. F. Hasler_, Aug 06 2015
%F A038189 For n >= 1, a(n) = A065339(n) mod 2. - _Peter Munn_, Jun 20 2022
%F A038189 From _A.H.M. Smeets_, Mar 08 2023: (Start)
%F A038189 a(n+1) = 1 - A014577(n) for n >= 0.
%F A038189 a(n+1) = 2 - A014710(n) for n >= 0.
%F A038189 a(n) = (1 - A034947(n))/2 for n > 0. (End)
%F A038189 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = 1/2. - _Amiram Eldar_, Aug 30 2024
%e A038189 a(6) = 1 since 6 = 110 and bit before rightmost 1 is a 1.
%p A038189 A038189 := proc(n)
%p A038189     option remember;
%p A038189     if n = 0 then
%p A038189         0 ;
%p A038189     elif type(n,'even') then
%p A038189         procname(n/2) ;
%p A038189     elif modp(n,4) = 1 then
%p A038189         0 ;
%p A038189     else
%p A038189         1 ;
%p A038189     end if;
%p A038189 end proc:
%p A038189 seq(A038189(n),n=0..100) ; # _R. J. Mathar_, Mar 30 2018
%t A038189 f[n_] := Block[{id2 = Join[{0}, IntegerDigits[n, 2]]}, While[ id2[[-1]] == 0, id2 = Most@ id2]; id2[[-2]]]; f[0] = 0; Array[f, 105, 0] (* _Robert G. Wilson v_, Apr 14 2009 and fixed Feb 27 2014 *)
%t A038189 f[n_] := f[n] = Switch[Mod[n, 4], 0, f[n/2], 1, 0, 2, f[n/2], 3, 1]; f[0] = 0; Array[f, 105, 0] (* _Robert G. Wilson v_, Apr 14 2009, fixed Feb 27 2014 *)
%t A038189 a[ n_] := If[n==0, 0, Mod[(n/2^IntegerExponent[n, 2]-1)/2, 2]]; (* _Michael Somos_, Oct 05 2024 *)
%o A038189 (C) int a(int n) { return (n & ((n&-n)<<1)) ? 1 : 0; } /* from _Russ Cox_ */
%o A038189 (PARI) {a(n) = if(n==0, 0, ((n/2^valuation(n,2)-1)/2)%2)}; /* _Michael Somos_, Sep 22 2005 */
%o A038189 (PARI) a(n) = if(n<3, 0, prod(m=1,n, kronecker(-n,m)==kronecker(m,n))) /* _Michael Somos_, Sep 22 2005 */
%o A038189 (PARI) A038189(n)=bittest(n,valuation(n,2)+1) \\ _M. F. Hasler_, Aug 06 2015
%o A038189 (PARI) a(n)=my(h=bitand(n,-n));n=bitand(n,h<<1);n!=0; \\ _Joerg Arndt_, Apr 09 2021
%o A038189 (Magma)
%o A038189 function a (n)
%o A038189   if n eq 0 then return 0; // alternatively,  return 1;
%o A038189   else while IsEven(n) do n := n div 2; end while; end if;
%o A038189   return n div 2 mod 2; end function;
%o A038189   nlo := 0; nhi := 32;
%o A038189   [a(n) : n in [nlo..nhi] ]; //  _Fred Lunnon_, Mar 27 2018
%o A038189 (Python)
%o A038189 def A038189(n):
%o A038189     s = bin(n)[2:]
%o A038189     m = len(s)
%o A038189     i = s[::-1].find('1')
%o A038189     return int(s[m-i-2]) if m-i-2 >= 0 else 0 # _Chai Wah Wu_, Apr 08 2021
%o A038189 (Python)
%o A038189 def a(n): return 1 if (n & ((n&-n)<<1)) else 0
%o A038189 print([a(n) for n in range(108)]) # _Michael S. Branicky_, Feb 06 2025 after _Russ Cox_
%Y A038189 Cf. A038190, A065339.
%Y A038189 A014707(n)=a(n+1). A014577(n)=1-a(n+1).
%Y A038189 The following are all essentially the same sequence: A014577, A014707, A014709, A014710, A034947, A038189, A082410. - _N. J. A. Sloane_, Jul 27 2012
%Y A038189 Related sequences A301848, A301849, A301850. - _Fred Lunnon_, Mar 27 2018
%K A038189 nonn,easy,base
%O A038189 0,1
%A A038189 _Fred Lunnon_, Dec 11 1999
%E A038189 More terms from _David W. Wilson_
%E A038189 Definition corrected by _Russ Cox_ and _Ralf Stephan_, Nov 08 2004
```
### A089013
```
%I A089013 #20 Aug 03 2020 02:03:54
%S A089013 1,0,0,1,0,0,1,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,0,0,
%T A089013 0,1,0,0,1,1,0,0,0,1,1,0,1,1,1,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,0,0,0,1,
%U A089013 0,0,1,1,0,0,0,1,1,0,1,1,0,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,1,0,0,1,0,0,1,1,0,0,0,1
%N A089013 a(n) = (A088567(8n) mod 2).
%C A089013 This is just to give a pointer to A088567, A089013 and A014707.
%H A089013 N. J. A. Sloane and J. A. Sellers, <a href="https://arxiv.org/abs/math/0312418">On non-squashing partitions</a>, arXiv:math/0312418 [math.CO], 2003.
%H A089013 N. J. A. Sloane and J. A. Sellers, <a href="https://doi.org/10.1016/j.disc.2004.11.014">On non-squashing partitions</a>, Discrete Math., 294 (2005), 259-274.
%H A089013 <a href="/index/Fo#fold">Index entries for sequences obtained by enumerating foldings</a>
%F A089013 a(0) = 1, a(2*n) = a(n) for n > 0 and a(2*n+1) = (n mod 2) for n >= 0. - _A.H.M. Smeets_, Aug 02 2018
%Y A089013 A038189(n)=a(n) if n>0.
%K A089013 nonn,easy
%O A089013 0,1
%A A089013 _N. J. A. Sloane_, Dec 20 2003
```

## Candidate 121: A118828 vs A118831 (score 73.8, agree 107, variant abs, family size 3)
Terms: 1, -1, 0, -1, -1, 1, 0, 1, 1, -1, 0, -1, -1, 1, 0, 1, 1, -1, 0, -1, -1, 1, 0, 1, 1, -1, 0, -1, -1, 1

### A118828
```
%I A118828 #20 May 21 2026 16:48:39
%S A118828 1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,
%T A118828 -1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,
%U A118828 -1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1,-1,1,0,1,1,-1,0,-1
%N A118828 Numerators of the convergents of the 2-adic continued fraction of zero given by A118827.
%H A118828 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,-1).
%F A118828 Period 8 sequence: [1, -1, 0, -1, -1, 1, 0, 1].
%F A118828 G.f.: (1 - x - x^3)/(1 + x^4).
%F A118828 Assuming offset 0 with a(0) = 1, then a has the g.f. (1 + x - x^2)/(1 + x^4) and a(n) = signum(mods(n+1, 4)*mods(n+1, 8)), where mods(a, b) is the symmetric modulo function. - _Peter Luschny_, Oct 13 2020
%e A118828 For n>=1, convergents A118828(k)/A118829(k) are:
%e A118828 at k = 4*n: -1/(2*A080277(n));
%e A118828 at k = 4*n+1: -1/(2*A080277(n)-1);
%e A118828 at k = 4*n+2: -1/(2*A080277(n)-2);
%e A118828 at k = 4*n-1: 0/(-1)^n.
%e A118828 Convergents begin:
%e A118828 1/1, -1/-2, 0/-1, -1/2, -1/1, 1/0, 0/1, 1/-8,
%e A118828 1/-7, -1/6, 0/-1, -1/10, -1/9, 1/-8, 0/1, 1/-24,
%e A118828 1/-23, -1/22, 0/-1, -1/26, -1/25, 1/-24, 0/1, 1/-32,
%e A118828 1/-31, -1/30, 0/-1, -1/34, -1/33, 1/-32, 0/1, 1/-64, ...
%p A118828 seq(signum(mods(n+1, 4)*mods(n+1, 8)), n=1..100); # _Peter Luschny_, Oct 13 2020
%t A118828 PadRight[{}, 104, {1, -1, 0, -1, -1, 1, 0, 1}] (* _Paolo Xausa_, May 21 2026 *)
%o A118828 (PARI) {a(n)=local(p=+1,q=-2,v=vector(n,i,if(i%2==1,p,q*2^valuation(i/2,2)))); contfracpnqn(v)[1,1]}
%Y A118828 Cf. A118827 (partial quotients), A118829 (denominators).
%K A118828 frac,sign,easy
%O A118828 1,1
%A A118828 _Paul D. Hanna_, May 01 2006
```
### A118831
```
%I A118831 #22 Feb 01 2026 19:06:40
%S A118831 -1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,
%T A118831 1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,
%U A118831 -1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0,-1,1,1,0,1,-1,-1,0
%N A118831 Numerators of the convergents of the 2-adic continued fraction of zero given by A118830.
%H A118831 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,-1).
%F A118831 Period 8 sequence: [ -1,-1,0,-1,1,1,0,1].
%F A118831 G.f.: -x*(1+x+x^3)/(1+x^4). [corrected by _R. J. Mathar_, Jul 22 2009]
%F A118831 a(n) = -a(n-4). - _R. J. Mathar_, Jul 22 2009
%e A118831 For n>=1, convergents A118831(k)/A118832(k) are:
%e A118831 at k = 4*n: 1/(2*A080277(n));
%e A118831 at k = 4*n+1: 1/(2*A080277(n)-1);
%e A118831 at k = 4*n+2: 1/(2*A080277(n)-2);
%e A118831 at k = 4*n-1: 0.
%e A118831 Convergents begin:
%e A118831 -1/1, -1/2, 0/-1, -1/-2, 1/1, 1/0, 0/1, 1/8,
%e A118831 -1/-7, -1/-6, 0/-1, -1/-10, 1/9, 1/8, 0/1, 1/24,
%e A118831 -1/-23, -1/-22, 0/-1, -1/-26, 1/25, 1/24, 0/1, 1/32,
%e A118831 -1/-31, -1/-30, 0/-1, -1/-34, 1/33, 1/32, 0/1, 1/64, ...
%t A118831 LinearRecurrence[{0,0,0,-1},{-1,-1,0,-1},120] (* _Harvey P. Dale_, Feb 01 2026 *)
%o A118831 (PARI) {a(n)=local(p=-1,q=+2,v=vector(n,i,if(i%2==1,p,q*2^valuation(i/2,2)))); contfracpnqn(v)[1,1]}
%Y A118831 Cf. A118830 (partial quotients), A118832 (denominators).
%K A118831 frac,sign
%O A118831 1,1
%A A118831 _Paul D. Hanna_, May 01 2006
```

## Candidate 122: A344696 vs A389087 (score 73.8, agree 107, variant raw, family size 5)
Terms: 1, 1, 1, 7, 1, 1, 1, 5, 13, 1, 1, 7, 1, 1, 1, 31, 1, 13, 1, 7, 1, 1, 1, 5, 31, 1, 10, 7, 1, 1

### A344696
```
%I A344696 #17 May 15 2026 10:09:09
%S A344696 1,1,1,7,1,1,1,5,13,1,1,7,1,1,1,31,1,13,1,7,1,1,1,5,31,1,10,7,1,1,1,
%T A344696 21,1,1,1,91,1,1,1,5,1,1,1,7,13,1,1,31,57,31,1,7,1,10,1,5,1,1,1,7,1,1,
%U A344696 13,127,1,1,1,7,1,1,1,65,1,1,31,7,1,1,1,31,121,1,1,7,1,1,1,5,1,13,1,7,1,1,1,21,1,57,13,217,1,1,1,5,1,1,1,35
%N A344696 a(n) = sigma(n) / gcd(sigma(n), A001615(n)).
%C A344696 This is not multiplicative. The first point where a(m*n) = a(m)*a(n) does not hold for coprime m and n is 108 = 4*27, where a(108) = 35, although a(4) = 7 and a(27) = 10. See A344702.
%H A344696 Antti Karttunen, <a href="/A344696/b344696.txt">Table of n, a(n) for n = 1..10404</a>
%H A344696 Antti Karttunen, <a href="/A344696/a344696.txt">Data supplement: n, a(n) computed for n = 1..65537</a>
%H A344696 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>
%F A344696 a(n) = A000203(n) / A344695(n).
%o A344696 (PARI)
%o A344696 A001615(n) = if(1==n,n, my(f=factor(n)); prod(i=1, #f~, f[i, 1]^f[i, 2] + f[i, 1]^(f[i, 2]-1))); \\ After code in A001615
%o A344696 A344696(n) = { my(u=sigma(n)); (u/gcd(u,A001615(n))); };
%Y A344696 Cf. A000203, A001615, A005117 (positions of ones), A344695, A344697, A344698, A344702.
%Y A344696 Cf. also A344756.
%K A344696 nonn
%O A344696 1,4
%A A344696 _Antti Karttunen_, May 26 2021
```
### A389087
```
%I A389087 #13 May 15 2026 10:09:42
%S A389087 1,1,1,7,1,1,1,5,13,1,1,7,1,1,1,31,1,13,1,7,1,1,1,5,31,1,10,7,1,1,1,
%T A389087 21,1,1,1,91,1,1,1,5,1,1,1,7,13,1,1,31,57,31,1,7,1,10,1,5,1,1,1,7,1,1,
%U A389087 13,127,1,1,1,7,1,1,1,65,1,1,31,7,1,1,1,31,121,1,1,7,1,1,1,5,1,13,1,7,1,1,1,21,1,57,13,217,1,1,1,5,1,1,1,70
%N A389087 Numerator of ratio sigma(n) / A048250(n), where sigma is the sum of divisors and A048250 is the sum of squarefree divisors.
%C A389087 First differs from A348504 at n = 72 and from A344696 at n = 108.
%C A389087 The sequence of fractions r(n) = A000203(n)/A048250(n), in their reduced form A389087(n)/A389089(n), begins as: 1, 1, 1, 7/3, 1, 1, 1, 5, 13/4, 1, 1, 7/3, 1, 1, 1, 31/3, 1, 13/4, 1, 7/3, 1, 1, 1, 5, 31/6, 1, 10, 7/3, 1, 1, 1, 21, 1, 1, 1, 91/12, 1, 1, 1, 5, etc. As both A000203 and A048250 are multiplicative sequences, r(n) is also. Thus, if gcd(x,y)=1, then r(x*y) = r(x)*r(y), as for example, r(196) = r(4)*r(49) = 7/3 * 57/8 = 133/8. However, as an integer sequence A389087 alone is not multiplicative, as for example a(4) = 7, a(49) = 57, but a(196) = 133 <> 7*57.
%H A389087 Antti Karttunen, <a href="/A389087/b389087.txt">Table of n, a(n) for n = 1..65537</a>
%H A389087 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>.
%F A389087 a(n) = A000203(n) / A389080(n).
%t A389087 a[n_]:=Numerator[DivisorSigma[1,n]/Total[Select[Divisors[n],SquareFreeQ]]];Array[a,100] (* _James C. McMahon_, Oct 07 2025 *)
%o A389087 (PARI)
%o A389087 A048250(n) = factorback(apply(p -> p+1,factor(n)[,1]));
%o A389087 A389087(n) = numerator(sigma(n)/A048250(n));
%Y A389087 Cf. A000203, A048250, A389080, A389089 (denominators).
%Y A389087 Cf. also A344696, A348504, A389074.
%K A389087 nonn,frac
%O A389087 1,4
%A A389087 _Antti Karttunen_, Oct 03 2025
```

## Candidate 123: A007094 vs A039155 (score 73.6, agree 64, variant raw, family size 10)
Terms: 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35

### A007094
```
%I A007094 M0498 #61 Jan 11 2025 02:38:47
%S A007094 0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,20,21,22,23,24,25,26,27,30,
%T A007094 31,32,33,34,35,36,37,40,41,42,43,44,45,46,47,50,51,52,53,54,55,56,57,
%U A007094 60,61,62,63,64,65,66,67,70,71,72,73,74,75,76,77,100,101,102,103,104,105,106,107,110,111
%N A007094 Numbers in base 8.
%D A007094 Jan Gullberg, Mathematics from the Birth of Numbers, W. W. Norton & Co., NY & London, 1997, §2.8 Binary, Octal, Hexadecimal, p. 64.
%D A007094 N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence).
%H A007094 Nathaniel Johnston, <a href="/A007094/b007094.txt">Table of n, a(n) for n = 0..10000</a>
%H A007094 Wikipedia, <a href="http://www.wikipedia.org/wiki/Octal">Octal</a>.
%H A007094 Robert G. Wilson v, <a href="/A007088/a007088.pdf">Letter to N. J. A. Sloane, Sep. 1992</a>
%H A007094 <a href="/index/Ar#10-automatic">Index entries for 10-automatic sequences</a>.
%F A007094 a(0) = 0; a(n) = 10*a(n/8) if n == 0 (mod 8); a(n) = a(n-1) + 1 otherwise. - _Benoit Cloitre_, Dec 22 2002
%F A007094 G.f.: sum(d>=0, 10^d*(x^(8^d) +2*x^(2*8^d) +3*x^(3*8^d) +4*x^(4*8^d) +5*x^(5*8^d) +6*x^(6*8^d) +7*x^(7*8^d)) * (1-x^(8^d)) / ((1-x^(8^(d+1)))*(1-x))). - _Robert Israel_, Aug 03 2014
%p A007094 A007094 := proc(n) local l: if(n=0)then return 0: fi: l:=convert(n,base,8): return op(convert(l,base,10,10^nops(l))): end: seq(A007094(n), n=0..66); # _Nathaniel Johnston_, May 06 2011
%t A007094 Table[FromDigits[IntegerDigits[n, 8]], {n, 0, 70}]
%o A007094 (PARI) a(n)=if(n<1,0,if(n%8,a(n-1)+1,10*a(n/8)))
%o A007094 (PARI) apply( A007094(n)=fromdigits(digits(n,8)), [0..77]) \\ _M. F. Hasler_, Nov 18 2019
%o A007094 (Haskell)
%o A007094 a007094 0 = 0
%o A007094 a007094 n = 10 * a007094 n' + m where (n', m) = divMod n 8
%o A007094 -- _Reinhard Zumkeller_, Aug 29 2013
%o A007094 (Python)
%o A007094 def a(n): return int(oct(n)[2:])
%o A007094 print([a(n) for n in range(74)]) # _Michael S. Branicky_, Jun 28 2021
%Y A007094 Cf. A057104; A000042 (base 1), A007088 (base 2), A007089 (base 3), A007090 (base 4), A007091 (base 5), A007092 (base 6), A007093 (base 7), A007095 (base 9).
%K A007094 nonn,easy,base
%O A007094 0,3
%A A007094 _N. J. A. Sloane_, _Robert G. Wilson v_
```
### A039155
```
%I A039155 #15 Jun 26 2021 01:52:51
%S A039155 0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,20,21,22,23,24,25,26,27,30,
%T A039155 31,32,33,34,35,36,37,40,41,42,43,44,45,46,47,50,51,52,53,54,55,56,57,
%U A039155 60,61,62,63,64,65,66,67,70,71,72,73,74,75,76,77,89,98,100,101,102
%N A039155 Numbers whose base-10 representation has the same number of 8's and 9's.
%t A039155 Select[Range[0,110], DigitCount[#,10,8] == DigitCount[#,10,9]&] (* _Harvey P. Dale_, Jan 13 2013 *)
%K A039155 nonn,base,easy
%O A039155 1,3
%A A039155 _Olivier Gérard_
```

## Candidate 124: A088828 vs A348741 (score 73.6, agree 64, variant raw, family size 3)
Terms: 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 51, 53, 55, 57, 59, 61, 63, 65, 67

### A088828
```
%I A088828 #75 Jun 19 2024 10:46:53
%S A088828 3,5,7,11,13,15,17,19,21,23,27,29,31,33,35,37,39,41,43,45,47,51,53,55,
%T A088828 57,59,61,63,65,67,69,71,73,75,77,79,83,85,87,89,91,93,95,97,99,101,
%U A088828 103,105,107,109,111,113,115,117,119,123,125,127,129,131,133,135,137,139
%N A088828 Nonsquare positive odd numbers.
%C A088828 Odd numbers with even abundance: primes and some composites too.
%C A088828 Odd numbers with odd abundance are in A016754. Even numbers with odd abundance are in A088827. Even numbers with even abundance are in A088829.
%C A088828 Or, odd numbers without the squares. - _Gerald Hillier_, Apr 12 2009
%H A088828 Amiram Eldar, <a href="/A088828/b088828.txt">Table of n, a(n) for n = 1..10000</a>
%F A088828 a(n) = 2*n + s - ((s+1) mod 2) where s = round(sqrt(2*n-1)). - _Gerald Hillier_, Apr 15 2009
%F A088828 A005408 SETMINUS A016754. - _R. J. Mathar_, Jun 16 2018
%F A088828 a(n) = 2*(n+h) + 1 where h = floor((1/4)*(sqrt(8*n) - 1)) is the largest value such that A014105(h) < n. - _John Tyler Rascoe_, Jul 05 2022
%e A088828 n = p prime, abundance = 1 - p = even and negative;
%e A088828 n = 21, sigma = 1 + 3 + 7 + 21 = 32, abundance = 32 - 42 = -20.
%t A088828 Do[s=DivisorSigma[1, n]-2*n; If[ !OddQ[s]&&OddQ[n], Print[{n, s}]], {n, 1, 1000}]
%t A088828 Select[Range[1, 500, 2], EvenQ[DivisorSigma[1, #] - 2 #] &] (* _Vladimir Joseph Stephan Orlovsky_, Apr 15 2011 *)
%o A088828 (Magma) [ n: n in [1..140 by 2] | IsEven(SumOfDivisors(n)-2*n) ]; // _Klaus Brockhaus_, Apr 15 2009
%o A088828 (PARI) isok(n) = (n>0) && (n % 2) && ! issquare(n); \\ _Michel Marcus_, Aug 28 2013
%o A088828 (Python)
%o A088828 from itertools import count, islice
%o A088828 from sympy.ntheory.primetest import is_square
%o A088828 def A088828_gen(startvalue=1): # generator of terms >= startvalue
%o A088828     return filter(lambda n:not is_square(n),count(max(startvalue+(startvalue&1^1),1),2))
%o A088828 A088828_list = list(islice(A088828_gen(),30)) # _Chai Wah Wu_, Jul 06 2023
%o A088828 (Python)
%o A088828 from math import isqrt
%o A088828 def A088828(n): return (s:=(m:=isqrt(k:=(n<<1)-1))+(k-m*(m+1)>=1))+k+(s&1) # _Chai Wah Wu_, Jun 19 2024
%Y A088828 Cf. A005408, A014105, A016754, A088827, A088829, A157502.
%K A088828 nonn,easy
%O A088828 1,1
%A A088828 _Labos Elemer_, Oct 28 2003
%E A088828 Entry revised by _N. J. A. Sloane_, Jan 31 2014 at the suggestion of _Omar E. Pol_
```
### A348741
```
%I A348741 #19 Nov 30 2024 23:46:54
%S A348741 3,5,7,11,13,15,17,19,21,23,27,29,31,33,35,37,39,41,43,45,47,51,53,55,
%T A348741 57,59,61,63,65,67,69,71,73,75,77,79,83,85,87,89,91,93,95,97,99,101,
%U A348741 103,105,107,109,111,113,115,117,119,123,125,127,129,131,133,135,137,139,141,143,145,147,149,151,153,155,157
%N A348741 Odd numbers k for which A161942(k) < k, where A161942 is the odd part of sigma.
%C A348741 Differs from A088828 for the first time at n=1080, where a(1080) = 2207, while A088828(1080) = 2205 = A348743(1), the value which is missing from this sequence.
%H A348741 Antti Karttunen, <a href="/A348741/b348741.txt">Table of n, a(n) for n = 1..16291</a>
%H A348741 <a href="/index/Si#SIGMAN">Index entries for sequences related to sigma(n)</a>
%t A348741 odd[n_] := n/2^IntegerExponent[n, 2]; Select[Range[1, 150, 2], odd[DivisorSigma[1, #]] < # &] (* _Amiram Eldar_, Nov 02 2021 *)
%o A348741 (PARI)
%o A348741 A000265(n) = (n >> valuation(n, 2));
%o A348741 isA348741(n) = ((n%2)&&A000265(sigma(n))<n);
%Y A348741 Setwise difference A088828 \ A348743.
%Y A348741 Cf. A161942, A348742 (complement among the odd numbers).
%Y A348741 Cf. also A348738, A348753, A348931.
%K A348741 nonn
%O A348741 1,1
%A A348741 _Antti Karttunen_, Nov 02 2021
```

## Candidate 125: A213222 vs A265283 (score 73.6, agree 64, variant drop2, family size 3)
Terms: 3, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18, 20, 20, 22, 22, 24, 24, 26, 26, 28, 28, 30, 30, 32

### A213222
```
%I A213222 #38 May 30 2026 16:40:37
%S A213222 3,4,4,6,6,8,8,10,10,12,12,14,14,16,16,18,18,20,20,22,22,24,24,26,26,
%T A213222 28,28,30,30,32,32,34,34,36,36,38,38,40,40,42,42,44,44,46,46,48,48,50,
%U A213222 50,52,52,54,54,56,56,58,58,60,60,62,62,64,64,66,66,68,68,70,70,72,72,74,74,76,76,78,78,80,80,82,82,84
%N A213222 Minimum number of distinct slopes formed by n noncollinear points in the plane.
%C A213222 Scott formulated the problem (on the basis of a similar problem of Erdős), gave bounds, and conjectured the formula which Unger later proved.
%C A213222 Also the edge chromatic number of the n-polygon diagonal intersection graph. - _Eric W. Weisstein_, Mar 23 2018
%D A213222 Martin Aigner and Gunter M. Ziegler, Proofs from THE BOOK, Second Edition, Springer-Verlag, Berlin, 2000. Chapter 10.
%H A213222 Vincenzo Librandi, <a href="/A213222/b213222.txt">Table of n, a(n) for n = 3..1000</a>
%H A213222 J. E. Goodman and R. Pollack, <a href="https://doi.org/10.1016/0097-3165(80)90011-4">On the combinatorial classification of nondegenerate configurations in the plane</a>, J. Combin. Theory Ser. A, 29 (1980), pp. 220-235.
%H A213222 Giovanni Resta, <a href="/A213222/a213222.png">Illustration of terms a(3)-a(7)</a>
%H A213222 P. R. Scott, <a href="https://www.jstor.org/stable/2317384">On the sets of directions determined by n points</a>, The American Mathematical Monthly 77:5 (1970), pp. 502-505.
%H A213222 Peter Ungar, <a href="https://doi.org/10.1016/0097-3165(82)90045-0">2N noncollinear points determine at least 2N directions</a>, Journal of Combinatorial Theory, Series A, 33:3 (1982), pp. 343-347.
%H A213222 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/EdgeChromaticNumber.html">Edge Chromatic Number</a>
%H A213222 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/PolygonDiagonalIntersectionGraph.html">Polygon Diagonal Intersection Graph</a>
%H A213222 <a href="/index/Rec#order_03">Index entries for linear recurrences with constant coefficients</a>, signature (1,1,-1).
%F A213222 a(n) = 2*floor(n/2) for n > 3.
%F A213222 G.f.: x^3*(3+x-3*x^2+x^3)/((1+x)*(1-x)^2). [_Bruno Berselli_, Mar 04 2013]
%p A213222 A213222:=n->`if`(n = 3, 3, 2*floor(n/2)); seq(A213222(n), n=3..100); # _Wesley Ivan Hurt_, Mar 28 2014
%t A213222 CoefficientList[Series[(3 + x - 3 x^2 + x^3)/((1 + x) (1 - x)^2), {x, 0, 100}], x] (* _Vincenzo Librandi_, Mar 29 2014 *)
%t A213222 LinearRecurrence[{1,1,-1},{3,4,4,6},100] (* _Harvey P. Dale_, Dec 29 2024 *)
%o A213222 (PARI) a(n)=if(n>3,n\2*2,3)
%o A213222 (Magma) [2*Floor(n/2): n in [3..100]]; // _Vincenzo Librandi_, Mar 29 2014
%Y A213222 Cf. A000769, A000755, A219760.
%Y A213222 Cf. A000217 (maximum number of slopes, with offset 1).
%K A213222 nonn,easy
%O A213222 3,1
%A A213222 _Charles R Greathouse IV_, Mar 02 2013
```
### A265283
```
%I A265283 #29 Feb 16 2025 08:33:27
%S A265283 1,3,4,6,6,8,8,10,10,12,12,14,14,16,16,18,18,20,20,22,22,24,24,26,26,
%T A265283 28,28,30,30,32,32,34,34,36,36,38,38,40,40,42,42,44,44,46,46,48,48,50,
%U A265283 50,52,52,54,54,56,56,58,58,60,60,62,62,64,64,66,66,68
%N A265283 Number of ON (black) cells in the n-th iteration of the "Rule 94" elementary cellular automaton starting with a single ON (black) cell.
%C A265283 From _Gus Wiseman_, Apr 13 2019: (Start)
%C A265283 Also the number of integer partitions of n + 3 such that lesser of the maximum part and the number of parts is 2. The Heinz numbers of these partitions are given by A325229. For example, the a(0) = 1 through a(7) = 10 partitions are:
%C A265283   (21)  (22)   (32)    (33)     (43)      (44)       (54)        (55)
%C A265283         (31)   (41)    (42)     (52)      (53)       (63)        (64)
%C A265283         (211)  (221)   (51)     (61)      (62)       (72)        (73)
%C A265283                (2111)  (222)    (2221)    (71)       (81)        (82)
%C A265283                        (2211)   (22111)   (2222)     (22221)     (91)
%C A265283                        (21111)  (211111)  (22211)    (222111)    (22222)
%C A265283                                           (221111)   (2211111)   (222211)
%C A265283                                           (2111111)  (21111111)  (2221111)
%C A265283                                                                  (22111111)
%C A265283                                                                  (211111111)
%C A265283 (End)
%D A265283 S. Wolfram, A New Kind of Science, Wolfram Media, 2002; p. 55.
%H A265283 Robert Price, <a href="/A265283/b265283.txt">Table of n, a(n) for n = 0..999</a>
%H A265283 FindStat, <a href="http://www.findstat.org/StatisticsDatabase/St000533">St000533: The maximal number of non-attacking rooks on a Ferrers shape</a>
%H A265283 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/ElementaryCellularAutomaton.html">Elementary Cellular Automaton</a>
%H A265283 <a href="/index/Ce#cell">Index entries for sequences related to cellular automata</a>
%H A265283 <a href="https://oeis.org/wiki/Index_to_Elementary_Cellular_Automata">Index to Elementary Cellular Automata</a>
%F A265283 Conjectures from _Colin Barker_, Dec 07 2015 and Apr 16 2019: (Start)
%F A265283 a(n) = (5-(-1)^n+2*n)/2 = A213222(n+3) for n>1.
%F A265283 a(n) = n+2 for n>1 and even.
%F A265283 a(n) = n+3 for n>1 and odd.
%F A265283 a(n) = a(n-1) + a(n-2) - a(n-3) for n>2.
%F A265283 G.f.: (1+2*x-x^4) / ((1-x)^2*(1+x)).
%F A265283 (End)
%e A265283 From _Michael De Vlieger_, Dec 14 2015: (Start)
%e A265283 First 12 rows, replacing "0" with "." for better visibility of ON cells, followed by the total number of 1's per row:
%e A265283                         1                          =  1
%e A265283                       1 1 1                        =  3
%e A265283                     1 1 . 1 1                      =  4
%e A265283                   1 1 1 . 1 1 1                    =  6
%e A265283                 1 1 . 1 . 1 . 1 1                  =  6
%e A265283               1 1 1 . 1 . 1 . 1 1 1                =  8
%e A265283             1 1 . 1 . 1 . 1 . 1 . 1 1              =  8
%e A265283           1 1 1 . 1 . 1 . 1 . 1 . 1 1 1            = 10
%e A265283         1 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 1          = 10
%e A265283       1 1 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 1 1        = 12
%e A265283     1 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 1      = 12
%e A265283   1 1 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 1 1    = 14
%e A265283 1 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 . 1 1  = 14
%e A265283 (End)
%t A265283 rule = 94; rows = 30; Table[Total[Table[Take[CellularAutomaton[rule, {{1},0},rows-1,{All,All}][[k]], {rows-k+1, rows+k-1}], {k,1,rows}][[k]]], {k,1,rows}]
%t A265283 Total /@ CellularAutomaton[94, {{1}, 0}, 65] (* _Michael De Vlieger_, Dec 14 2015 *)
%Y A265283 Column k = 2 of A325227.
%Y A265283 Cf. A004526, A051924, A118102, A263297, A325193, A325225, A325228, A325229, A325232.
%K A265283 nonn,easy
%O A265283 0,2
%A A265283 _Robert Price_, Dec 06 2015
```

## Candidate 126: A099564 vs A276153 (score 73.1, agree 106, variant raw, family size 4)
Terms: 0, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4

### A099564
```
%I A099564 #19 Aug 23 2016 12:39:31
%S A099564 0,1,1,1,2,2,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,1,1,1,1,
%T A099564 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,
%U A099564 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3
%N A099564 a(0) = 0; for n > 0, a(n) = final nonzero number in the sequence n, f(n,2), f(f(n,2),3), f(f(f(n,2),3),4),..., where f(n,d)=Floor(n/F(d+1)), with F denoting the Fibonacci numbers (A000045).
%C A099564 Records in {a(n)} are given in A099565.
%C A099564 a(n) gives the most significant digit of n when written in "base A003266", like A099563 and A276153 give the most significant digit in bases A000142 and A002110 respectively. - _Antti Karttunen_, Aug 23 2016
%H A099564 Antti Karttunen, <a href="/A099564/b099564.txt">Table of n, a(n) for n = 0..3120</a>
%o A099564 (Scheme)
%o A099564 (define (A099564 n) (let loop ((n n) (i 3)) (let* ((f (A000045 i)) (dig (modulo n f)) (next-n (/ (- n dig) f))) (if (zero? next-n) dig (loop next-n (+ 1 i))))))
%o A099564 ;; Standalone version:
%o A099564 (define (A099564 n) (let loop ((n n) (f1 1) (f2 2)) (let* ((dig (modulo n f2)) (next-n (/ (- n dig) f2))) (if (zero? next-n) dig (loop next-n f2 (+ f1 f2))))))
%o A099564 ;; _Antti Karttunen_, Aug 23 2016
%Y A099564 Cf. A000045, A003266, A099565 (positions of records).
%Y A099564 Differs from A099563 for the first time at n=24.
%Y A099564 Differs from A276153 for the first time at n=210, where a(210)=7, while A276153(210)=1.
%K A099564 nonn
%O A099564 0,5
%A A099564 _John W. Layman_, Oct 22 2004
%E A099564 a(0) = 0 prepended and the name corrected by _Antti Karttunen_, Aug 23 2016
```
### A276153
```
%I A276153 #14 Aug 31 2016 20:54:03
%S A276153 0,1,1,1,2,2,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,1,1,1,1,
%T A276153 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,
%U A276153 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4
%N A276153 The most significant digit when n is written in primorial base (A049345).
%H A276153 Antti Karttunen, <a href="/A276153/b276153.txt">Table of n, a(n) for n = 0..30030</a>
%H A276153 <a href="/index/Pri#primorialbase">Index entries for sequences related to primorial base</a>
%F A276153 a(n) = A071178(A276086(n)).
%e A276153 For n=24, which is "400" in primorial base (as 24 = 4*(3*2*1) + 0*(2*1) + 0*1, see A049345), the most significant digit is 4, thus a(24) = 4.
%e A276153 For n=210, which is "10000" in primorial base (as 210 = A002110(4) = 7*5*3*2*1), the most significant digit is 1, thus a(210) = 1.
%e A276153 For n=2100, which could be written "A0000" in primorial base (where A stands for digit "ten", as 2100 = 10*A002110(4)), the most significant value holder is thus 10 and a(2100) = 10. (The first point where this sequence attains a value larger than 9).
%t A276153 nn = 120; Table[First@ IntegerDigits[n, MixedRadix[Reverse@ Prime@ Range@ PrimePi@ nn]], {n, 0, nn}] (* _Michael De Vlieger_, Aug 25 2016, Version 10.2 *)
%o A276153 (Scheme) (define (A276153 n) (let loop ((n n) (i 1)) (let* ((p (A000040 i)) (dig (modulo n p)) (next-n (/ (- n dig) p))) (if (zero? next-n) dig (loop next-n (+ 1 i))))))
%Y A276153 Cf. A000040, A002110, A049345, A071178, A276086.
%Y A276153 Differs from A099563 for the first time at n=24.
%Y A276153 Differs from A099564 for the first time at n=210, where a(210)=1, while A099564(210)=7.
%K A276153 nonn,base
%O A276153 0,5
%A A276153 _Antti Karttunen_, Aug 22 2016
```

## Candidate 127: A276150 vs A341513 (score 73.1, agree 106, variant raw, family size 4)
Terms: 0, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 4, 2, 3, 3, 4, 4, 5, 3, 4, 4, 5, 5, 6, 4, 5, 5, 6, 6, 7

### A276150
```
%I A276150 #66 Sep 11 2025 21:41:27
%S A276150 0,1,1,2,2,3,1,2,2,3,3,4,2,3,3,4,4,5,3,4,4,5,5,6,4,5,5,6,6,7,1,2,2,3,
%T A276150 3,4,2,3,3,4,4,5,3,4,4,5,5,6,4,5,5,6,6,7,5,6,6,7,7,8,2,3,3,4,4,5,3,4,
%U A276150 4,5,5,6,4,5,5,6,6,7,5,6,6,7,7,8,6,7,7,8,8,9,3,4,4,5,5,6,4,5,5,6,6,7,5,6,6,7,7,8,6,7,7,8,8,9,7,8,8,9,9,10,4
%N A276150 Sum of digits when n is written in primorial base (A049345); minimal number of primorials (A002110) that add to n.
%C A276150 The sum of digits of n in primorial base is odd if n is 1 or 2 (mod 4) and even if n is 0 or 3 (mod 4). Proof: primorials are 1 or 2 (mod 4) and a(n) can be constructed via the greedy algorithm. So if n = 4k + r where 0 <= r < 4, 4k needs an even number of primorials and r needs hammingweight(r) = A000120(r) primorials. Q.E.D. - _David A. Corneth_, Feb 27 2019
%H A276150 Antti Karttunen, <a href="/A276150/b276150.txt">Table of n, a(n) for n = 0..30030</a>
%H A276150 <a href="/index/Pri#primorialbase">Index entries for sequences related to primorial base</a>
%F A276150 a(n) = 1 + a(A276151(n)) = 1 + a(n-A002110(A276084(n))), a(0) = 0.
%F A276150 or for n >= 1: a(n) = 1 + a(n-A260188(n)).
%F A276150 Other identities and observations. For all n >= 0:
%F A276150 a(n) = A001222(A276086(n)) = A001222(A278226(n)).
%F A276150 a(n) >= A371091(n) >= A267263(n).
%F A276150 From _Antti Karttunen_, Feb 27 2019: (Start)
%F A276150 a(n) = A000120(A277022(n)).
%F A276150 a(A283477(n)) = A324342(n).
%F A276150 (End)
%F A276150 a(n) = A373606(n) + A373607(n). - _Antti Karttunen_, Jun 19 2024
%e A276150 For n=24, which is "400" in primorial base (as 24 = 4*(3*2*1) + 0*(2*1) + 0*1, see A049345), the sum of digits is 4, thus a(24) = 4.
%t A276150 nn = 120; b = MixedRadix[Reverse@ Prime@ NestWhileList[# + 1 &, 1, Times @@ Prime@ Range[# + 1] <= nn &]]; Table[Total@ IntegerDigits[n, b], {n, 0, nn}] (* Version 10.2, or *)
%t A276150 nn = 120; f[n_] := Block[{a = {{0, n}}}, Do[AppendTo[a, {First@ #, Last@ #} &@ QuotientRemainder[a[[-1, -1]], Times @@ Prime@ Range[# - i]]], {i, 0, #}] &@ NestWhile[# + 1 &, 0, Times @@ Prime@ Range[# + 1] <= n &]; Rest[a][[All, 1]]]; Table[Total@ f@ n, {n, 0, 120}] (* _Michael De Vlieger_, Aug 26 2016 *)
%o A276150 (Scheme) ;; Two versions.
%o A276150 (definec (A276150 n) (if (zero? n) 0 (+ 1 (A276150 (- n (A002110 (A276084 n)))))))
%o A276150 (define (A276150 n) (A001222 (A276086 n)))
%o A276150 (Python)
%o A276150 from sympy import prime, primefactors
%o A276150 def Omega(n): return 0 if n==1 else Omega(n//primefactors(n)[0]) + 1
%o A276150 def a276086(n):
%o A276150     i=0
%o A276150     m=pr=1
%o A276150     while n>0:
%o A276150         i+=1
%o A276150         N=prime(i)*pr
%o A276150         if n%N!=0:
%o A276150             m*=(prime(i)**((n%N)/pr))
%o A276150             n-=n%N
%o A276150         pr=N
%o A276150     return m
%o A276150 def a(n): return Omega(a276086(n))
%o A276150 print([a(n) for n in range(201)]) # _Indranil Ghosh_, Jun 23 2017
%o A276150 (PARI) A276150(n) = { my(s=0, p=2, d); while(n, d = (n%p); s += d; n = (n-d)/p; p = nextprime(1+p)); (s); }; \\ _Antti Karttunen_, Feb 27 2019
%Y A276150 Cf. A000120, A001222, A002110, A049345, A053589, A235168, A260188, A267263, A276084, A276086, A276151, A277022, A278226, A283477, A319713, A319715 (inverse Möbius transform), A321683, A324342, A324382, A324383, A324386, A324387, A371091, A373605, A373606, A373607.
%Y A276150 Cf. A333426 [k such that a(k)|k], A339215 [numbers not of the form x+a(x) for any x], A358977 [k such that gcd(k, a(k)) = 1].
%Y A276150 Cf. A338835, A366693.
%Y A276150 Cf. A014601, A042963 (positions of even and odd terms), A343048 (positions of records).
%Y A276150 Differs from analogous A034968 for the first time at n=24.
%K A276150 nonn,look,base
%O A276150 0,4
%A A276150 _Antti Karttunen_, Aug 22 2016
```
### A341513
```
%I A341513 #13 Feb 24 2021 08:18:56
%S A341513 0,1,1,2,2,3,1,2,2,3,3,4,2,3,3,4,4,5,3,4,4,5,5,6,4,5,5,6,6,7,1,2,2,3,
%T A341513 3,4,2,3,3,4,4,5,3,4,4,5,5,6,4,5,5,6,6,7,5,6,6,7,7,8,2,3,3,4,4,5,3,4,
%U A341513 4,5,5,6,4,5,5,6,6,7,5,6,6,7,7,8,6,7,7,8,8,9,3,4,4,5,5,6,4,5,5,6,6,7,5,6,6,7
%N A341513 Sum of digits in A097801-base.
%C A341513 A097801-base uses values 1, 2, 2*3, 2*3*5, 2*3*5*7, 2*3*5*7*9, 2*3*5*7*9*11, 2*3*5*7*9*11*13, 2*3*5*7*9*11*13*15, ..., for its digit-positions, instead of primorials (A002110), thus up to 1889 = 2*3*5*7*9 - 1 = 9*A002110(4) - 1 its representation is identical with the primorial base A049345. Thus this sequence differs from A276150 for the first time at n=1890, where a(1890)=1, while A276150(1890)=9, as 1890 = 9*A002110(4).
%H A341513 Antti Karttunen, <a href="/A341513/b341513.txt">Table of n, a(n) for n = 0..65537</a>
%e A341513 In A097801-base, where the digit-positions are given by 1 and the terms of A097801 from its term a(1) onward: 2, 6, 30, 210, 1890, 20790, 270270, 4054050, ..., number 29 is expressed as "421" as 29 = 4*6 + 2*2 + 1*1, thus a(29) = 4+2+1 = 7. In the same base, number 30 is expressed as "1000" as 30 = 1*30, thus a(30) = 1, and number 1890 = 2*3*5*7*9 is expressed as "100000", thus a(1890) = 1 also.
%t A341513 Block[{nn = 105, b}, b = MixedRadix@ NestWhile[Prepend[#1, 2 #2 - 1] & @@ {#, Length[#] + 1} &, {2}, Times @@ # < nn &]; Array[Total@ IntegerDigits[#, b] &, nn + 1, 0]] (* _Michael De Vlieger_, Feb 23 2021 *)
%o A341513 (PARI) A341513(n) = { my(u=0,m=2,k=3); while(n, u += n%m; n \= m; m = k; k += 2); (u); };
%Y A341513 Cf. A097801, A341356 (most significant digit in the same base).
%Y A341513 Cf. also A002110, A049345, A276150.
%K A341513 nonn,base
%O A341513 0,4
%A A341513 _Antti Karttunen_, Feb 23 2021
```

## Candidate 128: A292592 vs A332996 (score 73.1, agree 106, variant raw, family size 3)
Terms: 0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 4, 5, 4, 5, 0, 0, 2, 2, 0, 1, 0, 0, 8, 8, 10, 11, 8, 8

### A292592
```
%I A292592 #27 Sep 24 2017 13:17:07
%S A292592 0,0,0,1,0,0,2,2,0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,8,8,10,11,8,8,10,10,
%T A292592 0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,16,17,16,17,20,20,22,23,16,17,16,16,
%U A292592 20,21,20,21,0,0,2,2,0,1,0,0,8,8,10,11,8,8,10,10,0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,32,32,34,35,32,32,34,34,40,41,40,41
%N A292592 a(n) = A292590(A245612(n)).
%C A292592 Because A292590(n) =  a(A245611(n)), the sequence works as a "masking function" where the 1-bits in a(n) (always a subset of the 1-bits in binary expansion of n) indicate which numbers are multiples of 3 in binary tree A245612 on that trajectory which leads from the root of the tree to the node containing A245612(n). See the examples.
%H A292592 Antti Karttunen, <a href="/A292592/b292592.txt">Table of n, a(n) for n = 0..8191</a>
%H A292592 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%H A292592 <a href="/index/Pri#prime_indices">Index entries for sequences computed from indices in prime factorization</a>
%F A292592 a(n) + A292593(n) = n, a(n) AND A292593(n) = 0.
%F A292592 a(n) AND n = a(n), where AND is bitwise-AND (A004198).
%e A292592 A245612(18) = 188, that is, at "node address" 18 in binary tree A245612 sits number 188. 18 in binary is "10010", which when read from left to right (after the most significant bit which is always 1) gives the directions to follow in the tree when starting from the root, to land in node containing number 188. Here, after 1 and 2, turn left from 2, turn left from 5, turn right from 14 and then turn left from 63 and then indeed one lands in 188. These turns correspond with the four lowermost bits of the code, "0010". When one selects multiples of 3 from this path 1 -> 2 -> 5 -> 14 -> 63 -> 188, the only one is 63, which corresponds with the second rightmost bit (which also is the only 1-bit) in the code, which can be masked with 2 (binary "10"), thus a(18) = 2.
%e A292592 A245612(15) = 6, that is, at "node address" 15 in binary tree A245612 sits number 6. 15 in binary is "1111", which tells that 6 can be located in tree A245612 by going (after the initial root 1 and 2) three steps towards right from 2: 1 -> 2 -> 3 -> 4 -> 6. Of these numbers, only 3 and 6 are multiples of 3, thus the mask to obtain the corresponding bits from "1111" is "00101" (5 in binary), thus a(15) = 5.
%e A292592 A245612(31) = 7, that is, at "node address" 31 in binary tree A245612 sits number 7. 31 in binary is "11111", which tells that 7 can be located in tree A245612 by going (after the initial root 1 and 2) four steps towards right from 2: 1 -> 2 -> 3 -> 4 -> 6 -> 7. Of these numbers, only 3 and 6 are multiples of 3, thus the mask to obtain the corresponding bits from "11111" is "001010" (ten in binary), thus a(31) = 10.
%t A292592 f[n_] := f[n] = Which[n == 1, 0, Mod[n, 3] == 2, Ceiling[n/3], True, (Times @@ Power[If[# == 1, 1, NextPrime[#, -1]] & /@ First@ #, Last@ #] &@ Transpose@ FactorInteger[2 n - 1] + 1)/2]; g[n_] := g[n] = If[n == 1, 0, 2 g[f@ n] + Boole[Divisible[n, 3]]]; h[n_] := (Times @@ Power[If[# == 1, 1, NextPrime@ #] & /@ First@ #, Last@ #] + 1)/2 &@ Transpose@ FactorInteger@If[n == 0, 1, Prime[#] Product[ Prime[m]^(Map[ Ceiling[(Length@ # - 1)/2] &, DeleteCases[ Split@ Join[ Riffle[ IntegerDigits[n, 2], 0], {0}], {k__} /;k == 1]][[-m]]), {m, #}] &[DigitCount[n, 2, 1]]]; Array[g@ h@ # &, 108, 0] (* _Michael De Vlieger_, Sep 22 2017 *)
%Y A292592 Cf. A004198, A292590, A292593.
%Y A292592 Cf. also A292377.
%Y A292592 Differs from related A292274 for the first time at n=31, where a(31) = 10, while A292274(31) = 11. Compare also the scatter plots.
%K A292592 nonn,base
%O A292592 0,7
%A A292592 _Antti Karttunen_, Sep 20 2017
```
### A332996
```
%I A332996 #11 Mar 10 2020 00:29:19
%S A332996 0,0,0,1,0,0,2,2,0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,8,8,10,11,8,8,10,10,
%T A332996 0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,16,17,16,17,20,20,22,23,16,17,16,16,
%U A332996 20,21,20,21,0,0,2,2,0,1,0,0,8,8,10,11,8,8,10,10,0,1,0,0,4,5,4,5,0,0,2,2,0,1,0,0,32,32,34,35,32,32,34,34,40,41
%N A332996 a(n) = A332896(A332817(n)).
%C A332996 In contrast to similarly constructed A292274, this sequence can be computed directly from the binary expansion of n, without involving primes or their distribution at all.
%H A332996 Antti Karttunen, <a href="/A332996/b332996.txt">Table of n, a(n) for n = 0..16383</a>
%H A332996 Antti Karttunen, <a href="/A332996/a332996.txt">Data supplement: n, a(n) computed for n = 0..65537</a>
%H A332996 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%F A332996 a(n) = A332896(A332817(n)).
%F A332996 a(n) = n - A332995(n) = n XOR A332995(n).
%F A332996 A000120(a(n)) = A332998(n).
%o A332996 (PARI) A332996(n) = A332896(A332817(n));
%Y A332996 Cf. A292274, A332817, A332896, A332995, A332998.
%Y A332996 Differs from a similarly constructed A292592 for the first time at n=511, where a(511) = 170, while A292592(511) = 171.
%K A332996 nonn
%O A332996 0,7
%A A332996 _Antti Karttunen_, Mar 05 2020
```

## Candidate 129: A328482 vs A371091 (score 73.1, agree 106, variant raw, family size 6)
Terms: 0, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3, 2, 3, 2, 3, 3, 4, 3, 4, 1, 2, 2, 3, 2, 3

### A328482
```
%I A328482 #10 Oct 19 2019 21:26:23
%S A328482 0,1,1,2,1,2,1,2,2,3,2,3,1,2,2,3,2,3,2,3,3,4,3,4,1,2,2,3,2,3,1,2,2,3,
%T A328482 2,3,2,3,3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,2,3,3,4,3,4,1,2,2,3,2,3,2,3,
%U A328482 3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,2,3,3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,3,4,4,5
%N A328482 Number of distinct terms required when n is expressed as a greedy sum of terms of A129912 (number of nonzero digits when n is expressed in greedy A129912-base).
%H A328482 Antti Karttunen, <a href="/A328482/b328482.txt">Table of n, a(n) for n = 0..30030</a>
%H A328482 <a href="/index/Pri#primorial_numbers">Index entries for sequences related to primorial numbers</a>
%F A328482 a(A129912(n)) = a(A002110(n)) = 1.
%F A328482 For all n, a(n) <= A328481(n).
%e A328482 Terms of A129912 (numbers that are products of distinct primorial numbers) begin as: 1, 2, 6, 12, 30, 60, 180, 210, 360, 420, 1260, ...
%e A328482 Number 5 is expressed as 5 = 2 + 2 + 1 = 2*2 + 1*1, when always choosing the largest term which is <= {what is remaining of the original number}. Thus a(5) = 2 (number of distinct terms used, 1 and 2).
%e A328482 Number 21 is expressed as 21 = 12 + 6 + 2 + 1, thus a(21) = 4.
%o A328482 (PARI)
%o A328482 isA129912(n) = { my(o=valuation(n, 2), t); if(o<1||n<2, return(n==1)); n>>=o; forprime(p=3, , t=valuation(n, p); n/=p^t; if(t>o || t<o-1, return(0)); if(t==0, return(n==1)); o=t); }; \\ From A129912
%o A328482 prepare_A129912_upto(n) = { my(xs=List([]), k=0); while(k<n, k++; if(isA129912(k), listput(xs,k))); List(Vecrev(xs)); };
%o A328482 number_of_distinct_terms_in_greedy_sum(n,terms) = { my(c=0); while(n,if(terms[1] > n, listpop(terms,1), c++; n %= terms[1])); (c); };
%o A328482 A328482(n) = number_of_distinct_terms_in_greedy_sum(n,prepare_A129912_upto(n));
%Y A328482 Cf. A002110, A129912, A328481, A328483.
%Y A328482 Cf. also A267263.
%K A328482 nonn
%O A328482 0,4
%A A328482 _Antti Karttunen_, Oct 19 2019
```
### A371091
```
%I A371091 #27 Aug 24 2026 01:08:34
%S A371091 0,1,1,2,1,2,1,2,2,3,2,3,1,2,2,3,2,3,2,3,3,4,3,4,1,2,2,3,2,3,1,2,2,3,
%T A371091 2,3,2,3,3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,2,3,3,4,3,4,1,2,2,3,2,3,2,3,
%U A371091 3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,2,3,3,4,3,4,2,3,3,4,3,4,3,4,4,5,4,5,3,4,4,5,4,5,4,5,5,6,5,6,3,4,4,5,4,5,1
%N A371091 Number of 1's in the recursive decomposition of primorial base expansion of n.
%C A371091 Take the primorial base expansion of n (A049345), and then replace any digit larger than 1 with its own primorial base expansion, and do this recursively until no digits larger than 1 remain. a(n) is then the number of 1's in the completed decomposition. (See the examples). This decomposition offers a way to design a natural primorial based numeral system that does not require an infinite number of arbitrary glyphs for its digits, but instead suffices with just two graphically distinct subfigures whose exact positions in the whole hierarchically organized composite glyph determines the numerical value of that glyph, a bit like in Maya numerals or Babylonian cuneiform digits, but based on a primorial number system instead of vigesimal or sexagesimal.
%H A371091 Antti Karttunen, <a href="/A371091/b371091.txt">Table of n, a(n) for n = 0..60060</a>
%H A371091 <a href="/index/Pri#primorialbase">Index entries for sequences related to primorial base</a>.
%F A371091 a(n) = A371090(A276086(n)).
%F A371091 For all n, A267263(n) <= a(n) <= A276150(n).
%e A371091      n  A049345(n)     recursive              a(n) = number of 1's
%e A371091                        decomposition          in the decomposition
%e A371091 --------------------------------------------------------------------
%e A371091      0         0         ()                             0
%e A371091      1         1         (1)                            1
%e A371091      2        10         (1 0)                          1
%e A371091      3        11         (1 1)                          2
%e A371091      4        20         ((1 0) 0)                      1
%e A371091      5        21         ((1 0) 1)                      2
%e A371091      6       100         (1 0 0)                        1
%e A371091      7       101         (1 0 1)                        2
%e A371091      8       110         (1 1 0)                        2
%e A371091      9       111         (1 1 1)                        3
%e A371091     10       120         (1 (1 0) 0)                    2
%e A371091     11       121         (1 (1 0) 1)                    3
%e A371091     12       200         ((1 0) 0 0)                    1
%e A371091     ..
%e A371091     21       311         ((1 1) 1 1)                    4
%e A371091     ..
%e A371091     24       400         (((1 0) 0) 0 0)                1
%e A371091     ..
%e A371091     29       421         (((1 0) 0) (1 0) 1)            3
%e A371091     30      1000         (1 0 0 0)                      1
%e A371091     ..
%e A371091     51      1311         (1 (1 1) 1 1)                  5
%e A371091     ..
%e A371091     59      1421         (1 ((1 0) 0) (1 0) 1)          4
%e A371091     60      2000         ((1 0) 0 0 0)                  1
%e A371091     ..
%e A371091    111      3311         ((1 1) (1 1) 1 1)              6
%e A371091    ...
%e A371091    360     15000         (1 ((1 0) 1) 0 0 0)            3
%e A371091    ...
%e A371091   2001     93311         ((1 1 1) (1 1) (1 1) 1 1)      9
%e A371091   ....
%e A371091   4311    193311         (1 (1 1 1) (1 1) (1 1) 1 1)   10.
%e A371091 29 is decomposed in piecemeal fashion as: A049345(29) = 421 --> ("20" "10" "1") --> (((1 0) 0) (1 0) 1).
%t A371091 s[n_, p_] := s[n, p] = If[n <= 0, 1, p^Mod[n, p] * s[Floor[n/p], NextPrime[p]]]; A276086[n_] := s[n, 2];
%t A371091 f[p_, e_] := If[e == 1, 1, A371090[A276086[e]]]; A371090[1] = 0; A371090[n_] := Plus @@ f @@@ FactorInteger[n];
%t A371091 a[n_] := A371090[A276086[n]]; Array[a, 100, 0] (* _Amiram Eldar_, Aug 24 2026 *)
%o A371091 (PARI)
%o A371091 A276086(n) = { my(m=1, p=2); while(n, m *= (p^(n%p)); n = n\p; p = nextprime(1+p)); (m); };
%o A371091 A371090(n) = vecsum(apply(e->if(1==e,1,A371091(e)),factor(n)[, 2]));
%o A371091 A371091(n) = A371090(A276086(n));
%Y A371091 Cf. A049345, A267263, A276086, A276150, A371090.
%Y A371091 Cf. A372559 (positions of records and the first occurrence of n).
%Y A371091 Differs from A328482 for the first time at n=360, where a(360) = 3, while A328482(360) = 1.
%K A371091 nonn,base
%O A371091 0,4
%A A371091 _Antti Karttunen_, Mar 31 2024
```

## Candidate 130: A133265 vs A275365 (score 73.0, agree 73, variant drop1, family size 2)
Terms: 2, 2, 2, 4, 2, 6, 2, 8, 2, 10, 2, 12, 2, 14, 2, 16, 2, 18, 2, 20, 2, 22, 2, 24, 2, 26, 2, 28, 2, 30

### A133265
```
%I A133265 #25 Sep 08 2022 08:45:31
%S A133265 2,2,2,4,2,6,2,8,2,10,2,12,2,14,2,16,2,18,2,20,2,22,2,24,2,26,2,28,2,
%T A133265 30,2,32,2,34,2,36,2,38,2,40,2,42,2,44,2,46,2,48,2,50,2,52,2,54,2,56,
%U A133265 2,58,2,60,2,62,2,64,2,66,2,68,2,70,2,72,2,74,2,76,2,78,2,80
%N A133265 Diagonal of the A135356 triangle.
%C A133265 Regular continued fraction expansion of 2*sin(1/2)/( cos(1/2) - sin(1/2) ) = 2.40822 34423 35827 84841 ... = 2 + 1/(2 + 1/(2 + 1/(4 + 1/(2 + 1/(6 + 1/(2 + 1/(8 + 1/(2 + ... )))))))). Cf. A019425. - _Peter Bala_, Feb 15 2015
%H A133265 Vincenzo Librandi, <a href="/A133265/b133265.txt">Table of n, a(n) for n = 0..1000</a>
%H A133265 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,2,0,-1).
%F A133265 2*(A057979 without 1, 0, first two terms).
%F A133265 a(n) = (n+3+(n-1)*(-1)^(n+1))/2. - _Vincenzo Librandi_, Aug 30 2011
%F A133265 a(n) = (2*n + 5) mod (n*(3 + (-1)^n) - (-1)^n + 7)/2. - _Lechoslaw Ratajczak_, Nov 17 2016
%F A133265 From _Colin Barker_, Nov 17 2016: (Start)
%F A133265 a(n) = 2*a(n-2) - a(n-4) for n>3.
%F A133265 G.f.: 2*(1 + x - x^2) / ((1 - x)^2 * (1 + x)^2).
%F A133265 (End)
%p A133265 A133265 := n -> (n+2+(n-2)*(-1)^n)/2: # _Peter Luschny_, Aug 30 2011
%t A133265 Table[(n + 3 + (n - 1) (-1)^(n + 1))/2, {n, 0, 79}] (* or *)
%t A133265 Table[Mod[(2 n + 5), (n (3 + (-1)^n) - (-1)^n + 7)/2], {n, 0, 79}] (* or *)
%t A133265 CoefficientList[Series[2 (1 + x - x^2)/((1 - x)^2*(1 + x)^2), {x, 0, 79}], x] (* _Michael De Vlieger_, Nov 18 2016 *)
%o A133265 (Magma) [(n+3+(n-1)*(-1)^(n+1))/2: n in [0..80]]; // _Vincenzo Librandi_, Aug 30 2011
%o A133265 (PARI) Vec(2*(1 + x - x^2) / ((1 - x)^2 * (1 + x)^2) + O(x^100)) \\ _Colin Barker_, Nov 17 2016
%Y A133265 Cf. A019425.
%K A133265 nonn,easy
%O A133265 0,1
%A A133265 _Paul Curtz_, Dec 20 2007
```
### A275365
```
%I A275365 #14 Feb 19 2019 04:11:01
%S A275365 0,2,2,4,2,6,2,8,2,10,2,12,2,14,2,16,2,18,2,20,2,22,2,24,2,26,2,28,2,
%T A275365 30,2,32,2,34,2,36,2,38,2,40,2,42,2,44,2,46,2,48,2,50,2,52,2,54,2,56,
%U A275365 2,58,2,60,2,62,2,64,2,66,2,68,2,70,2,72,2,74
%N A275365 a(1)=2, a(2)=2; thereafter a(n) = a(n-a(n-1)) + a(n-a(n-2)).
%C A275365 a(n) is the solution to the recurrence relation a(n) = a(n-a(n-1)) + a(n-a(n-2)) [Hofstadter's Q recurrence], with the initial conditions: a(n) = 0 if n <= 0; a(1) = 2, a(2) = 2.
%C A275365 Starting with n=1, a(n) is A005843 interleaved with A007395.
%C A275365 This sequence is the same as A133265 with the leading 2 changed to a 0.
%H A275365 Nathan Fox, <a href="/A275365/b275365.txt">Table of n, a(n) for n = 0..1000</a>
%H A275365 Nathan Fox, <a href="https://arxiv.org/abs/1609.06342">Finding Linear-Recurrent Solutions to Hofstadter-Like Recurrences Using Symbolic Computation</a>, arXiv:1609.06342 [math.NT], 2016.
%H A275365 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,2,0,-1).
%F A275365 a(0) = 0; thereafter, a(2n) = 2, a(2n+1) = 2n+2.
%F A275365 a(n) = 2*a(n-2) - a(n-4) for n>4.
%F A275365 G.f.: -(2*x^3 -2*x -2)/((x-1)^2*(x+1)^2).
%t A275365 Join[{0}, LinearRecurrence[{0, 2, 0, -1}, {2, 2, 4, 2}, 73]] (* _Jean-François Alcover_, Feb 19 2019 *)
%Y A275365 Cf. A005185, A133265, A188670, A244477, A264756, A264757, A264758, A268368, A275153, A275361, A275362.
%K A275365 easy,nonn
%O A275365 0,2
%A A275365 _Nathan Fox_, Jul 24 2016
```

## Candidate 131: A002324 vs A171774 (score 72.4, agree 105, variant raw, family size 3)
Terms: 1, 0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 1, 2, 0, 0

### A002324
```
%I A002324 M0016 N0002 #153 May 30 2026 16:39:44
%S A002324 1,0,1,1,0,0,2,0,1,0,0,1,2,0,0,1,0,0,2,0,2,0,0,0,1,0,1,2,0,0,2,0,0,0,
%T A002324 0,1,2,0,2,0,0,0,2,0,0,0,0,1,3,0,0,2,0,0,0,0,2,0,0,0,2,0,2,1,0,0,2,0,
%U A002324 0,0,0,0,2,0,1,2,0,0,2,0,1,0,0,2,0,0,0,0,0,0,4,0,2,0,0,0,2,0,0,1,0,0,2,0,0,0,0,1,2,0,2,2,0,0
%N A002324 Number of divisors of n == 1 (mod 3) minus number of divisors of n == 2 (mod 3).
%C A002324 Coefficients of Dedekind zeta function for the quadratic number field of discriminant -3. See Formula section for the general expression. - _N. J. A. Sloane_, Mar 22 2022
%C A002324 Coefficients in expansion of Dirichlet series Product_p (1 - (Kronecker(m,p) + 1)*p^(-s) + Kronecker(m,p) * p^(-2s))^(-1) for m = -3.
%C A002324 (Number of points of norm n in hexagonal lattice) / 6, n>0.
%C A002324 The hexagonal lattice is the familiar 2-dimensional lattice (A_2) in which each point has 6 neighbors. This is sometimes called the triangular lattice.
%C A002324 The first occurrence of a(n) = 1, 2, 3, 4,... is at n= 1, 7, 49, 91, 2401, 637, ... as tabulated in A343771. - _R. J. Mathar_, Sep 21 2024
%D A002324 J. H. Conway and N. J. A. Sloane, "Sphere Packings, Lattices and Groups", Springer-Verlag, p. 112, first display.
%D A002324 J. W. L. Glaisher, Table of the excess of the number of (3k+1)-divisors of a number over the number of (3k+2)-divisors, Messenger Math., 31 (1901), 64-72.
%D A002324 D. H. Lehmer, Guide to Tables in the Theory of Numbers. Bulletin No. 105, National Research Council, Washington, DC, 1941, pp. 7-10.
%D A002324 N. J. A. Sloane, A Handbook of Integer Sequences, Academic Press, 1973 (includes this sequence).
%D A002324 N. J. A. Sloane and Simon Plouffe, The Encyclopedia of Integer Sequences, Academic Press, 1995 (includes this sequence).
%H A002324 T. D. Noe, <a href="/A002324/b002324.txt">Table of n, a(n) for n = 1..10000</a>
%H A002324 G. E. Andrews, <a href="http://www.mat.univie.ac.at/~slc/opapers/s25andrews.html">Three aspects of partitions</a>, Séminaire Lotharingien de Combinatoire, B25f (1990), 1 p.
%H A002324 Hershel M. Farkas, <a href="https://doi.org/10.1007/s11139-004-0141-5">On an arithmetical function</a>, Ramanujan J., 8(3) (2004), 309-315.
%H A002324 Pavel Guerzhoy and Ka Lun Wong, <a href="https://arxiv.org/abs/1905.06506">Farkas' identities with quartic characters</a>, arXiv:1905.06506 [math.NT], 2019.
%H A002324 Christian Kassel and Christophe Reutenauer, <a href="https://arxiv.org/abs/1505.07229v3">The zeta function of the Hilbert scheme of n points on a two-dimensional torus</a>, arXiv:1505.07229v3 [math.AG], 2015. [A later version of this paper has a different title and different contents, and the number-theoretical part of the paper was moved to the publication below.]
%H A002324 Christian Kassel and Christophe Reutenauer, <a href="https://arxiv.org/abs/1610.07793">Complete determination of the zeta function of the Hilbert scheme of n points on a two-dimensional torus</a>, arXiv:1610.07793 [math.NT], 2016.
%H A002324 Gabriele Nebe and N. J. A. Sloane, <a href="http://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/A2.html">Home page for hexagonal (or triangular) lattice A2</a>.
%H A002324 José Manuel Rodríguez Caballero, <a href="https://arxiv.org/abs/1709.09621">Divisors on overlapped intervals and multiplicative functions</a>, arXiv:1709.09621 [math.NT], 2017.
%H A002324 J. S. Rutherford, <a href="https://doi.org/10.1007/BF01164477">Generating functions for the cage isomers of the C_{20n} icosahedral fullerenes, J. Mathematical Chem.</a>, 14 (1993), 385-390. [From _N. J. A. Sloane_, Mar 12 2009]
%H A002324 John S. Rutherford, <a href="https://doi.org/10.1107/S010876730804333X">Sublattice enumeration. IV. Equivalence classes of plane sublattices by parent Patterson symmetry and colour lattice group type</a>, Acta Cryst. (2009). A65, 156-163. [See Table 1]. - From _N. J. A. Sloane_, Feb 23 2009
%H A002324 N. J. A. Sloane, <a href="/A002324/a002324.txt">Maple code for Dedekind zeta functions of quadratic number fields</a>.
%F A002324 From _N. J. A. Sloane_, Mar 22 2022 (Start):
%F A002324 The Dedekind zeta function DZ_K(s) for a quadratic field K of discriminant D is as follows.
%F A002324 Here m is defined by K = Q(sqrt(m)) (so m=D/4 if D is a multiple of 4, otherwise m=D).
%F A002324 DZ_K(s) is the product of three terms:
%F A002324 (a) Product_{odd primes p | D} 1/(1-1/p^s)
%F A002324 (b) Product_{odd primes p such that (D|p) = -1} 1/(1-1/p^(2s))
%F A002324 (c) Product_{odd primes p such that (D|p) = 1} 1/(1-1/p^s)^2
%F A002324 and if m is
%F A002324    0,1,2,3,4,5,6,7 mod 8, the prime 2 is to be included in term
%F A002324    -,c,a,a,-,b,a,a, respectively.
%F A002324 For Maple (and PARI) implementations, see link. (End)
%F A002324 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^4)) where f(u, v, w) = u^2 - 3*v^2 + 4*w^2 - 2*u*w + w - v. - _Michael Somos_, Jul 20 2004
%F A002324 Has a nice Dirichlet series expansion, see PARI line.
%F A002324 G.f.: Sum_{k>0} x^k/(1+x^k+x^(2*k)). - _Vladeta Jovovic_, Dec 16 2002
%F A002324 a(3*n + 2) = 0, a(3*n) = a(n), a(3*n + 1) = A033687(n). - _Michael Somos_, Apr 04 2003
%F A002324 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^3), A(x^6)) where f(u1, u2, u3, u6) = (u1 - u3)*(u3 - u6) - (u2 - u6)^2. - _Michael Somos_, May 20 2005
%F A002324 Multiplicative with a(3^e) = 1, a(p^e) = e+1 if p == 1 (mod 3), a(p^e) = (1+(-1)^e)/2 if p == 2 (mod 3). - _Michael Somos_, May 20 2005
%F A002324 G.f.: Sum_{k>0} x^(3*k - 2) / (1 - x^(3*k - 2)) - x^(3*k - 1)  / (1 - x^(3*k - 1)). - _Michael Somos_, Nov 02 2005
%F A002324 G.f.: Sum_{n >= 1} q^(n^2)(1-q)(1-q^2)...(1-q^(n-1))/((1-q^(n+1))(1-q^(n+2))...(1-q^(2n))). - _Jeremy Lovejoy_, Jun 12 2009
%F A002324 a(n) = A001817(n) - A001822(n). - _R. J. Mathar_, Mar 31 2011
%F A002324 A004016(n) = 6*a(n) unless n=0.
%F A002324 Dirichlet g.f.: zeta(s)*L(chi_2(3),s), with chi_2(3) the nontrivial Dirichlet character modulo 3 (A102283). - _Ralf Stephan_, Mar 27 2015
%F A002324 From _Andrey Zabolotskiy_, May 07 2018: (Start)
%F A002324 a(n) = Sum_{ m: m^2|n } A000086(n/m^2).
%F A002324 a(A003136(m)) > 0, a(A034020(m)) = 0 for all m. (End)
%F A002324 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi/(3*sqrt(3)) = 0.604599... (A073010). - _Amiram Eldar_, Oct 11 2022
%e A002324 G.f. = x + x^3 + x^4 + 2*x^7 + x^9 + x^12 + 2*x^13 + x^16 + 2*x^19 + 2*x^21 + ...
%p A002324 A002324 := proc(n)
%p A002324     local a,pe,p,e;
%p A002324     a :=1 ;
%p A002324     for pe in ifactors(n)[2] do
%p A002324         p := op(1,pe) ;
%p A002324         e := op(2,pe) ;
%p A002324         if p = 3 then
%p A002324             ;
%p A002324         elif modp(p,3) = 1 then
%p A002324             a := a*(e+1) ;
%p A002324         else
%p A002324             a := a*(1+(-1)^e)/2 ;
%p A002324         end if;
%p A002324     end do:
%p A002324     a ;
%p A002324 end proc:
%p A002324 seq(A002324(n),n=1..100) ; # _R. J. Mathar_, Sep 21 2024
%t A002324 dn12[n_]:=Module[{dn=Divisors[n]},Count[dn,_?(Mod[#,3]==1&)]-Count[ dn,_?(Mod[#,3]==2&)]]; dn12/@Range[120]  (* _Harvey P. Dale_, Apr 26 2011 *)
%t A002324 a[ n_] := If[ n < 1, 0, DivisorSum[ n, KroneckerSymbol[ -3, #] &]]; (* _Michael Somos_, Aug 24 2014 *)
%t A002324 Table[DirichletConvolve[DirichletCharacter[3,2,m],1,m,n],{n,1,30}] (* _Steven Foster Clark_, May 29 2019 *)
%t A002324 f[3, p_] := 1; f[p_, e_] := If[Mod[p, 3] == 1, e+1, (1+(-1)^e)/2]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Sep 17 2020 *)
%o A002324 (PARI) {a(n) = if( n<0, 0, polcoeff( sum(k=1, n, x^k / (1 + x^k + x^(2*k)), x * O(x^n)), n))}; \\ _Michael Somos_
%o A002324 (PARI) {a(n) = if( n<1, 0, sumdiv(n, d, (d%3==1) - (d%3==2)))};
%o A002324 (PARI) {a(n) = local(A, p, e); if( n<1, 0, A = factor(n); prod(k=1, matsize(A)[1], if( p=A[k,1], e=A[k,2]; if( p==3, 1, if( p%3==1, e+1, !(e%2))))))}; \\ _Michael Somos_, May 20 2005
%o A002324 (PARI) {a(n) = if( n<1, 0, qfrep([2,1; 1,2], n, 1)[n] / 3)}; \\ _Michael Somos_, Jun 05 2005
%o A002324 (PARI) {a(n) = if( n<1, 0, direuler(p=2, n, 1 / (1 - X) / (1 - kronecker(-3, p)*X))[n])}; \\ _Michael Somos_, Jun 05 2005
%o A002324 (PARI) my(B=bnfinit(x^2+x+1)); vector(100,n,#bnfisintnorm(B,n)) \\ _Joerg Arndt_, Jun 01 2024
%o A002324 (Haskell)
%o A002324 a002324 n = a001817 n - a001822 n  -- _Reinhard Zumkeller_, Nov 26 2011
%o A002324 (Python)
%o A002324 from math import prod
%o A002324 from sympy import factorint
%o A002324 def A002324(n): return prod(e+1 if p%3==1 else int(not e&1) for p, e in factorint(n).items() if p != 3) # _Chai Wah Wu_, Nov 17 2022
%Y A002324 Cf. A004016, A035019, A073010, A145377, A293899, A000086, A003136, A034020, A145394.
%Y A002324 Moebius transform gives A102283.
%Y A002324 Cf. A007645 (primes not inert in Q(sqrt(-3))), A002476 (primes decomposing), A003627 (primes remaining inert), A045309 (primes not decomposing).
%Y A002324 Dedekind zeta functions for imaginary quadratic number fields of discriminants D = -3..-47, -67, -163: this sequence, A002654, A035182, A002325, A035179, A035175, A035171, A035170, A035167, A192013, A035159, A035155, A035151, A035180, A035147, A035143, A318982, A318983.
%Y A002324 Dedekind zeta functions for real quadratic number fields of discriminants D = 5..41: A035187, A035185, A035194, A035195, A035199, A035203, A035188, A035210, A035211, A035215, A035219, A035192, A035223.
%K A002324 easy,nonn,nice,mult
%O A002324 1,7
%A A002324 _N. J. A. Sloane_
%E A002324 More terms from _David Radcliffe_
%E A002324 Somos D.g.f. replaced with correct version by _Ralf Stephan_, Mar 27 2015
```
### A171774
```
%I A171774 #8 Nov 26 2017 07:15:08
%S A171774 1,0,1,1,0,0,2,0,1,0,0,1,2,0,0,1,0,0,2,0,2,0,0,0,1,0,1,2,0,0,2,0,0,0,
%T A171774 0,1,2,0,2,0,0,0,2,0,0,0,0,1,3,0,0,2,0,0,0,0,2,0,0,0,2,0,2,1,0,0,2,0,
%U A171774 0,0,0,0,2,0,1,2,0,0,2,0,1,0,0,2,0,0,0,0,0,0,4,0,2,0,0,0,2,0,0,1,0,0,2,0,0
%N A171774 Radix expansion of -1/6 in radix -exp(Pi/sqrt(3)).
%H A171774 Michael Somos, <a href="/A171774/b171774.txt">Table of n, a(n) for n = 1..10000</a>
%F A171774 If r = -exp(Pi/sqrt(3)) and q = 1/r, then -1/6 = Sum_{k>0} a(k) * q^k.
%e A171774 q + q^3 + q^4 + 2*q^7 + q^9 + q^12 + 2*q^13 + q^16 + 2*q^19 + 2*q^21 + ...
%o A171774 (PARI) {a(n) = local(x,r,k); if( n<1, 0, default(realprecision, n ); r = -exp(Pi / sqrt(3)); x = -r/6; for(i=1, n, x = (x - (k = if(x>0, round(x), 0)))*r); k)};
%Y A171774 Differs from A002324 for the first time at n = 300, where a(300) = 0, while A002324(300) = 1.
%K A171774 nonn
%O A171774 1,7
%A A171774 _Michael Somos_, Dec 18 2009
```

## Candidate 132: A004258 vs A029837 (score 72.4, agree 105, variant raw, family size 11)
Terms: 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5

### A004258
```
%I A004258 #4 Jun 01 2010 03:00:00
%S A004258 0,1,2,2,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,
%T A004258 6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,
%U A004258 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7
%N A004258 Duplicate of A029837.
%K A004258 dead
%O A004258 1,3
```
### A029837
```
%I A029837 #117 Oct 22 2026 23:28:01
%S A029837 0,1,2,2,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,
%T A029837 6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,
%U A029837 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7
%N A029837 Binary order of n: log_2(n) rounded up to next integer.
%C A029837 Or, ceiling(log_2(n)).
%C A029837 Worst-case cost of binary search.
%C A029837 Equal to number of binary digits in n unless n is a power of 2 when it is one less.
%C A029837 Thus a(n) gives the length of the binary representation of n - 1 (n >= 2), which is also A070939(n - 1).
%C A029837 Let x(0) = n > 1 and x(k + 1) = x(k) - floor(x(k)/2), then a(n) is the smallest integer such that x(a(n)) = 1. - _Benoit Cloitre_, Aug 29 2002
%C A029837 Also number of division steps when going from n to 1 by process of adding 1 if odd, or dividing by 2 if even. - _Cino Hilliard_, Mar 25 2003
%C A029837 Number of ways to write n as (x + 2^y), x >= 0. Number of ways to write n + 1 as 2^x + 3^y (cf. A004050). - _Benoit Cloitre_, Mar 29 2003
%C A029837 The minimum number of cuts for dividing an object into n (possibly unequal) pieces. - Karl Ove Hufthammer (karl(AT)huftis.org), Mar 29 2010
%C A029837 Partial sums of A209229; number of powers of 2 not greater than n. - _Reinhard Zumkeller_, Mar 07 2012
%C A029837 Also the bipartite dimension of the cocktail party graph and the complete graph K_n. - _Eric W. Weisstein_, Jun 29 2026
%C A029837 The fewest fair coin tosses needed to get a head with probability >= (n-1)/n. - _Michael Shmoish_, Oct 18 2026
%D A029837 R. L. Graham, D. E. Knuth and O. Patashnik, Concrete Mathematics, Addison-Wesley, 1989, p. 70.
%D A029837 G. J. E. Rawlins, Compared to What? An Introduction to the Analysis of Algorithms, W. H. Freeman, 1992; see pp. 108, 118.
%H A029837 T. D. Noe, <a href="/A029837/b029837.txt">Table of n, a(n) for n = 1..10000</a>
%H A029837 Cino Hilliard, <a href="http://groups.msn.com/BC2LCC/page.msnw?fc_p=%2Fkx%2Bp%20problems&amp;fc_a=0">The x+1 conjecture</a> [broken link]
%H A029837 Lionel Levine, <a href="https://arxiv.org/abs/math/0409408">Fractal sequences and restricted Nim</a>, arXiv:math/0409408 [math.CO], 2004.
%H A029837 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/BipartiteDimension.html">Bipartite Dimension</a>.
%H A029837 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/BitLength.html">Bit Length.</a>
%H A029837 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/CocktailPartyGraph.html">Cocktail Party Graph</a>.
%H A029837 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/CompleteGraph.html">Complete Graph</a>.
%H A029837 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%F A029837 a(n) = ceiling(log_2(n)).
%F A029837 a(1) = 0; for n > 1, a(2n) = a(n) + 1, a(2n + 1) = a(n) + 1. Alternatively, a(1) = 0; for n > 1, a(n) = a(ceiling(n/2)) + 1. [corrected by _Ilya Gutkovskiy_, Mar 21 2020]
%F A029837 a(n) = k such that n^(1/k - 1) > 2 > n^(1/k), or the least value of k for which floor n^(1/k) = 1. a(n) = k for all n such that 2^(k - 1) < n < 2^k. - _Amarnath Murthy_, May 06 2001
%F A029837 G.f.: x/(1 - x) * Sum_{k >= 0} x^2^k. - _Ralf Stephan_, Apr 13 2002
%F A029837 A062383(n-1) = 2^a(n). - _Johannes W. Meijer_, Jul 06 2009
%F A029837 a(n+1) = -Sum_{k = 1..n} mu(2*k)*floor(n/k). - _Benoit Cloitre_, Oct 21 2009
%F A029837 a(n+1) = A113473(n). - _Michael Somos_, Jun 02 2019
%e A029837 a(1) = 0, since log_2(1) = 0.
%e A029837 a(2) = 1, since log_2(2) = 1.
%e A029837 a(3) = 2, since log_2(3) = 1.58...
%e A029837 a(n) = 7 for n = 65, 66, ..., 127, 128.
%e A029837 G.f. = x^2 + 2*x^3 + 2*x^4 + 3*x^5 + 3*x^6 + 3*x^7 + 3*x^8 + 4*x^9 + ... - _Michael Somos_, Jun 02 2019
%p A029837 a:= n-> (p-> p+`if`(2^p<n, 1, 0))(ilog2(n)):
%p A029837 seq(a(n), n=1..120);  # _Alois P. Heinz_, Mar 18 2013
%t A029837 a[n_] := Ceiling[Log[2, n]]; Array[a, 105] (* _Robert G. Wilson v_, Dec 09 2005 *)
%t A029837 (* Alternative: *)
%t A029837 Table[IntegerLength[n - 1, 2], {n, 1, 105}] (* _Peter Luschny_, Dec 02 2017 *)
%t A029837 (* Alternative: *)
%t A029837 a[n_] := If[n < 1, 0, BitLength[n - 1]]; (* _Michael Somos_, Jul 10 2018 *)
%t A029837 (* Alternative: *)
%t A029837 Join[{0}, IntegerLength[Range[130], 2]] (* _Vincenzo Librandi_, Jun 14 2019 *)
%t A029837 (* Alternative: *)
%t A029837 Ceiling[Log2[Range[20]]] (* _Eric W. Weisstein_, Jun 29 2026 *)
%o A029837 (PARI) {a(n) = if( n<1, 0, ceil(log(n) / log(2)))};
%o A029837 (PARI) /* Set p = 1, then: */
%o A029837 xpcount(n,p) = for(x=1, n, p1 = x; ct=0; while(p1>1, if(p1%2==0,p1/=2; ct++,p1 = p1*p+1)); print1(ct, ", "))
%o A029837 (PARI) {a(n) = if( n<2, 0, exponent(n-1)+1)}; /* _Michael Somos_, Jul 10 2018 */
%o A029837 (Haskell)
%o A029837 a029837 n = a029837_list !! (n-1)
%o A029837 a029837_list = scanl1 (+) a209229_list
%o A029837 -- _Reinhard Zumkeller_, Mar 07 2012
%o A029837 (Common Lisp) (defun A029837 (n) (integer-length (1- n))) ; _James Spahlinger_, Oct 15 2012
%o A029837 (Magma) [Ceiling(Log(2, n)): n in [1..100]]; // _Vincenzo Librandi_, Jun 14 2019
%o A029837 (Scala) (1 to 80).map(n => Math.ceil(Math.log(n)/Math.log(2)).toInt) // _Alonso del Arte_, Feb 19 2020
%o A029837 (Python)
%o A029837 def A029837(n):
%o A029837     s = bin(n)[2:]
%o A029837     return len(s) - (1 if s.count('1') == 1 else 0) # _Chai Wah Wu_, Jul 09 2020
%o A029837 (Python)
%o A029837 def A029837(n): return (n-1).bit_length() # _Chai Wah Wu_, Jun 30 2022
%Y A029837 Cf. A000523, A070939, A000193, A000195, A004233, A113473, A053644.
%Y A029837 Partial sums of A036987.
%Y A029837 Used for several definitions: A029827, A036378-A036390. Partial sums: A001855.
%Y A029837 Cf. A000120, A003817.
%K A029837 nonn,easy,nice,changed
%O A029837 1,3
%A A029837 _N. J. A. Sloane_
%E A029837 Additional comments from _Daniele Parisse_
%E A029837 More terms from _Michael Somos_, Aug 02 2002
```

## Candidate 133: A010476 vs A020762 (score 72.4, agree 105, variant raw, family size 4)
Terms: 4, 4, 7, 2, 1, 3, 5, 9, 5, 4, 9, 9, 9, 5, 7, 9, 3, 9, 2, 8, 1, 8, 3, 4, 7, 3, 3, 7, 4, 6

### A010476
```
%I A010476 #31 Sep 23 2025 03:42:54
%S A010476 4,4,7,2,1,3,5,9,5,4,9,9,9,5,7,9,3,9,2,8,1,8,3,4,7,3,3,7,4,6,2,5,5,2,
%T A010476 4,7,0,8,8,1,2,3,6,7,1,9,2,2,3,0,5,1,4,4,8,5,4,1,7,9,4,4,9,0,8,2,1,0,
%U A010476 4,1,8,5,1,2,7,5,6,0,9,7,9,8,8,2,8,8,2,8,8,1,6,7,5,7,5,6,4,5,4,9,9,3,9,0,1
%N A010476 Decimal expansion of square root of 20.
%C A010476 Continued fraction expansion is 4 followed by {2, 8} repeated. - _Harry J. Smith_, Jun 03 2009
%H A010476 Harry J. Smith, <a href="/A010476/b010476.txt">Table of n, a(n) for n = 1..20000</a>
%H A010476 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>
%F A010476 sqrt(20) = 2*sqrt(5) = 2*A002163. - _Alonso del Arte_, Jun 26 2015
%F A010476 Equals Sum_{k>=0} binomial(2*k,k) * k/5^k. - _Amiram Eldar_, Aug 03 2020
%e A010476 4.472135954999579392818347337462552470881236719223051448541794490821041....
%t A010476 RealDigits[N[Sqrt[20], 100]][[1]] (* _Vladimir Joseph Stephan Orlovsky_, Feb 21 2011 *)
%o A010476 (PARI)  default(realprecision, 20080); x=sqrt(20); for (n=1, 20000, d=floor(x); x=(x-d)*10; write("b010476.txt", n, " ", d));  \\ _Harry J. Smith_, Jun 03 2009
%Y A010476 Except for offset, same as A020762.
%Y A010476 Cf. A040015 (continued fraction). - _Harry J. Smith_, Jun 03 2009
%Y A010476 Cf. A002163 (decimal expansion of square root of 5).
%K A010476 nonn,cons,easy
%O A010476 1,1
%A A010476 _N. J. A. Sloane_
```
### A020762
```
%I A020762 #56 Feb 28 2026 15:00:55
%S A020762 4,4,7,2,1,3,5,9,5,4,9,9,9,5,7,9,3,9,2,8,1,8,3,4,7,3,3,7,4,6,2,5,5,2,
%T A020762 4,7,0,8,8,1,2,3,6,7,1,9,2,2,3,0,5,1,4,4,8,5,4,1,7,9,4,4,9,0,8,2,1,0,
%U A020762 4,1,8,5,1,2,7,5,6,0,9,7,9,8,8,2,8,8,2,8,8,1,6,7,5,7,5,6,4,5,4,9,9,3,9,0,1
%N A020762 Decimal expansion of 1/sqrt(5).
%C A020762 This number is the cosine of the central angle of a regular icosahedron; see A105199 for the angle itself. - _Clark Kimberling_, Feb 10 2009
%C A020762 Largest radius of ten circles tangent to a circle of radius 1. - _Charles R Greathouse IV_, Jan 14 2013
%C A020762 This constant times 10 gives the linear asymptotic coefficient of the variance of the number of basepairs in an RNA secondary structure on a number n of vertices tending to infinity (see Theorem 3 in Bu, Kauers, and Zeilberger). - _Stefano Spezia_, Feb 27 2026
%H A020762 Ivan Panchenko, <a href="/A020762/b020762.txt">Table of n, a(n) for n = 0..1000</a>
%H A020762 AJ Bu, Manuel Kauers, and Doron Zeilberger, <a href="https://arxiv.org/abs/2602.19255">Statistical Analysis of Hairpins and BasePairs in RNA Secondary Structures</a>, arXiv:2602.19255 [math.CO], 2026.
%H A020762 Hideyuki Ohtsuka, <a href="https://www.fq.math.ca/Problems/ElemProbSolnMay14.pdf">Problem B-1148</a>, Elementary Problems and Solutions, The Fibonacci Quarterly, Vol. 52, No. 2 (2014), p. 179; <a href="https://www.fq.math.ca/Problems/ElemProbSolnMay15.pdf">The Exact Value of an Infinite Series</a>, Solution to B-1148, ibid., Vol. 53, No. 2 (2015), pp. 183-184.
%H A020762 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%F A020762 Equals cos(arctan(2)). - _Clark Kimberling_, Feb 10 2009
%F A020762 Equals lim_{n -> infinity} A000045(n)/A000032(n). - _Bruno Berselli_, Jan 22 2018
%F A020762 From _Christian Katzmann_, Mar 19 2018: (Start)
%F A020762 Equals Sum_{n>=0} (2*n)!/(n!^2*3^(2*n+1)).
%F A020762 Equals Sum_{n>=0} 5*(2*n+1)!/(n!^2*3^(2*n+3)). (End)
%F A020762 Equals A010476/10. - _R. J. Mathar_, Jan 14 2021
%F A020762 Equals Sum_{k>=1} F(2^(k-1))/(L(2^k)+1) = Sum_{k>=0} A058635(k)/(A001566(k)+1), where F(k) = A000045(k) is the k-th Fibonacci number and L(k) = A000032(k) is the k-th Lucas number (Ohtsuka, 2014). - _Amiram Eldar_, Dec 09 2021
%F A020762 Equals 1/A002163. - _R. J. Mathar_, Feb 27 2026
%e A020762 0.447213595499957939281834733746255247088123671922305144854179449082104...
%t A020762 RealDigits[5^(-1/2), 10, 150] (* _Stefan Steinerberger_, Apr 08 2006 *)
%t A020762 Circs[n_] := With[{r = Sin[Pi/n]/(1 - Sin[Pi/n])}, Graphics[Append[
%t A020762   Table[Circle[(r + 1) {Sin[2 Pi k/n], Cos[2 Pi k/n]}, r], {k, n}],
%t A020762     {Blue, Circle[{0, 0}, 1]}]]]
%t A020762 Circs[10] (* _Charles R Greathouse IV_, Jan 14 2013 *)
%o A020762 (PARI) 1/sqrt(5) \\ _Charles R Greathouse IV_, Jan 14 2013
%Y A020762 Cf. A000032, A000045, A010476, A001566, A058635, A105199.
%K A020762 nonn,cons
%O A020762 0,1
%A A020762 _N. J. A. Sloane_
%E A020762 More terms from _Stefan Steinerberger_, Apr 08 2006
```

## Candidate 134: A025658 vs A025673 (score 72.4, agree 105, variant raw, family size 24)
Terms: 0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 0, 4, 1, 2, 3, 0, 4, 1, 5, 2, 3, 0, 4, 1, 5, 2

### A025658
```
%I A025658 #14 Jul 09 2025 12:51:15
%S A025658 0,0,1,0,1,2,0,1,2,3,0,1,2,3,0,4,1,2,3,0,4,1,5,2,3,0,4,1,5,2,6,3,0,4,
%T A025658 1,5,2,6,3,0,7,4,1,5,2,6,3,0,7,4,1,8,5,2,6,3,0,7,4,1,8,5,2,9,6,3,0,7,
%U A025658 4,1,8,5,2,9,6,3,10,0,7,4,1,8,5,2,9,6,3,10,0,7,4,11,1,8,5,2,9,6,3,10,0,7,4,11,1
%N A025658 Exponent of 6 (value of j) in n-th number of form 4^i*6^j.
%H A025658 Amiram Eldar, <a href="/A025658/b025658.txt">Table of n, a(n) for n = 1..10000</a>
%H A025658 <a href="/index/Se#sequences_which_agree_for_a_long_time">Index entries for sequences which agree for a long time but are different</a>.
%F A025658 a(n) = A122841(A025618(n)). - _Amiram Eldar_, Jul 09 2025
%t A025658 With[{max = 10^10}, IntegerExponent[Sort[Flatten[Table[4^i*6^j, {i, 0, Log[4, max]}, {j, 0, Log[6, max/4^i]}]]], 6]] (* _Amiram Eldar_, Jul 09 2025 *)
%Y A025658 Cf. A025618, A025647, A122841.
%Y A025658 Differs from A025673 at a(2805).
%K A025658 nonn
%O A025658 1,6
%A A025658 _David W. Wilson_
```
### A025673
```
%I A025673 #17 Jul 09 2025 12:50:38
%S A025673 0,0,1,0,1,2,0,1,2,3,0,1,2,3,0,4,1,2,3,0,4,1,5,2,3,0,4,1,5,2,6,3,0,4,
%T A025673 1,5,2,6,3,0,7,4,1,5,2,6,3,0,7,4,1,8,5,2,6,3,0,7,4,1,8,5,2,9,6,3,0,7,
%U A025673 4,1,8,5,2,9,6,3,10,0,7,4,1,8,5,2,9,6,3,10,0,7,4,11,1,8,5,2,9,6,3,10,0,7,4,11,1
%N A025673 Exponent of 8 (value of j) in n-th number of form 5^i*8^j.
%H A025673 Amiram Eldar, <a href="/A025673/b025673.txt">Table of n, a(n) for n = 1..10000</a>
%H A025673 <a href="/index/Se#sequences_which_agree_for_a_long_time">Index entries for sequences which agree for a long time but are different</a>.
%F A025673 a(n) = A244413(A025623(n)). - _Amiram Eldar_, Jul 09 2025
%t A025673 Take[Sort[Flatten[Table[{5^i 8^j,j},{i,0,20},{j,0,20}],1]][[;;,2]],120] (* _Harvey P. Dale_, Nov 10 2024 *)
%t A025673 With[{max = 10^11}, IntegerExponent[Sort[Flatten[Table[5^i*8^j, {i, 0, Log[5, max]}, {j, 0, Log[8, max/5^i]}]]], 8]] (* _Amiram Eldar_, Jul 09 2025 *)
%Y A025673 Cf. A025623, A025653, A244413.
%Y A025673 Differs from A025658 at a(2805).
%K A025673 nonn
%O A025673 1,6
%A A025673 _David W. Wilson_
```

## Candidate 135: A046978 vs A075553 (score 72.4, agree 105, variant abs, family size 3)
Terms: 0, 1, 1, 1, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1

### A046978
```
%I A046978 #47 Nov 26 2025 15:59:35
%S A046978 0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,
%T A046978 -1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,
%U A046978 1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0,1,1,1,0,-1,-1,-1,0
%N A046978 Numerators of Taylor series for exp(x)*sin(x).
%C A046978 Period 8: repeat [0, 1, 1, 1, 0, -1, -1, -1].
%C A046978 Lehmer sequence U_n for R=2, Q=1. - _Artur Jasinski_, Oct 06 2008
%C A046978 4*a(n+6) = period 8: repeat -4,-4,0,4,4,4,0,-4 = A189442(n+1) + A189442(n+5). - _Paul Curtz_, Jun 03 2011
%C A046978 This is a strong elliptic divisibility sequence t_n as given in [Kimberling, p. 16] where x = 1, y = 1, z = 0. - _Michael Somos_, Nov 27 2019
%D A046978 G. W. Caunt, Infinitesimal Calculus, Oxford Univ. Press, 1914, p. 477.
%H A046978 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,-1).
%H A046978 C. Kimberling, <a href="https://www.fq.math.ca/Scanned/17-1/kimberling1.pdf">Strong divisibility sequences and some conjectures</a>, Fib. Quart., 17 (1979), 13-17.
%F A046978 Euler transform of length 8 sequence [1, 0, -1, -1, 0, 0, 0, 1]. - _Michael Somos_, Jul 16 2006
%F A046978 G.f.: x * (1 + x + x^2) / (1 + x^4) = x * (1 - x^3) * (1 - x^4) / ((1 - x) * (1 - x^8)). a(-n) = a(n + 4) = -a(n). - _Michael Somos_, Jul 16 2006
%F A046978 a(n) = round((b^n - c^n)/(b - c)) where b = sqrt(2)-((1+i)/sqrt(2)), c = (1+i)/sqrt(2). - _Artur Jasinski_, Oct 06 2008
%F A046978 a(n) = sign(cos(Pi*(n-2)/4)). - _Wesley Ivan Hurt_, Oct 02 2013
%e A046978 G.f. = x + x^2 + x^3 - x^5 - x^6 - x^7 + x^9 + x^10 + x^11 - x^13 - x^14 - ...
%e A046978 1*x + 1*x^2 + (1/3)*x^3 - (1/30)*x^5 - (1/90)*x^6 - (1/630)*x^7 + (1/22680)*x^9 + (1/113400)*x^10 + ...
%p A046978 A046978 := n -> `if`(n mod 4 = 0,0,(-1)^iquo(n,4)): # _Peter Luschny_, Aug 21 2011
%t A046978 a = -((1 + I)/Sqrt[2]) + Sqrt[2]; b = (1 + I)/Sqrt[2]; Table[ Round[(a^n - b^n)/(a - b)], {n, 0, 200}] (* _Artur Jasinski_, Oct 06 2008 *)
%t A046978 Table[Sign[Cos[Pi*(n-2)/4]],{n,0,100}] (* _Wesley Ivan Hurt_, Oct 10 2013 *)
%t A046978 LinearRecurrence[{0,0,0,-1},{0,1,1,1},120] (* or *) PadRight[{},120,{0,1,1,1,0,-1,-1,-1}] (* _Harvey P. Dale_, Mar 17 2017 *)
%o A046978 (PARI) {a(n) = (n%4 > 0) * (-1)^(n\4)}; /* _Michael Somos_, Jul 16 2006 */
%Y A046978 Cf. A046979.
%K A046978 sign,frac,easy
%O A046978 0,1
%A A046978 _N. J. A. Sloane_
```
### A075553
```
%I A075553 #15 Oct 06 2026 18:00:42
%S A075553 0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,
%T A075553 -1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,
%U A075553 -1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0,1,-1,1,0,-1,1,-1,0
%N A075553 Numerators in the Maclaurin series for arctan(1+x).
%H A075553 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/InverseTangent.html">Inverse Tangent</a>.
%F A075553 Euler transform of length 8 sequence [ -1, 1, 1, -1, 0, -1, 0, 1]. - _Michael Somos_, Jul 16 2006
%F A075553 G.f.: x(1-x+x^2)/(1+x^4) = x(1-x)(1-x^4)(1-x^6)/((1-x^2)(1-x^3)(1-x^8)). a(-n) = a(n+4) = -a(n). - _Michael Somos_, Jul 16 2006
%t A075553 a[n_] := I ((-1 - I)^n - (-1 + I)^n)/2^Floor[1 + n/2]; Table[a[n], {n, 0, 100}]
%o A075553 (PARI) a(n)=[0,1,-1,1,0,-1,1,-1][n%8+1] /* _Michael Somos_, Jul 16 2006 */
%Y A075553 Cf. A075554.
%K A075553 sign,easy
%O A075553 0,1
%A A075553 _Eric W. Weisstein_, Sep 23 2002
```

## Candidate 136: A052409 vs A327503 (score 72.4, agree 105, variant raw, family size 12)
Terms: 0, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1

### A052409
```
%I A052409 #59 Feb 16 2025 08:32:41
%S A052409 0,1,1,2,1,1,1,3,2,1,1,1,1,1,1,4,1,1,1,1,1,1,1,1,2,1,3,1,1,1,1,5,1,1,
%T A052409 1,2,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,6,1,1,1,1,
%U A052409 1,1,1,1,1,1,1,1,1,1,1,1,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1
%N A052409 a(n) = largest integer power m for which a representation of the form n = k^m exists (for some k).
%C A052409 Greatest common divisor of all prime-exponents in canonical factorization of n for n>1: a(n)>1 iff n is a perfect power; a(A001597(k))=A025479(k). - _Reinhard Zumkeller_, Oct 13 2002
%C A052409 a(1) set to 0 since there is no largest finite integer power m for which a representation of the form 1 = 1^m exists (infinite largest m). - _Daniel Forgues_, Mar 06 2009
%C A052409 A052410(n)^a(n) = n. - _Reinhard Zumkeller_, Apr 06 2014
%C A052409 Positions of 1's are A007916. Smallest base is given by A052410. - _Gus Wiseman_, Jun 09 2020
%H A052409 Daniel Forgues, <a href="/A052409/b052409.txt">Table of n, a(n) for n = 1..100000</a>
%H A052409 N. J. A. Sloane, <a href="/A278028/a278028.txt">Maple programs for A007916, A278028, A278029, A052409, A089723, A277564</a>
%H A052409 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/Power.html">Power</a>
%H A052409 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/PerfectPower.html">Perfect Power</a>
%H A052409 <a href="/index/Eu#epf">Index entries for sequences computed from exponents in factorization of n</a>
%F A052409 a(1) = 0; for n > 1, a(n) = gcd(A067029(n), a(A028234(n))). - _Antti Karttunen_, Aug 07 2017
%e A052409 n = 72 = 2*2*2*3*3: GCD[exponents] = GCD[3,2] = 1. This is the least n for which a(n) <> A051904(n), the minimum of exponents.
%e A052409 For n = 10800 = 2^4 * 3^3 * 5^2, GCD[4,3,2] = 1, thus a(10800) = 1.
%p A052409 # See link.
%p A052409 #
%p A052409 a:= n-> igcd(map(i-> i[2], ifactors(n)[2])[]):
%p A052409 seq(a(n), n=1..120);  # _Alois P. Heinz_, Oct 20 2019
%t A052409 Table[GCD @@ Last /@ FactorInteger[n], {n, 100}] (* _Ray Chandler_, Jan 24 2006 *)
%o A052409 (Haskell)
%o A052409 a052409 1 = 0
%o A052409 a052409 n = foldr1 gcd $ a124010_row n
%o A052409 -- _Reinhard Zumkeller_, May 26 2012
%o A052409 (PARI) a(n)=my(k=ispower(n)); if(k, k, n>1) \\ _Charles R Greathouse IV_, Oct 30 2012
%o A052409 (Scheme) (define (A052409 n) (if (= 1 n) 0 (gcd (A067029 n) (A052409 (A028234 n))))) ;; _Antti Karttunen_, Aug 07 2017
%o A052409 (Python)
%o A052409 from math import gcd
%o A052409 from sympy import factorint
%o A052409 def A052409(n): return gcd(*factorint(n).values()) # _Chai Wah Wu_, Aug 31 2022
%Y A052409 Cf. A052410, A005361, A051903, A072411-A072414, A124010, A075802, A072776, A270492.
%Y A052409 Apart from the initial term essentially the same as A253641.
%Y A052409 Differs from A051904 for the first time at n=72, where a(72) = 1, while A051904(72) = 2.
%Y A052409 Differs from A158378 for the first time at n=10800, where a(10800) = 1, while A158378(10800) = 2.
%Y A052409 Cf. A000005, A000961, A001597, A052410, A303386, A327501.
%K A052409 nonn
%O A052409 1,4
%A A052409 _Eric W. Weisstein_
%E A052409 More terms from _Labos Elemer_, Jun 17 2002
```
### A327503
```
%I A327503 #20 Apr 03 2022 22:53:39
%S A327503 0,1,1,2,1,1,1,3,2,1,1,1,1,1,1,4,1,1,1,1,1,1,1,1,2,1,3,1,1,1,1,5,1,1,
%T A327503 1,2,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,6,1,1,1,1,
%U A327503 1,1,1,1,1,1,1,1,1,1,1,1,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1
%N A327503 Number of steps to reach a fixed point starting with n and repeatedly taking the quotient by the maximum divisor that is 1 or not a perfect power (A327501, A327502).
%C A327503 First differs from A052409 and A158378 at a(216) = 2, A052409(216) = A158378(216) = 3.
%C A327503 A multiset is aperiodic if its multiplicities are relatively prime. The Heinz number of an integer partition (y_1,...,y_k) is prime(y_1)*...*prime(y_k). Heinz numbers of aperiodic multisets are numbers that are not perfect powers (A007916).
%C A327503 a(n) does not depend only on the prime signature of n. A351948 gives the positions where a(A046523(n)) <> a(n). n = 125000 is the first time this happens, see the examples. - _Antti Karttunen_, Apr 03 2022
%H A327503 Antti Karttunen, <a href="/A327503/b327503.txt">Table of n, a(n) for n = 1..65537</a>
%H A327503 Gus Wiseman, <a href="https://docs.google.com/document/d/e/2PACX-1vSX9dPMGJhxB8rOknCGvOs6PiyhupdWNpqLsnphdgU6MEVqFBnWugAXidDhwHeKqZe_YnUqYeGOXsOk/pub">Sequences counting and encoding certain classes of multisets</a>
%F A327503 a(2^n) = n.
%e A327503 The transformation A327502 takes 144 -> 2 -> 1, so a(144) = 2.
%e A327503 From _Antti Karttunen_, Apr 03 2022: (Start)
%e A327503 For n = 1728 = 2^6 * 3^3, A327501(1728) = 864 = 2^5 * 3^3, and therefore A327502(1728) = 1728/864 = 2. A327501(2) = 2, thus A327502(2) = 2/2 = 1, so we reached 1 (= A327502(1)) in two steps, and therefore a(1728) = 2.
%e A327503 For n = 125000 = 2^3 * 5^6, A327501(125000) = 31250 = 2^1 * 5^6, and therefore A327502(125000) = 125000/31250 = 4. A327501(4) = 2, thus A327502(4) = 4/2 = 2, from which we reach 1 in one more step, therefore a(125000) = 3.
%e A327503 (End)
%t A327503 Table[Length[FixedPointList[#/Max[Select[Divisors[#],GCD@@Last/@FactorInteger[#]==1&]]&,n]]-2,{n,100}]
%o A327503 (PARI)
%o A327503 A327502(n) = if(n==1, 1, n/vecmax(select(x->((x>1) && !ispower(x)), divisors(n))));
%o A327503 A327503(n) = { my(u=A327502(n)); if(u==n, 0, 1+A327503(u)); }; \\ _Antti Karttunen_, Apr 02 2022
%Y A327503 See link for additional cross-references.
%Y A327503 Cf. A000961, A001597, A007916 (positions of 1's), A052409, A158378, A303386, A327501, A327502, A351948.
%Y A327503 Cf. also A327500.
%K A327503 nonn
%O A327503 1,4
%A A327503 _Gus Wiseman_, Sep 16 2019
%E A327503 Data section extended up to 105 terms by _Antti Karttunen_, Apr 02 2022
```

## Candidate 137: A069158 vs A359155 (score 72.4, agree 105, variant abs, family size 11)
Terms: 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, -1, 1

### A069158
```
%I A069158 #45 Apr 27 2026 01:20:14
%S A069158 1,-1,-1,0,-1,1,-1,0,0,1,-1,0,-1,1,1,0,-1,0,-1,0,1,1,-1,0,0,1,0,0,-1,
%T A069158 1,-1,0,1,1,1,0,-1,1,1,0,-1,1,-1,0,0,1,-1,0,0,0,1,0,-1,0,1,0,1,1,-1,0,
%U A069158 -1,1,0,0,1,1,-1,0,1,1,-1,0,-1,1,0,0,1,1,-1,0,0,1,-1,0,1,1,1,0,-1,0,1,0,1,1,1,0,-1,0,0,0,-1,1,-1,0,1,1
%N A069158 a(n) = Product_{d|n} mu(d), product over positive divisors, d, of n, where mu(d) = Moebius function (A008683).
%C A069158 Absolute value of a(n) = absolute value of mu(n).
%C A069158 Differs from A080323 at n=2, 105, 165, 195, 231, ..., 15015,..., 19635,.. (cf. A046389, A046391, ...) - _R. J. Mathar_, Dec 15 2008
%C A069158 Not multiplicative: For example a(2)*a(15) <> a(30). - _R. J. Mathar_, Mar 31 2012
%C A069158 Row products of table A225817. - _Reinhard Zumkeller_, Jul 30 2013
%C A069158 a(n) is the determinant of the symmetric tau(n) X tau(n) matrix M(n) defined by M(n) = [tau(d_i*d_j)], where d_i, d_j run through the divisors of n. - _Ridouane Oudra_, Apr 26 2026
%H A069158 Reinhard Zumkeller, <a href="/A069158/b069158.txt">Table of n, a(n) for n = 1..10000</a>
%F A069158 a(n) = 0 if mu(n) = 0 (A013929); a(n) = -1 if n = prime; a(n) = 1 if n = squarefree composite (A120944) or 1.
%F A069158 a(n) = A008966(n) - 2*A010051(n). - _Amiram Eldar_, Feb 10 2025
%e A069158 a(6) = mu(1)*mu(2)*mu(3)*mu(6) = 1*(-1)*(-1)*1 = 1.
%p A069158 A069158 := proc(n)
%p A069158     mul(numtheory[mobius](d),d=numtheory[divisors](n)) ;
%p A069158 end proc: # _R. J. Mathar_, May 28 2016
%t A069158 a[n_] := Product[MoebiusMu[d], {d, Divisors[n]}]; Array[a, 106] (* _Jean-François Alcover_, Feb 22 2018 *)
%o A069158 (Magma) f := function(n); t1 := &*[MoebiusMu(d) : d in Divisors(n) ]; return t1; end function;
%o A069158 (Haskell)
%o A069158 a069158 = product . a225817_row  -- _Reinhard Zumkeller_, Jul 30 2013
%o A069158 (PARI) a(n) = vecprod(apply(moebius, divisors(n))); \\ _Amiram Eldar_, Feb 10 2025
%o A069158 (Python)
%o A069158 from sympy import mobius, isprime
%o A069158 def A069158(n): return 0 if not mobius(n) else -1 if isprime(n) else 1 # _Chai Wah Wu_, Apr 25 2026
%Y A069158 Cf. A008683, A008966, A010051, A013929, A046389, A046391, A080323, A225817, A000005, A190902.
%K A069158 sign,easy
%O A069158 1,1
%A A069158 _Leroy Quet_, Apr 08 2002
```
### A359155
```
%I A359155 #21 Dec 29 2022 06:31:10
%S A359155 1,-1,1,0,1,-1,1,0,0,-1,1,0,1,-1,1,0,1,0,1,0,1,-1,1,0,0,-1,0,0,1,-1,1,
%T A359155 0,1,-1,1,0,1,-1,1,0,1,-1,1,0,0,-1,1,0,0,0,1,0,1,0,1,0,1,-1,1,0,1,-1,
%U A359155 0,0,1,-1,1,0,1,-1,1,0,1,-1,0,0,1,-1,1,0,0,-1,1,0,1,-1,1,0,1,0,1,0,1,-1,1,0,1,0,0,0,1,-1,1,0,1
%N A359155 Dirichlet inverse of A359154, where A359154 is multiplicative with a(p^e) = (-1)^(p*e).
%H A359155 Antti Karttunen, <a href="/A359155/b359155.txt">Table of n, a(n) for n = 1..100000</a>
%F A359155 Multiplicative with a(p) = (-1)^(1+p), and a(p^e) = 0 if e > 1.
%F A359155 a(n) = A008683(n) * A359154(n).
%F A359155 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A359154(n/d) * a(d).
%F A359155 For all n >= 1, a(A003961(n)) = A008966(n).
%F A359155 Dirichlet g.f.: (zeta(s)/zeta(2*s))*((2^s-1)/(2^s+1)). - _Amiram Eldar_, Dec 29 2022
%t A359155 f[p_, e_] := If[e == 1, 1, 0]; f[2, e_] := If[e == 1, -1, 0]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Dec 29 2022 *)
%o A359155 (PARI) A359155(n) = { my(f = factor(n)); prod(k=1, #f~, (1==f[k,2])*((-1)^(1+f[k, 1]))); };
%o A359155 (PARI) A359155(n) = { my(f = factor(n)); moebius(n)*prod(k=1, #f~, (-1)^(f[k, 1]*f[k, 2])); };
%o A359155 (Python)
%o A359155 from functools import reduce
%o A359155 from operator import ixor
%o A359155 from sympy import factorint
%o A359155 def A359155(n): return 0 if max((f:=factorint(n)).values(),default=0) > 1 else -1 if reduce(ixor,(p&1^1 for p in f.keys()),0) else 1 # _Chai Wah Wu_, Dec 21 2022
%Y A359155 Cf. A001414, A003961, A008683, A008966, A359154.
%K A359155 sign,mult
%O A359155 1
%A A359155 _Antti Karttunen_, Dec 19 2022
```

## Candidate 138: A077267 vs A081602 (score 72.4, agree 105, variant raw, family size 3)
Terms: 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 1, 1, 1, 0, 0, 1, 0, 0, 2, 1, 1, 1, 0, 0, 1, 0, 0, 3, 2, 2

### A077267
```
%I A077267 #45 Oct 22 2026 10:12:59
%S A077267 1,0,0,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,3,2,2,2,1,1,2,
%T A077267 1,1,2,1,1,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,3,2,2,2,1,1,2,1,1,2,1,1,1,0,
%U A077267 0,1,0,0,2,1,1,1,0,0,1,0,0,4,3,3,3,2,2,3,2,2,3,2,2,2,1,1,2,1,1,3,2,2,2,1,1,2
%N A077267 Number of zeros in base-3 expansion of n.
%H A077267 Reinhard Zumkeller, <a href="/A077267/b077267.txt">Table of n, a(n) for n = 0..10000</a>
%H A077267 Franklin T. Adams-Watters and Frank Ruskey, <a href="https://cs.uwaterloo.ca/journals/JIS/VOL12/Ruskey2/ruskey14.html">Generating Functions for the Digital Sum and Other Digit Counting Sequences</a>, JIS 12 (2009) 09.5.6.
%H A077267 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/Ternary.html">Ternary</a>.
%H A077267 Wikipedia, <a href="https://en.wikipedia.org/wiki/Ternary_numeral_system">Ternary numeral system</a>
%F A077267 a(1)=a(2)=0; a(3n)=a(n)+1; a(3n+1)=a(3n+2)=a(n). a(3^n-2)=a(3^n-1)=0; a(3^n)=n. a(n)=A077266(n, 3).
%F A077267 a(n) + A062756(n) + A081603(n) = A081604(n). - _Reinhard Zumkeller_, Mar 23 2003
%F A077267 G.f.: 1 + (Sum_{k>=0} x^(3^(k+1))/(1 + x^(3^k) + x^(2*3^k)))/(1-x). - _Franklin T. Adams-Watters_, Nov 03 2005
%F A077267 a(n) = A079978(n) if n < 3, A079978(n) + a(floor(n/3)) otherwise. - _Reinhard Zumkeller_, Feb 21 2013
%e A077267 a(8)=0 since 8 written in base 3 is 22 with 0 zeros;
%e A077267 a(9)=2 since 9 written in base 3 is 100 with 2 zeros;
%e A077267 a(10)=1 since 10 written in base 3 is 101 with 1 zero.
%t A077267 Table[Count[IntegerDigits[n,3],0],{n,0,6!}] (* _Vladimir Joseph Stephan Orlovsky_, Jul 25 2009 *)
%t A077267 (* Alternative: *)
%t A077267 DigitCount[Range[0,110],3,0] (* _Harvey P. Dale_, Jul 04 2021 *)
%o A077267 (Haskell)
%o A077267 a077267 n = a079978 n + if n < 3 then 0 else a077267 (n `div` 3)
%o A077267 -- _Reinhard Zumkeller_, Feb 21 2013
%o A077267 (PARI) a(n) = if (n==0, 1, my(d=digits(n,3)); sum(k=1, #d, d[k] == 0)); \\ _Michel Marcus_, Apr 17 2026
%Y A077267 Cf. A023416, A077266, A062756, A081603.
%Y A077267 Cf. A007089, A081605, A032924, A081607, A081608, A134023. - _Reinhard Zumkeller_, Mar 23 2003
%K A077267 base,nonn,changed
%O A077267 0,10
%A A077267 _Henry Bottomley_, Nov 01 2002
%E A077267 a(0)=1 added, offset changed to 0 and b-file adjusted by _Reinhard Zumkeller_, Feb 21 2013
%E A077267 Wrong formula deleted by _Reinhard Zumkeller_, Feb 21 2013
```
### A081602
```
%I A081602 #18 Feb 16 2022 11:14:09
%S A081602 1,0,0,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,3,2,2,2,1,1,2,
%T A081602 1,1,2,1,1,1,0,0,1,0,0,2,1,1,1,0,0,1,0,0,3,2,2,2,1,1,2,1,1,2,1,1,1,0,
%U A081602 0,1,0,0,2,1,1,1,0,0,1,0,0,4,3,3,3,2,2,3,2,2,3,2,2,2,1,1,2,1,1,3,2,2,2,1,1
%N A081602 Number of 0's in ternary representation of n.
%C A081602 Duplicate of A077267.
%K A081602 dead
%O A081602 0,10
%A A081602 _Reinhard Zumkeller_, Mar 23 2003
```

## Candidate 139: A083650 vs A138514 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, -1, 2, -1, 0, 2, -1, 0, 0, -2, -1, 2, -2, 0, -2, 1, 0, 2, 0, -2, 0, 1, 0, 0, -2, 0, 0, 0, -1, -2

### A083650
```
%I A083650 #33 Feb 16 2025 08:32:49
%S A083650 1,-1,2,-1,0,2,-1,0,0,-2,-1,2,-2,0,-2,1,0,2,0,-2,0,1,0,0,-2,0,0,0,-1,
%T A083650 -2,2,0,2,0,0,2,3,0,0,-2,0,0,-2,0,2,-1,2,0,0,0,2,-2,0,-2,2,1,-2,2,0,0,
%U A083650 0,0,0,0,0,2,-1,0,0,0,0,-2,2,0,-2,2,0,-2,-1,0,-2,0,-2,0,-2,0,0,4,0,0,0,1,0,0,0,-2,-2,0,0,0,2,2,0,0,-2
%N A083650 Expansion of f(-x, x^3) * phi(x^2) in powers of x where phi(), f() are Ramanujan theta functions.
%C A083650 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A083650 Essentially the expansion of eta(q)*eta(q^2). Cf. A010815. - _N. J. A. Sloane_, Feb 18 2010
%C A083650 A030204, A083650 and A138514 are the same except for signs. - _N. J. A. Sloane_, May 07 2010
%H A083650 G. C. Greubel, <a href="/A083650/b083650.txt">Table of n, a(n) for n = 0..1000</a>
%H A083650 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A083650 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A083650 Euler transform of period 16 sequence [ -1, 2, 1, -2, 1, 1, -1, -3, -1, 1, 1, -2, 1, 2, -1, -2, ...].
%F A083650 G.f.: (Sum_{k>=0} (-1)^(k + [k/4]) * x^(k*(k+1)/2)) * (Sum_k x^(2*k^2)).
%F A083650 (-1)^[n/2] * a(n) = A030204(n).
%e A083650 G.f. = 1 - x + 2*x^2 - x^3 + 2*x^5 - x^6 - 2*x^9 - x^10 + 2*x^11 - 2*x^12 - 2*x^14 + ...
%e A083650 G.f. = q - q^9 + 2*q^17 - q^25 + 2*q^41 - q^49 + 2*q^73 - q^81 + 2*q^89 - 2*q^97 + ...
%t A083650 QP = QPochhammer; s = QP[q]*QP[q^2] + O[q]^105; Table[(-1)^Quotient[n, 2]*Coefficient[s, q, n], {n, 0, 105}] (* _Jean-François Alcover_, Nov 27 2015, adapted from PARI *)
%o A083650 (PARI) {a(n) = my(A); if( n<0, 0, A = x * O(x^n); (-1)^(n\2) * polcoeff( eta(x + A) * eta(x^2 + A), n))}; /* _Michael Somos_, Mar 02 2010 */
%Y A083650 Cf. A000122, A000700, A010054, A010815, A030204, A083650, A121373, A138514, A143433.
%K A083650 sign
%O A083650 0,3
%A A083650 _Michael Somos_, May 01 2003
%E A083650 Revised by _Michael Somos_, Mar 02 2010
```
### A138514
```
%I A138514 #30 May 30 2026 16:40:32
%S A138514 1,1,-2,-1,0,-2,1,0,0,2,1,2,-2,0,2,1,0,-2,0,-2,0,-1,0,0,-2,0,0,0,-1,2,
%T A138514 -2,0,2,0,0,2,3,0,0,-2,0,0,2,0,2,1,-2,0,0,0,-2,-2,0,2,-2,1,-2,-2,0,0,
%U A138514 0,0,0,0,0,-2,1,0,0,0,0,-2,2,0,2,2,0,2,1,0,-2,0,2,0,-2,0,0,4,0,0,0,1,0,0,0,-2,-2,0,0,0,2,-2,0,0,-2
%N A138514 Expansion of q^(-1/8) * eta(q^2)^4 / (eta(q) * eta(q^4)) in powers of q.
%C A138514 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A138514 Number 70 of the 74 eta-quotients listed in Table I of Martin (1996).
%C A138514 A030204, A083650 and A138514 are the same except for signs. - _N. J. A. Sloane_, May 07 2010
%H A138514 Seiichi Manyama, <a href="/A138514/b138514.txt">Table of n, a(n) for n = 0..10000</a>
%H A138514 Y. Martin, <a href="https://doi.org/10.1090/S0002-9947-96-01743-6">Multiplicative eta-quotients</a>, Trans. Amer. Math. Soc. 348 (1996), no. 12, 4825-4856, see page 4852 Table I.
%H A138514 Michael Somos, <a href="/A030203/a030203.txt">Index to Yves Martin's list of 74 multiplicative eta-quotients and their A-numbers</a>
%H A138514 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A138514 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A138514 Expansion of f(x) * f(-x^2) = psi(-x) * phi(x) = chi(x) * f(-x^2)^2 = psi(x) * phi(-x^2) = f(x)^2 / chi(x) = f(x)^3 / phi(x) = f(-x^2)^3 / psi(-x) = phi(x)^2 / chi(x)^3 = chi(x)^3 * psi(-x)^2 = (f(x)^3 * psi(-x))^(1/2) = (f(-x^2)^3 * phi(x))^(1/2) in powers of x where phi(), psi(), chi(), f() are Ramanujan theta functions.
%F A138514 Expansion of psi(i * x) * psi(-i * x) in powers x^2 where i^2 = -1 and psi() is a Ramanujan theta function. - _Michael Somos_, Feb 16 2014
%F A138514 Euler transform of period 4 sequence [ 1, -3, 1, -2, ...].
%F A138514 a(n) = b(8*n + 1) where b(n) is multiplicative and b(2^e) = 0^e, b(p^e) = 0 if p == 3, 5, 7 (mod 8) and e odd, b(p^e) = 1 if p == 3 (mod 4) and e even, b(p^e) = (-1)^(e/2) if p == 5 (mod 8) and e even, b(p^e) = e+1 if p == 1 (mod 8) and p = x^2 + 64*y^2, b(p^e) = (-1)^e * (e+1) if p == 1 (mod 8) and p is not of the form x^2 + 64*y^2.
%F A138514 a(9*n + 1) = a(n), a(9*n + 4) = a(9*n + 7) = 0. a(n) = (-1)^n * A030204(n) = (-1)^floor((n+1)/2) * A083650(n).
%F A138514 G.f.: Product_{k>0} (1 - x^(2*k))^2 * (1 + x^(2*k - 1)).
%F A138514 G.f. is a period 1 Fourier series which satisfies f(-1 / (256 t)) = 16 (t/i) f(t) where q = exp(2 Pi i t). - _Michael Somos_, Jun 10 2015
%F A138514 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = (1/2) * exp(Pi / 8) * sqrt(Pi) * 2^(1/4) / Gamma(3/4)^2 = A388638. - _Simon Plouffe_, Sep 18 2025
%e A138514 G.f. = 1 + x - 2*x^2 - x^3 - 2*x^5 + x^6 + 2*x^9 + x^10 + 2*x^11 - 2*x^12 + ...
%e A138514 G.f. = q + q^9 - 2*q^17 - q^25 - 2*q^41 + q^49 + 2*q^73 + q^81 + 2*q^89 + ...
%t A138514 a[ n_] := SeriesCoefficient[ QPochhammer[ x^2] QPochhammer[ -x], {x, 0, n}]; (* _Michael Somos_, Jun 10 2015 *)
%t A138514 a[ n_] := SeriesCoefficient[ QPochhammer[ x^2]^4 / (QPochhammer[ x] QPochhammer[ x^4]), {x, 0, n}]; (* _Michael Somos_, Jun 10 2015 *)
%o A138514 (PARI) {a(n) = my(A); if( n<0, 0, A = x * O(x^n); polcoeff( eta(x^2 + A)^4 / (eta(x + A) * eta(x^4 + A)), n))};
%o A138514 (PARI) {a(n) = my(A, p, e); if( n<0, 0, n = 8*n + 1; A = factor(n); prod(k=1, matsize(A)[1], [p, e] = A[k,]; if( p==2, 0, p%8==1, (e+1) * if( qfbclassno( -8 * p) / 4 % 2, (-1)^e, 1), if( e%2==0, (-1)^(e/2 * (p%8==5)))))) };
%o A138514 (PARI) {a(n) = if( n<0, 0, n = 8*n + 1; (qfrep([ 1, 0; 0, 64], n) - qfrep([ 4, 2; 2, 17], n))[n])};
%Y A138514 Cf. A030204, A083650.
%K A138514 sign
%O A138514 0,3
%A A138514 _Michael Somos_, Mar 22 2008
```

## Candidate 140: A093829 vs A113447 (score 72.4, agree 105, variant abs, family size 4)
Terms: 1, -1, 1, 1, 0, -1, 2, -1, 1, 0, 0, 1, 2, -2, 0, 1, 0, -1, 2, 0, 2, 0, 0, -1, 1, -2, 1, 2, 0, 0

### A093829
```
%I A093829 #48 Oct 04 2026 10:13:42
%S A093829 1,-1,1,1,0,-1,2,-1,1,0,0,1,2,-2,0,1,0,-1,2,0,2,0,0,-1,1,-2,1,2,0,0,2,
%T A093829 -1,0,0,0,1,2,-2,2,0,0,-2,2,0,0,0,0,1,3,-1,0,2,0,-1,0,-2,2,0,0,0,2,-2,
%U A093829 2,1,0,0,2,0,0,0,0,-1,2,-2,1,2,0,-2,2,0,1,0,0,2,0,-2,0,0,0,0,4,0,2,0,0,-1,2,-3,0,1,0,0,2,-2,0
%N A093829 Expansion of q * psi(q^3)^3 / psi(q) in powers of q where psi() is a Ramanujan theta function.
%C A093829 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A093829 Cubic AGM theta functions: a(q) (see A004016), b(q) (A005928), c(q) (A005882).
%H A093829 G. C. Greubel, <a href="/A093829/b093829.txt">Table of n, a(n) for n = 1..1000</a>
%H A093829 James A. Sellers and Roberto Tauraso, <a href="https://arxiv.org/abs/2505.12813">Arithmetic properties of MacMahon-type sums of divisors: the odd case</a>, arXiv:2505.12813 [math.NT], 2025. See p. 3.
%H A093829 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>, 2019.
%H A093829 Pavel Tikhonov, Elena Tutubalina, Ivan Oseledets, Dmitry I. Ignatov, and Mikhail Seleznyov, <a href="https://arxiv.org/abs/2609.32264">LANTERN: Illuminating Hidden Mathematical Knowledge in Language Models</a>, arXiv:2609.32264 [cs.CL], 2026. See pp. 14, 16, 26, 48 (Summary Table).
%H A093829 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>.
%F A093829 Expansion of (a(q) - a(q^2)) / 6 = c(q^2)^2 / (3 * c(q)) in powers of q where a(), c() are cubic AGM functions. - _Michael Somos_, Sep 06 2007
%F A093829 Expansion of (eta(q) * eta(q^6)^6) / (eta(q^2)^2 * eta(q^3)^3) in powers of q.
%F A093829 Euler transform of period 6 sequence [ -1, 1, 2, 1, -1, -2, ...].
%F A093829 Moebius transform is period 6 sequence [ 1, -2, 0, 2, -1, 0, ...] = A112300. - _Michael Somos_, Jul 16 2006
%F A093829 Multiplicative with a(p^e) = (-1)^e if p=2; a(p^e) = 1 if p=3; a(p^e) = 1+e if p == 1 (mod 6); a(p^e) = (1 + (-1)^e) / 2 if p == 5 (mod 6).
%F A093829 G.f. is a period 1 Fourier series which satisfies f(-1 / (6 t)) = 12^(-1/2) (t/i) g(t) where q = exp(2 Pi i t) and g() is g.f. for A122859.
%F A093829 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^4)) where f(u, v, w) = w * (u + v)^2 - v * (v + w) * (v + 4*w).
%F A093829 G.f. A(x) satisfies 0 = f(A(x), A(x^2), A(x^3), A(x^6)) where f(u1, u2, u3, u6) = u2 * (u2 - u3 - 4*u6) - (u3 + u6) * (u1 - 3*u3 - 3*u6).
%F A093829 G.f.: Sum_{k>0} (x^k - 2 * x^(2*k) + 2 * x^(4*k) - x^(5*k)) / (1 - x^(6*k)) = x * Product_{k>0} ((1 - x^k) * (1 - x^(6*k))^6) / ((1 - x^(2*k))^2 * (1 - x^(3*k))^3).
%F A093829 a(n) = -(-1)^n * A113447(n). - _Michael Somos_, Jan 31 2015
%F A093829 a(2*n) = -a(n). a(3*n) = a(n). a(6*n + 5) = 0.
%F A093829 A035178(n) = |a(n)|. A033762(n) = a(2*n + 1). A033687(n) = a(3*n + 1).
%F A093829 a(4*n + 1) = A112604(n). a(4*n + 3) = A112605(n). a(6*n + 1) = A097195(n). a(8*n + 1) = A112606(n). a(8*n + 3) = A112608(n). a(8*n + 5) = 2 * A112607(n).
%F A093829 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi/(6*sqrt(3)) = 0.302299894039... . - _Amiram Eldar_, Nov 21 2023
%e A093829 G.f. = q - q^2 + q^3 + q^4 - q^6 + 2*q^7 - q^8 + q^9 + q^12 + 2*q^13 + ...
%t A093829 a[ n_] := If[ n < 1, 0, DivisorSum[ n, {1, -2, 0, 2, -1, 0} [[ Mod[#, 6, 1]]] &]];
%t A093829 QP = QPochhammer; s = (QP[q]*QP[q^6]^6)/(QP[q^2]^2*QP[q^3]^3) + O[q]^105; CoefficientList[s, q] (* _Jean-François Alcover_, Nov 30 2015, adapted from PARI *)
%o A093829 (PARI) {a(n) = if( n<1, 0, polcoeff( sum( k=0, n, x^k * (1 - x^k)^2 / (1 + x^(2*k) + x^(4*k)), x * O(x^n)), n))};
%o A093829 (PARI) {a(n) = local(A); if( n<1, 0, n--; A = x * O(x^n); polcoeff( eta(x + A) * eta(x^6 + A)^6 / (eta(x^2 + A)^2 * eta(x^3 + A)^3), n))};
%o A093829 (PARI) {a(n) = if( n<1, 0, sumdiv( n, d, kronecker( -12, d) - if( d%2==0, 2 * kronecker( -3, d/2) ) ))}; /* _Michael Somos_, May 29 2005 */
%o A093829 (SageMath) ModularForms( Gamma1(6), 1, prec=90).1; # _Michael Somos_, Sep 27 2013
%o A093829 (Magma) Basis( ModularForms( Gamma1(6), 1), 90) [2]; /* _Michael Somos_, Jul 02 2014 */
%Y A093829 Cf. A033687, A033762, A035178, A112300, A113447, A122859.
%Y A093829 Cf. A097195, A112604, A112605, A112606, A112607, A112608. - _Michael Somos_, Sep 27 2013
%Y A093829 Cf. A000700, A000122, A010054, A121373.
%K A093829 sign,mult,easy
%O A093829 1,7
%A A093829 _Michael Somos_, Apr 17 2004
```
### A113447
```
%I A113447 #37 Sep 18 2025 16:17:52
%S A113447 1,1,1,-1,0,1,2,1,1,0,0,-1,2,2,0,-1,0,1,2,0,2,0,0,1,1,2,1,-2,0,0,2,1,
%T A113447 0,0,0,-1,2,2,2,0,0,2,2,0,0,0,0,-1,3,1,0,-2,0,1,0,2,2,0,0,0,2,2,2,-1,
%U A113447 0,0,2,0,0,0,0,1,2,2,1,-2,0,2,2,0,1,0,0,-2,0,2,0,0,0,0,4,0,2,0,0,1,2,3,0,-1,0,0,2,2,0
%N A113447 Expansion of i * theta_2(i * q^3)^3 / (4 * theta_2(i * q)) in powers of q^2.
%C A113447 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A113447 Cubic AGM theta functions: a(q) (see A004016), b(q) (A005928), c(q) (A005882).
%H A113447 G. C. Greubel, <a href="/A113447/b113447.txt">Table of n, a(n) for n = 1..1000</a>
%H A113447 Li-Chien Shen, <a href="https://doi.org/10.1090/S0002-9939-1994-1212287-3">On the Modular Equations of Degree 3</a>, Proc. Amer. Math. Soc. 122 (1994), no. 4, 1101-1114. See p. 1105, equation (3.8).
%H A113447 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>, 2019.
%H A113447 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>.
%F A113447 Expansion of (eta(q^2) * eta(q^3)^3 * eta(q^12)^3) / (eta(q) * eta(q^4) * eta(q^6)^3) in powers of q.
%F A113447 Euler transform of period 12 sequence [1, 0, -2, 1, 1, 0, 1, 1, -2, 0, 1, -2, ...].
%F A113447 Moebius transform is period 12 sequence [1, 0, 0, -2, -1, 0, 1, 2, 0, 0, -1, 0, ...].
%F A113447 a(n) is multiplicative and a(2^e) = -(-1)^e if e>0, a(3^e) = 1, a(p^e) = e+1 if p == 1 (mod 6), a(p^e) = (1+(-1)^e)/2 if p == 5 (mod 6).
%F A113447 G.f.: Sum_{k>0} x^(6*k - 5) / (1 - x^(6*k - 5)) - x^(6*k - 1) / (1 - x^(6*k - 1)) - 2 * x^(12*k - 8) / (1 - x^(12*k - 8)) + 2 * x^(12*k - 4) / (1 - x^(12*k-4)).
%F A113447 G.f.: Sum_{k>0} x^k * (1 - x^(3*k))^2 / (1 + x^(4*k) + x^(8*k)).
%F A113447 G.f.: x * Product_{k>0} (1 - x^k) / (1 - x^(4*k - 2)) * ((1 - x^(12*k - 6)) / (1 - x^(3*k)))^3.
%F A113447 Expansion of theta_2(i * q^3)^3 / (4 * theta_2(i * q)) in powers of q^2.
%F A113447 Expansion of q * psi(-q^3)^3 / psi(-q) in powers of q where psi() is a Ramanujan theta function.
%F A113447 Expansion of (c(q) * c(q^4)) / (3 * c(q^2)) in powers of q where c() is a cubic AGM theta function.
%F A113447 G.f. is a period 1 Fourier series which satisfies f(-1 / (12 t)) = (4/3)^(1/2) (t/i) g(t) where q = exp(2 Pi i t) and g(t) is the g.f. for A132973.
%F A113447 a(n) = -(-1)^n * A093829(n). - _Michael Somos_, Jan 31 2015
%F A113447 Convolution inverse of A133637.
%F A113447 a(3*n) = a(n). a(6*n + 5) = a(12*n + 10) = 0. |a(n)| = A035178(n).
%F A113447 a(2*n) = A093829(n). a(2*n + 1) = A033762(n).
%F A113447 a(4*n + 1) = A112604(n). a(4*n + 3) = A112605(n).
%F A113447 a(6*n + 1) = A097195(n). a(6*n + 2) = A033687(n).
%F A113447 a(8*n + 1) = A112606(n). a(8*n + 3) = A112608(n). a(8*n + 5) = 2 * A112607(n). a(8*n + 6) = A112605(n). a(8*n + 7) = 2 * A112609(n).
%F A113447 a(12*n + 1) = A123884(n). a(12*n + 7) = 2 * A121361(n).
%F A113447 a(24*n + 1) = A131961(n). a(24*n + 7) = 2 * A131962(n). a(24*n + 13) = 2 * A121963(n). a(24*n + 19) = 2 * A131964(n).
%F A113447 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi/(6*sqrt(3)) = 0.604599... (A073010). - _Amiram Eldar_, Nov 23 2023
%F A113447 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = (1/36) * exp(Pi) * Pi^2*3^(1/2) * Gamma(11/12)^3 * sqrt(2) * (3^(1/2)-1)^3 / Gamma(2/3)^3 / Gamma(3/4)^5 = A388557. - _Simon Plouffe_, Sep 18 2025
%e A113447 G.f. = q + q^2 + q^3 - q^4 + q^6 + 2*q^7 + q^8 + q^9 - q^12 + 2*q^13 + ...
%t A113447 a[ n_] := If[ n < 1, 0, DivisorSum[ n, {1, 0, 0, -2, -1, 0, 1, 2, 0, 0, -1, 0}[[Mod[#, 12, 1]]] &]]; (* _Michael Somos_, Jan 31 2015 *)
%o A113447 (PARI) {a(n) = if( n<1, 0, -(-1)^max( 1, valuation( n, 2)) * sumdiv(n, d, kronecker( -12, d)))};
%o A113447 (PARI) {a(n) = if( n<1, 0, direuler( p=2, n, if( p==2, 1 + X / (1 + X), 1 / ((1 - X) * (1 - kronecker( -12, p) * X))))[n])};
%o A113447 (PARI) {a(n) = local(A); if( n<1, 0, n--; A = x * O(x^n); polcoeff( eta(x^2 + A) * eta(x^3 + A)^3 * eta(x^12 + A)^3 / (eta(x + A) * eta(x^4 + A) * eta(x^6 + A)^3), n))};
%o A113447 (PARI) {a(n) = if( n<1, 0, sumdiv(n, d, [ 0, 1, 0, 0, -2, -1, 0, 1, 2, 0, 0,-1][d%12 + 1]))}; /* _Michael Somos_, May 07 2015 */
%o A113447 (Magma) A := Basis( ModularForms( Gamma1(24), 1), 106); A[2] + A[3] + A[4] - A[5] + A[7] + 2*A[8] + A[9] + A[10]; /* _Michael Somos_, May 07 2015 */
%Y A113447 Cf. A033687, A033762, A035178, A073010, A093829, A097195, A112604, A112605, A112606, A112607, A112608, A112609, A121361, A123884, A131961, A131962, A131963, A131964. A133637.
%Y A113447 Cf. A000122, A000700, A004016, A005882, A005928, A010054, A121373.
%K A113447 sign,easy,mult
%O A113447 1,7
%A A113447 _Michael Somos_, Nov 02 2005
```

## Candidate 141: A099443 vs A132342 (score 72.4, agree 105, variant abs, family size 4)
Terms: 1, 1, 1, 1, 0, -1, -1, -1, -1, 0, 1, 1, 1, 1, 0, -1, -1, -1, -1, 0, 1, 1, 1, 1, 0, -1, -1, -1, -1, 0

### A099443
```
%I A099443 #32 Feb 23 2026 10:52:21
%S A099443 1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,
%T A099443 -1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,
%U A099443 -1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0
%N A099443 A Chebyshev transform of Fib(n+1).
%C A099443 The denominator is the 10th cyclotomic polynomial. It is also associated to the knots 4_1 and 5_1 by the Alexander and Jones polynomials respectively. The g.f. is the image of the g.f. of Fib(n+1) under the Chebyshev transform A(x)->(1/(1+x^2))A(x/(1+x^2)).
%C A099443 With offset 1 this is a strong elliptic divisibility sequence t_n as given in [Kimberling, p. 16] where x = y = z = 1.
%H A099443 Dror Bar-Natan, <a href="http://katlas.org/">The Rolfsen Knot Table</a>
%H A099443 C. Kimberling, <a href="https://www.fq.math.ca/Scanned/17-1/kimberling1.pdf">Strong divisibility sequences and some conjectures</a>, Fib. Quart., 17 (1979), 13-17.
%H A099443 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (1,-1,1,-1).
%F A099443 G.f.: (1+x^2)/(1-x+x^2-x^3+x^4).
%F A099443 a(n) = sqrt(2*(10 - 4*sqrt(5))/25)*cos((6*Pi*n +Pi)/10) + sqrt(2*(4*sqrt(5) + 10)/25)*sin(Pi*(n+1)/5).
%F A099443 a(n) = Sum_{k=0..floor(n/2)} binomial(n-k, k)*(-1)^k*Fib(n-2k+1).
%F A099443 a(n) = Sum_{k=0..n} binomial((n+k)/2, k)*(-1)^((n-k)/2)*(1+(-1)^(n+k))*Fib(k+1)/2.
%F A099443 a(n) = Sum_{k=0..n} A014019(n-k)*binomial(1, k/2)(1+(-1)^k)/2.
%F A099443 With a leading zero, this is sum{k=0..floor(n/2), binomial(n-k-1, k)(-1)^kFib(n-2k)}, or the image of x/(1-x-x^2) under the mapping g(x)->g(x/(1+x^2)). - _Paul Barry_, Jan 16 2005
%F A099443 Euler transform of length 10 sequence [1, 0, 0, -1, -1, 0, 0, 0, 0, 1]. - _Michael Somos_, Sep 18 2006
%F A099443 G.f.: (1 - x^4) * (1 - x^5) / ((1 - x) * (1 - x^10)). - _Michael Somos_, Sep 18 2006
%F A099443 a(n) = -a(n-5) = -a(-2-n) for all n in Z. - _Michael Somos_, Sep 18 2006
%F A099443 Hankel transform is 1,0,0,1,0,0,0,... - _Paul Barry_, Jun 24 2008
%F A099443 0 = (a(n) - a(n+1)) * (a(n) - a(n+1) + a(n+2)) for all n in Z. - _Michael Somos_, Jul 07 2014
%F A099443 0 = a(n)*a(n-4) - a(n-1)*a(n-3) + a(n-2)*a(n-2) for all n in Z. - _Michael Somos_, Jul 07 2014
%F A099443 0 = a(n)*a(n+5) - a(n+1)*a(n+4) + a(n+2)*a(n+3) for all n in Z. - _Michael Somos_, Jul 07 2014
%F A099443 a(n) = (-1)^n * A156174(n). - _Michael Somos_, Oct 17 2018
%F A099443 a(n) = A014019(n-2)+A014019(n). - _R. J. Mathar_, Feb 23 2026
%e A099443 G.f. = 1 + x + x^2 + x^3 - x^5 - x^6 - x^7 - x^8 + x^10 + x^11 + x^12 + ...
%t A099443 a[ n_] := With[ {m = n + 1}, Sign[Mod[m, 5]] (-1)^Quotient[m, 5]]; (* _Michael Somos_, Jun 17 2015 *)
%t A099443 LinearRecurrence[{1, -1, 1, -1}, {1, 1, 1, 1}, 50] (* _G. C. Greubel_, Aug 08 2017 *)
%o A099443 (PARI) {a(n) = n++; sign(n%5) * (-1)^(n\5)}; /* _Michael Somos_, Sep 18 2006 */
%Y A099443 Cf. A156174.
%K A099443 easy,sign
%O A099443 0,1
%A A099443 _Paul Barry_, Oct 16 2004
```
### A132342
```
%I A132342 #14 Sep 16 2015 13:55:28
%S A132342 1,1,1,1,0,-1,-1,-1,-1,0,-1,1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,
%T A132342 1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,
%U A132342 -1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0,1,-1,-1,1,0
%N A132342 a(n) = (a(n-1)*a(n-4)) - (a(n-2)*a(n-3)), with a(1)=a(2)=a(3)=a(4)=1.
%C A132342 Becomes cyclic with period 5: {-1, 1, 0, 1, -1} at a(13). - _Stefan Steinerberger_, Nov 17 2007
%H A132342 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (-1, -1, -1, -1).
%t A132342 a[1] = a[2] = a[3] = a[4] = 1; a[n_] := a[n] = a[n - 1]*a[n - 4] - a[n - 2]*a[n - 3]; Array[a, 105] (* _Robert G. Wilson v_, Nov 09 2007 *)
%t A132342 a = {1, 1, 1, 1}; Do[AppendTo[a, a[[ -1]]*a[[ -4]] - a[[ -2]]*a[[ -3]]], {90}]; a (* _Stefan Steinerberger_, Nov 17 2007 *)
%K A132342 sign,easy
%O A132342 1,1
%A A132342 _Ben Branman_, Nov 08 2007
%E A132342 More terms from _Robert G. Wilson v_, Nov 09 2007
```

## Candidate 142: A101871 vs A101875 (score 72.4, agree 105, variant raw, family size 3)
Terms: 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1

### A101871
```
%I A101871 #10 Sep 23 2023 03:41:17
%S A101871 1,1,1,1,2,1,1,1,1,1,1,1,2,3,1,1,1,1,1,1,1,1,2,1,2,1,1,1,1,1,1,2,1,1,
%T A101871 1,1,1,2,1,1,5,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,2,1,2,1,3,1,1,1,1,3,
%U A101871 1,1,1,1,1,2,1,1,2,1,1,1,1,1,1,1,2,2,1,2,1,1,1,1,1,1,3,1,1,1,1,1,1,1,1,2,1
%N A101871 Number of Abelian groups of order 2n+1.
%F A101871 From _Amiram Eldar_, Sep 23 2023: (Start)
%F A101871 a(n) = A000688(2*n+1) = A000688(4*n+2).
%F A101871 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = 2 * A048651 * A021002 = 1.32545452721253858057... . (End)
%t A101871 a[n_] := FiniteAbelianGroupCount[2*n + 1]; Array[a, 100, 0] (* _Amiram Eldar_, Sep 23 2023 *)
%Y A101871 Bisection of A000688.
%Y A101871 Cf. A021002, A048651.
%K A101871 nonn,easy
%O A101871 0,5
%A A101871 _N. J. A. Sloane_, Jan 28 2005
%E A101871 More terms from _Joshua Zucker_, May 10 2006
```
### A101875
```
%I A101875 #10 Sep 23 2023 12:11:58
%S A101875 1,1,1,1,2,1,1,1,1,1,1,1,2,3,1,1,1,1,1,1,1,1,2,1,2,1,1,1,1,1,1,2,1,1,
%T A101875 1,1,1,2,1,1,5,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,2,1,2,1,3,1,1,1,1,3,
%U A101875 1,1,1,1,1,2,1,1,2,1,1,1,1,1,1,1,2,2,1,2,1,1,1,1,1,1,3,1,1,1,1,1,1,1,1,2,1
%N A101875 Duplicate of A101871.
%C A101875 Previous name: Number of Abelian groups of order 4n+2.
%Y A101875 Bisection of A101872.
%K A101875 dead
%O A101875 0,5
%A A101875 _N. J. A. Sloane_, Jan 28 2005
%E A101875 More terms from _Joshua Zucker_, May 10 2006
```

## Candidate 143: A103391 vs A331743 (score 72.4, agree 105, variant raw, family size 4)
Terms: 1, 2, 2, 3, 2, 4, 3, 5, 2, 6, 4, 7, 3, 8, 5, 9, 2, 10, 6, 11, 4, 12, 7, 13, 3, 14, 8, 15, 5, 16

### A103391
```
%I A103391 #44 Mar 29 2024 02:13:24
%S A103391 1,2,2,3,2,4,3,5,2,6,4,7,3,8,5,9,2,10,6,11,4,12,7,13,3,14,8,15,5,16,9,
%T A103391 17,2,18,10,19,6,20,11,21,4,22,12,23,7,24,13,25,3,26,14,27,8,28,15,29,
%U A103391 5,30,16,31,9,32,17,33,2,34,18,35,10,36,19,37,6,38,20,39,11,40,21,41,4,42,22,43,12,44,23,45,7,46,24,47,13,48,25,49,3,50,26,51,14,52,27,53,8
%N A103391 "Even" fractal sequence for the natural numbers: Deleting every even-indexed term results in the same sequence.
%C A103391 A003602 is the "odd" fractal sequence for the natural numbers.
%C A103391 Lexicographically earliest infinite sequence such that a(i) = a(j) => A348717(A005940(i)) = A348717(A005940(j)) for all i, j >= 1. A365718 is an analogous sequence related to A356867 (Doudna variant D(3)). - _Antti Karttunen_, Sep 17 2023
%H A103391 Antti Karttunen, <a href="/A103391/b103391.txt">Table of n, a(n) for n = 1..65537</a> (terms 1..10000 from Reinhard Zumkeller)
%F A103391 For n > 1, a(n) = A003602(n-1) + 1. - _Benoit Cloitre_, May 26 2007, indexing corrected by _Antti Karttunen_, Feb 05 2020
%F A103391 a((2*n-3)*2^p+1) = n, p >= 0 and n >= 2, with a(1) = 1. - _Johannes W. Meijer_, Jan 28 2013
%F A103391 Sum_{k=1..n} a(k) ~ n^2/6. - _Amiram Eldar_, Sep 24 2023
%p A103391 nmax := 82: for p from 0 to ceil(simplify(log[2](nmax))) do for n from 2 to ceil(nmax/(p+2))+1 do a((2*n-3)*2^p+1) := n od: od: a(1) := 1: seq(a(n), n=1..nmax); # _Johannes W. Meijer_, Jan 28 2013
%t A103391 a[n_] := ((n-1)/2^IntegerExponent[n-1, 2] + 3)/2; a[1] = 1; Array[a, 100] (* _Amiram Eldar_, Sep 24 2023 *)
%o A103391 (Haskell)
%o A103391 -- import Data.List (transpose)
%o A103391 a103391 n = a103391_list !! (n-1)
%o A103391 a103391_list = 1 : ks where
%o A103391    ks = concat $ transpose [[2..], ks]
%o A103391 -- _Reinhard Zumkeller_, May 23 2013
%o A103391 (PARI)
%o A103391 A003602(n) = (n/2^valuation(n, 2)+1)/2; \\ From A003602
%o A103391 A103391(n) = if(1==n,1,(1+A003602(n-1))); \\ _Antti Karttunen_, Feb 05 2020
%o A103391 (Python)
%o A103391 def v(n): b = bin(n); return len(b) - len(b.rstrip("0"))
%o A103391 def b(n): return (n//2**v(n)+1)//2
%o A103391 def a(n): return 1 if n == 1 else 1 + b(n-1)
%o A103391 print([a(n) for n in range(1, 106)]) # _Michael S. Branicky_, May 29 2022
%o A103391 (Python)
%o A103391 def A103391(n): return (n-1>>(n-1&-n+1).bit_length())+2 if n>1 else 1 # _Chai Wah Wu_, Jan 04 2024
%Y A103391 Cf. A003602, A005940, A025480, A220466, A286387, A353368 (Dirichlet inverse).
%Y A103391 Cf. also A110962, A110963, A365718.
%Y A103391 Differs from A331743(n-1) for the first time at n=192, where a(192) = 97, while A331743(191) = 23.
%Y A103391 Differs from A351460.
%K A103391 easy,nonn
%O A103391 1,2
%A A103391 _Eric Rowland_, Mar 20 2005
%E A103391 Data section extended up to a(105) (to better differentiate from several nearby sequences) by _Antti Karttunen_, Feb 05 2020
```
### A331743
```
%I A331743 #14 Feb 05 2020 16:53:34
%S A331743 1,2,2,3,2,4,3,5,2,6,4,7,3,8,5,9,2,10,6,11,4,12,7,13,3,14,8,15,5,16,9,
%T A331743 17,2,18,10,19,6,20,11,21,4,22,12,23,7,24,13,25,3,26,14,27,8,28,15,29,
%U A331743 5,30,16,31,9,32,17,33,2,34,18,35,10,36,19,37,6,38,20,39,11,40,21,41,4,42,22,43,12,44,23,45,7,46,24,47,13,48,25,49,3,50,26,51,14,52,27,53,8,54
%N A331743 Lexicographically earliest infinite sequence such that a(i) = a(j) => A002487(i) = A002487(j) and A323901(i) = A323901(j) for all i, j.
%C A331743 Restricted growth sequence transform of the ordered pair [A002487(n), A002487(A163511(n))].
%C A331743 For all i, j:
%C A331743   a(i) = a(j) => A331748(i) = A331748(j),
%C A331743   a(i) = a(j) => A331749(i) = A331749(j).
%H A331743 Antti Karttunen, <a href="/A331743/b331743.txt">Table of n, a(n) for n = 0..65537</a>
%H A331743 <a href="/index/Bi#binary">Index entries for sequences related to binary expansion of n</a>
%H A331743 <a href="/index/St#Stern">Index entries for sequences related to Stern's sequences</a>
%F A331743 a(2^n) = 2 for all n >= 0.
%o A331743 (PARI)
%o A331743 \\ Needs also code from A323901.
%o A331743 up_to = 65537;
%o A331743 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A331743 Aux331743(n) = [A002487(n), A323901(n)];
%o A331743 v331743 = rgs_transform(vector(1+up_to, n, Aux331743(n-1)));
%o A331743 A331743(n) = v331743[1+n];
%Y A331743 Cf. A002487, A163511, A323901, A324400, A331742, A331744, A331748, A331749.
%Y A331743 Differs from A331745 for the first time at n=77, where a(77) = 40, while A331745(77) = 24.
%Y A331743 Differs from A103391(1+n) for the first time at n=191, where a(191) = 23, while A103391(192) = 97.
%K A331743 nonn
%O A331743 0,2
%A A331743 _Antti Karttunen_, Feb 05 2020
```

## Candidate 144: A106459 vs A143433 (score 72.4, agree 105, variant abs, family size 4)
Terms: 1, -1, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0

### A106459
```
%I A106459 #65 Sep 17 2025 23:04:39
%S A106459 1,-1,0,-1,0,0,1,0,0,0,1,0,0,0,0,-1,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,
%T A106459 0,0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,
%U A106459 0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0
%N A106459 Expansion of f(-x, -x^3) in powers of x where f(,) is Ramanujan's general theta function.
%C A106459 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A106459 This is a expansion of Ramanujan's general theta function in powers of x because |a(n)| = A010054(n) is also the characteristic function of generalized hexagonal numbers. - _Omar E. Pol_, Jun 13 2012
%C A106459 Number 4 of the 14 primitive eta-products which are holomorphic modular forms of weight 1/2 listed by D. Zagier on page 30 of "The 1-2-3 of Modular Forms". - _Michael Somos_, May 04 2016
%C A106459 Also the number of partitions of n into an even number of parts, where each part occurs at most 3 times, minus the number of partitions of n into an odd number of parts, where each part occurs at most 3 times. - _Jeremy Lovejoy_, Aug 04 2020
%D A106459 D. M. Bressoud, Proofs and Confirmations, Camb. Univ. Press, 1999; p. 53, Exer. 2.2.10
%H A106459 Seiichi Manyama, <a href="/A106459/b106459.txt">Table of n, a(n) for n = 0..1000</a>
%H A106459 D. R. Hickerson, <a href="https://doi.org/10.1016/0097-3165(73)90083-6">Identities relating the number of partitions into an even and odd number of parts</a>, J. Combin. Theory Ser. A, 15 (1973), 351-353.
%H A106459 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A106459 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A106459 Expansion of psi(-x) = f(x^6, x^10) - x * f(x^2, x^14) in powers of x where psi() is a Ramanujan theta function, and f(,) is Ramanujan's general theta function.
%F A106459 Expansion of q^(-1/8) * eta(q) * eta(q^4) / eta(q^2) in powers of q.
%F A106459 Euler transform of period 4 sequence [ -1, 0, -1, -1, ...].
%F A106459 G.f. is a period 1 Fourier series which satisfies f(-1 / (256 t)) = 4 (t/i)^(1/2) f(t) where q = exp(2 Pi i t).
%F A106459 Given g.f. A(x), then B(q) = q * A(q^8) satisfies 0 = f(B(q), B(q^2), B(q^3), B(q^6)) where f(u1, u2, u3, u6) = u1^4*u6^4 + u1^3*u2*u3^3*u6 + 2*u1*u2^3*u3*u6^3 - u2^4*u3^4.
%F A106459 a(n) = b(8*n + 1) where b() is multiplicative with b(p^e) = Kronecker(2, p)^(e/2) if e even, b(p^e) = 0 if e odd.
%F A106459 G.f.: Product_{k>0} (1 - x^k) * (1 + x^(2*k)) = Product_{k>0} (1 - x^k)  / (1 - x^(4*k - 2)).
%F A106459 G.f.: Product_{k>0} (1 - x^(2*k)) / (1 + x^(2*k - 1)) = Product_{k>0} (1 - x^(4*k)) * (1 - x^(2*k - 1)).
%F A106459 G.f.: Sum_{k>=0} a(k) * x^(8*k + 1) = Sum_{k in Z} (-1)^k * x^((4*k + 1)^2).
%F A106459 G.f.: Sum_{k>=0} (-x)^(k*(k + 1)/2) = Sum_{k in Z} x^(8*k^2 + 2*k) - x^(8*k^2 + 6*k + 1).
%F A106459 G.f. A(x) satisfies: x / A(F(x)) = F(x) = g.f. of A192540.
%F A106459 Convolution inverse of A006950.
%F A106459 |a(n)| = A010054(n) the characteristic function of triangular numbers.
%F A106459 G.f.: 1 + (-x)*(1 + (-x)^2*(1 + (-x)^3*(1 + ...))). - _Michael Somos_, Mar 03 2014
%F A106459 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = (1/2) * exp(Pi / 8) * Pi^(1/4) * 2^(1/4) / Gamma(3/4) = A388502. - _Simon Plouffe_, Sep 17 2025
%e A106459 G.f. = 1 - x - x^3 + x^6 + x^10 - x^15 - x^21 + x^28 + x^36 - x^45 - x^55 + x^66 + ...
%e A106459 G.f. = q - q^9 - q^25 + q^49 + q^81 - q^121 - q^169 + q^225 + q^289 - q^361 - ...
%t A106459 a[ n_] := If[ SquaresR[ 1, 8 n + 1] == 2, (-1)^Quotient[ Sqrt[8 n + 1] + 1, 4], 0]; (* _Michael Somos_, Nov 18 2011 *)
%t A106459 a[ n_] := SeriesCoefficient[ EllipticTheta[ 2, Pi/4, q] / (2^(1/2) q^(1/4)), {q, 0, 2 n}]; (* _Michael Somos_, Nov 18 2011 *)
%o A106459 (PARI) {a(n) = my(A); if( n<0, 0, A = x * O(x^n); polcoeff( eta(x + A) * eta(x^4 + A) / eta(x^2 + A), n))}
%o A106459 (PARI) {a(n) = my(x); if( issquare( 8*n + 1, &x), kronecker( 2, x))};
%Y A106459 Cf. A006950, A010054, A192540.
%K A106459 sign
%O A106459 0,1
%A A106459 _Michael Somos_, May 02 2005
```
### A143433
```
%I A143433 #15 Feb 16 2025 08:33:08
%S A143433 1,-1,0,1,0,0,-1,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,
%T A143433 0,0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,
%U A143433 -1,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0
%N A143433 Expansion of f(-x, x^3) in powers of x where f(,) is Ramanujan's general theta function.
%C A143433 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%H A143433 G. C. Greubel, <a href="/A143433/b143433.txt">Table of n, a(n) for n = 0..1000</a>
%H A143433 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A143433 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A143433 Euler transform of period 16 sequence [ -1, 0, 1, 1, 1, -1, -1, -2, -1, -1, 1, 1, 1, 0, -1, -1, ...].
%F A143433 Pattern of signs of nonzero terms is A143431.
%F A143433 G.f.: Sum_{k>=0} (-1)^(k + floor(k/4)) * x^(k * (k+1) / 2).
%F A143433 a(n) = (-1)^n * A143434(n).
%F A143433 a(2*n) = A244465(n). a(2*n + 1) = - A244525(n). a(3*n + 2) = a(5*n + 2) = a(5*n + 4) = 0.
%e A143433 G.f. = 1 - x + x^3 - x^6 - x^10 + x^15 - x^21 + x^28 + x^36 - x^45 + x^55 + ...
%e A143433 G.f. = q - q^9 + q^25 - q^49 - q^81 + q^121 - q^169 + q^225 + q^289 + ...
%t A143433 a[ n_] := SeriesCoefficient[ QPochhammer[ x, -x^4] QPochhammer[ -x^3, -x^4] QPochhammer[ -x^4], {x, 0, n}]; (* _Michael Somos_, Jun 03 2015 *)
%o A143433 (PARI) {a(n) = if( n<0, 0, if( issquare(8*n + 1, &n), n = n\2; (-1)^(n + n\4), 0))};
%o A143433 (PARI) {a(n) = my(A); if( n<0, 0, polcoeff( prod(k=1, n, (1 - x^k)^( [1, 1, 0, -1, -1, -1, 1, 1, 2, 1, 1, -1, -1, -1, 0, 1, 1] [k%16 + 1]), 1 + x * O(x^n)), n))};
%Y A143433 Cf. A143434, A244465, A244525.
%K A143433 sign
%O A143433 0,1
%A A143433 _Michael Somos_, Aug 14 2008
```

## Candidate 145: A106510 vs A163804 (score 72.4, agree 105, variant abs, family size 8)
Terms: 1, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1

### A106510
```
%I A106510 #41 Dec 28 2025 02:27:07
%S A106510 1,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,
%T A106510 -1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,
%U A106510 1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1,0,1,-1
%N A106510 Expansion of (1+x)^2/(1+x+x^2).
%C A106510 Row sums of the Riordan array ((1+x)/(1+x+x^2),x/(1+x)), A106509.
%C A106510 Equals INVERT transform of (1, -2, 3, -4, 5, ...). - _Gary W. Adamson_, Oct 10 2008
%H A106510 <a href="/index/Rec#order_02">Index entries for linear recurrences with constant coefficients</a>, signature (-1,-1).
%F A106510 a(n) = Sum_{k=0..n} Sum_{j=0..n-k} (-1)^j*binomial(2n-k-j, j)
%F A106510 a(n) = A049347(n-1) = A102283(n) if n >= 1. - _R. J. Mathar_, Aug 07 2011
%F A106510 From _Michael Somos_, Oct 15 2008: (Start)
%F A106510 Euler transform of length 3 sequence [ 1, -2, 1].
%F A106510 a(n) is multiplicative with a(3^e) = 0^e, a(p^e) = 1 if p == 1 (mod 3), a(p^e) = (-1)^e if p == 2 (mod 3).
%F A106510 G.f. A(x) satisfies 0=f(A(x), A(x^2)) where f(u, v) = 4 - 3*v - u * (4 - 2*v - u). (End)
%F A106510 a(-n) = a(n). a(n+3) = a(n) unless n = 0 or n = -3.
%F A106510 a(n) = Sum_{k=0..n} A128908(n,k)*(-1)^(n-k). - _Philippe Deléham_, Jan 22 2012
%F A106510 E.g.f.: 1 + 2*exp(-x/2)*sin(sqrt(3)*x/2)/sqrt(3). - _Amiram Eldar_, Dec 28 2025
%e A106510 1 + x - x^2 + x^4 - x^5 + x^7 - x^8 + x^10 - x^11 + x^13 - x^14 + ...
%t A106510 {1}~Join~LinearRecurrence[{-1, -1}, {1, -1}, 105] (* _Jean-François Alcover_, Oct 28 2019 *)
%o A106510 (PARI) {a(n) = if( n==0, 1, [0, 1, -1][n%3 + 1])} \\ _Michael Somos_, Oct 15 2008
%o A106510 (PARI) {a(n) = if( n==0, 1, kronecker(-3, n))} \\ _Michael Somos_, Oct 15 2008
%o A106510 (PARI) A106510(n)=kronecker(-3, n+!n) \\ _M. F. Hasler_, May 07 2018
%Y A106510 Cf. A049347, A102283, A106509, A128908.
%K A106510 easy,sign,mult
%O A106510 0,1
%A A106510 _Paul Barry_, May 04 2005
%E A106510 Edited by _M. F. Hasler_, May 07 2018
```
### A163804
```
%I A163804 #22 Oct 17 2026 17:17:23
%S A163804 1,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,
%T A163804 1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,
%U A163804 -1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0,-1,1,0
%N A163804 Expansion of (1 - x) * (1 - x^4) / ((1 - x^2) * (1 - x^3)) in powers of x.
%H A163804 G. C. Greubel, <a href="/A163804/b163804.txt">Table of n, a(n) for n = 0..1000</a>
%H A163804 <a href="/index/Rec#order_02">Index entries for linear recurrences with constant coefficients</a>, signature (-1,-1).
%F A163804 Euler transform of length 4 sequence [ -1, 1, 1, -1].
%F A163804 G.f. A(x) satisfies 0 = f(A(x), A(x^2)) where f(u, v) = 2 - v - u * (4 - 2*v - u).
%F A163804 a(3*n) = 0 unless n=0, a(3*n + 1) = -1, a(3*n + 2) = a(0) = 1.
%F A163804 a(-n) = -a(n) unless n=0. a(n+3) = a(n) unless n=0 or n=-3.
%F A163804 G.f.: (1 + x^2) / (1 + x + x^2).
%F A163804 G.f.: A(x) = 1 / (1 + x / (1 + x^2)) = 1 - x / (1 + x / (1 - x / (1 + x))). - _Michael Somos_, Jan 03 2013
%F A163804 a(n) = A057078(n-2), n>1. - _R. J. Mathar_, Aug 06 2009
%F A163804 From _Ridouane Oudra_, Jan 09 2025: (Start)
%F A163804 a(n) = 3*floor((n+1)/3) - n, for n>0.
%F A163804 a(n) = 2*sin(4*Pi*n/3)/sqrt(3), for n>0.
%F A163804 a(n) = - A102283(n), for n>0.
%F A163804 a(n) = - A106510(n), for n>0. (End)
%e A163804 G.f. = 1 - x + x^2 - x^4 + x^5 - x^7 + x^8 - x^10 + x^11 - x^13 + x^14 + ...
%p A163804 1, seq(2*sin(4*Pi*n/3)/sqrt(3), n=1..100); # _Ridouane Oudra_, Jan 09 2025
%t A163804 Join[{1},LinearRecurrence[{-1, -1},{-1, 1},105]] (* _Ray Chandler_, Sep 15 2015 *)
%o A163804 (PARI) {a(n) = (n==0) + [0, -1, 1][n%3 + 1]};
%o A163804 (PARI) {a(n) = (n==0) - kronecker(-3, n)};
%Y A163804 A106510(n) = -a(n) unless n=0. Convolution inverse of A117659.
%Y A163804 Cf. A102283.
%K A163804 sign,easy,changed
%O A163804 0,1
%A A163804 _Michael Somos_, Aug 04 2009
```

## Candidate 146: A109017 vs A110161 (score 72.4, agree 105, variant abs, family size 6)
Terms: 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1

### A109017
```
%I A109017 #33 Dec 11 2025 12:36:57
%S A109017 0,1,0,0,0,1,0,1,0,0,0,1,0,-1,0,0,0,-1,0,-1,0,0,0,-1,0,1,0,0,0,1,0,1,
%T A109017 0,0,0,1,0,-1,0,0,0,-1,0,-1,0,0,0,-1,0,1,0,0,0,1,0,1,0,0,0,1,0,-1,0,0,
%U A109017 0,-1,0,-1,0,0,0,-1,0,1,0,0,0,1,0,1,0,0,0,1,0,-1,0,0,0,-1,0,-1,0,0,0,-1,0,1,0,0,0,1,0,1,0
%N A109017 a(n) = Kronecker symbol (-6/n).
%D A109017 L. B. W. Jolley, Summation of Series, Dover Publications, 1961.
%H A109017 G. C. Greubel, <a href="/A109017/b109017.txt">Table of n, a(n) for n = 0..10000</a>
%H A109017 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/KroneckerSymbol.html">Kronecker Symbol</a>
%H A109017 <a href="/index/Rec#order_08">Index entries for linear recurrences with constant coefficients</a>, signature (0,0,0,1,0,0,0,-1).
%F A109017 Euler transform of length-24 sequence [ 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1].
%F A109017 a(n) = -a(-n) = a(n+24) for all n in Z.
%F A109017 G.f.: x * (1 + x^6) / (1 - x^4 + x^8).
%F A109017 G.f.: x *(1 -x^8)*(1 -x^12)^2 /((1 -x^4)*(1 -x^6)*(1 -x^24)).
%F A109017 Sum_{n>=1} |a(n)|/n^2 = Pi^2/9 [Jolley equ. 338].
%e A109017 G.f. = x + x^5 + x^7 + x^11 - x^13 - x^17 - x^19 - x^23 + x^25 + x^29 + ...
%p A109017 A109017 := proc(n)
%p A109017         numtheory[jacobi](-6,n) ;
%p A109017 end proc: # _R. J. Mathar_, Nov 03 2011
%t A109017 Table[KroneckerSymbol[-6, n], {n, 0, 104}] (* _Jean-François Alcover_, Jan 10 2014 *)
%o A109017 (PARI) {a(n) = kronecker(-6, n)};
%o A109017 (PARI) {a(n) = (n%2) * (n%3!=0) * (-1)^(n\12)};
%o A109017 (Magma) [KroneckerSymbol(-6,n): n in [0..120]]; // _Vincenzo Librandi_, Aug 09 2015
%Y A109017 Moebius transform of A192013.
%Y A109017 Cf. A296924 (primes not inert in Q(sqrt(-6))), A157437 (primes decomposing), A191059 (prime remaining inert).
%Y A109017 Kronecker symbols {(D/n)} for negative fundamental discriminants D = -3..-47, -67, -163: A102283, A101455, A175629, A188510, A011582, A316569, A011585, A289741, A011586, this sequence, A011588, A390614, A388073, A388072, A011591, A011592, A011596, A011615.
%Y A109017 Kronecker symbols {(D/n)} for positive fundamental discriminants D = 5..41: A080891, A091337, A110161, A011583, A011584, A322829, A322796, A390615, A011587, A391502, A011589, A391503, A011590.
%K A109017 sign,mult,easy
%O A109017 0,1
%A A109017 _Michael Somos_, Jun 16 2005
```
### A110161
```
%I A110161 #46 Jul 27 2026 14:30:58
%S A110161 0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,
%T A110161 -1,0,0,0,1,0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,
%U A110161 0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,-1,0,0,0,1,0,1,0,0,0,-1,0,-1,0
%N A110161 Expansion of x*(1-x^2)/(1-x^2+x^4).
%C A110161 Transform of A002605 by the Riordan array A102587. Denominator is the 12th cyclotomic polynomial.
%C A110161 The Dirichlet character associated with the real quadratic field Q(sqrt(3)) (discriminant 12). - _Jianing Song_, Dec 13 2025
%H A110161 Antti Karttunen, <a href="/A110161/b110161.txt">Table of n, a(n) for n = 0..65537</a>
%H A110161 Tricia Brown, Alexander Stokolos, and Dmitry Dmitrishin, <a href="https://doi.org/10.13140/RG.2.2.14770.77760">Convolutions of linear recurrent sequences and Gegenbauer polynomials</a>, ResearchGate (2026). See p. 9.
%H A110161 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (0,1,0,-1).
%F A110161 Periodic of length 12: 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1. - _T. D. Noe_, Dec 12 2006
%F A110161 From _Michael Somos_, Jun 11 2007: (Start)
%F A110161 Euler transform of length 12 sequence [0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1].
%F A110161 a(n) is multiplicative with a(2^e) = a(3^e) = 0^e, a(p^e) = 1 if p == 1, 11 (mod 12), a(p^e) = (-1)^e if p == 5, 7 (mod 12).
%F A110161 a(n) = a(-n) = -a(n + 6) for all n in Z.
%F A110161 G.f.: x * (1 - x^4) * (1 - x^6) / (1 - x^12). (End)
%F A110161 a(2*n - 1) = A010892(n). - _Michael Somos_, Jan 29 2015
%F A110161 a(n) = A014021(n+1). - _R. J. Mathar_, Nov 13 2023
%F A110161 E.g.f.: 2*cos(x/2)*sinh(sqrt(3)*x/2)/sqrt(3). - _Amiram Eldar_, Nov 27 2025
%t A110161 a[ n_] := JacobiSymbol[ 12, n]; (* _Michael Somos_, Jan 29 2015 *)
%t A110161 (* Alternative: *)
%t A110161 LinearRecurrence[{0,1,0,-1},{0,1,0,0},110] (* _Harvey P. Dale_, Jul 11 2015 *)
%o A110161 (PARI) {a(n) = kronecker( 12, n)}; /* _Michael Somos_, Jun 11 2007 */
%o A110161 (Magma)
%o A110161 A110161:= func< n | KroneckerSymbol(12, n) >;
%o A110161 [A110161(n): n in [0..120]]; // _G. C. Greubel_, Oct 23 2024
%o A110161 (SageMath)
%o A110161 def A110161(n): return kronecker(12, n)
%o A110161 [A110161(n) for n in range(121)] # _G. C. Greubel_, Oct 23 2024
%Y A110161 Cf. A002605, A010892, A014021, A102587.
%Y A110161 Moebius transform of A035194.
%Y A110161 Cf. A038874 (primes not inert in Q(sqrt(3))), A097933 (primes decomposing), A003630 (primes remaining inert).
%Y A110161 Kronecker symbols {(D/n)} for negative fundamental discriminants D = -3..-47, -67, -163: A102283, A101455, A175629, A188510, A011582, A316569, A011585, A289741, A011586, A109017, A011588, A390614, A388073, A388072, A011591, A011592, A011596, A011615.
%Y A110161 Kronecker symbols {(D/n)} for positive fundamental discriminants D = 5..41: A080891, A091337, this sequence, A011583, A011584, A322829, A322796, A390615, A011587, A391502, A011589, A391503, A011590.
%K A110161 easy,sign,mult
%O A110161 0,1
%A A110161 _Paul Barry_, Jul 14 2005
%E A110161 Corrected by _T. D. Noe_, Dec 12 2006
```

## Candidate 147: A113446 vs A121450 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, 1, -1, 1, 2, -1, 0, 1, 1, 2, 0, -1, 2, 0, -2, 1, 2, 1, 0, 2, 0, 0, 0, -1, 3, 2, -1, 0, 2, -2

### A113446
```
%I A113446 #26 Feb 16 2025 08:32:59
%S A113446 1,1,-1,1,2,-1,0,1,1,2,0,-1,2,0,-2,1,2,1,0,2,0,0,0,-1,3,2,-1,0,2,-2,0,
%T A113446 1,0,2,0,1,2,0,-2,2,2,0,0,0,2,0,0,-1,1,3,-2,2,2,-1,0,0,0,2,0,-2,2,0,0,
%U A113446 1,4,0,0,2,0,0,0,1,2,2,-3,0,0,-2,0,2,1,2,0,0,4,0,-2,0,2,2,0,0,0,0,0,-1,2,1,0,3,2,-2,0,2,0
%N A113446 Expansion of (phi(q)^2 - phi(q^3)^2) / 4 in powers of q where phi() is a Ramanujan theta function.
%C A113446 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%H A113446 G. C. Greubel, <a href="/A113446/b113446.txt">Table of n, a(n) for n = 1..1000</a>
%H A113446 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>, 2019.
%H A113446 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>.
%F A113446 Expansion of (eta(q^2)^3 * eta(q^6) * eta(q^12)^2) / (eta(q) * eta(q^3) * eta(q^4)^2) in powers of q.
%F A113446 Euler transform of period 12 sequence [1, -2, 2, 0, 1, -2, 1, 0, 2, -2, 1, -2, ...].
%F A113446 Moebius transform is period 12 sequence [1, 0, -2, 0, 1, 0, -1, 0, 2, 0, -1, 0, ...].
%F A113446 a(n) is multiplicative and a(2^e) = 1, a(3^e) = (-1)^e, a(p^e) = e+1 if p == 1 (mod 4), a(p^e) = (1 + (-1)^e)/2 if p == 3 (mod 4).
%F A113446 G.f.: ((Sum_{k} x^(k^2))^2 - (Sum_{k} x^(3*k^2))^2) / 4.
%F A113446 G.f.: Sum_{k>0} x^(3*k-1) / (1 + x^(6*k-2)) + x^(3*k-2)/(1 + x^(6*k-4)).
%F A113446 G.f.: Sum_{k>0} x^k * (1 - x^(2*k))^2 / (1 + x^(6*k)).
%F A113446 G.f.: x * Product_{k>0} (1 - x^k)^2 * (1 + x^k)^3 * (1 + x^(3*k)) * (1 + x^(4*k) + x^(8*k))^2.
%F A113446 G.f. is a period 1 Fourier series which satisfies f(-1 / (12 t)) = (t/i) g(t) where q = exp(2 Pi i t) and g() is the g.f. for A138949.
%F A113446 a(n) = (-1)^e * A035154(n) where 3^e is the highest power of 3 dividing n.
%F A113446 a(4*n + 1) = A008441(n).
%F A113446 Expansion of q * f(-q, -q^5) * f(q, q^5)^2 / phi(-q^3) in powers of q where phi(), f(,) are Ramanujan theta functions. - _Michael Somos_, Jan 31 2015
%F A113446 Expansion of q * (psi(q^3)^3 / psi(q)) * (phi(q) / phi(q^3)) in powers of q where phi(), psi() are Ramanujan theta functions.
%F A113446 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi/6 (A019673). - _Amiram Eldar_, Nov 24 2023
%e A113446 G.f. = q + q^2 - q^3 + q^4 + 2*q^5 - q^6 + q^8 + q^9 + 2*q^10 - q^12 + ...
%t A113446 a[ n_] := If[ n < 1, 0, (-1)^IntegerExponent[ n, 3] Sum[ KroneckerSymbol[ -36, d], { d, Divisors[ n]}]]; (* _Michael Somos_, Jan 31 2015 *)
%t A113446 a[ n_] := SeriesCoefficient[ (1/4) EllipticTheta[ 2, 0, q^(3/2)]^3 / EllipticTheta[ 2, 0, q^(1/2)] (EllipticTheta[ 3, 0, q] / EllipticTheta[ 3, 0, q^3]), {q, 0, n}]; (* _Michael Somos_, Jan 31 2015 *)
%o A113446 (PARI) {a(n) = if( n<1, 0, (-1)^valuation(n, 3) * sumdiv(n, d, kronecker(-36, d)))};
%o A113446 (PARI) {a(n) = if( n<1, 0, direuler(p=2, n, if( p==3, 1 / (1 + X), 1 / (1 - X) / (1 - kronecker(-36, p) * X)))[n])};
%o A113446 (PARI) {a(n) = local(A); if( n<1, 0, n--; A = x * O(x^n); polcoeff( eta(x^2 + A)^3 * eta(x^6 + A) * eta(x^12 + A)^2 / (eta(x + A) * eta(x^3 + A) * eta(x^4 + A)^2), n))};
%o A113446 (Magma) A := Basis( ModularForms( Gamma1(12), 1), 106); A[2] + A[3] - A[4] + A[5]; /* _Michael Somos_, Jan 31 2015 */
%Y A113446 Cf. A008441, A019673, A035154, A138949.
%Y A113446 Cf. A000122, A000700, A010054, A121373.
%K A113446 sign,easy,mult
%O A113446 1,5
%A A113446 _Michael Somos_, Nov 02 2005
```
### A121450
```
%I A121450 #14 Sep 07 2018 01:25:25
%S A121450 1,-1,-1,-1,2,1,0,-1,1,-2,0,1,2,0,-2,-1,2,-1,0,-2,0,0,0,1,3,-2,-1,0,2,
%T A121450 2,0,-1,0,-2,0,-1,2,0,-2,-2,2,0,0,0,2,0,0,1,1,-3,-2,-2,2,1,0,0,0,-2,0,
%U A121450 2,2,0,0,-1,4,0,0,-2,0,0,0,-1,2,-2,-3,0,0,2,0,-2,1,-2,0,0,4,0,-2,0,2,-2,0,0,0,0,0,1,2,-1,0,-3,2,2,0,-2,0
%N A121450 Expansion of (theta_4(q^3)^2 - theta_4(q)^2)/4 in powers of q.
%H A121450 G. C. Greubel, <a href="/A121450/b121450.txt">Table of n, a(n) for n = 1..5000</a>
%F A121450 Expansion of eta(q) * eta(q^3) * eta(q^12)^3 /(eta(q^4) * eta(q^6)^2) in powers of q.
%F A121450 Euler transform of period 12 sequence [-1, -1, -2, 0, -1, 0, -1, 0, -2, -1, -1, -2, ...].
%F A121450 Moebius transform is period 24 sequence [1, -2, -2, 0, 1, 4, -1, 0, 2, -2, -1, 0, 1, 2, -2, 0, 1, -4, -1, 0, 2, 2, -1, 0, ...].
%F A121450 Multiplicative with a(2^e) = -1 if e > 0, a(3^e) = (-1)^e, a(p^e) = (1+(-1)^e)/2 if p == 3 (mod 4), a(p^e) = e+1 if p == 1 (mod 4).
%F A121450 G.f.: Sum_{k>0} Kronecker(-4, k) * x^k * (1 - x^k)/ (1 + x^(3*k)) = x * Product_{k>0} (1 - x^k)^2 * (1 - x^k + x^(2*k)) * (1 + x^(2*k))^2 *(1 + x^k + x^(2*k))^2 * (1 - x^(2*k) + x^(4*k))^3.
%e A121450 G.f. = x - x^2 - x^3 - x^4 + 2*x^5 + x^6 - x^8 + x^9 - 2*x^10 + x^12 + ... - _Michael Somos_, Sep 07 2018
%t A121450 eta[q_]:= q^(1/24)*QPochhammer[q]; Rest[CoefficientList[Series[eta[q]* eta[q^3]*eta[q^12]^3/(eta[q^4]*eta[q^6]^2), {q, 0, 100}], q]] (* _G. C. Greubel_, Apr 19 2018 *)
%o A121450 (PARI) {a(n) = my(A, p, e); if( n<1, 0, A = factor(n); prod(k=1, matsize(A)[1], [p, e] = A[k, ]; if( p==2, -1, p==3, (-1)^e, p%4==1, (e+1), (1+(-1)^e)/2)))};
%o A121450 (PARI) {a(n) = my(A); if( n<1, 0, n--; A = x * O(x^n); polcoeff( eta(x + A) * eta(x^3 + A) * eta(x^12 + A)^3 / (eta(x^4 + A) * eta(x^6 + A)^2), n))};
%Y A121450 A035154(n) = |a(n)|.
%Y A121450 Apart from signs, same as A035154 and A113446.
%K A121450 sign,mult
%O A121450 1,5
%A A121450 _Michael Somos_, Jul 30 2006
```

## Candidate 148: A113661 vs A113974 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, 2, 1, -1, 0, 2, 2, 2, 1, 0, 0, -1, 2, 4, 0, -1, 0, 2, 2, 0, 2, 0, 0, 2, 1, 4, 1, -2, 0, 0

### A113661
```
%I A113661 #34 Feb 16 2025 08:32:59
%S A113661 1,2,1,-1,0,2,2,2,1,0,0,-1,2,4,0,-1,0,2,2,0,2,0,0,2,1,4,1,-2,0,0,2,2,
%T A113661 0,0,0,-1,2,4,2,0,0,4,2,0,0,0,0,-1,3,2,0,-2,0,2,0,4,2,0,0,0,2,4,2,-1,
%U A113661 0,0,2,0,0,0,0,2,2,4,1,-2,0,4,2,0,1,0,0,-2,0,4,0,0,0,0,4,0,2,0,0,2,2,6,0,-1,0,0,2,4,0
%N A113661 Expansion of (phi(x)^3/phi(x^3) - 1)/6 where phi() is a Ramanujan theta function.
%C A113661 Ramanujan theta functions: f(q) := Product_{k>=1} (1-(-q)^k) (see A121373), phi(q) := theta_3(q) := Sum_{k=-oo..oo} q^(k^2) (A000122), psi(q) := Sum_{k=0..oo} q^(k*(k+1)/2) (A010054), chi(q) := Product_{k>=0} (1+q^(2k+1)) (A000700).
%D A113661 Bruce C. Berndt, Ramanujan's Notebooks Part III, Springer-Verlag, 1991, see p. 227, Entry 4(iv).
%H A113661 G. C. Greubel, <a href="/A113661/b113661.txt">Table of n, a(n) for n = 1..1000</a>
%H A113661 Tewodros Amdeberhan, George E. Andrews, and Roberto Tauraso, <a href="https://arxiv.org/abs/2409.20400">Further study on MacMahon-type sums of divisors</a>, arXiv:2409.20400 [math.NT], 2024. See pp. 12, 18.
%H A113661 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>, 2019.
%H A113661 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>.
%F A113661 a(n) is multiplicative and a(2^e) = (1-3(-1)^e)/2 if e>0, a(3^e) = 1, a(p^e) = e+1 if p == 1 (mod 6), a(p^e) = (1+(-1)^e)/2 if p == 5 (mod 6).
%F A113661 Moebius transform is period 12 sequence [1, 1, 0, -3, -1, 0, 1, 3, 0, -1, -1, 0, ...].
%F A113661 Expansion of ((eta(q^2)^15*eta(q^3)^2*eta(q^12)^2)/(eta(q)^6*eta(q^4)^6*eta(q^6)^5)-1)/6 in powers of q.
%F A113661 G.f.: Sum_{k>0} x^k/(1+x^k+x^(2k)) +2*x^(4k-2)/(1+x^(4k-2)+x^(8k-4)).
%F A113661 6*a(n) = A113660(n), if n>0.
%F A113661 G.f.: Sum_{k >= 1} x^k/(1 + (-x)^k + x^(2*k)). - _Peter Bala_, Jan 12 2021
%F A113661 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = Pi/(2*sqrt(3)) = 0.906899... (A093766). - _Amiram Eldar_, Nov 21 2023
%e A113661 G.f. = x + 2*x^2 + x^3 - x^4 + 2*x^6 + 2*x^7 + 2*x^8 + x^9 - x^12 + ...
%p A113661 p := x -> convert(series(add(x^n/(1+(-x)^n+x^(2*n)), n = 1..100), x, 101), polynom):
%p A113661 seq(coeff(p(x), x, n), n = 1..100); # _Peter Bala_, Jan 12 2021
%t A113661 a[n_] := SeriesCoefficient[(EllipticTheta[3, 0, q]^3/EllipticTheta[3, 0, q^3] - 1)/6, {q, 0, n}]; Table[a[n], {n, 0, 50}] (* _G. C. Greubel_, Dec 16 2017 *)
%o A113661 (PARI) {a(n)=local(x); if(n<1, 0, x=valuation(n,2); if(n%2,1,(1-3*(-1)^x)/2)*sumdiv(n/2^x,d, kronecker(-3,d)))}
%o A113661 (PARI) {a(n)=local(A,p,e); if(n<1, 0, A=factor(n); prod(k=1,matsize(A)[1], if(p=A[k,1], e=A[k,2]; if(p==2, (1-3*(-1)^e)/2, if(p==3, 1, if(p%6==1, e+1, !(e%2)))))))}
%o A113661 (PARI) {a(n)=if(n<1, 0, direuler(p=2,n, if(p==2, 2-(1-2*X)/(1-X^2), 1/(1-X)/(1-kronecker(-3,p)*X)))[n])}
%o A113661 (PARI) {a(n)=local(A); if(n<1, 0, A=x*O(x^n); polcoeff( (eta(x^2+A)^15*eta(x^3+A)^2*eta(x^12+A)^2/ eta(x+A)^6/eta(x^4+A)^6/eta(x^6+A)^5-1)/6, n))}
%Y A113661 Cf. A093766, A113660.
%Y A113661 Cf. A000700, A000122, A010054, A121373.
%K A113661 sign,mult
%O A113661 1,2
%A A113661 _Michael Somos_, Nov 03 2005
```
### A113974
```
%I A113974 #23 Feb 16 2025 08:32:59
%S A113974 1,-2,1,-1,0,-2,2,-2,1,0,0,-1,2,-4,0,-1,0,-2,2,0,2,0,0,-2,1,-4,1,-2,0,
%T A113974 0,2,-2,0,0,0,-1,2,-4,2,0,0,-4,2,0,0,0,0,-1,3,-2,0,-2,0,-2,0,-4,2,0,0,
%U A113974 0,2,-4,2,-1,0,0,2,0,0,0,0,-2,2,-4,1,-2,0,-4,2,0,1,0,0,-2,0,-4,0,0,0,0,4,0,2,0,0,-2,2,-6,0,-1,0,0,2,-4,0
%N A113974 Expansion of (1-phi(x^3)^3/phi(x))/2 where phi() is a Ramanujan theta function.
%C A113974 Ramanujan theta functions: f(q) := Prod_{k>=1} (1-(-q)^k) (see A121373), phi(q) := theta_3(q) := Sum_{k=-oo..oo} q^(k^2) (A000122), psi(q) := Sum_{k=0..oo} q^(k*(k+1)/2) (A010054), chi(q) := Prod_{k>=0} (1+q^(2k+1)) (A000700).
%D A113974 Bruce C. Berndt, Ramanujan's Notebooks Part V, Springer-Verlag, 1985, see p. 375, Entry 35.
%H A113974 G. C. Greubel, <a href="/A113974/b113974.txt">Table of n, a(n) for n = 1..1000</a>
%H A113974 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>, 2019.
%H A113974 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>.
%F A113974 a(n) is multiplicative and a(2^e) = ((-1)^e-3)/2, a(3^e) = 1, a(p^e) = e+1 if p == 1 (mod 6), a(p^e) = (1+(-1)^e)/2 if p == 5 (mod 6). [corrected by _Amiram Eldar_, Nov 14 2023]
%F A113974 Moebius transform is period 12 sequence [1, -3, 0, 1, -1, 0, 1, -1, 0, 3, -1, 0, ...].
%F A113974 G.f.: (1-theta_3(q^3)^3/theta_3(q))/2.
%F A113974 G.f.: Sum_{k>0} x^(3k-2)/(1-(-x)^(3k-2)) - x^(3k-1)/(1-(-x)^(3k-1)) = Sum_{k>0} -(-1)^k x^k/(1+x^k+x^(2k)) -2 x^(4k)/(1+x^(4k)+x^(8k)).
%F A113974 -2*a(n) = A113973(n), if n>0.
%F A113974 Asymptotic mean: Limit_{m->oo} (1/m) * Sum_{k=1..m} a(k) = -Pi/(6*sqrt(3)) = -0.302299... . - _Amiram Eldar_, Nov 14 2023
%t A113974 a[n_]:= SeriesCoefficient[(1 - EllipticTheta[3, 0, q^3]^3/EllipticTheta[ 3, 0, q])/2, {q, 0, n}]; Table[a[n], {n, 1, 50}] (* _G. C. Greubel_, Dec 16 2017 *)
%t A113974 f[p_, e_] := If[Mod[p, 6] == 1, e + 1, (1 + (-1)^e)/2]; f[2, e_] := ((-1)^e - 3)/2; f[3, e_] := 1; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Nov 14 2023 *)
%o A113974 (PARI) {a(n)=local(x); if(n<1, 0, x=valuation(n,2); if(n%2,1,(-3+(-1)^x)/2)*sumdiv(n/2^x,d, kronecker(-3,d)))}
%o A113974 (PARI) {a(n)=local(A,p,e); if(n<1, 0, A=factor(n); prod(k=1,matsize(A)[1], if(p=A[k,1], e=A[k,2]; if(p==2, (-3+(-1)^e)/2, if(p==3, 1, if(p%6==1, e+1, !(e%2)))))))}
%o A113974 (PARI) {a(n)=if(n<1, 0, direuler(p=2,n, if(p==2, 2-(1+2*X)/(1-X^2), 1/(1-X)/(1-kronecker(-3,p)*X)))[n])}
%o A113974 (PARI) {a(n)=local(A); if(n<0, 0, A=sum(k=1,sqrtint(n), 2*x^k^2, 1+x*O(x^n)); polcoeff( (1-subst(A+x*O(x^(n\3)),x,x^3)^3/A)/2, n))}
%Y A113974 Cf. A000700, A000122, A010054, A113973, A121373.
%K A113974 sign,easy,mult
%O A113974 1,2
%A A113974 _Michael Somos_, Nov 10 2005
```

## Candidate 149: A121373 vs A199918 (score 72.4, agree 105, variant abs, family size 9)
Terms: 1, 1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0

### A121373
```
%I A121373 #47 Sep 18 2025 16:46:21
%S A121373 1,1,-1,0,0,-1,0,-1,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,
%T A121373 0,0,0,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,-1,0,0,0,0,0,0,0,
%U A121373 0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0
%N A121373 Expansion of f(x) = f(x, -x^2) in powers of x where f(, ) is Ramanujan's general theta function.
%C A121373 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A121373 This is an example of the quintuple product identity in the form f(a*b^4, a^2/b) - (a/b) * f(a^4*b, b^2/a) = f(-a*b, -a^2*b^2) * f(-a/b, -b^2) / f(a, b) where a = -x^3, b = -x. - _Michael Somos_, Jul 11 2012
%C A121373 Number 5 of the 14 primitive eta-products which are holomorphic modular forms of weight 1/2 listed by D. Zagier on page 30 of "The 1-2-3 of Modular Forms". - _Michael Somos_, May 04 2016
%H A121373 Seiichi Manyama, <a href="/A121373/b121373.txt">Table of n, a(n) for n = 0..10000</a>
%H A121373 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A121373 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%H A121373 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/QuintupleProductIdentity.html">Quintuple Product Identity</a>
%F A121373 Expansion of q^(-1/4) * (theta_1( Pi/12, q) + theta_2( Pi/12, q)) / sqrt(6) in powers of q^6. - _Michael Somos_, Jul 06 2013
%F A121373 Expansion of q^(-1/24) * eta(q^2)^3 / (eta(q) * eta(q^4)) in powers of q.
%F A121373 Euler transform of period 4 sequence [1, -2, 1, -1, ...].
%F A121373 a(n) = b(24*n + 1) where b() is multiplicative with b(p^2e) = (-1)^e if p == 7, 11, 13, 17 (mod 24), b(p^2e) = +1 if p == 1, 5, 19, 23 (mod 24) and b(p^(2e-1)) = b(2^e) = b(3^e) = 0 if e>0.
%F A121373 G.f.: (1 + x) * (1 - x^2) * (1 + x^3) * (1 - x^4) * ...
%F A121373 G.f.: 1 + x - x^2*(1 + x) + x^3*(1 + x)*(1 - x^2) - x^4*(1 + x)*(1 - x^2)*(1 + x^3) + ...
%F A121373 a(5*n + 3) = a(5*n + 4) = 0. a(25*n + 1) = a(n).
%F A121373 G.f.: Sum_{k>=0} a(k) * x^(24*k + 1) = Sum_{k in Z} (-1)^floor((k+1)/2) * x^(6*k + 1)^2.
%F A121373 a(n) = (-1)^n * A010815(n). |a(n)| = A080995(n).
%F A121373 Expansion of f(-x^5, -x^7) + x * f(-x, -x^11) in powers of x. - _Michael Somos_, Jan 10 2015
%F A121373 G.f. is a period 1 Fourier series which satisfies f(-1 / (2304 t)) = 48^(1/2) (t/i)^(1/2) f(t) where q = exp(2 Pi i t). - _Michael Somos_, May 05 2016
%F A121373 G.f.: exp(Sum_{k>=1} (-1)^(k+1)*x^k/(k*(1 - (-x)^k))). - _Ilya Gutkovskiy_, Jun 08 2018
%F A121373 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = (1/2) * exp(Pi / 24) * Pi^(1/4) * 2^(3/4) / Gamma(3/4) = A388569. - _Simon Plouffe_, Sep 18 2025
%e A121373 G.f. = 1 + x - x^2 - x^5 - x^7 - x^12 + x^15 + x^22 + x^26 + x^35 + ...
%e A121373 G.f. = q + q^25 - q^49 - q^121 - q^169 - q^289 + q^361 + q^529 + ...
%t A121373 a[ n_] := SeriesCoefficient[ Product[ 1 - (-x)^k, {k, n}], {x, 0, n}]; (* _Michael Somos_, Nov 14 2011 *)
%t A121373 a[ n_] := SeriesCoefficient[ QPochhammer[ -x], {x, 0, n}]; (* _Michael Somos_, Jul 06 2013 *)
%t A121373 a[ n_] := SeriesCoefficient[ (EllipticTheta[ 1, Pi/12, x^4] + EllipticTheta[ 2, Pi/12, x^4]) / Sqrt[6], {x, 0, 24 n + 1}] // Simplify; (* _Michael Somos_, Mar 20 2015 *)
%o A121373 (PARI) {a(n) = if( issquare( 24*n + 1, &n), kronecker( 6, n))};
%o A121373 (PARI) {a(n) = if( n<0, 0, polcoeff( eta( -x + x * O(x^n)), n))};
%Y A121373 Cf. A010815, A080995, A247133, A247223.
%K A121373 sign
%O A121373 0,1
%A A121373 _Michael Somos_, Jul 24 2006
```
### A199918
```
%I A199918 #35 May 30 2026 16:40:35
%S A199918 1,1,1,0,0,1,0,-1,0,0,0,0,-1,0,0,-1,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,
%T A199918 0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,
%U A199918 0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,0,0,0,0
%N A199918 Expansion of false theta series variation of Euler's pentagonal number series in powers of x.
%H A199918 G. C. Greubel, <a href="/A199918/b199918.txt">Table of n, a(n) for n = 0..10000</a>
%H A199918 Peter Bala, <a href="/A199918/a199918.jpg">A continuous interpolation function for A199918</a>.
%H A199918 B. C. Berndt, B. Kim, and A. J. Yee, <a href="https://doi.org/10.1016/j.jcta.2009.07.005">Ramanujan's lost notebook: Combinatorial proofs of identities associated with Heine's transformation or partial theta functions</a>, J. Comb. Thy. Ser. A, 117 (2010), 957-973.
%F A199918 a(n) = b(24*n + 1) where b(n) is multiplicative with b(p^(2*e)) = (-1)^e if p == 13, 17, 29, 23 (mod 24), b(p^(2*e)) = +1 if p = 1, 5, 7, 11 (mod 24) and b(p^(2*e - 1)) = b(2^e) = b(3^e) = 0 if e > 0.
%F A199918 G.f.: 1 + Sum_{k>0} x^k / Product_{i=1..k} (1 + x^(2*i)) = 1 + Sum_{k>0} x^k * Product_{i=1..k-1} (1 + (-x)^i) = Sum_{k in Z} x^((k^2 - 1) / 24) * Kronecker(-24, k).
%F A199918 |a(n)| = |A010815(n)| = |A143062(n)|.
%F A199918 G.f.: A(x) = 1/(1 - x) * (2 - Sum_{k >= 0} x^(3*k)/Product_{i = 1..k} 1 + x^(2*i)) = 1/((1 - x)*(1 - x^3)) * (-2*x^3 + Sum_{k >= 0} x^(5*k)/Product_{i = 1..k} 1 + x^(2*i)). - _Peter Bala_, Jan 24 2025
%F A199918 a(n) = lim_{x -> n} sqrt(3) * sin(Pi*x)/( u*sin(Pi*(u + 1)/6)*sin(Pi*(u - 1)/6) ), where u = sqrt(1 + 24*x). - _Peter Bala_, Sep 13 2025
%e A199918 G.f. = 1 + x + x^2 + x^5 - x^7 - x^12 - x^15 - x^22 + x^26 + x^35 + x^40 + ...
%e A199918 G.f. = q + q^25 + q^49 + q^121 - q^169 - q^289 - q^361 - q^529 + q^625 + q^841 + ...
%t A199918 a[ n_] := If[ SquaresR[ 1, 24 n + 1] == 2, KroneckerSymbol[ -6, Sqrt[ 24 n + 1]], 0];
%o A199918 (PARI) {a(n) = my(m); if( issquare( 24*n + 1, &m), kronecker( -6, m), 0)};
%Y A199918 Cf. A010815, A143062.
%K A199918 sign,easy
%O A199918 0,1
%A A199918 _Michael Somos_, Nov 12 2011
```

## Candidate 150: A143064 vs A185124 (score 72.4, agree 105, variant abs, family size 6)
Terms: 1, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0

### A143064
```
%I A143064 #35 Nov 05 2025 15:35:33
%S A143064 1,1,0,0,0,-1,0,0,-1,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
%T A143064 -1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,
%U A143064 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0
%N A143064 Expansion of a Ramanujan false theta series variation of A089801 in powers of x.
%D A143064 Srinivasa Ramanujan, The Lost Notebook and Other Unpublished Papers, Narosa Publishing House, New Delhi, 1988, p. 41, 13th equation.
%H A143064 Alois P. Heinz, <a href="/A143064/b143064.txt">Table of n, a(n) for n = 0..1000</a>
%H A143064 G. E. Andrews, <a href="https://www.jstor.org/stable/2331943">An introduction to Ramanujan's "lost" notebook</a>, Amer. Math. Monthly 86 (1979), no. 2, 89-108.  See page 89, Equation (1.2), page 100, Equation (5.3)
%H A143064 G. E. Andrews, <a href="https://georgeandrews1.github.io/pdf/320.pdf">The Bhargava-Adiga Summation and Partitions</a>, 2016. See page 3, Equation (1.5)
%F A143064 Expansion of Sum_{k>=0} x^k / (Product_{j=0..k} ( 1 + x^(2*k + 1) ) ) in powers of x^2. - _Michael Somos_, Nov 04 2013
%F A143064 a(n) = b(3*n + 1) where b() is multiplicative with b(p^(2*e)) = -(-1)^e if p = 2, b(p^(2*e)) = (-1)^e if p = 5 (mod 6), b(p^(2*e)) = 1 if p = 1 (mod 6), and b(p^(2*e-1)) = b(3^e) = 0 if e>0. - _Michael Somos_, Jul 19 2013
%F A143064 a(4*n + 2) = a(4*n + 3) = a(8*n + 4) = 0.
%F A143064 a(8*n) = A143062(n). Convolution of A010054 with A143065. - _Michael Somos_, Jul 19 2013
%F A143064 G.f.: Sum_{k>=0} (-1)^k * x^(3*k^2 + 2*k) * ( 1 + x^(2*k + 1) ).
%F A143064 G.f.: 1/(1 - x*(1-x)/(1 - x^2*(1-x^2)/(1 - x^3*(1-x^3)/(1 - x^4*(1-x^4)/(1 - ...))))), a continued fraction. - _Paul D. Hanna_, Jul 18 2013
%F A143064 abs(a(n)) = A089801(n). - _Michael Somos_, Jun 30 2015
%F A143064 G.f.: 1 + x*(1-x) + x^2*(1-x)*(1-x^3) + x^3*(1-x)*(1-x^3)*(1-x^5) + ... . - _Michael Somos_, Aug 03 2017
%e A143064 G.f. = 1 + x - x^5 - x^8 + x^16 + x^21 - x^33 - x^40 + x^56 + x^65 - x^85 - x^96 + ...
%e A143064 G.f. = q + q^4 - q^16 - q^25 + q^49 + q^64 - q^100 - q^121 + q^169 + q^196 + ...
%t A143064 a[ n_] := With[ {m = Sqrt[3 n + 1]}, If[ IntegerQ @ m, (-1)^Quotient[ m, 3], 0]]; (* _Michael Somos_, Jun 30 2015 *)
%t A143064 a[ n_] := SeriesCoefficient[ Sum[ (-1)^k x^(3 k^2 + 2 k) (1 + x^(2 k + 1)), {k, 0, n}], {x, 0, n}]; (* _Michael Somos_, Nov 04 2013 *)
%t A143064 a[ n_] := SeriesCoefficient[ Sum[ x^k QPochhammer[ x, x^2, k], {k, 0, n}], {x, 0, n}]; (* _Michael Somos_, Jun 30 2015 *)
%t A143064 a[ n_] := SeriesCoefficient[ Sum[ x^k / QPochhammer[ -x, x^2, k + 1], {k, 0, 2 n}], {x, 0, 2 n}]; (* _Michael Somos_, Jun 30 2015 *)
%o A143064 (PARI) {a(n) = my(m); if( issquare( 3*n + 1, &m), (-1)^(m \ 3) )};
%o A143064 (PARI) {a(n) = my(A, p, e); if( n<0, 0, n = 3*n + 1; A = factor(n); prod(k=1, matsize(A)[1], [p, e] = A[k, ]; if( e%2, 0, p==2, -(-1)^(e/2), p == 3, 0, p%6 == 1, 1, (-1)^(e/2))))}; /* _Michael Somos_, Jul 19 2013 */
%o A143064 (PARI) /* Continued Fraction: */
%o A143064 {a(n)=local(CF); CF=1+x; for(k=0, n, CF=1/(1 - x^(n-k+1)*(1 - x^(n-k+1))*CF+x*O(x^n))); polcoeff(CF, n)} \\ _Paul D. Hanna_, Jul 18 2013
%Y A143064 Cf. A089801, A010054, A143062, A143065.
%Y A143064 Column m=0 of A185646.
%K A143064 sign
%O A143064 0,1
%A A143064 _Michael Somos_, Jul 21 2008
```
### A185124
```
%I A185124 #22 Feb 16 2025 08:33:13
%S A185124 1,1,0,0,0,-1,0,0,-1,0,0,0,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,
%T A185124 0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,
%U A185124 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0
%N A185124 Expansion of f(x, -x^5) in powers of x where f(,) is the Ramanujan general theta function.
%C A185124 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A185124 a(n) is nonzero if and only if n is a number of A001082.
%C A185124 The exponents in the q-series for this sequence are the squares of the numbers of A001651.
%H A185124 G. C. Greubel, <a href="/A185124/b185124.txt">Table of n, a(n) for n = 0..1000</a>
%H A185124 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A185124 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A185124 Euler transform of period 24 sequence [ 1, -1, 0, 0, -1, 1, -1, 0, 0, 0, 1, -2, 1, 0, 0, 0, -1, 1, -1, 0, 0, -1, 1, -1, ...].
%F A185124 G.f.: Sum_{k in Z} (-1)^floor((k + 1)/2) * x^(k * (3*k + 2)).
%F A185124 a(4*n + 2) = a(4*n + 3) = a(5*n + 2) = a(5*n + 4) = a(8*n + 4) = 0. a(4*n + 1) = A080902(n). a(8*n) = A010815(n).
%F A185124 a(n) = (-1)^n * A185125(n). - _Michael Somos_, Jun 30 2015
%e A185124 G.f. = 1 + x - x^5 - x^8 - x^16 - x^21 + x^33 + x^40 + x^56 + x^65 - x^85 + ...
%e A185124 G.f. = q + q^4 - q^16 - q^25 - q^49 - q^64 + q^100 + q^121 + q^169 + q^196 + ...
%t A185124 a[ n_] := SeriesCoefficient[ QPochhammer[ -x, -x^6] QPochhammer[ x^5, -x^6] QPochhammer[ -x^6], {x, 0, n}]; (* _Michael Somos_, Jun 30 2015 *)
%o A185124 (PARI) {a(n) = my(m); if( issquare( 3*n + 1, &m), (m%3!=0) * (-1)^((m+3) \ 6), 0)};
%Y A185124 Cf. A010815, A080902, A185125.
%K A185124 sign,easy
%O A185124 0,1
%A A185124 _Michael Somos_, Jan 20 2012
```

## Candidate 151: A143259 vs A359818 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, -1, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0

### A143259
```
%I A143259 #45 May 30 2026 16:40:32
%S A143259 1,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,-1,
%T A143259 0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,
%U A143259 0,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,0,0
%N A143259 a(n) = 1 if n is a nonzero square, -1 if n is twice a nonzero square, 0 otherwise.
%C A143259 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%H A143259 Antti Karttunen, <a href="/A143259/b143259.txt">Table of n, a(n) for n = 1..65537</a>
%H A143259 S. Cooper and M. Hirschhorn, <a href="https://doi.org/10.1216/rmjm/1008959672">On some infinite product identities</a>, Rocky Mountain J. Math., 31 (2001) 131-139. see p. 133 Theorem 1.
%H A143259 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A143259 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A143259 Expansion of (phi(q) - phi(q^2)) / 2 = q * psi(q^4) * f(-q, -q^7) / f(-q^3, -q^5) in powers of q where phi(), psi() and f() are Ramanujan theta functions.
%F A143259 Expansion of q * f(-q, -q^7)^2 / psi(-q) in powers of q where psi(), f() are Ramanujan theta functions. - _Michael Somos_, Jan 01 2015
%F A143259 Euler transform of period 8 sequence [ -1, 0, 1, 1, 1, 0, -1, -1, ...].
%F A143259 a(2*n) = -a(n) for all n in Z.
%F A143259 a(n) is multiplicative with a(2^e) = (-1)^e, a(p^e) = (1 + (-1)^e) / 2 if p == 1 (mod 2).
%F A143259 Dirichlet g.f.: zeta(2*s) * (1 - 2^-s); Dirichlet convolution of A010052 and A154955.
%F A143259 G.f. A(x) satisfies: A(x) / A(x^2) = -1 + A111374(x).
%F A143259 G.f. A(x) satisfies: A(x^2) = - (A(x) + A(-x)) / 2.
%F A143259 G.f. A(x) satisfies: 0 = f(A(x), A(x^2), A(x^4)) where f(u, v, w) = w * (u + v)^2 - v * (v + w) * (v + 2*w).
%F A143259 G.f.: (theta_3(q) - theta_3(q^2)) / 2 = Sum_{k>0} x^(k^2) - x^(2k^2).
%F A143259 |a(n)| = A053866(n).
%F A143259 a(n) = A008836(n)*A053866(n). - _Jon Maiga_, Jan 11 2019
%F A143259 Sum_{k=1..n} a(k) ~ (1 - 1/sqrt(2)) * sqrt(n). - _Vaclav Kotesovec_, Oct 16 2020
%e A143259 G.f. = q - q^2 + q^4 - q^8 + q^9 + q^16 - q^18 + q^25 - q^32 + q^36 + q^49 - q^50 + ...
%t A143259 f[n_]:=Which[IntegerQ[Sqrt[n/2]],-1,IntegerQ[Sqrt[n]],1,True,0]; Array[f,110] (* _Harvey P. Dale_, Jul 07 2011 *)
%t A143259 a[ n_] := Boole[ IntegerQ[ Sqrt[n]]] - Boole[ IntegerQ[ Sqrt[2 n]]]; (* _Michael Somos_, Jun 10 2014 *)
%t A143259 a[ n_] := SeriesCoefficient[ (EllipticTheta[ 3, 0, q] - EllipticTheta[ 3, 0, q^2])/2, {q, 0, n}]; (* _Michael Somos_, Jun 10 2014 *)
%t A143259 Table[LiouvilleLambda[n]*Mod[DivisorSigma[1, n], 2], {n, 100}] (* _Jon Maiga_, Jan 11 2019 *)
%o A143259 (PARI) {a(n) = issquare(n) - issquare(2*n)};
%o A143259 (PARI) {a(n) = if( n<1, 0, n--; polcoeff( prod(k=1, n, (1 - x^k)^([1, 1, 0, -1, -1, -1, 0, 1][k%8 + 1]), 1 + x * O(x^n)), n))};
%o A143259 (Magma) Basis( ModularForms( Gamma1(8), 1/2), 100) [2] ; /* _Michael Somos_, Jun 10 2014 */
%Y A143259 Cf. A008836, A010052, A053866, A111374, A154955.
%K A143259 sign,mult
%O A143259 1,1
%A A143259 _Michael Somos_, Aug 02 2008
```
### A359818
```
%I A359818 #10 Jan 26 2023 16:13:25
%S A359818 1,-1,0,1,0,0,0,-1,-1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,
%T A359818 0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,
%U A359818 0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1
%N A359818 Dirichlet inverse of A359549, where A359549 is the characteristic function for numbers that are either an odd squarefree number squared or twice such a number.
%C A359818 Multiplicative because A359549 is.
%H A359818 Antti Karttunen, <a href="/A359818/b359818.txt">Table of n, a(n) for n = 1..100000</a>
%F A359818 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A359549(n/d) * a(d).
%F A359818 Multiplicative with a(2^e) = (-1)^e, and for p > 2, a(p^e) = 0 if e is odd, and (-1)^(e/2) if e is even. - _Amiram Eldar_, Jan 26 2023
%t A359818 f[p_, e_] := If[OddQ[e], 0, (-1)^(e/2)]; f[2, e_] := (-1)^e; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Jan 26 2023 *)
%o A359818 (PARI) A359818(n) = { my(f=factor(n)); prod(k=1, #f~, if(2==f[k, 1], (-1)^f[k, 2], if(f[k, 2]%2, 0, (-1)^(f[k, 2]/2)))); }; \\ (After Mathematica program) - _Antti Karttunen_, Jan 26 2023
%Y A359818 Cf. A053866 (parity and the absolute values).
%Y A359818 Cf. A359549 (Dirichlet inverse).
%Y A359818 Cf. also A143259.
%K A359818 sign,mult
%O A359818 1
%A A359818 _Antti Karttunen_, Jan 17 2023
```

## Candidate 152: A156277 vs A365428 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, -1, 0, 0, -1, 0, -1, 0, 0, 1, -1, 0, -1, 1, 0, 0, -1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, -1, 0

### A156277
```
%I A156277 #27 Jan 07 2023 04:02:29
%S A156277 1,-1,0,0,-1,0,-1,0,0,1,-1,0,-1,1,0,0,-1,0,-1,0,0,1,-1,0,0,1,0,0,-1,0,
%T A156277 -1,0,0,1,1,0,-1,1,0,0,-1,0,-1,0,0,1,-1,0,0,0,0,0,-1,0,1,0,0,1,-1,0,
%U A156277 -1,1,0,0,1,0,-1,0,0,-1,-1,0,-1,1,0,0,1,0,-1,0,0,1,-1,0,1,1,0,0,-1,0,1,0,0,1,1,0,-1,0,0,0,-1,0,-1,0,0,1
%N A156277 Dirichlet inverse of A011655, characteristic function of numbers that are not multiples of 3; Numbers appearing at every third row in the third column of A156241.
%C A156277 The Dirichlet inverse is A011655, and the Mobius inverse is represented by the absolute values of A154271. - _R. J. Mathar_, Jul 02 2013
%C A156277 From _Antti Karttunen_, Dec 31 2022: (Start)
%C A156277 Note the correspondences between four sequences:
%C A156277   A156277 --- abs ---> A359377
%C A156277      ^                    ^
%C A156277      |                    |
%C A156277     inv                  inv
%C A156277      |                    |
%C A156277      v                    v
%C A156277   A011655 <--- abs --- A359378
%C A156277 Here inv means that the sequences are Dirichlet Inverses of each other, and abs means taking absolute values.
%C A156277 (End)
%H A156277 Antti Karttunen, <a href="/A156277/b156277.txt">Table of n, a(n) for n = 1..100000</a>
%F A156277 a(n) = -A008683(3n). - _R. J. Mathar_, Mar 31 2011
%F A156277 Dirichlet g.f.: 3^s/((3^s-1)*zeta(s)). - _Amiram Eldar_, Jan 07 2023
%p A156277 seq( -numtheory[mobius](3*n),n=1..80) ; # _R. J. Mathar_, Mar 31 2011
%o A156277 (PARI) A156277(n) = -moebius(3*n); \\ _Antti Karttunen_, Dec 29 2022
%Y A156277 Cf. A008683, A011655 (Dirichlet inverse), A154271, A156277, A359377 (absolute values), A359378 (Dirichlet inverse of the absolute values).
%Y A156277 Cf. also A355689.
%K A156277 easy,sign,mult
%O A156277 1
%A A156277 _Mats Granvik_, Feb 07 2009
%E A156277 Data section extended up to a(106) and a new primary definition (from _R. J. Mathar_'s Jul 02 2013 comment) added to the name field by _Antti Karttunen_, Dec 29 2022
```
### A365428
```
%I A365428 #11 Sep 16 2023 21:03:13
%S A365428 1,1,0,0,1,0,-1,0,0,1,1,0,-1,-1,0,0,1,0,-1,0,0,1,1,0,0,-1,0,0,1,0,-1,
%T A365428 0,0,1,-1,0,-1,-1,0,0,1,0,-1,0,0,1,1,0,0,0,0,0,1,0,1,0,0,1,1,0,-1,-1,
%U A365428 0,0,-1,0,-1,0,0,-1,1,0,-1,-1,0,0,-1,0,-1,0,0,1,1,0,1,-1,0,0,1,0,1,0,0,1,-1,0,-1,0,0,0,1,0,-1,0,0
%N A365428 Dirichlet inverse of A102283.
%C A365428 Multiplicative because A102283 is.
%H A365428 Antti Karttunen, <a href="/A365428/b365428.txt">Table of n, a(n) for n = 1..100000</a>
%F A365428 a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A102283(n/d) * a(d).
%F A365428 Multiplicative with a(p) = -Legendre(-3, p), and a(p^e) = 0 for e >= 2. - _Amiram Eldar_, Sep 16 2023
%t A365428 f[p_, e_] := If[e == 1, -JacobiSymbol[-3, p], 0]; a[1] = 1; a[n_] := Times @@ f @@@ FactorInteger[n]; Array[a, 100] (* _Amiram Eldar_, Sep 16 2023 *)
%o A365428 (PARI) A365428(n) = { my(f=factor(n)); prod(k=1,#f~,if(1<f[k,2],0,-kronecker(-3,f[k,1]))); }; \\ (After _Amiram Eldar_'s multiplicative formula).
%o A365428 (PARI)
%o A365428 A102283(n) = ([0, 1, -1][n%3 + 1]);
%o A365428 memoA365428 = Map();
%o A365428 A365428(n) = if(1==n,1,my(v); if(mapisdefined(memoA365428,n,&v), v, v = -sumdiv(n,d,if(d<n,A102283(n/d)*A365428(d),0)); mapput(memoA365428,n,v); (v)));
%Y A365428 Cf. A102283, A134323, A156277, A359377 (absolute values).
%K A365428 sign,mult
%O A365428 1
%A A365428 _Antti Karttunen_, Sep 16 2023
```

## Candidate 153: A163812 vs A163818 (score 72.4, agree 105, variant abs, family size 9)
Terms: 1, 1, 1, 1, 1, 0, -1, -1, -1, -1, 0, 1, 1, 1, 1, 0, -1, -1, -1, -1, 0, 1, 1, 1, 1, 0, -1, -1, -1, -1

### A163812
```
%I A163812 #16 Dec 06 2019 12:27:06
%S A163812 1,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,
%T A163812 -1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,
%U A163812 -1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1,0,-1,-1,-1,-1,0,1,1,1,1
%N A163812 Expansion of (1 - x^5) * (1 - x^6) / ((1 - x) * (1 - x^10)) in powers of x.
%H A163812 G. C. Greubel, <a href="/A163812/b163812.txt">Table of n, a(n) for n = 0..1000</a>
%H A163812 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (1,-1,1,-1).
%F A163812 Euler transform of length 10 sequence [ 1, 0, 0, 0, -1, -1, 0, 0, 0, 1].
%F A163812 a(5*n) = 0 unless n=0.
%F A163812 a(n) = -a(-n) unless n=0. a(n+5) = -a(n) unless n=0 or n=-5.
%F A163812 G.f.: (1 + x^2 + x^4) / (1 - x + x^2 - x^3 + x^4).
%F A163812 a(n) = (-1)^n * A163818(n). Convolution inverse of A163811.
%F A163812 G.f.: A(x) = 1 / (1 - x / ( 1 + x^4 / (1 + x^2))) = 1 + x / (1 - x / (1 + x^3 / (1 + x^2 / (1 + x / (1 - x))))). - _Michael Somos_, Jan 03 2013
%F A163812 a(n) = A099443(n-1), n>0. - _R. J. Mathar_, Aug 05 2009
%e A163812 G.f. = 1 + x + x^2 + x^3 + x^4 - x^6 - x^7 - x^8 - x^9 + x^11 + x^12 + x^13 + ...
%t A163812 a[ n_] := Boole[n == 0] + (-1)^Quotient[n, 5] Sign@Mod[n, 5]; (* _Michael Somos_, Jun 17 2015 *)
%o A163812 (PARI) {a(n) = (n==0) + [0, 1, 1, 1, 1, 0, -1, -1, -1, -1][n%10 + 1]};
%Y A163812 Cf. A099443, A163811, A163818.
%K A163812 sign,easy
%O A163812 0,1
%A A163812 _Michael Somos_, Aug 04 2009
```
### A163818
```
%I A163818 #20 Oct 02 2023 11:32:21
%S A163818 1,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,
%T A163818 -1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,
%U A163818 -1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1,0,-1,1,-1,1
%N A163818 Expansion of (1 - x) * (1 - x^6) / ((1 - x^2) * (1 - x^5)) in powers of x.
%H A163818 G. C. Greubel, <a href="/A163818/b163818.txt">Table of n, a(n) for n = 0..1000</a>
%H A163818 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (-1, -1, -1, -1).
%F A163818 Euler transform of length 6 sequence [-1, 1, 0, 0, 1, -1].
%F A163818 a(5*n) = 0 unless n=0. a(5*n + 1) = a(5*n + 3) = -1, a(5*n + 2) = a(5*n + 4) = a(0) = 1.
%F A163818 a(n) = -a(-n) unless n=0. a(n+5) = a(n) unless n=0 or n=-5.
%F A163818 G.f.: (1 + x^2 + x^4) / (1 + x + x^2 + x^3 + x^4).
%F A163818 G.f.: 1 / (1 + x / (1 + x^4 / (1 + x^2))). - _Michael Somos_, Jan 03 2013
%F A163818 a(n) = (-1)^n * A163812(n). Convolution inverse of A163817.
%e A163818 G.f. = 1 - x + x^2 - x^3 + x^4 - x^6 + x^7 - x^8 + x^9 - x^11 + x^12 - x^13 + ...
%t A163818 a[ n_] := Boole[n == 0] + {-1, 1, -1, 1, 0}[[Mod[n, 5, 1]]]; (* _Michael Somos_, Jun 17 2015 *)
%t A163818 a[ n_] := Boole[n == 0] + (-1)^(n + Quotient[n, 5]) Sign@Mod[n, 5]; (* _Michael Somos_, Jun 17 2015 *)
%t A163818 CoefficientList[Series[(1 + x^2 + x^4) / (1 + x + x^2 + x^3 + x^4), {x, 0, 100}], x] (* _Vincenzo Librandi_, Aug 05 2017 *)
%o A163818 (PARI) {a(n) = (n==0) + [ 0, -1, 1, -1, 1][n%5 + 1]};
%o A163818 (PARI) {a(n) = (n==0) + (-1)^(n + n\5) * kronecker(25, n)};
%Y A163818 Cf. A163813, A163817.
%K A163818 sign,easy
%O A163818 0,1
%A A163818 _Michael Somos_, Aug 04 2009
```

## Candidate 154: A164116 vs A164118 (score 72.4, agree 105, variant abs, family size 3)
Terms: 1, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1

### A164116
```
%I A164116 #23 Oct 02 2023 11:34:39
%S A164116 1,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,
%T A164116 -1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,
%U A164116 0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1,2,-1,0,0,-1
%N A164116 Expansion of (1 - x) * (1 - x^4) / (1 - x^5) in powers of x.
%C A164116 This sequence with a(0) replaced by 2 appears, together with three other sequences, in the formula 2*exp(2*Pi*n*I/5) = 2*T(n,x) + S(n-1,x)*sqrt(2+phi)*I, with x = (phi-1)/2 and I  = sqrt(-1), where phi = (1+sqrt(5))/2 (golden section) after reduction of powers using phi^2 = phi+1. T and S are Chebyshev polynomials from A053120 and A049310. This results in 2*exp(2*Pi*n*I/5) = (A(n) + B(n)*phi) + (C(n) + D(n)*phi)*sqrt(2+phi)*I, with A(n) = a(n+5), B(n) = A080891(n), C(n) = A156174(n+4) and D(n) = A010891(n+3) for n >= 0. - _Wolfdieter Lang_, Feb 26 2014
%H A164116 G. C. Greubel, <a href="/A164116/b164116.txt">Table of n, a(n) for n = 0..10000</a>
%H A164116 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (-1, -1, -1, -1).
%F A164116 Euler transform of length 5 sequence [-1, 0, 0, -1, 1].
%F A164116 a(n) = a(-n) for all n in Z. a(n+5) = a(n) unless n=0 or n=-5.
%F A164116 G.f.: (1 - x^4)/(1 + x + x^2 + x^3 + x^4).
%F A164116 a(n) = (-1)^n * A164118(n). Convolution inverse of A164115.
%F A164116 a(n) = 2*0^mod(n,5) - 0^n - mod(mod(n+2,5),2). - _Wesley Ivan Hurt_, Apr 28 2015
%e A164116 G.f. = 1 - x - x^4 + 2*x^5 - x^6 - x^9 + 2*x^10 - x^11 - x^14 + 2*x^15 - x^16 + ...
%e A164116 exp(2*Pi*3*I/5) = (0 - phi) + (1 - phi)*sqrt(2+phi)*I, with phi = (1+sqrt(5))/2. - _Wolfdieter Lang_, Feb 26 2014
%t A164116 CoefficientList[Series[(1-x)(1-x^4)/(1-x^5),{x,0,110}],x] (* _Harvey P. Dale_, Sep 25 2013 *)
%o A164116 (PARI) {a(n) = -(n==0) + [2, -1, 0, 0, -1][n%5 + 1]};
%o A164116 (Magma) m:=50; R<x>:=PowerSeriesRing(Integers(), m); Coefficients(R!((1 - x^4)/(1+x+x^2+x^3+x^4))); // _G. C. Greubel_, Sep 22 2018
%Y A164116 Cf. A164115, A164118.
%K A164116 sign,easy
%O A164116 0,6
%A A164116 _Michael Somos_, Aug 10 2009
```
### A164118
```
%I A164118 #10 Oct 02 2023 11:35:48
%S A164118 1,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,
%T A164118 2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,
%U A164118 2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1,-2,-1,0,0,1,2,1,0,0,-1
%N A164118 Expansion of (1 - x^2) * (1 - x^4) * (1 - x^5) / ((1 - x) * (1 - x^10)) in powers of x.
%H A164118 <a href="/index/Rec#order_04">Index entries for linear recurrences with constant coefficients</a>, signature (1, -1, 1, -1).
%F A164118 Euler transform of length 10 sequence [ 1, -1, 0, -1, -1, 0, 0, 0, 0, 1].
%F A164118 a(-n) = a(n). a(n + 5) = -a(n) unless n=0 or n=-5.
%F A164118 G.f.: (1 - x^4) / (1 - x + x^2 - x^3 + x^4).
%t A164118 CoefficientList[Series[(1 - x^4) / (1 - x + x^2 - x^3 + x^4), {x, 0, 50}], x] (* _G. C. Greubel_, Sep 12 2017 *)
%o A164118 (PARI) {a(n) = -(n==0) + [2, 1, 0, 0, -1, -2, -1, 0, 0, 1][n%10 + 1]}
%Y A164118 A164116(n) = (-1)^n * a(n). Convolution inverse of A164117.
%K A164118 sign,easy
%O A164118 0,6
%A A164118 _Michael Somos_, Aug 10 2009
```

## Candidate 155: A209927 vs A223139 (score 72.4, agree 105, variant drop1, family size 4)
Terms: 2, 3, 0, 2, 7, 7, 5, 6, 3, 7, 7, 3, 1, 9, 9, 4, 6, 4, 6, 5, 5, 9, 6, 1, 0, 6, 3, 3, 7, 3

### A209927
```
%I A209927 #46 Feb 03 2025 10:50:57
%S A209927 2,3,0,2,7,7,5,6,3,7,7,3,1,9,9,4,6,4,6,5,5,9,6,1,0,6,3,3,7,3,5,2,4,7,
%T A209927 9,7,3,1,2,5,6,4,8,2,8,6,9,2,2,6,2,3,1,0,6,3,5,5,2,2,6,5,2,8,1,1,3,5,
%U A209927 8,3,4,7,4,1,4,6,5,0,5,2,2,2,6,0,2,3,0,9,5,4,1,0,0,9,2,4,5,3,5,8,8,3,6,7,5,7
%N A209927 Decimal expansion of sqrt(3 + sqrt(3 + sqrt(3 + sqrt(3 + ... )))).
%C A209927 The number x given by the infinitely nested radical for n = 3 is such that x^2 = x + 3, bearing some similarity to the golden ratio phi with its property that phi^2 = phi + 1. Also, 3/x = x - 1.
%C A209927 The mentioned polynomial x^2 - x - 3 has the present number as positive root, and the negative one is -A223139. - _Wolfdieter Lang_, Aug 29 2022
%C A209927 It is the spectral radius of the bull-graph (see Seeger and Sossa, 2023). - _Stefano Spezia_, Sep 19 2023
%C A209927 c^n = A006130(n) + A006130(n-1) * d, where c = (1 + sqrt(13))/2 and d = (-1 + sqrt(13))/2. - _Gary W. Adamson_, Nov 25 2023
%C A209927 c^n = A052533(n) + A006130(n-1)*c, with A006130(-1) = 0. This is also valid for powers of 1/c = A356033, with A052533 and A006130 given there in terms of S-Chebyshev polynomials (A049310), used for negative indices. - _Wolfdieter Lang_, Nov 26 2023
%H A209927 Alberto Seeger and David Sossa, <a href="https://ajc.maths.uq.edu.au/pdf/87/ajc_v87_p258.pdf">Infinite families of connected graphs with equal spectral radius</a>, Australas. J. Combin. 87 (2) (2023), 258-276. See p. 274.
%H A209927 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%F A209927 Closed form: (sqrt(13) + 1)/2 = A098316-1 = A085550+2 = 3*(A188943-1).
%e A209927 2.30277563773...
%p A209927 Digits:=140:
%p A209927 evalf((sqrt(13)+1)/2);  # _Alois P. Heinz_, Sep 19 2023
%t A209927 RealDigits[(1 + Sqrt[13])/2, 10, 130][[1]]
%t A209927 RealDigits[ Fold[ Sqrt[#1 + #2] &, 0, Table[3, {n, 168}]], 10, 111][[1]] (* _Robert G. Wilson v_, Oct 02 2018 *)
%o A209927 (PARI) (sqrt(13)+1)/2 \\ _Altug Alkan_, Oct 03 2018
%Y A209927 Cf. A157532 (continued fraction), A001622, A010470, A085550, A098316, A188943, A223139.
%Y A209927 Cf. A006130, A049310, A052533, A209927.
%K A209927 nonn,cons,easy
%O A209927 1,1
%A A209927 _Alonso del Arte_, Mar 17 2012
```
### A223139
```
%I A223139 #33 May 13 2026 23:14:36
%S A223139 1,3,0,2,7,7,5,6,3,7,7,3,1,9,9,4,6,4,6,5,5,9,6,1,0,6,3,3,7,3,5,2,4,7,
%T A223139 9,7,3,1,2,5,6,4,8,2,8,6,9,2,2,6,2,3,1,0,6,3,5,5,2,2,6,5,2,8,1,1,3,5,
%U A223139 8,3,4,7,4,1,4,6,5,0,5,2,2,2,6,0,2,3,0,9,5,4,1,0,0,9,2,4,5,3,5,8,8,3,6,7,5,7
%N A223139 Decimal expansion of (sqrt(13) - 1)/2.
%C A223139 Apart from a(1) the same as A209927 and A085550. - _Joerg Arndt_, Sep 17 2013
%C A223139 Decimal expansion of sqrt(3 - sqrt(3 - sqrt(3 - sqrt(3 - ... )))).
%C A223139 Sequence with a(1) = 2 is decimal expansion of sqrt(3 + sqrt(3 + sqrt(3 + sqrt(3 + ... )))) - A209927.
%C A223139 This is the positive root of x^2 + x - 3, and the negative one is -A209927. - _Wolfdieter Lang_, Aug 29 2022
%H A223139 B. Sury, <a href="https://www.jstor.org/stable/10.4169/002557010x521840">Nothing Lucky about 13</a>, Mathematics Magazine, Vol. 83, No. 4 (October 2010), pp. 289-293.
%H A223139 <a href="/index/Al#algebraic_02">Index entries for algebraic numbers, degree 2</a>.
%F A223139 Closed form: (sqrt(13) - 1)/2 = A209927-1 = A098316-2.
%F A223139 sqrt(3 - sqrt(3 - sqrt(3 - sqrt(3 - ... )))) + 1 = sqrt(3 + sqrt(3 + sqrt(3 + sqrt(3 + ... )))). See A209927.
%F A223139 Equals 2*(cos(2*Pi/13) + cos(6*Pi/13) + cos(8*Pi/13)) (see Sury link). - _Michel Marcus_, Aug 21 2015
%e A223139 1.3027756377319946465...
%t A223139 RealDigits[(Sqrt[13] - 1)/2, 10, 130]
%o A223139 (PARI) (sqrt(13)-1)/2 \\ _Altug Alkan_, Oct 02 2018
%Y A223139 Cf. A085550, A098316, A209927.
%Y A223139 Cf. A122553 (continued fraction).
%K A223139 nonn,cons,easy
%O A223139 1,2
%A A223139 _Jaroslav Krizek_, Apr 02 2013
```

## Candidate 156: A290110 vs A300250 (score 72.4, agree 105, variant raw, family size 14)
Terms: 1, 2, 2, 3, 2, 4, 2, 5, 3, 4, 2, 6, 2, 4, 4, 7, 2, 8, 2, 9, 4, 4, 2, 10, 3, 4, 5, 9, 2, 11

### A290110
```
%I A290110 #36 Jul 11 2026 18:50:08
%S A290110 1,2,2,3,2,4,2,5,3,4,2,6,2,4,4,7,2,8,2,9,4,4,2,10,3,4,5,9,2,11,2,12,4,
%T A290110 4,4,13,2,4,4,14,2,15,2,9,6,4,2,16,3,8,4,9,2,17,4,14,4,4,2,18,2,4,6,
%U A290110 19,4,15,2,9,4,11,2,20,2,4,8,9,4,15,2,21,7,4,2,22,4,4,4,23,2,24,4,9,4,4,4,25,2,8,9,26,2,15,2,23,11
%N A290110 a(n) = the discovery rank of the factorization pattern of the sequence of divisors of n.
%C A290110 The definition for the factorization pattern of the sequence of divisors of a number n is the same as in sequence A191743. Let's use the abbreviation FPSD. One can generate a list of distinct FPSD by trying all integers, 1, 2, 3, ..., and ignoring duplicates. a(n) is the index of the FPSD of n in this list.
%C A290110 From _Antti Karttunen_, Mar 07 & 08 2018: (Start)
%C A290110 This is NOT restricted growth sequence transform of A297174, but instead A300250 is, from which this differs for the first time at n=858, where a(858) = 115, while A300250(858) = 75.
%C A290110 This gives a finer partitioning of natural numbers than A300250, and indeed we have:
%C A290110 For all i, j:
%C A290110   a(i) = a(j) => A300250(i) = A300250(j) => A101296(i) = A101296(j).
%C A290110 (End)
%H A290110 Michael De Vlieger, <a href="/A290110/b290110.txt">Table of n, a(n) for n = 1..65537</a>
%F A290110 A191743(n) = MIN(k such that a(k)=n).
%F A290110 a(p) = 2, for p prime;
%F A290110 a(p^2) = 3, for p prime;
%F A290110 a(p*q) = 4, for p, q distinct primes.
%e A290110 The divisors of 17 are {1, 17}. They follow the pattern {1, p} which is pattern number 2 in discovery order. a(17)=2.
%e A290110 The divisors of 28 are {1, 2, 4, 7, 14, 28}. They follow the pattern {1, p, p^2, q, p*q, p^2*q}, which is pattern number 9 in discovery order. a(28)=9.
%e A290110 From _Michael De Vlieger_ and _Antti Karttunen_, Mar 07 & 08 2018: (Start)
%e A290110 Divisors of 462 = 2*3*7*11 (p=2, q=3, r=7, s=11) are 1, 2, 3, 6, 7, 11, 14, 21, 22, 33, 42, 66, 77, 154, 231, 462, thus the factorization patterns in the order of increasing divisors are: 1, p, q, pq, r, s, pr, qr, ps, qs, pqr, pqs, rs, prs, qrs and pqrs.
%e A290110 Divisors of 546 = 2*3*7*13 (p=2, q=3, r=7, s=13) are 1, 2, 3, 6, 7, 13, 14, 21, 26, 39, 42, 78, 91, 182, 273, 546, thus the factorization patterns are 1, p, q, pq, r, s, pr, qr, ps, qs, pqr, pqs, rs, prs, qrs and pqrs, that is, identical with those of 462, thus a(546) = a(462).
%e A290110 Divisors of 858 = 2*3*11*13 (p=2, q=3, r=11, s=13) are 1, 2, 3, 6, 11, 13, 22, 26, 33, 39, 66, 78, 143, 286, 429, 858, thus the factorization patterns are 1, p, q, pq, r, s, pr, ps, qr, qs, pqr, pqs, rs, prs, qrs and pqrs. At the 8th divisor (26), we see that pattern ps is different from pattern qr of the 8th divisor of 546 (21), thus a(858) is not equal to a(546).
%e A290110 (End)
%t A290110 FactorizationPattern[n_] := Module[
%t A290110   {pn, fd, f1, f2, d},
%t A290110   pn = First /@ FactorInteger[n];
%t A290110   fd = FactorInteger[ReplacePart[Divisors[n], 1 -> {}]];
%t A290110   f1 = (ReplacePart[#,
%t A290110       1 -> FromCharacterCode[
%t A290110         111 + First[Position[pn, First[#]]]]]) &;
%t A290110   f2 = (f1 /@ #) &;
%t A290110   fd = f2 /@ fd;
%t A290110   f1 = (Power[First[#], Last[#]]) &;
%t A290110   For[i = 1, i <= Length[fd], i++,
%t A290110    d = fd[[i]];
%t A290110    For[j = 1, j <= Length[d], j++,d[[j]] = f1[d[[j]]];];
%t A290110    d = Product[x, {x, d}];
%t A290110    fd[[i]] = d;
%t A290110   ];
%t A290110   fd
%t A290110 ]
%t A290110 ListFactorizationPatternIndices[n_] := Module[
%t A290110   {mem, k, i, p, a},
%t A290110   mem = Association[];
%t A290110   a = {}; k = 0;
%t A290110   For[i = 1, i \[LessSlantEqual] n, i++,
%t A290110    p = FactorizationPattern[i];
%t A290110    If[KeyExistsQ[mem, p],,
%t A290110     k++;
%t A290110     mem = Append[mem, p -> k]
%t A290110    ];
%t A290110    a = Append[a, mem[p]]
%t A290110   ];
%t A290110   a
%t A290110 ]
%t A290110 ListFactorizationPatternIndices[80]
%t A290110 (* Alternative: *)
%t A290110 f[n_] := If[n==1, 1, Block[{p = First /@ FactorInteger@n, z,x}, z= Table[p[[i]] -> x[i], {i, Length@p}]; Times @@ (((#[[1]] /. z)^#[[2]]) & /@ FactorInteger@ #) & /@ Divisors[n]]]; A = <||>; Table[k = f[n]; If[ KeyExistsQ[A, k], A[k], t = 1 + Length@A; A[k] = t], {n, 80}] (* _Giovanni Resta_, Jul 20 2017 *)
%Y A290110 Cf. A191743, A300250.
%K A290110 nonn
%O A290110 1,2
%A A290110 _Luc Rousseau_, Jul 19 2017
%E A290110 More terms from _Michael De Vlieger_ and _Antti Karttunen_, Mar 07 2018
```
### A300250
```
%I A300250 #13 Mar 24 2018 18:53:50
%S A300250 1,2,2,3,2,4,2,5,3,4,2,6,2,4,4,7,2,8,2,9,4,4,2,10,3,4,5,9,2,11,2,12,4,
%T A300250 4,4,13,2,4,4,14,2,15,2,9,6,4,2,16,3,8,4,9,2,17,4,14,4,4,2,18,2,4,6,
%U A300250 19,4,15,2,9,4,11,2,20,2,4,8,9,4,15,2,21,7,4,2,22,4,4,4,23,2,24,4,9,4,4,4,25,2,8,9,26,2,15,2,23,11
%N A300250 Restricted growth sequence transform of A297174: a filter sequence recording the prime signatures of divisors of n, with divisors ordered by their magnitude.
%C A300250 This sequence gives a coarser partitioning of natural numbers than A290110, and finer than A101296:
%C A300250 For all i, j:
%C A300250   A290110(i) = A290110(j) => a(i) = a(j) => A101296(i) = A101296(j).
%H A300250 Antti Karttunen, <a href="/A300250/b300250.txt">Table of n, a(n) for n = 1..65537</a>
%e A300250 Divisors of 462 are 1, 2, 3, 6, 7, 11, 14, 21, 22, 33, 42, 66, 77, 154, 231, 462.
%e A300250 Divisors of 858 are 1, 2, 3, 6, 11, 13, 22, 26, 33, 39, 66, 78, 143, 286, 429, 858.
%e A300250 If one takes the smallest prime-signature representative (A046523) of each these, one gets in both cases [1, 2, 2, 6, 2, 2, 6, 6, 6, 6, 30, 30, 6, 30, 30, 210]. E.g. 462 = 2*3*7*11 and 858 = 2*3*11*13, which both have the same prime signature as 210 = 2*3*5*7. And similarly for all the other divisors, from which follows that a(462) = a(858).
%e A300250 On the other hand, for 12 = 2*2*3 the divisors are 1, 2, 3, 2*2, 2*3, 2*2*3, and for 18 = 2*3*3 the divisors are 1, 2, 3, 2*3, 3*3, 2*3*3, and because the prime signatures differ both in the fourth and in the fifth places, a(18) != a(12).
%o A300250 (PARI)
%o A300250 up_to = 65537;
%o A300250 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A300250 write_to_bfile(start_offset,vec,bfilename) = { for(n=1, length(vec), write(bfilename, (n+start_offset)-1, " ", vec[n])); }
%o A300250 A046523(n) = { my(f=vecsort(factor(n)[, 2], , 4), p); prod(i=1, #f, (p=nextprime(p+1))^f[i]); };  \\ From A046523
%o A300250 v101296 = rgs_transform(vector(up_to, n, A046523(n)));
%o A300250 A101296(n) = v101296[n];
%o A300250 A297174(n) = { my(s=0,i=-1); fordiv(n, d, if(d>1, i += (A101296(d)-1); s += 2^i)); (s); };
%o A300250 write_to_bfile(1,rgs_transform(vector(up_to,n,A297174(n))),"b300250.txt");
%Y A300250 Cf. A046523, A101296, A297174, A300716.
%Y A300250 Differs from similar A290110 for the first time at n=858.
%K A300250 nonn
%O A300250 1,2
%A A300250 _Antti Karttunen_, Mar 07 2018
```

## Candidate 157: A305979 vs A334868 (score 72.4, agree 63, variant raw, family size 3)
Terms: 1, 2, 2, 2, 2, 3, 2, 4, 2, 5, 2, 6, 2, 7, 8, 2, 2, 9, 2, 10, 11, 12, 2, 13, 2, 14, 15, 16, 2, 17

### A305979
```
%I A305979 #7 Jul 02 2018 20:25:19
%S A305979 1,2,2,2,2,3,2,4,2,5,2,6,2,7,8,2,2,9,2,10,11,12,2,13,2,14,15,16,2,17,
%T A305979 2,18,19,20,21,22,2,23,24,25,2,26,2,27,28,29,2,30,2,31,32,33,2,34,35,
%U A305979 36,37,38,2,39,2,40,41,42,43,44,2,45,46,47,2,48,2,49,50,51,52,53,2,54,2,55,2,56,57,58,59,60,2,61,62,63,64,65,66,67,2,68,69,70,2
%N A305979 Filter sequence for a(Fermi-Dirac primes) = constant sequences.
%C A305979 For all i, j:
%C A305979   a(i) = a(j) => A305976(i) = A305976(j).
%C A305979   a(i) = a(j) => A302791(i) = A302791(j).
%H A305979 Antti Karttunen, <a href="/A305979/b305979.txt">Table of n, a(n) for n = 1..100000</a>
%F A305979 a(1) = 1; for n > 1, if A302777(n) is 1 [when n is in A050376], a(n) = 2, otherwise a(n) = 1 + n - A302778(n) = running count from 3 onward.
%o A305979 (PARI)
%o A305979 up_to = 100000;
%o A305979 partialsums(f,up_to) = { my(v = vector(up_to), s=0); for(i=1,up_to,s += f(i); v[i] = s); (v); }
%o A305979 A209229(n) = (n && !bitand(n, n-1));
%o A305979 A302777(n) = A209229(isprimepower(n));
%o A305979 v302778 = partialsums(A302777,up_to);
%o A305979 A302778(n) = v302778[n];
%o A305979 A305979(n) = if(1==n,n,if(1==A302777(n),2,1+n-A302778(n)));
%Y A305979 Cf. A050376, A302777, A302778, A302791, A305975, A305976.
%K A305979 nonn
%O A305979 1,2
%A A305979 _Antti Karttunen_, Jul 02 2018
```
### A334868
```
%I A334868 #8 Jun 09 2020 07:24:27
%S A334868 1,2,2,2,2,3,2,4,2,5,2,6,2,7,8,2,2,9,2,10,11,12,2,13,2,14,15,16,2,17,
%T A334868 2,18,19,20,21,22,2,23,24,25,2,26,2,27,28,29,2,30,2,31,32,33,2,34,35,
%U A334868 36,37,38,2,39,2,40,41,6,42,43,2,44,45,46,2,47,2,48,49,50,51,52,2,53,2,54,2,55,56,57,58,59,2,60,61,62,63,64,65,66,2,67,68,8,2,69,2,70,71
%N A334868 Lexicographically earliest infinite sequence such that a(i) = a(j) => f(i) = f(j) for all i, j >= 1, where f(1) = 0 and for n > 1, f(n) = -1 if n is in A050376, and f(n) = A334870(n) otherwise.
%C A334868 For all i, j: A305979(i) = A305979(j) => a(i) = a(j) => A334872(i) = A334872(j).
%H A334868 Antti Karttunen, <a href="/A334868/b334868.txt">Table of n, a(n) for n = 1..65537</a>
%o A334868 (PARI)
%o A334868 up_to = 65537;
%o A334868 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A334868 ispow2(n) = (n && !bitand(n,n-1));
%o A334868 A302777(n) = ispow2(isprimepower(n));
%o A334868 A334870(n) = if(issquare(n),sqrtint(n),my(c=core(n), m=n); forprime(p=2, , if(!(c % p), m/=p; break, m*=p)); (m));
%o A334868 A334868aux(n) = if(1==n,0,if(A302777(n),-1,A334870(n)));
%o A334868 v334868 = rgs_transform(vector(up_to,n,A334868aux(n)));
%o A334868 A334868(n) = v334868[n];
%Y A334868 Cf. A050376 (positions of 2's), A305979, A334869, A334870, A334872.
%K A334868 nonn
%O A334868 1,2
%A A334868 _Antti Karttunen_, Jun 08 2020
```

## Candidate 158: A351454 vs A351460 (score 72.4, agree 105, variant raw, family size 5)
Terms: 1, 2, 3, 2, 4, 3, 5, 2, 6, 4, 7, 3, 8, 5, 9, 2, 10, 6, 11, 4, 12, 7, 13, 3, 14, 8, 15, 5, 16, 9

### A351454
```
%I A351454 #12 Feb 14 2022 11:21:58
%S A351454 1,2,3,2,4,3,5,2,6,4,7,3,8,5,9,2,10,6,11,4,12,7,13,3,14,8,15,5,16,9,
%T A351454 17,2,18,10,19,6,20,11,21,4,22,12,23,7,24,13,25,3,26,14,27,8,28,15,29,
%U A351454 5,30,16,31,9,32,17,33,2,34,18,35,10,36,19,37,6,38,20,39,11,40,21,41,4,42,22,43,12,44,23,45,7,46,24,47,13,48,25,49,3,50,26,51,14,52,27,53,8,54
%N A351454 Lexicographically earliest infinite sequence such that a(i) = a(j) => A006530(i) = A006530(j), A329697(i) = A329697(j) and A331410(i) = A331410(j) for all i, j >= 1.
%C A351454 Restricted growth sequence transform of the triplet [A006530(n), A329697(n), A331410(n)], or equally, of the ordered pair [A006530(n), A335880(n)].
%C A351454 For all i, j >= 1: A324400(i) = A324400(j) => a(i) = a(j).
%H A351454 Antti Karttunen, <a href="/A351454/b351454.txt">Table of n, a(n) for n = 1..65537</a>
%e A351454 a(99) = a(121) because 99 = 3^2 * 11 and 121 = 11^2, so they have equal largest prime factor (A006530), and they also agree on A329697(99) = A329697(121) = 4 and on A331410(99) = A331410(121) = 4, therefore they get equal value (which is 51) allotted to them by the restricted growth sequence transform. - _Antti Karttunen_, Feb 14 2022
%o A351454 (PARI)
%o A351454 up_to = 65537;
%o A351454 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A351454 A006530(n) = if(1==n, n, my(f=factor(n)); f[#f~, 1]);
%o A351454 A329697(n) = if(!bitand(n,n-1),0,1+A329697(n-(n/vecmax(factor(n)[, 1]))));
%o A351454 A331410(n) = if(!bitand(n,n-1),0,1+A331410(n+(n/vecmax(factor(n)[, 1]))));
%o A351454 Aux351454(n) = [A006530(n), A329697(n), A331410(n)];
%o A351454 v351454 = rgs_transform(vector(up_to, n, Aux351454(n)));
%o A351454 A351454(n) = v351454[n];
%Y A351454 Cf. A006530, A329697, A331410, A335880.
%Y A351454 Cf. also A324400, A336936, A351453.
%Y A351454 Differs from A351452 for the first time at n=49, where a(49) = 26, while A351452(49) = 19.
%Y A351454 Differs from A351460 for the first time at n=121, where a(121) = 51, while A351460(121) = 62.
%Y A351454 Differs from A103391(1+n) for the first time after n=1 at n=121, where a(121) = 51, while A103391(122) = 62.
%K A351454 nonn
%O A351454 1,2
%A A351454 _Antti Karttunen_, Feb 11 2022
```
### A351460
```
%I A351460 #15 Feb 14 2022 11:22:17
%S A351460 1,2,3,2,4,3,5,2,6,4,7,3,8,5,9,2,10,6,11,4,12,7,13,3,14,8,15,5,16,9,
%T A351460 17,2,18,10,19,6,20,11,21,4,22,12,23,7,24,13,25,3,26,14,27,8,28,15,29,
%U A351460 5,30,16,31,9,32,17,33,2,34,18,35,10,36,19,37,6,38,20,39,11,40,21,41,4,42,22,43,12,44,23,45,7,46,24,47,13,48,25,49,3,50,26,51,14,52,27,53,8,54
%N A351460 Lexicographically earliest infinite sequence such that a(i) = a(j) => A006530(i) = A006530(j), A206787(i) = A206787(j) and A336651(i) = A336651(j) for all i, j >= 1.
%C A351460 Restricted growth sequence transform of the ordered triplet [A006530(n), A206787(n), A336651(n)].
%C A351460 For all i, j >= 1:
%C A351460   A324400(i) = A324400(j) => a(i) = a(j),
%C A351460   a(i) = a(j) => A347241(i) = A347241(j),
%C A351460   a(i) = a(j) => A351461(i) = A351461(j) => A347240(i) = A347240(j).
%H A351460 Antti Karttunen, <a href="/A351460/b351460.txt">Table of n, a(n) for n = 1..65537</a>
%e A351460 a(429) = a(455) because 429 = 3*11*13 and 455 = 5*7*13, so they have equal largest prime factor (A006530), and they also agree on A206787(429) = A206787(455) = 672 and on A336651(429) = A336651(455) = 1 (because both are squarefree), therefore they get equal value (which is 216) allotted to them by the restricted growth sequence transform. - _Antti Karttunen_, Feb 14 2022
%o A351460 (PARI)
%o A351460 up_to = 65537;
%o A351460 rgs_transform(invec) = { my(om = Map(), outvec = vector(length(invec)), u=1); for(i=1, length(invec), if(mapisdefined(om,invec[i]), my(pp = mapget(om, invec[i])); outvec[i] = outvec[pp] , mapput(om,invec[i],i); outvec[i] = u; u++ )); outvec; };
%o A351460 A006530(n) = if(1==n, n, my(f=factor(n)); f[#f~, 1]);
%o A351460 A206787(n) = sumdiv(n, d, d*(d % 2)*issquarefree(d)); \\ From A206787
%o A351460 A336651(n) = { my(f=factor(n)); prod(i=1, #f~, if(2==f[i,1],1,f[i,1]^(f[i,2]-1))); };
%o A351460 Aux351460(n) = [A006530(n), A206787(n), A336651(n)];
%o A351460 v351460 = rgs_transform(vector(up_to, n, Aux351460(n)));
%o A351460 A351460(n) = v351460[n];
%Y A351460 Cf. A006530, A206787, A336651, A347241, A351461.
%Y A351460 Cf. also A324400, A351452.
%Y A351460 Differs from A351454 for the first time at n=121, where a(121) = 62, while A351454(121) = 51.
%Y A351460 Differs from A103391(1+n) for the first time after n=1 at n=455, where a(455) = 216, while A103391(456) = 229.
%K A351460 nonn
%O A351460 1,2
%A A351460 _Antti Karttunen_, Feb 11 2022
```

## Candidate 159: A030205 vs A159817 (score 72.0, agree 72, variant abs, family size 2)
Terms: 1, -2, -1, 2, 1, 0, 2, 2, -6, -4, -4, 6, 1, 4, 6, -4, 0, -2, 2, -4, 6, -10, -1, -6, -3, 12, -6, 0, 8, 12

### A030205
```
%I A030205 #69 May 30 2026 16:40:00
%S A030205 1,-2,-1,2,1,0,2,2,-6,-4,-4,6,1,4,6,-4,0,-2,2,-4,6,-10,-1,-6,-3,12,-6,
%T A030205 0,8,12,2,2,-2,2,-12,-12,2,-2,0,8,-11,6,6,-12,-6,4,8,4,2,0,6,14,4,-6,
%U A030205 2,-4,-6,-6,2,-12,-11,-12,-1,2,20,0,-8,-4,18,-4,12,0
%N A030205 Expansion of q^(-1/2) * eta(q)^2 * eta(q^5)^2 in power of q.
%C A030205 This eta-quotient of conductor 20 is one of the twelve weight 2 newforms listed by Martin and Ono.
%C A030205 The associated elliptic curve is "20a1": y^2 = x^3 + x^2 + 4*x + 4 or "20a2": y^2 = x^3 + x^2 - x.
%C A030205 Number 39 of the 74 eta-quotients listed in Table I of Martin (1996).
%C A030205 The mentioned eta-quotient is in fact eta^2(2*z) * eta^2(10*z) with q = exp(2*Pi*i*tau) with Im(tau) > 0, I^2 = -1, with the q-expansion coefficients b(n) from the Michael Somos Oct Aug 13 2006 formula: b(2*n) = 0 and b(2*n+1) = a(n), for n >= 0. A273163(k) = b(prime(k)), k >= 1. See also the comments on multiplicativity of b(n) (called there c(n)) with b(2^k) = b(2)^k = 0, b(5^k) = b(5)^k = (-1)^k, and b(prime(n)^k) = (sqrt(prime(n)))^k*S(k,A273163(n)/sqrt(prime(n))) with Chebyshev's S polynomials (A049310), for n = 2, and n >= 4 and k >= 2. Compare this with the b(p^(e+2)) recurrence given by Michael Somos, Oct 31 2005. - _Wolfdieter Lang_, May 23 2016
%H A030205 Seiichi Manyama, <a href="/A030205/b030205.txt">Table of n, a(n) for n = 0..1000</a>
%H A030205 M. Koike, <a href="http://projecteuclid.org/euclid.nmj/1118787564">On McKay's conjecture</a>, Nagoya Math. J., 95 (1984), 85-89.
%H A030205 LMFDB, <a href="https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/20/2/">Space of modular forms of level 20 and weight 2</a>.
%H A030205 Y. Martin, <a href="https://doi.org/10.1090/S0002-9947-96-01743-6">Multiplicative eta-quotients</a>, Trans. Amer. Math. Soc. 348 (1996), no. 12, 4825-4856, see page 4852 Table I.
%H A030205 Y. Martin and K. Ono, <a href="https://doi.org/10.1090/S0002-9939-97-03928-2">Eta-quotients and elliptic curves</a>, Proc. Amer. Math. Soc. 125 (1997), no. 11, 3169-3176. MR1401749 (97m:11057)
%H A030205 K. Ono, <a href="https://www.jstor.org/stable/2974471">Ramanujan, taxicabs, birthdates, ZIP codes and twists</a>, Amer. Math. Monthly, 104 (1997), 912-917. MR1490909 (98i:11020)
%H A030205 Michael Somos, <a href="/A030203/a030203.txt">Index to Yves Martin's list of 74 multiplicative eta-quotients and their A-numbers</a>
%F A030205 Euler transform of period 5 sequence [ -2, -2, -2, -2, -4, ...]. - _Michael Somos_, Oct 31 2005
%F A030205 Given g.f. A(x), then B(q) = q * A(q)^2 satisfies 0 = f(B(q), B(q^2), B(q^4)) where f(u, v, w) = u*w * (u + 8*v + 16*w) - v^3. - _Michael Somos_, Oct 31 2005
%F A030205 a(n) = b(2*n + 1) where b() is multiplicative with b(2^e) = 0^e, b(5^e) = (-1)^e, else b(p^(e+2)) = b(p)*b(p^(e+1)) - p*b(p^e). - _Michael Somos_, Oct 31 2005
%F A030205 a(n) = b(2*n + 1) and b(p) = p minus number of points of elliptic curve "20a1" or "20a2" modulo p. - _Michael Somos_, Aug 13 2006
%F A030205 G.f.: (Product_{k>0} (1 - x^k) * (1 - x^(5*k)))^2.
%F A030205 a(121*n + 60) = -11 * a(n).
%F A030205 Convolution square is A030210. - _Michael Somos_, Jun 13 2014
%F A030205 a(n) = (-1)^n * A159817(n). - _Michael Somos_, Jun 10 2015
%F A030205 G.f. is a period 1 Fourier series which satisfies f(-1 / (20 t)) = 20 (t/i)^2 f(t) where q = exp(2 Pi i t). - _Michael Somos_, Jun 10 2015
%F A030205 a(n) = A276491(2*n+1), 0 = A276491(2*n). - _Michael Somos_, Oct 07 2025
%e A030205 G.f. = 1 - 2*x - x^2 + 2*x^3 + x^4 + 2*x^6 + 2*x^7 - 6*x^8 - 4*x^9 - 4*x^10 + ...
%e A030205 G.f. of b(n) from eta^2(2*z)*eta^2(10*z) = q - 2*q^3 - q^5 + 2*q^7 + q^9 + 2*q^13 + 2*q^15 - 6*q^17 - 4*q^19 + ..., where q = exp(2*Pi*I*z).
%t A030205 a[ n_] := SeriesCoefficient[ (QPochhammer[ x] QPochhammer[ x^5])^2, {x, 0, n}]; (* _Michael Somos_, May 28 2013 *)
%o A030205 (PARI) {a(n) = if( n<0, 0, n = 2*n + 1; ellan( ellinit( [0, 1, 0, 4, 4], 1), n)[n])}; /* _Michael Somos_, Oct 31 2005 */
%o A030205 (PARI) {a(n) = my(A); if( n<0, 0, A = x * O(x^n); polcoeff( (eta(x + A) * eta(x^5 + A))^2, n))}; /* _Michael Somos_, Oct 31 2005 */
%o A030205 (PARI) {a(n) = if( n<0, 0, n = 2*n + 1; ellan( ellinit( [0, 1, 0, -1, 0], 1), n)[n])}; /* _Michael Somos_, Aug 13 2006 */
%o A030205 (PARI) {a(n) = my(A, p, e, x, y, a0, a1); if( n<0, 0, n = 2*n + 1; A = factor(n); prod( k=1, matsize(A)[1], [p, e] = A[k,]; if( p==2, 0, p==5, (-1)^e, a0=1; a1 = y = -sum( x=0, p-1, kronecker( x^3 + x^2 - x, p)); for( i=2, e, x = y*a1 - p*a0; a0=a1; a1=x); a1)))}; /* _Michael Somos_, Aug 13 2006 */
%o A030205 (SageMath) CuspForms( Gamma0(20), 2, prec=92).0; # _Michael Somos_, May 28 2013
%o A030205 (Magma) Basis( CuspForms( Gamma0(20), 2), 145) [1]; /* _Michael Somos_, May 27 2014 */
%o A030205 (Magma) A := Basis( CuspForms( Gamma1(20), 2), 145); A[1] - 2*A[3]; /* _Michael Somos_, May 17 2015 */
%Y A030205 Cf. A030210, A049310, A159817, A273163, A276491.
%K A030205 sign
%O A030205 0,2
%A A030205 _N. J. A. Sloane_
```
### A159817
```
%I A159817 #26 May 30 2026 16:40:33
%S A159817 1,2,-1,-2,1,0,2,-2,-6,4,-4,-6,1,-4,6,4,0,2,2,4,6,10,-1,6,-3,-12,-6,0,
%T A159817 8,-12,2,-2,-2,-2,-12,12,2,2,0,-8,-11,-6,6,12,-6,-4,8,-4,2,0,6,-14,4,
%U A159817 6,2,4,-6,6,2,12,-11,12,-1,-2,20,0,-8,4,18,4,12,0,-6,-6,-6,-20,-6,-4,-22,-12,12,10,0,-18,-9,4,-6,-2,-24
%N A159817 Coefficients of L-series for elliptic curve "80b2": y^2 = x^3 - x^2 - x.
%C A159817 Number 61 of the 74 eta-quotients listed in Table I of Martin (1996).
%C A159817 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%H A159817 Seiichi Manyama, <a href="/A159817/b159817.txt">Table of n, a(n) for n = 0..1000</a>
%H A159817 Y. Martin, <a href="https://doi.org/10.1090/S0002-9947-96-01743-6">Multiplicative eta-quotients</a>, Trans. Amer. Math. Soc. 348 (1996), no. 12, 4825-4856, see page 4852 Table I.
%H A159817 Michael Somos, <a href="/A030203/a030203.txt">Index to Yves Martin's list of 74 multiplicative eta-quotients and their A-numbers</a>
%H A159817 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A159817 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A159817 Expansion of (f(x) * f(x^5))^2 in powers of x where f() is a Ramanujan theta function.
%F A159817 Expansion of q^(-1/2) * (eta(q^2)^3 * eta(q^10)^3 / (eta(q) * eta(q^4) * eta(q^5) * eta(q^20)))^2 in powers of q.
%F A159817 Euler transform of period 20 sequence [ 2, -4, 2, -2, 4, -4, 2, -2, 2, -8, 2, -2, 2, -4, 4, -2, 2, -4, 2, -4, ...].
%F A159817 a(n) = b(2*n + 1) where b() is multiplicative with b(2^e) = 0^e, b(5^e) = (-1)^e, b(p^e) = b(p) * b(p^(e-1)) - p * b(p^(e-2)) otherwise.
%F A159817 G.f. is a period 1 Fourier series which satisfies f(-1 / (80 t)) = 80 (t/i)^2 f(t) where q = exp(2 Pi i t).
%F A159817 G.f.: (Product_{k>0} (1 - (-x)^k) * (1 - (-x)^(5*k)))^2.
%F A159817 a(n) = (-1)^n * A030205(n). Convolution square of A159818.
%F A159817 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = (1/100) * exp(Pi / 2) * Pi * (5+5^(1/2)) * 5^(1/2) / Gamma(3/4)^4 = A388675. - _Simon Plouffe_, Sep 18 2025
%e A159817 G.f. = 1 + 2*x - x^2 - 2*x^3 + x^4 + 2*x^6 - 2*x^7 - 6*x^8 + 4*x^9 - 4*x^10 + ...
%e A159817 G.f. = q + 2*q^3 - q^5 - 2*q^7 + q^9 + 2*q^13 - 2*q^15 - 6*q^17 + 4*q^19 + ...
%t A159817 a[ n_] := SeriesCoefficient[ (QPochhammer[ -x] QPochhammer[ -x^5])^2, {x, 0, n}]; (* _Michael Somos_, Jun 10 2015 *)
%o A159817 (PARI) {a(n) = if( n<0, 0, ellak( ellinit([0, -1, 0, -1, 0], 1), 2*n + 1))};
%o A159817 (PARI) {a(n) = my(A); if( n<0, 0, A = x * O(x^n); polcoeff( (eta(x^2 + A)^3 * eta(x^10 + A)^3 / (eta(x + A) * eta(x^4 + A) * eta(x^5 + A) * eta(x^20 + A)))^2, n))};
%o A159817 (PARI) {a(n) = my(A, p, e, x, y, a0, a1); if( n<0, 0, n = 2*n + 1; A = factor(n); prod( k=1, matsize(A)[1], [p, e] = A[k, ]; if( p==2, 0, p==5, (-1)^e, a0=1; a1 = y = -sum(x=0, p-1, kronecker(x^3 - x^2 - x, p)); for(i=2, e, x = y*a1 - p*a0; a0=a1; a1=x); a1)))};
%Y A159817 Cf. A030205, A159818.
%K A159817 sign
%O A159817 0,2
%A A159817 _Michael Somos_, Apr 22 2009
```

## Candidate 160: A115633 vs A115713 (score 72.0, agree 120, variant abs, family size 2)
Terms: 1, 1, -1, -4, 0, 1, 0, 0, 1, -1, 0, -4, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, -4, 0, 0, 0, 1, 0, 0

### A115633
```
%I A115633 #12 Sep 22 2025 16:00:48
%S A115633 1,1,-1,-4,0,1,0,0,1,-1,0,-4,0,0,1,0,0,0,0,1,-1,0,0,-4,0,0,0,1,0,0,0,
%T A115633 0,0,0,1,-1,0,0,0,-4,0,0,0,0,1,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,-4,0,0,0,
%U A115633 0,0,1,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,-4,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-4,0,0,0,0,0,0,0,1
%N A115633 A divide and conquer-related triangle: see formula for T(n,k), n >= k >= 0.
%H A115633 G. C. Greubel, <a href="/A115633/b115633.txt">Rows n = 0..50 of the triangle, flattened</a>
%F A115633 T(n, k) = (-1)^n if n = k; else -4 if n = 2k+2; else (n mod 2) if n = k+1; else 0.
%F A115633 G.f.: (1+x-x*y)/(1-x^2*y^2) - 4*x^2/(1-x^2*y).
%F A115633 (1, -x) + (x, x)/2 + (x, -x)/2 - 4(x^2, x^2) expressed in the notation of stretched Riordan arrays.
%F A115633 Column k has g.f.: (-x)^k + (x*(-x)^k + x^(k+1))/2 - 4*x^(2*k+2).
%F A115633 Sum_{k=0..n} T(n, k) = A115634(n).
%F A115633 Sum_{k=0..floor(n/2)} T(n-k, k) = A115635(n).
%e A115633 Triangle begins
%e A115633    1;
%e A115633    1, -1;
%e A115633   -4,  0,  1;
%e A115633    0,  0,  1, -1;
%e A115633    0, -4,  0,  0,  1;
%e A115633    0,  0,  0,  0,  1, -1;
%e A115633    0,  0, -4,  0,  0,  0,  1;
%e A115633    0,  0,  0,  0,  0,  0,  1, -1;
%e A115633    0,  0,  0, -4,  0,  0,  0,  0,  1;
%e A115633    0,  0,  0,  0,  0,  0,  0,  0,  1, -1;
%e A115633    0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  1;
%e A115633    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1, -1;
%e A115633    0,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  0,  1;
%e A115633    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1, -1;
%e A115633    0,  0,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  0,  0,  1;
%e A115633    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1, -1;
%e A115633    0,  0,  0,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  0,  0,  0, 1;
%t A115633 T[n_, k_]:= If[k==n, (-1)^n, If[k==n-1, (1-(-1)^n)/2, If[n==2*k+2, -4, 0]]];
%t A115633 Table[T[n, k], {n,0,18}, {k,0,n}]//Flatten (* _G. C. Greubel_, Nov 23 2021 *)
%o A115633 (SageMath)
%o A115633 def A115633(n,k):
%o A115633     if (k==n): return (-1)^n
%o A115633     elif (k==n-1): return n%2
%o A115633     elif (n==2*k+2): return -4
%o A115633     else: return 0
%o A115633 flatten([[A115633(n,k) for k in (0..n)] for n in (0..18)]) # _G. C. Greubel_, Nov 23 2021
%o A115633 (PARI) A115633(n,k)=if(n==k, (-1)^n, bittest(n,0), k==n-1, k+1==n\2, -4) \\ _M. F. Hasler_, Nov 24 2021
%Y A115633 Cf. A115634 (row sums), A115635 (diagonal sums), A115636 (inverse).
%K A115633 easy,sign,tabl
%O A115633 0,4
%A A115633 _Paul Barry_, Jan 27 2006
```
### A115713
```
%I A115713 #9 Sep 22 2025 16:00:48
%S A115713 1,-1,1,-4,0,1,0,0,-1,1,0,-4,0,0,1,0,0,0,0,-1,1,0,0,-4,0,0,0,1,0,0,0,
%T A115713 0,0,0,-1,1,0,0,0,-4,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,-4,0,0,0,
%U A115713 0,0,1,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,-4,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,-4,0,0,0,0,0,0,0,1
%N A115713 A divide-and-conquer related triangle.
%H A115713 G. C. Greubel, <a href="/A115713/b115713.txt">Rows n = 0..50 of the triangle, flattened</a>
%F A115713 G.f.: (1-x+x*y)/(1-x^2*y^2) - 4*x^2/(1-x^2*y).
%F A115713 (1, x) - (x, x)/2 - (x, -x)/2 - 4*(x^2, x^2) expressed in the notation of stretched Riordan arrays.
%F A115713 Column k has g.f.: x^k - (x*(-x)^k + x^(k+1))/2 - 4*x^(2*k+2).
%F A115713 T(n, k) = if(n=k, 1, 0) OR if(n=2k+2, -4, 0) OR if(n=k+1, -(1+(-1)^k)/2, 0).
%F A115713 Sum_{k=0..n} T(n, k) = A115634(n).
%F A115713 Sum_{k=0..floor(n/2)} T(n-k, k) = A115714(n).
%e A115713 Triangle begins
%e A115713    1;
%e A115713   -1,  1;
%e A115713   -4,  0,  1;
%e A115713    0,  0, -1,  1;
%e A115713    0, -4,  0,  0,  1;
%e A115713    0,  0,  0,  0, -1,  1;
%e A115713    0,  0, -4,  0,  0,  0,  1;
%e A115713    0,  0,  0,  0,  0,  0, -1,  1;
%e A115713    0,  0,  0, -4,  0,  0,  0,  0,  1;
%e A115713    0,  0,  0,  0,  0,  0,  0,  0, -1,  1;
%e A115713    0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  1;
%e A115713    0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  1;
%e A115713    0,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  0,  1;
%e A115713    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, -1,  1;
%e A115713    0,  0,  0,  0,  0,  0, -4,  0,  0,  0,  0,  0,  0,  0,  1;
%p A115713 A115713 := proc(n,k)
%p A115713     coeftayl( (1-x+x*y)/(1-x^2*y^2)-4*x^2/(1-x^2*y),x=0,n) ;
%p A115713     coeftayl( %,y=0,k) ;
%p A115713 end proc: # _R. J. Mathar_, Sep 07 2016
%t A115713 T[n_, k_]:= If[k==n, 1, If[k==n-1, -(1-(-1)^n)/2, If[n==2*k+2, -4, 0]]];
%t A115713 Table[T[n, k], {n,0,18}, {k,0,n}]//Flatten (* _G. C. Greubel_, Nov 23 2021 *)
%o A115713 (SageMath)
%o A115713 def A115713(n,k):
%o A115713     if (k==n): return 1
%o A115713     elif (k==n-1): return -(n%2)
%o A115713     elif (n==2*k+2): return -4
%o A115713     else: return 0
%o A115713 flatten([[A115713(n,k) for k in (0..n)] for n in (0..18)]) # _G. C. Greubel_, Nov 23 2021
%Y A115713 Cf. A115634 (row sums), A115714 (diagonal sums), A115715 (inverse).
%K A115713 easy,sign,tabl
%O A115713 0,4
%A A115713 _Paul Barry_, Jan 29 2006
```

PACKET COMPLETE
