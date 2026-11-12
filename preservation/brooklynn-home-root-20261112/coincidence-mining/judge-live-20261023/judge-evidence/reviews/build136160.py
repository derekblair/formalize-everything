from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent.parent
metrics={x['rank']:x for x in json.loads((ROOT/'agreement.json').read_text())}
verified=json.loads((ROOT/'reviews'/'verification-136-160.json').read_text())

data={
136:dict(gate='Data integrity',
 novelty='The A327503 comment explicitly says this pair first differs at 216; its mention of A052409 is a published nonidentity, not an equality claim.',
 reason='The 105 displayed common terms conceal a finite-prefix coincidence. Independent factorization/divisor iteration verifies exactly 215 common terms, n=1..215, then A052409(216)=3 and A327503(216)=2.',
 integrity='216=6^3, so its largest perfect-power exponent is 3. The quotient iteration instead gives 216→2→1, since 108 is the largest divisor of 216 that is not a perfect power. No contradiction between these definitions and their own lists; the proposed infinite identity is false.'),
137:dict(gate='Interestingness',
 novelty='No direct equality between these two IDs is asserted in the inspected records. A069158 explicitly gives |a(n)|=|mu(n)|; A359155 publishes a(n)=mu(n)·A359154(n), with A359154 taking only ±1. These already explain the shared squarefree support.',
 reason='The proposed equality is merely equality after erasing signs: both absolute values are the indicator of squarefree integers. The original sequences disagree at n=3: −1 versus 1.',
 integrity='The multiplicative prime-power formula for A359155 gives magnitude 1 on squarefree integers and 0 otherwise. It is consistent with the displayed values; no offset issue.'),
138:dict(gate='Novelty',
 novelty='A081602 explicitly states “Duplicate of A077267” and has keyword dead. Both definitions count zero digits in ternary notation.',
 reason='An explicitly identified duplicate cannot be an unpublished identity.',
 integrity='Both offsets are 0. Their first 105 displayed values agree at n=0..104, including the convention a(0)=1. A077267 contains one further displayed value; there is no comparison beyond the shorter list.'),
139:dict(gate='Novelty',
 novelty='Both records explicitly state that A030204, A083650 and A138514 are the same except for signs (Sloane, May 7, 2010).',
 reason='The precise absolute-value relationship being mined has already been asserted on both records; it also fails the ban on trivial sign changes.',
 integrity='Both offsets are 0; absolute values agree for all 105 displayed positions. Raw values first differ at n=1: −1 versus 1. No additional contradiction was identified in the formulas used for this verdict.'),
140:dict(gate='Novelty',
 novelty='Both records publish the exact relation A093829(n)=−(−1)^n·A113447(n), dated January 31, 2015.',
 reason='The absolute-value match is a published parity sign change.',
 integrity='Both offsets are 1; 105 displayed absolute values match. Raw values first differ at n=2: −1 versus 1. There is also a nonessential numerical error in A113447: its asymptotic-mean line equates Pi/(6·sqrt(3)) to 0.604599..., whereas that expression is 0.302299...; this does not rescue novelty.'),
141:dict(gate='Interestingness',
 novelty='Neither record asserts a pairwise equality. A099443 publishes a(n+5)=−a(n), and A132342 explicitly states that it becomes period 5 at a(13). These published descriptions expose the elementary periodic pattern.',
 reason='After respecting offsets, the mined statement is |A099443(n)|=|A132342(n+1)|. Both magnitudes repeat 1,1,1,1,0. This is an offset shift plus sign erasure of short-period sequences.',
 integrity='Offsets are 0 and 1. The 105-position agreement compares A099443(0..104) with A132342(1..105), not equal indices. At equal indices only n=1..3 match before n=4 gives 0 versus 1; even their absolute values differ there. No contradiction with either recurrence is needed.'),
142:dict(gate='Novelty',
 novelty='A101875 is named “Duplicate of A101871” and has keyword dead. A101871 explicitly gives a(n)=A000688(2n+1)=A000688(4n+2).',
 reason='The former definitions—Abelian groups of odd order 2n+1 and of order 4n+2—are already equated in the surviving record.',
 integrity='Offsets are both 0 and all 105 common displayed terms agree at n=0..104. The extra prime factor 2 has exponent 1 and contributes only the unique group of order 2, consistent with the equality.'),
143:dict(gate='Data integrity',
 novelty='Both records explicitly publish the failure of the shifted equality at A103391(192)=97 versus A331743(191)=23. This is affirmative evidence against the proposed identity, not a mere cross-reference.',
 reason='The packet suppresses an offset difference and then stops before a known counterexample. Independent computation from the restricted-growth definition verifies exactly 191 shifted common terms: A103391(n+1)=A331743(n) for n=0..190, then failure at n=191.',
 integrity='Offsets are 1 and 0. At equal indices there are zero common initial terms: A103391(1)=1 but A331743(1)=2. The advertised 105 terms compare A103391(1..105) with A331743(0..104). Computation of A331743 additionally used the freshly fetched A323901 code for A002487(A163511(n)).'),
144:dict(gate='Interestingness',
 novelty='No direct pairwise identity is asserted in the two inspected records. A106459 explicitly gives |a(n)|=A010054(n), the triangular-number indicator; A143433 publishes a sum with one ±1 coefficient at each exponent k(k+1)/2.',
 reason='Erasing signs leaves the same elementary triangular-number support. This follows immediately from the displayed sparse series and is a trivial absolute-value transform under the stated gate.',
 integrity='Offsets are both 0. All 105 displayed absolute values match; raw values first differ at n=3: −1 versus 1. Distinct triangular exponents prevent hidden cancellation in the displayed series.'),
145:dict(gate='Novelty',
 novelty='A163804 explicitly states a(n)=−A106510(n) for n>0, both in a formula and in the cross-references.',
 reason='This is an already-published sign reversal, with a common exceptional initial value. Both tails have period 3.',
 integrity='Offsets are both 0. Absolute values match for 105 displayed terms. At n=0 both equal 1; raw values first differ at n=1: 1 versus −1. The two rational generating functions sum to 2, confirming the stated exception and tail sign reversal.'),
146:dict(gate='Interestingness',
 novelty='The cross-references list quadratic characters; they do not assert equality. The definitions already imply that the two absolute values are 1 exactly when gcd(n,6)=1, and 0 otherwise.',
 reason='The mined absolute-value sequence is the period-6 pattern 0,1,0,0,0,1. Both original characters have short periods (24 and 12). This fails the explicit short-period and sign-erasure exclusions.',
 integrity='Offsets are both 0. All 105 displayed absolute values match, while raw values first differ at n=5: 1 versus −1. The common zero set is consistent with the Kronecker/Dirichlet-character definitions.'),
147:dict(gate='Novelty',
 novelty='A121450 explicitly states “Apart from signs, same as A035154 and A113446.” It also gives A035154(n)=|a(n)|; A113446 publishes its sign relation to A035154.',
 reason='The exact absolute-value equality has already been asserted. The prime-power formulas show that the records differ only by a parity sign.',
 integrity='Offsets are both 1. There are 105 common displayed absolute values. Raw values first differ at n=2: 1 versus −1. No inconsistency was found in the compared terms or prime-power rules.'),
148:dict(gate='Interestingness',
 novelty='Neither inspected record expressly states an equality to the other ID. Each publishes its full multiplicative prime-power rule, which makes the relationship an immediate sign-only change at the prime 2.',
 reason='Writing n=2^e·m with m odd, the formulas give A113974(n)=(−1)^e·A113661(n). For e>0, A113661 has 2-power factor (1−3(−1)^e)/2 and A113974 has ((−1)^e−3)/2; all odd-prime factors coincide. This is a trivial valuation-dependent sign change.',
 integrity='Offsets are both 1. All 105 displayed absolute values agree; raw values first differ at n=2: 2 versus −2. The e=0 case uses a(1)=1, as appropriate for multiplicative functions, rather than applying a prime-power rule outside its positive-exponent domain.'),
149:dict(gate='Novelty',
 novelty='A121373 publishes a(n)=(−1)^n·A010815(n). A199918 explicitly publishes |a(n)|=|A010815(n)|. Thus the mined equality of absolute values is already asserted through the same named sequence.',
 reason='Both are sign decorations of Euler-pentagonal support; the common absolute-value identity is published, not a new target.',
 integrity='Offsets are both 0; 105 displayed absolute values match, but raw values first differ at n=2: −1 versus 1. Important internal contradictions in A199918: its bilateral sum over all integers k of x^((k²−1)/24)·Kronecker(−24,k) has constant coefficient 1+(−1)=0 from k=±1, whereas a(0)=1. Also its negative prime-residue list contains 29 mod 24, overlapping the positive class 5 and omitting 19; at n=35, 24n+1=29², that negative branch gives −1 while the list and executable formula give +1. These are formula errors, not evidence against the separately published absolute-value relation.'),
150:dict(gate='Interestingness',
 novelty='No direct pairwise equality is asserted in the two inspected records. A143064 explicitly identifies its absolute values with A089801; both records give executable square tests, so the same simple support is already explicit in their formulas.',
 reason='Both sequences vanish unless 3n+1=m², and otherwise equal ±1: A143064 uses (−1)^floor(m/3), while A185124 uses (−1)^floor((m+3)/6). Their absolute-value match discards only these signs.',
 integrity='Offsets are both 0. All 105 displayed absolute values match, with the first raw difference at n=16: 1 versus −1. A143064 has a literal formula/list contradiction: its first displayed sum has product over j=0..k of (1+x^(2k+1)); the k=0 and k=2 terms each contribute 1 to x², yielding a(1)=2 instead of the listed 1. The later QPochhammer code instead uses the running odd exponents 2j+1. This typo must not be silently treated as a verified formula.'),
151:dict(gate='Novelty',
 novelty='A143259 explicitly states |a(n)|=A053866(n). A359818 identifies A053866 as its “parity and the absolute values,” which is a qualified equality assertion, stronger than an unqualified Cf.',
 reason='The common absolute values are explicitly assigned to the same sequence; they indicate squares or twice squares. The remaining difference is a prime-factor-dependent sign.',
 integrity='Offsets are both 1. All 105 displayed absolute values match. Raw equality stops after n=8, with n=9 giving 1 versus −1. A359818 has magnitudes 1 exactly when every odd-prime exponent is even, consistent with square-or-twice-square support.'),
152:dict(gate='Novelty',
 novelty='A156277 explicitly diagrams A156277 --abs--> A359377 and labels A359377 “absolute values.” A365428 likewise labels A359377 “absolute values.” These are explicit common-target assertions, not generic cross-references.',
 reason='Both absolute-value sequences are the squarefree indicator with multiples of 3 excluded, already identified as A359377.',
 integrity='Offsets are both 1; 105 displayed absolute values match. Raw values first differ at n=2: −1 versus 1. The formulas −mu(3n) and the inverse-character prime-power rules agree with this support; the Legendre notation in the latter is interpreted with the character’s stated value at 2, confirmed by the listed terms.'),
153:dict(gate='Novelty',
 novelty='Both records explicitly publish a(n)=(−1)^n times the other sequence.',
 reason='The absolute-value match is an already-known alternating sign change. The tails also have periods 10 and 5.',
 integrity='Offsets are both 0. All 105 displayed absolute values agree; raw values first differ at n=1: 1 versus −1. Their rational generating functions are related by x→−x, consistent with the listed relation.'),
154:dict(gate='Novelty',
 novelty='A164116 explicitly gives a(n)=(−1)^n·A164118(n); A164118 repeats the same relation in its cross-references.',
 reason='A published alternating sign transform of an eventually period-5 sequence fails novelty and interestingness.',
 integrity='Offsets are both 0; 105 displayed absolute values agree. Raw values first differ at n=1: −1 versus 1. The generating functions are related by substituting −x, including the exceptional initial term in the periodic descriptions.'),
155:dict(gate='Novelty',
 novelty='A223139 expressly states that apart from a(1) it is the same as A209927, and gives its constant as A209927−1. It also states that replacing its first digit by 2 yields A209927.',
 reason='The constants (sqrt(13)+1)/2 and (sqrt(13)−1)/2 differ by the integer 1, so their decimal fractional digits coincide. This is an explicitly published initial-digit deletion.',
 integrity='Both offsets are 1. The raw sequences disagree immediately: integer digits 2 and 1. Deleting the first term from both gives 105 matched digits at indices 2..106; this is not a shift of one sequence alone.'),
156:dict(gate='Data integrity',
 novelty='A290110 explicitly states that it differs from A300250 for the first time at n=858, with values 115 and 75. A300250 repeats the first-disagreement claim. Neither asserts an infinite equality.',
 reason='Independent enumeration of divisor factorization patterns versus divisor prime-signature patterns confirms exactly 857 matched terms, n=1..857, then 115 versus 75 at n=858.',
 integrity='Both offsets are 1; the displayed 105 terms are correct but truncated before failure. The full factorization pattern remembers which prime symbols appear in each divisor; the prime-signature pattern forgets those identities. The two definitions are genuinely different, consistently with their records.'),
157:dict(gate='Data integrity',
 novelty='A334868 gives only a one-way implication between the equivalence relations defined by these sequences. That statement is not an equality claim; the generic Cf. is not novelty evidence either.',
 reason='The advertised prefix already ends at a counterexample inside the two displayed lists: exactly 63 terms agree, then A305979(64)=42 and A334868(64)=6. Independent implementation reproduces this failure.',
 integrity='Both offsets are 1. A334870(12)=8=A334870(64), so the restricted-growth transform reuses the label 6 at 64. A305979 assigns successive new labels to each number outside the Fermi-Dirac primes, hence 42. There is no infinite identity.'),
158:dict(gate='Data integrity',
 novelty='Both records explicitly state their first disagreement at n=121: A351454(121)=51, A351460(121)=62.',
 reason='Independent restricted-growth computations using the published auxiliary triples confirm exactly 120 common terms, n=1..120, and the published failure at 121.',
 integrity='Offsets are both 1. The packet’s 105 displayed values hide this near-future failure. A351454 merges 99 and 121 because their largest prime factor and both iteration counts agree; A351460 distinguishes the corresponding odd squarefree-divisor sum and odd excess-power data. No formula/list inconsistency is needed: the identity itself is false.'),
159:dict(gate='Novelty',
 novelty='A030205 explicitly publishes a(n)=(−1)^n·A159817(n), dated June 10, 2015; A159817 publishes the reciprocal relation.',
 reason='The absolute-value relationship between the two modular-form coefficient lists is a known parity twist, not a new identity.',
 integrity='Offsets are both 0. The shorter A030205 list permits 72 absolute-value comparisons, n=0..71, all matching. Raw values first differ at n=1: −2 versus 2. The published product generating functions are directly related by x→−x.'),
160:dict(gate='Interestingness',
 novelty='Neither inspected record explicitly names the other as an equal sequence. Their published triangle formulas, however, immediately give T115713(r,k)=(−1)^r·T115633(r,k). The shared row-sum reference alone is not used as an equality claim.',
 reason='This is simply an alternating row-sign change. The −4 entries occur only in even rows, diagonal signs are reversed in odd rows, and the odd-row subdiagonal changes from +1 to −1.',
 integrity='Offsets are both 0. Flattening rows 0..14 gives all 120 advertised absolute-value matches. The original flattened values disagree already at index 1: 1 versus −1. The bivariate generating functions are related by x→−x, verifying the sign relation for the entire triangles.'),
}

rows=[]
sections=[]
manifest={x['id']:x for x in json.loads((ROOT/'retrieval-manifest.json').read_text()) if 'id' in x}
for rank,d in data.items():
    m=metrics[rank]
    a,b=m['a'],m['b']
    assert manifest[a]['valid'] and manifest[b]['valid']
    assert manifest[a]['staged_equal'] and manifest[b]['staged_equal']
    p=m['packet_variant']; native=m['native']
    mode='absolute values' if p['absolute'] else 'raw values'
    agreement=f"Offsets: {a} starts at {m['offset_a']}, {b} at {m['offset_b']}. The packet transformation gives {p['count']} matched {mode} from ({a} index {p['a_start']}, {b} index {p['b_start']})"
    if p.get('censored_by_listing'):agreement+='; the shorter displayed list ends there.'
    else:agreement+=f"; the next values are {p['mismatch']['a']} and {p['mismatch']['b']}."
    row={'rank':rank,'a':a,'b':b,'verdict':'DROP','gate':d['gate'],'agreement':agreement,'metrics':m,**{k:v for k,v in d.items() if k!='gate'},'live_verified':True,'sources':[f'https://oeis.org/{a}',f'https://oeis.org/{b}']}
    if str(rank) in verified:row['independent_verification']=verified[str(rank)]
    if rank==143:row['sources'].append('https://oeis.org/A323901')
    rows.append(row)
    links=', '.join(f'[{u.rsplit("/",1)[-1]}]({u})' for u in row['sources'])
    sections.append(f"## Candidate {rank}: {a} vs {b} — DROP ({d['gate'].lower()})\n\n"
                    f"**Agreement.** {agreement}\n\n"
                    f"**Novelty.** {d['novelty']}\n\n"
                    f"**Decision and integrity.** {d['reason']} {d['integrity']}\n\n"
                    f"Sources: {links}.\n")
(ROOT/'reviews'/'136-160.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(ROOT/'reviews'/'136-160.md').write_text('\n'.join(sections))
print('Wrote 25 DROP reviews: 13 novelty, 7 interestingness, 5 data integrity; 0 KEEP.')
