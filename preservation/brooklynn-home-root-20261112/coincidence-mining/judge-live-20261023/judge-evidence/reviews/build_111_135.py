from pathlib import Path
import json

OUT=Path(__file__).parent
metrics={x['rank']:x for x in json.loads((OUT.parent/'agreement.json').read_text())}
checks=json.loads((OUT/'111-135-independent.json').read_text())
rows=[]

def add(rank,gate,agreement,novelty,integrity,sources=()):
    m=metrics[rank]
    rows.append(dict(rank=rank,a=m['a'],b=m['b'],verdict='DROP',primary_gate=gate,
                     agreement=agreement,novelty=novelty,integrity=integrity,
                     metrics=m,independent_check=checks.get(str(rank)),
                     sources=[f"https://oeis.org/{m['a']}",f"https://oeis.org/{m['b']}",*sources]))

add(111,'data integrity',
    'Offsets 0/0; all 127 common listed terms agree at n=0..126. Independent enumeration extends the exact agreement to 1729 terms, n=0..1728, then gives 2 versus 1 at n=1729.',
    'Both records explicitly publish this first disagreement; A373972 also publishes its signum relationship to A025446. This is an already documented finite-prefix coincidence, not an asserted equality.',
    '1729=1^3+12^3=9^3+10^3 has two unordered representations, while the characteristic function is 1. No internal term/formula contradiction was found in the checked definitions.')

add(112,'novelty',
    'Offsets 1/1. The native equality fails immediately at n=1 (0 versus 1); deleting each first term yields 66 common listed matches at n=2..67.',
    'A319371 explicitly conjectures a(n)=A004772(n) for n>1, clarified April 16, 2019. An already published conjecture fails the primary gate even without a proof.',
    'The candidate is an initial-term exception followed by a simple residue-class enumeration. A separate A004772 comment has an arithmetic typo: its displayed m=3*(a(n)+1) gives 3 at n=1, not the displayed 1. This does not rescue novelty.')

add(113,'data integrity',
    'Offsets 1/1; 66 common listed terms agree at n=1..66. Independent greedy constructions agree for 114 terms and first differ at n=115: 120 versus 121.',
    'A360305 explicitly publishes the n=115 disagreement with A249407. Its Cf. link is not being treated as an equality assertion.',
    'The four-leaf product 2*3*4*5=120 is already a tree-node value, so A360305 cannot later use it as a leaf. The pair-product sieve A249407 can. This is truncation, not an identity.')

add(114,'data integrity',
    'Offsets 1/1. Raw terms agree at n=1..127 (127 terms); the packet drop2 view retains only n=3..127 (125 matches). Both live lists already include the failure at n=128: 0 versus 1.',
    'Each record explicitly names this first disagreement with the other. No equality is asserted.',
    '128=2^7: exponent 7 is not a power of two, but has binary weight 3, which is odd. Independent factorization checks confirm the first failure. Deleting two initial terms does not remove it.')

add(115,'data integrity',
    'Offsets 0/0; the shared listed window contains 108 matches, n=0..107. Independent concatenation enumeration gives only 110 initial matches, n=0..109; the first failure is n=110: 10 versus 0.',
    'A347470 already discusses its finite agreement with A035930 and gives a disagreement example at n=112 (22 versus 12). There is no novel all-n equality.',
    'The A347470 comment claiming agreement for n<111 is itself false. At 110 the legal splits 1|10 and 11|0 have products 10 and 0; zero is expressly allowed as a whole number. Its listed a(110)=0 is correct, while A035930’s defining maximum gives 10. Thus the published n=112 example is not the first failure.')

add(116,'novelty',
    'Offsets 1/1; absolute values agree for all 108 common listed terms. Signed equality lasts six terms, failing at n=7: -1 versus +1.',
    'A087003’s February 19, 2004 comments explicitly assert the absolute-value identity and explain it; A091069 independently states and derives the same identity. This is much stronger evidence than a cross-reference.',
    'Both absolute values are the indicator of odd squarefree integers, a prohibited abs transform. Also A087003’s published prime-power formula (-1+(-1)^e)/2 for odd primes is wrong for odd e>1: at 3^3=27 it gives -1 although its name and listed term give 0. The correct local values are -1 at e=1 and 0 at e>1.')

add(117,'data integrity',
    'Offsets 1/1; 108 matches at n=1..108, followed by a mismatch already in both live lists: n=109 gives 170 versus 169.',
    'Both records explicitly document the difference, including the missing value 169. No equality is asserted.',
    '169=13^2 is allowed by A240370 because 13=1 mod 4; it is excluded by A193304, which permits repeated prime factors only for 5. Independent definition-based enumeration confirms the first failure.')

add(118,'data integrity',
    'Offsets 0/0; all 74 common listed terms agree at n=0..73. A346663 publishes agreement through n=2435 (2436 terms), then 2436 versus 2434 at n=2436.',
    'The longer agreement and its failure are explicitly published in A346663, which cites Clark–Shattuck (2021). No all-n equality is asserted.',
    'Independently, for P(x)=sum_{k=0}^{2436} prime(k+1)*x^k, exact integer Horner arithmetic gives P(-4983/5000)<0, while P(0)=2 and P(-1)=10790. Hence P has at least two real roots and cannot have 2436 nonreal roots. This independently refutes the identity; the exact count 2434 and first-failure claim are sourced to the OEIS record, not claimed to be proved by this sign test.',
    ['https://arxiv.org/abs/2107.05572'])

add(119,'data integrity',
    'Offsets 1/1; 107 common listed terms agree. Exact integer heap enumeration extends agreement to n=1..113, then gives 11 versus 0 at n=114.',
    'Both records explicitly state that the pair differs at a(114). This published counterexample rules out the candidate.',
    'The two orderings of multiplicative semigroups only share an initial exponent pattern. The independent calculation uses integer products, avoiding floating-point logarithm-ordering artifacts.')

add(120,'novelty',
    'Offsets 0/0; the first native terms differ, 0 versus 1 at n=0. After deleting both first terms, all 107 common entries agree at n=1..107.',
    'A089013 explicitly states A038189(n)=a(n) for n>0. Its recurrence also immediately reduces to the same binary-bit rule.',
    'This is a published equality with one changed initial value. The checked recurrences agree with the terms; the packet’s drop1 view suppresses the sole initial exception.')

add(121,'interestingness',
    'Offsets 1/1; 107 absolute-value matches at n=1..107. Signed equality fails immediately: 1 versus -1 at n=1.',
    'No explicit pairwise equality was found in either record. Both records already publish their complete period-8 blocks, however; their absolute values are the same elementary period-4 block. No broader novelty claim is needed for this rejection.',
    'The only coincidence is abs([1,-1,0,-1,-1,1,0,1])=abs([-1,-1,0,-1,1,1,0,1]), repeating. This is both a forbidden absolute-value transform and a short-period pattern. A118828’s first generating function is normalized to the first listed term; its later formula explicitly extends the indexing with a(0)=1. These conventions should not be mistaken for a new identity.')

add(122,'data integrity',
    'Offsets 1/1; 107 matches at n=1..107, then both live lists explicitly diverge at n=108: 35 versus 70.',
    'A389087 explicitly identifies the first difference from A344696 at n=108. No equality is asserted.',
    'At 108, sigma=280, Dedekind psi=216, and the sum of squarefree divisors is 12. Thus the respective numerators are 280/gcd(280,216)=35 and 280/gcd(280,12)=70. The definitions and listed mismatch are consistent.')

add(123,'data integrity',
    'Offsets 0/1. Same-index equality has zero initial matches: A007094(1)=1 while A039155(1)=0. Even after correcting the positional alignment to A007094(n)=A039155(n+1), there are only 64 matches, n=0..63; A007094(64)=100 but A039155(65)=89.',
    'Neither record asserts the proposed equality. This absence is not evidence of novelty: the candidate is directly false in its live listed data.',
    'Before 89, eligible decimal numbers have no 8 or 9 and imitate octal digit strings. The value 89 introduces one of each digit and is allowed by A039155, but cannot be an octal digit string. Independent enumeration reproduces the mismatch.')

add(124,'data integrity',
    'Offsets 1/1; 64 common listed matches. Independent enumeration agrees for 1079 terms and first differs at n=1080: 2205 versus 2207.',
    'A348741 explicitly publishes this first difference and identifies itself as A088828 with A348743 removed. This is not an assertion of equality.',
    '2205 is an odd nonsquare, but sigma(2205)=4446 has odd part 2223>2205, so it fails A348741’s defining inequality. The independently computed first failure agrees with the record.')

add(125,'novelty',
    'Offsets 3/0; literal same-index comparison fails at n=3 (3 versus 6). The packet drops two terms from each positional list, giving 64 matches A213222(n+3)=A265283(n), n=2..65.',
    'A265283 explicitly conjectures a(n)=A213222(n+3) for n>1 (Colin Barker, 2015/2019). That precise shifted claim is already published.',
    'Both tails are elementary repeated even numbers. The boundary exception is real: A213222(3)=3, while its listed Magma code incorrectly uses 2*floor(3/2)=2 at n=3. The main formula correctly restricts that expression to n>3.')

add(126,'data integrity',
    'Offsets 0/0; 106 common listed matches. Independent mixed-radix evaluation agrees for n=0..209 (210 terms), then gives 7 versus 1 at n=210.',
    'Both records explicitly publish this first disagreement.',
    'The initial division radices coincide at 2,3,5, but the next Fibonacci radix is 8 and the next prime radix is 7. At 210, successive quotients leave a final nonzero 7 in the former system and 1 in the latter. The long common prefix comes from the shared initial radices.')

add(127,'data integrity',
    'Offsets 0/0; 106 common listed matches. Independent mixed-radix calculations agree for n=0..1889 (1890 terms) and first differ at n=1890: 9 versus 1.',
    'A341513 explicitly explains this agreement range and first failure relative to A276150.',
    'The place values first separate after 210: the odd-number-radix system next uses 1890=210*9, while the primorial system next uses 2310=210*11. Consequently 1890 has digit sum 1 versus 9. No all-n equality exists.')

add(128,'data integrity',
    'Offsets 0/0; 106 common listed matches. The freshly fetched b-files agree for n=0..510 (511 terms) and first differ at n=511: 171 versus 170.',
    'A332996 explicitly publishes that first disagreement with A292592. Its Cf. links are not treated as equality evidence.',
    'The published long-prefix claim was checked directly against both full b-files, not merely inferred from the short S/T/U lists. The b-file comparison is a stronger data check, not an independent proof of their underlying definitions.',
    ['https://oeis.org/A292592/b292592.txt','https://oeis.org/A332996/b332996.txt'])

add(129,'data integrity',
    'Offsets 0/0; 106 common listed matches. Independent definition-based calculations agree for n=0..359 (360 terms) and first differ at n=360: 1 versus 3.',
    'A371091 explicitly records this first failure relative to A328482 and gives its recursive decomposition at 360.',
    '360=2*6*30 is itself a product of distinct primorials, so its greedy representation uses one distinct term. Its ordinary primorial expansion is 15000; recursively expanding digit 5 yields two ones in addition to the leading one, for a total of three.')

add(130,'novelty',
    'Offsets 0/0; equality fails at n=0 (2 versus 0). Deleting both first terms produces 73 common listed matches at n=1..73.',
    'A275365 explicitly states that it is A133265 with its initial 2 replaced by 0. This exact exception-handled identity is already published.',
    'Two internal contradictions also require flags: A275365’s printed generating function has constant coefficient 2, contradicting a(0)=0; A133265’s Maple expression (n+2+(n-2)*(-1)^n)/2 gives 0 at n=0 and 2 at n=3, contradicting listed 2 and 4. The correct main formulas and data still describe an elementary interleaving, so none of these errors creates a survivor.')

add(131,'data integrity',
    'Offsets 1/1; 105 common listed matches. Comparing an independent divisor-formula implementation with the freshly fetched A171774 b-file verifies agreement for n=1..299, then 1 versus 0 at n=300.',
    'A171774 explicitly publishes that first disagreement with A002324. It does not assert their equality.',
    'For 300=2^2*3*5^2, the multiplicative divisor-difference formula gives A002324(300)=1; the radix-expansion b-file has 0. The 299-term match is a finite-prefix artifact. The radix b-file was checked as data; no independent transcendental-digit proof is claimed.',
    ['https://oeis.org/A171774/b171774.txt'])

add(132,'novelty',
    'Offsets 1/1; all 105 common listed terms agree at n=1..105.',
    'A004258’s name explicitly declares it a duplicate of A029837 and its keyword is dead. The identity is not a discovery.',
    'A029837’s correct defining function is ceiling(log_2(n)), but its printed recurrence a(2n+1)=a(n)+1 for n>1 is false: n=2 predicts a(5)=2, whereas the listed value and definition give 3. Its alternative recurrence using ceiling(n/2) is correct. A further displayed characterization n^(1/k-1)>2 is impossible for n>=1,k>=1. These are record errors, not grounds to retain a duplicate.')

add(133,'novelty',
    'Offsets 1/0; the 105 positional digit matches mean A010476(n)=A020762(n-1), n=1..105. Same-index comparison matches only n=1, then fails at n=2 (4 versus 7).',
    'A010476 explicitly states equivalence except for offset, and A020762 explicitly gives its constant as A010476/10 (January 14, 2021).',
    'sqrt(20)=10/sqrt(5), so these are the same digits with the decimal point shifted. This also fails interestingness as a trivial scale/offset relation. Correcting offsets does not produce a new constant identity.')

add(134,'data integrity',
    'Offsets 1/1; all 105 common listed terms match. Exact integer heap enumeration agrees for n=1..2804 and first differs at n=2805: 0 versus 65.',
    'Both records explicitly publish the disagreement at a(2805) and link the index of sequences with long but finite agreement.',
    'The ordering of 4^i*6^j and 5^i*8^j eventually selects different exponents j. The counterexample was reproduced with exact products and ordering, without floating-point approximations.')

add(135,'interestingness',
    'Offsets 0/0; absolute values agree throughout all 105 common listed terms. Signed equality lasts two terms and fails at n=2: 1 versus -1.',
    'No explicit pairwise equality was found in either record. Both complete period-8 formulas are already given, determining their shared absolute-value pattern; no claim of an unpublished identity is warranted.',
    'Their absolute values are simply the period-4 block [0,1,1,1]. The relation is also A075553(n)=(-1)^(n+1)*A046978(n). This is a sign/abs transform of short-period sequences, expressly excluded by gate 2. The checked periodic formulas agree with the data.')

assert len(rows)==25 and {r['rank'] for r in rows}==set(range(111,136))
(OUT/'111-135.json').write_text(json.dumps(rows,indent=2)+'\n')
sections=[]
for r in rows:
    citations=' '.join(f'[{url.removeprefix("https://oeis.org/")} ]({url})'.replace(' ]',']') for url in r['sources'])
    sections.append(f"## Candidate {r['rank']}: {r['a']} vs {r['b']} — DROP ({r['primary_gate']})\n\n"
                    f"**Agreement and offsets.** {r['agreement']}\n\n"
                    f"**Novelty.** {r['novelty']}\n\n"
                    f"**Integrity and other gates.** {r['integrity']}\n\n"
                    f"Sources: {citations}\n")
(OUT/'111-135.md').write_text('\n'.join(sections))
print('Wrote 25 DROP reviews: 16 data integrity, 7 novelty, 2 interestingness.')
