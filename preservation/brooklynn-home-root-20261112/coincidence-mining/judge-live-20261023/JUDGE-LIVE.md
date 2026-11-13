# Independent judgment: coincidence-mining candidates 61–160

**Result: 0 KEEP; 100 DROP.** All 100 candidates fail at least one required gate. No candidate remains for proof or statement drafting.

| Primary failed gate | Count |
| --- | ---: |
| Data integrity: the proposed identity is false | 64 |
| Novelty: the relevant equality or transformed equality is already published | 26 |
| Interestingness: an excluded elementary sign, absolute-value, or periodic transform | 10 |
| **Total DROP** | **100** |
| **Total KEEP** | **0** |

Counts assign one decisive primary gate per candidate; secondary failures are recorded in the individual sections. A false proposed identity does not necessarily mean either OEIS sequence contains bad data.

## Method and evidence

Reviewed on **2026-10-23 UTC** against the brief's three gates. I independently retrieved all **200 complete records** from the official [OEIS data repository](https://github.com/oeis/oeisdata), using its `seq/Axxx/Axxxxxx.seq` files. Retrieval validation completed at **16:14:44 UTC**. All 200 match their staged counterparts after removing outer whitespace. The complete retrieved records, URLs, timestamps, byte counts, and SHA-256 hashes are retained in [the retrieval manifest](judge-evidence/retrieval-manifest.json) and its adjacent `records/` directory. No input file was changed.

The automated comparison concatenated each record's `%S`, `%T`, and `%U` terms and read the first `%O` component. It reproduced **all 100 advertised agreement lengths**, including the packet's transformations. The agreement metadata were therefore reproduced, but they are not evidence of infinite equality. Full numerical results are in [agreement.json](judge-evidence/agreement.json); the comparison is reproducible with [compare.py](judge-evidence/compare.py).

- **Native-index agreement** compares the original signed values at the same available index. **Positional agreement** compares their first listed terms, then their second listed terms, and so on; different offsets can make these different claims.
- **`drop1` / `drop2`** remove that many entries from **both** lists. They do not shift only one sequence. **`abs`** takes absolute values before positional comparison. Each section preserves the actual indices and exceptions.
- **A displayed-list agreement length is a lower bound when the shorter list ends.** Extended lengths are explicitly attributed to independent calculations, fetched b-files, or a published OEIS claim. A b-file comparison is data verification, not an independent proof of the definition. Where a first counterexample already occurs in `%S/%T/%U`, that is stated.
- For decimal expansions marked **`cons`**, the first offset also records the decimal-point position. Matching digit strings after moving that point or deleting initial digits does not assert equality of the constants. Native-index mismatch in such cases is a bookkeeping observation, not an additional mathematical counterexample.

Novelty checking inspected both complete records, including names, comments, formulas, qualified cross-references, and references. An explicit conjecture is already published and fails the novelty gate. Identical published formulas or explicit identification with the same third sequence also suffice; an unqualified `Cf.` or an implication between equivalence classes does not. Every candidate has a decisive counterexample, a published equivalence, or a prohibited elementary transform, so no candidate required a broader literature search to decide whether to KEEP it. No claim of exhaustive literature coverage is made for rejected pairs.

Finite-prefix counterexamples were independently calculated where practical and otherwise checked against the retrieved lists/b-files; the sections distinguish those evidence types. Reproducible calculations and supplementary-source manifests are saved in [judge-evidence/reviews](judge-evidence/reviews), with the first block's computations in [check_61_85.py](judge-evidence/check_61_85.py) and [computed-61-85.json](judge-evidence/computed-61-85.json). Independent block review and cross-review checked the verdicts and arithmetic.

## Material record errors found

These do not create survivors, but they matter for this programme's integrity gate:

- **Candidate 115:** A347470's claimed agreement for n<111 is false. Direct definitions first diverge at **n=110**, with **10 versus 0**, before its cited n=112 example.
- **Candidate 72:** A279186 publishes the exact same formula as A256608 while retaining a conflicting cross-reference claiming they are different. The published formula already defeats novelty.
- **Candidates 62, 116, 125, 130, 132, 149, and 150:** literal formulas or programs contradict listed terms or initial values; explicit witnesses appear below. In particular, A199918's bilateral sum gives constant coefficient 0 instead of 1, and A143064's mistyped product gives a(1)=2 instead of 1.
- Further malformed formulas, examples, comments, or code are flagged in **67, 78, 86, 91, 97, 104, 109, 112, and 140**. None was silently accepted as authority for an identity.

## Candidate 61: A353812 vs A353813

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A353812=1, A353813=1; displayed lengths 125 and 125. At equal native indices, the initial agreement is 125 terms (n=1..125); this count is limited by the shorter displayed list.

**Evidence.** The two records already publish their first difference at n=325. Independent factorization checks reproduce agreement for n=1..324 (324 terms), then A353812(325)=1 and A353813(325)=0: sigma(325)=434 is 2 mod 4, whereas 325=5^2*13 has three 1-mod-4 prime factors with multiplicity.

**Novelty and integrity.** Novelty check: both %Y fields explicitly document this near-coincidence and counterexample; neither asserts equality. The 125-term listing is truncated before the known failure. No self-formula/list conflict was found in this check.

Sources: [A353812](https://oeis.org/A353812), [A353813](https://oeis.org/A353813); freshly retrieved [first record](judge-evidence/records/A353812.seq) and [second record](judge-evidence/records/A353813.seq).

## Candidate 62: A118822 vs A230075

**DROP — interestingness.**

**Agreement and offsets.** Offsets: A118822=1, A230075=0; displayed lengths 108 and 110. At equal native indices, the initial agreement is 0 terms; the next comparison at n=1 is 2 versus 1. Packet `abs` agreement: 108 terms, comparing indices 1..108 and 0..107 after taking absolute values.

**Evidence.** Both records explicitly give period-8 sequences. The proposed 108-term agreement is |A118822(n+1)|=|A230075(n)|, a sign-and-offset transform of the period-4 pattern 2,1,0,1. Signed same-index equality fails immediately.

**Novelty and integrity.** Novelty check: the complete periodic patterns and closed formulas are already published; no substantive new identity remains after absolute values. Integrity flag: A230075's literal product of 2*cos((2*l+1)*Pi/2) predicts 0 at n=3, contradicting its listed a(3)=1 and its correct rational generating function.

Sources: [A118822](https://oeis.org/A118822), [A230075](https://oeis.org/A230075); freshly retrieved [first record](judge-evidence/records/A118822.seq) and [second record](judge-evidence/records/A230075.seq).

## Candidate 63: A295884 vs A380397

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A295884=1, A380397=1; displayed lengths 120 and 105. At equal native indices, the initial agreement is 105 terms (n=1..105); this count is limited by the shorter displayed list. Packet `drop1` agreement: 104 terms, comparing indices 2..105 and 2..105.

**Evidence.** A380397 %C already says the first difference is n=128. Independent divisor counting confirms 127 equal terms n=1..127, then 1 versus 2: A295884 counts the single exponent 7, whereas A380397 counts the nonunitary cube divisors 8 and 64.

**Novelty and integrity.** Novelty check: the record explicitly discusses and rejects the proposed equality. Removing the first term merely reduces the short displayed overlap from 105 to 104; it cannot remove the n=128 counterexample.

Sources: [A295884](https://oeis.org/A295884), [A380397](https://oeis.org/A380397); freshly retrieved [first record](judge-evidence/records/A295884.seq) and [second record](judge-evidence/records/A380397.seq).

## Candidate 64: A036453 vs A040000

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A036453=1, A040000=0; displayed lengths 105 and 105. At equal native indices, the initial agreement is 0 terms; the next comparison at n=1 is 1 versus 2. Packet `drop2` agreement: 103 terms, comparing indices 3..105 and 2..104.

**Evidence.** The offsets are 1 and 0. Aligning the two displayed strings compares A036453(n) with A040000(n-1), not equal native indices. Independently iterating the divisor-count function gives 5039 matching shifted terms n=1..5039, then A036453(5040)=3 while A040000(5039)=2. The iteration is 5040→60→12→6→4→3.

**Novelty and integrity.** Novelty check: A036453 %C already states the first non-2 value after the initial term occurs at 5040; A040000 %N states its entire constant tail. Interestingness also fails: the mined overlap is a run of 2s. No formula/list discrepancy is needed to reject this truncation artifact.

Sources: [A036453](https://oeis.org/A036453), [A040000](https://oeis.org/A040000); freshly retrieved [first record](judge-evidence/records/A036453.seq) and [second record](judge-evidence/records/A040000.seq).

## Candidate 65: A323152 vs A323153

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A323152=1, A323153=1; displayed lengths 120 and 120. At equal native indices, the initial agreement is 0 terms; the next comparison at n=1 is 1 versus 0. Packet `drop1` agreement: 118 terms, comparing indices 2..119 and 2..119.

**Evidence.** The sequences already differ at n=1 (1 versus 0). After dropping that term, the agreement is exactly 118 terms n=2..119; both displayed lists and an independent proper-divisor calculation give 1 versus 0 at n=120. Here sigma(120)=360 is divisible by every proper divisor, but 120 is neither prime nor perfect.

**Novelty and integrity.** Novelty check: both %C fields explicitly list disagreements at 1,120,672,... . This was already published as a nonidentity; no internal formula/list inconsistency was found.

Sources: [A323152](https://oeis.org/A323152), [A323153](https://oeis.org/A323153); freshly retrieved [first record](judge-evidence/records/A323152.seq) and [second record](judge-evidence/records/A323153.seq).

## Candidate 66: A061486 vs A264600

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A061486=0, A264600=0; displayed lengths 102 and 102. At equal native indices, the initial agreement is 101 terms (n=0..100); the next comparison at n=101 is 3 versus 12.

**Evidence.** Exactly 101 terms agree, n=0..100; the next displayed term is 3 versus 12 at n=101. Independent evaluation gives product(digit+1)-1=2*1*2-1=3, while the published reverse-order recurrence gives A264600(101)=A264600(10)+11=12.

**Novelty and integrity.** Novelty check: A061486 %C explicitly gives this counterexample and A264600 %Y points to it. The reported agreement ends at an actual mismatch already included in both records, not at evidence of an identity.

Sources: [A061486](https://oeis.org/A061486), [A264600](https://oeis.org/A264600); freshly retrieved [first record](judge-evidence/records/A061486.seq) and [second record](judge-evidence/records/A264600.seq).

## Candidate 67: A132272 vs A179051

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A132272=0, A179051=0; displayed lengths 100 and 100. At equal native indices, the initial agreement is 100 terms (n=0..99); this count is limited by the shorter displayed list. Packet `drop1` agreement: 99 terms, comparing indices 1..99 and 1..99.

**Evidence.** The unmodified lists agree in 100 positions n=0..99; drop1 reduces this to 99. Independent formulas give A132272(100)=(1+10)(1+1)=22, while partitions of 100 into 1,10,100 number 11+1=12.

**Novelty and integrity.** Novelty check: both records explicitly restrict their equality to n<100. Integrity flag: A132272's displayed upper-bound line equates a power of n with 2^A000217(log_p(n)) despite p=10; that equality of right-hand expressions is wrong (already at n=100). The main product definition, not that malformed bound, supplies the counterexample.

Sources: [A132272](https://oeis.org/A132272), [A179051](https://oeis.org/A179051); freshly retrieved [first record](judge-evidence/records/A132272.seq) and [second record](judge-evidence/records/A179051.seq).

## Candidate 68: A305900 vs A374478

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A305900=1, A374478=1; displayed lengths 98 and 101. At equal native indices, the initial agreement is 94 terms (n=1..94); the next comparison at n=95 is 74 versus 39.

**Evidence.** The agreement is exactly 94 terms n=1..94. The next terms, already displayed, are A305900(95)=74 and A374478(95)=39.

**Novelty and integrity.** Novelty check: A374478 %Y states this exact first difference. Its implication about equal labels is not an assertion that the two label sequences coincide. The records themselves reject the equality; no separate formula/list inconsistency was needed.

Sources: [A305900](https://oeis.org/A305900), [A374478](https://oeis.org/A374478); freshly retrieved [first record](judge-evidence/records/A305900.seq) and [second record](judge-evidence/records/A374478.seq).

## Candidate 69: A323077 vs A334201

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A323077=1, A334201=1; displayed lengths 105 and 105. At equal native indices, the initial agreement is 105 terms (n=1..105); this count is limited by the shorter displayed list.

**Evidence.** Independent iteration and prime-index sums extend the 105 displayed equal terms to exactly 168 terms n=1..168. At 169 the values are 5 versus 6. The first iteration goes 169→156→78→39→26→13, while the remaining Heinz partition part has size pi(13)=6.

**Novelty and integrity.** Novelty check: both %Y fields explicitly give the same first counterexample. The listed prefix is consistent with the definitions but is too short to expose the already-known failure.

Sources: [A323077](https://oeis.org/A323077), [A334201](https://oeis.org/A334201); freshly retrieved [first record](judge-evidence/records/A323077.seq) and [second record](judge-evidence/records/A334201.seq).

## Candidate 70: A052382 vs A209931

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A052382=1, A209931=1; displayed lengths 93 and 91. At equal native indices, the initial agreement is 91 terms (n=1..91); this count is limited by the shorter displayed list.

**Evidence.** The 91 displayed terms agree. Independent enumeration extends agreement to 172 terms; at index 173 the values are 212 versus 213. Although 212 has no zero digit, its divisor 106 contains zero, so it fails the second sequence's condition.

**Novelty and integrity.** Novelty check: A209931 %C explicitly states this first difference, corrected July 1, 2025. The current corrected comment and direct enumeration agree; the prefix does not support equality.

Sources: [A052382](https://oeis.org/A052382), [A209931](https://oeis.org/A209931); freshly retrieved [first record](judge-evidence/records/A052382.seq) and [second record](judge-evidence/records/A209931.seq).

## Candidate 71: A358678 vs A359150

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A358678=1, A359150=1; displayed lengths 121 and 128. At equal native indices, the initial agreement is 104 terms (n=1..104); the next comparison at n=105 is 0 versus 1. Packet `drop1` agreement: 103 terms, comparing indices 2..104 and 2..104.

**Evidence.** The raw agreement is 104 terms n=1..104; dropping the first term gives the claimed 103. At n=105 the displayed and independently calculated values are 0 versus 1: sigma(105)=192, while 105 is 1 mod4 and has three prime factors.

**Novelty and integrity.** Novelty check: both %Y fields explicitly state this counterexample. The matching block ends in the displayed lists, so there is no surviving identity or formula/list conflict here.

Sources: [A358678](https://oeis.org/A358678), [A359150](https://oeis.org/A359150); freshly retrieved [first record](judge-evidence/records/A358678.seq) and [second record](judge-evidence/records/A359150.seq).

## Candidate 72: A256608 vs A279186

**DROP — novelty.**

**Agreement and offsets.** Offsets: A256608=1, A279186=1; displayed lengths 86 and 88. At equal native indices, the initial agreement is 86 terms (n=1..86); this count is limited by the shorter displayed list.

**Evidence.** The two records already assert the identical formula A007733(A002322(n)). In A279186 this is explicitly credited to Max Alekseyev, February 2, 2024; its PARI program implements the same formula. The 86 common displayed terms therefore support an already-published equality, not a new target.

**Novelty and integrity.** Integrity flag: A279186 %Y still says all three sequences A256607, A256608 and A279186 are different. That conflicts with its own shared formula for this pair. No disagreement occurs in the 86 common terms; the stale distinctness statement cannot restore novelty. The two definitions concern maximal cycle length versus their lcm, but the identical formula already publishes the connection.

Sources: [A256608](https://oeis.org/A256608), [A279186](https://oeis.org/A279186); freshly retrieved [first record](judge-evidence/records/A256608.seq) and [second record](judge-evidence/records/A279186.seq).

## Candidate 73: A327517 vs A376504

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A327517=1, A376504=1; displayed lengths 87 and 87. At equal native indices, the initial agreement is 0 terms; the next comparison at n=1 is 1 versus 0. Packet `drop1` agreement: 86 terms, comparing indices 2..87 and 2..87.

**Evidence.** The lists disagree at n=1, 1 versus 0. After deleting that entry, direct formulas give 208 equal terms n=2..209, then 14 versus 11 at n=210. Indeed omega(210)=4, Bell(4)-1=14, and 2^4-4-1=11.

**Novelty and integrity.** Novelty check: A376504 %C explicitly says the sequences differ at 210 and gives its own value 11. The 86 displayed tail matches stop long before this documented witness; the initial empty-factorization convention is an additional mismatch.

Sources: [A327517](https://oeis.org/A327517), [A376504](https://oeis.org/A376504); freshly retrieved [first record](judge-evidence/records/A327517.seq) and [second record](judge-evidence/records/A376504.seq).

## Candidate 74: A064459 vs A342696

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A064459=0, A342696=0; displayed lengths 101 and 97. At equal native indices, the initial agreement is 97 terms (n=0..96); this count is limited by the shorter displayed list.

**Evidence.** Independent floor-sum evaluation gives exactly 144 equal terms n=0..143, then A064459(144)=13 versus A342696(144)=12. The packet only sees 97 terms through n=96.

**Novelty and integrity.** Novelty check: A342696 %C states both the agreement range and the counterexample. The sums differ as soon as the 12^2 denominator contributes. A064459 also records correction of its old factorial-valuation interpretation; that obsolete interpretation is not used here.

Sources: [A064459](https://oeis.org/A064459), [A342696](https://oeis.org/A342696); freshly retrieved [first record](judge-evidence/records/A064459.seq) and [second record](judge-evidence/records/A342696.seq).

## Candidate 75: A001462 vs A377862

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A001462=1, A377862=1; displayed lengths 84 and 85. At equal native indices, the initial agreement is 84 terms (n=1..84); this count is limited by the shorter displayed list.

**Evidence.** Independent generation from the self-count definitions extends the 84 displayed matches to 168 equal terms. At n=169 Golomb's sequence is 29 and the digit-count variant is 31. The latter value also appears in the freshly fetched A377862 b-file.

**Novelty and integrity.** Novelty check: A377862 %C explicitly gives this first difference. Counting digits instead of terms changes the object; the displayed truncation conceals the known divergence. No additional formula/list contradiction was identified.

Sources: [A001462](https://oeis.org/A001462), [A377862](https://oeis.org/A377862); freshly retrieved [first record](judge-evidence/records/A001462.seq) and [second record](judge-evidence/records/A377862.seq).

## Candidate 76: A031955 vs A288040

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A031955=1, A288040=1; displayed lengths 102 and 83. At equal native indices, the initial agreement is 83 terms (n=1..83); this count is limited by the shorter displayed list.

**Evidence.** Independent decimal-digit enumeration finds exactly 83 matching terms, then A031955(84)=110 versus A288040(84)=102. The number 102 has three distinct digits, a prime count, so belongs to A288040 but not to the exactly-two-digit sequence.

**Novelty and integrity.** Novelty check: A288040 %Y already describes its union with the three-distinct-digit sequence A031962. This is a published containment, not a published or true equality. The shorter displayed list stops exactly before the first mismatch.

Sources: [A031955](https://oeis.org/A031955), [A288040](https://oeis.org/A288040); freshly retrieved [first record](judge-evidence/records/A031955.seq) and [second record](judge-evidence/records/A288040.seq).

## Candidate 77: A108045 vs A127672

**DROP — novelty.**

**Agreement and offsets.** Offsets: A108045=0, A127672=0; displayed lengths 91 and 95. At equal native indices, the initial agreement is 0 terms; the next comparison at n=0 is 1 versus 2. Packet `drop1` agreement: 90 terms, comparing indices 1..90 and 1..90.

**Evidence.** A108045 %F gives the Riordan array ((1-x^2)/(1+x^2),x/(1+x^2)). A127672 %F explicitly gives that same array when its initial entry is changed from 2 to 1. The 90-term match after dropping the initial entry is therefore already published via identical array formulas.

**Novelty and integrity.** Interestingness also fails: this is a one-entry normalization of the same Chebyshev coefficient triangle. Native agreement is zero because the first entries are 1 and 2. This discrepancy is an intentional convention, not a newly discovered identity or erroneous displayed term.

Sources: [A108045](https://oeis.org/A108045), [A127672](https://oeis.org/A127672); freshly retrieved [first record](judge-evidence/records/A108045.seq) and [second record](judge-evidence/records/A127672.seq).

## Candidate 78: A277998 vs A289288

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A277998=1, A289288=1; displayed lengths 106 and 111. At equal native indices, the initial agreement is 90 terms (n=1..90); the next comparison at n=91 is 101 versus 111.

**Evidence.** Both displayed lists and independent greedy generation agree for exactly 90 terms. At n=91 the unrestricted sequence chooses 101, while the no-zero sequence chooses 111. Internal zeros are permitted by the first definition and prohibited by the second.

**Novelty and integrity.** Novelty check: no equality assertion between the pair was found in either record; their definitions themselves disprove it. Integrity flag: A277998's prose example omits the terms 7 and 3 after 93, whereas its data list and its greedy rule contain them. The counterexample uses the data and definition, not that abbreviated erroneous example.

Sources: [A277998](https://oeis.org/A277998), [A289288](https://oeis.org/A289288); freshly retrieved [first record](judge-evidence/records/A277998.seq) and [second record](judge-evidence/records/A289288.seq).

## Candidate 79: A188734 vs A188941

**DROP — novelty.**

**Agreement and offsets.** Offsets: A188734=1, A188941=1; displayed lengths 130 and 130. At equal native indices, the initial agreement is 0 terms; the next comparison at n=1 is 3 versus 4. Packet `drop2` agreement: 128 terms, comparing indices 3..130 and 3..130.

**Evidence.** Both %C fields explicitly state that the digit strings agree after their first two digits, with April 2011 attribution. Algebraically the constants (7+sqrt(65))/4 and (9+sqrt(65))/4 differ by exactly 1/2. The 128 digit-tail matches are a published trivial decimal-prefix transform.

**Novelty and integrity.** The first digits already differ (3 versus 4), as do the second digits. No new equality of constants or complete digit strings exists. The decimal expansions use the same decimal-point convention, so no offset repair alters this conclusion.

Sources: [A188734](https://oeis.org/A188734), [A188941](https://oeis.org/A188941); freshly retrieved [first record](judge-evidence/records/A188734.seq) and [second record](judge-evidence/records/A188941.seq).

## Candidate 80: A355824 vs A355826

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A355824=1, A355826=1; displayed lengths 128 and 128. At equal native indices, the initial agreement is 127 terms (n=1..127); the next comparison at n=128 is -3 versus -4. Packet `abs` agreement: 127 terms, comparing indices 1..127 and 1..127 after taking absolute values.

**Evidence.** The raw and absolute-value comparisons both agree for exactly 127 terms n=1..127. At n=128 the displayed values are -3 and -4, whose magnitudes also differ. Independent Dirichlet inversion of the two published characteristic functions reproduces those values.

**Novelty and integrity.** Novelty check: both %Y fields explicitly give the first difference at 128. The abs variant is irrelevant to this counterexample; both original definitions already diverge when exponent 7 first occurs.

Sources: [A355824](https://oeis.org/A355824), [A355826](https://oeis.org/A355826); freshly retrieved [first record](judge-evidence/records/A355824.seq) and [second record](judge-evidence/records/A355826.seq).

## Candidate 81: A374130 vs A374466

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A374130=1, A374466=1; displayed lengths 128 and 128. At equal native indices, the initial agreement is 127 terms (n=1..127); the next comparison at n=128 is 0 versus 1.

**Evidence.** Exactly 127 terms agree; at n=128=2^7 the displayed and independently computed values are 0 versus 1. The exponent XOR is 7, not 1, but Omega(128)=7 is odd and the binary weight of 7 is 3, also odd.

**Novelty and integrity.** Novelty check: both %Y fields explicitly give this first difference. The definitions and listed data agree; the mined equality is simply false.

Sources: [A374130](https://oeis.org/A374130), [A374466](https://oeis.org/A374466); freshly retrieved [first record](judge-evidence/records/A374130.seq) and [second record](judge-evidence/records/A374466.seq).

## Candidate 82: A298735 vs A384916

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A298735=1, A384916=1; displayed lengths 105 and 87. At equal native indices, the initial agreement is 87 terms (n=1..87); this count is limited by the shorter displayed list.

**Evidence.** The 87 displayed matches extend by direct evaluation to exactly 124 terms. At n=125=5^3 the odd-square-divisor count is 2, while the allowed prime-power factorizations correspond to 3, 2+1, and 1+1+1, giving 3.

**Novelty and integrity.** Novelty check: A384916 %C already states the first difference at 125 and cross-references A298735. No formula/list contradiction was found; the short list hides the documented failure.

Sources: [A298735](https://oeis.org/A298735), [A384916](https://oeis.org/A384916); freshly retrieved [first record](judge-evidence/records/A298735.seq) and [second record](judge-evidence/records/A384916.seq).

## Candidate 83: A185014 vs A240467

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A185014=0, A240467=0; displayed lengths 86 and 87. At equal native indices, the initial agreement is 0 terms; the next comparison at n=0 is 0 versus 1. Packet `drop1` agreement: 75 terms, comparing indices 1..75 and 1..75.

**Evidence.** Native equality fails at n=0 (0 versus 1). After dropping that term the match is exactly 75 terms n=1..75, then 0 versus -1 at n=76, already displayed. Since Phi_152(x)=(1+x^76)/(1+x^4), its inverse is (1+x^4)/(1+x^76), explaining both the single early spike and the negative coefficient at 76.

**Novelty and integrity.** Novelty check: no equality assertion was found; the published definitions immediately refute one. Interestingness also fails for the mined sparse block. The coefficient at 76 agrees with the cyclotomic definition; it is not a data error.

Sources: [A185014](https://oeis.org/A185014), [A240467](https://oeis.org/A240467); freshly retrieved [first record](judge-evidence/records/A185014.seq) and [second record](judge-evidence/records/A240467.seq).

## Candidate 84: A359466 vs A359467

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A359466=1, A359467=1; displayed lengths 125 and 125. At equal native indices, the initial agreement is 125 terms (n=1..125); this count is limited by the shorter displayed list.

**Evidence.** Independent factorization extends the 125 listed matches to exactly 224 terms. At n=225=3^2*5^2 the first sequence is 0 because there are two nonunitary prime factors; the second is 1 because 225 is an odd nonsquarefree number.

**Novelty and integrity.** Novelty check: both %Y fields explicitly publish this first difference. Their characteristic-function descriptions agree with the counterexample; the truncation is the failure.

Sources: [A359466](https://oeis.org/A359466), [A359467](https://oeis.org/A359467); freshly retrieved [first record](judge-evidence/records/A359466.seq) and [second record](judge-evidence/records/A359467.seq).

## Candidate 85: A046951 vs A159631

**DROP — data integrity.**

**Agreement and offsets.** Offsets: A046951=1, A159631=1; displayed lengths 125 and 125. At equal native indices, the initial agreement is 124 terms (n=1..124); the next comparison at n=125 is 2 versus 3.

**Evidence.** Exactly 124 terms agree, n=1..124. Both displayed lists include the next terms: A046951(125)=2 and A159631(125)=3. The first value counts the square divisors 1 and 25.

**Novelty and integrity.** Novelty check: both %C fields explicitly state equality only for n<125 and the unequal values at 125 (Steven Finch attribution April 22, 2009 on A046951). The modular-forms interpretation therefore gives a known finite coincidence, not an identity; no further formula/list contradiction is needed.

Sources: [A046951](https://oeis.org/A046951), [A159631](https://oeis.org/A159631); freshly retrieved [first record](judge-evidence/records/A046951.seq) and [second record](judge-evidence/records/A159631.seq).
## Candidate 86: A296073 vs A305800 — DROP (data integrity)

**Agreement.** Both offsets are 1. Exactly 124 terms agree at n=1..124; n=125 is 33 versus 96, already visible in both data sections and confirmed by the b-files.

**Novelty.** Both records explicitly publish the failure at n=125; A296073 also says it is not the restricted-growth transform defining A305800. No equality is asserted.

**Integrity / reason.** The packet stopped one term before a listed counterexample. A296073 reuses the class of 46 at 125, while A305800 assigns every composite its next distinct class. No record-term/b-file inconsistency found. Separately, A305800's notation comment prints S(i)=S(i) => T(i)=T(j); the antecedent should compare S(i) with S(j). The literal tautology would force T to be constant, contrary to its nonconstant data. This exposition typo is not used to infer equality.

Sources: [A296073](https://oeis.org/A296073); [A305800](https://oeis.org/A305800); [A296073 b-file](https://oeis.org/A296073/b296073.txt), [A305800 b-file](https://oeis.org/A305800/b305800.txt).

## Candidate 87: A321538 vs A321803 — DROP (data integrity)

**Agreement.** Both offsets are 0. The 124 common listed terms are n=0..123. Independent evaluation of the definitions agrees for all 11,011 indices n=0..11010, then gives 111 versus 1111 at n=11011.

**Novelty.** A321803 explicitly publishes n=11011 as the first disagreement with A321538; this is a known near-match, not an asserted identity.

**Integrity / reason.** A321538 first shortens each decimal run by one and then lengthens the resulting runs: 11011 -> 11 -> 111. A321803 retains the two original double-1 runs and deletes the isolated zero, giving 1111. The short listing hides this structural difference.

Sources: [A321538](https://oeis.org/A321538); [A321803](https://oeis.org/A321803); [A321536](https://oeis.org/A321536); [A321537](https://oeis.org/A321537).

## Candidate 88: A373491 vs A373588 — DROP (data integrity)

**Agreement.** Both offsets are 1. There are 125 equal listed terms, or 124 at n=2..125 under drop1. The b-files agree at n=1..342 and first differ at n=343: 1 versus 0; the transformed prefix therefore lasts 341 terms.

**Novelty.** A373588 explicitly states that it first differs from A373491 at n=343, including both values. No equality is asserted.

**Integrity / reason.** For 343=7^3, the two tests in A373491 give 3(7-1)=18 and numerator(3/7)=3, both divisible by 3. A373588 rejects it because 7 is not 2 modulo 3. This independently confirms the counterexample.

Sources: [A373491](https://oeis.org/A373491); [A373588](https://oeis.org/A373588); [A373491 b-file](https://oeis.org/A373491/b373491.txt), [A373588 b-file](https://oeis.org/A373588/b373588.txt).

## Candidate 89: A374134 vs A374136 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 125 listed terms agree; drop1 leaves 124. The b-files agree at n=1..254, then give 1 versus 0 at n=255, so drop1 agrees for 253 terms before failing.

**Novelty.** Both records explicitly give the first mutual disagreement at n=255. They separately describe agreement with parity only up to n=104.

**Integrity / reason.** 2*phi(255)=256>255, so A374134(255)=1. A374136 reports that the cyclotomic polynomial at 255 is not flat, giving 0. Neither the long parity-like stretch nor the shared zero at 105 makes the definitions equal.

Sources: [A374134](https://oeis.org/A374134); [A374136](https://oeis.org/A374136); [A374134 b-file](https://oeis.org/A374134/b374134.txt), [A374136 b-file](https://oeis.org/A374136/b374136.txt).

## Candidate 90: A335324 vs A366245 — DROP (data integrity)

**Agreement.** Both offsets are 1. All 85 common listed terms agree. The b-files extend agreement through n=255, then give A335324(256)=1 and A366245(256)=256.

**Novelty.** A366245 explicitly states that the first difference from A335324 is n=256. No equality is asserted.

**Integrity / reason.** At 256=2^8, the fourth-power-free square part is 1. A366245 retains the exponent bit of weight 8 in its infinitary divisor construction, so its value is 256. The prefix lacks a prime exponent large enough to expose that difference.

Sources: [A335324](https://oeis.org/A335324); [A366245](https://oeis.org/A366245); [A335324 b-file](https://oeis.org/A335324/b335324.txt), [A366245 b-file](https://oeis.org/A366245/b366245.txt).

## Candidate 91: A359162 vs A360111 — DROP (data integrity)

**Agreement.** Both offsets are 1. The native listing agrees for 123 terms at n=1..123, and drop1 for 122. Both b-files and an independent scan of the definitions first differ at n=135: 1 versus 0. Native agreement is 134 terms; drop1 agreement is 133.

**Novelty.** No assertion of equality between these two sequences was found in either record. Their relationships to A353479 concern characteristic functions and first differences, not a mutual identity. A counterexample makes further novelty hunting unnecessary.

**Integrity / reason.** 135=3^3*5 is 3 modulo 4 and has four prime factors with multiplicity, so A359162(135)=1. A360111(135)=0 because 3^3 divides 135. Separately, A360111 has an erroneous cross-reference saying it differs from A353479 at 158 while printing 1 for both values; the asserted difference cannot follow from those equal numbers. The direct calculation and b-files do not rely on this typo.

Sources: [A359162](https://oeis.org/A359162); [A360111](https://oeis.org/A360111); [A359162 b-file](https://oeis.org/A359162/b359162.txt), [A360111 b-file](https://oeis.org/A360111/b360111.txt).

## Candidate 92: A319707 vs A319717 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 121 common listed terms agree. The b-files agree through n=142 and first differ at n=143: 113 versus 51.

**Novelty.** A319717 explicitly publishes the first difference from A319707 at 143. The implication about equality classes in A319707 is a filter-refinement statement, not equality of the sequences.

**Integrity / reason.** A319707 gives every composite its own new class. A319717 can identify different composites sharing the stated divisor/residue data. The b-files confirm the published collision at 143; the lists simply stop too soon.

Sources: [A319707](https://oeis.org/A319707); [A319717](https://oeis.org/A319717); [A319707 b-file](https://oeis.org/A319707/b319707.txt), [A319717 b-file](https://oeis.org/A319717/b319717.txt).

## Candidate 93: A072411 vs A290107 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 120 listed terms agree. B-files and independent factorization calculations agree for n=1..143, then give 4 versus 8 at n=144.

**Novelty.** Both records explicitly state the first mutual difference is at n=144; no equality is asserted.

**Integrity / reason.** 144=2^4*3^2: lcm(4,2)=4, whereas the product of the distinct exponents is 4*2=8. Repeated or coprime small exponents conceal the distinction in the displayed prefix.

Sources: [A072411](https://oeis.org/A072411); [A290107](https://oeis.org/A290107); [A072411 b-file](https://oeis.org/A072411/b072411.txt), [A290107 b-file](https://oeis.org/A290107/b290107.txt).

## Candidate 94: A129251 vs A276077 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 120 common listed terms agree. B-files and independent calculations agree for n=1..624, then give 0 versus 1 at n=625.

**Novelty.** Both records explicitly publish n=625 and the unequal values as their first difference. No equality is asserted.

**Integrity / reason.** 625=5^4 fails the exponent threshold e>=p=5 for A129251, but meets e>=1+primepi(5)=4 for A276077. Agreement at the primes 2 and 3 does not continue to prime 5.

Sources: [A129251](https://oeis.org/A129251); [A276077](https://oeis.org/A276077); [A129251 b-file](https://oeis.org/A129251/b129251.txt), [A276077 b-file](https://oeis.org/A276077/b276077.txt).

## Candidate 95: A294936 vs A378539 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 120 common listed terms agree. The b-files agree for n=1..747 and first differ at n=748: 1 versus 0.

**Novelty.** A378539 explicitly lists 748 as the first disagreement with A294936 and labels itself different from A294936. No equality is asserted.

**Integrity / reason.** Independent subset-sum enumeration over the divisors of each divisor of 748 finds no Zumkeller divisor, while sigma(748)=1512>=1496=2*748. Thus the nondeficiency predicate is true and the Zumkeller-divisor predicate is false.

Sources: [A294936](https://oeis.org/A294936); [A378539](https://oeis.org/A378539); [A294936 b-file](https://oeis.org/A294936/b294936.txt), [A378539 b-file](https://oeis.org/A378539/b378539.txt).

## Candidate 96: A353675 vs A353676 — DROP (data integrity)

**Agreement.** Both offsets are 1. Native equality fails immediately at n=1: 1 versus 0. Removing the first entry gives the claimed 120 listed matches at n=2..121. The b-files and definitions extend this tail to n=1154, for 1,153 matches, then differ at 1155: 1 versus 0.

**Novelty.** Both records explicitly publish the exception at 1 and the next difference at 1155. The inequality A353675>=A353676 is not equality.

**Integrity / reason.** 1155=3*5*7*11 has an even number (four) of distinct prime factors, but does not have exactly two. Deleting the initial exception cannot repair the proposed identity.

Sources: [A353675](https://oeis.org/A353675); [A353676](https://oeis.org/A353676); [A353675 b-file](https://oeis.org/A353675/b353675.txt), [A353676 b-file](https://oeis.org/A353676/b353676.txt).

## Candidate 97: A055642 vs A348674 — DROP (data integrity)

**Agreement.** Both offsets are 0. Native agreement is exactly 120 terms at n=0..119; drop1 yields 119 at n=1..119. Both records already include n=120, where the values are 3 and 4. B-files and independent enumeration confirm this.

**Novelty.** A348674 explicitly identifies n=120 as its first difference from A055642 and gives both values. No equality is asserted.

**Integrity / reason.** The four distinct split sums of 120 are {3,12,21,120}, whereas 120 has three decimal digits. Also, A055642 contains a defective Common Lisp program: its positive branch floor(log(n,10)) omits +1 and gives 0 at n=1, contradicting the definition and listed value 1. The b-file and other implementations agree with the definition.

Sources: [A055642](https://oeis.org/A055642); [A348674](https://oeis.org/A348674); [A055642 b-file](https://oeis.org/A055642/b055642.txt), [A348674 b-file](https://oeis.org/A348674/b348674.txt).

## Candidate 98: A131734 vs A134452 — DROP (novelty)

**Agreement.** Both offsets are 0. Untransformed values agree only at n=0..10 (11 terms), then are -1 versus 1 at n=11. Taking absolute values gives the claimed 119 listed matches at n=0..118.

**Novelty.** This transformed identity is already published: A131734 states abs(a(n))=A000035(n), and A134452 states the identical formula. Equality through the shared parity sequence is explicit, not inferred from a bare cross-reference.

**Integrity / reason.** The absolute-value transformation erases the only differing information; both become the period-2 sequence n mod 2. This also fails interestingness as a trivial absolute-value transform and short-period pattern. The signed original sequences are unequal.

Sources: [A131734](https://oeis.org/A131734); [A134452](https://oeis.org/A134452).

## Candidate 99: A184582 vs A184734 — DROP (data integrity)

**Agreement.** Both offsets are 1. All 120 listed terms agree, or 119 after drop1. Independent 70-digit evaluation of the published floor formulas agrees at n=1..136, then gives 221 versus 222 at n=137; drop1 therefore agrees for 135 terms before failing.

**Novelty.** A184734 explicitly states that the first difference from A184582 is at index 137. No equality is asserted.

**Integrity / reason.** The intercepts are phi/5 and 1/3, which are unequal. Their small separation explains a long shared floor-function prefix but cannot produce a global equality. At n=137 the two real arguments fall on opposite sides of 222.

Sources: [A184582](https://oeis.org/A184582); [A184734](https://oeis.org/A184734).

## Candidate 100: A322437 vs A322438 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 120 common listed terms agree; drop1 leaves 119. B-files agree at n=1..143 and first give 3 versus 4 at n=144, so the transformed prefix has 142 matching terms.

**Novelty.** Both records explicitly state the first mutual difference at n=144 and give the values 3 and 4. No equality is asserted.

**Integrity / reason.** Independent enumeration finds the extra pair (4*4*9, 4*6*6) for 144. Equal factors 4 are permitted when only proper divisibility is forbidden (A322438), but forbidden when any divisibility is prohibited (A322437). This is a substantive difference hidden by truncation.

Sources: [A322437](https://oeis.org/A322437); [A322438](https://oeis.org/A322438); [A322437 b-file](https://oeis.org/A322437/b322437.txt), [A322438 b-file](https://oeis.org/A322438/b322438.txt).

## Candidate 101: A347246 vs A353626 — DROP (data integrity)

**Agreement.** Both offsets are 1. Native equality already fails at n=1: 1 versus 0. drop2 gives 119 listed matches at n=3..121. B-files and independent definitions agree from n=2 through 152, then give 0 versus 1 at 153; the drop2 prefix has 150 matches.

**Novelty.** A353626 explicitly names the initial exception and the next difference from A347246 at n=153. No equality is asserted.

**Integrity / reason.** 153=3^2*17 has a repeated odd prime factor, so A353626=1. The sum of its odd divisors is sigma(153)=13*18=234, whose greatest prime factor is 13<17, so A347246=0.

Sources: [A347246](https://oeis.org/A347246); [A353626](https://oeis.org/A353626); [A347246 b-file](https://oeis.org/A347246/b347246.txt), [A353626 b-file](https://oeis.org/A353626/b353626.txt).

## Candidate 102: A353480 vs A359595 — DROP (data integrity)

**Agreement.** Both offsets are 1. Native equality fails at n=1: 0 versus 1. drop2 gives 119 listed matches at n=3..121. The b-files agree from n=2 through 134, then give 0 versus 1 at 135; drop2 agreement is 132 terms.

**Novelty.** A359595 explicitly lists the disagreement set via A359597 and says the next difference after 1 is 135. Its bounding inequality involving A353480 does not assert equality.

**Integrity / reason.** 135=3^3*5 has four prime factors with multiplicity, so it is not semiprime. Independent Dirichlet inversion of the stated characteristic function gives inverse value 1 at 135, hence odd parity. This confirms the b-file counterexample.

Sources: [A353480](https://oeis.org/A353480); [A359595](https://oeis.org/A359595); [A353480 b-file](https://oeis.org/A353480/b353480.txt), [A359595 b-file](https://oeis.org/A359595/b359595.txt).

## Candidate 103: A227349 vs A284580 — DROP (data integrity)

**Agreement.** Both offsets are 0. Native agreement is 119 terms at n=0..118; drop1 produces 118 at n=1..118. The first disagreement at n=119 is 9 versus 5, present in the listed terms and confirmed by the b-files and computation.

**Novelty.** Both records explicitly publish this first disagreement at n=119. No equality is asserted.

**Integrity / reason.** 119 has binary expansion 1110111, with run lengths 3 and 3. Ordinary multiplication gives 9; carryless binary multiplication gives (x+1)^2=x^2+1 over GF(2), encoded as 5. The packet stops at the first counterexample.

Sources: [A227349](https://oeis.org/A227349); [A284580](https://oeis.org/A284580); [A227349 b-file](https://oeis.org/A227349/b227349.txt), [A284580 b-file](https://oeis.org/A284580/b284580.txt).

## Candidate 104: A103889 vs A114112 — DROP (novelty)

**Agreement.** Both offsets are 1. Native equality fails at n=1 (2 versus 1) and also n=2 (1 versus 2). After drop2, the 70 displayed terms at n=3..72 agree; the published formulas establish the same tail for every n>=3.

**Novelty.** A114112 explicitly groups A103889 and itself as essentially the same sequence. Its name already gives the common formula n-(-1)^n for n>2, and its comments publish the induction reducing the original greedy definition to that formula.

**Integrity / reason.** This is a known two-entry modification of a simple odd/even swap, also failing interestingness. The A114112 induction paragraph has transcription errors: it assigns both 2i+1 and 2i-1 to a(2i) and gives two different A(2i) formulas. The name, data, and final formula consistently specify the simple tail, so these prose errors do not rescue novelty.

Sources: [A103889](https://oeis.org/A103889); [A114112](https://oeis.org/A114112).

## Candidate 105: A270418 vs A367168 — DROP (data integrity)

**Agreement.** Both offsets are 1. All 70 common listed terms agree. The b-files agree for n=1..127 and first differ at 128: 8 versus 1.

**Novelty.** A367168 explicitly states that its first difference from A270418 is at n=128. No equality is asserted.

**Integrity / reason.** For 128=2^7, the alternating binary sum of exponent 7=111_2 is 4-2+1=3, giving A270418(128)=2^3=8. A367168 gives 1, as confirmed by its b-file. The prime-power formulas are different.

Sources: [A270418](https://oeis.org/A270418); [A367168](https://oeis.org/A367168); [A270418 b-file](https://oeis.org/A270418/b270418.txt), [A367168 b-file](https://oeis.org/A367168/b367168.txt).

## Candidate 106: A206074 vs A325559 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 69 common listed terms agree. The b-files agree for the first 172 terms, then A206074(173)=557 while A325559(173)=555.

**Novelty.** A325559 explicitly publishes this first disagreement, says 555 is absent from A206074, and gives examples excluded in the opposite direction. This is already a documented near-match.

**Integrity / reason.** The binary polynomial encoded by 555 is x^9+x^5+x^3+x+1, divisible over Q by x^2-x+1, so it is excluded from A206074. Independent GF(2) remainder tests show that among integer divisors d of 555 only d=1 and d=555 have encoded polynomials dividing it; thus 555 satisfies A325559. The two irreducibility/divisor notions genuinely differ.

Sources: [A206074](https://oeis.org/A206074); [A325559](https://oeis.org/A325559); [A206074 b-file](https://oeis.org/A206074/b206074.txt), [A325559 b-file](https://oeis.org/A325559/b325559.txt).

## Candidate 107: A085971 vs A387421 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 68 common listed terms agree. The b-files agree for the first 209 terms, then give 225 versus 226 at sequence index 210.

**Novelty.** Both records explicitly publish the first mutual disagreement at index 210, including 225 and 226. The separate >= versus > conjecture in A387421 concerns another characterization and does not assert equality with A085971.

**Integrity / reason.** 225=3^2*5^2 is not a prime power, so it belongs to A085971. Its powerful part is 225 but sigma(225)=403<450, so it is excluded from A387421. This directly validates the first missing value.

Sources: [A085971](https://oeis.org/A085971); [A387421](https://oeis.org/A387421); [A085971 b-file](https://oeis.org/A085971/b085971.txt), [A387421 b-file](https://oeis.org/A387421/b387421.txt).

## Candidate 108: A252895 vs A366242 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 67 common listed terms agree. The b-files agree for the first 171 terms, then give 256 versus 257 at sequence index 172.

**Novelty.** A366242 explicitly describes itself as a subsequence of A252895 and identifies the first difference at 172, with 256 missing. The subsequence statement does not assert equality.

**Integrity / reason.** 256=2^8 has five square divisors and is included in A252895. Its prime exponent 8 has base-4 digits 20, which violate the allowed 0/1 digits in the Moser-de Bruijn exponent condition defining A366242.

Sources: [A252895](https://oeis.org/A252895); [A366242](https://oeis.org/A366242); [A252895 b-file](https://oeis.org/A252895/b252895.txt), [A366242 b-file](https://oeis.org/A366242/b366242.txt).

## Candidate 109: A389215 vs A393981 — DROP (data integrity)

**Agreement.** Both offsets are 1. The 67 common listed terms agree. B-files and independent generation from the definitions agree for the first 184 terms, then give 240 versus 241 at index 185.

**Novelty.** A393981 explicitly identifies A389215(185)=240 as absent from its own sequence. No equality is asserted; the cross-reference is accompanied by a counterexample.

**Integrity / reason.** At 240, the unitary-divisor sum is 408 and the squarefree-divisor sum is 72, totaling 480=2*240, so A389215 includes it. A393981 excludes it since 240/rad(240)=8 is not <7. Also flag two internal A393981 comment errors: for p^j the ratio is p^(j-1), not always p; and the claimed union containing A246547\{4} includes 8, contradicting its own intersection claim, definition, and listed terms. A246547 explicitly lists 8 among proper prime powers. The principal definition and b-file consistently exclude 8 and 240.

Sources: [A389215](https://oeis.org/A389215); [A393981](https://oeis.org/A393981); [A246547](https://oeis.org/A246547); [A389215 b-file](https://oeis.org/A389215/b389215.txt), [A393981 b-file](https://oeis.org/A393981/b393981.txt).

## Candidate 110: A188658 vs A248803 — DROP (novelty)

**Agreement.** The cons offsets 1 and 2 place the decimal points differently. As ordinal digit strings, only the first digit agrees before the second digit differs (1 versus 0); deleting the first two digits from each gives the claimed 128 matches at digit positions 3..130. Same stored indices instead give only two initial matches before 4 versus 0; neither comparison makes the original constants equal.

**Novelty.** A248803 explicitly states that its digits differ from A188658 in only one digit. More decisively, the published names give x=(1+sqrt(101))/10 and y=sqrt(101), so y=10*x-1. The observed tail relation is already specified algebraically and in the comment.

**Integrity / reason.** Independent high-precision evaluation confirms the 128-digit tail. This is a decimal-point shift plus a change in a leading digit, also failing interestingness as a trivial transform. The constants and full digit strings are different; offset metadata must not be mistaken for identical decimal places.

Sources: [A188658](https://oeis.org/A188658); [A248803](https://oeis.org/A248803).
## Candidate 111: A025446 vs A373972 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; all 127 common listed terms agree at n=0..126. Independent enumeration extends the exact agreement to 1729 terms, n=0..1728, then gives 2 versus 1 at n=1729.

**Novelty.** Both records explicitly publish this first disagreement; A373972 also publishes its signum relationship to A025446. This is an already documented finite-prefix coincidence, not an asserted equality.

**Integrity and other gates.** 1729=1^3+12^3=9^3+10^3 has two unordered representations, while the characteristic function is 1. No internal term/formula contradiction was found in the checked definitions.

Sources: [A025446](https://oeis.org/A025446) [A373972](https://oeis.org/A373972)

## Candidate 112: A004772 vs A319371 — DROP (novelty)

**Agreement and offsets.** Offsets 1/1. The native equality fails immediately at n=1 (0 versus 1); deleting each first term yields 66 common listed matches at n=2..67.

**Novelty.** A319371 explicitly conjectures a(n)=A004772(n) for n>1, clarified April 16, 2019. An already published conjecture fails the primary gate even without a proof.

**Integrity and other gates.** The candidate is an initial-term exception followed by a simple residue-class enumeration. A separate A004772 comment has an arithmetic typo: its displayed m=3*(a(n)+1) gives 3 at n=1, not the displayed 1. This does not rescue novelty.

Sources: [A004772](https://oeis.org/A004772) [A319371](https://oeis.org/A319371)

## Candidate 113: A249407 vs A360305 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 66 common listed terms agree at n=1..66. Independent greedy constructions agree for 114 terms and first differ at n=115: 120 versus 121.

**Novelty.** A360305 explicitly publishes the n=115 disagreement with A249407. Its Cf. link is not being treated as an equality assertion.

**Integrity and other gates.** The four-leaf product 2*3*4*5=120 is already a tree-node value, so A360305 cannot later use it as a leaf. The pair-product sieve A249407 can. This is truncation, not an identity.

Sources: [A249407](https://oeis.org/A249407) [A360305](https://oeis.org/A360305)

## Candidate 114: A355823 vs A355825 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1. Raw terms agree at n=1..127 (127 terms); the packet drop2 view retains only n=3..127 (125 matches). Both live lists already include the failure at n=128: 0 versus 1.

**Novelty.** Each record explicitly names this first disagreement with the other. No equality is asserted.

**Integrity and other gates.** 128=2^7: exponent 7 is not a power of two, but has binary weight 3, which is odd. Independent factorization checks confirm the first failure. Deleting two initial terms does not remove it.

Sources: [A355823](https://oeis.org/A355823) [A355825](https://oeis.org/A355825)

## Candidate 115: A035930 vs A347470 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; the shared listed window contains 108 matches, n=0..107. Independent concatenation enumeration gives only 110 initial matches, n=0..109; the first failure is n=110: 10 versus 0.

**Novelty.** A347470 already discusses its finite agreement with A035930 and gives a disagreement example at n=112 (22 versus 12). There is no novel all-n equality.

**Integrity and other gates.** The A347470 comment claiming agreement for n<111 is itself false. At 110 the legal splits 1|10 and 11|0 have products 10 and 0; zero is expressly allowed as a whole number. Its listed a(110)=0 is correct, while A035930’s defining maximum gives 10. Thus the published n=112 example is not the first failure.

Sources: [A035930](https://oeis.org/A035930) [A347470](https://oeis.org/A347470)

## Candidate 116: A087003 vs A091069 — DROP (novelty)

**Agreement and offsets.** Offsets 1/1; absolute values agree for all 108 common listed terms. Signed equality lasts six terms, failing at n=7: -1 versus +1.

**Novelty.** A087003’s February 19, 2004 comments explicitly assert the absolute-value identity and explain it; A091069 independently states and derives the same identity. This is much stronger evidence than a cross-reference.

**Integrity and other gates.** Both absolute values are the indicator of odd squarefree integers, a prohibited abs transform. Also A087003’s published prime-power formula (-1+(-1)^e)/2 for odd primes is wrong for odd e>1: at 3^3=27 it gives -1 although its name and listed term give 0. The correct local values are -1 at e=1 and 0 at e>1.

Sources: [A087003](https://oeis.org/A087003) [A091069](https://oeis.org/A091069)

## Candidate 117: A193304 vs A240370 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 108 matches at n=1..108, followed by a mismatch already in both live lists: n=109 gives 170 versus 169.

**Novelty.** Both records explicitly document the difference, including the missing value 169. No equality is asserted.

**Integrity and other gates.** 169=13^2 is allowed by A240370 because 13=1 mod 4; it is excluded by A193304, which permits repeated prime factors only for 5. Independent definition-based enumeration confirms the first failure.

Sources: [A193304](https://oeis.org/A193304) [A240370](https://oeis.org/A240370)

## Candidate 118: A052928 vs A346663 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; all 74 common listed terms agree at n=0..73. A346663 publishes agreement through n=2435 (2436 terms), then 2436 versus 2434 at n=2436.

**Novelty.** The longer agreement and its failure are explicitly published in A346663, which cites Clark–Shattuck (2021). No all-n equality is asserted.

**Integrity and other gates.** Independently, for P(x)=sum_{k=0}^{2436} prime(k+1)*x^k, exact integer Horner arithmetic gives P(-4983/5000)<0, while P(0)=2 and P(-1)=10790. Hence P has at least two real roots and cannot have 2436 nonreal roots. This independently refutes the identity; the exact count 2434 and first-failure claim are sourced to the OEIS record, not claimed to be proved by this sign test.

Sources: [A052928](https://oeis.org/A052928) [A346663](https://oeis.org/A346663) [Clark–Shattuck paper cited by OEIS](https://arxiv.org/abs/2107.05572)

## Candidate 119: A025657 vs A025686 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 107 common listed terms agree. Exact integer heap enumeration extends agreement to n=1..113, then gives 11 versus 0 at n=114.

**Novelty.** Both records explicitly state that the pair differs at a(114). This published counterexample rules out the candidate.

**Integrity and other gates.** The two orderings of multiplicative semigroups only share an initial exponent pattern. The independent calculation uses integer products, avoiding floating-point logarithm-ordering artifacts.

Sources: [A025657](https://oeis.org/A025657) [A025686](https://oeis.org/A025686)

## Candidate 120: A038189 vs A089013 — DROP (novelty)

**Agreement and offsets.** Offsets 0/0; the first native terms differ, 0 versus 1 at n=0. After deleting both first terms, all 107 common entries agree at n=1..107.

**Novelty.** A089013 explicitly states A038189(n)=a(n) for n>0. Its recurrence also immediately reduces to the same binary-bit rule.

**Integrity and other gates.** This is a published equality with one changed initial value. The checked recurrences agree with the terms; the packet’s drop1 view suppresses the sole initial exception.

Sources: [A038189](https://oeis.org/A038189) [A089013](https://oeis.org/A089013)

## Candidate 121: A118828 vs A118831 — DROP (interestingness)

**Agreement and offsets.** Offsets 1/1; 107 absolute-value matches at n=1..107. Signed equality fails immediately: 1 versus -1 at n=1.

**Novelty.** No explicit pairwise equality was found in either record. Both records already publish their complete period-8 blocks, however; their absolute values are the same elementary period-4 block. No broader novelty claim is needed for this rejection.

**Integrity and other gates.** The only coincidence is abs([1,-1,0,-1,-1,1,0,1])=abs([-1,-1,0,-1,1,1,0,1]), repeating. This is both a forbidden absolute-value transform and a short-period pattern. A118828’s first generating function is normalized to the first listed term; its later formula explicitly extends the indexing with a(0)=1. These conventions should not be mistaken for a new identity.

Sources: [A118828](https://oeis.org/A118828) [A118831](https://oeis.org/A118831)

## Candidate 122: A344696 vs A389087 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 107 matches at n=1..107, then both live lists explicitly diverge at n=108: 35 versus 70.

**Novelty.** A389087 explicitly identifies the first difference from A344696 at n=108. No equality is asserted.

**Integrity and other gates.** At 108, sigma=280, Dedekind psi=216, and the sum of squarefree divisors is 12. Thus the respective numerators are 280/gcd(280,216)=35 and 280/gcd(280,12)=70. The definitions and listed mismatch are consistent.

Sources: [A344696](https://oeis.org/A344696) [A389087](https://oeis.org/A389087)

## Candidate 123: A007094 vs A039155 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/1. Same-index equality has zero initial matches: A007094(1)=1 while A039155(1)=0. Even after correcting the positional alignment to A007094(n)=A039155(n+1), there are only 64 matches, n=0..63; A007094(64)=100 but A039155(65)=89.

**Novelty.** Neither record asserts the proposed equality. This absence is not evidence of novelty: the candidate is directly false in its live listed data.

**Integrity and other gates.** Before 89, eligible decimal numbers have no 8 or 9 and imitate octal digit strings. The value 89 introduces one of each digit and is allowed by A039155, but cannot be an octal digit string. Independent enumeration reproduces the mismatch.

Sources: [A007094](https://oeis.org/A007094) [A039155](https://oeis.org/A039155)

## Candidate 124: A088828 vs A348741 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 64 common listed matches. Independent enumeration agrees for 1079 terms and first differs at n=1080: 2205 versus 2207.

**Novelty.** A348741 explicitly publishes this first difference and identifies itself as A088828 with A348743 removed. This is not an assertion of equality.

**Integrity and other gates.** 2205 is an odd nonsquare, but sigma(2205)=4446 has odd part 2223>2205, so it fails A348741’s defining inequality. The independently computed first failure agrees with the record.

Sources: [A088828](https://oeis.org/A088828) [A348741](https://oeis.org/A348741)

## Candidate 125: A213222 vs A265283 — DROP (novelty)

**Agreement and offsets.** Offsets 3/0; literal same-index comparison fails at n=3 (3 versus 6). The packet drops two terms from each positional list, giving 64 matches A213222(n+3)=A265283(n), n=2..65.

**Novelty.** A265283 explicitly conjectures a(n)=A213222(n+3) for n>1 (Colin Barker, 2015/2019). That precise shifted claim is already published.

**Integrity and other gates.** Both tails are elementary repeated even numbers. The boundary exception is real: A213222(3)=3, while its listed Magma code incorrectly uses 2*floor(3/2)=2 at n=3. The main formula correctly restricts that expression to n>3.

Sources: [A213222](https://oeis.org/A213222) [A265283](https://oeis.org/A265283)

## Candidate 126: A099564 vs A276153 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; 106 common listed matches. Independent mixed-radix evaluation agrees for n=0..209 (210 terms), then gives 7 versus 1 at n=210.

**Novelty.** Both records explicitly publish this first disagreement.

**Integrity and other gates.** The initial division radices coincide at 2,3,5, but the next Fibonacci radix is 8 and the next prime radix is 7. At 210, successive quotients leave a final nonzero 7 in the former system and 1 in the latter. The long common prefix comes from the shared initial radices.

Sources: [A099564](https://oeis.org/A099564) [A276153](https://oeis.org/A276153)

## Candidate 127: A276150 vs A341513 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; 106 common listed matches. Independent mixed-radix calculations agree for n=0..1889 (1890 terms) and first differ at n=1890: 9 versus 1.

**Novelty.** A341513 explicitly explains this agreement range and first failure relative to A276150.

**Integrity and other gates.** The place values first separate after 210: the odd-number-radix system next uses 1890=210*9, while the primorial system next uses 2310=210*11. Consequently 1890 has digit sum 1 versus 9. No all-n equality exists.

Sources: [A276150](https://oeis.org/A276150) [A341513](https://oeis.org/A341513)

## Candidate 128: A292592 vs A332996 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; 106 common listed matches. The freshly fetched b-files agree for n=0..510 (511 terms) and first differ at n=511: 171 versus 170.

**Novelty.** A332996 explicitly publishes that first disagreement with A292592. Its Cf. links are not treated as equality evidence.

**Integrity and other gates.** The published long-prefix claim was checked directly against both full b-files, not merely inferred from the short S/T/U lists. The b-file comparison is a stronger data check, not an independent proof of their underlying definitions.

Sources: [A292592](https://oeis.org/A292592) [A332996](https://oeis.org/A332996) [A292592/b292592.txt](https://oeis.org/A292592/b292592.txt) [A332996/b332996.txt](https://oeis.org/A332996/b332996.txt)

## Candidate 129: A328482 vs A371091 — DROP (data integrity)

**Agreement and offsets.** Offsets 0/0; 106 common listed matches. Independent definition-based calculations agree for n=0..359 (360 terms) and first differ at n=360: 1 versus 3.

**Novelty.** A371091 explicitly records this first failure relative to A328482 and gives its recursive decomposition at 360.

**Integrity and other gates.** 360=2*6*30 is itself a product of distinct primorials, so its greedy representation uses one distinct term. Its ordinary primorial expansion is 15000; recursively expanding digit 5 yields two ones in addition to the leading one, for a total of three.

Sources: [A328482](https://oeis.org/A328482) [A371091](https://oeis.org/A371091)

## Candidate 130: A133265 vs A275365 — DROP (novelty)

**Agreement and offsets.** Offsets 0/0; equality fails at n=0 (2 versus 0). Deleting both first terms produces 73 common listed matches at n=1..73.

**Novelty.** A275365 explicitly states that it is A133265 with its initial 2 replaced by 0. This exact exception-handled identity is already published.

**Integrity and other gates.** Two internal contradictions also require flags: A275365’s printed generating function has constant coefficient 2, contradicting a(0)=0; A133265’s Maple expression (n+2+(n-2)*(-1)^n)/2 gives 0 at n=0 and 2 at n=3, contradicting listed 2 and 4. The correct main formulas and data still describe an elementary interleaving, so none of these errors creates a survivor.

Sources: [A133265](https://oeis.org/A133265) [A275365](https://oeis.org/A275365)

## Candidate 131: A002324 vs A171774 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; 105 common listed matches. Comparing an independent divisor-formula implementation with the freshly fetched A171774 b-file verifies agreement for n=1..299, then 1 versus 0 at n=300.

**Novelty.** A171774 explicitly publishes that first disagreement with A002324. It does not assert their equality.

**Integrity and other gates.** For 300=2^2*3*5^2, the multiplicative divisor-difference formula gives A002324(300)=1; the radix-expansion b-file has 0. The 299-term match is a finite-prefix artifact. The radix b-file was checked as data; no independent transcendental-digit proof is claimed.

Sources: [A002324](https://oeis.org/A002324) [A171774](https://oeis.org/A171774) [A171774/b171774.txt](https://oeis.org/A171774/b171774.txt)

## Candidate 132: A004258 vs A029837 — DROP (novelty)

**Agreement and offsets.** Offsets 1/1; all 105 common listed terms agree at n=1..105.

**Novelty.** A004258’s name explicitly declares it a duplicate of A029837 and its keyword is dead. The identity is not a discovery.

**Integrity and other gates.** A029837’s correct defining function is ceiling(log_2(n)), but its printed recurrence a(2n+1)=a(n)+1 for n>1 is false: n=2 predicts a(5)=2, whereas the listed value and definition give 3. Its alternative recurrence using ceiling(n/2) is correct. A further displayed characterization n^(1/k-1)>2 is impossible for n>=1,k>=1. These are record errors, not grounds to retain a duplicate.

Sources: [A004258](https://oeis.org/A004258) [A029837](https://oeis.org/A029837)

## Candidate 133: A010476 vs A020762 — DROP (novelty)

**Agreement and offsets.** The `cons` offsets 1/0 encode different decimal-point positions. The 105 positional digit matches mean A010476(n)=A020762(n-1), n=1..105. A comparison using identical stored indices matches only n=1, then fails at n=2 (4 versus 7); this is bookkeeping, not a new mathematical discrepancy.

**Novelty.** A010476 explicitly states equivalence except for offset, and A020762 explicitly gives its constant as A010476/10 (January 14, 2021).

**Integrity and other gates.** sqrt(20)=10/sqrt(5), so these are the same digits with the decimal point shifted. This also fails interestingness as a trivial scale/offset relation. Correcting offsets does not produce a new constant identity.

Sources: [A010476](https://oeis.org/A010476) [A020762](https://oeis.org/A020762)

## Candidate 134: A025658 vs A025673 — DROP (data integrity)

**Agreement and offsets.** Offsets 1/1; all 105 common listed terms match. Exact integer heap enumeration agrees for n=1..2804 and first differs at n=2805: 0 versus 65.

**Novelty.** Both records explicitly publish the disagreement at a(2805) and link the index of sequences with long but finite agreement.

**Integrity and other gates.** The ordering of 4^i*6^j and 5^i*8^j eventually selects different exponents j. The counterexample was reproduced with exact products and ordering, without floating-point approximations.

Sources: [A025658](https://oeis.org/A025658) [A025673](https://oeis.org/A025673)

## Candidate 135: A046978 vs A075553 — DROP (interestingness)

**Agreement and offsets.** Offsets 0/0; absolute values agree throughout all 105 common listed terms. Signed equality lasts two terms and fails at n=2: 1 versus -1.

**Novelty.** No explicit pairwise equality was found in either record. Both complete period-8 formulas are already given, determining their shared absolute-value pattern; no claim of an unpublished identity is warranted.

**Integrity and other gates.** Their absolute values are simply the period-4 block [0,1,1,1]. The relation is also A075553(n)=(-1)^(n+1)*A046978(n). This is a sign/abs transform of short-period sequences, expressly excluded by gate 2. The checked periodic formulas agree with the data.

Sources: [A046978](https://oeis.org/A046978) [A075553](https://oeis.org/A075553)
## Candidate 136: A052409 vs A327503 — DROP (data integrity)

**Agreement.** Offsets: A052409 starts at 1, A327503 at 1. The packet transformation gives 105 matched raw values from (A052409 index 1, A327503 index 1); the shorter displayed list ends there.

**Novelty.** The A327503 comment explicitly says this pair first differs at 216; its mention of A052409 is a published nonidentity, not an equality claim.

**Decision and integrity.** The 105 displayed common terms conceal a finite-prefix coincidence. Independent factorization/divisor iteration verifies exactly 215 common terms, n=1..215, then A052409(216)=3 and A327503(216)=2. 216=6^3, so its largest perfect-power exponent is 3. The quotient iteration instead gives 216→2→1, since 108 is the largest divisor of 216 that is not a perfect power. No contradiction between these definitions and their own lists; the proposed infinite identity is false.

Sources: [A052409](https://oeis.org/A052409), [A327503](https://oeis.org/A327503).

## Candidate 137: A069158 vs A359155 — DROP (interestingness)

**Agreement.** Offsets: A069158 starts at 1, A359155 at 1. The packet transformation gives 105 matched absolute values from (A069158 index 1, A359155 index 1); the shorter displayed list ends there.

**Novelty.** No direct equality between these two IDs is asserted in the inspected records. A069158 explicitly gives |a(n)|=|mu(n)|; A359155 publishes a(n)=mu(n)·A359154(n), with A359154 taking only ±1. These already explain the shared squarefree support.

**Decision and integrity.** The proposed equality is merely equality after erasing signs: both absolute values are the indicator of squarefree integers. The original sequences disagree at n=3: −1 versus 1. The multiplicative prime-power formula for A359155 gives magnitude 1 on squarefree integers and 0 otherwise. It is consistent with the displayed values; no offset issue.

Sources: [A069158](https://oeis.org/A069158), [A359155](https://oeis.org/A359155).

## Candidate 138: A077267 vs A081602 — DROP (novelty)

**Agreement.** Offsets: A077267 starts at 0, A081602 at 0. The packet transformation gives 105 matched raw values from (A077267 index 0, A081602 index 0); the shorter displayed list ends there.

**Novelty.** A081602 explicitly states “Duplicate of A077267” and has keyword dead. Both definitions count zero digits in ternary notation.

**Decision and integrity.** An explicitly identified duplicate cannot be an unpublished identity. Both offsets are 0. Their first 105 displayed values agree at n=0..104, including the convention a(0)=1. A077267 contains one further displayed value; there is no comparison beyond the shorter list.

Sources: [A077267](https://oeis.org/A077267), [A081602](https://oeis.org/A081602).

## Candidate 139: A083650 vs A138514 — DROP (novelty)

**Agreement.** Offsets: A083650 starts at 0, A138514 at 0. The packet transformation gives 105 matched absolute values from (A083650 index 0, A138514 index 0); the shorter displayed list ends there.

**Novelty.** Both records explicitly state that A030204, A083650 and A138514 are the same except for signs (Sloane, May 7, 2010).

**Decision and integrity.** The precise absolute-value relationship being mined has already been asserted on both records; it also fails the ban on trivial sign changes. Both offsets are 0; absolute values agree for all 105 displayed positions. Raw values first differ at n=1: −1 versus 1. No additional contradiction was identified in the formulas used for this verdict.

Sources: [A083650](https://oeis.org/A083650), [A138514](https://oeis.org/A138514).

## Candidate 140: A093829 vs A113447 — DROP (novelty)

**Agreement.** Offsets: A093829 starts at 1, A113447 at 1. The packet transformation gives 105 matched absolute values from (A093829 index 1, A113447 index 1); the shorter displayed list ends there.

**Novelty.** Both records publish the exact relation A093829(n)=−(−1)^n·A113447(n), dated January 31, 2015.

**Decision and integrity.** The absolute-value match is a published parity sign change. Both offsets are 1; 105 displayed absolute values match. Raw values first differ at n=2: −1 versus 1. There is also a nonessential numerical error in A113447: its asymptotic-mean line equates Pi/(6·sqrt(3)) to 0.604599..., whereas that expression is 0.302299...; this does not rescue novelty.

Sources: [A093829](https://oeis.org/A093829), [A113447](https://oeis.org/A113447).

## Candidate 141: A099443 vs A132342 — DROP (interestingness)

**Agreement.** Offsets: A099443 starts at 0, A132342 at 1. The packet transformation gives 105 matched absolute values from (A099443 index 0, A132342 index 1); the shorter displayed list ends there.

**Novelty.** Neither record asserts a pairwise equality. A099443 publishes a(n+5)=−a(n), and A132342 explicitly states that it becomes period 5 at a(13). These published descriptions expose the elementary periodic pattern.

**Decision and integrity.** After respecting offsets, the mined statement is |A099443(n)|=|A132342(n+1)|. Both magnitudes repeat 1,1,1,1,0. This is an offset shift plus sign erasure of short-period sequences. Offsets are 0 and 1. The 105-position agreement compares A099443(0..104) with A132342(1..105), not equal indices. At equal indices only n=1..3 match before n=4 gives 0 versus 1; even their absolute values differ there. No contradiction with either recurrence is needed.

Sources: [A099443](https://oeis.org/A099443), [A132342](https://oeis.org/A132342).

## Candidate 142: A101871 vs A101875 — DROP (novelty)

**Agreement.** Offsets: A101871 starts at 0, A101875 at 0. The packet transformation gives 105 matched raw values from (A101871 index 0, A101875 index 0); the shorter displayed list ends there.

**Novelty.** A101875 is named “Duplicate of A101871” and has keyword dead. A101871 explicitly gives a(n)=A000688(2n+1)=A000688(4n+2).

**Decision and integrity.** The former definitions—Abelian groups of odd order 2n+1 and of order 4n+2—are already equated in the surviving record. Offsets are both 0 and all 105 common displayed terms agree at n=0..104. The extra prime factor 2 has exponent 1 and contributes only the unique group of order 2, consistent with the equality.

Sources: [A101871](https://oeis.org/A101871), [A101875](https://oeis.org/A101875).

## Candidate 143: A103391 vs A331743 — DROP (data integrity)

**Agreement.** Offsets: A103391 starts at 1, A331743 at 0. The packet transformation gives 105 matched raw values from (A103391 index 1, A331743 index 0); the shorter displayed list ends there.

**Novelty.** Both records explicitly publish the failure of the shifted equality at A103391(192)=97 versus A331743(191)=23. This is affirmative evidence against the proposed identity, not a mere cross-reference.

**Decision and integrity.** The packet suppresses an offset difference and then stops before a known counterexample. Independent computation from the restricted-growth definition verifies exactly 191 shifted common terms: A103391(n+1)=A331743(n) for n=0..190, then failure at n=191. Offsets are 1 and 0. At equal indices there are zero common initial terms: A103391(1)=1 but A331743(1)=2. The advertised 105 terms compare A103391(1..105) with A331743(0..104). Computation of A331743 additionally used the freshly fetched A323901 code for A002487(A163511(n)).

Sources: [A103391](https://oeis.org/A103391), [A331743](https://oeis.org/A331743), [A323901](https://oeis.org/A323901).

## Candidate 144: A106459 vs A143433 — DROP (interestingness)

**Agreement.** Offsets: A106459 starts at 0, A143433 at 0. The packet transformation gives 105 matched absolute values from (A106459 index 0, A143433 index 0); the shorter displayed list ends there.

**Novelty.** No direct pairwise identity is asserted in the two inspected records. A106459 explicitly gives |a(n)|=A010054(n), the triangular-number indicator; A143433 publishes a sum with one ±1 coefficient at each exponent k(k+1)/2.

**Decision and integrity.** Erasing signs leaves the same elementary triangular-number support. This follows immediately from the displayed sparse series and is a trivial absolute-value transform under the stated gate. Offsets are both 0. All 105 displayed absolute values match; raw values first differ at n=3: −1 versus 1. Distinct triangular exponents prevent hidden cancellation in the displayed series.

Sources: [A106459](https://oeis.org/A106459), [A143433](https://oeis.org/A143433).

## Candidate 145: A106510 vs A163804 — DROP (novelty)

**Agreement.** Offsets: A106510 starts at 0, A163804 at 0. The packet transformation gives 105 matched absolute values from (A106510 index 0, A163804 index 0); the shorter displayed list ends there.

**Novelty.** A163804 explicitly states a(n)=−A106510(n) for n>0, both in a formula and in the cross-references.

**Decision and integrity.** This is an already-published sign reversal, with a common exceptional initial value. Both tails have period 3. Offsets are both 0. Absolute values match for 105 displayed terms. At n=0 both equal 1; raw values first differ at n=1: 1 versus −1. The two rational generating functions sum to 2, confirming the stated exception and tail sign reversal.

Sources: [A106510](https://oeis.org/A106510), [A163804](https://oeis.org/A163804).

## Candidate 146: A109017 vs A110161 — DROP (interestingness)

**Agreement.** Offsets: A109017 starts at 0, A110161 at 0. The packet transformation gives 105 matched absolute values from (A109017 index 0, A110161 index 0); the shorter displayed list ends there.

**Novelty.** The cross-references list quadratic characters; they do not assert equality. The definitions already imply that the two absolute values are 1 exactly when gcd(n,6)=1, and 0 otherwise.

**Decision and integrity.** The mined absolute-value sequence is the period-6 pattern 0,1,0,0,0,1. Both original characters have short periods (24 and 12). This fails the explicit short-period and sign-erasure exclusions. Offsets are both 0. All 105 displayed absolute values match, while raw values first differ at n=5: 1 versus −1. The common zero set is consistent with the Kronecker/Dirichlet-character definitions.

Sources: [A109017](https://oeis.org/A109017), [A110161](https://oeis.org/A110161).

## Candidate 147: A113446 vs A121450 — DROP (novelty)

**Agreement.** Offsets: A113446 starts at 1, A121450 at 1. The packet transformation gives 105 matched absolute values from (A113446 index 1, A121450 index 1); the shorter displayed list ends there.

**Novelty.** A121450 explicitly states “Apart from signs, same as A035154 and A113446.” It also gives A035154(n)=|a(n)|; A113446 publishes its sign relation to A035154.

**Decision and integrity.** The exact absolute-value equality has already been asserted. The prime-power formulas show that the records differ only by a parity sign. Offsets are both 1. There are 105 common displayed absolute values. Raw values first differ at n=2: 1 versus −1. No inconsistency was found in the compared terms or prime-power rules.

Sources: [A113446](https://oeis.org/A113446), [A121450](https://oeis.org/A121450).

## Candidate 148: A113661 vs A113974 — DROP (interestingness)

**Agreement.** Offsets: A113661 starts at 1, A113974 at 1. The packet transformation gives 105 matched absolute values from (A113661 index 1, A113974 index 1); the shorter displayed list ends there.

**Novelty.** Neither inspected record expressly states an equality to the other ID. Each publishes its full multiplicative prime-power rule, which makes the relationship an immediate sign-only change at the prime 2.

**Decision and integrity.** Writing n=2^e·m with m odd, the formulas give A113974(n)=(−1)^e·A113661(n). For e>0, A113661 has 2-power factor (1−3(−1)^e)/2 and A113974 has ((−1)^e−3)/2; all odd-prime factors coincide. This is a trivial valuation-dependent sign change. Offsets are both 1. All 105 displayed absolute values agree; raw values first differ at n=2: 2 versus −2. The e=0 case uses a(1)=1, as appropriate for multiplicative functions, rather than applying a prime-power rule outside its positive-exponent domain.

Sources: [A113661](https://oeis.org/A113661), [A113974](https://oeis.org/A113974).

## Candidate 149: A121373 vs A199918 — DROP (novelty)

**Agreement.** Offsets: A121373 starts at 0, A199918 at 0. The packet transformation gives 105 matched absolute values from (A121373 index 0, A199918 index 0); the shorter displayed list ends there.

**Novelty.** A121373 publishes a(n)=(−1)^n·A010815(n). A199918 explicitly publishes |a(n)|=|A010815(n)|. Thus the mined equality of absolute values is already asserted through the same named sequence.

**Decision and integrity.** Both are sign decorations of Euler-pentagonal support; the common absolute-value identity is published, not a new target. Offsets are both 0; 105 displayed absolute values match, but raw values first differ at n=2: −1 versus 1. Important internal contradictions in A199918: its bilateral sum over all integers k of x^((k²−1)/24)·Kronecker(−24,k) has constant coefficient 1+(−1)=0 from k=±1, whereas a(0)=1. Also its negative prime-residue list contains 29 mod 24, overlapping the positive class 5 and omitting 19; at n=35, 24n+1=29², that negative branch gives −1 while the list and executable formula give +1. These are formula errors, not evidence against the separately published absolute-value relation.

Sources: [A121373](https://oeis.org/A121373), [A199918](https://oeis.org/A199918).

## Candidate 150: A143064 vs A185124 — DROP (interestingness)

**Agreement.** Offsets: A143064 starts at 0, A185124 at 0. The packet transformation gives 105 matched absolute values from (A143064 index 0, A185124 index 0); the shorter displayed list ends there.

**Novelty.** No direct pairwise equality is asserted in the two inspected records. A143064 explicitly identifies its absolute values with A089801; both records give executable square tests, so the same simple support is already explicit in their formulas.

**Decision and integrity.** Both sequences vanish unless 3n+1=m², and otherwise equal ±1: A143064 uses (−1)^floor(m/3), while A185124 uses (−1)^floor((m+3)/6). Their absolute-value match discards only these signs. Offsets are both 0. All 105 displayed absolute values match, with the first raw difference at n=16: 1 versus −1. A143064 has a literal formula/list contradiction: its first displayed sum has product over j=0..k of (1+x^(2k+1)); the k=0 and k=2 terms each contribute 1 to x², yielding a(1)=2 instead of the listed 1. The later QPochhammer code instead uses the running odd exponents 2j+1. This typo must not be silently treated as a verified formula.

Sources: [A143064](https://oeis.org/A143064), [A185124](https://oeis.org/A185124).

## Candidate 151: A143259 vs A359818 — DROP (novelty)

**Agreement.** Offsets: A143259 starts at 1, A359818 at 1. The packet transformation gives 105 matched absolute values from (A143259 index 1, A359818 index 1); the shorter displayed list ends there.

**Novelty.** A143259 explicitly states |a(n)|=A053866(n). A359818 identifies A053866 as its “parity and the absolute values,” which is a qualified equality assertion, stronger than an unqualified Cf.

**Decision and integrity.** The common absolute values are explicitly assigned to the same sequence; they indicate squares or twice squares. The remaining difference is a prime-factor-dependent sign. Offsets are both 1. All 105 displayed absolute values match. Raw equality stops after n=8, with n=9 giving 1 versus −1. A359818 has magnitudes 1 exactly when every odd-prime exponent is even, consistent with square-or-twice-square support.

Sources: [A143259](https://oeis.org/A143259), [A359818](https://oeis.org/A359818).

## Candidate 152: A156277 vs A365428 — DROP (novelty)

**Agreement.** Offsets: A156277 starts at 1, A365428 at 1. The packet transformation gives 105 matched absolute values from (A156277 index 1, A365428 index 1); the shorter displayed list ends there.

**Novelty.** A156277 explicitly diagrams A156277 --abs--> A359377 and labels A359377 “absolute values.” A365428 likewise labels A359377 “absolute values.” These are explicit common-target assertions, not generic cross-references.

**Decision and integrity.** Both absolute-value sequences are the squarefree indicator with multiples of 3 excluded, already identified as A359377. Offsets are both 1; 105 displayed absolute values match. Raw values first differ at n=2: −1 versus 1. The formulas −mu(3n) and the inverse-character prime-power rules agree with this support; the Legendre notation in the latter is interpreted with the character’s stated value at 2, confirmed by the listed terms.

Sources: [A156277](https://oeis.org/A156277), [A365428](https://oeis.org/A365428).

## Candidate 153: A163812 vs A163818 — DROP (novelty)

**Agreement.** Offsets: A163812 starts at 0, A163818 at 0. The packet transformation gives 105 matched absolute values from (A163812 index 0, A163818 index 0); the shorter displayed list ends there.

**Novelty.** Both records explicitly publish a(n)=(−1)^n times the other sequence.

**Decision and integrity.** The absolute-value match is an already-known alternating sign change. The tails also have periods 10 and 5. Offsets are both 0. All 105 displayed absolute values agree; raw values first differ at n=1: 1 versus −1. Their rational generating functions are related by x→−x, consistent with the listed relation.

Sources: [A163812](https://oeis.org/A163812), [A163818](https://oeis.org/A163818).

## Candidate 154: A164116 vs A164118 — DROP (novelty)

**Agreement.** Offsets: A164116 starts at 0, A164118 at 0. The packet transformation gives 105 matched absolute values from (A164116 index 0, A164118 index 0); the shorter displayed list ends there.

**Novelty.** A164116 explicitly gives a(n)=(−1)^n·A164118(n); A164118 repeats the same relation in its cross-references.

**Decision and integrity.** A published alternating sign transform of an eventually period-5 sequence fails novelty and interestingness. Offsets are both 0; 105 displayed absolute values agree. Raw values first differ at n=1: −1 versus 1. The generating functions are related by substituting −x, including the exceptional initial term in the periodic descriptions.

Sources: [A164116](https://oeis.org/A164116), [A164118](https://oeis.org/A164118).

## Candidate 155: A209927 vs A223139 — DROP (novelty)

**Agreement.** Offsets: A209927 starts at 1, A223139 at 1. The packet transformation gives 105 matched raw values from (A209927 index 2, A223139 index 2); the shorter displayed list ends there.

**Novelty.** A223139 expressly states that apart from a(1) it is the same as A209927, and gives its constant as A209927−1. It also states that replacing its first digit by 2 yields A209927.

**Decision and integrity.** The constants (sqrt(13)+1)/2 and (sqrt(13)−1)/2 differ by the integer 1, so their decimal fractional digits coincide. This is an explicitly published initial-digit deletion. Both offsets are 1. The raw sequences disagree immediately: integer digits 2 and 1. Deleting the first term from both gives 105 matched digits at indices 2..106; this is not a shift of one sequence alone.

Sources: [A209927](https://oeis.org/A209927), [A223139](https://oeis.org/A223139).

## Candidate 156: A290110 vs A300250 — DROP (data integrity)

**Agreement.** Offsets: A290110 starts at 1, A300250 at 1. The packet transformation gives 105 matched raw values from (A290110 index 1, A300250 index 1); the shorter displayed list ends there.

**Novelty.** A290110 explicitly states that it differs from A300250 for the first time at n=858, with values 115 and 75. A300250 repeats the first-disagreement claim. Neither asserts an infinite equality.

**Decision and integrity.** Independent enumeration of divisor factorization patterns versus divisor prime-signature patterns confirms exactly 857 matched terms, n=1..857, then 115 versus 75 at n=858. Both offsets are 1; the displayed 105 terms are correct but truncated before failure. The full factorization pattern remembers which prime symbols appear in each divisor; the prime-signature pattern forgets those identities. The two definitions are genuinely different, consistently with their records.

Sources: [A290110](https://oeis.org/A290110), [A300250](https://oeis.org/A300250).

## Candidate 157: A305979 vs A334868 — DROP (data integrity)

**Agreement.** Offsets: A305979 starts at 1, A334868 at 1. The packet transformation gives 63 matched raw values from (A305979 index 1, A334868 index 1); the next values are 42 and 6.

**Novelty.** A334868 gives only a one-way implication between the equivalence relations defined by these sequences. That statement is not an equality claim; the generic Cf. is not novelty evidence either.

**Decision and integrity.** The advertised prefix already ends at a counterexample inside the two displayed lists: exactly 63 terms agree, then A305979(64)=42 and A334868(64)=6. Independent implementation reproduces this failure. Both offsets are 1. A334870(12)=8=A334870(64), so the restricted-growth transform reuses the label 6 at 64. A305979 assigns successive new labels to each number outside the Fermi-Dirac primes, hence 42. There is no infinite identity.

Sources: [A305979](https://oeis.org/A305979), [A334868](https://oeis.org/A334868).

## Candidate 158: A351454 vs A351460 — DROP (data integrity)

**Agreement.** Offsets: A351454 starts at 1, A351460 at 1. The packet transformation gives 105 matched raw values from (A351454 index 1, A351460 index 1); the shorter displayed list ends there.

**Novelty.** Both records explicitly state their first disagreement at n=121: A351454(121)=51, A351460(121)=62.

**Decision and integrity.** Independent restricted-growth computations using the published auxiliary triples confirm exactly 120 common terms, n=1..120, and the published failure at 121. Offsets are both 1. The packet’s 105 displayed values hide this near-future failure. A351454 merges 99 and 121 because their largest prime factor and both iteration counts agree; A351460 distinguishes the corresponding odd squarefree-divisor sum and odd excess-power data. No formula/list inconsistency is needed: the identity itself is false.

Sources: [A351454](https://oeis.org/A351454), [A351460](https://oeis.org/A351460).

## Candidate 159: A030205 vs A159817 — DROP (novelty)

**Agreement.** Offsets: A030205 starts at 0, A159817 at 0. The packet transformation gives 72 matched absolute values from (A030205 index 0, A159817 index 0); the shorter displayed list ends there.

**Novelty.** A030205 explicitly publishes a(n)=(−1)^n·A159817(n), dated June 10, 2015; A159817 publishes the reciprocal relation.

**Decision and integrity.** The absolute-value relationship between the two modular-form coefficient lists is a known parity twist, not a new identity. Offsets are both 0. The shorter A030205 list permits 72 absolute-value comparisons, n=0..71, all matching. Raw values first differ at n=1: −2 versus 2. The published product generating functions are directly related by x→−x.

Sources: [A030205](https://oeis.org/A030205), [A159817](https://oeis.org/A159817).

## Candidate 160: A115633 vs A115713 — DROP (interestingness)

**Agreement.** Offsets: A115633 starts at 0, A115713 at 0. The packet transformation gives 120 matched absolute values from (A115633 index 0, A115713 index 0); the shorter displayed list ends there.

**Novelty.** Neither inspected record explicitly names the other as an equal sequence. Their published triangle formulas, however, immediately give T115713(r,k)=(−1)^r·T115633(r,k). The shared row-sum reference alone is not used as an equality claim.

**Decision and integrity.** This is simply an alternating row-sign change. The −4 entries occur only in even rows, diagonal signs are reversed in odd rows, and the odd-row subdiagonal changes from +1 to −1. Offsets are both 0. Flattening rows 0..14 gives all 120 advertised absolute-value matches. The original flattened values disagree already at index 1: 1 versus −1. The bivariate generating functions are related by x→−x, verifying the sign relation for the entire triangles.

Sources: [A115633](https://oeis.org/A115633), [A115713](https://oeis.org/A115713).

JUDGE COMPLETE
