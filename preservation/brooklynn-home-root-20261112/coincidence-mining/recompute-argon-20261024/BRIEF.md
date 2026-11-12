# BRIEF — Independent recomputation of candidates C36 and C2 (verification lane)

You are an independent verification lane for a mathematics programme. Two other lanes will do (or have done) the same work from the same brief; your value is independence — write your own code from the definitions below, do not look for other lanes' results. Use Python 3 standard library only (fractions, decimal, math) so the work is reproducible anywhere. Put every deliverable in THIS task directory.

## Task A — C36: cellular automaton vs powers of 2

Definitions (from the OEIS records' definition lines, not from their listings):
- A267579(n): the centre cell at step n of the elementary cellular automaton Rule 167 started from a single ON cell on an all-zero background. Rule 167 neighbourhood outputs (for neighbourhoods 111, 110, 101, 100, 011, 010, 001, 000) are 1, 0, 1, 0, 0, 1, 1, 1. Offset: n starts at 0.
- A347523(n): 1 if n is not a power of 2, else 0 (with a(0) = 1 by convention; n is a power of 2 iff n >= 1 and n AND (n-1) = 0).

Pinned claim under test: for all n >= 2, A267579(n) = A347523(n). (The unrestricted claim fails at n = 1 by the definitions; do not treat that as a mismatch.)

Compute both sides independently to N = 2000. Compare on 2 <= n <= 2000.

Deliverable `result-C36.json` with fields: {"candidate": "C36", "compared_to": 2000, "domain": "n>=2", "mismatches": <int>, "first_mismatch": <n or null>, "verdict": "AGREE_TO_2000" or "MISMATCH"}.

## Task B — C2: the sign of Maslanka's coefficients

Definition (Maslanka 1997, arXiv:math-ph/0105007; also A355437's own formula line): for n >= 0,
A(n) = Sum_{j=0..n} (-1)^j * binomial(n, j) * (2j+1) * zeta(2j+2).

Compute A(n) for n = 0..300 at at least 200-digit precision. Suggested route: zeta(2k) = (-1)^(k+1) * B_{2k} * (2*pi)^(2k) / (2 * (2k)!), with Bernoulli numbers B_{2k} as exact fractions and pi computed to 250 digits (e.g. a Machin-like formula with decimal). Cross-check a sample of small n against the equivalent m-series A(n) = Sum_{m>=1} m^(-2) * (1 - m^(-2))^(n-1) * (1 - (2n+1)*m^(-2)) (truncate when terms fall below 10^(-220); skip or special-case n = 0). For every n, record |A(n)|: the sign counts as certified only if |A(n)| > 10^(-150) at the working precision; otherwise mark that n UNCERTAIN and say so.

Pinned claim under test: sign(A(n)) = -1 iff n = 1 (mod 8), else +1, for all n >= 0.

Also diagnose the listing: A355437's published listing (%S/%T/%U in the OEIS record) reads, for n = 0..29: 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 (fetch the record yourself for the rest if needed: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A355/A355437.seq). List every n <= 300 where the listing's sign differs from your computed sign.

Deliverable `result-C2.json` with fields: {"candidate": "C2", "computed_to": 300, "precision_digits": <int>, "pattern_holds": true/false, "first_pattern_break": <n or null>, "uncertain_n": [<list>], "listing_disagreements": [<list of n>], "signs_0_to_60": [<list of -1/0/1>], "min_abs_value": <string>, "crosscheck": "pass"/"fail + detail"}.

## Finish

Keep your script(s) in this directory (recompute.py or split files). Write `DONE.txt` whose last line is `RECOMPUTE COMPLETE`. If anything blocks you (missing tools, precision failures), write what you have, name the blocker in DONE.txt, and still end with RECOMPUTE COMPLETE so the collector can pick it up.
