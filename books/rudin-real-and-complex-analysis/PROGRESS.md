# Progress — Rudin, *Real and Complex Analysis*

Node counts are established by each cluster's inventory pass (Stage 1 of
its ticket) and updated as chapters land. "Done" means proved at the bar
(zero sorries, standard axioms, faithful statement) on main.

| Chapter | Title | Nodes (total) | Done |
|---|---|---|---|
| 1 | Abstract Integration | TBD | 0 |
| 2 | Positive Borel Measures | TBD | 0 |
| 3 | Lp-Spaces | TBD | 0 |
| 4 | Elementary Hilbert Space Theory | 26 | 0 |
| 5 | Examples of Banach Space Techniques | 25 | 0 |
| 6 | Complex Measures | TBD | 0 |
| 7 | Differentiation | TBD | 0 |
| 8 | Integration on Product Spaces | TBD | 0 |
| 9 | Fourier Transforms | TBD | 0 |
| 10 | Elementary Properties of Holomorphic Functions | TBD | 0 |
| 11 | Harmonic Functions | TBD | 0 |
| 12 | The Maximum Modulus Principle | TBD | 0 |
| 13 | Approximation by Rational Functions | TBD | 0 |
| 14 | Conformal Mapping | TBD | 0 |
| 15 | Zeros of Holomorphic Functions | TBD | 0 |
| 16 | Analytic Continuation | TBD | 0 |
| 17 | Hp-Spaces | TBD | 0 |
| 18 | Elementary Theory of Banach Algebras | 21 (+ 3 local corollaries) | 0 |
| 19 | Holomorphic Fourier Transforms | 11 | 0 |
| 20 | Uniform Approximation by Polynomials | 5 | 0 |

Cluster B's counts come from a fresh printed-text enumeration in
[INVENTORY-B.md](INVENTORY-B.md): 4.1–4.26 and 5.1–5.25, including numbered
definitions and narrative/proof passages. See [SCOPING-B.md](SCOPING-B.md)
for conventions, corrected statements, and the closed-graph exercise scope
discrepancy. Stage 2 implementation and clean build/axiom gates for both cluster B chapters have passed on branch `rca-b-stage2-proton`;
the `Done` column continues to mean independently reviewed and landed on main.

## Cluster B branch gates

Both chapters passed their required clean-slate builds and axiom audits on
2026-11-01. The separate Chapter 4 gate passed before Chapter 5 compilation;
the final gate rebuilt and reaudited both modules from a fresh `.lake`.

| Module | Numbered nodes implemented | Theorem/lemma declarations | Audit records | Clean build / audit |
| --- | ---: | ---: | ---: | --- |
| `RudinRCA/Chapter04.lean` | 26/26 | 172 | 172 | PASS; [evidence](BUILD-CHAPTER04.md) |
| `RudinRCA/Chapter05.lean` | 25/25, including the printed strict 5.11 bound | 182 | 184 (includes two instances) | PASS; [F1 follow-up evidence](evidence/f1-gates.md) |

Each cache fetch, ordinary full build, and axiom checker exited 0. Both modules
have zero proof placeholders and only `propext`, `Classical.choice`, and
`Quot.sound` in their audited axiom unions. See the
[Chapter 4 coverage](CHAPTER04-COVERAGE.md),
[Chapter 5 coverage](CHAPTER05-COVERAGE.md), and
[statement disclosures](SCOPING-B.md).

PR: [#48](https://github.com/derekblair/formalize-everything/pull/48).
Coordinator-appointed crossed review is still required. The main table above
continues to count only independently reviewed work landed on main.

## Cluster H inventory and scope correction

Printed third-edition Chapters 18–20 have 37 top-level numbered nodes, plus
three locally numbered corollaries under 18.4. The previous titles, also present
in issue #44, do not match the printed edition. This branch follows the printed
chapter numbers and discloses the discrepancy; see [SCOPING-H.md](SCOPING-H.md).
No separate Stage 1 lane inventory was supplied. Counts here were independently
enumerated from the printed third-edition scan. Exercises are excluded.

The main-branch Done column remains zero until reviewed changes land. A
successful supporting lemma does not imply completion of its entire book node.
