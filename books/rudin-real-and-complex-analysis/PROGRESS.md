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
| 10 | Elementary Properties of Holomorphic Functions | 44 | 0 |
| 11 | Harmonic Functions | 32 | 0 |
| 12 | The Maximum Modulus Principle | 14 | 0 |
| 13 | Approximation by Rational Functions | TBD | 0 |
| 14 | Conformal Mapping | TBD | 0 |
| 15 | Zeros of Holomorphic Functions | TBD | 0 |
| 16 | Analytic Continuation | TBD | 0 |
| 17 | Hp-Spaces | TBD | 0 |
| 18 | Some Applications of the Phragmén–Lindelöf Method | TBD | 0 |
| 19 | Entire Functions | TBD | 0 |
| 20 | Boundary Behavior of Bounded Analytic Functions | TBD | 0 |

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

Cluster E's [inventory](inventory/README.md) verifies all 90 numbered nodes
of Chapters 10–12 against the third-edition scan. Unnumbered corollaries and
assertions belong to their numbered parent; exercises are excluded.
The `Done` column continues to mean accepted on main, so it is not advanced
by unreviewed work on `books/rca-holomorphic`. Branch proof coverage and
fidelity stops are recorded separately in the inventory and `QUEUE.md`.

Branch checkpoint, 2026-11-01 (unreviewed; ticket #41):

| Chapter | Inventoried | Complete nodes proved on branch | Remaining |
|---|---:|---:|---:|
| 10 | 44 | 16 | 28 |
| 11 | 32 | 4 | 28 |
| 12 | 14 | 3 | 11 |
| **Cluster E** | **90** | **23** | **67** |

Chapter 10 completion is enumerated in its inventory; Chapter 11 covers
11.1–11.4, and Chapter 12 covers 12.2, 12.3, and 12.9. Partial nodes and
the corrected subclaim of 11.5 do not inflate these counts. This is a
draft delivery: the Chapter 10 path/index machinery and the 10.37 fidelity
hold remain open. `scripts/build-cluster-e-clean.py` verifies the current
sources in a fresh output directory, retaining existing work and artifacts.
