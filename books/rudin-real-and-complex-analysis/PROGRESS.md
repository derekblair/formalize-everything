# Progress — Rudin, *Real and Complex Analysis*

Node counts are established by each cluster's inventory pass (Stage 1 of
its ticket) and updated as chapters land. "Done" means proved at the bar
(zero sorries, standard axioms, faithful statement) on main.

| Chapter | Title | Nodes (total) | Done |
|---|---|---|---|
| 1 | Abstract Integration | TBD | 0 |
| 2 | Positive Borel Measures | TBD | 0 |
| 3 | Lp-Spaces | TBD | 0 |
| 4 | Elementary Hilbert Space Theory | TBD | 0 |
| 5 | Examples of Banach Space Techniques | TBD | 0 |
| 6 | Complex Measures | TBD | 0 |
| 7 | Differentiation | TBD | 0 |
| 8 | Integration on Product Spaces | 18 | 0 |
| 9 | Fourier Transforms | 23 | 0 |
| 10 | Elementary Properties of Holomorphic Functions | TBD | 0 |
| 11 | Harmonic Functions | TBD | 0 |
| 12 | The Maximum Modulus Principle | TBD | 0 |
| 13 | Approximation by Rational Functions | TBD | 0 |
| 14 | Conformal Mapping | TBD | 0 |
| 15 | Zeros of Holomorphic Functions | TBD | 0 |
| 16 | Analytic Continuation | TBD | 0 |
| 17 | Hp-Spaces | TBD | 0 |
| 18 | Some Applications of the Phragmén–Lindelöf Method | TBD | 0 |
| 19 | Entire Functions | TBD | 0 |
| 20 | Boundary Behavior of Bounded Analytic Functions | TBD | 0 |

## Cluster D development branch

The independently reconstructed [inventory](SCOPING-D.md) counts 18 Chapter 8 nodes and
23 Chapter 9 nodes (41 total); no separately produced Stage 1 inventory was received.
[Chapter 9 claims](CLAIMS-D-CH09.md) record the precise Fourier normalization and known
adaptation gaps. No numeric count in issue #40 conflicts with these counts.

This branch is **in progress**. The complete Chapter 8 module (all 18 numbered
nodes, 177 public declarations) passed its integrated full Lake build on
2026-10-29, with 2838 jobs and unchanged Lean/Mathlib pins. Final clean-slate
build and all-declaration axiom audit are pending; no completed chapter is
claimed before those gates. Chapter 9 formalization waits for Chapter 8.
Main's Done counts remain zero. No independent review or merge is claimed.
