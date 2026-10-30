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
| 8 | Integration on Product Spaces | TBD | 0 |
| 9 | Fourier Transforms | TBD | 0 |
| 10 | Elementary Properties of Holomorphic Functions | TBD | 0 |
| 11 | Harmonic Functions | TBD | 0 |
| 12 | The Maximum Modulus Principle | TBD | 0 |
| 13 | Approximation by Rational Functions | 12 | 0 |
| 14 | Conformal Mapping | 22 | 0 |
| 15 | Zeros of Holomorphic Functions | TBD | 0 |
| 16 | Analytic Continuation | TBD | 0 |
| 17 | Hp-Spaces | TBD | 0 |
| 18 | Some Applications of the Phragmén–Lindelöf Method | TBD | 0 |
| 19 | Entire Functions | TBD | 0 |
| 20 | Boundary Behavior of Bounded Analytic Functions | TBD | 0 |

## Cluster F working-branch status

The independent inventory in [SCOPING-F.md](SCOPING-F.md) counts all 34 numbered nodes: 13.1–13.12 and 14.1–14.22, including definitions and exposition with substantive assertions. No chapter is complete. The `Done` column above retains its stated meaning of proved and reviewed on main.

The ticket’s headline numbering differs from the printed third edition: Runge is 13.6/13.9; 13.10 is Mittag-Leffler; 13.12 is harmonicity of log modulus. Mergelyan is 20.5 and is outside this cluster. The forward dependency 13.11(j) → 14.8 is explicit in the book.

The working Chapter13 module contains the sphere topology and exact stereographic map, inverse-chart singularity definitions, bounded removability and polynomial principal parts at infinity, entire nonpolynomial essential singularities, and the full 13.12 log-modulus harmonicity statement. The combined module and umbrella build passed with48 allowed-axiom declaration audits on2026-10-29. This is an incremental branch checkpoint: neither a complete chapter nor the clean-slate PR gate. Further assertions of13.1 and the drafts for13.2 onward remain under verification. Partial assertions are not counted as completed numbered nodes.
