# Progress — Rudin, *Real and Complex Analysis*

Node counts are established by each cluster's inventory pass (Stage 1 of
its ticket) and updated as chapters land. "Done" means proved at the bar
(zero sorries, standard axioms, faithful statement) on main.

| Chapter | Title | Nodes (total) | Done |
|---|---|---|---|
| 1 | Abstract Integration | 41 | 0 |
| 2 | Positive Borel Measures | 25 | 0 |
| 3 | Lp-Spaces | 17 | 0 |
| 4 | Elementary Hilbert Space Theory | 26 | 0 |
| 5 | Examples of Banach Space Techniques | 25 | 0 |
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

## Cluster A inventory (branch `books/rca-foundations`)

The complete verified ranges are 1.1–1.41, 2.1–2.25, and 3.1–3.17: **83
numbered items**, including definitions and exposition. Of these, **49 are
tracked theorem/proposition groups** (25 / 14 / 10). Assertions accompanying
definitions are also obligations of their numbered items. Attached unnumbered
corollaries are obligations of the parent group, not extra numbered items.
The `Done` column above continues to mean accepted on main; branch proofs
are reported separately and never equated with accepted completion.

| Chapter | Inventoried | Result groups | Numbering unverified | Inventory and claims |
|---|---:|---:|---:|---|
| 1 | 41 | 25 | 0 | [Chapter 1](INVENTORY-CH01.md) |
| 2 | 25 | 14 | 0 | [Chapter 2](INVENTORY-CH02.md) |
| 3 | 17 | 10 | 0 | [Chapter 3](INVENTORY-CH03.md) |

These counts verify identifiers, not the correctness or formalization of
every statement. Section 3.7 has a disclosed zero-measure fidelity hold;
see [QUEUE.md](QUEUE.md). No exercise is included.

## Cluster A formalization on this branch (independent review pending)

| Chapter | Inventoried | Formalized items | Remaining original items | Proved result groups / total |
|---|---:|---:|---:|---:|
| 1 | 41 | 41 | 0 | 25 / 25 |
| 2 | 25 | 14 | 11 | 7 / 14 |
| 3 | 17 | 0 | 17 | 0 / 10 |
| Total | 83 | 55 | 28 | 32 / 49 |

Chapter 2 covers 2.1, 2.3–2.13, and 2.15–2.16, including definition
assertions, notation 2.11, and attached corollaries. The consequences in
2.16 retain the required measure hypotheses from 2.14 explicitly; the
representation theorem 2.14 remains pending. Chapter 3
contains four proved results: a counterexample and three facts about the
explicit repair of 3.7, but no original numbered item is counted complete. Of its 17
remaining items, 3.7 is held for a fidelity ruling and 16 are deferred.
The `Done` column in the main table remains zero because no merge occurred.
