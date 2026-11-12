# Progress — Rudin, *Real and Complex Analysis*

Node counts are established by each cluster's inventory pass (Stage 1 of
its ticket) and updated as chapters land. "Done" means proved at the bar
(zero sorries, standard axioms, faithful statement) on main.

| Chapter | Title | Nodes (total) | Done |
|---|---|---|---|
| 1 | Abstract Integration | 41 | 41 |
| 2 | Positive Borel Measures | 25 | 14 |
| 3 | Lp-Spaces | 17 | 0 |
| 4 | Elementary Hilbert Space Theory | 26 | 26 |
| 5 | Examples of Banach Space Techniques | 25 | 25 |
| 6 | Complex Measures | 19 | 8 |
| 7 | Differentiation | 26 | 24 |
| 8 | Integration on Product Spaces | 18 | 18 |
| 9 | Fourier Transforms | 23 | 0 |
| 10 | Elementary Properties of Holomorphic Functions | 44 | 0 |
| 11 | Harmonic Functions | 32 | 0 |
| 12 | The Maximum Modulus Principle | 14 | 0 |
| 13 | Approximation by Rational Functions | 12 | 0 |
| 14 | Conformal Mapping | 22 | 0 |
| 15 | Zeros of Holomorphic Functions | 27 | 0 |
| 16 | Analytic Continuation | 22 | 0 |
| 17 | Hp-Spaces | 26 | 0 |
| 18 | Elementary Theory of Banach Algebras | 21 (+ 3 local corollaries) | 0 |
| 19 | Holomorphic Fourier Transforms | 11 | 0 |
| 20 | Uniform Approximation by Polynomials | 5 | 0 |

Cluster A (Chapters 1–3) was recorded as Done on 2026-11-11 after
coordinator-appointed independent crossed review (PASS WITH ISSUES, zero
blocking findings) of the content as it stands on main; see FE #37.
Chapter 1: 41, Chapter 2: 14, Chapter 3: 0 (55/83 items, 32/49 result
groups) as independently reviewed-and-landed.

Cluster B's counts come from a fresh printed-text enumeration in
[INVENTORY-B.md](INVENTORY-B.md): 4.1–4.26 and 5.1–5.25, including numbered
definitions and narrative/proof passages. See [SCOPING-B.md](SCOPING-B.md)
for conventions, corrected statements, and the closed-graph exercise scope
discrepancy. Stage 2 implementation and clean build/axiom gates for both cluster B chapters have passed on branch `rca-b-stage2-proton`;
the `Done` column continues to mean independently reviewed and landed on main.
Cluster B (Chapters 4–5) was recorded as Done on 2026-11-11 after
coordinator-appointed independent crossed review (PASS WITH ISSUES, zero
blocking findings) of the content as it stands on main, with Chapter 4: 26
(26/26) and Chapter 5: 25 (25/25) — 51/51 items — as independently
reviewed-and-landed; see FE #38.

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
Coordinator-appointed crossed review passed (`PASS WITH ISSUES`, zero blocking findings; see FE #38) and PR [#79](https://github.com/derekblair/formalize-everything/pull/79) merged (`aba161c6`). The main table above
continues to count only independently reviewed work landed on main.

Cluster C independently enumerated 45 numbered nodes (6.1–6.19 and 7.1–7.26); see [SCOPING-C.md](SCOPING-C.md) for printed statements, pages, subclauses, pinned Mathlib claims checks, and uncovered obligations, and [COVERAGE-C.md](COVERAGE-C.md) for the live module ledger. `RudinRCA/Chapter06.lean` (`442` lines, blob `a7cbfb23ef0326a9f9222b1d098fc58839d6f58a`) is imported into the audited graph on `main` (`FE #82`, PR #84), proving **8/19** complete Chapter 6 nodes (`6.1`, `6.2`, `6.4`, `6.5`, `6.6`, `6.7`, `6.8`, `6.17`) at the programme bar (`Done: 8` after coordinator-appointed crossed review); `RudinRCA/Chapter07.lean` (`5,393` lines, blob `23a686de561f79fc7a3f1d7ff43f8d66e10b2686`) is wired into the audited graph for `FE #86` (FE #86, PR #89, crossed review PASS), proving **24/26** complete Chapter 7 nodes (`7.1`–`7.22`, `7.25`, `7.26`) at the programme bar (`Done: 24`, bringing the main-table `Done` sum from `132/456` on `main` to `156/456`); the remaining `11/19` Chapter 6 nodes (`6.3`, `6.9`–`6.16`, `6.18`, `6.19`) and `2/26` Chapter 7 gap nodes (`7.23`, `7.24`) remain pending.

## Cluster D development branch

The independently reconstructed [inventory](SCOPING-D.md) counts 18 Chapter 8 nodes and
23 Chapter 9 nodes (41 total); no separately produced Stage 1 inventory was received.
[Chapter 9 claims](CLAIMS-D-CH09.md) record the precise Fourier normalization and known
adaptation gaps. No numeric count in issue #40 conflicts with these counts.

Chapter 8 (18/18 numbered nodes, 8.1–8.18) is independently reviewed-and-landed
on `main` (`Done: 18`) — coordinator-appointed crossed Carbon review
`PASS WITH ISSUES` (0 blocking, `NB-1`–`NB-3`), review SHA-256
`f4d891365a78abc620ba5484ae672c6e0ca740b935a516d2305bd97de19d5210`, recorded
on [FE #40](https://github.com/derekblair/formalize-everything/issues/40) as
comment `6806962135`; clean-slate `lake build` exited 0 (8,938 jobs); `AuditA`
passed across 1,576 project declarations; the audited axiom union is exactly
`{propext, Classical.choice, Quot.sound}`; zero `sorry`. In
`RudinRCA/Chapter08.lean`, the declaration counts reconcile as `177` public
*value* declarations (`98` `theorem` + `36` `lemma` + `31` `def` + `6` `abbrev`
+ `6` `instance`), `180` public source declarations (adding the 3 public
type/predicate formers `IsMonotoneClass`, `MonotoneClosure`, `PowersetCopy`),
`182` total source declarations (adding the 2 `private theorem`s
`measurableRectangles_semiring` and `sigmaFinite_completion`), `140`
`#print axioms` records (`136` theorem/lemma declarations + `4` named
instances), and `274` `AuditA` constants; see
[Chapter 8 coverage](CHAPTER08-COVERAGE.md) and
[Chapter 8 build evidence](BUILD-CHAPTER08.md). With Chapter 8 now done on
`main`, Chapter 9 (23 numbered nodes, 9.1–9.23) no longer waits on Chapter 8,
though Chapter 9 formalization remains out of scope (`Done: 0`).

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

## Cluster A formalization (landed on main)

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
Cluster A is independently reviewed and merged on `main` (55/83 items recorded in `Done`; current main-table `Done` total is 156/456, including 24/26 Chapter 7 nodes landed in FE #86 (PR #89)).

## Cluster F working-branch status

The independent inventory in [SCOPING-F.md](SCOPING-F.md) counts all 34 numbered nodes: 13.1–13.12 and 14.1–14.22, including definitions and exposition with substantive assertions. No chapter is complete. The `Done` column above retains its stated meaning of proved and reviewed on main.

The ticket’s headline numbering differs from the printed third edition: Runge is 13.6/13.9; 13.10 is Mittag-Leffler; 13.12 is harmonicity of log modulus. Mergelyan is 20.5 and is outside this cluster. The forward dependency 13.11(j) → 14.8 is explicit in the book.

The working Chapter13 module contains the sphere topology and exact stereographic map, inverse-chart singularity definitions, bounded removability and polynomial principal parts at infinity, entire nonpolynomial essential singularities, and the full 13.12 log-modulus harmonicity statement. The combined module and umbrella build passed with 48 allowed-axiom declaration audits on 2026-10-29. This is an incremental branch checkpoint: neither a complete chapter nor the clean-slate PR gate. Further assertions of 13.1 and the drafts for 13.2 onward remain under verification. Partial assertions are not counted as completed numbered nodes.

Cluster G counts were independently checked against the printed third edition; see [SCOPING-G.md](SCOPING-G.md). F. and M. Riesz is 17.13 in that edition, whereas issue #43 labels it 17.11. No complete chapter or merged Stage 2 coverage is claimed by this inventory update.

## Cluster H inventory and scope correction

Printed third-edition Chapters 18–20 have 37 top-level numbered nodes, plus
three locally numbered corollaries under 18.4. The previous titles, also present
in issue #44, do not match the printed edition. This branch follows the printed
chapter numbers and discloses the discrepancy; see [SCOPING-H.md](SCOPING-H.md).
No separate Stage 1 lane inventory was supplied. Counts here were independently
enumerated from the printed third-edition scan. Exercises are excluded.

Reviewed changes have landed on `main` (`Done` total 156/456 on `main` (FE #86 landed in PR #89); Chapters 18–20 are at `Done: 0`, as only reviewed work landed on `main` is counted). A
successful supporting lemma does not imply completion of its entire book node.

Cluster E's [inventory](inventory/README.md) verifies all 90 numbered nodes
of Chapters 10–12 against the third-edition scan. Unnumbered corollaries and
assertions belong to their numbered parent; exercises are excluded.
The `Done` column continues to mean accepted on main, so it is not advanced
by unreviewed work on `books/rca-holomorphic`. Branch proof coverage and
fidelity stops are recorded separately in the inventory and `QUEUE.md`.

Branch checkpoint, 2026-11-07 (unreviewed; ticket #41):

| Chapter | Inventoried | Complete nodes proved on branch | Remaining |
|---|---:|---:|---:|
| 10 | 44 | 16 | 28 |
| 11 | 32 | 4 | 28 |
| 12 | 14 | 3 | 11 |
| **Cluster E** | **90** | **23** | **67** |

Chapter 10 completion is enumerated in its inventory; Chapter 11 covers
11.1–11.4, and Chapter 12 covers 12.2, 12.3, and 12.9. The latter includes
the p. 258 sharpness example as `theorem12_9_sharpness`, so the justified
counts remain 3/11 and 23/67 rather than the pre-proof 2/12 and 22/68.
Partial nodes and the corrected subclaim of 11.5 do not inflate these
counts. This is a draft delivery: the Chapter 10 path/index machinery and
the 10.37 fidelity hold remain open. `scripts/build-cluster-e-clean.py`
verifies the current sources in a fresh output directory, retaining
existing work and artifacts.
