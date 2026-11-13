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
| 9 | Fourier Transforms | 23 | 23 |
| 10 | Elementary Properties of Holomorphic Functions | 44 | 44 |
| 11 | Harmonic Functions | 32 | 19 |
| 12 | The Maximum Modulus Principle | 14 | 8 |
| 13 | Approximation by Rational Functions | 12 | 12 |
| 14 | Conformal Mapping | 22 | 19 |
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
[Chapter 8 build evidence](BUILD-CHAPTER08.md). `RudinRCA/Chapter09.lean`
(`4,333` lines, blob `0e31e98ed13f377c735755b72205751cdf25db49`) is wired into
the audited graph for `FE #87` (coordinator-appointed crossed review PASS WITH ISSUES, 0 blocking, recorded on FE #87; landed by PR #90), proving **23/23** complete Chapter 9 nodes
(`9.1`–`9.23`) at the programme bar (`Done: 23`, bringing the main-table `Done`
sum from `156/456` on `main` to `179/456`); clean-slate `lake build` exited 0
(`8,941` jobs, `0` errors) and `AuditA` passed across `2,369` project
declarations (`+393` over `1,976` on `main`, axiom union strictly
`{propext, Classical.choice, Quot.sound}`, zero `sorry`). In
`RudinRCA/Chapter09.lean`, the declaration counts reconcile as `203` public
*value* declarations (`134` `theorem` + `11` `lemma` + `36` `def` + `3`
`abbrev` + `19` `instance`), `205` public source declarations (adding the 2
public type/class formers `RudinL1Algebra` and `IsRudinBanachAlgebra`), `222`
total source declarations (adding `17` `private lemma`s), and `393` `AuditA`
constants; see [Chapter 9 coverage](CHAPTER09-COVERAGE.md).

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
Cluster A is independently reviewed and merged on `main` (55/83 items recorded in `Done`; main-table `Done` total is 281/456 after landing the 31/34 Cluster F Stage 2 nodes in FE #42 (PR #101, crossed review PASS WITH ISSUES) on top of the 250/456 total from the 71/90 Cluster E Stage 2 nodes in FE #88 (PR #91, crossed review PASS WITH ISSUES) and the 179/456 baseline on `main` including 24/26 Chapter 7 nodes landed in FE #86 (PR #89) and 23/23 Chapter 9 nodes landed in FE #87 (PR #90, crossed review PASS WITH ISSUES)).

## Cluster F Stage 2 (Chapters 13–14; FE #42)

The independent inventory in [SCOPING-F.md](SCOPING-F.md) counts all **34** numbered nodes of Chapters 13–14 (`13.1`–`13.12` and `14.1`–`14.22`), including definitions, remarks, and exposition with substantive assertions; unnumbered corollaries (`|a₁| ≤ 1` under `14.13`) belong to their numbered parent and exercises are excluded. Per the printed third edition, Runge is `13.6`/`13.7`/`13.9`, `13.10` is Mittag-Leffler, `13.12` is harmonicity of `log |f|`, and Mergelyan (`20.5`) is outside Cluster F.

Stage 2 (`FE #42`, umbrella `#36`, branch `coordinator/rca-cluster-f-stage2-20261112`; main-table `Done` advances from `250/456` on `main` `35efa215` to `281/456` on this branch for the `31/34` nodes verified proved in full, coordinator-appointed crossed review passed — PASS WITH ISSUES, zero blocking findings; PR #101):

| Chapter | Inventoried | Complete nodes proved (`Done`) | Pending | Coverage ledger |
|---|---:|---:|---:|---|
| 13 | 12 | 12 | 0 | [Chapter 13 coverage](CHAPTER13-COVERAGE.md) |
| 14 | 22 | 19 | 3 | [Chapter 14 coverage](CHAPTER14-COVERAGE.md) |
| **Cluster F** | **34** | **31** | **3** | [SCOPING-F.md](SCOPING-F.md) |

- `RudinRCA/Chapter13.lean` (`6,559` lines, blob `1793405c5aa3f3e858255b88203f7689a63acf74`; `165` source declarations / `124` public source / `123` public value / `431` `AuditA` constants, `+331` over the `100` foundational constants on `main` `35efa215`) proves **12/12** Chapter 13 nodes (`13.1`–`13.12`) in full: Riemann-sphere topology and singularity trichotomy at `∞` (`13.1`), rational partial fractions off poles (`13.2`), compact exhaustion with spherical-complement component containment (`13.3`), multiplicity-preserving balanced-interval partition (`13.4`), grid-square simultaneous Cauchy cycle (`13.5`), compact/polynomial/open-set Runge (`13.6`, `13.7`, `13.9`) and quantitative `1/m` necessity (`13.8`), Mittag-Leffler allowing zero principal parts (`13.10`), the full 9-way equivalence of plane simple connectedness (`13.11`, resolving `13.11(j) → 13.11(a)` without circularity via `riemann_mapping_of_holomorphic_sqrt`), and local holomorphic logarithms + harmonicity of `log ‖f‖` (`13.12`).
- `RudinRCA/Chapter14.lean` (`7,180` lines, blob `565f0871fc7af2d820c0463131e58abf38083282`; `118` source declarations / `112` public source / `111` public value / `295` `AuditA` constants) proves **19/22** Chapter 14 nodes (`14.1`–`14.17`, `14.21`–`14.22`) in full: oriented-angle preservation (`14.1`–`14.2`), linear fractional transformations and generalized circles (`14.3`, including a formal proof in `theorem14_3_stereographic_circle_iff` of the stereographic-circle characterization omitted in print), circular Schwarz reflection on an explicit symmetric neighborhood (`14.4`), normal families and Montel (`14.5`–`14.6`), conformal equivalence (`14.7`), the full Riemann mapping theorem (`14.8`) and extremal uniqueness (`14.9`), class `S`, Koebe functions, and odd square-root transforms (`14.10`–`14.12`), the area theorem (`14.13`, with proved summability), Bieberbach `|a₂| ≤ 2` + Koebe `1/4`-disc (`14.14`), omitted-value bound `|w₁ - w₂| ≤ 4` (`14.15`), simple boundary points and nonsimple slit/comb examples (`14.16`–`14.17`), and annulus conformal classification (`14.21`–`14.22`). The **3/22** Carathéodory boundary extension and Jordan-curve nodes (`14.18`–`14.20`) remain pending and are excluded from `Done`.
- Clean-slate `lake build` exited `0` (`8,942` jobs, `0` errors); whole-book `AuditA` passed across `3,712` project declarations across `17` audited modules (`+626` over the `3,086` baseline on `main` `35efa215`, axiom union strictly `{propext, Classical.choice, Quot.sound}`, zero `sorry`).

Cluster G counts were independently checked against the printed third edition; see [SCOPING-G.md](SCOPING-G.md). F. and M. Riesz is 17.13 in that edition, whereas issue #43 labels it 17.11. No complete chapter or merged Stage 2 coverage is claimed by this inventory update.

## Cluster H inventory and scope correction

Printed third-edition Chapters 18–20 have 37 top-level numbered nodes, plus
three locally numbered corollaries under 18.4. The previous titles, also present
in issue #44, do not match the printed edition. This branch follows the printed
chapter numbers and discloses the discrepancy; see [SCOPING-H.md](SCOPING-H.md).
No separate Stage 1 lane inventory was supplied. Counts here were independently
enumerated from the printed third-edition scan. Exercises are excluded.

Reviewed changes through PR #101 have landed on `main` (`281/456` total: `250/456` from FE #86 / PR #89, FE #87 / PR #90 and FE #88 / PR #91 plus the `31/34` Cluster F Stage 2 nodes in FE #42 landed by PR #101 after coordinator-appointed crossed review (PASS WITH ISSUES, zero blocking findings; see FE #42); Chapters 18–20 are at `Done: 0`, as only reviewed work landed on `main` is counted). A
successful supporting lemma does not imply completion of its entire book node.

## Cluster E Stage 2 (Chapters 10–12; FE #88)

Cluster E's [inventory](inventory/README.md) verifies all 90 numbered nodes
of Chapters 10–12 against the third-edition scan. Unnumbered corollaries and
assertions belong to their numbered parent; exercises are excluded.

Stage 2 (`FE #88`, extending Stage 1 `#41` / PR `#58`; coordinator-appointed crossed review passed — PASS WITH ISSUES, zero blocking findings; PR #91):

| Chapter | Inventoried | Complete nodes proved (`Done`) | Pending | Coverage ledger |
|---|---:|---:|---:|---|
| 10 | 44 | 44 | 0 | [Chapter 10 coverage](CHAPTER10-COVERAGE.md) |
| 11 | 32 | 19 | 13 | [Chapter 11 coverage](CHAPTER11-COVERAGE.md) |
| 12 | 14 | 8 | 6 | [Chapter 12 coverage](CHAPTER12-COVERAGE.md) |
| **Cluster E** | **90** | **71** | **19** | [Inventory](inventory/README.md), [QUEUE.md](QUEUE.md) |

- `RudinRCA/Chapter10.lean` (`9,059` lines, blob `36ea97885606ba5cc20bb33fa6015b846c5e37a7`; `363` source declarations / `650` `AuditA` constants) proves **44/44** Chapter 10 nodes (`10.1`–`10.44`), including general piecewise-`C¹` paths/chains/cycles, integral-defined winding index `Ind`, global homological and homotopical Cauchy theorems, the Residue Theorem, Argument Principle, Rouché's theorem, and the symmetric sinc Fourier transform `10.44`. For `10.37` (`E-10.37`), both literal printed counterexamples (`node10_37_literal_conclusion_counterexample`, `node10_37_literal_geometric_counterexample`) and the explicitly disclosed `z ∈ D₊` corrected crosscut index-jump theorem (`theorem10_37_corrected`) are proved; final `Done` adjudication of disclosed fidelity repairs was passed by the crossed review, which approved both `E-10.37` and `E-11.5` as faithful; nodes `10.37` and `11.5` are in `Done`.
- `RudinRCA/Chapter11.lean` (`3,559` lines, blob `7230d97929f0d9c784bcc4082d67d443814370eb`; `114` source declarations / `208` environment constants in standalone `AuditE` (`207` in combined `AuditA` after upstream `IsMaxFilter.eq_1` deduplication) proves **19/32** Chapter 11 nodes (`11.1`–`11.15`, `11.27`–`11.29`, `11.31`), retaining Rudin's weak `11.3` `HarmonicOn` predicate and proving its reverse equivalence to smooth `HarmonicOnNhd` (`11.10`), uniform equicontinuity (`11.27`–`11.28`), sequential Banach–Alaoglu (`11.29`), completeness of `H^∞(Ω)` (`11.31`), and all subclauses of `11.5` alongside the `r = 0` counterexample and `0 < r` strict-inequality repair (`E-11.5`). The `13/32` radial/nontangential maximal, Fatou, and measure-Poisson nodes (`11.16`–`11.26`, `11.30`, `11.32`) remain pending.
- `RudinRCA/Chapter12.lean` (`1,085` lines, blob `df0cfaef5808911b5eea0e28cc7c18e0528eae40`; `33` source declarations / `57` `AuditA` constants) proves **8/14** Chapter 12 nodes (`12.2`–`12.9`, including `12.8`'s logarithmic-convexity corollary and `theorem12_9_sharpness`). Partial node `12.1` (missing the recalled `H^∞` radial-boundary-value assertion) and nodes `12.10`–`12.14` remain pending and are excluded from `Done`.
- Clean-slate `lake build` exited `0` (`8,941` jobs, `0` errors, `0` warnings in Chapters 10–12); `AuditE` passed across `915` Cluster E declarations (`650 + 208 + 57`); whole-book `AuditA` passed across `3,086` project declarations (`+717` over the `2,369` baseline on `main`, axiom union strictly `{propext, Classical.choice, Quot.sound}`, zero `sorry`).
