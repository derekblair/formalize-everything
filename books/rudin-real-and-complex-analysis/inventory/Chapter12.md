# Chapter 12 inventory and pinned Mathlib claims check

Inventory date: 2026-10-27. Edition: third, 1987. **14 numbered nodes,
12.1–12.14; all numbers and identities VERIFIED.** Exercises are excluded.
The unnumbered corollary under 12.8 belongs to that node rather than adding
an invented number.

The primary evidence is the [book scan and OCR](https://djvu.online/file/NKmAEzkLVs8Io),
printed pp. 253–263; the chapter ends before the exercises on p. 264.
The [publisher's third-edition contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india)
independently confirms the chapter title. Scan images were inspected where
OCR lost formulas, bars, inequalities, or node numbers: particularly
[p.254](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/266.webp),
[p.255](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/267.webp),
[p.257](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/269.webp),
[p.258](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/270.webp),
[p.260](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/272.webp),
[p.261](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/273.webp),
[p.262](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/274.webp), and
[p.263](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/275.webp).

Claims were checked in Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, not the moving online
documentation. A = directly usable content or primitive definition;
V = available variants/components, with the stated adaptation still
required; M = no theorem for the complete node located in this revision.
M does not claim mathematical impossibility or absence of useful lemmas.
All node statuses below concern source coverage, not a Lean proof count.

| Node | Page | Kind and concise identification | Check | Pinned Mathlib evidence / remaining work |
|---|---:|---|---|---|
| 12.1 | 253 | Discussion: boundary maximum, rigidity, bounded-function boundary values | V | `Complex.norm_le_of_forall_mem_frontier_norm_le` and `Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm` in `Analysis/Complex/AbsMax.lean`; `H∞` boundary-value part needs the Chapter 11 representation machinery. |
| 12.2 | 254 | Theorem: Schwarz inequalities and rigidity | A | `Complex.norm_le_norm_of_mapsTo_ball`, `Complex.norm_deriv_le_one_of_mapsTo_ball`, `Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'` in `Analysis/Complex/Schwarz.lean`. Radius one, scalar target, zero center. |
| 12.3 | 254 | Definition: disk transformation | A | Direct field expression using `Complex` arithmetic and conjugation; no upstream theorem needed for the definition. |
| 12.4 | 254 | Theorem: transformation bijections, inverse, derivatives | M | No disk-transformation package found in `Complex/UnitDisc/Basic.lean`. `HasDerivAt.div` in `Analysis/Calculus/Deriv/Inv.lean` supplies calculus; domain, inverse, boundary, and derivative identities need explicit proofs. |
| 12.5 | 255 | Extremal problem: Schwarz–Pick derivative bound and equality | M | `Schwarz.lean` supplies centered bounds and rigidity, but the complete arbitrary-center statement was not found. Need 12.4, composition, and equality-case transport. |
| 12.6 | 255 | Theorem: classification of disk automorphisms | M | No classification found in `UnitDisc/Basic.lean` or `Schwarz.lean`. Requires inversion, 12.4, and 12.5; upper-half-plane Möbius actions are not this classification. |
| 12.7 | 256 | Examples: unbounded-strip failure; sublinear entire-function rigidity | V | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` in `Analysis/Complex/Liouville.lean` plus `Complex.exp` calculus. Both examples require new calculations and a limiting argument. |
| 12.8 | 257 | Theorem: three-lines inequality; logarithmic convexity corollary | V | `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` and `norm_le_interpStrip_of_mem_verticalClosedStrip` in `Analysis/Complex/Hadamard.lean`. Convert pointwise bounds into line suprema and normalize real powers. Handle zero boundary supremum and the zero-function case explicitly. |
| 12.9 | 258 | Theorem: strip growth condition implies boundary bound | V | `PhragmenLindelof.horizontal_strip` in `Analysis/Complex/PhragmenLindelof.lean`. Its arbitrary strip and big-O assumption specialize to the displayed strip and pointwise growth condition. |
| 12.10 | 259 | Lindelöf theorem: curve limit determines radial limit | M | `PhragmenLindelof.lean` contains strip/quadrant/half-plane growth estimates, not this boundary curve theorem. No radial-limit theorem found. |
| 12.11 | 260 | Setup: bounded orthonormal coefficients and endpoint estimates | V | `Orthonormal.sum_inner_products_le` and `Orthonormal.tsum_inner_products_le` in `Analysis/InnerProductSpace/Orthonormal.lean`; Bochner integral bounds provide the other endpoint. Need measure-function representatives and coefficient summability/integrability bridges. |
| 12.12 | 261 | Hausdorff–Young theorem for the preceding coefficient system | M | No Hausdorff–Young or Riesz–Thorin theorem found in `Analysis`, `MeasureTheory`, or file names. `Hadamard.lean` supplies the analytic interpolation ingredient, not the complete operator estimate. |
| 12.13 | 262 | Theorem: maximum property characterizes a function space | M | No converse theorem found. `Analysis/Complex/Harmonic/Poisson.lean` supplies formulas for already-harmonic functions, not the required harmonicity from a norm property. The book route uses Chapter 5 functional analysis; an independent Mathlib-based proof still needs that bridge. |
| 12.14 | 263 | Radó theorem: holomorphic away from the zero set | M | `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` in `Analysis/Complex/RemovableSingularity.lean` handles an isolated missing point; it does not handle an arbitrary zero set. No complete Radó theorem found. |

Coverage totals: **A 2, V 5, M 7 = 14**. No numbered node is
UNVERIFIED. Coverage is a source inspection, not a completed formalization.

The negative searches included `Rado`, `Radó`, `Hausdorff.Young`,
`Riesz.Thorin`, `schwarz.pick`, `radial.*limit`, `nontangential`,
`automorph`, `moebius`, and `mobius`; the relevant complex-analysis,
Fourier-analysis, measure-theory, and unit-disk files were then inspected.
The full-tree name search found unrelated Rado selection and Radon results,
which are not evidence for 12.14.

## Implementation accounting

`RudinRCA/Chapter12.lean` states the complete Schwarz lemma as
`RudinRCA.Chapter12.theorem12_2`, the definition in 12.3 as `phi`,
and the strip theorem in 12.9 as `theorem12_9`.
The two `theorem12_1_boundary_*` declarations cover the continuous-boundary
portion of 12.1 only; **12.1 remains incomplete** because its recalled
`H∞` boundary-value assertion is absent. Thus **3 nodes are covered,
11 remain incomplete**. No other node is claimed proved.
`lake env lean RudinRCA/Chapter12.lean` exited 0 with no warnings after
the last proof change; the integrated clean build and audit belong to
the lane report.

No printed statement has been silently changed. No counterexample or
correction was required by this source pass. In particular, the excluded
zero point in the Schwarz equality alternative and both derivative and
value equality alternatives were checked against the scan.
