# Chapter 11 inventory and pinned Mathlib claims check

Inventory date: 2026-10-27. All **32 numbered entries, 11.1–11.32**, are
accounted for. Numbered expository and definition-bearing entries count;
exercises do not. **Numbered nodes proved on this branch: 1 (11.2);
remaining: 31.** The
counterexample and corrected subclaim for 11.5 do not complete that node.

Numbering and page references were checked in the third-edition printed
text, pp. 231–249, against the [public scan/OCR](https://djvu.online/file/NKmAEzkLVs8Io).
The [publisher's contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india)
independently confirms the chapter title. The already-cached PDF used for
page inspection is `/tmp/rca-ch01-source.pdf` (433 pages, SHA256
`a739b79e2ce55292667e2c9dec10e5b29430e9ebbd4a820bf41e4661fedf17cd`);
printed page 231 is PDF page 246. Page images resolved OCR ambiguities
in 11.3, 11.5, 11.15, 11.16 and 11.20. No numbered entry is UNVERIFIED.

Mathlib source was inspected at exactly
`d13f23b723b8a846827a245b89c10fc7d3f11612`, first through the existing
`fe-rca-a` clone and subsequently through this lane's fetched dependency.
This is a claims check, not a claim that every candidate adaptation compiles.

**A** = usable content exists; **V** = a related result or representation
exists but a faithful bridge remains; **M** = the required result was not
located in the pinned source and needs local development. M is a bounded
search finding, not a claim of mathematical impossibility. **F** is an
additional fidelity stop. For definitions, V includes explicit local
packaging. Source keys below refer to exact pinned files.

| Node | Printed page | Kind / topic | Claim | Pinned declaration or exact gap | Integration dependency |
|---|---:|---|---|---|---|
| 11.1 | 231 | Operators ∂, ∂̄ | V | C: `fderiv`; `differentiableAt_complex_iff_differentiableAt_real`; local Wirtinger definitions and decomposition needed. | None |
| 11.2 | 232 | Cauchy–Riemann | A | C: `differentiableAt_complex_iff_differentiableAt_real`, `complexOfReal_deriv`; pointwise globalization and algebraic notation conversion. | None |
| 11.3 | 232 | Laplacian; harmonicity | V | B: `InnerProductSpace.HarmonicAt` and `HarmonicOnNhd` impose extra regularity; see fidelity note below. L: `laplacian_eq_iteratedFDeriv_complexPlane`. | None |
| 11.4 | 232 | Holomorphic ⇒ harmonic | V | H: `AnalyticAt.harmonicAt`, `AnalyticAt.harmonicAt_re`, `AnalyticAt.harmonicAt_im`; transfer to the book's weaker definition still required. | None |
| 11.5 | 233 | Poisson kernel | V; F | P: `poissonKernel`, `poissonKernel_eq_re_herglotzRieszKernel`, `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel`; Fourier form and normalization bridges remain. Strict endpoint assertion is false; see below. | Circle integration / Fourier series |
| 11.6 | 233–234 | Poisson integral | V | P: kernel integrals are expressed with `Real.circleAverage`; local named integral and angular normalization bridge required. | Bochner / circle integration |
| 11.7 | 234 | Integral harmonicity | V | P: `analyticOnNhd_circleAverage_herglotzRieszKernel_smul`, `re_circleAverage_herglotzRieszKernel_smul`; H: analytic real/imaginary parts. L¹-circle and weak-definition bridges remain. | Integrability; parameter differentiation |
| 11.8 | 234–235 | Continuous boundary data | M | No Poisson extension boundary-continuity theorem located in P or HP; approximate-identity argument remains. | Uniform approximation / integration |
| 11.9 | 235 | Boundary representation | V | HP: `InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul`; P: analytic Herglotz integral. Weak harmonicity bridge required. | Circle integration |
| 11.10 | 235–236 | General discs; regularity | V | HP: arbitrary-center/radius formula; HA: `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, `HarmonicAt.analyticAt`. The weak-to-C² bridge is missing. | Change of variables; circle integration |
| 11.11 | 236 | Harnack convergence | M | No Harnack convergence/dichotomy theorem located. P supplies kernel bounds, not the required convergence theorem. | Monotone convergence; compact uniform convergence |
| 11.12 | 237 | Mean-value definition | V | HM: `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`; a local predicate for a point-dependent shrinking sequence of radii is needed. | Circle averages |
| 11.13 | 237 | Converse mean value | M | HM proves the forward direction; no converse for the preceding sequence-of-radii predicate located. | Poisson representation |
| 11.14 | 237–239 | Schwarz reflection | M | No matching reflection theorem located; continuation must use the stated imaginary-part boundary condition. | Depends on 11.13 |
| 11.15 | 239 | Radial restrictions | V | Local definition by composition; boundary uniform convergence depends on the missing 11.8 bridge. | Depends on 11.8 |
| 11.16 | 239–240 | Lp contraction; convergence | M | No Poisson-specific Lp contraction and radial norm-convergence package located. | Jensen/Hölder, Fubini, density in Lp |
| 11.17 | 240 | Measure Poisson integral | M | P treats function integrals on circles; complex-measure integral, harmonicity and variation bound need development. | Complex measures; Fubini |
| 11.18 | 240–241 | Approach regions | M | No matching Stolz-region definition located; local geometric definition and properties required. | None |
| 11.19 | 241–242 | Maximal functions | M | No nontangential/radial maximal package on the circle located; semicontinuity and normalized-circle differentiation bridges required. | Measure differentiation; normalized arc measure |
| 11.20 | 242–243 | Maximal comparisons | M | No matching Poisson maximal comparison located; P's pointwise kernel bounds do not establish it. | Positive measure integration |
| 11.21 | 243 | Nontangential limits | M | No matching named definition located; encode all approach regions with restricted filters or sequences. | None |
| 11.22 | 243–244 | Zero derivative limit | M | No matching boundary-limit theorem located. | Measure differentiation; 11.20 |
| 11.23 | 244 | Lebesgue-point limits | M | No matching Poisson nontangential Lebesgue-point theorem located. | Lebesgue differentiation; 11.22 |
| 11.24 | 244 | Almost-everywhere limits | M | No matching complex-measure Fatou theorem located. | Lebesgue decomposition; 11.22–23 |
| 11.25 | 244–245 | Weak/strong maximal bounds | M | No matching Poisson maximal weak-(1,1)/strong-(p,p) theorem located. | Maximal inequality / distribution functions |
| 11.26 | 245 | Representation roadmap | M | Its mathematical content is the criterion in 11.30, not a separately completed result. | Weak convergence; 11.30 |
| 11.27 | 245 | Equicontinuity; boundedness | V | E: `UniformEquicontinuous`, **not merely** `Equicontinuous`; pointwise boundedness can use `Bornology.IsBounded`. | None |
| 11.28 | 245–246 | Arzelà–Ascoli | V | AS: `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, `EquicontinuousOn.tendsto_uniformOnFun_iff_pi`; separability/diagonal sequential extraction and topology conversion remain. | None |
| 11.29 | 246–247 | Dual subsequence | A | W: `WeakDual.isSeqCompact_closedBall`, `WeakDual.eval_continuous`; apply to the bounded sequence, recover pointwise limits and norm bound. | None |
| 11.30 | 247–248 | Poisson representation | M | No measure/Lp/Herglotz representation package located. W provides weak-* subsequences only; representation and uniqueness still required. | Riesz representation, Lp duality, Fubini |
| 11.31 | 248–249 | H∞ space | V | `BoundedContinuousFunction` and uniform-limit holomorphicity provide ingredients; a closed holomorphic subspace and completeness proof remain. | No new integration |
| 11.32 | 249 | H∞ boundary uniqueness | M | No matching radial-limit isometry and boundary-arc uniqueness theorem located. | 11.16, 11.23, 11.30 |

The table has 2 A, 13 V, and 17 M rows (F is additional to V).
Node 11.2 is proved by `node11_2_holomorphic_iff` and `node11_2_deriv` in
`Chapter11.lean`, using explicit Wirtinger definitions. The other 31 rows
remain uncompleted at the full-node bar. The file compiles with
`lake env lean RudinRCA/Chapter11.lean` (exit 0); the cluster audit and
clean-slate build are tracked in the lane report.

## Fidelity events and representation constraints

1. **11.5(4), printed p. 233: false endpoint claim.** The admitted parameter
   range includes `r = 0`, where `P₀(t) = 1`; the printed strict inequality
   therefore fails, for example at `δ = 1`, `t = 2`. Stop this subclaim.
   `Chapter11.lean` proves the explicit counterexample and a corrected
   strict statement with the additional assumption `0 < r`. Neither is
   counted as completion of 11.5. The event must remain in `QUEUE.md`.
2. **11.3 / 11.10: regularity bridge, not a claimed false statement.**
   Rudin assumes continuity and existence of the two pure second partials,
   with their sum zero. Mathlib's `HarmonicAt` assumes `ContDiffAt ℝ 2`.
   Proving results under the latter hypothesis alone does not establish
   the corresponding book node. No unproved equivalence may be introduced.
3. **11.27: terminology bridge.** The book's global epsilon–delta condition
   corresponds to Mathlib's `UniformEquicontinuous`. Its weaker pointwise
   `Equicontinuous` notion is not a definitional replacement.

## Pinned source index and search scope

All paths below are relative to `Mathlib/` at the pinned commit. The
[pinned tree](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib)
is the source of the declaration claims.

| Key | Source path |
|---|---|
| C | `Analysis/Complex/Conformal.lean` |
| B | `Analysis/InnerProductSpace/Harmonic/Basic.lean` |
| L | `Analysis/InnerProductSpace/Laplacian.lean` |
| H | `Analysis/InnerProductSpace/Harmonic/Constructions.lean` |
| P | `Analysis/Complex/Poisson.lean` |
| HP | `Analysis/Complex/Harmonic/Poisson.lean` |
| HA | `Analysis/Complex/Harmonic/Analytic.lean` |
| HM | `Analysis/Complex/Harmonic/MeanValue.lean` |
| E | `Topology/UniformSpace/Equicontinuity.lean` |
| AS | `Topology/UniformSpace/Ascoli.lean` |
| W | `Analysis/Normed/Module/WeakDual.lean` |

The full pinned `Mathlib/` tree was searched case-insensitively for
`Harnack`, `nontangential`, `non.?tangential`, Schwarz/reflection combinations,
Poisson integral/limit combinations, and harmonic mean/uniform/limit
combinations; all complex/inner-product harmonic files and both Poisson
files were inspected. The general Arzelà–Ascoli and weak-dual files were
also inspected. Generic integration and topology lemmas are ingredients,
not evidence that the missing book-specific result is already proved.

The integration-dependency column identifies where Mathlib's corresponding
measure/integration tools can replace dependencies on Chapters 1–9;
this cluster need not wait for those chapter modules.
