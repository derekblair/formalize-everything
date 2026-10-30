# Chapter 5 pinned Mathlib API research

Read-only claims check, 2026-10-29. Sources: printed text extracted in `rudin-ch4-5-raw.txt`, issues #38 and #36, and the fresh clone's book-local `.lake/packages/mathlib/Mathlib` at pin `d13f23b723b8a846827a245b89c10fc7d3f11612`. Paths below are relative to that Mathlib root. This is an API mapping, not a formalization or build claim.

| Node | Printed subject | Pinned coverage / required work |
|---|---|---|
| 5.1 | Introductory discussion | No independent theorem; record narrative node. |
| 5.2 | Normed and Banach spaces, metric, examples | `NormedAddCommGroup`, `NormedSpace ℂ`, `CompleteSpace`; `dist_eq_norm`; Lp and C₀ completeness instances. Definition wrapper and all stated examples needed. |
| 5.3 | Operator norm as closed-ball supremum, sphere supremum, least bound | `Analysis/Normed/Operator/NNNorm.lean`: `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`, `sSup_unit_ball_eq_norm`, `sSup_sphere_eq_norm`; `le_opNorm` and `opNorm_le_bound` supply least-bound inequalities. Zero-domain caveat for sphere formulation must be handled explicitly. |
| 5.4 | Bounded iff continuous iff continuous at one point | `Analysis/Normed/Operator/BoundedLinearMaps.lean:318`: `IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap`; `Topology/Algebra/Group/Neighborhood.lean` has `continuous_of_continuousAt_zero` for additive homs. Book-faithful triple equivalence must be stated for algebraic maps. |
| 5.5 | Introductory discussion | No independent theorem. |
| 5.6 | Baire, plus dense Gδ intersection corollary | `Topology/Baire/CompleteMetrizable.lean`: `BaireSpace.of_completelyPseudoMetrizable`; `Topology/Baire/Lemmas.lean`: `dense_iInter_of_isOpen`, `dense_iInter_of_Gδ`. Need combine latter with `IsGδ.iInter` for complete corollary. |
| 5.7 | Nowhere dense/meagre definitions and complete space nonmeagre | `IsNowhereDense`, `IsMeagre`, `not_isMeagre_of_isOpen`; printed nonmeagreness needs nonempty X (empty complete space is meagre). Disclose caveat, not silently strengthen. |
| 5.8 | Uniform norm bound OR residual pointwise unboundedness | `Analysis/Normed/Operator/BanachSteinhaus.lean`: global `banach_steinhaus`. This is weaker in presentation: pointwise bounded everywhere implies bounded operator norms. Printed dense-Gδ alternative requires new argument with open sets `{x | ∃ i, n < ‖g i x‖}`; density follows from no common norm bound using translation/scaling. Do NOT substitute ordinary UBP as whole node. |
| 5.9 | Surjective bounded map sends unit ball over δ-ball; open map | `Analysis/Normed/Operator/Banach.lean`: `ContinuousLinearMap.exists_preimage_norm_le`, `ContinuousLinearMap.isOpenMap`. δ=1/C from positive controlled-preimage constant yields exact ball assertion. |
| 5.10 | Bijective bounded map has lower bound and bounded inverse | Same file: `LinearEquiv.continuous_symm`, `ContinuousLinearEquiv.ofBijective`; derive positive lower bound using inverse op-norm or `exists_preimage_norm_le`. |
| 5.11 | Fourier partial-sum convolution, Dirichlet kernel, logarithmic divergent L1 norms, resonance | No Dirichlet kernel/Lebesgue constant/divergent continuous Fourier-series theorem found by whole-library name/content searches. `Analysis/Fourier/AddCircle.lean` supplies Fourier coefficients and orthogonality, but kernel identities, lower bound, operator norm equality require development. |
| 5.12 | Dense Gδ family of continuous functions with dense Gδ unboundedness points | No direct theorem found; depends on full 5.8 and missing 5.11. Baire APIs usable. |
| 5.13 | Countable dense set not Gδ in complete space without isolated points | `Topology/Baire/Lemmas.lean`: `not_isMeagre_of_isGδ_of_dense`; use countable meagreness in a perfect T1 space. Nonempty assumption needed for literal printed statement: empty space is complete/no isolated points, ∅ is countable dense Gδ. |
| 5.14 | Fourier coefficients L1 tend to zero, c₀ definition/completeness | `Analysis/Fourier/RiemannLebesgueLemma.lean` proves whole-space Riemann–Lebesgue; no direct AddCircle coefficient tail theorem found. Could prove using L1 density of finite Fourier combinations (`span_fourierLp_closure_eq_top`) and coefficient bound. `ZeroAtInftyContinuousMap`/`C₀(ℤ,ℂ)` provides c₀ with discrete topology. |
| 5.15 | Fourier L1→c₀ bounded injective, norm one, not onto | No full direct theorem; coefficient map/density give parts. Non-surjectivity depends on missing Dirichlet-kernel L1 growth from 5.11. |
| 5.16 | Norm-preserving Hahn–Banach on arbitrary subspace | `Analysis/Normed/Module/HahnBanach.lean:44`: global `exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) : ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖`; no closedness/completeness assumption. |
| 5.17 | Real part of complex functional and complex extension, same norm | `Analysis/RCLike/Extend.lean`: `Module.Dual.extendRCLike_apply`, `re_extendRCLike_apply`, equivalence; `Analysis/Normed/Module/RCLike/Extend.lean`: `StrongDual.norm_extendRCLike`. |
| 5.18 | Hahn–Banach proof construction | Covered mathematically by 5.16; if recording internal extension lemma, `Analysis/Convex/Cone/Extension.lean:159` global `exists_extension_of_le_sublinear`, and `Analysis/LocallyConvex/HahnBanach.lean`: `Module.Dual.exists_extension_of_le_seminorm_real`. |
| 5.19 | Membership in closed subspace iff annihilated by annihilators | No exact easy normed-space theorem located in initial search. Quotient by topological closure plus Hahn–Banach `exists_dual_vector` proves separation; forward direction uses continuity/closure. |
| 5.20 | Norm-one functional attains norm at nonzero vector | `Analysis/Normed/Module/HahnBanach.lean:67`: global `exists_dual_vector 𝕜 x (h : ‖x‖ ≠ 0)`. |
| 5.21 | Dual Banach, separates points, bidual evaluation norm | `Analysis/Normed/Module/Dual.lean`: `NormedSpace.eq_iff_forall_dual_eq`; `Analysis/Normed/Module/DoubleDual.lean`: `NormedSpace.inclusionInDoubleDualLi`, `double_dual_bound`, `norm_le_dual_bound`; dual completeness follows complete codomain CLM instance. Unit-sphere supremum at zero space needs explicit convention/caveat. |
| 5.22 | Boundary representation by positive probability measures | Hahn–Banach plus Riesz measure APIs exist separately. No exact abstract boundary representing-measure theorem located. Need prove a unital norm-one complex functional is positive, then obtain regular probability measure, matching general compact Hausdorff statement. |
| 5.23 | Polynomial maximum modulus on closed disc/boundary | `Analysis/Complex/AbsMax.lean` maximum modulus machinery available; exact compact-disc supremum statement needs wrapper. |
| 5.24 | Poisson kernel series/closed form, representing measure uniqueness | `Analysis/Complex/Poisson.lean` defines Poisson kernel and proves differentiable-function integral formula. This does NOT directly give arbitrary abstract A as printed; 5.22 plus moments/trig density required. Kernel series identity itself requires development/check. |
| 5.25 | Abstract maximum-principle subspace implies Poisson formula | No direct theorem found. Holomorphic or harmonic Poisson formulas impose extra hypotheses and may NOT silently replace this statement. |

## Exact reusable core signatures

- `banach_steinhaus {ι} [CompleteSpace E] {g : ι → E →SL[σ] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C'`.
- `ContinuousLinearMap.exists_preimage_norm_le (f : E →SL[σ] F) (surj : Function.Surjective f) : ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖`, both spaces complete, isometric invertible scalar hom.
- `dense_iInter_of_isOpen [Countable ι] {f : ι → Set X} (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) : Dense (⋂ i, f i)`, `[BaireSpace X]`.
- `nonempty_interior_of_iUnion_of_closed [Countable ι] [Nonempty X] (hc : ∀ i, IsClosed (f i)) (hU : ⋃ i, f i = Set.univ) : ∃ i, (interior (f i)).Nonempty`.

## Scope discrepancy

Issue #38 mentions closed-graph consequences in its headline; the printed Chapter 5 places the closed graph theorem in exercise 16 (raw text around line 1415), not in numbered sections 5.1–5.25. Exercises are explicitly out of scope for v1. The API exists (`LinearMap.continuous_of_isClosed_graph` and `LinearMap.continuous_of_seq_closed_graph`, `Analysis/Normed/Operator/Banach.lean`) but should not inflate required node counts.
