# Cluster B Mathlib claims check

Pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `v4.34.1`.
Printed scope and all subclaims are in [INVENTORY-B.md](INVENTORY-B.md).
This is a claims mapping, not a claim that the chapter currently passes Lean.
“Direct” means the pinned library contains the mathematical statement; “adapt”
means restatement, combining results, or a convention bridge is required;
“new” means no matching direct result was found and the lane must supply proof.
A row may contain several of these statuses because a numbered node can contain
several independent assertions.

| Node | Status | Pinned APIs / work needed |
| --- | --- | --- |
| 4.1 | Adapt | `InnerProductSpace`, `inner_conj_symm`, `inner_add_right`, `inner_smul_right`, `norm_eq_sqrt_re_inner`; reverse the inner-product arguments to preserve Rudin's convention. |
| 4.2 | Direct | `norm_inner_le_norm`, including seminormed spaces without positive definiteness. |
| 4.3 | Direct | `norm_add_le`. |
| 4.4 | Direct | `dist_eq_norm`, `CompleteSpace`, `cauchySeq_tendsto_of_complete`. |
| 4.5 | Direct / new | `EuclideanSpace`, `PiLp.inner_apply`, `L2.inner_def`, `L2.integrable_inner`, completeness instances. Continuous interval functions with the integral norm require a separate incompleteness proof; supremum-norm completeness is irrelevant. |
| 4.6 | Direct / adapt | `Continuous.inner`, `continuous_norm`, `LipschitzWith.of_dist_le_mul`, `lipschitzWith_one_norm`. |
| 4.7 | Adapt / correction | `Submodule`, `topologicalClosure`, `finrank_le`, `finrank_eq_zero`, `eq_top_of_finrank_eq`; prove the corrected closure criterion and its empty-set counterexample, bounded-functions subspace and non-example. |
| 4.8 | Direct / adapt | `Convex`, `convex_iff_forall_pos`, `Submodule.convex`, `Convex.translate`; statements retain arbitrary vector spaces. |
| 4.9 | Direct / adapt | `inner_eq_zero_symm`, `Submodule.mem_orthogonal`, `isClosed_orthogonal`; singleton perpendicular subspace and intersection formula. |
| 4.10 | Adapt | `exists_norm_eq_iInf_of_complete_convex` provides existence; prove uniqueness using `norm_eq_iInf_iff_real_inner_le_zero`. |
| 4.11 | Direct / adapt | `Submodule.starProjection`, complementary projection/decomposition, `starProjection_minimal`, `norm_sq_eq_add_norm_sq_starProjection`, `orthogonal_eq_bot_iff`; package all parts and nearest-point uniqueness. |
| 4.12 | Direct / adapt | `InnerProductSpace.toDual`, its inverse and `ext_inner_right`; retain uniqueness and first-slot linearity. |
| 4.13 | Direct / adapt | `Submodule.span_le`, `Finsupp.mem_span_iff_linearCombination`, `linearIndependent_iff`, `orthonormal_iff_ite`; algebraic clauses need no Hilbert-space assumption. |
| 4.14 | Adapt | `Orthonormal.inner_right_sum`, `OrthogonalFamily.norm_sum`, `sum_inner_products_le`; derive strict best approximation, coefficient values outside the support, and the remainder identity. |
| 4.15 | Direct / adapt | `ENNReal.tsum_eq_iSup_sum`, `lintegral_count`, `lp.norm_rpow_eq_tsum`, `lp.summable_inner`, `lp.inner_eq_tsum`, `Summable.countable_support`, `lp.hasSum_single`, ℓ² completeness; arbitrary index sets retained. |
| 4.16 | Adapt | Dense-set isometry extension and closed range of complete isometric images; no completeness of the target assumed. |
| 4.17 | Adapt | `OrthogonalFamily.linearIsometry`, `range_linearIsometry`, adjoints, and Hilbert bases of the closed span; build a surjective coefficient map for an arbitrary orthonormal family. |
| 4.18 | Adapt | `maximal_orthonormal_iff_orthogonalComplement_eq_bot`, Hilbert-basis representation and ℓ² norm/inner identities; prove all four equivalent conditions. |
| 4.19 | Direct / new | `HilbertBasis.repr`, `exists_hilbertBasis`; cardinal classification requires a countable-support covering argument and finite-dimensional dimension comparison. |
| 4.20 | Correction | `PartialOrder`, `IsChain`, `MaximalChain`; prove that the printed disc chain admits a proper extension by the whole plane. |
| 4.21 | Direct | Hausdorff maximal-chain theorem from `Mathlib.Order.Zorn`; normalize a nonzero Hilbert vector to a unit vector. |
| 4.22 | Direct / adapt | Maximal orthonormal-set extension API in `Analysis.InnerProductSpace`; preserve extension of a given set, rather than existence alone. |
| 4.23 | Adapt | `AddCircle.homeomorphCircle'`, `fourier`, `fourierLp`, `orthonormal_fourier`, Haar probability measure; bridge periodic/circle models and sine/cosine/exponential finite forms. |
| 4.24 | Direct | `span_fourierLp_closure_eq_top`. The proof may differ from the book's approximate-identity construction. |
| 4.25 | Direct / new | `span_fourier_closure_eq_top` gives uniform trigonometric approximation. The appended Fejér assertion requires a new kernel proof, using the general approximate-identity theorem in `MeasureTheory.Integral.PeakFunction`. |
| 4.26 | Direct / adapt | `fourierCoeff_eq_intervalIntegral`, `fourierBasis.repr`, `fourierBasis_repr`, ℓ² and Hilbert-basis identities; express actual symmetric partial sums and exact tail norm. |

Chapter 5's node-by-node pinned API mapping is included in
[CLAIMS-B-CHAPTER05.md](CLAIMS-B-CHAPTER05.md). It records each of 5.1–5.25,
including the stronger residual form of uniform boundedness and the Fourier / 
boundary-measure gaps. A weaker headline theorem does not discharge an entire
printed node.
