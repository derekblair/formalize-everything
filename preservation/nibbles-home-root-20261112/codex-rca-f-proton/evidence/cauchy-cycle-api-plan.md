# 13.5 dependency reconnaissance

This is source-based preparation, not an implementation or a completion claim.
The printed statement requires one polygonal cycle in Ω \ K that works for
all holomorphic f on Ω and every z in K. K may be disconnected and have holes.

At the pinned Mathlib commit, `Analysis/Complex/CauchyIntegral.lean` provides
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (line 296):
rectangle Cauchy–Goursat vanishing. It provides circle Cauchy integral formulas
(lines 493–574). It does not directly provide the rectangle Cauchy formula with
an interior evaluation point, nor an arbitrary polygon-cycle formula. A source
search over Analysis, MeasureTheory/Integral, and Topology for winding numbers,
path Cauchy formulas, and homotopy integral invariance produced no such theorem.

`MeasureTheory/Integral/CurveIntegral/Basic.lean` provides useful integration
infrastructure: `curveIntegral_symm` (214), `curveIntegral_trans` (274),
`curveIntegral_segment` (303), `norm_curveIntegral_segment_le` (318), and
`ContinuousOn.curveIntegrable_of_contDiffOn` (331). These support finite sums
of oriented line-segment integrals once the cycle's combinatorics is built.

`Analysis/Complex/HasPrimitives.lean` proves primitive existence on disks,
not on arbitrary simply connected regions; its documentation explicitly lists
the latter as a TODO. Thus a general homological Cauchy theorem cannot simply
be cited through that module.

The printed proof has the following substantial obligations:

1. Choose a positive square mesh uniformly inside Ω near K, using compactness.
2. Select the finitely many grid squares meeting K, and prove each lies in Ω.
3. Sum oriented boundaries and cancel shared edges. Every residual edge avoids
   K, and residual initial/end counts agree; 13.4 gives cycle decomposition.
4. Prove the rectangle Cauchy evaluation formula. For an interior z, one can
   reduce to the kernel integral using the removable divided difference
   (f(ζ)−f(z))/(ζ−z) and rectangle Cauchy–Goursat. The kernel integral itself,
   equal to 2πi for a positively oriented containing rectangle, remains a real
   proof obligation (e.g. explicit logarithm branches or an excision argument).
5. Sum square formulas at points away from grid lines. Extend to all z in K
   by continuity, since residual edges are disjoint from K.

Replacing this with the single-disk formula would silently restrict K and Ω,
and would not discharge 13.5.
