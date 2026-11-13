# Actual radial boundary limits needed by RCA 15.19

Research only, 2026-10-29. No radial-limit existence theorem has been proved or checked. Scope is the prerequisite used in Chapter 15; this does not claim completion of earlier or later chapters.

The needed conclusion is: if `f` is holomorphic and bounded on the open unit disc, then a measurable boundary function `f*` exists and `f(r exp(iθ)) → f*(θ)` for almost every θ as real `r → 1` from below. A subsequence limit is insufficient. This is a genuine missing prerequisite, not an assumption that may be inserted into the final 15.19 statement.

## Exact pinned APIs inspected

Source paths are relative to the lane book's `.lake/packages/mathlib/Mathlib/` at pinned commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| API | Location | What it proves / what it does not prove |
| --- | --- | --- |
| `DiffContOnCl.circleAverage_poissonKernel_smul` | `Analysis/Complex/Poisson.lean` | Poisson formula on a disc with continuous closure data; applies to inner circles of a bounded holomorphic function. No outer boundary-value existence. |
| `poissonKernel`, kernel bounds | same file, definition near line 58; upper/lower Herglotz bounds near lines 110 and 146 | Kernel formula and interior bounds. No approximate-identity convergence theorem for measurable boundary data. |
| `HarmonicOnNhd.circleAverage_poissonKernel_smul`, `HarmonicContOnCl.circleAverage_poissonKernel_smul` | `Analysis/Complex/Harmonic/Poisson.lean`, lines 109 and 120 | Harmonic interior Poisson formula with neighborhood/continuous-closure hypotheses; no Fatou theorem. |
| `AddCircle.fourierBasis` | `Analysis/Fourier/AddCircle.lean:411` | Complete Hilbert basis of `Lp ℂ 2 haarAddCircle`, indexed by integers. `haarAddCircle` has total mass one. |
| `fourierBasis_repr` | same file:423 | Identifies Hilbert-basis coordinates with Fourier integrals. |
| `hasSum_fourier_series_L2`, `hasSum_sq_fourierCoeff` | same file:433 and 440 | L² Fourier convergence and exact Parseval equality. They do not assert pointwise Fourier convergence. |
| `VitaliFamily.ae_tendsto_average_norm_sub` | `MeasureTheory/Covering/Differentiation.lean:867` | Almost every point is a Lebesgue point for locally integrable Banach-valued data. This is the right measure-theoretic source for Poisson boundary convergence. |
| `LocallyIntegrable.ae_hasDerivAt_integral` | `MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean:40` | Almost-everywhere derivative of the indefinite integral; an alternative to the average formulation. |
| `Besicovitch.tendsto_filterAt` | `MeasureTheory/Covering/BesicovitchVectorSpace.lean` | Shrinking closed balls tend through the Vitali differentiation filter. Applied explicitly in the bump-convolution theorem below. |
| `tendsto_integral_smul_of_tendsto_average_norm_sub` | `MeasureTheory/Integral/Average.lean:835` | Peak integrals converge at Lebesgue points if kernels have shrinking support and a uniform bound by `K / measure(support ball)`. The full Poisson kernel has no shrinking support, so this cannot be applied directly. |
| `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` | `Analysis/Calculus/BumpFunction/Convolution.lean:107` | Almost-everywhere convergence for normalized bumps with comparable inner/outer radii. It is a useful proof template, not the Poisson theorem. |
| `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` | `MeasureTheory/Integral/PeakFunction.lean:183` | Convergence for integrable input continuous at the peak. Lebesgue-point hypotheses are not a substitute without an additional argument. |
| `tendsto_tsum_of_dominated_convergence` | `Analysis/Normed/Group/Tannery.lean:45` | Arbitrary-filter dominated convergence of a series. Suitable for dyadic-annulus estimates of the Poisson error. |

Whole-source searches over Analysis and MeasureTheory for radial/radially, Fatou/fatou, Abel boundary convergence, LebesguePoint, approximate identities, and convolution convergence found no ready radial Fatou theorem. `Complex/AbelLimit.lean` assumes the boundary series already converges and therefore does not solve the problem. Martingale convergence exists in Probability, but constructing the necessary analytic martingale/Poisson bridge would add substantial work rather than remove this gap.

## Shortest credible construction route

1. From bounded holomorphic `f`, construct an `L²` boundary function using the Fourier Hilbert basis. The inner-circle Fourier coefficients are `a_n r^n` for nonnegative n and zero for negative n. Parseval/Bessel bounds give `Σ |a_n|² ≤ M²`; the inverse Hilbert-basis coordinate isometry then constructs the boundary function. Prove radial L² convergence by dominated convergence of the coefficient squares.
2. Obtain an essentially bounded representative (`|f*| ≤ M`) from that L² convergence, for example using an almost-everywhere convergent subsequence. This use of a subsequence is only to transfer the bound, not to assert full radial convergence.
3. Derive the actual Poisson representation of `f` from the Fourier coefficients, or pass the inner-circle Poisson formula to the L² limit using the fixed interior kernel as a bounded linear functional.
4. Prove that Poisson integrals of essentially bounded circle data converge at every Lebesgue point. With `δ=1-r`, the angular kernel is bounded by a constant times `δ/(δ²+t²)` for `r≥1/2` and `|t|≤π`. Decompose into the central interval and dyadic annuli. The error is bounded by a constant times `Σ_k 2^(-k) A(2^k δ)`, where `A(s)` is the mean norm error on a centered interval of radius s. For each fixed k the mean error tends to zero by Lebesgue differentiation; all means are bounded by `2M`. Tannery's theorem gives convergence of the entire weighted sum. Periodic representatives handle intervals crossing the chosen angular cut.
5. Combine with the Poisson representation and transfer normalized AddCircle measure to the real-angle convention used by the Chapter 15 circle means.

An alternative to step 4 uses integration by parts against the cumulative mean error and the decreasing Poisson kernel, followed by the existing continuous-input peak-function theorem. It requires an explicit absolutely-continuous/Fubini integration-by-parts bridge. The dyadic route uses only nonnegative integral inequalities and summable geometric bounds and currently looks more direct.

## Concrete outstanding proof obligations

- Inner-circle Fourier coefficient identification and square-summability bound.
- Construction of the L² boundary function and the true Poisson representation.
- Circle-to-periodic-real Lebesgue-point and measure-normalization bridge.
- Poisson angular denominator lower bound and the complete dyadic integral estimate.
- Full real-radius limit, followed by measurability and the boundary norm bound.

None of these obligations is discharged merely by the existence of the APIs in the table. They remain required for an unconditional 15.19 formalization.

## Shorter route found after the Fourier search

A primitive-and-peak argument avoids the L² construction entirely. Pinned `DifferentiableOn.isExactOn_ball` (`Analysis/Complex/HasPrimitives.lean:291`) gives a primitive F of the bounded function. `Convex.lipschitzOnWith_of_nnnorm_deriv_le` (`Analysis/Calculus/MeanValue.lean:737`) makes F Lipschitz on the disc. `LipschitzOnWith.extend_finite_dimension` (`Analysis/Normed/Module/FiniteDimension.lean:210`) gives a global Lipschitz extension, retaining analyticity and F'=f on the open disc. Its boundary curve θ↦F(exp(iθ)) is Lipschitz. `LipschitzWith.ae_differentiableAt_real` (`Analysis/BoundedVariation.lean:269`) supplies its ordinary angular derivative almost everywhere.

At a point θ of boundary differentiability, differentiate the existing Poisson formula for F in the angular variable. After rotation, the derivative integral is a peak integral of the difference quotient `(F(exp(i(θ+t)))-F(exp(iθ)))/t`, using the kernel `ψ_r(t)=−t P'_r(t)/(2π)` on `[-π,π]`. This kernel is nonnegative; integration by parts gives total mass `1-P_r(π)`, tending to one. It tends uniformly to zero away from t=0. The difference quotient is bounded by the Lipschitz constant, is integrable, and tends to the actual angular derivative at t=0. The existing continuous-input peak theorem now applies directly. The angular derivative inside the disc equals `i r exp(iθ) f(r exp(iθ))`; division by its prefactor yields the full radial limit. This uses ordinary a.e. differentiability of the primitive boundary curve, so no a.e. Poisson convergence theorem or Fourier representation is needed.

`RadialBoundaryWork.lean` now contains uncompiled drafts of the primitive extension, actual a.e. angular differentiability, the angular Poisson kernel, its derivative, and positivity of the derivative peak. Outstanding: the precise Poisson/angular derivative integral identity, its peak normalization and uniform tails, the bounded difference-quotient input and final a.e. limit wrapper. No compiler has been launched for this file, and no radial-limit existence claim is made.
