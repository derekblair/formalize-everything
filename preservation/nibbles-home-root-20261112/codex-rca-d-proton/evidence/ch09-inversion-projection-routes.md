# Pinned-source routes for 9.11–9.17

Read-only research at Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. No Chapter 9 Lean declarations or imports were created. Chapter 8 gate remains with root. The normalizations and full printed-node inventory are in `ch09-claims.md`.

## 9.11 and 9.12: a.e. inversion and uniqueness via test functions

A shorter route than constructing a new distribution embedding is available. Work first in Mathlib's volume/exp(-2πixt) convention and transfer using the dilation isometry described in the claims report.

For complex smooth compactly supported ψ (hence Schwartz), Fψ and F⁻ψ are Schwartz, integrable, and satisfy exact inverse identities. `VectorFourier.integral_fourierIntegral_smul_eq_flip` (`Analysis/Fourier/FourierTransform.lean:242`) proves the bilinear pairing identity for **arbitrary integrable f and g**, with no continuity assumption on f and no assumption that Ff is integrable. The more general continuous-bilinear version is `integral_bilin_fourierIntegral_eq_flip` (line 218); the sesquilinear version `integral_sesq_fourierIntegral_eq_neg_flip` is line 254. For inverse Fourier use `L := -innerₗ ℝ`; the negated flipped bilinear form simplifies directly.

If f and Ff are integrable and h=F⁻Ff, apply the pairing identity twice:

`∫ h ψ = ∫ (Ff) (F⁻ψ) = ∫ f F(F⁻ψ) = ∫ f ψ`.

The function h is continuous because Ff is integrable (`VectorFourier.fourierIntegral_continuous`, line 163; inverse uses the same theorem with negative bilinear form), hence locally integrable. Conclude h=f a.e. using `ae_eq_of_integral_contDiff_smul_eq` (root namespace) (`Analysis/Distribution/AEEqOfIntegralContDiff.lean:195`). Its tests are real-valued smooth compactly supported functions; convert them using `Complex.ofRealCLM` and `HasCompactSupport.toSchwartzMap`. The test-uniqueness theorem explicitly assumes only local integrability of the two compared functions. This avoids a circular assumption that h is globally integrable before proving it equals f a.e.

For L¹ uniqueness Ff=Fg, use only one paired Fourier identity against F⁻ψ to show the test integrals of f and g agree. The zero version is `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (line 186). This does not require the common transform to be integrable. The already available pointwise theorem `Integrable.fourierInv_fourier_eq` only handles continuity points and does not alone imply these arbitrary-L¹ statements.

This is a mathematically complete proposed route; its adapters and Lean proofs are still to be written and checked.

## 9.13: classical/L² compatibility and cutoff limits

The existing unitary is `MeasureTheory.Lp.fourierTransformₗᵢ` (`Analysis/Fourier/LpSpace.lean:50`). Its inverse, norm and inner-product identities are already provided. Direct compatibility is exposed for Schwartz inputs only (`SchwartzMap.toLp_fourier_eq`, line 101).

For general f∈L¹∩L², combine the same pairing identity with `Lp.fourier_toTemperedDistribution_eq` (LpSpace:123), `TemperedDistribution.fourier_apply` (`Analysis/Distribution/TemperedDistribution.lean:482`) and `Lp.toTemperedDistribution_apply` (line 169). These identify the test integral of the L² Fourier representative with `∫f Fψ`; the latter equals the test integral of the classical integral Ff. The L² representative is locally integrable (`MemLp.locallyIntegrable`) and the classical Ff is continuous, so the same test-uniqueness theorem identifies them a.e. This is an actual route for all L¹∩L², not an assertion that Schwartz compatibility already suffices without a density/duality argument.

For the printed symmetric cutoff f_A=1_[-A,A] f, `integrableOn_Lp_of_measure_ne_top` (`MeasureTheory/Integral/IntegrableOn.lean:468`) gives L¹ integrability of each cutoff of an L² representative. L² membership follows from `MemLp.indicator`. The squared difference tends pointwise to zero and is dominated by ‖f‖². Use `tendsto_integral_filter_of_dominated_convergence` on this nonnegative real integrand, then the L² norm-square formula / square-root continuity. `Lp.tendsto_Lp_iff_tendsto_eLpNorm''` (`Function/LpSpace/Complete.lean:133`) converts a statement about function representatives into a bundled Lp limit. Continuity of the unitary Fourier map gives the forward cutoff limit; the inverse unitary gives the printed inverse cutoff limit. These cutoff bridges remain new proofs.

## 9.17: projection argument without a commutant theorem

Root proposed the following useful construction. Let H be the closed translation-invariant L² subspace and conjugate its orthogonal projection by Fourier. The resulting projection T commutes with all character multipliers M_t. Self-adjointness and commutation imply equality of the Fourier integrals of the L¹ functions `(Tf) * conj(g)` and `f * conj(Tg)`, for every f,g∈L². L¹ uniqueness from 9.12 then gives `(Tf) conj(g) = f conj(Tg)` a.e.

Fix the everywhere-positive L² function g(x)=exp(-x²). Define the measurable multiplier P=conj(Tg)/g (g is real). The last identity gives Tf=P f a.e. for every f. Using f=g identifies Tg=Pg; using f=Tg and T²g=Tg gives P²=P a.e. because g never vanishes. Thus P∈{0,1} a.e. and the range of T is exactly the functions vanishing a.e. on the measurable set {P=0}. Exceptional null sets may depend on f; no unjustified uncountable intersection is required.

Exact pinned APIs:

- `Submodule.starProjection : E →L[ℂ] E` (`Analysis/InnerProductSpace/Projection/Basic.lean:132`) is the projection into the ambient space. `orthogonalProjectionOnto` instead lands in the subspace. The old `orthogonalProjection` alias is deprecated.
- Closed submodules of a complete Hilbert space have `HasOrthogonalProjection` (line 92); for ordinary submodules with a complete subtype, `HasOrthogonalProjection.ofCompleteSpace` (line 55).
- `Submodule.isIdempotentElem_starProjection` (line 255), `range_starProjection` (260), `starProjection_eq_self_iff` (248), `inner_starProjection_left_eq_right` (610), `starProjection_isSymmetric` (616).
- `LinearIsometry.map_starProjection` (line 298) and `Submodule.starProjection_map_apply` (316) implement transport of projections by isometries/unitaries. Invariance for t and -t gives equality of the mapped subspace; these lemmas then yield commutation. No abstract spectral commutant API is needed.
- `Lp.compMeasurePreservingₗᵢ` (`Function/LpSpace/Basic.lean:667`) bundles translation as a linear isometry. `coeFn_compMeasurePreserving` (607), `compMeasurePreserving_comp` (632), and `compMeasurePreserving_id` (624) establish representatives and the inverse using translation by -t.
- `SchwartzMap.compSubConstCLM` (`Analysis/Distribution/SchwartzSpace/Basic.lean:1068`) supplies translation on Schwartz functions; its value is f(x-a). `VectorFourier.fourierIntegral_comp_add_right` (`FourierTransform.lean:107`) supplies the classical translation/character identity with the sign explicitly determined by f(x+a).
- Extend that identity from Schwartz to L² by `SchwartzMap.denseRange_toLpCLM` and continuity. No direct L² translation/character theorem was found in LpSpace.lean; this extension remains necessary.
- `ContinuousLinearMap.holderL` (`MeasureTheory/Function/Holder.lean:129`) builds the L∞×L²→L² character multiplication map from complex multiplication. Its `coeFn_holder` (line 79) gives a.e. representatives; norm one of characters gives isometry. Alternatively construct the isometry from `MemLp.toLp` and `eLpNorm_congr_norm_ae`.
- `MeasureTheory.L2.inner_def` (`Function/L2Space.lean:136`) writes the Hilbert inner product as a pointwise integral; `L2.integrable_inner` (173) gives the needed integrability. Complex inner products are conjugate-linear in their first argument: use the swapped pair or conjugate explicitly when matching Rudin's `f * conj(g)` convention. `MemLp.integrable_mul` (`Function/L1Space/Integrable.lean:1086`) is another direct L²×L²→L¹ route with the appropriate `HolderTriple` instance.
- g∈L² follows from `memLp_two_iff_integrable_sq_norm` (`Function/L2Space.lean:45`) and `integrable_exp_neg_mul_sq` (`Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:116`) with b=2; `Real.exp_pos` supplies nonvanishing. A pre-existing bundled Gaussian Schwartz function is unnecessary.

Remaining new work for 9.17: build/transport character multiplication, prove the L² translation identity, match the complex inner-product orientation, derive the Fourier-equality identity with explicit signs, build the a.e. multiplier and show its idempotence, then prove both inclusions of the range description. All of these are genuine proof obligations, not new hypotheses added to the printed theorem.
