# Chapter 9 normalization: pinned interfaces

Research only; no Chapter 9 Lean implementation or compilation performed. Paths below are relative to the pinned Mathlib root `.lake/packages/mathlib/Mathlib` in this lane's book checkout.

Let `s = Real.sqrt (2 * Real.pi)`, `c = 1 / s`, and `m = ENNReal.ofReal c • (volume : Measure ℝ)`. First prove `0 < s` by `Real.sqrt_pos.2`, `s ≠ 0`, and `s^2 = 2*pi` by `Real.sq_sqrt`. In algebraic rewrites, normalize `c` to `s⁻¹`. All square-root arguments are positive.

## The exact Lp isometry

Set `e : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ s hs_ne`. Its function is `u ↦ s*u`, and its inverse is `x ↦ s⁻¹*x`.

| Interface | Exact role and location |
|---|---|
| `MeasurableEquiv.mulLeft₀`, `coe_mulLeft₀`, `symm_mulLeft₀` | Measurable equivalence and inverse formula. `MeasureTheory/Group/MeasurableEquiv.lean:138,145,148`. |
| `Real.map_volume_mul_left (h : a ≠ 0)` | `Measure.map (a * ·) volume = ENNReal.ofReal \|a⁻¹\| • volume`. `MeasureTheory/Measure/Lebesgue/Basic.lean:318`. |
| `MeasurePreserving.symm e h` | If `h : MeasurePreserving e μ ν`, returns `MeasurePreserving e.symm ν μ`. **The e argument is explicit.** `Dynamics/Ergodic/MeasurePreserving.lean:72`. |
| `Lp.compMeasurePreservingₗᵢ ℂ e h` | For `[Fact (1 ≤ p)]`, a map `Lp ℂ p ν →ₗᵢ[ℂ] Lp ℂ p μ`. Composition is contravariant in the measures. `MeasureTheory/Function/LpSpace/Basic.lean:667`. |
| `Lp.coeFn_compMeasurePreserving g h` | Representative equality `compMeasurePreserving e h g =ᵐ[μ] g ∘ e`. Same file:607. |
| `Lp.compMeasurePreserving_comp_apply g hf hf'` | Composition rule: pullback by `f ∘ f'` equals first pullback by f, then by f'. Same file:639. |
| `Lp.compMeasurePreserving_id_apply` | Pullback by id is id. Same file:629. |
| `LinearIsometryEquiv.ofLinearIsometry U V.toLinearMap hUV hVU` | Builds an equivalence from a linear isometry U and an explicit inverse linear map V. Requires `U.toLinearMap.comp V.toLinearMap = LinearMap.id` and the reverse identity. `Analysis/Normed/Operator/LinearIsometry.lean:979`. |
| `LinearIsometryEquiv.coe_ofLinearIsometry_symm` | The inverse is definitionally the supplied V, avoiding a choice-based inverse. Same file:992. |

Construct `hscale : MeasurePreserving e volume m` by fields: measurability from e; map equality from `Real.map_volume_mul_left hs_ne`, simplifying `abs_of_pos (inv_pos.mpr hs_pos)` and `one_div`. Then `hinv := MeasurePreserving.symm e hscale`.

Define the two *research interfaces*:

    U : Lp ℂ p m →ₗᵢ[ℂ] Lp ℂ p volume
      := Lp.compMeasurePreservingₗᵢ ℂ e hscale
    V : Lp ℂ p volume →ₗᵢ[ℂ] Lp ℂ p m
      := Lp.compMeasurePreservingₗᵢ ℂ e.symm hinv

For U∘V, use the composition lemma with `hf=hinv`, `hf'=hscale`, so the composite underlying map is `e.symm ∘ e = id`. For V∘U reverse these arguments and use `e ∘ e.symm = id`. Extensionality of linear maps and the id-pullback lemma give the two inverse identities. Proof irrelevance handles the proof fields in the composed measure-preserving witnesses. This supplies `Uequiv` via `ofLinearIsometry`.

The a.e. formulas are exactly `(Uf)(u)=f(s*u)` with respect to volume, and `(Vg)(x)=g(x/s)` with respect to m. There is **no amplitude factor**. This route works for every `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`, including ∞; only translation-continuity applications later need `p ≠ ∞`.

For actual functions before quotienting, `MemLp.comp_measurePreserving` (`LpSeminorm/Basic.lean:1001`) and `Lp.toLp_compMeasurePreserving` (`LpSpace/Basic.lean:620`) connect the same operation to `MemLp.toLp`.

## Two transform adapters

The convenient *definition* for exact Rudin conventions is

    Fourier.fourierIntegral Real.probChar m f t

not the default `𝓕`, which has ordinary volume and a 2π phase. `Real.probChar` is already an additive character into `Circle`, with `Real.probChar_apply x = Complex.exp (x * I)` and `Real.continuous_probChar` (`Analysis/Complex/Circle.lean:247–257`). `VectorFourier.fourierIntegral_probChar` (`Fourier/FourierTransform.lean:287`) gives the exact integral `∫ x, exp (-(x*t)*I) • f x ∂m`; specialize its pairing to `LinearMap.mul ℝ ℝ`. `Fourier.fourierIntegral` is that specialization by definition (same file:340).

Write FR for this transform and FM for default Mathlib `𝓕`. Prove both adapters:

1. **Same coordinate:** `FR f t = c • FM f (t / (2*pi))`.
2. **Isometric coordinate:** `FR f (s*v) = FM (fun u => f (s*u)) v`, equivalently `U(FR f)=FM(Uf)`.

Adapter 1 uses `integral_smul_measure` (`Bochner/Basic.lean:1047`), `ENNReal.toReal_ofReal hc_nonneg`, and `Real.fourier_real_eq_integral_exp_smul` (`FourierTransform.lean:485`); identify exponents using `pi ≠ 0` and complex cast/ring algebra.

Adapter 2 uses `MeasurePreserving.integral_comp' hscale integrand` (`Bochner/Basic.lean:1115`) and `s*s=2*pi`. This change-of-variables lemma requires no integrability hypothesis because e is a measurable equivalence. Positive-sign inverse transforms have the identical adapters with signs reversed.

For L2, the candidate exact Rudin unitary is

    Uequiv.trans ((Lp.fourierTransformₗᵢ ℝ ℂ).trans Uequiv.symm).

`Lp.fourierTransformₗᵢ` is the Mathlib volume-based complex linear isometric equivalence (`Fourier/LpSpace.lean:51`). Conjugation gives norm/inner-product/inverse/surjectivity immediately; **the arbitrary L1∩L2 compatibility bridge is still required**, since the library's explicit compatibility is only `SchwartzMap.toLp_fourier_eq` (same file:101).

## Exact routes for 9.2 and 9.6

| Printed clause | Precise adapter / proof recipe |
|---|---|
| 9.2(a): `g(x)=f(x)exp(i*a*x)` gives `FR g(t)=FR f(t-a)` | Direct `integral_congr`; combine exponentials with `← Complex.exp_add`, then ring on the exponents. No dedicated real-line modulation theorem was found. Integrability is obtained from `VectorFourier.fourierIntegral_convergent_iff Real.continuous_probChar ... (-a)` (`FourierTransform.lean:136`). |
| 9.2(b): `g(x)=f(x-a)` gives `FR g(t)=FR f(t)exp(-i*a*t)` | `Fourier.fourierIntegral_comp_add_right Real.probChar m f (-a)` (`FourierTransform.lean:358`), then `sub_eq_add_neg`, `Circle.smul_def`, `Real.probChar_apply`. The scaled measure has the inherited `isAddRightInvariant_smul` instance (`MeasureTheory/Group/Measure.lean:63`). |
| 9.2(c): convolution product | `Real.fourier_mul_convolution_eq hf hg ξ` is for volume and default FM (`Fourier/Convolution.lean:121`). Use `f *_R g = c • (f *_M g)` and adapter 1: the two factors of c on the left match `(c*FMf)*(c*FMg)`. Alternatively conjugate convolution by U, where `U(f *_R g)=(Uf)*_M(Ug)`. |
| 9.2(d): **conjugate-reflection** `g(x)=conj(f(-x))` gives `FR g=conj(FR f)` | Use `integral_neg_eq_self integrand m` (`MeasureTheory/Group/Integral.lean:41`, generated additively from `integral_inv_eq_self`) and `integral_conj` (`Bochner/ContinuousLinearMap.lean:173`); simplify with `Complex.exp_conj`, `map_mul`, and conjugation of real casts/I. No standalone real-line conjugate-reflection Fourier theorem was found. |
| 9.2(e): `g(x)=f(x/λ)`, **λ>0**, gives `FR g(t)=λ*FR f(λ*t)` | `Measure.integral_comp_div (g : ℝ → E) (λ : ℝ)` yields `∫x,g(x/λ) = \|λ\| • ∫x,g(x)` (`Measure/Haar/NormedSpace.lean:168`); take the kernel integrand at frequency λt, use λ≠0 and `abs_of_pos`. Combine with `integral_smul_measure` for m. Also available: `Measure.integral_comp_mul_left/right`, inverse-mul variants (same file:152–165). |
| 9.2(f): `g(x)=-i*x*f(x)` integrable gives `HasDerivAt (FR f) (FR g t) t` | Adapter 1 + `Real.hasDerivAt_fourier hf_vol hxf_vol (t/(2*pi))` (`FourierTransformDeriv.lean:761`). Its weighted hypothesis is `Integrable (fun x : ℝ => x • f x) volume`, and derivative is `FM (fun x => (-2*pi*I*x) • f x)`. Compose using **`HasDerivAt.scomp`** with `(hasDerivAt_id t).div_const (2*pi)`, then `HasDerivAt.const_smul c`; the 2π factors cancel. Derive hxf from the printed g-integrability by multiplying g by I. |
| 9.6 continuity and norm | Direct `VectorFourier.fourierIntegral_continuous Real.continuous_probChar continuous_pairing hf` (FourierTransform:163), and `VectorFourier.norm_fourierIntegral_le_integral_norm` (:100). |
| 9.6 vanishing at infinity | Adapter 1 plus `Real.zero_at_infty_fourier f` (`RiemannLebesgueLemma.lean:215`). Compose with nonzero dilation tending cocompact-to-cocompact using `Filter.tendsto_cocompact_mul_right₀` (`Topology/Algebra/Field.lean:35`), then multiply by c. |

Measure-convention conversion for derivative/convolution hypotheses is exactly `integrable_smul_measure hc_ne_zero hc_ne_top : Integrable f (cENN • μ) ↔ Integrable f μ` (`Function/L1Space/Integrable.lean:329`). Do not replace the printed `g ∈ L¹` with unproved differentiability of f. `Real.fourier_deriv` is a different theorem requiring everywhere differentiability of f and is not the adapter for 9.2(f).

Minimal extra imports to plan for: `MeasureTheory.Group.MeasurableEquiv`, `MeasureTheory.Measure.Lebesgue.Basic`, `MeasureTheory.Measure.Haar.NormedSpace`, `MeasureTheory.Function.LpSpace.Basic`, `Analysis.Fourier.FourierTransform`, `Analysis.Fourier.FourierTransformDeriv`, and `Topology.Algebra.Field`. Exact imports may already be public transitive dependencies; no compile was run to minimize them.

A practical negation-invariance fallback for 9.2(d): `(Measure.measurePreserving_neg volume).smul_measure (ENNReal.ofReal c)` gives measure preservation of negation for m directly (`Dynamics/Ergodic/MeasurePreserving.lean:185`). Combine it with `MeasurePreserving.integral_comp` and the measurable embedding of negation. This avoids relying on typeclass search for an `IsNegInvariant m` instance while the new measure definition is being introduced.
