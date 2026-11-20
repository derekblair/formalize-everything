# Chapter 9.3–9.4: exact obligations and implementation routes

Research only; no candidate Lean declarations or compiler checks were added. Printed source: `sources/rudin-rca-third.pdf`, pp. 180–182 (PDF pages 193–195); equation 9.4(7) visually checked in `evidence/ch09-page181.png`. Pinned Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`. Paths below are relative to its `Mathlib/`; during the Chapter 8 clean build the inspected checkout is `evidence/lake-before-clean-ch08/packages/mathlib/`.

## 9.3: sequential limits and finite differences

**(a) Sequential justification.** The preceding difference quotient in 9.2 assumes `s ≠ t`. The formal content is that convergence of that quotient along every sequence tending to the *punctured* neighborhood of `t` implies its punctured limit. It is not a statement about all sequences tending to `t`, since a sequence constantly equal to `t` would sample Lean's totalized quotient at zero.

Use `Filter.tendsto_iff_seq_tendsto` or `Filter.tendsto_of_seq_tendsto` in `Order/Filter/AtTopBot/CountablyGenerated.lean:84,95`, with source filter `𝓝[≠] t`. The source needs `IsCountablyGenerated`, available for this real punctured neighborhood. A faithful endpoint may specialize the generic equivalence to

`q s = (fourier f s - fourier f t) / ((s - t : ℝ) : ℂ)`.

Alternatively expose the actual derivative limit from 9.2(f) and cite this generic sequential characterization in the node documentation. Applying ordinary-neighborhood `tendsto_nhds_iff_seq_tendsto` without handling the deleted point is incorrect.

**(b) Displayed finite-difference identity.** For `f ∈ L¹(m)` and real `α ≠ 0`, define `Dα f x = (f (x + α) - f x) / α`. Prove its integrability and

`fourier (Dα f) t = fourier f t * (Complex.exp (I * α * t) - 1) / α`.

This follows from 9.2(b), linearity, and translation invariance. In the direct `Real.probChar` implementation, `VectorFourier.fourierIntegral_comp_add_right` (`Analysis/Fourier/FourierTransform.lean:108`) already uses the literal `f (x + α)` and gives the positive phase. `VectorFourier.fourierIntegral_add` (152) and `integral_sub`/`integral_smul` supply linearity; integrability of translated `f` must be retained. Rearrange the scalar factors in `ℂ` to match the displayed formula.

**Explicit exercise boundary.** The subsequent derivative-transform statement under `f,f′ ∈ L¹` and the indefinite-integral hypothesis is expressly left as an exercise, together with related results. It is not an additional v1 proof obligation. Record the motivation and exercise reference; do not introduce stronger differentiability assumptions and count them as a proof of a required node.

## 9.4: Fourier-series analogy

Use `T = 2 * Real.pi`, `AddCircle T`, and **normalized** `AddCircle.haarAddCircle`, whose mass is one. The default circle volume is scaled differently. With `a = -Real.pi`, `AddCircle.fourierCoeff_eq_intervalIntegral` (`Analysis/Fourier/AddCircle.lean:303`) recovers the printed coefficient

`c n = (1/(2π)) ∫ x in -π..π, f x * exp(-I*n*x)`.

The recalled assertions have explicit earlier-chapter provenance:

- The `L²` convergence assertion recalls §4.26. It is directly supported by `AddCircle.hasSum_fourier_series_L2` (433). For literal symmetric partial sums use `Filter.tendsto_Icc_neg` (`Order/Filter/AtTopBot/Interval.lean:79`) to specialize its `HasSum` limit.
- Failure of pointwise convergence for some continuous functions recalls §5.11–5.12. No corresponding pinned Mathlib counterexample was found. Per the cluster boundary, record this earlier-chapter dependency explicitly, rather than expand this lane into Chapter 5 or claim it follows from the summable-coefficient theorem.

### The actual new argument: arbitrary L¹ plus absolutely summable coefficients

A faithful endpoint is: if `Integrable f haarAddCircle` and `Summable (fun n : ℤ => ‖fourierCoeff f n‖)`, then there exists `g : C(AddCircle T, ℂ)` such that

1. `HasSum (fun n => fourierCoeff f n • fourier n) g` in the continuous-function sup norm;
2. `∀ n, fourierCoeff g n = fourierCoeff f n`;
3. `f =ᵐ[haarAddCircle] g`;
4. consequently the Fourier series converges to `f x` almost everywhere (and converges uniformly to `g`).

Do **not** replace the first hypothesis by continuity of `f`. The existing `AddCircle.hasSum_fourier_series_of_summable` (495) and `has_pointwise_sum_fourier_series_of_summable` (504) both assume `f : C(AddCircle T, ℂ)`; neither proves the printed arbitrary-`L¹` result.

Implementable proof route:

1. Put `c n = fourierCoeff f n`. By `fourier_norm` (181), `‖c n • fourier n‖ = ‖c n‖`. `Summable.of_norm` in the Banach space of continuous maps constructs its sum `g`. This is uniform convergence and gives continuity without any regularity hypothesis on the original `f`.
2. For each `k`, make the bounded linear functional `Lk(φ) = ∫ x, fourier (-k) x * φ x ∂haarAddCircle` on continuous maps. Its norm is at most one because Haar mass is one and the character has norm one. Apply the functional to the `HasSum`; `AddCircle.fourierCoeff_fourier` (515), `fourierCoeff.const_smul` (338), and the singleton sum compute `Lk(g) = c k`. This formalizes termwise integration and orthogonality in (5). Using dominated convergence instead of packaging `Lk` is equally faithful.
3. Add a reusable **L¹ Fourier-coefficient uniqueness bridge**, described below, and apply it to `f` and `g`. Continuous `g` is integrable on this compact finite-measure circle. This is the substantial missing bridge; the pinned file does not supply an arbitrary-`L¹` coefficient injectivity theorem.
4. `ContinuousMap.evalCLM ℂ x` takes the continuous-map `HasSum` to pointwise `HasSum`; combine with the almost-everywhere equality. Compose with `Filter.tendsto_Icc_neg` if exposing the book's symmetric partial sums explicitly.

### Concrete route for the L¹ uniqueness bridge

For integrable `h` with every Fourier coefficient zero:

1. Define a bounded linear functional `Λh : C(AddCircle T, ℂ) →L[ℂ] ℂ` by `Λh(φ) = ∫ x, φ x * h x`. The bound is `‖Λh(φ)‖ ≤ ‖φ‖ * ∫ ‖h‖`; bounded continuous multiplication preserves integrability. `LinearMap.mkContinuous` plus `norm_integral_le_integral_norm` is a direct construction.
2. `Λh(fourier n) = fourierCoeff h (-n) = 0`. Linearity makes it zero on the character span. `AddCircle.span_fourier_closure_eq_top` (245) and continuity extend this to every continuous test function. This uses uniform density, so it remains valid for `h ∈ L¹`; replacing it with an `L²` inner-product argument would wrongly require `h ∈ L²`.
3. Recover zero integrals on every closed subset `K` of the circle. Treat `K = ∅` separately. For nonempty `K`, use the real continuous cutoffs

   `u n x = max 0 (1 - (n : ℝ) * Metric.infDist x K)`.

   They lie in `[0,1]`, equal one on `K`, and tend pointwise to `K.indicator (fun _ => 1)`. Relevant APIs: `Metric.continuous_infDist_pt`, `Metric.infDist_zero_of_mem`, and `IsClosed.notMem_iff_infDist_pos` in `Topology/MetricSpace/HausdorffDistance.lean:557,493,585`. Cast `u n` to complex continuous maps. Dominated convergence, dominated by `‖h‖`, turns `Λh(u n) = 0` into `∫ x in K, h x = 0`.
4. Apply `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero` (`MeasureTheory/Function/AEEqOfIntegral.lean:376`). It takes precisely integrability and zero integrals on all closed sets. This avoids introducing a smooth-manifold structure on the circle. Finally apply the zero-coefficient result to `h = f - g`; `fourierCoeff.add`, `fourierCoeff.const_smul`, and integrability identify its coefficients.

### Follow-up: replace the explicit distance cutoffs with an existing sequence

A focused second search found a shorter implementation of step 3 above. Import `Mathlib.MeasureTheory.Measure.HasOuterApproxClosed`. The pinned library already constructs the needed sequence, including all bounds and convergence. Exact interfaces, from lines 168–198:

```lean
-- Variables: {X : Type*} [TopologicalSpace X] [HasOuterApproxClosed X]
--            {F : Set X} (hF : IsClosed F)
IsClosed.apprSeq (hF : IsClosed F) : ℕ → (X →ᵇ ℝ≥0)

HasOuterApproxClosed.apprSeq_apply_le_one (hF : IsClosed F) (n : ℕ) (x : X) :
  hF.apprSeq n x ≤ 1

HasOuterApproxClosed.apprSeq_apply_eq_one (hF : IsClosed F) (n : ℕ)
    {x : X} (hxF : x ∈ F) : hF.apprSeq n x = 1

HasOuterApproxClosed.tendsto_apprSeq (hF : IsClosed F) :
  Tendsto (fun n : ℕ ↦ (fun x ↦ hF.apprSeq n x)) atTop
    (𝓝 (F.indicator fun _ ↦ (1 : ℝ≥0)))
```

At line 222 there is an instance `[TopologicalSpace.PseudoMetrizableSpace X] → HasOuterApproxClosed X`, so the circle needs no new approximation construction. This also handles the empty closed set, avoiding a separate case. For a closed `F`, cast `hF.apprSeq n` through `ℝ` to a complex continuous map and apply the vanishing-test-integral hypothesis. Use `tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF)` for each point, coerce the `ℝ≥0` limit to `ℝ`, and multiply/smul by `h x`. Dominated convergence with bound `‖h x‖` gives the zero set integral. Finish with the exact existing theorem:

```lean
-- MeasureTheory/Function/AEEqOfIntegral.lean:375
-- [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero
    {μ : Measure X} {f : X → E}
    (hf : Integrable f μ)
    (h'f : ∀ s : Set X, IsClosed s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0
```

This is the recommended route: only the short DCT bridge is new. A direct theorem already taking all continuous-test integrals was not found after searching `AEEqOfIntegral`, continuous-map density/duality, vector measures, and measure/Riesz extensionality throughout the pinned source.

Nearby alternatives do not eliminate the bridge as directly:

- `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` (`Measure/HasOuterApproxClosed.lean:269`) takes two **positive finite measures** and equality of integrals of every `X →ᵇ ℝ`. Its conclusion is equality of measures. Applying it to complex densities requires separate positive/negative real and imaginary parts, their finite-measure instances, and change-of-density integral identities.
- `MeasureTheory.Integrable.ae_eq_of_withDensityᵥ_eq` (`VectorMeasure/WithDensity.lean:155`) has signature `hf : Integrable f μ`, `hg : Integrable g μ`, `μ.withDensityᵥ f = μ.withDensityᵥ g` → `f =ᵐ[μ] g`, with `[CompleteSpace E]`. It is not a continuous-test criterion; vector-measure equality remains to be proved.
- `ae_eq_zero_of_integral_contMDiff_smul_eq_zero` (`Analysis/Distribution/AEEqOfIntegralContDiff.lean:44`) takes vanishing integrals against smooth compactly supported real tests and local integrability, but requires a finite-dimensional smooth-manifold structure on the domain. This would add unnecessary structure for `AddCircle`; `IsClosed.apprSeq` is simpler.

All follow-up findings are source research only, without elaboration or compilation.

## 9.4: real-line analogy and the invalid interchange

The definition `g x = ∫ t, fourier f t * exp(I*t*x) ∂m` is well-defined as an integrable integral whenever `fourier f ∈ L¹(m)`. Prove integrability of its integrand for **every** `x`; the phase has modulus one. The direct API is `VectorFourier.fourierIntegral_convergent_iff` (`Analysis/Fourier/FourierTransform.lean:136`) at the opposite frequency, with `Real.probChar` and the multiplication pairing. This is an integrability assertion, not yet the inversion theorem. The final `f = g` assertion must be almost everywhere for an arbitrary `L¹` representative and is supplied by 9.11, with its additional continuity-point endpoint if appropriate.

The tempting computation of the transform of `g` contains the printed inner integral

`∫ x : ℝ, Complex.exp (I * ((t - s) * x)) ∂volume`.

**The printed equation (7) uses ordinary `dx`, not normalized `dm`.** For every real `t,s`, this integrand is not Lebesgue integrable, including `t = s`. Prove `¬ Integrable ... volume` by taking the norm of a hypothetical integrability proof, simplifying with `Complex.norm_exp_ofReal_mul_I` or `Complex.norm_exp_I_mul_ofReal` (`Analysis/Complex/Trigonometric.lean:950,954`), and contradicting integrability of the constant real function one. Use `MeasureTheory.integrable_const_iff_isFiniteMeasure` (`MeasureTheory/Function/L1Space/Integrable.lean:146`) and `Real.volume_univ` (`MeasureTheory/Measure/Lebesgue/Basic.lean:125`). The normalized-measure version is also true and can be exposed as a companion through the positive finite scalar change of measure.

This proves the obstruction stated in the text. Do not formalize an unrestricted Fubini swap, identify this ordinary integral with a Dirac delta, or use its totalized Lean value as an inversion argument: Lean's Bochner integral returns a default value when integrability fails. No theorem about every possible regularized or distributional interpretation is asserted here.

The bracketed paragraph on p. 182 mentions that symmetric improper integrals may recover inversion without `fourier f ∈ L¹`, then explicitly declines to pursue that subject. Record the scope remark; it does not add an improper-inversion theorem or an exercise to this cluster.
