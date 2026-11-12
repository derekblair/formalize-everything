# Chapter 19.1–19.3 Fourier implementation plan

Read-only research against Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. No Chapter 19 implementation or checks have been run. This supplements `INVENTORY-19-20.md`; it is not completion evidence.

## Printed normalization and exact obligations

Source: `scope-source-rudin.txt` lines 20371–20680, printed pp. 371–376. The chapter explicitly changes from Chapter 9's normalized measure to ordinary Lebesgue measure.

* 19.1(a): for `F ∈ L²(0,∞)`, `f(z)=∫₀∞ F(t) exp(i t z) dt` is holomorphic on `{z | 0 < z.im}` and, for every `y>0`,
  `(1/(2π)) ∫ℝ ‖f(x+iy)‖² dx = ∫₀∞ ‖F(t)‖² exp(-2ty) dt ≤ ∫₀∞ ‖F(t)‖² dt`.
* 19.1(b): for `A>0`, `F ∈ L²(-A,A)`, the same finite-interval integral is entire; its real restriction lies in L²; `‖f(z)‖ ≤ C exp(A‖z‖)` with `C=∫_{-A}^A ‖F(t)‖ dt <∞`. The intermediate sharper estimate is `‖f(z)‖ ≤ C exp(A|z.im|)`.
* 19.2: every holomorphic upper-half-plane function with uniformly bounded horizontal L² integrals has that representation; the exact supremum `C` equals `∫₀∞ ‖F‖²`. A theorem giving only `≤ C` would omit the printed equality. An arbitrary supplied upper bound `C` must be distinguished from the supremum.
* 19.3: entire `f`, `A,C>0`, global `‖f(z)‖≤C exp(A‖z‖)`, and real restriction in L² imply an `L²(-A,A)` integral representation at **every complex point**, not merely almost every real point. Endpoints do not matter for Lebesgue integration; support in `[-A,A]` faithfully adapts to L² on `(-A,A)`.

## Fourier sign and scaling: keep one explicit adapter

Mathlib uses ordinary Lebesgue measure and

`𝓕 h ξ = ∫ℝ exp(-2π i x ξ) h(x) dx`.

The exact source declaration is `Real.fourier_real_eq_integral_exp_smul` in `Analysis/Fourier/FourierTransform.lean:485`; its type is

```lean
𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v
```

`Real.fourierInv_eq_fourier_neg` at line 460 identifies `𝓕⁻ f w` with `𝓕 f (-w)`. Therefore, for an integrable real-line function `G`,

`∫ G(t) exp(i t x) dt = 𝓕⁻ G (x/(2π))`.

For 19.1 set `G_y(t) = 1_{(0,∞)}(t) F(t) exp(-ty)`. Then

`f(x+iy) = 𝓕⁻ G_y (x/(2π))`.

For the converse, the correct scaled forward transform is

`R h(t) = (1/(2π)) 𝓕 h (t/(2π))`.

Then `R(f_y)(t) = exp(-ty) F(t)` and `∫ ‖R h‖² = (1/(2π)) ∫ ‖h‖²`. The minus sign is already inside Mathlib's forward transform. Do not use `𝓕⁻` in the definition of `R`.

Change of variables is available exactly as `MeasureTheory.Measure.integral_comp_div` in `MeasureTheory/Measure/Haar/NormedSpace.lean:168`:

```lean
(∫ x : ℝ, g (x / a)) = |a| • ∫ y : ℝ, g y
```

This directly produces the factor `2π` in the horizontal Plancherel equality.

## L² Plancherel pipeline and the bridge that needs implementation

`Analysis/Fourier/LpSpace.lean` defines the genuine L² isometric equivalence:

```lean
MeasureTheory.Lp.fourierTransformₗᵢ (E F) :
  (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)
```

For `E=ℝ`, `F=ℂ`, `MeasureTheory.Lp.norm_fourier_eq` (line 94) gives `‖𝓕 f‖=‖f‖`, and `inner_fourier_eq` gives equality of inner products. Inverse Fourier is the inverse isometry, so it preserves norm as well. `MeasureTheory.L2.inner_def` in `MeasureTheory/Function/L2Space.lean:136` identifies the L² inner product with the integral of pointwise inner products. Apply the usual `inner_self_eq_norm_sq_to_K` to get the squared-norm integral identity; do **not** cite the private local `norm_sq_eq_re_inner` at line154 as a public API.

The source directly proves compatibility only for Schwartz functions:

* `SchwartzMap.toLp_fourier_eq` (`LpSpace.lean:101`): `𝓕 (f.toLp 2) = (𝓕 f).toLp 2`.
* `SchwartzMap.toLp_fourierInv_eq` (`:110`): analogous inverse identity.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` (`:125`): Fourier of the distribution represented by an L² function equals the distribution represented by its L² Fourier transform.

The similarly named `Real.fourierTransform_toLp` in `FourierTransform.lean:524` concerns **L¹** and the bounded continuous Fourier transform; it is not the required L² identification. The search of the full pinned Fourier/Distribution directories found no direct declaration identifying the L² Fourier representative with the ordinary Fourier integral for arbitrary L¹∩L² functions.

A concrete route to that missing compatibility lemma is through distributions:

1. Fourier of an L¹ distribution can be computed by Fubini, using `VectorFourier.integral_fourierIntegral_smul_eq_flip` (`FourierTransform.lean:242`) and the integrability of Schwartz test functions.
2. Identify it with the bounded continuous ordinary Fourier transform as a locally integrable distribution.
3. Compare with `Lp.fourier_toTemperedDistribution_eq` for the same L¹∩L² input.
4. Conclude equality almost everywhere using test-function uniqueness (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), or the Lp embedding injectivity once L² membership of the ordinary transform has been obtained. Avoid circularly assuming that membership.

Relevant exact distribution APIs in `Analysis/Distribution/TemperedDistribution.lean`:

* `MeasureTheory.Lp.toTemperedDistribution_apply` (`:169`): evaluation on test function `g` is `∫ x, g x • f x`.
* `MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot` (`:215`): the natural Lp-to-distribution continuous linear map has zero kernel (finite-dimensional domain, locally finite measure).
* `TemperedDistribution.fourier_apply` (`:482`): `𝓕 f g = f (𝓕 g)`.

The most direct implementation of step4 is to let `u` be the L² Fourier representative and `v` the bounded continuous ordinary Fourier integral. Then `u-v` is locally integrable without knowing `v∈L²`. Fubini and distribution compatibility show its integral against every compactly supported smooth test function is zero. Apply `ae_eq_zero_of_integral_contDiff_smul_eq_zero` to obtain `u=v` a.e.; only then transfer `MemLp u 2` to v. This avoids the apparent circularity of using Lp embedding injectivity before proving v belongs to Lp.

An alternative is simultaneous L¹ and L² Schwartz approximation, but that requires proving a common approximation sequence; density in L² alone does not justify convergence of ordinary Fourier integrals.

## 19.1 holomorphy without rebuilding Morera

Use differentiation under the integral with **complex** scalar field. The generic theorem accepts `𝕜=ℂ` despite prose mentioning a real variable:

`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `Analysis/Calculus/ParametricIntegral.lean:288`:

```lean
(hs : s ∈ 𝓝 x₀)
(hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
(hF_int : Integrable (F x₀) μ)
(hF'_meas : AEStronglyMeasurable (F' x₀) μ)
(h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
(bound_integrable : Integrable bound μ)
(h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x)
```

returns integrability of the derivative and `HasDerivAt` of the integral. For a point `z₀.im>0`, choose a small ball on which `z.im≥δ>0`; derivative envelope is `‖F(t)‖ t exp(-δt)` on positive t. Cauchy–Schwarz reduces its integrability to L² of F and integrability of `t² exp(-2δt)`. For compact spectral support, all polynomial factors in t are bounded and `F` is L¹ on the finite-measure interval.

`Analysis/SpecialFunctions/ImproperIntegrals.lean` gives `integrableOn_exp_mul_Ioi` (`:77`) and `integrableOn_exp_mul_complex_Ioi` (`:63`) for a negative real part. Polynomial-times-exponential integrability can also be bounded by a slower exponential, avoiding a gamma-function import. `Complex.norm_exp` is the key pointwise reduction.

This route proves the printed holomorphy conclusions directly; it does not need to copy Rudin's Morera proof.

## 19.2 contour and convergence prerequisites

The rectangular Cauchy identity already exists in exactly the useful form:

`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `Analysis/Complex/CauchyIntegral.lean:296`. For `f` complex differentiable on the closed rectangle with opposite corners z,w, it proves

```text
∫[z.re,w.re] f(x+i z.im) dx - ∫[z.re,w.re] f(x+i w.im) dx
+ i ∫[z.im,w.im] f(w.re+i y) dy - i ∫[z.im,w.im] f(z.re+i y) dy = 0.
```

Apply it to `z ↦ f z * exp(-i t z)`, corners `-α+i` and `α+i y`. Since both heights are strictly positive, their entire closed interval lies in the upper half-plane. This avoids an arbitrary path-integral formalization.

Still required local lemmas:

* From the uniform horizontal L² bound, Fubini gives integrability of `A(β)=∫_{min(1,y)}^{max(1,y)} ‖f(β+iu)‖² du`.
* Choose a common sequence `α_j→∞` with `A(α_j)+A(-α_j)→0`; this sequence must be independent of t. An integrability-versus-infinite-tail-measure argument yields the needed choice. No direct ready-made selection lemma was located in the improper-integral sources inspected.
* Cauchy–Schwarz bounds both vertical integrals and gives the book's pointwise-in-t limit identity.
* Truncations of each horizontal L² function converge in L². Continuity of the L² Fourier isometry transports this to transformed truncations.
* `MeasureTheory.tendstoInMeasure_of_tendsto_Lp` (`MeasureTheory/Function/ConvergenceInMeasure.lean:461`) followed by `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` (`:273`) provides an almost-everywhere subsequence. For each fixed y, extract a common subsequence for heights y and1; their null exceptional sets may depend on y, which is sufficient.
* Define F from the height1 transformed representative; derive `exp(-ty)F(t)=R(f_y)(t)` a.e. for each y. Fatou/monotone convergence as y→∞ kills the negative half-line, and as y↓0 gives the L² bound. The forward 19.1 equality then supplies exact equality with the supremum.

The final reconstruction must use the L¹∩L² compatibility lemma, since the exponentially weighted F is L¹. `MeasureTheory.Integrable.fourierInv_fourier_eq` in `Analysis/Fourier/Inversion.lean:165` assumes both a function and its ordinary Fourier transform are L¹; it cannot by itself invert a merely L² horizontal function. Equality of continuous representatives upgrades the L²/a.e. equality to equality at all real x.

## 19.3 ray deformation: primitives are a useful substitute for sectors

The book introduces `Φ_α(w)=exp(iα)∫₀∞ f(s exp(iα)) exp(-w s exp(iα)) ds`, holomorphic when `Re(w exp(iα))>A`. The α=0,π rays have the larger half-plane domains from the L² hypothesis. Show overlap agreement by a circular arc estimate, then analytic continuation.

A general sector-contour theorem is unnecessary. For fixed w, `z↦f(z)exp(-wz)` is entire. `Differentiable.isExactOn_univ` in `Analysis/Complex/HasPrimitives.lean:310` supplies a global primitive; `Complex.IsExactOn` (`:116`) means `∃g,∀z∈univ,HasDerivAt g (integrand z) z`. Compose that primitive with radial segments and circular arcs, and use interval-integral FTC. The resulting endpoint cancellation is exactly the needed ray/arc identity. This avoids building a general contour API.

Then prove exponential arc decay when `w=|w|exp(-i(α+β)/2)` and `|w| cos((β-α)/2)>A`. Complex analytic identity on the connected overlap of two half-planes extends agreement from this ray. The printed regularization `f_ε(x)=f(x)exp(-ε|x|)` lies in L¹∩L²; it converges to f in L² as ε↓0. The regularized Fourier integrals vanish in the limit at every frequency `|t|>A` by the two ray continuations. Subsequence a.e. convergence then proves compact spectral support of `R f`.

Once support is compact, the forward 19.1(b) transform is entire and gives the same L² boundary function. Equality of continuous real restrictions plus complex identity theorem yields equality for every complex z. No Paley–Wiener theorem was found in the pinned Analysis tree; this is a substantial new proof, not a wrapper around a theorem with a similar name.
