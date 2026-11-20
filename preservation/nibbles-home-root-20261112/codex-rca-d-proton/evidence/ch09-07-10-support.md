# Chapter 9.7–9.10 support at pinned Mathlib

Research only; no Chapter 9 Lean declarations created. Mathlib pin is
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Printed statements and normalization

Primary source: `sources/rudin-rca-third.pdf`, printed pp.183–185, text lines
10047–10127. Equation 9.7(3) visually verified in
`sources/ch09-verification-183.png` (PDF page 196, one-based).

The chapter uses `dm = dx / sqrt(2*pi)` and its convolution uses this same `m`.

* **9.7:** `H(t)=exp(-|t|)`; for `lambda>0`,
  `h_lambda(x)=integral H(lambda*t)*exp(i*t*x) dm(t)`;
  `h_lambda(x)=sqrt(2/pi)*lambda/(lambda^2+x^2)`;
  `integral h_lambda dm=1`; `0<H(t)<=1`; `H(lambda*t)->1` as `lambda->0`.
* **9.8:** If `f` is L1, for every x and positive lambda,
  `(f*h_lambda)(x)=integral H(lambda*t)*fhat(t)*exp(i*x*t) dm(t)`.
* **9.9:** If `g` is L-infinity and continuous at x, then
  `(g*h_lambda)(x)->g(x)` as lambda tends to zero through positive values.
* **9.10:** For `1<=p<infinity` and `f` in Lp,
  `norm_p(f*h_lambda-f)->0`. The proof explicitly establishes existence of
  convolution at every x using conjugate-exponent kernel membership. Its
  parenthetical continuity assertion refers to Exercise 8.

## Exact kernel and transform support

`Probability/Distributions/Cauchy.lean` exports:

* `ProbabilityTheory.cauchyPDFReal x0 gamma x`
  is `pi⁻¹*gamma*((x-x0)^2+gamma^2)⁻¹`, with `gamma : NNReal` (line44).
* `cauchyPDFReal_def'` rewrites this as
  `pi⁻¹*gamma⁻¹*(1+((x-x0)/gamma)^2)⁻¹` (line64).
* `cauchyPDF_pos` (line122), `integral_cauchyPDFReal_eq_one` (line129),
  `integrable_cauchyPDFReal` (line142), `lintegral_cauchyPDF_eq_one` (line155).
* `cauchyMeasure_of_scale_ne_zero` and
  `instIsProbabilityMeasure_cauchyMeasure` give the normalized weighted measure.

Thus the measure with density `h_lambda` relative to Rudin's `m` is exactly
the centered Cauchy measure with scale lambda. One can define the kernel through
`sqrt(2*pi)*cauchyPDFReal 0 gamma`, then prove its printed formula, or define
the printed formula and prove the density equality.

No direct half-plane Poisson Fourier-transform theorem was found. The similarly
named `Analysis/Complex/Poisson.lean` treats a disk/circle kernel and does not
directly give this transform.

The short elementary Fourier computation is supported by
`Analysis/SpecialFunctions/ImproperIntegrals.lean`:

* `integrableOn_exp_mul_complex_Ioi` and `_Iic` (lines64–75).
* `integral_exp_mul_complex_Ioi` (line87): for `a.re<0`,
  `integral_(c,infinity) exp(a*x) dx = -exp(a*c)/a`.
* `integral_exp_mul_complex_Iic` (line96): for `0<a.re`,
  `integral_(-infinity,c] exp(a*x) dx = exp(a*c)/a`.
* `integrable_inv_one_add_sq` (line274),
  `integral_univ_inv_one_add_sq` (line292), and the scaled variants (297,302).

Split at zero with `integral_Iic_add_Ioi` (IntervalIntegral/Basic:1214).
The two exponential coefficients are `lambda+i*x` and `-lambda+i*x`; adding
the half-line integrals gives `2*lambda/(lambda^2+x^2)` before multiplying by
Rudin's measure constant. This proves the inverse-transform formula without
depending on the later inversion theorem.

For 9.8, `Integrable.mul_prod` (Integral/Prod:297) proves product domination,
and `integral_integral_swap` handles Fubini. The oscillatory factor has norm one.
`integral_sub_left_eq_self` and related Haar translation/substitution lemmas
handle the change of variables.

## Approximation at a point

`MeasureTheory.convolution_tendsto_right` (Analysis/Convolution:835) assumes
that **supports** shrink to zero. It does not apply directly to these full-support
Poisson kernels. The bump-function specializations have the same restriction.

Use the printed scaling `h_lambda(y)=lambda⁻¹*h_1(y/lambda)` and
`Measure.integral_comp_mul_left` / `_inv_mul_left`
(Measure/Haar/NormedSpace:152–158) to rewrite the convolution error as the
integral of `(g(x-lambda*s)-g(x))*h_1(s)`.

`tendsto_integral_filter_of_dominated_convergence`
(Integral/DominatedConvergence:67) accepts a countably generated filter,
eventual AE measurability, eventual AE bounds, and AE pointwise convergence.
It applies directly to the positive-neighborhood filter at zero.

For an L-infinity representative, avoid assuming a global pointwise bound.
Use an integrable majorant `(essSupNorm(g)+norm(g(x)))*h_1(s)`.
`quasiMeasurePreserving_smul` (Lebesgue/EqHaar:345), combined with translation
and negation, transports the AE bound through `s -> x-lambda*s` for lambda>0.
`AEStronglyMeasurable.comp_quasiMeasurePreserving` is in the corresponding
strong-measurability file (line620).

## Lp approximation and the Jensen step

Full pinned-source searches for `eLpNorm_integral`, `lpNorm_integral`,
integral Minkowski, and convolution Lp convergence found no direct integral
Minkowski or full Poisson approximate-identity theorem.

There is no need to implement Jensen from scratch:

1. For the probability measure `nu_lambda = h_lambda * m`,
   `enorm_integral_le_lintegral_enorm` (Bochner/Basic:333) bounds the norm of
   an integral by its L1 norm.
2. `eLpNorm_le_eLpNorm_of_exponent_le`
   (LpSeminorm/CompareExp:115) gives `norm_1 <= norm_p` on **any probability
   measure**, assuming only `1<=p`. The real-exponent variant is at line108.
3. Raising this inequality to p yields the printed Jensen estimate, including
   the endpoint p=1. `eLpNorm_one_eq_lintegral_enorm` and
   `eLpNorm_eq_lintegral_rpow_enorm_toReal` expose the integrals.
4. Convert weighted integrals with
   `integral_withDensity_eq_integral_toReal_smul`
   (Bochner/ContinuousLinearMap:317) and the standard lintegral withDensity
   formula; apply Tonelli.
5. Apply 9.9 at zero to the globally bounded function
   `y -> norm_p(translation_y f-f)^p`, continuous at zero by 9.5, and squeeze.

An alternate ready-made Jensen theorem is `ConvexOn.map_integral_le`
(Analysis/Convex/Integral:197), requiring continuity of the convex map and
integrability of both the input and composed map. The Lp-comparison route has
fewer side conditions and permits extended intermediate integrals.

For pointwise existence, use
`ConvolutionExists.of_memLp_memLp` (Analysis/Convolution:548):
`[p.HolderConjugate q]`, `MemLp f p`, `MemLp h q` imply convolution exists
**everywhere**. `enorm_convolution_le` follows at line557.
For the kernel, prove finite-q membership from positive boundedness and L1:
`h^q <= C^(q-1)*h`. `memLp_top_of_bound` (LpSeminorm/Basic:611) handles
q=infinity. `MemLp.mono_exponent` requires finite measure and therefore does
not justify this step on the whole real line.

The final 9.10 statement should retain `MemLp (f*h_lambda) p` for every
positive lambda before converting `eLpNorm` to a real number: `infinity.toReal=0`
must not hide a non-Lp convolution. Jensen plus Tonelli and the bounded
translation-error norm supply the required finiteness.
