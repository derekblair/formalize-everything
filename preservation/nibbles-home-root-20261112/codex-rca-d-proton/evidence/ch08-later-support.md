# Later Chapter 8 support at pinned Mathlib

Source: `sources/rudin-rca-third.pdf`, printed pages 170–174; corresponding text lines 9314–9531. Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Node | Printed content | Support / remaining work |
|---|---|---|
| 8.13 | Motivation for a.e. convolution existence, and L1-product counterexample | Complete a.e. existence follows from 8.14. The illustrative `x^(-1/2)` product counterexample is not yet formalized here. |
| 8.14 | Complex L1 convolution absolutely converges a.e., is integrable, and satisfies sharp L1 norm bound | Full candidate `theorem_8_14` in `Ch08Later.lean`. Uses Mathlib `Integrable.ae_convolution_exists`, `Integrable.integrable_convolution`, and `integral_convolution`; adds the norm estimate explicitly. |
| 8.15 | Extended distribution function, antitone/Borel, layer cake | Definition/antitone/Borel in `Ch08Later.lean`; full genuinely extended-valued layer cake candidate `layerCake_ennreal` in `Ch08LayerCake.lean`. Mathlib's own `lintegral_eq_lintegral_meas_lt` accepts real-valued f only. |
| 8.16 | Extended-valued layer cake with monotonic locally absolutely continuous φ, φ(0)=0, continuous limit at ∞ | Full candidate `theorem_8_16` in `Ch08Phi.lean`. Uses Tonelli on the subgraph, absolutely-continuous FTC, and AECover at ∞. Real-coordinate finite-value premise makes explicit what local absolute continuity means. **Printed hypothesis is AC, not C1.** |
| 8.17 | Recall weak (1,1) estimate from 7.4; L∞ contraction of maximal function | No maximal function/weak-type declaration found by full pinned Mathlib text searches. New definitions and the elementary L∞ argument are in `Ch08Maximal.lean`; the concrete weak estimate with constant `5^dim` is in `Ch08WeakMaximal.lean`. |
| 8.18 | Hardy–Littlewood maximal function maps Lp(R^k) to Lp(R^k), 1<p<∞ | No direct or variant theorem found. Mathlib has Vitali/Besicovitch covering and differentiation theorems, but no Hardy–Littlewood maximal operator or Marcinkiewicz interpolation theorem. Concrete new proof is drafted across `Ch08WeakMaximal.lean`, `Ch08PowerLayerCake.lean`, and `Ch08StrongMaximal.lean`: covering bound, measurable maximal function, truncation, extended power layer cake, strong integral estimate, AE finiteness, and actual complex-input Lp membership. No weak-type premise is assumed. The parameterized cutoff and optimized norm estimate are now drafted in `Ch08ParameterizedMaximal.lean` and `Ch08MaximalNorm.lean`; root supplies scalar coefficient bounds and endpoint limits in `Ch08MaximalConstant.lean`. |

## Exact relevant Mathlib declarations

- `Analysis/Convolution.lean`: `Integrable.convolution_integrand` (271), `Integrable.ae_convolution_exists` (288), `Integrable.integrable_convolution` (527), `convolution_mul_swap` (704), `integral_convolution` (890).
- `MeasureTheory/Integral/Layercake.lean`: `lintegral_comp_eq_lintegral_meas_lt_mul` (478), `lintegral_eq_lintegral_meas_lt` (496). The hypotheses quantify `f : X → ℝ`, so directly aliasing these is not full 8.15/8.16.
- `MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`: `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` (225).
- `MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`: `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` (160).
- `Analysis/Calculus/Deriv/Slope.lean`: `Monotone.deriv_nonneg` (191).
- `MeasureTheory/Integral/IntegralEqImproper.lean`: `aecover_Iio` (176), `AECover.lintegral_eq_of_tendsto` (394).
- `MeasureTheory/Covering/Vitali.lean`: `exists_disjoint_subfamily_covering_enlargement_ball` (195), `exists_disjoint_covering_ae` (237). These are plausible ingredients for a new maximal weak (1,1) proof, not substitutes for it.

## Validation status

Initial two Lean checks were deliberately terminated with exit 143 because the shared machine exhausted RAM/swap. Checks now use Lean module imports and one compiler per lane. `ch08-all-support-check2.log` has no errors in `Ch08Later.lean`, `Ch08LayerCake.lean`, or `Ch08Phi.lean`; all six remaining diagnostics were in maximal support and have been fixed in source. Combined check3 exited 1: every earlier family, including all concrete weak-maximal support, elaborated cleanly; only four local errors in the new power/strong interpolation fragments remained and are now fixed in source. Combined check4 exited 1 with four local diagnostics in support fragments (unfolding the weight in two tails, and pointwise AE power equalities in two conversions), plus root-owned scalar-limit diagnostics. All four support diagnostics are fixed in source. The remaining strong estimates, AE finiteness, optimized norm conversion, and Euclidean specialization had no body errors. Explicit weak-L1 and L∞ norm wrappers for 8.17 were added after the check4 snapshot. All current fragments are handed to root for the integrated production build and axiom audit; no further standalone support check is planned. Scope is frozen. **No complete exit-0 or final axiom audit is claimed by this support lane yet; the production build/audit is owned by root.**
