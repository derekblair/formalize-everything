# Rudin 7.16(a): pinned proof route

Read-only research, 2026-10-29. No Lean source or compiler run was produced for this node. APIs below were read directly from the lane's pinned Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (Lean 4.34.1). Paths are relative to its `Mathlib/` directory.

The proposed bounded-variation route is viable using existing pinned theorems. No oscillatory change of variables or integration of an absolute cosine is needed. One terminology correction: the points with sine phase `π/2 + nπ` are **alternating sample points**, not stationary extrema of `x² sin(x⁻²)`. Their values alone establish unbounded variation.

## Faithful target and function

Use `f x := x ^ 2 * Real.sin ((x ^ 2)⁻¹)`. At zero this is zero automatically, and away from zero it is exactly the printed function. Target the following assertions separately:

1. `Differentiable ℝ f` and `deriv f 0 = 0`.
2. `¬ IntegrableOn (deriv f) (Set.Icc 0 1) volume`.
3. The explicit printed infinite-mass formulation: `∫⁻ x in Set.Icc 0 1, ENNReal.ofReal |deriv f x| = ∞`.
4. The immediately attached improper-FTC assertion: as `ε → 0+`, `∫ x in ε..1, deriv f x` tends to `f 1 - f 0 = Real.sin 1`.

The same argument proves nonintegrability on `[0,b]` for every `b > 0`; the unit-interval statement suffices for the printed example. Do not state a Bochner integral of the nonintegrable derivative equal to infinity: Bochner integration has a default finite value outside its domain, so the infinite absolute integral must use `lintegral`.

## 1. Differentiability

Away from zero, use the derivative rules for powers, inversion, sine and multiplication. For differentiability alone there is no need to normalize the derivative formula. The usual explicit formula, if later useful, is

`f′(x) = 2*x*sin((x²)⁻¹) - 2*x⁻¹*cos((x²)⁻¹)` for `x ≠ 0`.

At zero, apply `hasDerivAt_iff_tendsto` and squeeze the normalized remainder between zero and `‖x‖`:

`0 ≤ ‖x‖⁻¹ * ‖x² * sin((x²)⁻¹)‖ ≤ ‖x‖`.

The upper estimate follows from `|sin t| ≤ 1`; split the zero case before canceling `‖x‖`. Continuity of the norm supplies the limit. This establishes `HasDerivAt f 0 0` without any assertion that the oscillatory sine has a limit.

Pinned APIs:

| API | Location |
|---|---|
| `hasDerivAt_iff_tendsto` | `Analysis/Calculus/Deriv/Basic.lean:290` |
| `HasDerivAt.sin`, `Real.hasDerivAt_sin` | `Analysis/SpecialFunctions/Trigonometric/Deriv.lean:595`, `:322` |
| Inverse derivative/composition rules | `Analysis/Calculus/Deriv/Inv.lean` |
| `Real.abs_sin_le_one`, `Real.sin_add_nat_mul_pi`, `Real.sin_pi_div_two` | `Analysis/SpecialFunctions/Trigonometric/Basic.lean` (phase formula `:295`, half-pi value `:440`) |

## 2. Alternating samples force unbounded variation

Set `θ n := π/2 + (n : ℝ)*π`, `a n := (θ n)⁻¹`, and `u n := Real.sqrt (a n)`. This square-root-of-the-inverse encoding simplifies evaluation: `u n ^ 2 = a n` by `Real.sq_sqrt`, hence `(u n ^ 2)⁻¹ = θ n`.

Prove these elementary sample facts:

- `θ n > 0`, `a n > 0`, `u n > 0`; `u` is antitone.
- `u n ≤ 1`, since `π/2 > 1` and hence `a n ≤ 1`.
- `f (u n) = (-1 : ℝ)^n * a n`, using `Real.sin_add_nat_mul_pi` and `Real.sin_pi_div_two`.
- `dist (f (u (n+1))) (f (u n)) = a (n+1) + a n`. Expand `pow_succ`, factor `(-1)^n`, and use its absolute value one and positivity of both amplitudes.
- Therefore `1 / ((n : ℝ)+1) ≤ π * dist (f (u (n+1))) (f (u n))`, since `θ n ≤ π*((n:ℝ)+1)`.

Assume `hBV : BoundedVariationOn f (Icc 0 1)` and put `V := (eVariationOn f (Icc 0 1)).toReal`. Avoid manually reversing every finite partition:

1. `eVariationOn.comp_le_of_antitoneOn` transfers the variation bound to `f ∘ u` on `Set.univ : Set ℕ`.
2. Apply `eVariationOn.sum_le` to the identity increasing sequence in ℕ.
3. Convert the resulting finite ENNReal distance sum to a real sum using `edist_dist`, `ENNReal.ofReal_sum_of_nonneg`, and `ENNReal.ofReal_le_iff_le_toReal hBV`.
4. Sum the pointwise harmonic lower bound. It yields, for every `N`,

   `∑ n ∈ Finset.range N, 1 / ((n:ℝ)+1) ≤ π * V`.

5. Contradict `Real.tendsto_sum_range_one_div_nat_succ_atTop` by selecting a partial sum strictly larger than `π*V`.

This is a finite-sum argument throughout; no conditional-series interchange is needed.

Pinned APIs:

| API | Location |
|---|---|
| `eVariationOn.sum_le` | `Topology/EMetricSpace/BoundedVariation.lean:94` |
| `eVariationOn.comp_le_of_antitoneOn` | same file `:507` |
| `BoundedVariationOn`, `eVariationOn` definitions | same file `:61–67` |
| `Real.sq_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_pos`, `Real.sqrt_le_one` | `Analysis/Real/Sqrt.lean:178`, `:209`, `:286`, `:300` |
| `ENNReal.ofReal_sum_of_nonneg` | `Basic/ENNReal/BigOperators.lean:123` |
| `ENNReal.ofReal_le_iff_le_toReal` | `Basic/ENNReal/Real.lean:262` |
| `Real.tendsto_sum_range_one_div_nat_succ_atTop` | `Analysis/PSeries.lean:361` |

For every `[0,b]`, use a tail `u (n+M)` lying below `b`. `u n → 0` follows from `tendsto_mul_add_inv_atTop_nhds_zero π (π/2) Real.pi_ne_zero`, composition with the natural-number cast, and `Real.continuous_sqrt`. The affine-inverse theorem is at `Analysis/SpecificLimits/Basic.lean:123`. The denominator estimate

`θ (n+M) ≤ π*(M+1)*(n+1)`

gives the same harmonic contradiction with a larger fixed constant. The special unit-interval proof can be implemented first.

## 3. Integrable derivative would force bounded variation

Assume derivative integrability on `[0,1]` and convert it to `IntervalIntegrable (deriv f) volume 0 1`. Let `F x := ∫ t in 0..x, deriv f t`.

- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` makes `F` absolutely continuous on `[0,1]`.
- For every `x ∈ [0,1]`, restrict the interval-integrability hypothesis using `IntervalIntegrable.mono_set` and apply `intervalIntegral.integral_deriv_eq_sub`. Since `f` is everywhere differentiable and `f 0 = 0`, this gives `F x = f x`.
- `AbsolutelyContinuousOnInterval.congr`, then `.boundedVariationOn`, gives bounded variation of `f` on `[0,1]`, contradicting the preceding sample calculation.

Pinned APIs:

| API | Location |
|---|---|
| `intervalIntegrable_iff_integrableOn_Icc_of_le` | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:141` |
| `IntervalIntegrable.mono_set` | same file `:264` |
| `intervalIntegral.integral_deriv_eq_sub` | `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1176` |
| `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` | `MeasureTheory/Function/AbsolutelyContinuous.lean:450` |
| `AbsolutelyContinuousOnInterval.congr`, `.boundedVariationOn` | same file `:184`, `:357` |

Using the existing Mathlib FTC is legitimate here even though Rudin proves a corresponding general theorem later at 7.21. This does not create a Lean declaration cycle: the supporting theorem is already imported independently.

To obtain the explicit infinite `lintegral`, use `aestronglyMeasurable_deriv f (volume.restrict (Icc 0 1))` (`Analysis/Calculus/FDeriv/Measurable.lean:416`) and `hasFiniteIntegral_iff_norm` (`MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:93`). A finite absolute `lintegral` together with that measurability would imply the integrability just refuted.

## 4. Attached improper-limit claim

For each `0 < ε ≤ 1`, the explicit derivative formula is continuous on `[ε,1]`; denominators never vanish. Use its `ContinuousOn.intervalIntegrable` and `intervalIntegral.integral_deriv_eq_sub` to obtain

`∫ x in ε..1, deriv f x = f 1 - f ε`.

The right side tends to `f 1 - f 0` as `ε → 0+` because `f` is continuous at zero (already obtained from differentiability). Transfer this limit by eventual equality on the right-neighborhood filter. No integrability across zero is used. Normalize `f 1 - f 0` to `Real.sin 1` only at the end.

## Expected implementation effort and remaining risks

The pinned library supplies all analytic transitions. The new work consists of the derivative-at-zero squeeze, sample algebra/monotonicity, and ENNReal-to-real finite-sum bookkeeping. The sample argument is substantially more direct than proving divergence of an oscillatory integral by substitution. No ready-made theorem for this exact example was found in the pinned tree. This is a concrete source-based plan, not an elaborated proof or a claim that these steps have passed Lean.
