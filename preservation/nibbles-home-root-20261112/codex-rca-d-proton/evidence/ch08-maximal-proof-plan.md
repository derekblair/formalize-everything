# 8.18 source proof plan and support boundaries

This is a proof plan, not a formalized theorem or evidence of a completed node.

## Concrete domain and operator

Use `E := EuclideanSpace ℝ (Fin k)` and `μ := (volume : Measure E)`, with `f : E → ℂ`. The operator in `Ch08Maximal.lean` is

```
M f x = ⨆ (r : ℝ) (_ : 0 < r),
  (∫⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ) / μ (Metric.ball x r).
```

This keeps infinite values; prematurely defining `M f` using `toReal` would wrongly map infinity to zero. Prove measurable/AE measurable extended output before extracting a real representative once the Lp integral is finite. For arbitrary Lebesgue-measurable inputs, pass to Borel representatives and prove the operator unchanged at every x under AE equality.

## Elementary L∞ bound

`Ch08Maximal.lean` contains a source candidate for `M f x ≤ eLpNormEssSup f μ`, even pointwise. This follows by restriction of the a.e. norm bound, integration, and `a*a⁻¹ ≤ 1`. It is independent of the weak (1,1) estimate.

## Weak (1,1), which cannot be assumed to finish 8.18

1. For each x in `{M f > t}` choose a radius with average greater than t. Work first with witnesses of radius bounded above by R (or bound the witness radii using the total L1 norm and Euclidean ball-volume scaling).
2. Apply `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` with enlargement factor 5. Its exact interface is in `MeasureTheory/Covering/Vitali.lean:195` and requires only `r a ≤ R`.
3. Countability of the selected disjoint nonempty open balls follows from second countability.
4. Bound the original level set by the union of the selected 5-times enlarged balls. Euclidean Haar scaling gives `μ(B(x,5r)) = 5^k μ(B(x,r))`.
5. The selected balls are disjoint, so `t * Σ μ(B) ≤ Σ∫_B |f| ≤ ||f||₁`.
6. Exhaust the radius bound R to obtain `μ{M f > t} ≤ 5^k/t * ||f||₁` for all t>0. This need not use the optimal weak constant.

## Distribution-tail interpolation

Fix p>1 and c∈(0,1), with A the concrete weak bound.

- Split `g_t := 1_{|f|>ct} f`, `h_t := f-g_t`.
- Prove `g_t ∈ L1`: on `{|f|>ct}`, `|f| ≤ (ct)^(1-p)|f|^p`; its integral is finite because `f∈Lp`. The low part satisfies `|h_t|≤ct` pointwise.
- Subadditivity and the L∞ bound imply `{M f>t}⊆{M g_t>(1-c)t}`.
- Thus `μ{M f>t} ≤ A/((1-c)t) * ∫_{|f|>ct}|f|`.
- The full extended layer-cake theorem in `Ch08Phi.lean`, applied to Φ(s)=s^p, yields
  `∫(M f)^p = p ∫₀∞ t^(p-1) μ{M f>t} dt`.
- Tonelli, followed by `integral_rpow` (`Analysis/SpecialFunctions/Integrals/Basic.lean:147`), computes
  `∫₀∞ t^(p-2) ∫_{|f|>ct}|f| dt = c^(1-p)/(p-1) ∫|f|^p`.
- Therefore `∫(M f)^p ≤ A*p*c^(1-p)/((1-c)*(p-1)) ∫|f|^p <∞`.

This proves the printed membership theorem. The printed proof additionally optimizes c=(p−1)/p. A valid larger constant is enough for the stated membership claim; if claiming the printed displayed optimized bound, formalize that arithmetic separately. The inventory agent visually verified the printed bound as `C_p=(A e p q)^(1/p)` on p174.

## Precise completion boundary

A theorem with the weak (1,1) bound as an extra premise is generic interpolation support only. It does not establish Rudin 8.18 until the concrete centered maximal operator satisfies that premise. No global pinned Mathlib declaration for Hardy–Littlewood maximal/Marcinkiewicz interpolation was found in searches of all Mathlib sources; the available declarations are covering and differentiation ingredients.
