# Rudin 13.10: pinned API and exact construction

All source references below concern Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. This is implementation evidence, not a completed-node assertion. The three Lean scratch files listed below are uncompiled pending the parent's aggregate check.

## Existing library core

- `Mathlib/Analysis/Complex/LocallyUniformLimit.lean:171`, `differentiableOn_tsum_of_summable_norm`: if `Summable u`, every `F i` is complex differentiable on an open `U`, and `∀ i z∈U, ‖F i z‖ ≤ u i`, then `z ↦ ∑' i, F i z` is complex differentiable on `U`. No derivative bounds are required.
- `Mathlib/Analysis/Complex/SummableUniformlyOn.lean:21`, `SummableLocallyUniformlyOn.differentiableOn`: the equivalent locally uniform sum API is also present.
- `Mathlib/Topology/Compactness/Compact.lean:920`, `Set.Infinite.exists_accPt_of_subset_isCompact`: an infinite subset of a compact set has an accumulation point in that compact set. This proves finiteness of `A∩K` from the exact absence of accumulation points in Ω.
- `Mathlib/Topology/ClusterPt.lean:231`, `AccPt.mono`: transfers the accumulation point of `A∩K` to `A`.
- `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:222,234`, additive declarations `summable_nat_add_iff` and `Summable.sum_add_tsum_nat_add`: recover summability of a full series from a bounded tail and split it into a finite prefix and that tail.
- `Mathlib/Analysis/Complex/CauchyIntegral.lean:704`, `DifferentiableOn.analyticAt`: complex differentiability on a neighborhood implies analyticity at the point.
- `Mathlib/Analysis/Meromorphic/Basic.lean`: meromorphic functions are closed under finite sums, multiplication, inverse, and powers; analyticity implies meromorphicity. No Mittag-Leffler realization theorem was found.
- `RatFunc.eval` is the canonical reduced numerator evaluation divided by the reduced denominator evaluation. Away from denominator zeros, polynomial analyticity and analytic division give `AnalyticAt` directly; no incorrect global evaluation-ring-hom argument is needed.

## Draft files and exact obligations

1. `MittagLefflerCore.lean`: finite intersection with compact subsets, finite negative-power principal parts, and the analytic normal-tail-minus-finite-prefix lemma.
2. `MittagLefflerSeries.lean`: for finite cumulative sets `Sₙ=A∩Kₙ`, write `Qₙ` for their sum of prescribed principal parts and `gₙ=Qₙ₊₁−Qₙ−rₙ`. If every correction `rₙ` is holomorphic on Ω and `‖gₙ‖≤2⁻ⁿ` on `Kₙ`, define `f=Q₀+∑gₙ`. The draft proves meromorphicity on Ω, analyticity of `f−Pα` at every prescribed point, and analyticity of `f` at every other point.
3. `MittagLefflerAssembly.lean`: constructs the finite sets using no accumulation, proves `Qₙ₊₁−Qₙ` holomorphic on the open set obtained by removing the finite new shell from Ω, and calls the conditional compact Runge theorem with permitted poles in the spherical complement of Ω. The final explicit prerequisite is genuine existence of a universal `FiniteCauchyRepresentation K U` for every compact `K⊆U` with `U` open. That is exactly the remaining 13.5 construction, not an extra Mittag-Leffler hypothesis hidden in the claim.

The theorem retains arbitrary open Ω, possibly disconnected, and arbitrary prescribed finite negative-power coefficients. A positive declared degree does not force a pole if all relevant coefficients vanish. Accordingly the conclusion does not assert that every α is a pole: it asserts the exact principal part and absence of all other poles.
