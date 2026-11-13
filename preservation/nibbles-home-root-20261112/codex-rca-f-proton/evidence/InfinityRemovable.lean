import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Field.Lemmas

open Filter Set Function
open scoped Topology

namespace RudinRCA.Chapter13Scratch

/-- The bounded removable-singularity statement at infinity in Rudin RCA 13.1.
The value assigned at zero to the inverse-coordinate expression is explicitly updated. -/
theorem removable_at_infinity_of_bounded
    {f : ℂ → ℂ} {r M : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z‖})
    (hb : ∀ z : ℂ, r < ‖z‖ → ‖f z‖ ≤ M) :
    ∃ c : ℂ, Tendsto f (cocompact ℂ) (𝓝 c) ∧
      AnalyticAt ℂ (Function.update (fun z : ℂ => f z⁻¹) 0 c) 0 := by
  classical
  let g : ℂ → ℂ := fun z => f z⁻¹
  have hext : ∀ᶠ z : ℂ in 𝓝[≠] 0, r < ‖z⁻¹‖ :=
    (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero).eventually_gt_atTop r
  have hd : ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ g z := by
    filter_upwards [hext, self_mem_nhdsWithin] with z hz hz0
    have hdf : DifferentiableAt ℂ f z⁻¹ :=
      hf.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    exact hdf.comp z (differentiableAt_inv hz0)
  have hbound : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ))
      (fun z => ‖g z - g 0‖) := by
    refine ⟨M + ‖g 0‖, ?_⟩
    exact eventually_map.mpr (hext.mono fun z hz => norm_sub_le_of_le (hb z⁻¹ hz) le_rfl)
  let c : ℂ := limUnder (𝓝[≠] (0 : ℂ)) g
  have hlim : Tendsto g (𝓝[≠] 0) (𝓝 c) :=
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hbound
  refine ⟨c, ?_, ?_⟩
  · have h := hlim.comp (tendsto_inv₀_cobounded' (α := ℂ))
    simpa only [g, Function.comp_def, inv_inv, Metric.cobounded_eq_cocompact] using h
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hd, self_mem_nhdsWithin] with z hz hz0
      apply hz.congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw c g
    · exact continuousAt_update_same.mpr hlim

#print axioms removable_at_infinity_of_bounded

end RudinRCA.Chapter13Scratch
