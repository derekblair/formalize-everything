import RudinRCA.Chapter13
open Set Filter Metric
open scoped Topology
namespace RudinRCA.Chapter13
/-- The exterior-domain and punctured inverse-chart definitions of isolation agree. -/
theorem hasIsolatedSingularityAtInfinity_iff {f : ℂ → ℂ} :
    HasIsolatedSingularityAtInfinity f ↔
      ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (fun w : ℂ => f w⁻¹) z := by
  constructor
  · rintro ⟨r, _, hf⟩
    have hext : ∀ᶠ z : ℂ in 𝓝[≠] 0, r < ‖z⁻¹‖ :=
      (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero).eventually_gt_atTop r
    filter_upwards [hext, self_mem_nhdsWithin] with z hz hz0
    exact (hf.differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)).comp z
        (differentiableAt_inv hz0)
  · intro h
    have hback := (tendsto_inv₀_cobounded' (α := ℂ)).eventually h
    have hext : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, 0 < ‖z‖ :=
      tendsto_norm_cobounded_atTop.eventually_gt_atTop 0
    have hd : ∀ᶠ z : ℂ in cocompact ℂ, DifferentiableAt ℂ f z := by
      rw [← Metric.cobounded_eq_cocompact]
      filter_upwards [hback, hext] with z hz hz0
      simpa only [Function.comp_def, inv_inv] using
        hz.comp z (differentiableAt_inv (norm_pos_iff.mp hz0))
    obtain ⟨K, hK, hKd⟩ := mem_cocompact.mp hd
    obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨r, hr, fun z hz => (hKd ?_).differentiableWithinAt⟩
    exact fun hzK => (not_lt_of_ge (hKr z hzK)) hz

theorem pole_hasIsolatedSingularityAtInfinity {f : ℂ → ℂ} {m : ℕ}
    (h : HasPoleAtInfinity f m) : HasIsolatedSingularityAtInfinity f := by
  apply hasIsolatedSingularityAtInfinity_iff.mpr
  exact h.2.1.eventually_analyticAt.mono fun _ hz => hz.differentiableAt


#print axioms hasIsolatedSingularityAtInfinity_iff
#print axioms pole_hasIsolatedSingularityAtInfinity
end RudinRCA.Chapter13
