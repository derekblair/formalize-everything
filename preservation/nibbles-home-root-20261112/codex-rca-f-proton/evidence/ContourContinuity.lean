import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

open Set Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace RudinRCA.Chapter13Scratch

/-- A fixed parameterized contour integral with a Cauchy denominator is continuous in the
evaluation point when a positive lower bound on distance to the contour is available. -/
theorem continuousAt_kernel_intervalIntegral_of_bounds
    {γ g : ℝ → ℂ} {a b : ℝ} {z : ℂ} {δ M : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hsep : ∀ t ∈ uIcc a b, δ ≤ ‖γ t - z‖)
    (hbound : ∀ t ∈ uIcc a b, ‖g t‖ ≤ M) :
    ContinuousAt (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w)) z := by
  have hn : ∀ᶠ w : ℂ in 𝓝 z, ‖w - z‖ < δ / 2 := by
    filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with w hw
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hden {w : ℂ} (hw : ‖w - z‖ < δ / 2) {t : ℝ} (ht : t ∈ uIcc a b) :
      δ / 2 ≤ ‖γ t - w‖ := by
    have htri : ‖γ t - z‖ ≤ ‖γ t - w‖ + ‖w - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (γ t - w) (w - z)
    have hs := hsep t ht
    linarith
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ : ℝ => M / (δ / 2))
  · filter_upwards [hn] with w hw
    have hc : ContinuousOn (fun t : ℝ => g t / (γ t - w)) (uIcc a b) :=
      hg.div (hγ.sub continuousOn_const) fun t ht =>
        norm_pos_iff.mp ((half_pos hδ).trans_le (hden hw ht))
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hn] with w hw
    exact Filter.Eventually.of_forall fun t ht => by
      rw [norm_div]
      exact div_le_div₀ hM (hbound t (Ioc_subset_Icc_self ht))
        (half_pos hδ) (hden hw (Ioc_subset_Icc_self ht))
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht =>
      continuousAt_const.div (continuousAt_const.sub continuousAt_id)
        (norm_pos_iff.mp (hδ.trans_le (hsep t (Ioc_subset_Icc_self ht))))

/-- A Cauchy-type integral over a compact parameter interval depends continuously on every
evaluation point outside the contour image. The numerator may include the contour velocity. -/
theorem continuousAt_kernel_intervalIntegral
    {γ g : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hz : z ∉ γ '' uIcc a b) :
    ContinuousAt (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w)) z := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_uIcc.exists_isMinOn
    (show (uIcc a b).Nonempty from ⟨a, left_mem_uIcc⟩)
    (hγ.sub continuousOn_const).norm
  have hsep : 0 < ‖γ t₀ - z‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro h
    exact hz ⟨t₀, ht₀, h⟩
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    (show (uIcc a b).Nonempty from ⟨a, left_mem_uIcc⟩) hg.norm
  exact continuousAt_kernel_intervalIntegral_of_bounds hγ hg hsep (norm_nonneg _)
    (fun t ht => hmin ht) (fun t ht => hmax ht)

theorem continuousOn_kernel_intervalIntegral
    {γ g : ℝ → ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b)) :
    ContinuousOn (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w))
      (γ '' uIcc a b)ᶜ := by
  intro z hz
  exact (continuousAt_kernel_intervalIntegral hγ hg hz).continuousWithinAt

#print axioms continuousAt_kernel_intervalIntegral_of_bounds
#print axioms continuousAt_kernel_intervalIntegral
#print axioms continuousOn_kernel_intervalIntegral

end RudinRCA.Chapter13Scratch
