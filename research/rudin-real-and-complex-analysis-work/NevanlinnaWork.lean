import RudinRCA.Chapter15
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The bounded holomorphic functions used in 15.19 and 15.22. -/
def BoundedHolomorphic (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧
    ∃ M : ℝ, ∀ z ∈ Metric.ball 0 1, ‖f z‖ ≤ M

/-- Definition 15.22: the Nevanlinna class on the unit disk. The circle average
uses the rotation-invariant circle measure with total mass one. -/
def NevanlinnaClass (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧
    ∃ M : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
      Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 r ≤ M

/-- The positive logarithm has the piecewise convention of 15.22. -/
theorem posLog_norm_eq (z : ℂ) :
    Real.posLog ‖z‖ = if 1 < ‖z‖ then Real.log ‖z‖ else 0 := by
  by_cases hz : 1 < ‖z‖
  · simp only [if_pos hz]
    exact Real.posLog_eq_log (by simpa only [abs_of_nonneg (norm_nonneg z)] using hz.le)
  · simp only [if_neg hz]
    apply (Real.posLog_eq_zero_iff _).2
    simpa only [abs_of_nonneg (norm_nonneg z)] using le_of_not_gt hz

/-- The positive logarithm of the modulus is circle-integrable on each circle
strictly inside the holomorphy disk, including circles meeting zeros of f. -/
theorem circleIntegrable_posLog_norm {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    CircleIntegrable (fun z ↦ Real.posLog ‖f z‖) 0 r := by
  apply ContinuousOn.circleIntegrable hr0
  apply Real.continuous_posLog.comp_continuousOn
  apply hf.continuousOn.norm.mono
  intro z hz
  have hz' : ‖z‖ = r := by simpa using hz
  simpa [Metric.mem_ball, dist_zero_right, hz'] using hr

/-- The explicit inclusion H∞ ⊆ N asserted in 15.22. -/
theorem BoundedHolomorphic.nevanlinnaClass {f : ℂ → ℂ} (hf : BoundedHolomorphic f) :
    NevanlinnaClass f := by
  obtain ⟨hd, M, hM⟩ := hf
  refine ⟨hd, Real.posLog M, ?_⟩
  intro r hr
  apply Real.circleAverage_mono_on_of_le_circle (circleIntegrable_posLog_norm hd hr.1.le hr.2)
  intro z hz
  have hz' : ‖z‖ = r := by simpa [abs_of_pos hr.1] using hz
  apply Real.posLog_le_posLog (by linarith [norm_nonneg (f z)])
  apply hM
  simpa [Metric.mem_ball, dist_zero_right, hz'] using hr.2

#print axioms posLog_norm_eq
#print axioms circleIntegrable_posLog_norm
#print axioms BoundedHolomorphic.nevanlinnaClass

end RudinRCA.Chapter15
