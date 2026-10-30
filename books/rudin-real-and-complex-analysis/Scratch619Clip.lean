import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set

namespace RudinRCA.Chapter06

/-- Radial truncation to the closed unit disk, preserving zero. -/
def unitClip (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

@[simp] theorem unitClip_zero : unitClip 0 = 0 := by simp [unitClip]

theorem continuous_unitClip : Continuous unitClip := by
  unfold unitClip
  exact ((continuous_const.max continuous_norm).inv₀
    (fun z ↦ (zero_lt_one.trans_le (le_max_left 1 ‖z‖)).ne')).smul continuous_id

theorem norm_unitClip_le (z : ℂ) : ‖unitClip z‖ ≤ 1 := by
  have hn : 0 < max 1 ‖z‖ := zero_lt_one.trans_le (le_max_left _ _)
  rw [unitClip, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  exact (inv_mul_le_one₀ hn).mpr (le_max_right _ _)

theorem unitClip_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : unitClip z = z := by
  simp [unitClip, max_eq_left hz]

/-- Truncating an approximation loses at most a factor two in its error
relative to a point in the closed unit disk. -/
theorem unitClip_error_le (z w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖unitClip z - w‖ ≤ 2 * ‖z - w‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [unitClip_eq_self hz]
    linarith [norm_nonneg (z - w)]
  have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
  have hn : 0 < ‖z‖ := zero_lt_one.trans hz1
  have hdiff : ‖unitClip z - z‖ = ‖z‖ - 1 := by
    rw [norm_sub_rev, unitClip, max_eq_right hz1.le]
    have heq : z - ‖z‖⁻¹ • z = (1 - ‖z‖⁻¹) • z := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_of_nonneg
      (sub_nonneg.mpr (inv_le_one_of_one_le₀ hz1.le))]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hn.ne']
  have hdist : ‖z‖ - 1 ≤ ‖z - w‖ := by
    linarith [norm_sub_norm_le z w]
  calc
    ‖unitClip z - w‖ = ‖(unitClip z - z) + (z - w)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖unitClip z - z‖ + ‖z - w‖ := norm_add_le _ _
    _ ≤ 2 * ‖z - w‖ := by rw [hdiff]; linarith

/-- A compact-support L1 approximation property also provides approximations
within the unit ball. The approximation hypothesis is explicit: the pinned
library's standard density wrapper carries an additional normality hypothesis. -/
theorem exists_unitBounded_compactSupport_approx
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    {f : X → ℂ} (hf : Integrable f μ) (hn : ∀ x, ‖f x‖ ≤ 1)
    (happrox : ∀ η : ℝ, 0 < η → ∃ g : X → ℂ,
      HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ η ∧
      Continuous g ∧ Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℂ, HasCompactSupport g ∧ Continuous g ∧
      (∀ x, ‖g x‖ ≤ 1) ∧ Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨g, hgc, hge, hgcont, hgi⟩ :=
    happrox (ε / 2) (half_pos hε)
  let k := unitClip ∘ g
  have hkc : HasCompactSupport k := hgc.comp_left unitClip_zero
  have hkcont : Continuous k := continuous_unitClip.comp hgcont
  have hkn : ∀ x, ‖k x‖ ≤ 1 := fun x ↦ norm_unitClip_le (g x)
  have hki : Integrable k μ := Integrable.of_bound hkcont.aestronglyMeasurable 1 (ae_of_all μ hkn)
  refine ⟨k, hkc, hkcont, hkn, hki, ?_⟩
  calc
    (∫ x, ‖f x - k x‖ ∂μ) ≤ ∫ x, 2 * ‖f x - g x‖ ∂μ := by
      apply integral_mono (hf.sub hki).norm ((hf.sub hgi).norm.const_mul 2)
      intro x
      simpa only [k, Pi.sub_apply, Function.comp_apply, norm_sub_rev] using
        unitClip_error_le (g x) (f x) (hn x)
    _ = 2 * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul _ _
    _ ≤ ε := by linarith

#print axioms unitClip_error_le
#print axioms exists_unitBounded_compactSupport_approx
end RudinRCA.Chapter06
