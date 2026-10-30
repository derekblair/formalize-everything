import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RudinRCA.Chapter06

/-- Lebesgue measure on (0,1), extended by zero outside the interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

/-- The positive, unbounded measure used in the discussion of Rudin 6.11. -/
def inverseDensityMeasure : Measure ℝ :=
  unitIntervalMeasure.withDensity (fun x ↦ ENNReal.ofReal x⁻¹)

theorem inverseDensity_absolutelyContinuous :
    inverseDensityMeasure ≪ unitIntervalMeasure :=
  withDensity_absolutelyContinuous _ _

theorem inverseDensity_Ioo {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    inverseDensityMeasure (Ioo 0 a) = ∞ := by
  rw [inverseDensityMeasure, withDensity_apply _ measurableSet_Ioo,
    unitIntervalMeasure, Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl ha1)]
  apply Classical.byContradiction
  intro hfinite
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ x⁻¹)
      (volume.restrict (Ioo 0 a)) := measurable_inv.aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 a)] (fun x : ℝ ↦ x⁻¹) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ (inv_pos.mpr hx.1).le
  have hi := (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hfinite
  have hr : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo 0 a) := by
    simpa only [IntegrableOn, Real.rpow_neg_one] using hi
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ha).mp hr
  exact (lt_irrefl (-1 : ℝ)) this

/-- Although absolutely continuous, this positive measure has infinite mass on
arbitrarily small intervals, so it fails the epsilon/delta criterion of 6.11. -/
theorem inverseDensity_fails_uniform_absoluteContinuity :
    ∀ δ : ℝ, 0 < δ → ∃ E : Set ℝ, MeasurableSet E ∧
      unitIntervalMeasure E < ENNReal.ofReal δ ∧ inverseDensityMeasure E = ∞ := by
  intro δ hδ
  let a := min (δ / 2) (1 / 2)
  have ha : 0 < a := lt_min (half_pos hδ) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have had : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨Ioo 0 a, measurableSet_Ioo, ?_, inverseDensity_Ioo ha ha1⟩
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo le_rfl ha1), Real.volume_Ioo, sub_zero]
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr had

#print axioms inverseDensity_absolutelyContinuous
#print axioms inverseDensity_Ioo
#print axioms inverseDensity_fails_uniform_absoluteContinuity
end RudinRCA.Chapter06
