import Scratch610Discussion
import Scratch611Example
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RCA611Completed

open RCA610Discussion RudinRCA.Chapter06

/-- The inclusion from the completed open interval into the real line is
measurable: the completed domain sigma algebra contains the Borel sets. -/
theorem measurable_interval_val :
    Measurable (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) :=
  ((measurable_subtype_coe : Measurable (fun x : Ioo (0 : ℝ) 1 ↦ x.val)).nullMeasurable
    (μ := openIntervalVolume)).measurable'

/-- Completion and restriction give precisely the ambient restricted Lebesgue
measure under the inclusion map. This is the transfer bridge for the example. -/
theorem interval_val_measurePreserving :
    MeasurePreserving (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ))
      openIntervalLebesgue unitIntervalMeasure where
  measurable := measurable_interval_val
  map_eq := by
    ext E hE
    rw [Measure.map_apply measurable_interval_val hE, openIntervalLebesgue_apply,
      unitIntervalMeasure, Measure.restrict_apply hE, image_preimage_eq_inter_range]
    have hrange : Set.range (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) =
        Ioo (0 : ℝ) 1 := Subtype.range_coe
    rw [hrange]

/-- The reciprocal density on the Lebesgue-completed open interval, as in the
discussion following Rudin 6.11. -/
def completedInverseDensity : Measure CompletedOpenUnitInterval :=
  openIntervalLebesgue.withDensity (fun x ↦ ENNReal.ofReal (x.val⁻¹))

theorem completedInverseDensity_absolutelyContinuous :
    completedInverseDensity ≪ openIntervalLebesgue :=
  withDensity_absolutelyContinuous _ _

/-- On every Borel test set, the density measure agrees with the ambient
inverse-density example under the inclusion. -/
theorem completedInverseDensity_preimage {E : Set ℝ} (hE : MeasurableSet E) :
    completedInverseDensity ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E) =
      inverseDensityMeasure E := by
  rw [completedInverseDensity,
    withDensity_apply _ (hE.preimage measurable_interval_val),
    inverseDensityMeasure, withDensity_apply _ hE]
  exact interval_val_measurePreserving.setLIntegral_comp_preimage hE
    measurable_inv.ennreal_ofReal

theorem completedInverseDensity_Ioo {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    completedInverseDensity
      ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' Ioo 0 a) = ∞ :=
  (completedInverseDensity_preimage measurableSet_Ioo).trans (inverseDensity_Ioo ha ha1)

/-- The exact completed-space counterexample: the positive measure is absolutely
continuous, but its mass is infinite on sets of arbitrarily small Lebesgue mass. -/
theorem completedInverseDensity_fails_uniform_absoluteContinuity :
    completedInverseDensity ≪ openIntervalLebesgue ∧
      ∀ δ : ℝ, 0 < δ → ∃ E : Set CompletedOpenUnitInterval, MeasurableSet E ∧
        openIntervalLebesgue E < ENNReal.ofReal δ ∧ completedInverseDensity E = ∞ := by
  refine ⟨completedInverseDensity_absolutelyContinuous, ?_⟩
  intro δ hδ
  obtain ⟨E, hE, hsmall, hinfty⟩ := inverseDensity_fails_uniform_absoluteContinuity δ hδ
  refine ⟨(fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E,
    hE.preimage measurable_interval_val, ?_, ?_⟩
  · have hmass : openIntervalLebesgue
        ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E) = unitIntervalMeasure E := by
      rw [← Measure.map_apply measurable_interval_val hE, interval_val_measurePreserving.map_eq]
    exact hmass.symm ▸ hsmall
  · exact (completedInverseDensity_preimage hE).trans hinfty

#print axioms measurable_interval_val
#print axioms interval_val_measurePreserving
#print axioms completedInverseDensity_absolutelyContinuous
#print axioms completedInverseDensity_preimage
#print axioms completedInverseDensity_Ioo
#print axioms completedInverseDensity_fails_uniform_absoluteContinuity

end RCA611Completed
