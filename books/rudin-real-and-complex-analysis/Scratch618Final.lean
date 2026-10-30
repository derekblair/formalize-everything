import Scratch69
import Scratch618Polar
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.18: a complex Borel measure is regular precisely when its total
variation is regular. Under `BorelSpace X`, the underlying measurable sets are
the Borel sets. -/
def IsRegularComplexMeasure [TopologicalSpace X] (c : ComplexMeasure X) : Prop :=
  Measure.Regular c.variation

/-- The native complex integral defines the bounded complex functional on C0
asserted in 6.18, with the total-variation norm bound. -/
theorem theorem_6_18_functional [TopologicalSpace X] [BorelSpace X]
    (c : ComplexMeasure X) :
    ∃ Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ,
      (∀ f, Φ f = complexIntegral c f) ∧ ‖Φ‖ ≤ c.variation.real univ := by
  obtain ⟨h, hm, hn, hi, hr⟩ := theorem_6_12 c
  obtain ⟨Φ, hΦ, hbound⟩ := theorem_6_18_polar_functional c h hm hn
  refine ⟨Φ, ?_, hbound⟩
  intro f
  rw [hΦ]
  have hf : Integrable (fun x ↦ f x) c.variation :=
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  exact (vectorIntegral_eq_polar c h hm hn hi hr hf).symm

end RudinRCA.Chapter06

#print axioms RudinRCA.Chapter06.theorem_6_18_functional
