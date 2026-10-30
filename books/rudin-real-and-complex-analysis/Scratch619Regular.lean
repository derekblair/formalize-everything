import RudinRCA.Chapter06
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RudinRCA.Chapter06
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]

/-- Domination by a finite regular measure preserves regularity, on an arbitrary
Hausdorff Borel space. No countability hypothesis on the topology is needed. -/
theorem regular_of_le_finite_regular (μ ν : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (hνμ : ν ≤ μ) : ν.Regular := by
  letI : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνμ
  have hinner : ν.InnerRegular := by
    constructor
    intro E hE r hr
    have hrfinite : r ≠ ∞ := ne_top_of_lt (hr.trans_le (le_top))
    have hreal : r.toReal < ν.real E :=
      (ENNReal.toReal_lt_toReal hrfinite (measure_ne_top ν E)).mpr hr
    let ε := (ν.real E - r.toReal) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr hreal)
    obtain ⟨K, hKE, hK, hsmall⟩ := hE.exists_isCompact_sdiff_lt
      (μ := μ) (measure_ne_top μ E) (ENNReal.ofReal_ne_zero_iff.mpr hε)
    have hνsmall : ν (E \ K) < ENNReal.ofReal ε := (hνμ _).trans_lt hsmall
    have hsmallreal : ν.real (E \ K) < ε := by
      have ht := (ENNReal.toReal_lt_toReal (measure_ne_top ν (E \ K))
        ENNReal.ofReal_ne_top).mpr hνsmall
      simpa only [ENNReal.toReal_ofReal hε.le, measureReal_def] using ht
    have hsplit := measureReal_sdiff (μ := ν) hKE hK.measurableSet
    refine ⟨K, hKE, hK, ?_⟩
    apply (ENNReal.toReal_lt_toReal hrfinite (measure_ne_top ν K)).mp
    change r.toReal < ν.real K
    dsimp [ε] at hsmallreal
    linarith
  letI : ν.InnerRegular := hinner
  infer_instance

/-- Finite sums of finite regular measures are regular. -/
theorem regular_add_finite (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular] : (μ + ν).Regular := by
  infer_instance

/-- The difference of two regular complex measures is regular, as used in 6.19. -/
theorem complex_variation_sub_regular (c d : ComplexMeasure X)
    [c.variation.Regular] [d.variation.Regular] : (c - d).variation.Regular := by
  letI : (c.variation + d.variation).Regular := regular_add_finite _ _
  apply regular_of_le_finite_regular (c.variation + d.variation)
  simpa only [sub_eq_add_neg, VectorMeasure.variation_neg] using
    (VectorMeasure.variation_add_le (μ := c) (ν := -d))

#print axioms regular_of_le_finite_regular
#print axioms regular_add_finite
#print axioms complex_variation_sub_regular
end RudinRCA.Chapter06
