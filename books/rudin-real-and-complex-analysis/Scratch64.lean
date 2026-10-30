import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Tactic.Linarith

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- The real and imaginary signed variations dominate the complex variation. -/
theorem complex_variation_le_re_add_im (μ : ComplexMeasure X) :
    μ.variation ≤ μ.re.totalVariation + μ.im.totalVariation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  have h : ‖μ E‖ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
    calc
      ‖μ E‖ ≤ |(μ E).re| + |(μ E).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ μ.re.totalVariation.real E + μ.im.totalVariation.real E := by
        have hre : μ.re E = (μ E).re := rfl
        have him : μ.im E = (μ E).im := rfl
        have h₁ := μ.re.norm_le_totalVariation E
        have h₂ := μ.im.norm_le_totalVariation E
        rw [hre, Real.norm_eq_abs] at h₁
        rw [him, Real.norm_eq_abs] at h₂
        exact add_le_add h₁ h₂
  calc
    ‖μ E‖ₑ = ENNReal.ofReal ‖μ E‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (μ.re.totalVariation.real E + μ.im.totalVariation.real E) :=
      ENNReal.ofReal_le_ofReal h
    _ = (μ.re.totalVariation + μ.im.totalVariation) E := by
      rw [ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg)]
      simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), Measure.add_apply]

/-- Rudin 6.4: every complex measure has finite total variation. -/
theorem complex_variation_univ_lt_top (μ : ComplexMeasure X) : μ.variation univ < ∞ :=
  lt_of_le_of_lt (complex_variation_le_re_add_im μ univ) (measure_lt_top _ _)

instance complexVariationFinite (μ : ComplexMeasure X) : IsFiniteMeasure μ.variation where
  measure_univ_lt_top := complex_variation_univ_lt_top μ

/-- The total-variation norm from Rudin 6.5. -/
def complexMeasureNorm : AddGroupNorm (ComplexMeasure X) where
  toFun μ := μ.variation.real univ
  map_zero' := by simp [measureReal_def]
  neg' μ := by simp only [VectorMeasure.variation_neg]
  add_le' μ ν := by
    calc
      (μ + ν).variation.real univ ≤ (μ.variation + ν.variation).real univ := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        exact VectorMeasure.variation_add_le univ
      _ = μ.variation.real univ + ν.variation.real univ := by rw [measureReal_add_apply]
  eq_zero_of_map_eq_zero' μ h := by
    apply VectorMeasure.variation_eq_zero.mp
    apply Measure.measure_univ_eq_zero.mp
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (measure_ne_top _ _)

instance complexMeasureNormedAddCommGroup : NormedAddCommGroup (ComplexMeasure X) :=
  complexMeasureNorm.toNormedAddCommGroup

theorem complex_norm_eq_variation (μ : ComplexMeasure X) :
    ‖μ‖ = μ.variation.real univ := rfl

instance complexMeasureNormedSpace : NormedSpace ℂ (ComplexMeasure X) where
  norm_smul_le c μ := by
    change (c • μ).variation.real univ ≤ ‖c‖ * μ.variation.real univ
    simp [VectorMeasure.variation_smul, measureReal_nnreal_smul_apply]

/-- Every value of a complex measure is bounded by its total-variation norm. -/
theorem complex_measure_norm_le (μ : ComplexMeasure X) (E : Set X) : ‖μ E‖ ≤ ‖μ‖ :=
  (VectorMeasure.norm_measure_le_variation (μ := μ)).trans
    (measureReal_mono (subset_univ E))

/-- Positive variation in Rudin 6.6, as a finite positive measure. -/
def positiveVariation (μ : SignedMeasure X) : Measure X := μ.toJordanDecomposition.posPart

/-- Negative variation in Rudin 6.6, as a finite positive measure. -/
def negativeVariation (μ : SignedMeasure X) : Measure X := μ.toJordanDecomposition.negPart

instance positiveVariationFinite (μ : SignedMeasure X) : IsFiniteMeasure (positiveVariation μ) :=
  inferInstanceAs (IsFiniteMeasure μ.toJordanDecomposition.posPart)

instance negativeVariationFinite (μ : SignedMeasure X) : IsFiniteMeasure (negativeVariation μ) :=
  inferInstanceAs (IsFiniteMeasure μ.toJordanDecomposition.negPart)

theorem positive_add_negative_variation (μ : SignedMeasure X) :
    positiveVariation μ + negativeVariation μ = μ.variation :=
  μ.totalVariation_eq_variation

theorem positive_sub_negative_variation (μ : SignedMeasure X) :
    (positiveVariation μ).toSignedMeasure - (negativeVariation μ).toSignedMeasure = μ :=
  μ.toSignedMeasure_toJordanDecomposition

theorem positiveVariation_real_eq (μ : SignedMeasure X) {E : Set X} (hE : MeasurableSet E) :
    (positiveVariation μ).real E = (μ.variation.real E + μ E) / 2 := by
  have hsub := μ.apply_eq_posPart_real_sub_negPart_real hE
  have hadd : μ.variation.real E =
      (positiveVariation μ).real E + (negativeVariation μ).real E := by
    rw [← positive_add_negative_variation, measureReal_add_apply]
  change μ E = (positiveVariation μ).real E - (negativeVariation μ).real E at hsub
  linarith

theorem negativeVariation_real_eq (μ : SignedMeasure X) {E : Set X} (hE : MeasurableSet E) :
    (negativeVariation μ).real E = (μ.variation.real E - μ E) / 2 := by
  have hsub := μ.apply_eq_posPart_real_sub_negPart_real hE
  have hadd : μ.variation.real E =
      (positiveVariation μ).real E + (negativeVariation μ).real E := by
    rw [← positive_add_negative_variation, measureReal_add_apply]
  change μ E = (positiveVariation μ).real E - (negativeVariation μ).real E at hsub
  linarith

#print axioms complex_variation_le_re_add_im
#print axioms complex_variation_univ_lt_top
#print axioms complexMeasureNorm
#print axioms complexMeasureNormedSpace
#print axioms complex_measure_norm_le
#print axioms positive_add_negative_variation
#print axioms positive_sub_negative_variation
#print axioms positiveVariation_real_eq
#print axioms negativeVariation_real_eq

end RudinRCA.Chapter06
