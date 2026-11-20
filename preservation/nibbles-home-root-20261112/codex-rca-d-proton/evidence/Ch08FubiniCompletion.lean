module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- 8.10: a nonmeasurable rectangle inside a measurable null rectangle shows that
the product measure is not complete. The factor completeness assumptions are not
needed for this implication, so it applies in particular to complete factors. -/
theorem product_not_complete (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    {A : Set X} {B : Set Y} (hA : A.Nonempty) (hμA : μ A = 0)
    (hB : ¬ MeasurableSet B) : ¬ (μ.prod ν).IsComplete := by
  intro hc
  have hn : (μ.prod ν) (A ×ˢ B) = 0 := by
    simp [Measure.prod_prod, hμA]
  letI : (μ.prod ν).IsComplete := hc
  have hm : MeasurableSet (A ×ˢ B) := measurableSet_of_null hn
  obtain ⟨a, ha⟩ := hA
  have hs := (measurable_prodMk_left : Measurable (Prod.mk a)) hm
  have heq : Prod.mk a ⁻¹' (A ×ˢ B) = B := by
    ext y
    simp [ha]
  exact hB (by simpa only [heq] using hs)

variable (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- 8.12, Lemma 1: a completion-measurable function has an original-measurable
representative. `NullMeasurable` is measurability for the completed sigma algebra.
The countably generated target covers both targets in the book, ℂ and [0,∞]. -/
theorem completion_measurable_representative [MeasurableSpace Z]
    [MeasurableSpace.CountablyGenerated Z] {f : X → Z} (hf : NullMeasurable f μ) :
    ∃ g : X → Z, Measurable g ∧ f =ᵐ[μ] g := hf.aemeasurable

/-- 8.12, Lemma 2: a product-null function vanishes on almost every section. -/
theorem zero_ae_sections [Zero Z] {f : X × Y → Z}
    (hf : f =ᵐ[μ.prod ν] 0) : ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[ν] 0 :=
  Measure.ae_ae_of_ae_prod hf

/-- The measurable-section conclusion of 8.12, with completeness on the second factor. -/
theorem completed_measurable_sections_left [MeasurableSpace Z]
    [MeasurableSpace.CountablyGenerated Z] [ν.IsComplete] {f : X × Y → Z}
    (hf : NullMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Measurable (fun y => f (x, y)) := by
  have ha := hf.aemeasurable
  filter_upwards [Measure.ae_ae_of_ae_prod ha.ae_eq_mk] with x hx
  exact ((ha.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr (Filter.EventuallyEq.symm hx)).nullMeasurable.measurable_of_complete

/-- Both section-measurability assertions in 8.12. -/
theorem completed_measurable_sections [MeasurableSpace Z]
    [MeasurableSpace.CountablyGenerated Z] [μ.IsComplete] [ν.IsComplete]
    {f : X × Y → Z} (hf : NullMeasurable f (μ.prod ν)) :
    (∀ᵐ x ∂μ, Measurable (fun y => f (x, y))) ∧
    (∀ᵐ y ∂ν, Measurable (fun x => f (x, y))) := by
  refine ⟨completed_measurable_sections_left μ ν hf, ?_⟩
  exact completed_measurable_sections_left ν μ hf.aemeasurable.prod_swap.nullMeasurable

/-- 8.12(a): Tonelli for a function measurable in the completion.
Mathlib's integral of an a.e.-measurable representative already implements integration
on the completion; no Borel measurability of f is imposed here. -/
theorem completed_tonelli [μ.IsComplete] [ν.IsComplete]
    {f : X × Y → ℝ≥0∞} (hf : NullMeasurable f (μ.prod ν)) :
    (∀ᵐ x ∂μ, Measurable (fun y => f (x, y))) ∧
    (∀ᵐ y ∂ν, Measurable (fun x => f (x, y))) ∧
    Measurable (fun x => ∫⁻ y, f (x, y) ∂ν) ∧
    Measurable (fun y => ∫⁻ x, f (x, y) ∂μ) ∧
    (∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ) = ∫⁻ z, f z ∂μ.prod ν ∧
    (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  have ha := hf.aemeasurable
  exact ⟨(completed_measurable_sections μ ν hf).1,
    (completed_measurable_sections μ ν hf).2,
    ha.lintegral_prod_right'.nullMeasurable.measurable_of_complete,
    ha.lintegral_prod_left'.nullMeasurable.measurable_of_complete,
    (lintegral_prod f ha).symm, lintegral_prod_symm f ha⟩

/-- 8.12(b), the completion version of the modulus integrability criterion. -/
theorem completed_integrable_of_iterated_norm {f : X × Y → ℂ}
    (hf : NullMeasurable f (μ.prod ν))
    (hfin : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂ν ∂μ) < ∞) :
    Integrable f (μ.prod ν) := by
  refine ⟨hf.aemeasurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hf.aemeasurable.enorm]
  exact hfin

/-- 8.12(c), retaining actual measurable sections on complete factors. -/
theorem completed_fubini [μ.IsComplete] [ν.IsComplete]
    {f : X × Y → ℂ} (hf : Integrable f (μ.prod ν)) :
    (∀ᵐ x ∂μ, Measurable (fun y => f (x, y))) ∧
    (∀ᵐ y ∂ν, Measurable (fun x => f (x, y))) ∧
    (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ ∧
    Integrable (fun y => ∫ x, f (x, y) ∂μ) ν ∧
    (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ z, f z ∂μ.prod ν ∧
    (∫ z, f z ∂μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  have hs := completed_measurable_sections μ ν hf.aestronglyMeasurable.aemeasurable.nullMeasurable
  exact ⟨hs.1, hs.2, hf.prod_right_ae, hf.prod_left_ae,
    hf.integral_prod_left, hf.integral_prod_right,
    (integral_prod f hf).symm, integral_prod_symm f hf⟩

end RudinRCA.Chapter08
