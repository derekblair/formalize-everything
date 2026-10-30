import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal unitInterval

namespace RCA610Discussion

variable {X : Type*} [MeasurableSpace X]

/-- Every measure is absolutely continuous with respect to counting measure. -/
theorem absolutelyContinuous_count (μ : Measure X) : μ ≪ Measure.count := by
  intro E hE
  rw [Measure.count_eq_zero_iff.mp hE]
  exact measure_empty

/-- Counting measure has no absolutely-continuous/singular decomposition relative
to a nonzero measure that vanishes on singletons. -/
theorem count_no_decomposition [MeasurableSingletonClass X]
    (μ : Measure X) [NullSingletonClass μ] (hμ : μ ≠ 0) :
    ¬ ∃ a s : Measure X, Measure.count = a + s ∧ a ≪ μ ∧ s ⟂ₘ μ := by
  rintro ⟨a, s, hsum, hac, N, hN, hsN, hμNc⟩
  have hNempty : N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have ha : a {x} = 0 := hac (measure_singleton x)
    have hs : s {x} = 0 := measure_mono_null (singleton_subset_iff.mpr hx) hsN
    have h := congrArg (fun ν : Measure X ↦ ν {x}) hsum
    simpa only [Measure.count_singleton, Measure.add_apply, ha, hs, zero_add,
      one_ne_zero] using h
  apply hμ
  apply Measure.measure_univ_eq_zero.mp
  simpa only [hNempty, compl_empty] using hμNc

/-- A nonzero measure vanishing on singletons cannot have a density with respect
to counting measure: every singleton would force the density to vanish there. -/
theorem count_no_density [MeasurableSingletonClass X]
    (μ : Measure X) [NullSingletonClass μ] (hμ : μ ≠ 0) :
    ¬ ∃ f : X → ℝ≥0∞, Measure.count.withDensity f = μ := by
  rintro ⟨f, hf⟩
  have hfzero : f = 0 := by
    funext x
    have h := congrArg (fun ν : Measure X ↦ ν {x}) hf
    simpa only [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
      Measure.count_singleton, mul_one, measure_singleton, Pi.zero_apply] using h
  apply hμ
  rw [← hf, hfzero]
  exact withDensity_zero

/-- The same obstruction applies to real or complex integrable densities in
Rudin's set-integral formulation. -/
theorem count_no_complex_density [MeasurableSingletonClass X]
    (μ : Measure X) [NullSingletonClass μ] [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    ¬ ∃ f : X → ℂ, Integrable f Measure.count ∧
      ∀ E : Set X, MeasurableSet E →
        (μ.real E : ℂ) = ∫ x in E, f x ∂Measure.count := by
  rintro ⟨f, _, hf⟩
  have hfzero : f = 0 := by
    funext x
    have h := hf {x} (measurableSet_singleton x)
    simpa only [measureReal_def, measure_singleton, ENNReal.toReal_zero,
      Complex.ofReal_zero, integral_singleton, count_real_singleton, one_smul,
      Measure.count_singleton, ENNReal.toReal_one, Pi.zero_apply] using h.symm
  have huniv : (μ Set.univ).toReal = 0 := by
    have h := congrArg Complex.re (hf Set.univ MeasurableSet.univ)
    simpa [hfzero, measureReal_def] using h
  apply hμ
  apply Measure.measure_univ_eq_zero.mp
  exact ((ENNReal.toReal_eq_zero_iff _).mp huniv).resolve_right (measure_ne_top μ Set.univ)

/-- A closed-unit-interval variant: counting measure cannot
be decomposed relative to Lebesgue measure, while Lebesgue measure is absolutely
continuous with respect to counting measure but has no density. -/
theorem unitInterval_counterexamples :
    (volume : Measure I) ≪ Measure.count ∧
    (¬ ∃ a s : Measure I, Measure.count = a + s ∧ a ≪ volume ∧ s ⟂ₘ volume) ∧
    (¬ ∃ f : I → ℝ≥0∞, Measure.count.withDensity f = volume) ∧
    (¬ ∃ f : I → ℂ, Integrable f Measure.count ∧
      ∀ E : Set I, MeasurableSet E →
        ((volume : Measure I).real E : ℂ) = ∫ x in E, f x ∂Measure.count) := by
  have hμ : (volume : Measure I) ≠ 0 := IsProbabilityMeasure.ne_zero _
  exact ⟨absolutelyContinuous_count _, count_no_decomposition _ hμ,
    count_no_density _ hμ, count_no_complex_density _ hμ⟩

/-- The reference counting measure in the second counterexample is not
sigma-finite. -/
theorem unitInterval_count_not_sigmaFinite : ¬ SigmaFinite (Measure.count : Measure I) := by
  intro hcount
  letI : SigmaFinite (Measure.count : Measure I) := hcount
  apply count_no_density (volume : Measure I) (IsProbabilityMeasure.ne_zero _)
  exact ⟨(volume : Measure I).rnDeriv Measure.count,
    Measure.withDensity_rnDeriv_eq _ _ (absolutelyContinuous_count _)⟩

/-- Borel Lebesgue measure restricted to the open unit interval. -/
def openIntervalVolume : Measure (Ioo (0 : ℝ) 1) :=
  Measure.comap Subtype.val volume

/-- Rudin's space (0,1) with the Lebesgue-completed sigma algebra. -/
abbrev CompletedOpenUnitInterval :=
  NullMeasurableSpace (Ioo (0 : ℝ) 1) openIntervalVolume

/-- The completed Lebesgue measure used by the printed counterexamples. -/
def openIntervalLebesgue : Measure CompletedOpenUnitInterval := openIntervalVolume.completion

/-- Completion changes the sigma algebra, while preserving the outer-measure
value of every subset. -/
theorem openIntervalLebesgue_apply (E : Set CompletedOpenUnitInterval) :
    openIntervalLebesgue E = volume (Subtype.val '' E : Set ℝ) := by
  change openIntervalVolume E = volume (Subtype.val '' E : Set ℝ)
  exact Measure.comap_subtype_coe_apply measurableSet_Ioo volume E

/-- Measurability in this type is precisely null-measurability for Borel
Lebesgue measure on (0,1), not merely Borel measurability. -/
theorem completedOpenUnitInterval_measurable_iff (E : Set CompletedOpenUnitInterval) :
    MeasurableSet E ↔ NullMeasurableSet (E : Set (Ioo (0 : ℝ) 1)) openIntervalVolume :=
  Iff.rfl

instance openIntervalLebesgue_isComplete : openIntervalLebesgue.IsComplete := by
  change openIntervalVolume.completion.IsComplete
  infer_instance

instance openIntervalLebesgue_isProbabilityMeasure : IsProbabilityMeasure openIntervalLebesgue := by
  constructor
  rw [openIntervalLebesgue_apply]
  simp only [image_univ, Subtype.range_coe, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]

instance openIntervalLebesgue_nullSingletonClass : NullSingletonClass openIntervalLebesgue where
  measure_singleton x := by
    rw [openIntervalLebesgue_apply]
    simp only [image_singleton, measure_singleton]

/-- The two counterexamples following 6.10, on the printed space (0,1) with
Lebesgue-measurable sets and completed Lebesgue measure. -/
theorem openInterval_counterexamples :
    openIntervalLebesgue.IsComplete ∧ openIntervalLebesgue ≪ Measure.count ∧
    (¬ ∃ a s : Measure CompletedOpenUnitInterval,
      Measure.count = a + s ∧ a ≪ openIntervalLebesgue ∧ s ⟂ₘ openIntervalLebesgue) ∧
    (¬ ∃ f : CompletedOpenUnitInterval → ℝ≥0∞,
      Measure.count.withDensity f = openIntervalLebesgue) ∧
    (¬ ∃ f : CompletedOpenUnitInterval → ℂ, Integrable f Measure.count ∧
      ∀ E : Set CompletedOpenUnitInterval, MeasurableSet E →
        (openIntervalLebesgue.real E : ℂ) = ∫ x in E, f x ∂Measure.count) := by
  have hμ : openIntervalLebesgue ≠ 0 := IsProbabilityMeasure.ne_zero _
  exact ⟨inferInstance, absolutelyContinuous_count _, count_no_decomposition _ hμ,
    count_no_density _ hμ, count_no_complex_density _ hμ⟩

theorem completedOpenUnitInterval_count_not_sigmaFinite :
    ¬ SigmaFinite (Measure.count : Measure CompletedOpenUnitInterval) := by
  intro hcount
  letI : SigmaFinite (Measure.count : Measure CompletedOpenUnitInterval) := hcount
  apply count_no_density openIntervalLebesgue (IsProbabilityMeasure.ne_zero _)
  exact ⟨openIntervalLebesgue.rnDeriv Measure.count,
    Measure.withDensity_rnDeriv_eq _ _ (absolutelyContinuous_count _)⟩

/-- The positive sigma-finite extension of Rudin 6.10.  The density is an
everywhere finite, nonnegative real function and is integrable on each set of
finite mass for the original measure. -/
theorem sigmaFinite_positive_decomposition (ν μ : Measure X)
    [SigmaFinite ν] [SigmaFinite μ] :
    ∃ s : Measure X, ∃ h : X → ℝ,
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧ s ⟂ₘ μ ∧
      ν = s + μ.withDensity (fun x ↦ ENNReal.ofReal (h x)) ∧
      (∀ E : Set X, ν E ≠ ∞ → IntegrableOn h E μ) ∧
      (∀ t : Measure X, ∀ g : X → ℝ≥0∞, Measurable g → t ⟂ₘ μ →
        ν = t + μ.withDensity g →
        t = s ∧ g =ᵐ[μ] (fun x ↦ ENNReal.ofReal (h x))) := by
  have hdensity : (fun x ↦ ENNReal.ofReal ((ν.rnDeriv μ x).toReal)) =ᵐ[μ] ν.rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
    exact ENNReal.ofReal_toReal hx
  refine ⟨ν.singularPart μ, fun x ↦ (ν.rnDeriv μ x).toReal,
    (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, Measure.mutuallySingular_singularPart _ _, ?_, ?_, ?_⟩
  · rw [withDensity_congr_ae hdensity]
    exact Measure.haveLebesgueDecomposition_add _ _
  · intro E hE
    exact Measure.integrableOn_toReal_rnDeriv hE
  · intro t g hg ht heq
    exact ⟨Measure.eq_singularPart hg ht heq,
      (Measure.eq_rnDeriv hg ht heq).trans hdensity.symm⟩

/-- In the sigma-finite positive extension, global integrability of the density
cannot be required. Counting measure on the natural numbers has density one
relative to itself; this density is integrable on every finite-mass set but not
on the whole space. -/
theorem sigmaFinite_density_need_not_be_integrable :
    SigmaFinite (Measure.count : Measure ℕ) ∧
    (Measure.count : Measure ℕ).withDensity (fun _ ↦ ENNReal.ofReal (1 : ℝ)) =
      Measure.count ∧
    (∀ E : Set ℕ, Measure.count E ≠ ∞ →
      IntegrableOn (fun _ : ℕ ↦ (1 : ℝ)) E Measure.count) ∧
    ¬ Integrable (fun _ : ℕ ↦ (1 : ℝ)) Measure.count := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · simp
  · intro E hE
    exact integrableOn_const hE
  · rw [integrable_const_iff_isFiniteMeasure one_ne_zero, not_isFiniteMeasure_iff]
    exact Measure.count_apply_infinite (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

#print axioms count_no_decomposition
#print axioms count_no_density
#print axioms count_no_complex_density
#print axioms unitInterval_counterexamples
#print axioms unitInterval_count_not_sigmaFinite
#print axioms openIntervalLebesgue_apply
#print axioms completedOpenUnitInterval_measurable_iff
#print axioms openInterval_counterexamples
#print axioms completedOpenUnitInterval_count_not_sigmaFinite
#print axioms sigmaFinite_positive_decomposition
#print axioms sigmaFinite_density_need_not_be_integrable

end RCA610Discussion
