module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

/- BEGIN Ch08Completion.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace RudinRCA.Chapter08

/-- The sigma algebra of the completion, retained as an explicit object. -/
abbrev completedSigma {α : Type*} [MeasurableSpace α] (μ : Measure α) : MeasurableSpace α :=
  inferInstanceAs (MeasurableSpace (NullMeasurableSpace α μ))

section CompletionProduct
variable {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β)

/-- Enlarging both factor sigma algebras also enlarges their product sigma algebra. -/
theorem originalProduct_le_completedFactors :
    mα.prod mβ ≤ (completedSigma μ).prod (completedSigma ν) :=
  sup_le_sup (MeasurableSpace.comap_mono fun _ hs => hs.nullMeasurableSet)
    (MeasurableSpace.comap_mono fun _ hs => hs.nullMeasurableSet)

variable [SigmaFinite μ] [SigmaFinite ν]

/-- A set measurable for the product of the completed factors is null-measurable
for the original product. The two sigma algebras are not asserted equal. -/
theorem completedFactors_le_completedProduct :
    (completedSigma μ).prod (completedSigma ν) ≤ completedSigma (μ.prod ν) := by
  have hfst : @Measurable (α × β) α (completedSigma (μ.prod ν)) (completedSigma μ)
      Prod.fst := fun _ hs => NullMeasurableSet.preimage hs Measure.quasiMeasurePreserving_fst
  have hsnd : @Measurable (α × β) β (completedSigma (μ.prod ν)) (completedSigma ν)
      Prod.snd := fun _ hs => NullMeasurableSet.preimage hs Measure.quasiMeasurePreserving_snd
  intro s hs
  exact (hfst.prodMk hsnd) hs

/-- The original product outer measure, on the intermediate sigma algebra that is
obtained by completing each factor before taking the product. -/
def intermediateCompletedProduct :
    Measure (NullMeasurableSpace α μ × NullMeasurableSpace β ν) where
  toOuterMeasure := (μ.prod ν).toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint)
    (fun i => completedFactors_le_completedProduct μ ν _ (hs i))
  trim_le := by
    nth_rewrite 2 [← (μ.prod ν).trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ (originalProduct_le_completedFactors μ ν)

private theorem sigmaFinite_completion (μ : Measure α) [SigmaFinite μ] :
    SigmaFinite μ.completion :=
  ⟨⟨{ set := spanningSets μ,
        set_mem := fun _ => Set.mem_univ _,
        finite := measure_spanningSets_lt_top μ,
        spanning := iUnion_spanningSets μ }⟩⟩

/-- Completing each factor does not change the product outer measure on any set. -/
theorem completedFactors_product_apply (s : Set (α × β)) :
    (μ.completion.prod ν.completion) s = (μ.prod ν) s := by
  letI := sigmaFinite_completion μ
  letI := sigmaFinite_completion ν
  have heq : μ.completion.prod ν.completion = intermediateCompletedProduct μ ν := by
    apply Measure.prod_eq
    intro a b _ _
    exact Measure.prod_prod (μ := μ) (ν := ν) a b
  rw [heq]
  rfl

/-- The original and completed-factor products have the same null sets and a.e. filter. -/
theorem completedFactors_product_ae :
    ae (μ.completion.prod ν.completion) = ae (μ.prod ν) := by
  ext s
  change (μ.completion.prod ν.completion) sᶜ = 0 ↔ (μ.prod ν) sᶜ = 0
  exact (congrArg (fun z : ℝ≥0∞ => z = 0)
    (completedFactors_product_apply μ ν (show Set (α × β) from sᶜ))).to_iff

/-- Completing the product of completed factors gives precisely the same sigma
algebra as completing the original product. This is the completion content of 8.11. -/
theorem completedFactors_product_completedSigma :
    completedSigma (μ.completion.prod ν.completion) =
      (completedSigma (μ.prod ν) : MeasurableSpace (α × β)) := by
  apply le_antisymm
  · intro s hs
    rcases hs with ⟨t, ht, hst⟩
    have ht' : @NullMeasurableSet (α × β) (mα.prod mβ)
        (show Set (α × β) from t) (μ.prod ν) :=
      completedFactors_le_completedProduct μ ν t ht
    rw [completedFactors_product_ae μ ν] at hst
    exact ht'.congr (Filter.EventuallyEq.symm hst)
  · intro s hs
    rcases hs with ⟨t, ht, hst⟩
    refine ⟨t, originalProduct_le_completedFactors μ ν t ht, ?_⟩
    rwa [completedFactors_product_ae μ ν]

/-- The identity equivalence identifies the two completed product measure spaces. -/
def completedProductEquiv :
    NullMeasurableSpace (NullMeasurableSpace α μ × NullMeasurableSpace β ν)
      (μ.completion.prod ν.completion) ≃ᵐ NullMeasurableSpace (α × β) (μ.prod ν) where
  toEquiv := Equiv.refl (α × β)
  measurable_toFun := measurable_id'' (completedFactors_product_completedSigma μ ν).ge
  measurable_invFun := measurable_id'' (completedFactors_product_completedSigma μ ν).le

theorem completedProductEquiv_measurePreserving :
    MeasurePreserving (completedProductEquiv μ ν)
      (μ.completion.prod ν.completion).completion (μ.prod ν).completion where
  measurable := (completedProductEquiv μ ν).measurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply (completedProductEquiv μ ν).measurable hs]
    exact completedFactors_product_apply μ ν s

end CompletionProduct

section CompletionEquiv
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Any measure-preserving measurable equivalence extends to the completed spaces. -/
def completionEquiv (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    NullMeasurableSpace α μ ≃ᵐ NullMeasurableSpace β ν where
  toEquiv := e.toEquiv
  measurable_toFun := fun _ hs => NullMeasurableSet.preimage hs he.quasiMeasurePreserving
  measurable_invFun := fun _ hs => NullMeasurableSet.preimage hs (MeasurePreserving.symm e he).quasiMeasurePreserving

theorem completionEquiv_measurePreserving (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    MeasurePreserving (completionEquiv e he) μ.completion ν.completion where
  measurable := (completionEquiv e he).measurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply (completionEquiv e he).measurable hs]
    exact he.measure_preimage_equiv s

end CompletionEquiv

/-- Standard split of r+s real coordinates into the first r and last s coordinates. -/
def euclideanCoordinateSplit (r s : ℕ) :
    (Fin (r + s) → ℝ) ≃ᵐ ((Fin r → ℝ) × (Fin s → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin r ⊕ Fin s => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s => ℝ))

theorem euclideanCoordinateSplit_measurePreserving (r s : ℕ) :
    MeasurePreserving (euclideanCoordinateSplit r s) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin s => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin r ⊕ Fin s => ℝ) finSumFinEquiv.symm)

/-- Full 8.11: completed Lebesgue measure on r+s real coordinates identifies with
completion of the product of completed r- and s-dimensional Lebesgue measures.
This even covers zero dimensions, so in particular covers Rudin's r,s≥1. -/
def lebesgueCompletedCoordinateSplit (r s : ℕ) :
    NullMeasurableSpace (Fin (r + s) → ℝ) (volume : Measure (Fin (r + s) → ℝ)) ≃ᵐ
      NullMeasurableSpace
        (NullMeasurableSpace (Fin r → ℝ) (volume : Measure (Fin r → ℝ)) ×
         NullMeasurableSpace (Fin s → ℝ) (volume : Measure (Fin s → ℝ)))
        ((volume : Measure (Fin r → ℝ)).completion.prod
         (volume : Measure (Fin s → ℝ)).completion) :=
  (completionEquiv (euclideanCoordinateSplit r s)
    (euclideanCoordinateSplit_measurePreserving r s)).trans
    (completedProductEquiv (volume : Measure (Fin r → ℝ))
      (volume : Measure (Fin s → ℝ))).symm

theorem lebesgueCompletedCoordinateSplit_measurePreserving (r s : ℕ) :
    MeasurePreserving (lebesgueCompletedCoordinateSplit r s)
      (volume : Measure (Fin (r + s) → ℝ)).completion
      ((volume : Measure (Fin r → ℝ)).completion.prod
        (volume : Measure (Fin s → ℝ)).completion).completion :=
  (MeasurePreserving.symm
    (completedProductEquiv (volume : Measure (Fin r → ℝ)) (volume : Measure (Fin s → ℝ)))
    (completedProductEquiv_measurePreserving (volume : Measure (Fin r → ℝ))
      (volume : Measure (Fin s → ℝ)))).comp
    (completionEquiv_measurePreserving (euclideanCoordinateSplit r s)
      (euclideanCoordinateSplit_measurePreserving r s))

end RudinRCA.Chapter08
end
/- END Ch08Completion.lean -/

/- BEGIN Ch08FubiniCompletion.lean -/
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
end
/- END Ch08FubiniCompletion.lean -/

/- BEGIN Ch08CounterexampleCount.lean -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- 8.9(b), diagonal of the unit square. Both integrals use restrictions to [0,1],
which is the ambient-real representation of integration over the book's interval. -/
def diagonalIndicator (x y : ℝ) : ℝ≥0∞ := if x = y then 1 else 0

lemma diagonalIndicator_section (x : ℝ) :
    diagonalIndicator x = ({x} : Set ℝ).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext y
  simp only [diagonalIndicator, Set.indicator_apply, Set.mem_singleton_iff]
  split_ifs <;> simp_all

lemma diagonalIndicator_symm (x y : ℝ) : diagonalIndicator x y = diagonalIndicator y x := by
  simp only [diagonalIndicator, eq_comm]

lemma diagonalIndicator_measurable : Measurable (fun z : ℝ × ℝ => diagonalIndicator z.1 z.2) := by
  change Measurable (fun z : ℝ × ℝ => if z.1 = z.2 then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const measurable_const

lemma diagonal_lebesgue_section (y : ℝ) :
    ∫⁻ x, diagonalIndicator x y ∂volume.restrict (Icc (0 : ℝ) 1) = 0 := by
  simp_rw [diagonalIndicator_symm _ y, diagonalIndicator_section]
  rw [lintegral_indicator (measurableSet_singleton y)]
  simp [Measure.restrict_apply, measurableSet_singleton]

lemma diagonal_count_section {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫⁻ y, diagonalIndicator x y ∂Measure.count.restrict (Icc (0 : ℝ) 1) = 1 := by
  rw [diagonalIndicator_section, lintegral_indicator (measurableSet_singleton x)]
  simp [Measure.restrict_apply, measurableSet_singleton, hx]

/-- 8.9(b): two finite unequal iterated integrals of a nonnegative measurable function. -/
theorem counting_measure_counterexample :
    (∫⁻ y, ∫⁻ x, diagonalIndicator x y ∂volume.restrict (Icc (0 : ℝ) 1)
      ∂Measure.count.restrict (Icc (0 : ℝ) 1)) = 0 ∧
    (∫⁻ x, ∫⁻ y, diagonalIndicator x y ∂Measure.count.restrict (Icc (0 : ℝ) 1)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 1 := by
  constructor
  · simp_rw [diagonal_lebesgue_section, lintegral_zero]
  · calc
      _ = ∫⁻ _x, (1 : ℝ≥0∞) ∂volume.restrict (Icc (0 : ℝ) 1) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact diagonal_count_section hx
      _ = 1 := by simp

/-- The counting measure in 8.9(b) is not sigma-finite, as the counterexample itself proves. -/
theorem interval_count_not_sigmaFinite :
    ¬ SigmaFinite (Measure.count.restrict (Icc (0 : ℝ) 1)) := by
  intro h
  letI := h
  have heq := lintegral_lintegral_swap (f := diagonalIndicator)
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := Measure.count.restrict (Icc (0 : ℝ) 1))
    diagonalIndicator_measurable.aemeasurable
  rw [counting_measure_counterexample.1, counting_measure_counterexample.2] at heq
  exact one_ne_zero heq

end RudinRCA.Chapter08
end
/- END Ch08CounterexampleCount.lean -/

/- BEGIN Ch08ProductExample.lean -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- The function in 8.13: x^(-1/2) on (0,1), zero elsewhere. -/
def inverseSqrtExample : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-1 / 2 : ℝ))

/-- The printed function in 8.13 is in L1. -/
theorem inverseSqrtExample_integrable : Integrable inverseSqrtExample := by
  rw [inverseSqrtExample, integrable_indicator_iff measurableSet_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)

/-- A product of two L1 functions need not be in L1, using the printed example. -/
theorem inverseSqrtExample_square_not_integrable :
    ¬ Integrable (fun x => inverseSqrtExample x * inverseSqrtExample x) := by
  have heq : (fun x => inverseSqrtExample x * inverseSqrtExample x) =
      (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · simp only [inverseSqrtExample, indicator_of_mem hx]
      rw [← Real.rpow_add hx.1]
      norm_num
    · simp [inverseSqrtExample, hx]
  rw [heq, integrable_indicator_iff measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  exact lt_irrefl _

/-- Extended-valued positive convolution from 8.13, defined even at exceptional points. -/
def positiveConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (f (x - y) * g y)

/-- 8.13: positive L1 factors give a finite positive convolution almost everywhere,
with finite integral; the exceptional values were never replaced by zero. -/
theorem positiveConvolution_finite {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    AEMeasurable (positiveConvolution f g) volume ∧
    (∫⁻ x, positiveConvolution f g x) < ∞ ∧
    (∀ᵐ x, positiveConvolution f g x < ∞) := by
  have hi : Integrable (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2)
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf
  have he (p : ℝ × ℝ) : ‖f (p.1 - p.2) * g p.2‖ₑ =
      ENNReal.ofReal (f (p.1 - p.2) * g p.2) :=
    Real.enorm_eq_ofReal (mul_nonneg (hfn _) (hgn _))
  have hm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (f (p.1 - p.2) * g p.2))
      (volume.prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hfinProd : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (f (p.1 - p.2) * g p.2)
      ∂volume.prod volume) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, he] using hi.hasFiniteIntegral
  have hm' : AEMeasurable (positiveConvolution f g) volume := hm.lintegral_prod_right'
  have hfin : (∫⁻ x, positiveConvolution f g x) < ∞ := by
    change (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x - y) * g y)) < ∞
    rw [← lintegral_prod _ hm]
    exact hfinProd
  exact ⟨hm', hfin, ae_lt_top' hm' hfin.ne⟩

end RudinRCA.Chapter08
end
/- END Ch08ProductExample.lean -/

/- BEGIN Ch08Vitali.lean -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- Rational translation equivalence used to construct a Lebesgue nonmeasurable set. -/
def rationalTranslationSetoid : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = (q : ℝ)
  iseqv := ⟨fun x => ⟨0, by simp⟩,
    by
      rintro x y ⟨q, hq⟩
      exact ⟨-q, by push_cast; linarith⟩,
    by
      rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
      exact ⟨q + r, by push_cast; linarith⟩⟩

/-- Choose one representative of each rational translation class. -/
def vitaliRepresentatives : Set ℝ :=
  range (Quotient.out : Quotient rationalTranslationSetoid → ℝ)

lemma vitali_representatives_unique {x y : ℝ} (hx : x ∈ vitaliRepresentatives)
    (hy : y ∈ vitaliRepresentatives) {q : ℚ} (hxy : x - y = (q : ℝ)) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have h : a = b := by
    simpa only [Quotient.out_eq] using (Quotient.sound (s := rationalTranslationSetoid) ⟨q, hxy⟩)
  rw [h]

lemma rational_translate_disjoint {W : Set ℝ} (hW : W ⊆ vitaliRepresentatives) :
    Pairwise (fun q r : ℚ => Disjoint {x : ℝ | x - (q : ℝ) ∈ W}
      {x : ℝ | x - (r : ℝ) ∈ W}) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he : x - (q : ℝ) = x - (r : ℝ) :=
    vitali_representatives_unique (hW hx) (hW hy)
      (q := r - q) (by push_cast; ring)
  have hc : (q : ℝ) = (r : ℝ) := by linarith
  exact hqr (Rat.cast_injective hc)

lemma volume_rational_translate (W : Set ℝ) (q : ℚ) :
    volume {x : ℝ | x - (q : ℝ) ∈ W} = volume W := by
  change volume ((fun x : ℝ => x - (q : ℝ)) ⁻¹' W) = volume W
  simpa only [sub_eq_add_neg] using measure_preimage_add_right volume (-(q : ℝ)) W

/-- Every bounded Lebesgue-measurable subset of a rational transversal is null. -/
lemma bounded_vitali_subset_null {W : Set ℝ} (hW : W ⊆ vitaliRepresentatives)
    (hm : NullMeasurableSet W volume) {n : ℝ} (hb : W ⊆ Icc (-n) n) : volume W = 0 := by
  classical
  let T := {q : ℚ // q ∈ Icc (0 : ℚ) 1}
  haveI : Infinite T := (Set.Icc_infinite (by norm_num : (0 : ℚ) < 1)).to_subtype
  let F : T → Set ℝ := fun q => {x | x - (q.1 : ℝ) ∈ W}
  have hFd : Pairwise (fun q r : T => Disjoint (F q) (F r)) := by
    intro q r hqr
    exact rational_translate_disjoint hW (fun h => hqr (Subtype.ext h))
  have hFm (q : T) : NullMeasurableSet (F q) volume := by
    exact hm.preimage (measurePreserving_sub_right volume (q.1 : ℝ)).quasiMeasurePreserving
  have hbound : (⋃ q, F q) ⊆ Icc (-n) (n + 1) := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    have hw := hb hq
    have hq0 : (0 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast q.2.1
    have hq1 : (q.1 : ℝ) ≤ (1 : ℝ) := by exact_mod_cast q.2.2
    constructor <;> linarith [hw.1, hw.2]
  by_contra hn
  have hi : volume (⋃ q, F q) = ∞ := by
    rw [measure_iUnion₀ (fun i j hij => (hFd hij).aedisjoint) hFm]
    simp only [F, volume_rational_translate]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hn
  have hle : volume (⋃ q, F q) ≤ volume (Icc (-n) (n + 1)) := measure_mono hbound
  rw [hi] at hle
  have hfinite : volume (Icc (-n) (n + 1)) < ∞ := isCompact_Icc.measure_lt_top
  exact hfinite.ne (top_unique hle)

/-- Existence of a non-Lebesgue-measurable set, used by the concrete example in 8.10. -/
theorem exists_not_lebesgue_measurable : ∃ B : Set ℝ, ¬ NullMeasurableSet B volume := by
  refine ⟨vitaliRepresentatives, ?_⟩
  intro hm
  have hw (n : ℕ) : volume (vitaliRepresentatives ∩ Icc (-(n : ℝ)) n) = 0 :=
    bounded_vitali_subset_null inter_subset_left (hm.inter measurableSet_Icc.nullMeasurableSet)
      inter_subset_right
  have hv : volume vitaliRepresentatives = 0 := by
    apply measure_mono_null (t := ⋃ n : ℕ, vitaliRepresentatives ∩ Icc (-(n : ℝ)) n) ?_
      (measure_iUnion_null hw)
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    apply mem_iUnion.mpr
    refine ⟨n, hx, ?_, ?_⟩
    · have hh := neg_abs_le x
      linarith
    · exact (le_abs_self x).trans hn
  have hcover : (⋃ q : ℚ, {x : ℝ | x - (q : ℝ) ∈ vitaliRepresentatives}) = univ := by
    apply eq_univ_of_forall
    intro x
    let a : Quotient rationalTranslationSetoid := Quotient.mk _ x
    have hr : rationalTranslationSetoid x a.out := Quotient.exact (Quotient.out_eq a).symm
    obtain ⟨q, hq⟩ := hr
    apply mem_iUnion.mpr
    refine ⟨q, ?_⟩
    have he : x - (q : ℝ) = a.out := by linarith
    change x - (q : ℝ) ∈ vitaliRepresentatives
    rw [he]
    exact ⟨a, rfl⟩
  have hnull := measure_iUnion_null (fun q : ℚ => (volume_rational_translate vitaliRepresentatives q).trans hv)
  rw [hcover] at hnull
  simpa using hnull

/-- 8.10's concrete Lebesgue example: even the product of two complete one-dimensional
Lebesgue measures is not complete. This uses the actual Vitali construction above. -/
theorem completed_lebesgue_product_not_complete :
    ¬ ((volume : Measure ℝ).completion.prod (volume : Measure ℝ).completion).IsComplete := by
  letI : SigmaFinite (volume : Measure ℝ).completion := sigmaFinite_completion volume
  obtain ⟨B, hB⟩ := exists_not_lebesgue_measurable
  let z : NullMeasurableSpace ℝ (volume : Measure ℝ) := (0 : ℝ)
  apply product_not_complete (volume : Measure ℝ).completion (volume : Measure ℝ).completion
    (A := {z}) (B := B) (singleton_nonempty z)
  · change (volume : Measure ℝ) ({0} : Set ℝ) = 0
    simp
  · exact hB

end RudinRCA.Chapter08
end
/- END Ch08Vitali.lean -/

/- BEGIN Ch08Sierpinski.lean -/
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace RudinRCA.Chapter08

variable {X W : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [LinearOrder W] (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The set in 8.9(c), using the well-order supplied in Rudin's conditional construction. -/
def sierpinskiSet (j : X ≃ W) : Set (X × X) := {p | j p.1 < j p.2}

/-- 8.9(c), conditional form with precisely the countable-predecessor well-order that
Rudin takes from CH. No continuum-hypothesis axiom is introduced. Instantiating `X`
with the unit interval and its Lebesgue probability measure gives the printed example.
The additional CH-to-existence implication is not asserted by this theorem. -/
theorem sierpinski_counterexample (j : X ≃ W)
    (_hw : WellFounded ((· < ·) : W → W → Prop))
    (hcount : ∀ w : W, (Set.Iio w).Countable) :
    (∀ x : X, MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1) ∧
    (∀ y : X, MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0) ∧
    (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 ∧
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 ∧
    ¬ MeasurableSet (sierpinskiSet j) := by
  classical
  have hpred (y : X) : {x : X | j x < j y}.Countable :=
    (hcount (j y)).preimage j.injective
  have hsucc (x : X) : ({y : X | j x < j y}ᶜ).Countable := by
    have heq : {y : X | j x < j y}ᶜ = {y : X | j y < j x} ∪ {x} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_singleton_iff, not_lt, le_iff_lt_or_eq, j.injective.eq_iff]
    rw [heq]
    exact (hpred x).union (Set.countable_singleton x)
  have hx (x : X) : MeasurableSet {y | (x, y) ∈ sierpinskiSet j} ∧
      μ {y | (x, y) ∈ sierpinskiSet j} = 1 := by
    constructor
    · simpa only [compl_compl, sierpinskiSet, Set.mem_ofPred_eq] using (hsucc x).measurableSet.compl
    · have h := measure_compl (hsucc x).measurableSet
        (measure_ne_top μ ({y : X | j x < j y}ᶜ))
      simpa only [compl_compl, (hsucc x).measure_zero μ, measure_univ, tsub_zero, sierpinskiSet, Set.mem_ofPred_eq] using h
  have hy (y : X) : MeasurableSet {x | (x, y) ∈ sierpinskiSet j} ∧
      μ {x | (x, y) ∈ sierpinskiSet j} = 0 :=
    ⟨(hpred y).measurableSet, (hpred y).measure_zero μ⟩
  have hxint : (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) = 1 := by
    calc
      _ = ∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ := lintegral_congr (fun x => (hx x).2)
      _ = 1 := by simp
  have hyint : (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) = 0 := by
    calc
      _ = ∫⁻ _ : X, (0 : ℝ≥0∞) ∂μ := lintegral_congr (fun y => (hy y).2)
      _ = 0 := by simp
  refine ⟨hx, hy, hxint, hyint, ?_⟩
  intro hQ
  have h := (Measure.prod_apply (μ := μ) (ν := μ) hQ).symm.trans
    (Measure.prod_apply_symm (μ := μ) (ν := μ) hQ)
  change (∫⁻ x, μ {y | (x, y) ∈ sierpinskiSet j} ∂μ) =
    (∫⁻ y, μ {x | (x, y) ∈ sierpinskiSet j} ∂μ) at h
  rw [hxint, hyint] at h
  exact one_ne_zero h


/-- A concrete well-order of first uncountable cardinality. -/
abbrev SierpinskiOrder := (Cardinal.aleph 1 : Cardinal.{0}).ord.ToType

/-- The set-theoretic step used in 8.9(c), explicitly conditional on CH.
The hypothesis is a proposition, never an added axiom. -/
theorem ch_unitInterval_wellOrder
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    Nonempty ((Set.Icc (0 : ℝ) 1) ≃ SierpinskiOrder) ∧
    WellFounded ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) ∧
    (∀ w : SierpinskiOrder, (Set.Iio w).Countable) := by
  constructor
  · apply Cardinal.eq.mp
    rw [Cardinal.mk_Icc_real zero_lt_one]
    exact hCH.trans (Cardinal.mk_ord_toType _).symm
  · constructor
    · exact wellFounded_lt
    · intro w
      apply Cardinal.le_aleph0_iff_set_countable.mp
      apply Cardinal.lt_aleph_one_iff.mp
      have ho : (Cardinal.mk SierpinskiOrder).ord = Ordinal.type ((· < ·) : SierpinskiOrder → SierpinskiOrder → Prop) := by
        simp only [SierpinskiOrder, Cardinal.mk_ord_toType, Ordinal.type_toType]
      have h := Cardinal.mk_Iio_lt w ho
      simpa only [SierpinskiOrder, Cardinal.mk_ord_toType] using h

/-- The literal unit interval used in the printed counterexample. -/
abbrev SierpinskiInterval := Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to the unit interval and regarded as a measure on it. -/
noncomputable def sierpinskiIntervalMeasure : Measure SierpinskiInterval :=
  (volume : Measure ℝ).comap Subtype.val

instance sierpinskiInterval_probability : IsProbabilityMeasure sierpinskiIntervalMeasure where
  measure_univ := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) Set.univ = 1
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
    change volume (Set.Icc (0 : ℝ) 1) = 1
    simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

instance sierpinskiInterval_nullSingletons : NullSingletonClass sierpinskiIntervalMeasure where
  measure_singleton x := by
    change ((volume : Measure ℝ).comap (Subtype.val : SierpinskiInterval → ℝ)) {x} = 0
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
    simp

/-- The unit interval with the completed Lebesgue σ-algebra, as in Rudin. -/
abbrev CompletedSierpinskiInterval :=
  NullMeasurableSpace SierpinskiInterval sierpinskiIntervalMeasure

noncomputable abbrev completeSierpinskiIntervalMeasure : Measure CompletedSierpinskiInterval :=
  sierpinskiIntervalMeasure.completion

instance completedSierpinskiInterval_probability :
    IsProbabilityMeasure completeSierpinskiIntervalMeasure where
  measure_univ := by
    change sierpinskiIntervalMeasure Set.univ = 1
    exact measure_univ

instance completedSierpinskiInterval_nullSingletons :
    NullSingletonClass completeSierpinskiIntervalMeasure where
  measure_singleton x := by
    change sierpinskiIntervalMeasure {x} = 0
    exact @measure_singleton SierpinskiInterval _ sierpinskiIntervalMeasure
      sierpinskiInterval_nullSingletons x

/-- 8.9(c) on the unit square, with CH as an explicit hypothesis. The section integrals
are those of the characteristic function of `Q`, because each section is measurable. -/
theorem unit_square_sierpinski_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (CompletedSierpinskiInterval × CompletedSierpinskiInterval),
      (∀ x : CompletedSierpinskiInterval, MeasurableSet {y | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : CompletedSierpinskiInterval, MeasurableSet {x | (x, y) ∈ Q} ∧
        completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, completeSierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  exact ⟨sierpinskiSet j, sierpinski_counterexample completeSierpinskiIntervalMeasure j hw hc⟩

end RudinRCA.Chapter08
end
/- END Ch08Sierpinski.lean -/

/- BEGIN Ch08PowersetCount.lean -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RudinRCA.Chapter08

/-- A copy of X with the power-set sigma algebra used for the counting factor in 8.9(b). -/
structure PowersetCopy (X : Type*) where
  val : X

instance (X : Type*) : MeasurableSpace (PowersetCopy X) := ⊤
instance (X : Type*) : MeasurableSingletonClass (PowersetCopy X) := ⟨fun _ => trivial⟩

/-- 8.9(b), with the full power-set counting sigma algebra and an arbitrary atomless
probability first factor. The explicit diagonal measurability hypothesis holds for the
completed Lebesgue unit interval, as shown in the specialization below. -/
theorem powerset_counting_counterexample {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hd : MeasurableSet {p : X × X | p.1 = p.2}) :
    ∃ Q : Set (X × PowersetCopy X), MeasurableSet Q ∧
      (∀ x, Measure.count {y | (x, y) ∈ Q} = 1) ∧
      (∀ y, μ {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂μ) = 1 ∧
      (∫⁻ y, μ {x | (x, y) ∈ Q} ∂Measure.count) = 0 := by
  let Q : Set (X × PowersetCopy X) := {p | p.1 = p.2.val}
  have hv : Measurable (PowersetCopy.val : PowersetCopy X → X) := fun _ _ => trivial
  have hQ : MeasurableSet Q := hd.preimage (measurable_fst.prodMk (hv.comp measurable_snd))
  have hx (x : X) : {y : PowersetCopy X | (x, y) ∈ Q} = {⟨x⟩} := by
    ext y
    cases y
    simp [Q, eq_comm]
  have hy (y : PowersetCopy X) : {x : X | (x, y) ∈ Q} = {y.val} := by
    ext x
    simp [Q]
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hx]; simp
  · intro y; rw [hy]; simp
  · simp_rw [hx]; simp
  · simp_rw [hy]; simp

/-- The exact completed-Lebesgue / power-set-counting unit-square instance of 8.9(b).
This declaration is assembled after the interval-measure definitions accompanying 8.9(c). -/
theorem unit_square_powerset_counting_counterexample :
    ∃ Q : Set (CompletedSierpinskiInterval × PowersetCopy CompletedSierpinskiInterval),
      MeasurableSet Q ∧
      (∀ x, Measure.count {y | (x, y) ∈ Q} = 1) ∧
      (∀ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂Measure.count) = 0 := by
  apply powerset_counting_counterexample completeSierpinskiIntervalMeasure
  have hm : Measurable (fun x : CompletedSierpinskiInterval => (show SierpinskiInterval from x).val) := by
    intro s hs
    exact (measurable_subtype_coe hs).nullMeasurableSet
  have hd := measurableSet_eq_fun (hm.comp measurable_fst) (hm.comp measurable_snd)
  convert hd using 1
  ext p
  exact Subtype.ext_iff

/-- The counting factor used in the exact example is not sigma-finite. -/
theorem unit_interval_powerset_count_not_sigmaFinite :
    ¬ SigmaFinite (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval)) := by
  intro hc
  letI := hc
  obtain ⟨Q, hQ, _, _, hi, hj⟩ := unit_square_powerset_counting_counterexample
  have h := (Measure.prod_apply (μ := completeSierpinskiIntervalMeasure)
    (ν := (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval))) hQ).symm.trans
    (Measure.prod_apply_symm (μ := completeSierpinskiIntervalMeasure)
      (ν := (Measure.count : Measure (PowersetCopy CompletedSierpinskiInterval))) hQ)
  change (∫⁻ x, Measure.count {y | (x, y) ∈ Q} ∂completeSierpinskiIntervalMeasure) =
    (∫⁻ y, completeSierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂Measure.count) at h
  rw [hi, hj] at h
  exact one_ne_zero h

end RudinRCA.Chapter08
end
/- END Ch08PowersetCount.lean -/

