module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

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
