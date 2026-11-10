import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

noncomputable section
open MeasureTheory Set
open scoped ENNReal Function
namespace RudinRCA.Chapter06
universe u
variable {X : Type u} [MeasurableSpace X]

/-- A countable measurable partition; finite and empty index types are allowed. -/
structure CountablePartition (E : Set X) where
  Index : Type u
  countable : Countable Index
  part : Index → Set X
  measurable : ∀ i, MeasurableSet (part i)
  disjoint : Pairwise (Disjoint on part)
  covers : (⋃ i, part i) = E

attribute [instance] CountablePartition.countable

/-- Rudin's definition of total variation as the supremum over countable partitions. -/
theorem variation_eq_iSup_countablePartitions (μ : ComplexMeasure X) {E : Set X}
    (hE : MeasurableSet E) :
    μ.variation E = ⨆ P : CountablePartition E, ∑' i, ‖μ (P.part i)‖ₑ := by
  classical
  apply le_antisymm
  · change preVariation (‖μ ·‖ₑ) _ _ E ≤ _
    rw [preVariation_apply, VectorMeasure.ennrealToMeasure_apply hE,
      ennrealPreVariation_apply, preVariationFun_apply _ hE]
    apply iSup_le
    intro P
    let Q : CountablePartition E := {
      Index := P.parts
      countable := inferInstance
      part := fun i => i.val.val
      measurable := fun i => i.val.property
      disjoint := by
        intro i j hij
        exact (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl)
          i.property j.property (fun h => hij (Subtype.ext h))
      covers := by
        simpa only [Finset.sup_set_eq_biUnion, Set.iUnion_coe_set, Finset.mem_coe]
          using P.sup_parts_apply (fun _ _ => rfl) rfl }
    have h := le_iSup (fun Q : CountablePartition E => ∑' i, ‖μ (Q.part i)‖ₑ) Q
    simpa only [Q, tsum_fintype, Finset.sum_coe_sort] using h
  · apply iSup_le
    intro P
    calc
      (∑' i, ‖μ (P.part i)‖ₑ) ≤ ∑' i, μ.variation (P.part i) :=
        ENNReal.tsum_le_tsum fun i => μ.enorm_measure_le_variation _
      _ = μ.variation E := by rw [← measure_iUnion P.disjoint P.measurable, P.covers]
end RudinRCA.Chapter06
