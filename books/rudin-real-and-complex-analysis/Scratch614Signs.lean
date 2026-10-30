import Scratch69

noncomputable section
open MeasureTheory Set

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- The Hahn partition from 6.14 has nonnegative signed measure on every
measurable subset of its positive part, and nonpositive signed measure on every
measurable subset of its negative part. The same partition realizes the Jordan
variation identities. -/
theorem theorem_6_14_signs (s : SignedMeasure X) :
    ∃ A B : Set X, MeasurableSet A ∧ MeasurableSet B ∧ A ∪ B = univ ∧ Disjoint A B ∧
      (∀ E, MeasurableSet E →
        s.toJordanDecomposition.posPart.real E = s (E ∩ A) ∧
        s.toJordanDecomposition.negPart.real E = -s (E ∩ B)) ∧
      (∀ E, MeasurableSet E → E ⊆ A → 0 ≤ s E) ∧
      (∀ E, MeasurableSet E → E ⊆ B → s E ≤ 0) := by
  obtain ⟨A, B, hA, hB, hcover, hdisjoint, hparts⟩ := theorem_6_14 s
  refine ⟨A, B, hA, hB, hcover, hdisjoint, hparts, ?_, ?_⟩
  · intro E hE hEA
    have heq := (hparts E hE).1
    rw [inter_eq_left.mpr hEA] at heq
    rw [← heq]
    exact measureReal_nonneg
  · intro E hE hEB
    have heq := (hparts E hE).2
    rw [inter_eq_left.mpr hEB] at heq
    apply neg_nonneg.mp
    rw [← heq]
    exact measureReal_nonneg

#print axioms theorem_6_14_signs

end RudinRCA.Chapter06
