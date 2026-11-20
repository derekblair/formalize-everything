module
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

public section

open Set MeasureTheory MeasurableSpace

namespace RudinRCA.Chapter08

variable {α β : Type*}

/-- 8.1: rectangles, without any measurability requirement. -/
def IsRectangle (E : Set (α × β)) : Prop :=
  ∃ A : Set α, ∃ B : Set β, E = A ×ˢ B

/-- 8.1: the measurable rectangles in a product of measurable spaces. -/
def measurableRectangles [MeasurableSpace α] [MeasurableSpace β] : Set (Set (α × β)) :=
  Set.image2 (· ×ˢ ·) {A : Set α | MeasurableSet A} {B : Set β | MeasurableSet B}

/-- 8.1: an elementary set is a union of finitely many disjoint measurable rectangles.
`Finpartition` records the finite disjoint union and its equality with the original set. -/
def elementarySets [MeasurableSpace α] [MeasurableSpace β] : Set (Set (α × β)) :=
  {E | ∃ P : Finpartition E, (P.parts : Set (Set (α × β))) ⊆ measurableRectangles}

/-- 8.1: the generated product σ-algebra. -/
@[instance_reducible]
def rectangleProductSpace [MeasurableSpace α] [MeasurableSpace β] : MeasurableSpace (α × β) :=
  MeasurableSpace.generateFrom measurableRectangles

/-- 8.1: set sections in the two coordinates. -/
def setSectionX (E : Set (α × β)) (x : α) : Set β := {y | (x, y) ∈ E}
def setSectionY (E : Set (α × β)) (y : β) : Set α := {x | (x, y) ∈ E}

/-- 8.1: a monotone class is closed under increasing unions and decreasing intersections. -/
structure IsMonotoneClass (M : Set (Set α)) : Prop where
  iUnion_mem : ∀ s : ℕ → Set α, Monotone s → (∀ n, s n ∈ M) → (⋃ n, s n) ∈ M
  iInter_mem : ∀ s : ℕ → Set α, Antitone s → (∀ n, s n ∈ M) → (⋂ n, s n) ∈ M

/-- The smallest class obtained from `C` using precisely the monotone-class operations. -/
inductive MonotoneClosure (C : Set (Set α)) : Set α → Prop
  | base {s} : s ∈ C → MonotoneClosure C s
  | iUnion (s : ℕ → Set α) : Monotone s → (∀ n, MonotoneClosure C (s n)) →
      MonotoneClosure C (⋃ n, s n)
  | iInter (s : ℕ → Set α) : Antitone s → (∀ n, MonotoneClosure C (s n)) →
      MonotoneClosure C (⋂ n, s n)

namespace MonotoneClosure

variable {C M : Set (Set α)} {s t : Set α}

theorem minimal (hM : IsMonotoneClass M) (hCM : C ⊆ M)
    (hs : MonotoneClosure C s) : s ∈ M := by
  induction hs with
  | base h => exact hCM h
  | iUnion s hm _ ih => exact hM.iUnion_mem s hm ih
  | iInter s hm _ ih => exact hM.iInter_mem s hm ih

theorem compl_mem (hC : IsSetAlgebra C) (hs : MonotoneClosure C s) :
    MonotoneClosure C sᶜ := by
  induction hs with
  | base h => exact .base (hC.compl_mem h)
  | iUnion s hm _ ih =>
    rw [compl_iUnion]
    exact .iInter (fun n => (s n)ᶜ) (fun i j hij => compl_subset_compl.mpr (hm hij)) ih
  | iInter s hm _ ih =>
    rw [compl_iInter]
    exact .iUnion (fun n => (s n)ᶜ) (fun i j hij => compl_subset_compl.mpr (hm hij)) ih

theorem inter_base (hC : IsSetAlgebra C) (hs : MonotoneClosure C s) (ht : t ∈ C) :
    MonotoneClosure C (s ∩ t) := by
  induction hs with
  | base h => exact .base (hC.inter_mem h ht)
  | iUnion s hm _ ih =>
    rw [iUnion_inter]
    exact .iUnion (fun n => s n ∩ t) (fun i j hij => inter_subset_inter_left _ (hm hij)) ih
  | iInter s hm _ ih =>
    rw [iInter_inter]
    exact .iInter (fun n => s n ∩ t) (fun i j hij => inter_subset_inter_left _ (hm hij)) ih

theorem inter_mem (hC : IsSetAlgebra C) (hs : MonotoneClosure C s)
    (ht : MonotoneClosure C t) : MonotoneClosure C (s ∩ t) := by
  induction ht with
  | base h => exact inter_base hC hs h
  | iUnion t hm _ ih =>
    rw [inter_iUnion]
    exact .iUnion (fun n => s ∩ t n) (fun i j hij => inter_subset_inter_right _ (hm hij)) ih
  | iInter t hm _ ih =>
    rw [inter_iInter]
    exact .iInter (fun n => s ∩ t n) (fun i j hij => inter_subset_inter_right _ (hm hij)) ih

theorem isSetAlgebra (hC : IsSetAlgebra C) : IsSetAlgebra {s | MonotoneClosure C s} where
  empty_mem := .base hC.empty_mem
  compl_mem := fun {_} hs => compl_mem hC hs
  union_mem := by
    intro s t hs ht
    rw [union_eq_compl_compl_inter_compl]
    exact compl_mem hC (inter_mem hC (compl_mem hC hs) (compl_mem hC ht))

@[instance_reducible]
def measurableSpace (hC : IsSetAlgebra C) : MeasurableSpace α where
  MeasurableSet' := MonotoneClosure C
  measurableSet_empty := .base hC.empty_mem
  measurableSet_compl := fun _ => compl_mem hC
  measurableSet_iUnion := by
    intro s hs
    rw [← iUnion_accumulate (s := s)]
    exact .iUnion (accumulate s) (monotone_accumulate (s := s))
      (fun n => (isSetAlgebra hC).isSetRing.accumulate_mem hs n)

theorem iff_measurableSet (hC : IsSetAlgebra C) :
    MonotoneClosure C s ↔ MeasurableSet[MeasurableSpace.generateFrom C] s := by
  constructor
  · intro hs
    induction hs with
    | base h => exact measurableSet_generateFrom h
    | iUnion _ _ _ ih => exact MeasurableSet.iUnion ih
    | iInter _ _ _ ih => exact MeasurableSet.iInter ih
  · exact MeasurableSpace.generateFrom_le (m := measurableSpace hC) (fun _ hs => .base hs) s

end MonotoneClosure

variable [MeasurableSpace α] [MeasurableSpace β]

theorem rectangleProductSpace_eq :
    rectangleProductSpace (α := α) (β := β) = (inferInstance : MeasurableSpace (α × β)) :=
  generateFrom_prod

private theorem measurableRectangles_semiring :
    IsSetSemiring (measurableRectangles (α := α) (β := β)) where
  empty_mem := by
    exact ⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, Set.empty_prod⟩
  inter_mem := by
    rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
    exact ⟨A ∩ C, hA.inter hC, B ∩ D, hB.inter hD, Set.prod_inter_prod.symm⟩
  sdiff_eq_sUnion' := by
    classical
    rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
    let U := (A \ C) ×ˢ B
    let V := (A ∩ C) ×ˢ (B \ D)
    refine ⟨{U, V}, ?_, ?_, ?_⟩
    · intro E hE
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hE
      rcases hE with rfl | rfl
      · exact ⟨A \ C, hA.diff hC, B, hB, rfl⟩
      · exact ⟨A ∩ C, hA.inter hC, B \ D, hB.diff hD, rfl⟩
    · have hUV : Disjoint U V := by
        rw [Set.disjoint_left]
        rintro ⟨x, y⟩ hx hy
        exact hx.1.2 hy.1.2
      intro E hE F hF hEF
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hE hF
      rcases hE with rfl | rfl <;> rcases hF with rfl | rfl
      · exact (hEF rfl).elim
      · exact hUV
      · exact hUV.symm
      · exact (hEF rfl).elim
    · ext p
      by_cases hpc : p.1 ∈ C <;> simp [U, V, hpc, and_assoc]

theorem elementarySets_eq_supClosure :
    elementarySets (α := α) (β := β) = supClosure measurableRectangles := by
  ext E
  exact measurableRectangles_semiring.mem_supClosure_iff.symm

theorem elementarySets_isSetAlgebra :
    IsSetAlgebra (elementarySets (α := α) (β := β)) := by
  rw [elementarySets_eq_supClosure]
  have hR := measurableRectangles_semiring (α := α) (β := β)
  have hu : (Set.univ : Set (α × β)) ∈ supClosure measurableRectangles := by
    apply subset_supClosure
    exact ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, Set.univ_prod_univ⟩
  exact { hR.isSetRing_supClosure with
    compl_mem := fun {_} hs => by simpa only [← compl_eq_univ_sdiff] using hR.isSetRing_supClosure.sdiff_mem hu hs }

theorem rectangle_mem_elementary {E : Set (α × β)} (hE : E ∈ measurableRectangles) :
    E ∈ elementarySets := by
  rw [elementarySets_eq_supClosure]
  exact subset_supClosure hE

theorem elementary_measurable {E : Set (α × β)} (hE : E ∈ elementarySets) :
    MeasurableSet E := by
  obtain ⟨P, hP⟩ := hE
  rw [← P.sup_parts, Finset.sup_id_set_eq_sUnion]
  apply MeasurableSet.sUnion P.parts.finite_toSet.countable
  intro R hR
  obtain ⟨A, hA, B, hB, rfl⟩ := hP hR
  exact hA.prod hB

theorem generateFrom_elementarySets :
    MeasurableSpace.generateFrom (elementarySets (α := α) (β := β)) = (inferInstance : MeasurableSpace (α × β)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le (fun _ hE => elementary_measurable hE)
  · rw [← rectangleProductSpace_eq]
    exact MeasurableSpace.generateFrom_mono (fun _ h => rectangle_mem_elementary h)

/-- 8.3: the product measurable sets form the smallest monotone class containing
all elementary sets (finite disjoint unions of measurable rectangles). -/
theorem product_measurable_smallest_monotone_class :
    IsLeast {M : Set (Set (α × β)) | IsMonotoneClass M ∧ elementarySets ⊆ M}
      {E : Set (α × β) | MeasurableSet E} := by
  constructor
  · constructor
    · constructor
      · intro s _ hs
        change ∀ n, MeasurableSet (s n) at hs
        change MeasurableSet (⋃ n, s n)
        exact MeasurableSet.iUnion hs
      · intro s _ hs
        change ∀ n, MeasurableSet (s n) at hs
        change MeasurableSet (⋂ n, s n)
        exact MeasurableSet.iInter hs
    · exact fun _ hE => elementary_measurable hE
  · rintro M ⟨hM, hE⟩ E h
    apply MonotoneClosure.minimal hM hE
    apply (MonotoneClosure.iff_measurableSet elementarySets_isSetAlgebra).mpr
    rw [generateFrom_elementarySets]
    exact h


end RudinRCA.Chapter08
