module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
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
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Rudin, Real and Complex Analysis, Chapter 8

The printed nodes and their statement mapping are recorded in `SCOPING-D.md`.
Positive integrals take values in `ℝ≥0∞`. Completed measurable spaces are represented
explicitly by `NullMeasurableSpace`, so completion is not conflated with Borel measure.
-/

@[expose] public section

/- Ch08FirstEight -/
noncomputable section

open Set MeasureTheory
open scoped ENNReal

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


namespace RudinRCA.Chapter08

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- 8.2: every section of a product-measurable set is measurable. -/
theorem measurable_sections {E : Set (X × Y)} (hE : MeasurableSet E) :
    (∀ x, MeasurableSet {y | (x, y) ∈ E}) ∧
    (∀ y, MeasurableSet {x | (x, y) ∈ E}) :=
  ⟨fun _ => measurable_prodMk_left hE, fun _ => measurable_prodMk_right hE⟩

/-- 8.4: the function on Y obtained by fixing x. -/
def functionSectionX (f : X × Y → Z) (x : X) : Y → Z := fun y => f (x, y)

/-- 8.4: the function on X obtained by fixing y. -/
def functionSectionY (f : X × Y → Z) (y : Y) : X → Z := fun x => f (x, y)

/-- 8.5(a,b), for an arbitrary measurable target. -/
theorem measurable_function_sections [MeasurableSpace Z] {f : X × Y → Z}
    (hf : Measurable f) :
    (∀ x, Measurable (functionSectionX f x)) ∧
    (∀ y, Measurable (functionSectionY f y)) :=
  ⟨fun _ => hf.comp measurable_prodMk_left, fun _ => hf.comp measurable_prodMk_right⟩

variable (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- 8.6: section measures are measurable and have equal integrals. -/
theorem section_measures {Q : Set (X × Y)} (hQ : MeasurableSet Q) :
    Measurable (fun x => ν {y | (x, y) ∈ Q}) ∧
    Measurable (fun y => μ {x | (x, y) ∈ Q}) ∧
    (∫⁻ x, ν {y | (x, y) ∈ Q} ∂μ) = ∫⁻ y, μ {x | (x, y) ∈ Q} ∂ν := by
  refine ⟨measurable_measure_prodMk_left hQ, measurable_measure_prodMk_right hQ, ?_⟩
  exact (Measure.prod_apply hQ).symm.trans (Measure.prod_apply_symm hQ)

/-- 8.7: the product measure is the integral of either section measure. -/
theorem product_measure_definition {Q : Set (X × Y)} (hQ : MeasurableSet Q) :
    (μ.prod ν) Q = (∫⁻ x, ν {y | (x, y) ∈ Q} ∂μ) ∧
    (μ.prod ν) Q = ∫⁻ y, μ {x | (x, y) ∈ Q} ∂ν :=
  ⟨Measure.prod_apply hQ, Measure.prod_apply_symm hQ⟩

/-- The countable additivity assertion in 8.7. -/
theorem product_measure_countably_additive (Q : ℕ → Set (X × Y))
    (hQ : ∀ n, MeasurableSet (Q n)) (hdis : Pairwise (fun i j => Disjoint (Q i) (Q j))) :
    (μ.prod ν) (⋃ n, Q n) = ∑' n, (μ.prod ν) (Q n) :=
  measure_iUnion hdis hQ

/-- The sigma-finiteness assertion in 8.7. -/
theorem product_measure_sigmaFinite : SigmaFinite (μ.prod ν) := inferInstance

/-- 8.8(a), Tonelli, including the measurability of both inner integrals. -/
theorem tonelli {f : X × Y → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun x => ∫⁻ y, f (x, y) ∂ν) ∧
    Measurable (fun y => ∫⁻ x, f (x, y) ∂μ) ∧
    (∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ) = ∫⁻ z, f z ∂μ.prod ν ∧
    (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  ⟨hf.lintegral_prod_right', hf.lintegral_prod_left',
    (lintegral_prod f hf.aemeasurable).symm, lintegral_prod_symm f hf.aemeasurable⟩

/-- 8.8(b): finiteness of the iterated integral of the modulus implies L1 integrability. -/
theorem integrable_of_iterated_norm {f : X × Y → ℂ} (hf : Measurable f)
    (hfin : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂ν ∂μ) < ∞) :
    Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hf.enorm.aemeasurable]
  exact hfin

/-- 8.8(c), Fubini: integrable sections almost everywhere, integrable inner integrals,
and both orders equal the product integral. -/
theorem fubini {f : X × Y → ℂ} (hf : Integrable f (μ.prod ν)) :
    (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ ∧
    Integrable (fun y => ∫ x, f (x, y) ∂μ) ν ∧
    (∫ x, ∫ y, f (x, y) ∂ν ∂μ) = ∫ z, f z ∂μ.prod ν ∧
    (∫ z, f z ∂μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
  ⟨hf.prod_right_ae, hf.prod_left_ae, hf.integral_prod_left, hf.integral_prod_right,
    (integral_prod f hf).symm, integral_prod_symm f hf⟩


end RudinRCA.Chapter08
end

/- Ch08Completion -/
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

/- Ch08FubiniCompletion -/
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

/- Ch08CounterexampleCount -/
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

/- Ch08ProductExample -/
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

/- Ch08Vitali -/
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

/- Ch08Sierpinski -/
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

/-- The sections in Sierpinski's construction are Borel sets in the literal unit
interval, which is stronger than measurability in its Lebesgue completion. This
companion retains the Borel statement explicitly alongside the completed endpoint. -/
theorem unit_square_sierpinski_borel_sections_under_CH
    (hCH : Cardinal.continuum = (Cardinal.aleph 1 : Cardinal.{0})) :
    ∃ Q : Set (SierpinskiInterval × SierpinskiInterval),
      (∀ x : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {y | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {y | (x, y) ∈ Q} = 1) ∧
      (∀ y : SierpinskiInterval,
        @MeasurableSet SierpinskiInterval (borel SierpinskiInterval) {x | (x, y) ∈ Q} ∧
          sierpinskiIntervalMeasure {x | (x, y) ∈ Q} = 0) ∧
      (∫⁻ x, sierpinskiIntervalMeasure {y | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 1 ∧
      (∫⁻ y, sierpinskiIntervalMeasure {x | (x, y) ∈ Q} ∂sierpinskiIntervalMeasure) = 0 ∧
      ¬ MeasurableSet Q := by
  obtain ⟨⟨j⟩, hw, hc⟩ := ch_unitInterval_wellOrder hCH
  have H := sierpinski_counterexample sierpinskiIntervalMeasure j hw hc
  have hb : (inferInstance : MeasurableSpace SierpinskiInterval) = borel SierpinskiInterval :=
    BorelSpace.measurable_eq
  refine ⟨sierpinskiSet j, ?_, ?_, H.2.2.1, H.2.2.2.1, H.2.2.2.2⟩
  · intro x
    refine ⟨?_, (H.1 x).2⟩
    rw [← hb]
    exact (H.1 x).1
  · intro y
    refine ⟨?_, (H.2.1 y).2⟩
    rw [← hb]
    exact (H.2.1 y).1

end RudinRCA.Chapter08
end

/- Ch08PowersetCount -/
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

/- Ch08BumpExample -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace RudinRCA.Chapter08

/-- The subdivisions in 8.9(a), indexed from zero. -/
noncomputable def bumpDivision (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

@[simp] lemma bumpDivision_zero : bumpDivision 0 = 0 := by
  norm_num [bumpDivision]

lemma bumpDivision_strictMono : StrictMono bumpDivision := by
  intro m n hmn
  have h := pow_right_strictAnti₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hmn
  exact sub_lt_sub_left h 1

lemma bumpDivision_lt_one (n : ℕ) : bumpDivision n < 1 := by
  have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
  dsimp [bumpDivision]
  linarith

lemma bumpDivision_nonneg (n : ℕ) : 0 ≤ bumpDivision n := by
  have h := bumpDivision_strictMono.monotone (Nat.zero_le n)
  simpa [bumpDivision] using h

lemma bumpDivision_tendsto : Tendsto bumpDivision atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  change Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ n) atTop (𝓝 1)
  simpa only [sub_zero] using h

noncomputable def rudinBump (n : ℕ) :
    ContDiffBump ((bumpDivision n + bumpDivision (n + 1)) / 2) where
  rIn := (bumpDivision (n + 1) - bumpDivision n) / 8
  rOut := (bumpDivision (n + 1) - bumpDivision n) / 4
  rIn_pos := by
    have h := bumpDivision_strictMono (Nat.lt_succ_self n)
    linarith
  rIn_lt_rOut := by
    have h := bumpDivision_strictMono (Nat.lt_succ_self n)
    linarith

/-- A concrete choice of Rudin's continuous bumps, with integral one. -/
noncomputable def rudinBumpFunction (n : ℕ) : ℝ → ℝ :=
  (rudinBump n).normed volume

lemma rudinBumpFunction_continuous (n : ℕ) : Continuous (rudinBumpFunction n) :=
  (rudinBump n).continuous_normed

lemma rudinBumpFunction_support (n : ℕ) :
    Function.support (rudinBumpFunction n) ⊆ Ioo (bumpDivision n) (bumpDivision (n + 1)) := by
  intro x hx
  rw [rudinBumpFunction, (rudinBump n).support_normed_eq] at hx
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
  have hd := bumpDivision_strictMono (Nat.lt_succ_self n)
  change -( (bumpDivision (n + 1) - bumpDivision n) / 4) <
      x - (bumpDivision n + bumpDivision (n + 1)) / 2 ∧
    x - (bumpDivision n + bumpDivision (n + 1)) / 2 <
      (bumpDivision (n + 1) - bumpDivision n) / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

/-- The topological support also lies strictly inside its assigned interval. -/
lemma rudinBumpFunction_tsupport (n : ℕ) :
    tsupport (rudinBumpFunction n) ⊆ Ioo (bumpDivision n) (bumpDivision (n + 1)) := by
  intro x hx
  rw [rudinBumpFunction, (rudinBump n).tsupport_normed_eq] at hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have hd := bumpDivision_strictMono (Nat.lt_succ_self n)
  change -((bumpDivision (n + 1) - bumpDivision n) / 4) ≤
      x - (bumpDivision n + bumpDivision (n + 1)) / 2 ∧
    x - (bumpDivision n + bumpDivision (n + 1)) / 2 ≤
      (bumpDivision (n + 1) - bumpDivision n) / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

lemma rudinBumpFunction_zero_of_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (bumpDivision n) (bumpDivision (n + 1))) :
    rudinBumpFunction n x = 0 := by
  by_contra hn
  exact hx (rudinBumpFunction_support n hn)

lemma rudinBumpFunction_pairwise (x : ℝ) {n m : ℕ}
    (hn : rudinBumpFunction n x ≠ 0) (hm : rudinBumpFunction m x ≠ 0) : n = m := by
  have hnx := rudinBumpFunction_support n hn
  have hmx := rudinBumpFunction_support m hm
  rcases lt_trichotomy n m with h | h | h
  · have hd := bumpDivision_strictMono.monotone (Nat.succ_le_of_lt h)
    exact False.elim (not_lt_of_ge hd (hmx.1.trans hnx.2))
  · exact h
  · have hd := bumpDivision_strictMono.monotone (Nat.succ_le_of_lt h)
    exact False.elim (not_lt_of_ge hd (hnx.1.trans hmx.2))

lemma rudinBumpFunction_local_cutoff {x : ℝ} (hx : x ≠ 1) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, rudinBumpFunction n y = 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (bumpDivision_tendsto.eventually (eventually_gt_nhds hx))
    refine ⟨N, ?_⟩
    filter_upwards [eventually_lt_nhds (hN N le_rfl)] with y hy
    intro n hn
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    have hd := bumpDivision_strictMono.monotone hn
    exact (not_lt_of_ge hd) (hmem.1.trans hy)
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_gt_nhds hx] with y hy
    intro n _
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    exact (not_lt_of_ge hy.le) (hmem.2.trans (bumpDivision_lt_one (n + 1)))

lemma rudinBumpFunction_cutoff (x : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, rudinBumpFunction n x = 0 := by
  by_cases hx : x = 1
  · subst x
    refine ⟨0, fun n _ => rudinBumpFunction_zero_of_outside n ?_⟩
    intro hmem
    exact (not_lt_of_ge (bumpDivision_lt_one (n + 1)).le) hmem.2
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hx
    exact ⟨N, Filter.Eventually.self_of_nhds hN⟩

noncomputable abbrev bumpIntervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

lemma rudinBumpFunction_integrable (n : ℕ) :
    Integrable (rudinBumpFunction n) bumpIntervalMeasure :=
  (rudinBump n).integrable_normed.restrict

lemma rudinBumpFunction_integral (n : ℕ) :
    (∫ x, rudinBumpFunction n x ∂bumpIntervalMeasure) = 1 := by
  have h : (∫ x, rudinBumpFunction n x ∂bumpIntervalMeasure) =
      ∫ x, rudinBumpFunction n x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply rudinBumpFunction_zero_of_outside
    intro hmem
    exact hx ⟨(bumpDivision_nonneg n).trans hmem.1.le,
      hmem.2.le.trans (bumpDivision_lt_one (n + 1)).le⟩
  rw [h]
  exact (rudinBump n).integral_normed

/-- Rudin's exact series in 8.9(a), with the first bump indexed by zero. -/
noncomputable def rudinBumpSeries (x y : ℝ) : ℝ :=
  ∑' n : ℕ, (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y


/-- There is at most one nonzero summand at every point, as observed in 8.9(a). -/
lemma rudinBumpSeries_unique_nonzero_term (x y : ℝ) {n m : ℕ}
    (hn : (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y ≠ 0)
    (hm : (rudinBumpFunction m x - rudinBumpFunction (m + 1) x) * rudinBumpFunction m y ≠ 0) :
    n = m :=
  rudinBumpFunction_pairwise y (mul_ne_zero_iff.mp hn).2 (mul_ne_zero_iff.mp hm).2

lemma rudinBumpSeries_measurable : Measurable (Function.uncurry rudinBumpSeries) := by
  apply Measurable.tsum
  intro n
  exact (((rudinBumpFunction_continuous n).measurable.comp measurable_fst).sub
    ((rudinBumpFunction_continuous (n + 1)).measurable.comp measurable_fst)).mul
    ((rudinBumpFunction_continuous n).measurable.comp measurable_snd)

lemma rudinBumpSeries_finite_left (x : ℝ) :
    ∃ N : ℕ, ∀ y, rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff x
  refine ⟨N, fun y => tsum_eq_sum (fun n hn => ?_)⟩
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  rw [hN n hn', hN (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]

lemma rudinBumpSeries_finite_right (y : ℝ) :
    ∃ N : ℕ, ∀ x, rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff y
  refine ⟨N, fun x => tsum_eq_sum (fun n hn => ?_)⟩
  rw [hN n (Nat.le_of_not_gt (by simpa using hn)), mul_zero]

lemma rudinBumpSeries_sections_integrable :
    (∀ x, Integrable (rudinBumpSeries x) bumpIntervalMeasure) ∧
    (∀ y, Integrable (fun x => rudinBumpSeries x y) bumpIntervalMeasure) := by
  constructor
  · intro x
    obtain ⟨N, hN⟩ := rudinBumpSeries_finite_left x
    change Integrable (fun y => rudinBumpSeries x y) bumpIntervalMeasure
    simp_rw [hN]
    exact integrable_finsetSum _ (fun n _ => (rudinBumpFunction_integrable n).const_mul _)
  · intro y
    obtain ⟨N, hN⟩ := rudinBumpSeries_finite_right y
    simp_rw [hN]
    exact integrable_finsetSum _ (fun n _ =>
      ((rudinBumpFunction_integrable n).sub (rudinBumpFunction_integrable (n + 1))).mul_const _)

lemma rudinBumpSeries_integral_right (x : ℝ) :
    (∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure) = rudinBumpFunction 0 x := by
  obtain ⟨N, hN⟩ := rudinBumpFunction_cutoff x
  have heq (y : ℝ) : rudinBumpSeries x y =
      ∑ n ∈ Finset.range N,
        (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y := by
    apply tsum_eq_sum
    intro n hn
    have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [hN n hn', hN (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun n _ => (rudinBumpFunction_integrable n).const_mul _)]
  simp_rw [integral_const_mul, rudinBumpFunction_integral, mul_one]
  have htel (M : ℕ) :
      (∑ n ∈ Finset.range M, (rudinBumpFunction n x - rudinBumpFunction (n + 1) x)) =
      rudinBumpFunction 0 x - rudinBumpFunction M x := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel, hN N le_rfl, sub_zero]

lemma rudinBumpSeries_integral_left (y : ℝ) :
    (∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure) = 0 := by
  obtain ⟨N, hN⟩ := rudinBumpSeries_finite_right y
  simp_rw [hN]
  rw [integral_finsetSum (Finset.range N)
    (f := fun n x => (rudinBumpFunction n x - rudinBumpFunction (n + 1) x) * rudinBumpFunction n y)
    (fun n _ => ((rudinBumpFunction_integrable n).sub
      (rudinBumpFunction_integrable (n + 1))).mul_const (rudinBumpFunction n y))]
  simp_rw [integral_mul_const, integral_sub (rudinBumpFunction_integrable _)
    (rudinBumpFunction_integrable _), rudinBumpFunction_integral, sub_self, zero_mul]
  exact Finset.sum_const_zero

lemma rudinBumpSeries_continuousAt {p : ℝ × ℝ} (hp : p ≠ (1, 1)) :
    ContinuousAt (Function.uncurry rudinBumpSeries) p := by
  have hp' : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
    by_contra h
    push Not at h
    exact hp (Prod.ext h.1 h.2)
  rcases hp' with hx | hy
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hx
    have hc : Continuous (fun q : ℝ × ℝ => ∑ n ∈ Finset.range N,
        (rudinBumpFunction n q.1 - rudinBumpFunction (n + 1) q.1) * rudinBumpFunction n q.2) := by
      apply continuous_finsetSum
      intro n _
      exact (((rudinBumpFunction_continuous n).comp continuous_fst).sub
        ((rudinBumpFunction_continuous (n + 1)).comp continuous_fst)).mul
        ((rudinBumpFunction_continuous n).comp continuous_snd)
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually hN] with q hq
    apply tsum_eq_sum
    intro n hn
    have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [hq n hn', hq (n + 1) (hn'.trans (Nat.le_succ n)), sub_self, zero_mul]
  · obtain ⟨N, hN⟩ := rudinBumpFunction_local_cutoff hy
    have hc : Continuous (fun q : ℝ × ℝ => ∑ n ∈ Finset.range N,
        (rudinBumpFunction n q.1 - rudinBumpFunction (n + 1) q.1) * rudinBumpFunction n q.2) := by
      apply continuous_finsetSum
      intro n _
      exact (((rudinBumpFunction_continuous n).comp continuous_fst).sub
        ((rudinBumpFunction_continuous (n + 1)).comp continuous_fst)).mul
        ((rudinBumpFunction_continuous n).comp continuous_snd)
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually hN] with q hq
    apply tsum_eq_sum
    intro n hn
    rw [hq n (Nat.le_of_not_gt (by simpa using hn)), mul_zero]

/-- 8.9(a): both iterated integrals exist and differ, although the exact printed
bump series is continuous away from the corner. Its absolute double integral is infinite. -/
theorem rudin_bump_counterexample :
    (∀ x, Integrable (rudinBumpSeries x) bumpIntervalMeasure) ∧
    (∀ y, Integrable (fun x => rudinBumpSeries x y) bumpIntervalMeasure) ∧
    Integrable (fun x => ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure) bumpIntervalMeasure ∧
    Integrable (fun y => ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure) bumpIntervalMeasure ∧
    (∫ x, ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 1 ∧
    (∫ y, ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 0 ∧
    (∀ p : ℝ × ℝ, p ≠ (1, 1) → ContinuousAt (Function.uncurry rudinBumpSeries) p) ∧
    (∫⁻ p, ‖rudinBumpSeries p.1 p.2‖ₑ
      ∂bumpIntervalMeasure.prod bumpIntervalMeasure) = ∞ := by
  have hi : (∫ x, ∫ y, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 1 := by
    simp_rw [rudinBumpSeries_integral_right]
    exact rudinBumpFunction_integral 0
  have hj : (∫ y, ∫ x, rudinBumpSeries x y ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = 0 := by
    simp_rw [rudinBumpSeries_integral_left, integral_zero]
  refine ⟨rudinBumpSeries_sections_integrable.1, rudinBumpSeries_sections_integrable.2,
    ?_, ?_, hi, hj, fun _ hp => rudinBumpSeries_continuousAt hp, ?_⟩
  · simp_rw [rudinBumpSeries_integral_right]
    exact rudinBumpFunction_integrable 0
  · simp_rw [rudinBumpSeries_integral_left]
    exact integrable_zero _ _ _
  · by_contra h
    have hint : Integrable (Function.uncurry rudinBumpSeries)
        (bumpIntervalMeasure.prod bumpIntervalMeasure) :=
      ⟨rudinBumpSeries_measurable.aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.mpr (lt_top_iff_ne_top.mpr h)⟩
    have he := integral_integral_swap hint
    rw [hi, hj] at he
    exact one_ne_zero he

/-- The divergent iterated absolute integral displayed in 8.9(a). -/
theorem rudin_bump_absolute_iterated :
    (∫⁻ x, ∫⁻ y, ‖rudinBumpSeries x y‖ₑ ∂bumpIntervalMeasure ∂bumpIntervalMeasure) = ∞ := by
  rw [← lintegral_prod (fun p : ℝ × ℝ => ‖rudinBumpSeries p.1 p.2‖ₑ)
    rudinBumpSeries_measurable.enorm.aemeasurable]
  exact rudin_bump_counterexample.2.2.2.2.2.2.2

/-- The exceptional corner really is a discontinuity; all other points are covered above. -/
theorem rudin_bump_not_continuousAt_corner :
    ¬ ContinuousAt (Function.uncurry rudinBumpSeries) (1, 1) := by
  intro hc
  have hcont : Continuous (Function.uncurry rudinBumpSeries) :=
    continuous_iff_continuousAt.mpr (fun p => by
      by_cases hp : p = (1, 1)
      · simpa [hp] using hc
      · exact rudinBumpSeries_continuousAt hp)
  have hi : IntegrableOn (Function.uncurry rudinBumpSeries)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ((volume : Measure ℝ).prod volume) :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  change Integrable (Function.uncurry rudinBumpSeries)
    (((volume : Measure ℝ).prod volume).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) at hi
  rw [← Measure.prod_restrict] at hi
  have h := integral_integral_swap hi
  have h₁ := rudin_bump_counterexample.2.2.2.2.1
  have h₀ := rudin_bump_counterexample.2.2.2.2.2.1
  rw [h₁, h₀] at h
  exact one_ne_zero h

end RudinRCA.Chapter08
end

/- Ch08Later -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution

namespace RudinRCA.Chapter08

/-- Rudin's convolution convention, including the standard zero choice on the null set
where the Bochner integral is not defined. -/
noncomputable def rudinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g y

lemma rudinConvolution_eq (f g : ℝ → ℂ) :
    rudinConvolution f g = convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  exact (convolution_mul_swap (f := f) (g := g) (x := x)).symm

/-- 8.14: absolute convergence for almost every point, integrability of the convolution,
and the sharp L¹ norm estimate. The functions are arbitrary Lebesgue-a.e. measurable
representatives, not just Borel representatives. -/
theorem theorem_8_14 {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∀ᵐ x : ℝ, Integrable (fun y => f (x - y) * g y)) ∧
    Integrable (rudinConvolution f g) ∧
    (∫ x, ‖rudinConvolution f g x‖) ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hex := hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hg
  have hi := hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hex] with x hx
    exact hx.integrable_swap
  · simpa only [rudinConvolution_eq] using hi
  · rw [rudinConvolution_eq]
    calc
      (∫ x, ‖convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume x‖) ≤
          ∫ x, convolution (fun t => ‖f t‖) (fun t => ‖g t‖)
            (ContinuousLinearMap.mul ℝ ℝ) volume x := by
        apply integral_mono hi.norm
          (hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm)
        intro x
        simp only [convolution_mul]
        simpa only [norm_mul] using norm_integral_le_integral_norm (fun t => f t * g (x - t))
      _ = (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
        exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

/-- 8.15: Rudin's distribution function, defined at every real threshold.
Only its restriction to the nonnegative real line is used in the book. -/
noncomputable def distributionFunction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  μ {x | ENNReal.ofReal t < f x}

/-- 8.15: the distribution function is nonincreasing. -/
theorem distributionFunction_antitone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Antitone (distributionFunction μ f) := by
  intro s t hst
  exact measure_mono fun x hx => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- 8.15: the distribution function is Borel measurable. -/
theorem distributionFunction_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : Measurable (distributionFunction μ f) :=
  (distributionFunction_antitone μ f).measurable

-- The following finite-valued cases are support lemmas only; they do NOT complete
-- Rudin 8.15/8.16, where f may take the value ∞.
theorem layerCake_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Ioi 0, μ {x | t < f x} :=
  lintegral_eq_lintegral_meas_lt μ hfn hf

theorem layerCake_integratedWeight_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} {g : ℝ → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hg : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (hgn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ x, ENNReal.ofReal (∫ t in 0..f x, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {x | t < f x} * ENNReal.ofReal (g t) :=
  lintegral_comp_eq_lintegral_meas_lt_mul μ hfn hf hg hgn


end RudinRCA.Chapter08
end

/- Ch08LayerCake -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

lemma volume_positive_lt_ennreal (a : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = a := by
  by_cases ha : a = ∞
  · simp only [ha, ENNReal.ofReal_lt_top, and_true]
    change volume (Ioi (0 : ℝ)) = ∞
    exact Real.volume_Ioi
  · have hs : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < a} = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨ht, hat⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat⟩
    rw [hs, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- Cavalieri's formula for a genuinely extended-valued function. -/
theorem layerCake_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} := by
  let F : X × ℝ → ℝ≥0∞ := fun p =>
    {q : X × ℝ | ENNReal.ofReal q.2 < f q.1}.indicator (fun _ => 1) p
  have hset : MeasurableSet {q : X × ℝ | ENNReal.ofReal q.2 < f q.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have hF : Measurable F := measurable_const.indicator hset
  have hx (x : X) : ∫⁻ t in Ioi 0, F (x, t) = f x := by
    rw [show (fun t => F (x, t)) = {t : ℝ | ENNReal.ofReal t < f x}.indicator (fun _ => 1) by rfl]
    rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
    rw [Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < f x} ∩ Ioi 0 =
        {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi]
      exact and_comm
    rw [hs]
    exact volume_positive_lt_ennreal (f x)
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ :=
      lintegral_congr fun x => (hx x).symm
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      change (∫⁻ x, {x | ENNReal.ofReal t < f x}.indicator (fun _ => 1) x ∂μ) = _
      rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
      simp

end RudinRCA.Chapter08
end

/- Ch08Phi -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Weighted Cavalieri formula, retaining infinite values of `f`. -/
theorem layerCake_ennreal_weight {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, ∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < f x}.indicator g t ∂volume ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * g t := by
  let F : X × ℝ → ℝ≥0∞ :=
    {q : X × ℝ | ENNReal.ofReal q.2 < f q.1}.indicator (fun q => g q.2)
  have hset : MeasurableSet {q : X × ℝ | ENNReal.ofReal q.2 < f q.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have hF : Measurable F := (hg.comp measurable_snd).indicator hset
  change (∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ) = _
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ :=
      lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi 0))
        (f := fun x t => F (x, t)) hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      change (∫⁻ x, {x | ENNReal.ofReal t < f x}.indicator (fun _ => g t) x ∂μ) = _
      rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
      simp [mul_comm]

lemma lintegral_deriv_Ioo {φ : ℝ → ℝ} (hm : Monotone φ) (h0 : φ 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) (ha : AbsolutelyContinuousOnInterval φ 0 T) :
    ∫⁻ t in Ioo 0 T, ENNReal.ofReal (deriv φ t) = ENNReal.ofReal (φ T) := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo 0 T =ᵐ[volume] Ioc 0 T)]
  rw [← ofReal_integral_eq_lintegral_ofReal ha.intervalIntegrable_deriv.1
    (Eventually.of_forall fun _ => hm.deriv_nonneg)]
  rw [← intervalIntegral.integral_of_le hT, ha.integral_deriv_eq_sub, h0, sub_zero]

/-- Extending a nonnegative real function continuously to a possibly infinite value at infinity. -/
noncomputable def extendedNonnegative (φ : ℝ → ℝ) (φInfinity : ℝ≥0∞) (a : ℝ≥0∞) : ℝ≥0∞ :=
  if a = ∞ then φInfinity else ENNReal.ofReal (φ a.toReal)

lemma extendedNonnegative_eq_integral {φ : ℝ → ℝ} {φInfinity : ℝ≥0∞}
    (hm : Monotone φ) (h0 : φ 0 = 0)
    (hac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval φ 0 T)
    (hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 φInfinity))
    (a : ℝ≥0∞) :
    extendedNonnegative φ φInfinity a =
      ∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < a}.indicator
        (fun t => ENNReal.ofReal (deriv φ t)) t := by
  by_cases ha : a = ∞
  · subst a
    simp only [extendedNonnegative, if_pos rfl, ENNReal.ofReal_lt_top,
      setOf_true, indicator_univ]
    let ν : Measure ℝ := volume.restrict (Ioi 0)
    have hc : AECover ν atTop (fun n : ℕ => Iio (n : ℝ)) :=
      aecover_Iio (μ := ν) tendsto_natCast_atTop_atTop
    have he (n : ℕ) :
        ∫⁻ t in Iio (n : ℝ), ENNReal.ofReal (deriv φ t) ∂ν =
          ENNReal.ofReal (φ n) := by
      rw [show ν = volume.restrict (Ioi 0) from rfl,
        Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio (n : ℝ) ∩ Ioi 0 = Ioo 0 (n : ℝ) := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        exact and_comm
      rw [hs]
      exact lintegral_deriv_Ioo hm h0 (Nat.cast_nonneg n) (hac n (Nat.cast_nonneg n))
    exact (hc.lintegral_eq_of_tendsto φInfinity
      (ENNReal.measurable_ofReal.comp (measurable_deriv φ)).aemeasurable
      (by simpa only [Function.comp_def, he] using hlim.comp tendsto_natCast_atTop_atTop)).symm
  · rw [extendedNonnegative, if_neg ha]
    rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_restrict (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨hat, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat, ht⟩
    rw [hs]
    exact (lintegral_deriv_Ioo hm h0 ENNReal.toReal_nonneg
      (hac _ ENNReal.toReal_nonneg)).symm

/-- 8.16, in the real-coordinate representation of the finite part of φ. -/
theorem layerCake_locallyAbsolutelyContinuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {φ : ℝ → ℝ} {φInfinity : ℝ≥0∞}
    (hm : Monotone φ) (h0 : φ 0 = 0)
    (hac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval φ 0 T)
    (hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 φInfinity)) :
    (∫⁻ x, extendedNonnegative φ φInfinity (f x) ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (deriv φ t) := by
  simp_rw [extendedNonnegative_eq_integral hm h0 hac hlim]
  exact layerCake_ennreal_weight μ hf (ENNReal.measurable_ofReal.comp (measurable_deriv φ))

/-- 8.16: full extended-valued formulation. Local absolute continuity is expressed
in real coordinates on each finite interval. Its finite-value condition records that
absolutely continuous functions there are real valued, as in the printed definition. -/
theorem theorem_8_16 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {Φ : ℝ≥0∞ → ℝ≥0∞} (hm : Monotone Φ) (h0 : Φ 0 = 0)
    (hfinite : ∀ t : ℝ, Φ (ENNReal.ofReal t) ≠ ∞)
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval
      (fun t => (Φ (ENNReal.ofReal t)).toReal) 0 T)
    (hlim : Tendsto (fun t : ℝ => Φ (ENNReal.ofReal t)) atTop (𝓝 (Φ ∞))) :
    (∫⁻ x, Φ (f x) ∂μ) =
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} *
        ENNReal.ofReal (deriv (fun t => (Φ (ENNReal.ofReal t)).toReal) t) := by
  let φ : ℝ → ℝ := fun t => (Φ (ENNReal.ofReal t)).toReal
  have hm' : Monotone φ := fun s t hst =>
    ENNReal.toReal_mono (hfinite t) (hm (ENNReal.ofReal_le_ofReal hst))
  have h0' : φ 0 = 0 := by simp [φ, h0]
  have hlim' : Tendsto (fun t : ℝ => ENNReal.ofReal (φ t)) atTop (𝓝 (Φ ∞)) := by
    simpa only [φ, ENNReal.ofReal_toReal (hfinite _)] using hlim
  have he (a : ℝ≥0∞) : extendedNonnegative φ (Φ ∞) a = Φ a := by
    by_cases ha : a = ∞
    · simp [extendedNonnegative, ha]
    · have hfa : Φ a ≠ ∞ := by
        simpa only [ENNReal.ofReal_toReal ha] using hfinite a.toReal
      simp [extendedNonnegative, ha, φ, ENNReal.ofReal_toReal ha,
        ENNReal.ofReal_toReal hfa]
  simpa only [he] using layerCake_locallyAbsolutelyContinuous μ hf hm' h0' hac hlim'

end RudinRCA.Chapter08
end

/- Ch08Maximal -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- The centered Hardy–Littlewood maximal function, using all positive radii.
For Euclidean space and Lebesgue measure this is Rudin's maximal function of `|f|`. -/
noncomputable def maximalFunction {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r)

/-- 8.17's L∞ estimate in the stronger pointwise form. The concrete weak (1,1)
estimate is proved separately by the covering argument. -/
theorem maximalFunction_le_essSup {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (x : X) :
    maximalFunction μ f x ≤ eLpNormEssSup f μ := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) / μ (ball x r) ≤
        (eLpNormEssSup f μ * μ (ball x r)) / μ (ball x r) := by
      apply ENNReal.div_le_div_right
      calc
        (∫⁻ y in ball x r, ‖f y‖ₑ ∂μ) ≤
            ∫⁻ _y in ball x r, eLpNormEssSup f μ ∂μ :=
          lintegral_mono_ae (ae_restrict_of_ae ae_le_eLpNormEssSup)
        _ = _ := by simp
    _ ≤ eLpNormEssSup f μ := by
      rw [div_eq_mul_inv, mul_assoc]
      exact (mul_le_mul_right (ENNReal.mul_inv_le_one _) _).trans_eq (mul_one _)

/-- The high part in Rudin's interpolation proof is integrable. This is support for
8.18, not the maximal-function theorem itself. -/
theorem integrable_highPart {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hfmeas : Measurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    Integrable ({x | ε < ‖f x‖ₑ}.indicator f) μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hs : MeasurableSet {x | ε < ‖f x‖ₑ} :=
    measurableSet_lt measurable_const hfmeas.enorm
  have hsub : {x | ε < ‖f x‖ₑ} ⊆ {x | ε ≤ ‖f x‖ₑ} := by
    intro x hx
    change ε < ‖f x‖ₑ at hx
    change ε ≤ ‖f x‖ₑ
    exact hx.le
  have hmeasure : μ {x | ε < ‖f x‖ₑ} < ∞ :=
    (measure_mono hsub).trans_lt
      (hf.meas_ge_lt_top'_enorm hp0 hptop hε (fun h => (hεtop h).elim))
  apply memLp_one_iff_integrable.mp
  exact (hf.indicator hs).mono_exponent_of_measure_support_ne_top
    (fun x hx => Set.indicator_of_notMem hx f) hmeasure.ne hp

end RudinRCA.Chapter08
end

/- Ch08WeakMaximal -/
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Covering-lemma part of the concrete maximal weak estimate. This is support only:
to apply it to an entire maximal-function level set, uniformly bound witness radii. -/
theorem weak_bound_of_bounded_ball_witnesses {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {s : Set X} {t C : ℝ≥0∞} {R : ℝ}
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r))
    (hwitness : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ) :
    t * μ s ≤ C * ∫⁻ x, f x ∂μ := by
  classical
  choose r hrpos hrbound hrint using fun x : s => hwitness x x.property
  obtain ⟨u, hu, hdis, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (univ : Set s) (fun x : s => (x : X)) r R (fun x _ => hrbound x) 5 (by norm_num)
  have huc : u.Countable := hdis.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun x _ => nonempty_ball.mpr (hrpos x))
  letI : Countable u := huc.to_subtype
  have hscover : s ⊆ ⋃ i : u, ball ((i : s) : X) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hinc⟩ := hcover ⟨x, hx⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hinc (mem_ball_self (hrpos ⟨x, hx⟩))⟩
  have hmeasure : μ s ≤ C * ∑' i : u, μ (ball ((i : s) : X) (r i)) := by
    calc
      μ s ≤ μ (⋃ i : u, ball ((i : s) : X) (5 * r i)) := measure_mono hscover
      _ ≤ ∑' i : u, μ (ball ((i : s) : X) (5 * r i)) := measure_iUnion_le _
      _ ≤ ∑' i : u, C * μ (ball ((i : s) : X) (r i)) :=
        ENNReal.tsum_le_tsum fun i => hgrowth i (r i) (hrpos i)
      _ = _ := ENNReal.tsum_mul_left
  have hiunion : (∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ) ≤
      ∫⁻ x, f x ∂μ := by
    rw [← lintegral_iUnion (fun _ => measurableSet_ball) (hdis.subtype _ _)]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    t * μ s ≤ t * (C * ∑' i : u, μ (ball ((i : s) : X) (r i))) :=
      mul_le_mul_right hmeasure t
    _ = C * ∑' i : u, t * μ (ball ((i : s) : X) (r i)) := by
      rw [ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ C * ∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ :=
      mul_le_mul_right (ENNReal.tsum_le_tsum fun i : u => hrint (i : s)) C
    _ ≤ C * ∫⁻ x, f x ∂μ := mul_le_mul_right hiunion C

/-- The Euclidean ball-growth constant required in the weak estimate. -/
theorem haar_ball_five_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (ball x (5 * r)) = ENNReal.ofReal (5 ^ Module.finrank ℝ E) * μ (ball x r) := by
  rw [μ.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 5) r,
    μ.addHaar_ball_center x r]

/-- Centered maximal operator for nonnegative extended-valued functions. -/
noncomputable def centeredMaximal {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r)

/-- The weak estimate follows by exhausting bounded-radius witnesses. The measure
continuity theorem used here works for arbitrary level sets, before measurability is known. -/
theorem centeredMaximal_weak_bound {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {t C : ℝ≥0∞}
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r)) :
    t * μ {x | t < centeredMaximal μ f x} ≤ C * ∫⁻ x, f x ∂μ := by
  let S : ℕ → Set X := fun n => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (n : ℝ) ∧
    t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ}
  have hSmono : Monotone S := by
    intro m n hmn x hx
    obtain ⟨r, hrpos, hrbound, hrint⟩ := hx
    exact ⟨r, hrpos, hrbound.trans (by exact_mod_cast hmn), hrint⟩
  have hSbound (n : ℕ) : t * μ (S n) ≤ C * ∫⁻ x, f x ∂μ :=
    weak_bound_of_bounded_ball_witnesses μ f hgrowth (fun _ hx => hx)
  have hcover : {x | t < centeredMaximal μ f x} ⊆ ⋃ n : ℕ, S n := by
    intro x hx
    change t < centeredMaximal μ f x at hx
    unfold centeredMaximal at hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hx
    obtain ⟨hrpos, hrmean⟩ := lt_iSup_iff.mp hr
    obtain ⟨n, hn⟩ := exists_nat_ge r
    refine mem_iUnion.mpr ⟨n, r, hrpos, hn, ?_⟩
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hballs x r hrpos).1)
      (Or.inl (hballs x r hrpos).2)).mp hrmean).le
  calc
    t * μ {x | t < centeredMaximal μ f x} ≤ t * μ (⋃ n : ℕ, S n) :=
      mul_le_mul_right (measure_mono hcover) t
    _ = ⨆ n : ℕ, t * μ (S n) := by rw [hSmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ C * ∫⁻ x, f x ∂μ := iSup_le hSbound

/-- Concrete weak (1,1) bound for the centered maximal operator on a finite-dimensional
real normed space, with explicit dimension-dependent constant 5^dim. -/
theorem centeredMaximal_weak_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    t * μ {x | t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, f x ∂μ := by
  apply centeredMaximal_weak_bound μ f
  · intro x r hr
    exact ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩
  · intro x r hr
    exact (haar_ball_five_growth μ x r).le

/-- All radii can be replaced by positive rational radii, because open balls are
unions of smaller rational-radius balls. -/
theorem centeredMaximal_eq_rational {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞) (x : X)
    (hballs : ∀ r : ℝ, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) :
    centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ)) := by
  let S := ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
    (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ))
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply ENNReal.div_le_of_le_mul
    let Q := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}
    have hu : ball x r = ⋃ q : Q, ball x ((q : ℚ) : ℝ) := by
      ext y
      constructor
      · intro hy
        change dist y x < r at hy
        obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hy
        exact mem_iUnion.mpr ⟨⟨q, lt_of_le_of_lt dist_nonneg hq₁, hq₂⟩, hq₁⟩
      · intro hy
        obtain ⟨q, hq⟩ := mem_iUnion.mp hy
        exact hq.trans q.property.2
    have hd : Directed (· ⊆ ·) (fun q : Q => ball x ((q : ℚ) : ℝ)) := by
      intro a b
      rcases le_total (a : ℚ) (b : ℚ) with hab | hba
      · exact ⟨b, ball_subset_ball (by exact_mod_cast hab), Subset.rfl⟩
      · exact ⟨a, Subset.rfl, ball_subset_ball (by exact_mod_cast hba)⟩
    have hi : (∫⁻ y in ball x r, f y ∂μ) =
        ⨆ q : Q, ∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ := by
      rw [hu, setLIntegral_iUnion_of_directed f hd]
    rw [hi]
    apply iSup_le
    intro q
    calc
      (∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ) ≤
          S * μ (ball x ((q : ℚ) : ℝ)) := by
        apply (ENNReal.div_le_iff_le_mul (Or.inl (hballs _ q.property.1).1)
          (Or.inl (hballs _ q.property.1).2)).mp
        exact le_iSup_of_le (q : ℚ) (le_iSup_of_le q.property.1 le_rfl)
      _ ≤ S * μ (ball x r) :=
        mul_le_mul_right (measure_mono (ball_subset_ball q.property.2.le)) S
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)

/-- Measurability of the mass of a ball with moving center. -/
theorem measurable_lintegral_ball {X : Type*} [PseudoMetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    Measurable (fun x => ∫⁻ y in ball x r, f y ∂μ) := by
  let F : X × X → ℝ≥0∞ :=
    {p : X × X | dist p.2 p.1 < r}.indicator (fun p => f p.2)
  have hF : Measurable F := (hf.comp measurable_snd).indicator
    (measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const)
  have hmeas : Measurable (fun x => ∫⁻ y, F (x, y) ∂μ) := hF.lintegral_prod_right'
  have he : (fun x => ∫⁻ y in ball x r, f y ∂μ) = (fun x => ∫⁻ y, F (x, y) ∂μ) := by
    funext x
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  rw [he]
  exact hmeas

/-- The centered maximal function is measurable for a measurable nonnegative input. -/
theorem centeredMaximal_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (centeredMaximal μ f) := by
  have he (x : E) : centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ)) := by
    rw [centeredMaximal_eq_rational μ f x
      (fun r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩)]
    simp_rw [μ.addHaar_ball_center x]
  have hefun : centeredMaximal μ f = (fun x =>
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ))) := funext he
  rw [hefun]
  exact Measurable.iSup fun q => Measurable.iSup fun _ =>
    (measurable_lintegral_ball μ hf (q : ℝ)).div measurable_const

/-- Adding a pointwise constant bound adds at most that constant to the maximal average. -/
theorem centeredMaximal_le_add_const {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x, f x ≤ g x + c)
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (x : X) : centeredMaximal μ f x ≤ centeredMaximal μ g x + c := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r) ≤
        (∫⁻ y in ball x r, g y + c ∂μ) / μ (ball x r) :=
      ENNReal.div_le_div_right (lintegral_mono h) _
    _ = (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r) + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const,
        Measure.restrict_apply_univ, ENNReal.add_div,
        ENNReal.mul_div_cancel_right (hballs x r hr).1 (hballs x r hr).2]
    _ ≤ centeredMaximal μ g x + c :=
      add_le_add (le_iSup_of_le r (le_iSup_of_le hr le_rfl)) le_rfl

/-- The truncation-distribution inequality at c=1/2, the main intermediate estimate
in Rudin's proof of 8.18. It is concrete, with no assumed weak-type hypothesis. -/
theorem centeredMaximal_truncation_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t / 2) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) *
        ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ := by
  let q := ENNReal.ofReal (t / 2)
  let g := {x | q < f x}.indicator f
  have hqsum : q + q = ENNReal.ofReal t := by
    change ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)]
    congr 1
    ring
  have hfg (x : E) : f x ≤ g x + q := by
    by_cases hx : q < f x
    · simp only [g, mem_setOf_eq, hx, indicator_of_mem]
      exact le_add_right le_rfl
    · simp only [g, mem_setOf_eq, hx, not_false_eq_true, indicator_of_notMem, zero_add]
      exact le_of_not_gt hx
  have hM (x : E) : centeredMaximal μ f x ≤ centeredMaximal μ g x + q :=
    centeredMaximal_le_add_const μ hfg
      (fun x r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩) x
  have hs : {x | ENNReal.ofReal t < centeredMaximal μ f x} ⊆
      {x | q < centeredMaximal μ g x} := by
    intro x hx
    by_contra hnot
    have hle := (hM x).trans (add_le_add (le_of_not_gt hnot) le_rfl)
    rw [hqsum] at hle
    exact (not_le_of_gt hx) hle
  calc
    q * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
        q * μ {x | q < centeredMaximal μ g x} := mul_le_mul_right (measure_mono hs) q
    _ ≤ ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, g x ∂μ :=
      centeredMaximal_weak_one μ g q
    _ = _ := by rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

end RudinRCA.Chapter08
end

/- Ch08PowerLayerCake -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

lemma lintegral_rpow_Ioo {p T : ℝ} (hp : 0 < p) (hT : 0 ≤ T) :
    (∫⁻ t in Ioo 0 T, ENNReal.ofReal (t ^ (p - 1))) =
      ENNReal.ofReal (T ^ p / p) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] (fun t : ℝ => t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo 0 T =ᵐ[volume] Ioc 0 T),
    ← ofReal_integral_eq_lintegral_ofReal hi.1 hn,
    ← intervalIntegral.integral_of_le hT, integral_rpow (Or.inl (by linarith))]
  simp [show p - 1 + 1 = p by ring, Real.zero_rpow hp.ne']

/-- The power primitive on an extended interval, including an infinite upper endpoint. -/
theorem lintegral_rpow_below_ennreal (a : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∫⁻ t in Ioi 0, {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (t ^ (p - 1))) t) = a ^ p / ENNReal.ofReal p := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  by_cases ha : a = ∞
  · subst a
    simp only [ENNReal.ofReal_lt_top, setOf_true, indicator_univ]
    let ν : Measure ℝ := volume.restrict (Ioi 0)
    have hc : AECover ν atTop (fun n : ℕ => Iio (n : ℝ)) :=
      aecover_Iio (μ := ν) tendsto_natCast_atTop_atTop
    have he (n : ℕ) :
        (∫⁻ t in Iio (n : ℝ), ENNReal.ofReal (t ^ (p - 1)) ∂ν) =
          (n : ℝ≥0∞) ^ p / ENNReal.ofReal p := by
      rw [show ν = volume.restrict (Ioi 0) from rfl,
        Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio (n : ℝ) ∩ Ioi 0 = Ioo 0 (n : ℝ) := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
        exact and_comm
      rw [hs, lintegral_rpow_Ioo hp (Nat.cast_nonneg n),
        ENNReal.ofReal_div_of_pos hp,
        ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n) hp.le]
      simp
    have hlim : Tendsto (fun n : ℕ => (n : ℝ≥0∞) ^ p / ENNReal.ofReal p) atTop
        (𝓝 ((∞ : ℝ≥0∞) ^ p / ENNReal.ofReal p)) :=
      ENNReal.Tendsto.div_const
        (((ENNReal.continuous_rpow_const (y := p)).tendsto ∞).comp
          ENNReal.tendsto_nat_nhds_top) (Or.inr (ENNReal.ofReal_pos.mpr hp).ne')
    apply hc.lintegral_eq_of_tendsto _ hm.aemeasurable
    simpa only [he] using hlim
  · rw [lintegral_indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_restrict (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    have hs : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      constructor
      · rintro ⟨hat, ht⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mp hat⟩
      · rintro ⟨ht, hat⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht.le ha).mpr hat, ht⟩
    rw [hs, lintegral_rpow_Ioo hp ENNReal.toReal_nonneg, ENNReal.ofReal_div_of_pos hp,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal ha]

-- The following theorem is a combined-file fragment: it depends on
-- layerCake_ennreal_weight from Ch08Phi.lean.
theorem layerCake_rpow_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi 0, μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := layerCake_ennreal_weight (g := fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))) μ hf
    (ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const) :
      Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1))))
  simp_rw [lintegral_rpow_below_ennreal _ hp] at h
  calc
    (∫⁻ x, f x ^ p ∂μ) =
        ENNReal.ofReal p * ∫⁻ x, f x ^ p / ENNReal.ofReal p ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [mul_comm, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hp).ne'
        ENNReal.ofReal_ne_top]
    _ = _ := congrArg (ENNReal.ofReal p * ·) h

end RudinRCA.Chapter08
end

/- Ch08StrongMaximal -/
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Tonelli evaluation of the truncated tails used in the maximal interpolation proof.
This fragment follows the power-layer-cake and weak-maximal fragments in a combined file. -/
theorem weighted_truncation_tails {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 2)) *
      ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) =
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  classical
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 2))
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  let F : X × ℝ → ℝ≥0∞ :=
    {z : X × ℝ | ENNReal.ofReal (z.2 / 2) < f z.1}.indicator
      (fun z => f z.1 * w z.2)
  have hs : MeasurableSet {z : X × ℝ | ENNReal.ofReal (z.2 / 2) < f z.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.div_const 2))
      (hf.comp measurable_fst)
  have hF : Measurable F := ((hf.comp measurable_fst).mul (hw.comp measurable_snd)).indicator hs
  have hinner (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      w t * ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ := by
    change (∫⁻ x, {x | ENNReal.ofReal (t / 2) < f x}.indicator (fun x => f x * w t) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf), lintegral_mul_const _ hf]
    exact mul_comm _ _
  have hcut (a : ℝ≥0∞) : {t : ℝ | ENNReal.ofReal (t / 2) < a} =
      {t : ℝ | ENNReal.ofReal t < 2 * a} := by
    ext t
    rw [mem_setOf_eq, mem_setOf_eq, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), mul_comm a]
  have hxinner (x : X) : (∫⁻ t in Ioi 0, F (x, t)) =
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * f x ^ p := by
    have he : (fun t => F (x, t)) =
        (fun t => f x * {t : ℝ | ENNReal.ofReal (t / 2) < f x}.indicator w t) := by
      funext t
      by_cases ht : ENNReal.ofReal (t / 2) < f x <;> simp [F, ht]
    have hmeas : Measurable ({t : ℝ | ENNReal.ofReal (t / 2) < f x}.indicator w) :=
      hw.indicator (measurableSet_lt
        (ENNReal.measurable_ofReal.comp (measurable_id.div_const 2)) measurable_const)
    rw [he, lintegral_const_mul _ hmeas, hcut]
    have hwexp : w = (fun t : ℝ => ENNReal.ofReal (t ^ ((p - 1) - 1))) := by
      funext t
      change ENNReal.ofReal (t ^ (p - 2)) = ENNReal.ofReal (t ^ ((p - 1) - 1))
      rw [show p - 2 = (p - 1) - 1 by ring]
    rw [hwexp, lintegral_rpow_below_ennreal _ (by linarith : 0 < p - 1),
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p - 1)]
    have hpow : f x * f x ^ (p - 1) = f x ^ p := by
      calc
        f x * f x ^ (p - 1) = f x ^ (1 : ℝ) * f x ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ = f x ^ (1 + (p - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (by linarith)).symm
        _ = f x ^ p := by congr 1; ring
    calc
      f x * (2 ^ (p - 1) * f x ^ (p - 1) / ENNReal.ofReal (p - 1)) =
          (2 ^ (p - 1) / ENNReal.ofReal (p - 1)) * (f x * f x ^ (p - 1)) := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ = _ := by rw [hpow]
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ := by simp only [hinner, w]
    _ = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi 0))
        (f := fun x t => F (x, t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hxinner]
      exact lintegral_const_mul _ (hf.pow_const p)

/-- Strong integral estimate with an explicit, nonoptimal dimension-dependent constant.
Rudin optimizes the truncation parameter; fixing it at one half suffices for membership. -/
theorem centeredMaximal_strong_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (2 * ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      ((2 : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  let C : ℝ≥0∞ := ENNReal.ofReal (5 ^ Module.finrank ℝ E)
  have htbound (t : ℝ) (ht : 0 < t) :
      μ {x | ENNReal.ofReal t < centeredMaximal μ f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (2 * C) * (ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) := by
    have h := mul_le_mul_right (centeredMaximal_truncation_tail μ hf ht)
      (2 * ENNReal.ofReal (t ^ (p - 2)))
    have hcoeff : (2 : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal (t / 2) =
        ENNReal.ofReal (t ^ (p - 1)) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t ^ (p - 2))]
      congr 1
      calc
        2 * t ^ (p - 2) * (t / 2) = t ^ (p - 2) * t ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
        _ = t ^ (p - 2 + 1) := (Real.rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (2 * ENNReal.ofReal (t ^ (p - 2))) *
          (ENNReal.ofReal (t / 2) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x}) := by
            rw [← mul_assoc, hcoeff, mul_comm]
      _ ≤ _ := by simpa only [C, mul_assoc, mul_left_comm, mul_comm] using h
  rw [layerCake_rpow_ennreal μ (centeredMaximal_measurable μ hf) (by linarith : 0 < p)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, (2 * C) * (ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ) := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      exact fun t ht => htbound t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top), weighted_truncation_tails μ hf hp]
      simp only [C, mul_assoc]

/-- The maximal operator depends only on the almost-everywhere class of its input. -/
theorem centeredMaximal_congr_ae {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ≥0∞} (hfg : f =ᵐ[μ] g) :
    centeredMaximal μ f = centeredMaximal μ g := by
  funext x
  unfold centeredMaximal
  congr 1
  funext r
  congr 1
  funext hr
  rw [lintegral_congr_ae (ae_restrict_of_ae hfg)]

/-- Finiteness of the strong integral implies an almost-everywhere finite maximal function
and actual real-valued Lp membership. The separate finiteness clause prevents `toReal` from
concealing infinite maximal values. -/
theorem centeredMaximal_memLp_of_lintegral_rpow_lt_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfi : (∫⁻ x, f x ^ p ∂μ) < ∞) :
    (∀ᵐ x ∂μ, centeredMaximal μ f x < ∞) ∧
      MemLp (fun x => (centeredMaximal μ f x).toReal) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hMi : (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) < ∞ := by
    apply lt_of_le_of_lt (centeredMaximal_strong_bound μ hf hp)
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      · apply ENNReal.div_lt_top
        · exact (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by norm_num)).ne
        · exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    · exact hfi
  have hm := centeredMaximal_measurable μ hf
  have hae : ∀ᵐ x ∂μ, centeredMaximal μ f x < ∞ := by
    filter_upwards [ae_lt_top (hm.pow_const p) hMi.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx
  refine ⟨hae, ?_⟩
  change eLpNorm (fun x => (centeredMaximal μ f x).toReal) (ENNReal.ofReal p) μ < ∞
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    hm.ennreal_toReal.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  have he : (∫⁻ x, ‖(centeredMaximal μ f x).toReal‖ₑ ^ p ∂μ) =
      ∫⁻ x, centeredMaximal μ f x ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [Real.enorm_toReal hx.ne]
  rwa [he]

/-- Rudin 8.18 for complex-valued functions on any finite-dimensional real normed
space with Haar measure, hence in particular Euclidean R^k with Lebesgue measure. -/
theorem theorem_8_18 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∀ᵐ x ∂μ, maximalFunction μ f x < ∞) ∧
      MemLp (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let g : E → ℝ≥0∞ := fun x => ‖hf.aestronglyMeasurable.mk f x‖ₑ
  have hg : Measurable g := hf.aestronglyMeasurable.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have hgi : (∫⁻ x, g x ^ p ∂μ) < ∞ := by
    have hfi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hp0.le] at hfi
    have hpow : (fun x => ‖f x‖ₑ ^ p) =ᵐ[μ] (fun x => g x ^ p) := by
      filter_upwards [hfg] with x hx
      rw [hx]
    rw [← lintegral_congr_ae hpow]
    exact hfi
  have he : maximalFunction μ f = centeredMaximal μ g :=
    centeredMaximal_congr_ae μ hfg
  rw [he]
  exact centeredMaximal_memLp_of_lintegral_rpow_lt_top μ hg hp hgi

end RudinRCA.Chapter08
end

/- Ch08MaximalConstant -/
noncomputable section
open Filter Set
open scoped Topology
namespace RudinRCA.Chapter08

/-- The elementary exponential estimate used in Rudin's optimized maximal bound. -/
theorem conjugateExponent_rpow_le_exp {p : ℝ} (hp : 1 < p) :
    (p / (p - 1)) ^ (p - 1) ≤ Real.exp 1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  rw [Real.rpow_def_of_pos hq, Real.exp_le_exp]
  have hlog := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hq) hd.le
  have he : (p / (p - 1) - 1) * (p - 1) = 1 := by
    field_simp [hd.ne']
    ring
  exact hlog.trans_eq he

/-- Bounding the optimized p-th-power coefficient by the one printed in 8.18. -/
theorem maximalLpCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    A * p * (p / (p - 1)) ^ p ≤ A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = (A * p * (p / (p - 1))) * (p / (p - 1)) ^ (p - 1) := by rw [hpow]; ring
    _ ≤ (A * p * (p / (p - 1))) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (conjugateExponent_rpow_le_exp hp) (by positivity)
    _ = _ := by ring

/-- Scalar form of the optimized truncation coefficient, with cutoff t/q. -/
theorem maximalLpParameterizedCoefficient_le {A p : ℝ} (hA : 0 ≤ A) (hp : 1 < p) :
    p * (1 / (1 - 1 / (p / (p - 1)))) * A *
        ((p / (p - 1)) ^ (p - 1) / (p - 1)) ≤
      A * Real.exp 1 * p * (p / (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have hden : 1 - 1 / (p / (p - 1)) = 1 / p := by
    field_simp [hp0.ne', hd.ne']
    ring
  have hpow : (p / (p - 1)) ^ p =
      (p / (p - 1)) * (p / (p - 1)) ^ (p - 1) := by
    calc
      _ = (p / (p - 1)) ^ (1 + (p - 1)) := by congr 1; ring
      _ = (p / (p - 1)) ^ (1 : ℝ) * (p / (p - 1)) ^ (p - 1) := Real.rpow_add hq _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = A * p * (p / (p - 1)) ^ p := by
      rw [hden, one_div_one_div, hpow]
      ring
    _ ≤ _ := maximalLpCoefficient_le hA hp

/-- The constant displayed after the proof of 8.18, for weak-type constant A. -/
noncomputable def maximalLpConstant (A p : ℝ) : ℝ :=
  (A * Real.exp 1 * p * (p / (p - 1))) ^ (1 / p)

/-- The optimized constant approaches one as p increases without bound. -/
theorem maximalLpConstant_tendsto_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) atTop (𝓝 1) := by
  have hi : Tendsto (fun p : ℝ => 1 / p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) atTop (𝓝 1) := by
    have hdtop : Tendsto (fun p : ℝ => p - 1) atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b + 1)] with p hp
      linarith
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_inv_atTop_zero.comp hdtop)
    apply (show Tendsto (fun p : ℝ => 1 + (p - 1)⁻¹) atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
    field_simp [(sub_pos.mpr hp).ne'] <;> ring
  have hc : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := A * Real.exp 1)).rpow hi
      (Or.inl (ne_of_gt (mul_pos hA (Real.exp_pos _))))
  have hqp : Tendsto (fun p : ℝ => (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa using hq.rpow hi (Or.inl one_ne_zero)
  have hprod : Tendsto (fun p : ℝ => (A * Real.exp 1) ^ (1 / p) *
      p ^ (1 / p) * (p / (p - 1)) ^ (1 / p)) atTop (𝓝 1) := by
    simpa [Pi.mul_apply] using (hc.mul tendsto_rpow_div).mul hqp
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  dsimp [maximalLpConstant]
  rw [Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1 * p) hq0.le,
    Real.mul_rpow (by positivity : 0 ≤ A * Real.exp 1) hp0.le]

/-- The optimized constant diverges as p decreases to one from above. -/
theorem maximalLpConstant_tendsto_one_right {A : ℝ} (hA : 0 < A) :
    Tendsto (maximalLpConstant A) (𝓝[>] 1) atTop := by
  have hid : Tendsto (fun p : ℝ => p) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun p : ℝ => p - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hid.sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact sub_pos.mpr hp
  have hq : Tendsto (fun p : ℝ => p / (p - 1)) (𝓝[>] 1) atTop := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      hid.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hd)
  have hb : Tendsto (fun p : ℝ => A * Real.exp 1 * p * (p / (p - 1)))
      (𝓝[>] 1) atTop := by
    have hc : Tendsto (fun p : ℝ => A * Real.exp 1 * p) (𝓝[>] 1)
        (𝓝 (A * Real.exp 1)) := by simpa using hid.const_mul (A * Real.exp 1)
    exact hc.pos_mul_atTop (mul_pos hA (Real.exp_pos _)) hq
  have hi : Tendsto (fun p : ℝ => 1 / p) (𝓝[>] 1) (𝓝 1) := by
    simpa only [one_div, inv_one] using hid.inv₀ one_ne_zero
  have h := Real.tendsto_exp_atTop.comp
    ((Real.tendsto_log_atTop.comp hb).atTop_mul_pos zero_lt_one hi)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  exact (Real.rpow_def_of_pos (by positivity : 0 < A * Real.exp 1 * p * (p / (p - 1))) _).symm

end RudinRCA.Chapter08
end

/- Ch08ParameterizedMaximal -/
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

theorem weighted_truncation_tails_parameter {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (d : ℝ) (hd : 0 < d) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 2)) *
      ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) =
      ((ENNReal.ofReal d : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  classical
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 2))
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow measurable_const)
  let F : X × ℝ → ℝ≥0∞ :=
    {z : X × ℝ | ENNReal.ofReal (z.2 / d) < f z.1}.indicator
      (fun z => f z.1 * w z.2)
  have hs : MeasurableSet {z : X × ℝ | ENNReal.ofReal (z.2 / d) < f z.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.div_const d))
      (hf.comp measurable_fst)
  have hF : Measurable F := ((hf.comp measurable_fst).mul (hw.comp measurable_snd)).indicator hs
  have hinner (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      w t * ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ := by
    change (∫⁻ x, {x | ENNReal.ofReal (t / d) < f x}.indicator (fun x => f x * w t) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf), lintegral_mul_const _ hf]
    exact mul_comm _ _
  have hcut (a : ℝ≥0∞) : {t : ℝ | ENNReal.ofReal (t / d) < a} =
      {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal d * a} := by
    ext t
    rw [mem_setOf_eq, mem_setOf_eq, ENNReal.ofReal_div_of_pos hd]
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hd).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm a]
  have hxinner (x : X) : (∫⁻ t in Ioi 0, F (x, t)) =
      ((ENNReal.ofReal d : ℝ≥0∞) ^ (p - 1) / ENNReal.ofReal (p - 1)) * f x ^ p := by
    have he : (fun t => F (x, t)) =
        (fun t => f x * {t : ℝ | ENNReal.ofReal (t / d) < f x}.indicator w t) := by
      funext t
      by_cases ht : ENNReal.ofReal (t / d) < f x <;> simp [F, ht]
    have hmeas : Measurable ({t : ℝ | ENNReal.ofReal (t / d) < f x}.indicator w) :=
      hw.indicator (measurableSet_lt
        (ENNReal.measurable_ofReal.comp (measurable_id.div_const d)) measurable_const)
    rw [he, lintegral_const_mul _ hmeas, hcut]
    have hwexp : w = (fun t : ℝ => ENNReal.ofReal (t ^ ((p - 1) - 1))) := by
      funext t
      change ENNReal.ofReal (t ^ (p - 2)) = ENNReal.ofReal (t ^ ((p - 1) - 1))
      rw [show p - 2 = (p - 1) - 1 by ring]
    rw [hwexp, lintegral_rpow_below_ennreal _ (by linarith : 0 < p - 1),
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p - 1)]
    have hpow : f x * f x ^ (p - 1) = f x ^ p := by
      calc
        f x * f x ^ (p - 1) = f x ^ (1 : ℝ) * f x ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ = f x ^ (1 + (p - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (by linarith)).symm
        _ = f x ^ p := by congr 1; ring
    calc
      f x * (ENNReal.ofReal d ^ (p - 1) * f x ^ (p - 1) / ENNReal.ofReal (p - 1)) =
          (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * (f x * f x ^ (p - 1)) := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ = _ := by rw [hpow]
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) ∂μ := by simp only [hinner, w]
    _ = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) ∂volume ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi 0))
        (f := fun x t => F (x, t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hxinner]
      exact lintegral_const_mul _ (hf.pow_const p)


/-- Truncation at an arbitrary fraction `1 / d` of the level. -/
theorem centeredMaximal_truncation_tail_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {t d : ℝ} (ht : 0 < t) (hd : 1 < d) :
    ENNReal.ofReal ((1 - 1 / d) * t) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) *
        ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ := by
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hc : 0 < 1 - 1 / d := by rw [sub_pos, div_lt_one hd0]; exact hd
  let q := ENNReal.ofReal (t / d)
  let a := ENNReal.ofReal ((1 - 1 / d) * t)
  let g := {x | q < f x}.indicator f
  have hsum : a + q = ENNReal.ofReal t := by
    change ENNReal.ofReal ((1 - 1 / d) * t) + ENNReal.ofReal (t / d) = ENNReal.ofReal t
    rw [← ENNReal.ofReal_add (mul_nonneg hc.le ht.le) (div_nonneg ht.le hd0.le)]
    congr 1
    ring
  have hfg (x : E) : f x ≤ g x + q := by
    by_cases hx : q < f x
    · simp only [g, mem_setOf_eq, hx, indicator_of_mem]
      exact le_add_right le_rfl
    · simp only [g, mem_setOf_eq, hx, not_false_eq_true, indicator_of_notMem, zero_add]
      exact le_of_not_gt hx
  have hM (x : E) : centeredMaximal μ f x ≤ centeredMaximal μ g x + q :=
    centeredMaximal_le_add_const μ hfg
      (fun x r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩) x
  have hs : {x | ENNReal.ofReal t < centeredMaximal μ f x} ⊆
      {x | a < centeredMaximal μ g x} := by
    intro x hx
    by_contra hnot
    have hle := (hM x).trans (add_le_add (le_of_not_gt hnot) le_rfl)
    rw [hsum] at hle
    exact (not_le_of_gt hx) hle
  calc
    a * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
        a * μ {x | a < centeredMaximal μ g x} := mul_le_mul_right (measure_mono hs) a
    _ ≤ ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, g x ∂μ :=
      centeredMaximal_weak_one μ g a
    _ = _ := by rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

/-- The strong estimate before choosing the truncation parameter. -/
theorem centeredMaximal_strong_bound_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ≥0∞} (hf : Measurable f) {p d : ℝ} (hp : 1 < p) (hd : 1 < d) :
    (∫⁻ x, centeredMaximal μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / d)) *
        ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, f x ^ p ∂μ := by
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hc : 0 < 1 - 1 / d := by rw [sub_pos, div_lt_one hd0]; exact hd
  let C : ℝ≥0∞ := ENNReal.ofReal (5 ^ Module.finrank ℝ E)
  let b : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - 1 / d))
  have htbound (t : ℝ) (ht : 0 < t) :
      μ {x | ENNReal.ofReal t < centeredMaximal μ f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (b * C) * (ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) := by
    have h := mul_le_mul_right (centeredMaximal_truncation_tail_parameter μ hf ht hd)
      (b * ENNReal.ofReal (t ^ (p - 2)))
    have hcoeff : b * ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal ((1 - 1 / d) * t) =
        ENNReal.ofReal (t ^ (p - 1)) := by
      change ENNReal.ofReal (1 / (1 - 1 / d)) * ENNReal.ofReal (t ^ (p - 2)) *
        ENNReal.ofReal ((1 - 1 / d) * t) = _
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - 1 / d)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - 1 / d) * t ^ (p - 2))]
      congr 1
      calc
        1 / (1 - 1 / d) * t ^ (p - 2) * ((1 - 1 / d) * t) =
            t ^ (p - 2) * t ^ (1 : ℝ) := by
              rw [Real.rpow_one]
              calc
                _ = (1 / (1 - 1 / d) * (1 - 1 / d)) * (t ^ (p - 2) * t) := by ring
                _ = _ := by rw [div_mul_cancel₀ 1 hc.ne', one_mul]
        _ = t ^ (p - 2 + 1) := (Real.rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (b * ENNReal.ofReal (t ^ (p - 2))) *
          (ENNReal.ofReal ((1 - 1 / d) * t) *
            μ {x | ENNReal.ofReal t < centeredMaximal μ f x}) := by
              rw [← mul_assoc, hcoeff, mul_comm]
      _ ≤ _ := by simpa only [C, mul_assoc, mul_left_comm, mul_comm] using h
  rw [layerCake_rpow_ennreal μ (centeredMaximal_measurable μ hf) (by linarith : 0 < p)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, (b * C) * (ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ x in {x | ENNReal.ofReal (t / d) < f x}, f x ∂μ) := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      exact fun t ht => htbound t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
        weighted_truncation_tails_parameter μ hf hp d hd0]
      simp only [C, b, mul_assoc]

end RudinRCA.Chapter08
end

/- Ch08MaximalNorm -/
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

theorem maximalFunction_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    (hf : AEStronglyMeasurable f μ) : Measurable (maximalFunction μ f) := by
  let g : E → ℝ≥0∞ := fun x => ‖hf.mk f x‖ₑ
  have hg : Measurable g := hf.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have he : maximalFunction μ f = centeredMaximal μ g := centeredMaximal_congr_ae μ hfg
  rw [he]
  exact centeredMaximal_measurable μ hg

/-- The weak-L1 assertion recalled in 8.17, expressed as uniform boundedness
of level times distribution measure. -/
theorem theorem_8_17_weak_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ} (hf : Integrable f μ) :
    Measurable (maximalFunction μ f) ∧ ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | ENNReal.ofReal t < maximalFunction μ f x} ≤ C := by
  refine ⟨maximalFunction_measurable μ hf.aestronglyMeasurable,
    ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, ‖f x‖ₑ ∂μ, ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral)
  · intro t ht
    exact centeredMaximal_weak_one μ (fun x => ‖f x‖ₑ) (ENNReal.ofReal t)

/-- The L-infinity contraction printed in 8.17, for the actual real-valued maximal function. -/
theorem theorem_8_17_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ} (hf : MemLp f ∞ μ) :
    (∀ x, maximalFunction μ f x < ∞) ∧
      MemLp (fun x => (maximalFunction μ f x).toReal) ∞ μ ∧
      eLpNorm (fun x => (maximalFunction μ f x).toReal) ∞ μ ≤ eLpNorm f ∞ μ := by
  have hm := maximalFunction_measurable μ hf.aestronglyMeasurable
  have hfinite (x : E) : maximalFunction μ f x < ∞ := by
    apply lt_of_le_of_lt (maximalFunction_le_essSup μ f x)
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  have hn : eLpNorm (fun x => (maximalFunction μ f x).toReal) ∞ μ ≤ eLpNorm f ∞ μ := by
    rw [eLpNorm_exponent_top hm.ennreal_toReal.aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    apply Eventually.of_forall
    intro x
    rw [Real.enorm_toReal (hfinite x).ne]
    exact maximalFunction_le_essSup μ f x
  exact ⟨hfinite, hn.trans_lt hf.eLpNorm_lt_top, hn⟩

theorem maximalFunction_strong_bound_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} (hf : AEStronglyMeasurable f μ) {p d : ℝ} (hp : 1 < p) (hd : 1 < d) :
    (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / d)) *
        ENNReal.ofReal (5 ^ Module.finrank ℝ E)) *
      (ENNReal.ofReal d ^ (p - 1) / ENNReal.ofReal (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let g : E → ℝ≥0∞ := fun x => ‖hf.mk f x‖ₑ
  have hg : Measurable g := hf.measurable_mk.enorm
  have hfg : (fun x => ‖f x‖ₑ) =ᵐ[μ] g := by
    filter_upwards [hf.ae_eq_mk] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ₑ) hx
  have he : maximalFunction μ f = centeredMaximal μ g := centeredMaximal_congr_ae μ hfg
  have hpow : (fun x => ‖f x‖ₑ ^ p) =ᵐ[μ] (fun x => g x ^ p) := by
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [he, lintegral_congr_ae hpow]
  exact centeredMaximal_strong_bound_parameter μ hg hp hd

/-- Conversion of an integral-power estimate to the corresponding Lp seminorm estimate. -/
theorem maximalFunction_eLpNorm_le_of_integral_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    {B : ℝ≥0∞} (hbound : (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      B * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    eLpNorm (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ ≤
      B ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hm := maximalFunction_measurable μ hf.aestronglyMeasurable
  have hae := (theorem_8_18 μ hp hf).1
  have he : (∫⁻ x, ‖(maximalFunction μ f x).toReal‖ₑ ^ p ∂μ) =
      ∫⁻ x, maximalFunction μ f x ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [Real.enorm_toReal hx.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hm.ennreal_toReal.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, he]
  calc
    _ ≤ (B * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hbound (by positivity)
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

/-- The quantitative conclusion accompanying Rudin 8.18, with the displayed
constant `(A * exp 1 * p * q)^(1/p)` and `A = 5^dim`. -/
theorem theorem_8_18_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => (maximalFunction μ f x).toReal) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (maximalLpConstant (5 ^ Module.finrank ℝ E) p) *
        eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpd : 0 < p - 1 := sub_pos.mpr hp
  let q : ℝ := p / (p - 1)
  let A : ℝ := 5 ^ Module.finrank ℝ E
  have hA : 0 ≤ A := by positivity
  have hq : 1 < q := by
    change 1 < p / (p - 1)
    rw [one_lt_div hpd]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hc : 0 < 1 - 1 / q := by rw [sub_pos, div_lt_one hq0]; exact hq
  have hb : 0 ≤ 1 / (1 - 1 / q) := by positivity
  have hecoeff :
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / q)) * ENNReal.ofReal A) *
        (ENNReal.ofReal q ^ (p - 1) / ENNReal.ofReal (p - 1)) =
      ENNReal.ofReal (p * (1 / (1 - 1 / q)) * A * (q ^ (p - 1) / (p - 1))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hq0.le hpd.le,
      ← ENNReal.ofReal_div_of_pos hpd,
      ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_mul hp0.le,
      ← ENNReal.ofReal_mul (mul_nonneg hp0.le (mul_nonneg hb hA))]
    congr 1
    ring
  have hcoeff :
      ENNReal.ofReal p * (ENNReal.ofReal (1 / (1 - 1 / q)) * ENNReal.ofReal A) *
        (ENNReal.ofReal q ^ (p - 1) / ENNReal.ofReal (p - 1)) ≤
      ENNReal.ofReal (A * Real.exp 1 * p * q) := by
    rw [hecoeff]
    exact ENNReal.ofReal_le_ofReal (maximalLpParameterizedCoefficient_le hA hp)
  have hbound : (∫⁻ x, maximalFunction μ f x ^ p ∂μ) ≤
      ENNReal.ofReal (A * Real.exp 1 * p * q) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
    (maximalFunction_strong_bound_parameter μ hf.aestronglyMeasurable hp hq).trans
      (mul_le_mul_left hcoeff _)
  have hnorm := maximalFunction_eLpNorm_le_of_integral_bound μ hp hf hbound
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)] at hnorm
  exact hnorm

/-- The printed Euclidean-space specialization, including finiteness and the norm bound. -/
theorem theorem_8_18_euclidean (k : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℂ}
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∀ᵐ x, maximalFunction volume f x < ∞) ∧
      MemLp (fun x => (maximalFunction volume f x).toReal) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x => (maximalFunction volume f x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (maximalLpConstant (5 ^ k) p) * eLpNorm f (ENNReal.ofReal p) volume := by
  refine ⟨(theorem_8_18 volume hp hf).1, (theorem_8_18 volume hp hf).2, ?_⟩
  simpa only [finrank_euclideanSpace_fin] using theorem_8_18_norm_bound volume hp hf

end RudinRCA.Chapter08
end

