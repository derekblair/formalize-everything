import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.VectorMeasure.Relations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- BEGIN SOURCE RudinRCA/Chapter06.lean










/-!
# Chapter 6: Complex measures

Numbered declarations follow Rudin, *Real and Complex Analysis*, third edition.
`ComplexMeasure X` encodes countable additivity without assuming finite variation.
Values on nonmeasurable sets are conventionally zero; book statements concern
measurable sets. Coverage is recorded separately in `SCOPING-C.md`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace RudinRCA.Chapter06

universe u
variable {X : Type u} [MeasurableSpace X]

/-- 6.1: the series in the definition of a complex measure converges to the
measure of the union. `HasSum` includes convergence. -/
theorem complexMeasure_hasSum (μ : ComplexMeasure X) (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) (hdisj : Pairwise (Disjoint on E)) :
    HasSum (fun n => μ (E n)) (μ (⋃ n, E n)) :=
  μ.m_iUnion hE hdisj

/-- 6.1: countable additivity is absolutely convergent. -/
theorem complexMeasure_summable_norm (μ : ComplexMeasure X) (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) (hdisj : Pairwise (Disjoint on E)) :
    Summable (fun n => ‖μ (E n)‖) :=
  (complexMeasure_hasSum μ E hE hdisj).summable.norm

/-- 6.1: the total variation measure. -/
abbrev totalVariation (μ : ComplexMeasure X) : Measure X := μ.variation

/-- 6.1: total variation dominates the absolute value of the measure. -/
theorem enorm_le_totalVariation (μ : ComplexMeasure X) (E : Set X) :
    ‖μ E‖ₑ ≤ totalVariation μ E :=
  μ.enorm_measure_le_variation E

/-- 6.1: total variation is the least positive measure with this domination. -/
theorem totalVariation_minimal (μ : ComplexMeasure X) (ν : Measure X)
    (h : ∀ E, MeasurableSet E → ‖μ E‖ₑ ≤ ν E) :
    totalVariation μ ≤ ν :=
  VectorMeasure.variation_le_of_forall_enorm_le h

/-- 6.1: taking variation leaves a finite positive measure unchanged. -/
theorem variation_positive (μ : Measure X) [IsFiniteMeasure μ] :
    μ.toSignedMeasure.variation = μ :=
  Measure.variation_toSignedMeasure

/-- 6.1: the same assertion includes infinite positive measures, represented as
extended nonnegative vector measures. -/
theorem variation_positive_extended (μ : Measure X) :
    μ.toENNRealVectorMeasure.variation = μ := by
  rw [VectorMeasure.variation_eq_ennrealToMeasure,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]

/-- 6.2: the total variation assigns zero to the empty set. -/
theorem totalVariation_empty (μ : ComplexMeasure X) : totalVariation μ ∅ = 0 :=
  measure_empty

/-- 6.2: the total variation is countably additive. -/
theorem totalVariation_iUnion (μ : ComplexMeasure X) (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) (hdisj : Pairwise (Disjoint on E)) :
    totalVariation μ (⋃ n, E n) = ∑' n, totalVariation μ (E n) :=
  measure_iUnion hdisj hE

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
        exact (P.pairwiseDisjoint_apply (f := fun A : Subtype (MeasurableSet : Set X → Prop) => A.val) (fun _ _ => rfl) rfl)
          i.property j.property (fun h => hij (Subtype.ext h))
      covers := by
        have hc : (⋃ i : P.parts, i.val.val) = P.parts.sup Subtype.val := by
          ext x
          simp only [Finset.sup_set_eq_biUnion, Set.mem_iUnion]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨i.val, i.property, hi⟩
          · rintro ⟨A, hA, hx⟩
            exact ⟨⟨A, hA⟩, hx⟩
        exact hc.trans (P.sup_parts_apply
          (f := fun A : Subtype (MeasurableSet : Set X → Prop) => A.val)
          (fun _ _ => rfl) rfl) }
    have h := le_iSup (fun Q : CountablePartition E => ∑' i, ‖μ (Q.part i)‖ₑ) Q
    change (∑' i : P.parts, ‖μ i.val.val‖ₑ) ≤ _ at h
    rw [tsum_fintype] at h
    have hsum : (∑ i : P.parts, ‖μ i.val.val‖ₑ) = ∑ p ∈ P.parts, ‖μ p.val‖ₑ :=
      Finset.sum_coe_sort P.parts (fun p => ‖μ p.val‖ₑ)
    exact hsum ▸ h
  · apply iSup_le
    intro P
    calc
      (∑' i, ‖μ (P.part i)‖ₑ) ≤ ∑' i, μ.variation (P.part i) :=
        ENNReal.tsum_le_tsum fun i => μ.enorm_measure_le_variation _
      _ = μ.variation E := by rw [← measure_iUnion P.disjoint P.measurable, P.covers]



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

/-- 6.5: the vector-space addition agrees with setwise addition. -/
theorem complexMeasure_add_apply (μ ν : ComplexMeasure X) (E : Set X) :
    (μ + ν) E = μ E + ν E := rfl

/-- 6.5: the complex scalar action agrees with setwise multiplication. -/
theorem complexMeasure_smul_apply (z : ℂ) (μ : ComplexMeasure X) (E : Set X) :
    (z • μ) E = z * μ E := rfl

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
#print axioms complexMeasure_add_apply
#print axioms complexMeasure_smul_apply
#print axioms complex_norm_eq_variation
#print axioms complexMeasureNormedSpace
#print axioms complex_measure_norm_le
#print axioms positive_add_negative_variation
#print axioms positive_sub_negative_variation
#print axioms positiveVariation_real_eq
#print axioms negativeVariation_real_eq


section AbsoluteContinuity

variable {V W : Type*}
  [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V] [ContinuousAdd V]
  [TopologicalSpace W] [ENormedAddCommMonoid W] [T2Space W] [ContinuousAdd W]

/-- 6.7: concentration on a measurable set, in its equivalent null-set form.
Using vector measures includes complex and signed measures. -/
def ConcentratedOn (μ : VectorMeasure X V) (A : Set X) : Prop :=
  ∀ E, Disjoint E A → μ E = 0

/-- 6.7: the library absolute-continuity relation is exactly the book's
null-set condition on measurable sets. -/
theorem absolutelyContinuous_iff_null_sets (μ : VectorMeasure X V) (ρ : Measure X) :
    μ ≪ᵥ ρ.toENNRealVectorMeasure ↔
      ∀ E, MeasurableSet E → ρ E = 0 → μ E = 0 := by
  constructor
  · intro h E hE hρ
    exact h (by rw [Measure.toENNRealVectorMeasure_apply_measurable hE, hρ])
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro E hE hρ
    exact h E hE (by simpa only [Measure.toENNRealVectorMeasure_apply_measurable hE] using hρ)

/-- 6.7: the library singularity relation is exactly concentration on disjoint
measurable sets, including the case of positive measures encoded over ENNReal. -/
theorem mutuallySingular_iff_concentrated (μ : VectorMeasure X V) (ν : VectorMeasure X W) :
    μ ⟂ᵥ ν ↔ ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ Disjoint A B ∧
      ConcentratedOn μ A ∧ ConcentratedOn ν B := by
  constructor
  · rintro ⟨S, hS, hμ, hν⟩
    refine ⟨Sᶜ, S, hS.compl, hS, disjoint_compl_left, ?_, ?_⟩
    · intro E hE
      apply hμ E
      intro x hx
      by_contra h
      exact Set.disjoint_left.mp hE hx h
    · intro E hE
      exact hν E (Set.disjoint_left.mp hE)
  · rintro ⟨A, B, hA, hB, hAB, hμ, hν⟩
    refine ⟨Aᶜ, hA.compl, ?_, ?_⟩
    · intro E hE
      exact hμ E (Set.disjoint_left.mpr fun x hx hxa => hE hx hxa)
    · intro E hE
      apply hν E
      apply hAB.mono_left
      simpa only [compl_compl] using hE

/-- 6.7: concentration is equivalent to restricting every measurable argument
to its intersection with the concentration set. -/
theorem concentratedOn_iff_inter (μ : VectorMeasure X V) {A : Set X}
    (hA : MeasurableSet A) :
    ConcentratedOn μ A ↔ ∀ E, MeasurableSet E → μ E = μ (A ∩ E) := by
  constructor
  · intro h E hE
    have hsplit : E = (A ∩ E) ∪ (E \ A) := by ext x; simp; tauto
    calc
      μ E = μ ((A ∩ E) ∪ (E \ A)) := congrArg μ hsplit
      _ = μ (A ∩ E) + μ (E \ A) := μ.of_union
        (by exact disjoint_sdiff_right.mono_left inter_subset_left) (hA.inter hE) (hE.diff hA)
      _ = μ (A ∩ E) := by rw [h _ disjoint_sdiff_left, add_zero]
  · intro h E hEA
    by_cases hE : MeasurableSet E
    · rw [h E hE, (Set.disjoint_iff_inter_eq_empty.mp hEA.symm), μ.empty]
    · exact μ.not_measurable hE

/-- 6.8(a): concentration passes to total variation. The positive measure is
expressed by its value zero on every set disjoint from the concentration set. -/
theorem variation_concentratedOn {μ : VectorMeasure X V} {A : Set X}
    (hA : MeasurableSet A) (h : ConcentratedOn μ A) :
    ∀ E, Disjoint E A → μ.variation E = 0 := by
  have hz : μ.variation Aᶜ = 0 :=
    (VectorMeasure.variation_apply_eq_zero hA.compl).2 fun E hE _ =>
      h E (Set.disjoint_left.mpr fun x hx hxa => hE hx hxa)
  intro E hE
  exact measure_mono_null (Set.disjoint_left.mp hE) hz

/-- 6.8(b): mutual singularity passes to the total variation measures. -/
theorem variations_mutuallySingular {μ : VectorMeasure X V} {ν : VectorMeasure X W}
    (h : μ ⟂ᵥ ν) : μ.variation ⟂ₘ ν.variation := by
  obtain ⟨A, hA, hμ, hν⟩ := h
  exact ⟨A, hA, (VectorMeasure.variation_apply_eq_zero hA).2 (fun E hE _ => hμ E hE),
    (VectorMeasure.variation_apply_eq_zero hA.compl).2 (fun E hE _ => hν E hE)⟩

/-- 6.8(c): the sum of two measures singular to a fixed positive measure is singular. -/
theorem singular_add {μ ν : VectorMeasure X V} {ρ : Measure X}
    (hμ : μ ⟂ᵥ ρ.toENNRealVectorMeasure) (hν : ν ⟂ᵥ ρ.toENNRealVectorMeasure) :
    μ + ν ⟂ᵥ ρ.toENNRealVectorMeasure := hμ.add_left hν

/-- 6.8(d): absolute continuity is closed under addition. -/
theorem absolutelyContinuous_add {μ ν : VectorMeasure X V} {ρ : Measure X}
    (hμ : μ ≪ᵥ ρ.toENNRealVectorMeasure) (hν : ν ≪ᵥ ρ.toENNRealVectorMeasure) :
    μ + ν ≪ᵥ ρ.toENNRealVectorMeasure := hμ.add hν

/-- 6.8(e): absolute continuity passes to total variation. -/
theorem variation_absolutelyContinuous {μ : VectorMeasure X V} {ρ : Measure X}
    (h : μ ≪ᵥ ρ.toENNRealVectorMeasure) : μ.variation ≪ ρ := by
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hρ
  apply (VectorMeasure.variation_apply_eq_zero hE).2
  intro F hFE hF
  apply h
  rw [Measure.toENNRealVectorMeasure_apply_measurable hF]
  exact measure_mono_null hFE hρ

/-- 6.8(f): absolute continuity and singularity relative to the same positive
measure imply mutual singularity. -/
theorem mutuallySingular_of_ac_of_singular {μ : VectorMeasure X V}
    {ν : VectorMeasure X W} {ρ : Measure X}
    (hμ : μ ≪ᵥ ρ.toENNRealVectorMeasure) (hν : ν ⟂ᵥ ρ.toENNRealVectorMeasure) :
    μ ⟂ᵥ ν := by
  obtain ⟨A, hA, hνA, hρA⟩ := hν
  exact ⟨Aᶜ, hA.compl, fun E hE => hμ (hρA E hE), by simpa using hνA⟩

/-- 6.8(g): a measure both absolutely continuous and singular is zero. -/
theorem eq_zero_of_ac_of_singular {μ : VectorMeasure X V} {ρ : Measure X}
    (hac : μ ≪ᵥ ρ.toENNRealVectorMeasure) (hs : μ ⟂ᵥ ρ.toENNRealVectorMeasure) :
    μ = 0 := by
  have hself := variations_mutuallySingular (mutuallySingular_of_ac_of_singular hac hs)
  have hz : μ.variation = 0 := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
    Measure.AbsolutelyContinuous.rfl hself
  exact VectorMeasure.variation_eq_zero.mp hz

end AbsoluteContinuity

#print axioms complexMeasure_hasSum
#print axioms complexMeasure_summable_norm
#print axioms enorm_le_totalVariation
#print axioms totalVariation_minimal
#print axioms variation_positive
#print axioms variation_positive_extended
#print axioms totalVariation_empty
#print axioms totalVariation_iUnion
#print axioms variation_eq_iSup_countablePartitions
#print axioms absolutelyContinuous_iff_null_sets
#print axioms mutuallySingular_iff_concentrated
#print axioms concentratedOn_iff_inter
#print axioms variation_concentratedOn
#print axioms variations_mutuallySingular
#print axioms singular_add
#print axioms absolutelyContinuous_add
#print axioms variation_absolutelyContinuous
#print axioms mutuallySingular_of_ac_of_singular
#print axioms eq_zero_of_ac_of_singular



private theorem norm_star_lp_two (μ : Measure X) (g : Lp ℂ 2 μ) : ‖star g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star g), eLpNorm_star]

private theorem inner_star_lp_two (μ : Measure X) (g f : Lp ℂ 2 μ) :
    inner ℂ (star g) f = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

/-- 6.17: the Hilbert-space case of complex Lp duality, with the book's
unconjugated product convention explicitly obtained by conjugating the Riesz vector.
The general 6.16 theorem remains a separate obligation. -/
theorem hilbert_lp_duality (μ : Measure X) (Φ : Lp ℂ 2 μ →L[ℂ] ℂ) :
    ∃! g : Lp ℂ 2 μ, (∀ f, Φ f = ∫ x, f x * g x ∂μ) ∧ ‖Φ‖ = ‖g‖ := by
  let y := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm Φ
  have hre : ∀ f, Φ f = ∫ x, f x * (star y) x ∂μ := by
    intro f
    calc
      Φ f = inner ℂ y f := InnerProductSpace.toDual_symm_apply.symm
      _ = inner ℂ (star (star y)) f := by rw [star_star]
      _ = ∫ x, f x * (star y) x ∂μ := inner_star_lp_two μ (star y) f
  refine ⟨star y, ⟨hre, ?_⟩, ?_⟩
  · rw [norm_star_lp_two]
    exact ((InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm.norm_map Φ).symm
  · intro g hg
    apply star_injective
    apply (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).injective
    ext f
    simpa only [InnerProductSpace.toDual_apply_apply, inner_star_lp_two] using
      (hg.1 f).symm.trans (hre f)

#print axioms hilbert_lp_duality

end RudinRCA.Chapter06
-- END SOURCE RudinRCA/Chapter06.lean

-- BEGIN SOURCE DevelopmentImports.lean













-- Stable anticipated imports for the remaining Chapter 6 drafts.
-- END SOURCE DevelopmentImports.lean

-- BEGIN SOURCE Scratch69.lean













noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal MeasureTheory

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.9: strict bounds are pointwise, not only almost everywhere. -/
theorem lemma_6_9 (μ : Measure X) [SigmaFinite μ] :
    ∃ w : X → ℝ, Measurable w ∧ Integrable w μ ∧ ∀ x, 0 < w x ∧ w x < 1 := by
  obtain ⟨g, hgpos, hgmeas, hgint⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite μ (ε := ∞) (by simp)
  have hgi : Integrable (fun x ↦ (g x : ℝ)) μ := by
    simpa using integrable_toReal_of_lintegral_ne_top
      hgmeas.coe_nnreal_ennreal.aemeasurable hgint.ne
  refine ⟨fun x ↦ min (g x : ℝ) (1 / 2), hgmeas.coe_nnreal_real.min measurable_const, ?_, ?_⟩
  · apply hgi.mono' (hgmeas.coe_nnreal_real.min measurable_const).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (g x).coe_nonneg (by norm_num))]
    exact min_le_left _ _
  · intro x
    exact ⟨lt_min (hgpos x) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩

/-- The consequence following 6.9: a finite measure with exactly the same null sets. -/
theorem lemma_6_9_equivalent_finite_measure (μ : Measure X) [SigmaFinite μ] :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ ∀ E, ν E = 0 ↔ μ E = 0 := by
  obtain ⟨w, hwm, hwi, hw⟩ := lemma_6_9 μ
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
  have hfinite : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all μ fun x ↦ (hw x).1.le)]
    exact ENNReal.ofReal_ne_top)
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hrev : μ ≪ ν := withDensity_absolutelyContinuous' hwm.ennreal_ofReal.aemeasurable
    (ae_of_all μ fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hw x).1)
  exact ⟨ν, hfinite, fun E ↦ ⟨fun hz ↦ hrev hz, fun hz ↦ hac hz⟩⟩

private theorem complexDensity_ac (μ : Measure X) {f : X → ℂ} (hf : Integrable f μ) :
    μ.withDensityᵥ f ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  rw [withDensityᵥ_apply hf hs, Measure.restrict_zero_set hzero, integral_zero_measure]

private theorem complex_rn_measurable (c : ComplexMeasure X) (μ : Measure X) :
    Measurable (c.rnDeriv μ) :=
  Complex.equivRealProdCLM.symm.continuous.measurable.comp
    ((c.re.measurable_rnDeriv μ).prodMk (c.im.measurable_rnDeriv μ))

/-- Complex Radon–Nikodym reconstruction, used in Rudin 6.10 and 6.12. -/
theorem complex_rn_reconstruction (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ]
    (hc : c ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (c.rnDeriv μ) = c := by
  obtain ⟨hr, hi⟩ := (c.absolutelyContinuous_ennreal_iff μ.toENNRealVectorMeasure).mp hc
  have hfr := SignedMeasure.withDensityᵥ_rnDeriv_eq c.re μ hr
  have hfi := SignedMeasure.withDensityᵥ_rnDeriv_eq c.im μ hi
  ext s hs
  apply Complex.ext
  · rw [withDensityᵥ_apply (c.integrable_rnDeriv μ) hs,
      ← RCLike.re_eq_complex_re, ← integral_re (c.integrable_rnDeriv μ).integrableOn]
    change (∫ x in s, c.re.rnDeriv μ x ∂μ) = c.re s
    rw [← withDensityᵥ_apply (c.re.integrable_rnDeriv μ) hs, hfr]
  · rw [withDensityᵥ_apply (c.integrable_rnDeriv μ) hs,
      ← RCLike.im_eq_complex_im, ← integral_im (c.integrable_rnDeriv μ).integrableOn]
    change (∫ x in s, c.im.rnDeriv μ x ∂μ) = c.im s
    rw [← withDensityᵥ_apply (c.im.integrable_rnDeriv μ) hs, hfi]

private theorem complex_singularPart_singular (c : ComplexMeasure X) (μ : Measure X) :
    c.singularPart μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  obtain ⟨A, hA, hr, hμA⟩ := c.re.mutuallySingular_singularPart μ
  obtain ⟨B, hB, hi, hμB⟩ := c.im.mutuallySingular_singularPart μ
  apply VectorMeasure.MutuallySingular.mk (A ∩ B) (hA.inter hB)
  · intro E hE _
    change Complex.mk (c.re.singularPart μ E) (c.im.singularPart μ E) = 0
    rw [hr E (hE.trans inter_subset_left), hi E (hE.trans inter_subset_right)]
    rfl
  · intro E hE hEm
    rw [Measure.toENNRealVectorMeasure_apply_measurable hEm]
    have hAz : μ Aᶜ = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA.compl] using
        hμA Aᶜ Subset.rfl
    have hBz : μ Bᶜ = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hB.compl] using
        hμB Bᶜ Subset.rfl
    apply measure_mono_null hE
    rw [compl_inter]
    exact measure_union_null hAz hBz

private theorem complex_ac_singular_zero (c : ComplexMeasure X) (μ : Measure X)
    (hac : c ≪ᵥ μ.toENNRealVectorMeasure) (hsing : c ⟂ᵥ μ.toENNRealVectorMeasure) :
    c = 0 := eq_zero_of_ac_of_singular hac hsing

/-- The unique pair in the complex Lebesgue decomposition of Rudin 6.10(a). -/
theorem theorem_6_10_lebesgue (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ] :
    ∃! d : ComplexMeasure X × ComplexMeasure X,
      d.1 + d.2 = c ∧ d.1 ≪ᵥ μ.toENNRealVectorMeasure ∧
        d.2 ⟂ᵥ μ.toENNRealVectorMeasure := by
  letI : c.HaveLebesgueDecomposition μ := ⟨inferInstance, inferInstance⟩
  let a := μ.withDensityᵥ (c.rnDeriv μ)
  let s := c.singularPart μ
  have ha : a ≪ᵥ μ.toENNRealVectorMeasure := complexDensity_ac μ (c.integrable_rnDeriv μ)
  have hs : s ⟂ᵥ μ.toENNRealVectorMeasure := complex_singularPart_singular c μ
  have heq : a + s = c := by
    rw [add_comm]
    exact ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq (c := c) (μ := μ)
  refine ⟨(a, s), ⟨heq, ha, hs⟩, ?_⟩
  rintro ⟨a', s'⟩ ⟨heq', ha', hs'⟩
  have hdiff : a' - a = s - s' := by
    have := heq'.trans heq.symm
    dsimp at this
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using this)
  have hz : a' - a = 0 := complex_ac_singular_zero (a' - a) μ
    (ha'.sub ha) (by rw [hdiff]; exact hs.add_left hs'.neg_left)
  have haa : a' = a := sub_eq_zero.mp hz
  apply Prod.ext haa
  dsimp at heq'
  rw [haa, heq.symm] at heq'
  exact add_left_cancel heq'

/-- The positive finite clause of 6.10(a), stated in the positive-measure type. -/
theorem theorem_6_10_positive (ρ μ : Measure X) [IsFiniteMeasure ρ] [SigmaFinite μ] :
    ∃! d : Measure X × Measure X,
      IsFiniteMeasure d.1 ∧ IsFiniteMeasure d.2 ∧ d.1 + d.2 = ρ ∧
        d.1 ≪ μ ∧ d.2.MutuallySingular μ := by
  refine ⟨(μ.withDensity (ρ.rnDeriv μ), ρ.singularPart μ),
    ⟨inferInstance, inferInstance, ρ.rnDeriv_add_singularPart μ,
      withDensity_absolutelyContinuous _ _, ρ.mutuallySingular_singularPart μ⟩, ?_⟩
  rintro ⟨a, s⟩ ⟨ha, hs, heq, hac, hsing⟩
  letI : IsFiniteMeasure a := ha
  have haeq : μ.withDensity (a.rnDeriv μ) = a := Measure.withDensity_rnDeriv_eq a μ hac
  have hdecomp : ρ = s + μ.withDensity (a.rnDeriv μ) := by
    rw [haeq, add_comm]
    exact heq.symm
  apply Prod.ext
  · rw [← haeq]
    exact Measure.eq_withDensity_rnDeriv (a.measurable_rnDeriv μ) hsing hdecomp
  · exact Measure.eq_singularPart (a.measurable_rnDeriv μ) hsing hdecomp

/-- The Radon–Nikodym part of 6.10, including uniqueness modulo null sets. -/
theorem theorem_6_10_radon_nikodym (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ]
    (hc : c ≪ᵥ μ.toENNRealVectorMeasure) :
    ∃ h : X → ℂ, Measurable h ∧ Integrable h μ ∧
      (∀ E, MeasurableSet E → c E = ∫ x in E, h x ∂μ) ∧
      ∀ g : X → ℂ, Integrable g μ →
        (∀ E, MeasurableSet E → c E = ∫ x in E, g x ∂μ) → g =ᵐ[μ] h := by
  refine ⟨c.rnDeriv μ, complex_rn_measurable c μ, c.integrable_rnDeriv μ, ?_, ?_⟩
  · intro E hE
    calc
      c E = (μ.withDensityᵥ (c.rnDeriv μ)) E :=
        congrArg (fun v : ComplexMeasure X ↦ v E) (complex_rn_reconstruction c μ hc).symm
      _ = ∫ x in E, c.rnDeriv μ x ∂μ := withDensityᵥ_apply (c.integrable_rnDeriv μ) hE
  · intro g hg hge
    apply hg.ae_eq_of_withDensityᵥ_eq (c.integrable_rnDeriv μ)
    rw [complex_rn_reconstruction c μ hc]
    ext E hE
    rw [withDensityᵥ_apply hg hE, ← hge E hE]

private theorem finite_measure_uniform_ac (ν μ : Measure X) [IsFiniteMeasure ν]
    (hac : ∀ E, MeasurableSet E → μ E = 0 → ν E = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ ∀ E, MeasurableSet E → μ E < δ → ν E < ε := by
  classical
  by_contra h
  push_neg at h
  have hseq : ∀ n : ℕ, ∃ E : Set X, MeasurableSet E ∧
      μ E < (2 : ℝ≥0∞)⁻¹ ^ n ∧ ε ≤ ν E := by
    intro n
    exact h ((2 : ℝ≥0∞)⁻¹ ^ n) (pow_ne_zero _ (by simp))
  choose E hEm hEμ hEν using hseq
  let A : ℕ → Set X := fun n ↦ ⋃ k ≥ n, E k
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦ .iUnion fun k ↦ .iUnion fun _ ↦ hEm k
  have hanti : Antitone A := by
    intro n m hnm x hx
    obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨k, hnm.trans hk, hx⟩
  have hμzero : μ (⋂ n, A n) = 0 := by
    have hs : ∑' n, μ (E n) ≠ ∞ :=
      ne_top_of_le_ne_top (by
        simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
          (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞))
        (ENNReal.tsum_le_tsum fun n ↦ (hEμ n).le)
    simpa only [limsup_eq_iInf_iSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter, A] using
      (measure_limsup_atTop_eq_zero (μ := μ) hs)
  have hνzero := hac (⋂ n, A n) (.iInter hAm) hμzero
  have heps : ε ≤ ν (⋂ n, A n) := by
    rw [hanti.measure_iInter (fun n ↦ (hAm n).nullMeasurableSet)
      ⟨0, measure_ne_top ν (A 0)⟩]
    apply le_iInf
    intro n
    exact (hEν n).trans (measure_mono (fun x hx ↦ mem_iUnion₂.mpr ⟨n, le_rfl, hx⟩))
  exact hε (le_zero_iff.mp (hνzero ▸ heps))

/-- Rudin 6.11. ENNReal epsilon/delta is equivalent to the usual positive-real form;
the positive reference measure is arbitrary and need not be sigma-finite. -/
theorem theorem_6_11_of_finite_variation (c : ComplexMeasure X)
    [IsFiniteMeasure c.variation] (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
        ∀ E, MeasurableSet E → μ E < δ → ‖c E‖ₑ < ε := by
  constructor
  · intro hac ε hε
    have hvac : ∀ E, MeasurableSet E → μ E = 0 → c.variation E = 0 := by
      intro E hE hz
      apply (VectorMeasure.variation_apply_eq_zero (μ := c) hE).mpr
      intro F hFE hF
      apply hac
      rw [Measure.toENNRealVectorMeasure_apply_measurable hF]
      exact measure_mono_null hFE hz
    obtain ⟨δ, hδ, hbound⟩ := finite_measure_uniform_ac c.variation μ hvac ε hε
    refine ⟨δ, hδ, fun E hE hμE ↦ ?_⟩
    exact (c.enorm_measure_le_variation E).trans_lt (hbound E hE hμE)
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro E hE hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hz
    by_contra hc
    obtain ⟨δ, hδ, hbound⟩ := h ‖c E‖ₑ (by simpa using hc)
    exact (lt_irrefl ‖c E‖ₑ) (hbound E hE (hz ▸ bot_lt_iff_ne_bot.mpr hδ))

/-- The literal positive-real epsilon/delta formulation of Rudin 6.11. -/
theorem theorem_6_11_real_of_finite_variation (c : ComplexMeasure X)
    [IsFiniteMeasure c.variation] (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖c E‖ < ε := by
  constructor
  · intro hac ε hε
    obtain ⟨δ, hδ, hbound⟩ := (theorem_6_11_of_finite_variation c μ).mp hac
      (ENNReal.ofReal ε) (ENNReal.ofReal_ne_zero_iff.mpr hε)
    let d := min δ 1
    have hd0 : d ≠ 0 := ne_of_gt (lt_min (bot_lt_iff_ne_bot.mpr hδ) zero_lt_one)
    have hdt : d ≠ ∞ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    refine ⟨d.toReal, ENNReal.toReal_pos hd0 hdt, ?_⟩
    intro E hE hμE
    rw [ENNReal.ofReal_toReal hdt] at hμE
    have hb := hbound E hE (hμE.trans_le (min_le_left _ _))
    rw [← ofReal_norm] at hb
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hb
  · intro h
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro E hE hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hz
    by_contra hc
    obtain ⟨δ, hδ, hbound⟩ := h ‖c E‖ (norm_pos_iff.mpr hc)
    exact (lt_irrefl ‖c E‖) (hbound E hE (hz ▸ ENNReal.ofReal_pos.mpr hδ))

/-- Rudin 6.13 as equality of positive measures; applies without sigma-finiteness. -/
theorem theorem_6_13 (μ : Measure X) {g : X → ℂ} (hg : Integrable g μ) :
    (μ.withDensityᵥ g).variation = μ.withDensity (fun x ↦ ‖g x‖ₑ) :=
  Measure.variation_withDensityᵥ hg

/-- The setwise real-integral formula printed in 6.13. -/
theorem theorem_6_13_apply (μ : Measure X) {g : X → ℂ} (hg : Integrable g μ)
    (E : Set X) (hE : MeasurableSet E) :
    (μ.withDensityᵥ g).variation.real E = ∫ x in E, ‖g x‖ ∂μ := by
  rw [theorem_6_13 μ hg, measureReal_def, withDensity_apply _ hE]
  exact (integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable.restrict).symm

/-- Polar decomposition; the finite-variation instance is discharged by 6.4 at integration. -/
theorem theorem_6_12_of_finite_variation (c : ComplexMeasure X) [IsFiniteMeasure c.variation] :
    ∃ h : X → ℂ, Measurable h ∧ (∀ x, ‖h x‖ = 1) ∧
      Integrable h c.variation ∧ c.variation.withDensityᵥ h = c := by
  classical
  let f := c.rnDeriv c.variation
  have hf : Measurable f := complex_rn_measurable c c.variation
  have hfi : Integrable f c.variation := c.integrable_rnDeriv c.variation
  have hrep : c.variation.withDensityᵥ f = c :=
    complex_rn_reconstruction c c.variation c.absolutelyContinuous
  have heq : c.variation.withDensity (fun x ↦ ‖f x‖ₑ) = c.variation.withDensity 1 := by
    rw [withDensity_one, ← theorem_6_13 c.variation hfi, hrep]
  have heqae : (fun x ↦ ‖f x‖ₑ) =ᵐ[c.variation] (1 : X → ℝ≥0∞) :=
    (withDensity_eq_iff_of_sigmaFinite hf.enorm.aemeasurable measurable_const.aemeasurable).mp heq
  have hnorm : ∀ᵐ x ∂c.variation, ‖f x‖ = 1 := by
    filter_upwards [heqae] with x hx
    have hx' := congrArg ENNReal.toReal hx
    simpa using hx'
  let h : X → ℂ := fun x ↦ if ‖f x‖ = 1 then f x else 1
  have hmeas : Measurable h := Measurable.ite
    (measurableSet_eq_fun hf.norm measurable_const) hf measurable_const
  have hhae : h =ᵐ[c.variation] f := by
    filter_upwards [hnorm] with x hx
    simp [h, hx]
  refine ⟨h, hmeas, ?_, hfi.congr hhae.symm, ?_⟩
  · intro x
    by_cases hx : ‖f x‖ = 1 <;> simp [h, hx]
  · rw [WithDensityᵥEq.congr_ae hhae, hrep]

/-- Rudin 6.11, with finite variation supplied by the proved theorem 6.4. -/
theorem theorem_6_11 (c : ComplexMeasure X) (μ : Measure X) :
    c ≪ᵥ μ.toENNRealVectorMeasure ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖c E‖ < ε :=
  theorem_6_11_real_of_finite_variation c μ

/-- Rudin 6.12, for every complex measure, with modulus one everywhere. -/
theorem theorem_6_12 (c : ComplexMeasure X) :
    ∃ h : X → ℂ, Measurable h ∧ (∀ x, ‖h x‖ = 1) ∧
      Integrable h c.variation ∧ c.variation.withDensityᵥ h = c :=
  theorem_6_12_of_finite_variation c

/-- Rudin 6.14: the partition realizes the canonical positive/negative variations. -/
theorem theorem_6_14 (s : SignedMeasure X) :
    ∃ A B : Set X, MeasurableSet A ∧ MeasurableSet B ∧ A ∪ B = univ ∧ Disjoint A B ∧
      ∀ E, MeasurableSet E →
        s.toJordanDecomposition.posPart.real E = s (E ∩ A) ∧
        s.toJordanDecomposition.negPart.real E = -s (E ∩ B) := by
  obtain ⟨A, hA, hpos, hneg, hP, hN⟩ := s.toJordanDecomposition_spec
  refine ⟨A, Aᶜ, hA, hA.compl, union_compl_self A, disjoint_compl_right, ?_⟩
  intro E hE
  rw [hP, hN, s.toMeasureOfZeroLE_real_apply hpos hA hE,
    s.toMeasureOfLEZero_real_apply hneg hA.compl hE]
  simp [inter_comm]

/-- The minimum property in the corollary to 6.14. -/
theorem theorem_6_14_minimal (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : SignedMeasure X) (hs : s = μ.toSignedMeasure - ν.toSignedMeasure) :
    s.toJordanDecomposition.posPart ≤ μ ∧ s.toJordanDecomposition.negPart ≤ ν := by
  rw [hs, Measure.toJordanDecomposition_toSignedMeasure_sub]
  exact ⟨Measure.sub_le, Measure.sub_le⟩

/-- Rudin 6.15: the integral pairing gives a bounded functional, with the Hölder norm bound. -/
theorem theorem_6_15 (μ : Measure X) (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (g : Lp ℂ q μ) :
    ∃ Φ : Lp ℂ p μ →L[ℂ] ℂ,
      (∀ f, Φ f = ∫ x, f x * g x ∂μ) ∧ ‖Φ‖ ≤ ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Φ := B.lpPairing μ q p g
  refine ⟨Φ, ?_, ?_⟩
  · intro f
    simpa only [B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral g f
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    intro f
    have hvalue : Φ f = L1.integral (B.holder 1 g f) := by
      change L1.integralCLM' ℂ (B.holder 1 g f) = L1.integral (B.holder 1 g f)
      exact (L1.integral_eq' ℂ _).symm
    rw [hvalue]
    calc
      ‖L1.integral (B.holder 1 g f)‖ ≤ ‖B.holder 1 g f‖ := L1.norm_integral_le _
      _ ≤ ‖B‖ * ‖g‖ * ‖f‖ := B.norm_holder_apply_apply_le g f
      _ ≤ 1 * ‖g‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) (norm_nonneg g))
          (norm_nonneg f)
      _ = ‖g‖ * ‖f‖ := by rw [one_mul]

/-- The standard vector-measure integral specialized to complex multiplication.
The remaining 6.18 obligation is to identify this with Rudin's polar-density definition. -/
def complexIntegral (c : ComplexMeasure X) (f : X → ℂ) : ℂ :=
  ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c]

/-- The indicator identity in 6.18, for the standard complex vector integral. -/
theorem theorem_6_18_indicator (c : ComplexMeasure X) [IsFiniteMeasure c.variation]
    (E : Set X) (hE : MeasurableSet E) :
    complexIntegral c (E.indicator (fun _ ↦ (1 : ℂ))) = c E := by
  simpa only [complexIntegral, ContinuousLinearMap.mul_apply', one_mul] using
    (VectorMeasure.integral_indicator_const (μ := c) (B := ContinuousLinearMap.mul ℝ ℂ) 1 hE)

/-- The measure-addition identity in 6.18 for every bounded measurable function. -/
theorem theorem_6_18_add (c d : ComplexMeasure X)
    [IsFiniteMeasure c.variation] [IsFiniteMeasure d.variation]
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    complexIntegral (c + d) f = complexIntegral c f + complexIntegral d f := by
  have hc : c.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hd : d.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  exact VectorMeasure.integral_add_vectorMeasure hc hd

/-- The total-variation bound underlying 6.18's bounded-functional assertion. -/
theorem theorem_6_18_bound (c : ComplexMeasure X) [IsFiniteMeasure c.variation]
    (f : X → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖complexIntegral c f‖ ≤ C * c.variation.real univ := by
  calc
    ‖complexIntegral c f‖ ≤
        C * ‖ContinuousLinearMap.mul ℝ ℂ‖ * c.variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ hC)
    _ ≤ C * 1 * c.variation.real univ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) hC0)
        ENNReal.toReal_nonneg
    _ = C * c.variation.real univ := by rw [mul_one]

/-- The bounded complex functional in 6.18, expressed using the printed polar integral. -/
theorem theorem_6_18_polar_functional [TopologicalSpace X] [BorelSpace X]
    (c : ComplexMeasure X) (h : X → ℂ) (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1) :
    ∃ Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ,
      (∀ f, Φ f = ∫ x, f x * h x ∂c.variation) ∧ ‖Φ‖ ≤ c.variation.real univ := by
  have hnorm (f : ZeroAtInftyContinuousMap X ℂ) (x : X) : ‖f x * h x‖ ≤ ‖f‖ := by
    rw [norm_mul, hn, mul_one]
    exact f.toBCF.norm_coe_le_norm x
  have hi (f : ZeroAtInftyContinuousMap X ℂ) :
      Integrable (fun x ↦ f x * h x) c.variation :=
    Integrable.of_bound (f.continuous.measurable.mul hm).aestronglyMeasurable ‖f‖
      (ae_of_all _ (hnorm f))
  let L : ZeroAtInftyContinuousMap X ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f x * h x ∂c.variation
      map_add' := by
        intro f g
        change (∫ x, (f x + g x) * h x ∂c.variation) = _
        simp_rw [add_mul]
        exact integral_add (hi f) (hi g)
      map_smul' := by
        intro z f
        change (∫ x, (z * f x) * h x ∂c.variation) = z * _
        simp_rw [mul_assoc]
        exact integral_const_mul z _ }
  have hbound (f : ZeroAtInftyContinuousMap X ℂ) :
      ‖L f‖ ≤ c.variation.real univ * ‖f‖ := by
    change ‖∫ x, f x * h x ∂c.variation‖ ≤ _
    simpa only [mul_comm] using
      (norm_integral_le_of_norm_le_const (ae_of_all c.variation (hnorm f)))
  exact ⟨L.mkContinuous (c.variation.real univ) hbound, fun _ ↦ rfl,
    L.mkContinuous_norm_le ENNReal.toReal_nonneg hbound⟩

end RudinRCA.Chapter06

#print axioms RudinRCA.Chapter06.lemma_6_9
#print axioms RudinRCA.Chapter06.lemma_6_9_equivalent_finite_measure
#print axioms RudinRCA.Chapter06.complex_rn_reconstruction
#print axioms RudinRCA.Chapter06.theorem_6_10_lebesgue
#print axioms RudinRCA.Chapter06.theorem_6_10_positive
#print axioms RudinRCA.Chapter06.theorem_6_10_radon_nikodym
#print axioms RudinRCA.Chapter06.theorem_6_11_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_11_real_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_11
#print axioms RudinRCA.Chapter06.theorem_6_12_of_finite_variation
#print axioms RudinRCA.Chapter06.theorem_6_12
#print axioms RudinRCA.Chapter06.theorem_6_13
#print axioms RudinRCA.Chapter06.theorem_6_13_apply
#print axioms RudinRCA.Chapter06.theorem_6_14
#print axioms RudinRCA.Chapter06.theorem_6_14_minimal
#print axioms RudinRCA.Chapter06.theorem_6_15
#print axioms RudinRCA.Chapter06.theorem_6_18_indicator
#print axioms RudinRCA.Chapter06.theorem_6_18_add
#print axioms RudinRCA.Chapter06.theorem_6_18_bound
#print axioms RudinRCA.Chapter06.theorem_6_18_polar_functional
-- END SOURCE Scratch69.lean

-- BEGIN SOURCE Scratch63.lean









open Real Complex Set MeasureTheory
open scoped BigOperators

namespace RCA63

lemma integral_pos_cos :
    (∫ t in (-(Real.pi / 2))..(Real.pi + Real.pi / 2), max (Real.cos t) 0) = 2 := by
  have hc : Continuous (fun t : ℝ => max (Real.cos t) 0) :=
    Real.continuous_cos.max continuous_const
  have h₁ : (∫ t in (-(Real.pi / 2))..(Real.pi / 2), max (Real.cos t) 0) = 2 := by
    calc
      _ = ∫ t in (-(Real.pi / 2))..(Real.pi / 2), Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact max_eq_left (Real.cos_nonneg_of_mem_Icc ht)
      _ = 2 := by rw [integral_cos]; simp only [Real.sin_pi_div_two, Real.sin_neg]; norm_num
  have h₂ : (∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), max (Real.cos t) 0) = 0 := by
    calc
      _ = ∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact max_eq_right (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 ht.2)
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h₁, h₂, add_zero]

lemma integral_pos_cos_shift (a : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), max (Real.cos (t - a)) 0) = 2 := by
  have hp : Function.Periodic (fun t : ℝ => max (Real.cos t) 0) (2 * Real.pi) :=
    fun t => by
      change max (Real.cos (t + 2 * Real.pi)) 0 = max (Real.cos t) 0
      rw [Real.cos_add_two_pi]
  calc
    _ = ∫ t in (-a)..(-a + 2 * Real.pi), max (Real.cos t) 0 := by
      simpa only [zero_sub, sub_eq_add_neg, add_comm, add_zero] using
        intervalIntegral.integral_comp_sub_right
          (fun t : ℝ => max (Real.cos t) 0) (a := 0) (b := 2 * Real.pi) a
    _ = ∫ t in (-(Real.pi / 2))..(-(Real.pi / 2) + 2 * Real.pi),
        max (Real.cos t) 0 := hp.intervalIntegral_add_eq (-a) (-(Real.pi / 2))
    _ = ∫ t in (-(Real.pi / 2))..(Real.pi + Real.pi / 2), max (Real.cos t) 0 := by
      congr 1 <;> ring
    _ = 2 := integral_pos_cos

lemma projection_arg (z : ℂ) (t : ℝ) :
    (Complex.exp (-(t : ℂ) * Complex.I) * z).re =
      ‖z‖ * Real.cos (t - Complex.arg z) := by
  calc
    _ = Real.cos t * z.re + Real.sin t * z.im := by
      rw [Complex.mul_re, Complex.exp_re, Complex.exp_im]
      simp [Complex.mul_im, Complex.mul_re]
    _ = Real.cos t * (‖z‖ * Real.cos (Complex.arg z)) +
        Real.sin t * (‖z‖ * Real.sin (Complex.arg z)) := by
      rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    _ = ‖z‖ * Real.cos (t - Complex.arg z) := by
      rw [Real.cos_sub]
      ring

lemma integral_pos_projection (z : ℂ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      max (Complex.exp (-(t : ℂ) * Complex.I) * z).re 0) = 2 * ‖z‖ := by
  simp_rw [projection_arg]
  have heq : (fun t : ℝ => max (‖z‖ * Real.cos (t - Complex.arg z)) 0) =
      (fun t : ℝ => ‖z‖ * max (Real.cos (t - Complex.arg z)) 0) := by
    funext t
    rw [mul_max_of_nonneg _ _ (norm_nonneg z), mul_zero]
  rw [heq, intervalIntegral.integral_const_mul, integral_pos_cos_shift]
  ring

lemma projection_continuous (z : ℂ) :
    Continuous (fun t : ℝ => max (Complex.exp (-(t : ℂ) * Complex.I) * z).re 0) := by
  simp_rw [projection_arg]
  fun_prop

theorem exists_subset_sum_norm {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ S ⊆ s, (∑ i ∈ s, ‖z i‖) / Real.pi ≤ ‖∑ i ∈ S, z i‖ := by
  classical
  obtain ⟨S, hS, hmax⟩ := s.powerset.exists_max_image
    (fun S : Finset ι => ‖∑ i ∈ S, z i‖) ⟨∅, by simp⟩
  refine ⟨S, Finset.mem_powerset.mp hS, ?_⟩
  have hbound (t : ℝ) :
      (∑ i ∈ s, max (Complex.exp (-(t : ℂ) * Complex.I) * z i).re 0) ≤
        ‖∑ i ∈ S, z i‖ := by
    let u : ℂ := Complex.exp (-(t : ℂ) * Complex.I)
    let T := s.filter (fun i => 0 ≤ (u * z i).re)
    have hT : T ⊆ s := Finset.filter_subset _ _
    have heq : (∑ i ∈ s, max (u * z i).re 0) = (u * ∑ i ∈ T, z i).re := by
      simp only [Finset.mul_sum, Complex.re_sum, T, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with h
      · exact max_eq_left h
      · simpa only [mul_zero, Complex.zero_re] using max_eq_right (le_of_not_ge h)
    calc
      _ = (u * ∑ i ∈ T, z i).re := heq
      _ ≤ ‖u * ∑ i ∈ T, z i‖ := Complex.re_le_norm _
      _ = ‖∑ i ∈ T, z i‖ := by simp [u, Complex.norm_exp]
      _ ≤ ‖∑ i ∈ S, z i‖ := hmax T (Finset.mem_powerset.mpr hT)
  have hcont : Continuous (fun t : ℝ =>
      ∑ i ∈ s, max (Complex.exp (-(t : ℂ) * Complex.I) * z i).re 0) :=
    continuous_finsetSum _ fun i hi => projection_continuous (z i)
  have hint := intervalIntegral.integral_mono (μ := volume) (a := 0) (b := 2 * Real.pi)
    (by positivity) (hcont.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_finsetSum
    (fun i hi => (projection_continuous (z i)).intervalIntegrable _ _)] at hint
  simp_rw [integral_pos_projection] at hint
  rw [← Finset.mul_sum] at hint
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith

#print axioms exists_subset_sum_norm
end RCA63
-- END SOURCE Scratch63.lean

-- BEGIN SOURCE Scratch618Extension.lean







open Set Filter
open scoped Topology ZeroAtInfty

noncomputable section

namespace RCA618

variable (X : Type*) [TopologicalSpace X]

/-- The compactly supported continuous functions, equipped with their inherited supremum norm. -/
def compactSupportSubmodule : Submodule ℂ C₀(X, ℂ) where
  carrier := {f | HasCompactSupport (f : X → ℂ)}
  zero_mem' := by
    change HasCompactSupport (fun _ : X => (0 : ℂ))
    exact HasCompactSupport.zero
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change HasCompactSupport (fun x : X => c • f x)
    exact HasCompactSupport.smul_left (f := fun _ : X => c) hf

local instance compactSupportSubmoduleNormedAddCommGroup :
    NormedAddCommGroup (compactSupportSubmodule X) :=
  Submodule.normedAddCommGroup _

local instance compactSupportSubmoduleNormedSpace :
    NormedSpace ℂ (compactSupportSubmodule X) :=
  Submodule.normedSpace _

variable [LocallyCompactSpace X] [T2Space X]

set_option maxHeartbeats 800000 in
/-- Cutoff approximation does not require sigma compactness or a countable basis. -/
theorem exists_compactSupport_approx (f : C₀(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C₀(X, ℂ), HasCompactSupport (g : X → ℂ) ∧ dist f g < ε := by
  have hev : ∀ᶠ x in cocompact X, dist (f x) 0 < ε / 2 :=
    Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (half_pos hε)
  obtain ⟨K, hK, hKf⟩ := mem_cocompact.mp hev
  obtain ⟨φ, hφK, hφcomp, _, hφrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
      (subset_univ K)
  have hgcomp : HasCompactSupport (fun x : X => φ x • f x) :=
    HasCompactSupport.smul_right hφcomp
  let g : C₀(X, ℂ) :=
    ⟨⟨fun x => φ x • f x, (map_continuous φ).smul (map_continuous f)⟩,
      hgcomp.is_zero_at_infty⟩
  refine ⟨g, hgcomp, ?_⟩
  have hbound (x : X) : ‖((f - g) : C₀(X, ℂ)) x‖ ≤ ε / 2 := by
    change ‖f x - φ x • f x‖ ≤ ε / 2
    by_cases hx : x ∈ K
    · have hφx : φ x = 1 := hφK hx
      simp only [hφx, one_smul, sub_self, norm_zero]
      exact (half_pos hε).le
    · have hfsmall : ‖f x‖ < ε / 2 := by
        simpa only [dist_zero_right, Set.mem_setOf_eq] using hKf hx
      have hφx := hφrange x
      have heq : f x - φ x • f x = (1 - φ x) • f x := by
        rw [sub_smul, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hφx.2)]
      exact (mul_le_of_le_one_left (norm_nonneg (f x)) (by linarith [hφx.1])).trans
        hfsmall.le
  have hn : ‖f - g‖ ≤ ε / 2 := by
    change ‖(f - g).toBCF‖ ≤ ε / 2
    exact (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr hbound
  rw [dist_eq_norm]
  exact hn.trans_lt (half_lt_self hε)

theorem dense_compactSupport :
    Dense {f : C₀(X, ℂ) | HasCompactSupport (f : X → ℂ)} := by
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨g, hg, hfg⟩ := exists_compactSupport_approx X f hε
  refine ⟨g, ?_, hg⟩
  simpa only [Metric.mem_ball, dist_comm] using hfg

/-- The extension assertion at the start of Rudin 6.18, with uniqueness and norm equality. -/
theorem exists_unique_extension
    (F : (compactSupportSubmodule X) →L[ℂ] ℂ) :
    ∃! G : C₀(X, ℂ) →L[ℂ] ℂ,
      (∀ f : compactSupportSubmodule X, G f = F f) ∧ ‖G‖ = ‖F‖ := by
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq (compactSupportSubmodule X) F
  refine ⟨G, ⟨hG, hnorm⟩, ?_⟩
  intro H hH
  apply DFunLike.ext'
  apply H.continuous.ext_on (dense_compactSupport X) G.continuous
  intro f hf
  exact (hH.1 ⟨f, hf⟩).trans (hG ⟨f, hf⟩).symm

#print axioms exists_unique_extension
end RCA618
-- END SOURCE Scratch618Extension.lean

-- BEGIN SOURCE Scratch618Polar.lean






noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06
variable {X : Type*} [MeasurableSpace X]

/-- The native vector integral agrees with the polar-density definition in 6.18.
This statement works for every choice of a measurable unit polar density. -/
theorem vectorIntegral_eq_polar (c : ComplexMeasure X) (h : X → ℂ)
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1)
    (hi : Integrable h c.variation) (hr : c.variation.withDensityᵥ h = c)
    {f : X → ℂ} (hf : Integrable f c.variation) :
    (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c]) =
      ∫ x, f x * h x ∂c.variation := by
  let B := ContinuousLinearMap.mul ℝ ℂ
  have hb : ∀ᵐ x ∂c.variation, ‖h x‖ ≤ 1 := ae_of_all _ fun x ↦ (hn x).le
  have htop : MemLp h ∞ c.variation := memLp_top_of_bound hm.aestronglyMeasurable 1 hb
  let H : Lp ℂ ∞ c.variation := htop.toLp h
  have hH : (H : X → ℂ) =ᵐ[c.variation] h := htop.coeFn_toLp
  have hmul {f : X → ℂ} (hf : Integrable f c.variation) :
      Integrable (fun x ↦ f x * h x) c.variation :=
    hf.mul_bdd hm.aestronglyMeasurable hb
  have hcont : Continuous (fun f : Lp ℂ 1 c.variation ↦ ∫ x, f x * h x ∂c.variation) := by
    have heq : (fun f : Lp ℂ 1 c.variation ↦ ∫ x, f x * h x ∂c.variation) =
        fun f ↦ B.lpPairing c.variation ∞ 1 H f := by
      funext f
      rw [B.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      simp [B, hx, mul_comm]
    rw [heq]
    exact (B.lpPairing c.variation ∞ 1 H).continuous
  refine Integrable.induction
    (P := fun f ↦ (∫ᵛ x, f x ∂[B; c]) = ∫ x, f x * h x ∂c.variation)
    ?_ ?_ ?_ ?_ hf
  · intro z E hE _
    rw [VectorMeasure.integral_indicator_const z hE]
    change z * c E = _
    have hcE : c E = ∫ x in E, h x ∂c.variation := by
      calc
        c E = (c.variation.withDensityᵥ h) E :=
          congrArg (fun v : ComplexMeasure X ↦ v E) hr.symm
        _ = ∫ x in E, h x ∂c.variation := withDensityᵥ_apply hi hE
    rw [hcE]
    have hfun : (fun x ↦ E.indicator (fun _ ↦ z) x * h x) =
        E.indicator (fun x ↦ z * h x) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [hfun, integral_indicator hE, integral_const_mul]
  · intro f g _ hf hg hfe hge
    rw [VectorMeasure.integral_add hf hg, hfe, hge]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (hmul hf) (hmul hg)).symm
  · exact isClosed_eq VectorMeasure.continuous_integral hcont
  · intro f g hfg _ heq
    rw [← VectorMeasure.integral_congr_ae hfg, heq]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx using congrArg (· * h x) hx

#print axioms vectorIntegral_eq_polar
end RudinRCA.Chapter06
-- END SOURCE Scratch618Polar.lean

-- BEGIN SOURCE Scratch618Final.lean





noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.18: a complex Borel measure is regular precisely when its total
variation is regular. Under `BorelSpace X`, the underlying measurable sets are
the Borel sets. -/
def IsRegularComplexMeasure [TopologicalSpace X] (c : ComplexMeasure X) : Prop :=
  Measure.Regular c.variation

/-- The native complex integral defines the bounded complex functional on C0
asserted in 6.18, with the total-variation norm bound. -/
theorem theorem_6_18_functional [TopologicalSpace X] [BorelSpace X]
    (c : ComplexMeasure X) :
    ∃ Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ,
      (∀ f, Φ f = complexIntegral c f) ∧ ‖Φ‖ ≤ c.variation.real univ := by
  obtain ⟨h, hm, hn, hi, hr⟩ := theorem_6_12 c
  obtain ⟨Φ, hΦ, hbound⟩ := theorem_6_18_polar_functional c h hm hn
  refine ⟨Φ, ?_, hbound⟩
  intro f
  rw [hΦ]
  have hf : Integrable (fun x ↦ f x) c.variation :=
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  exact (vectorIntegral_eq_polar c h hm hn hi hr hf).symm

end RudinRCA.Chapter06

#print axioms RudinRCA.Chapter06.theorem_6_18_functional
-- END SOURCE Scratch618Final.lean

-- BEGIN SOURCE Scratch611Example.lean





noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RudinRCA.Chapter06

/-- Lebesgue measure on (0,1), extended by zero outside the interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

/-- The positive, unbounded measure used in the discussion of Rudin 6.11. -/
def inverseDensityMeasure : Measure ℝ :=
  unitIntervalMeasure.withDensity (fun x ↦ ENNReal.ofReal x⁻¹)

theorem inverseDensity_absolutelyContinuous :
    inverseDensityMeasure ≪ unitIntervalMeasure :=
  withDensity_absolutelyContinuous _ _

theorem inverseDensity_Ioo {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    inverseDensityMeasure (Ioo 0 a) = ∞ := by
  rw [inverseDensityMeasure, withDensity_apply _ measurableSet_Ioo,
    unitIntervalMeasure, Measure.restrict_restrict_of_subset (Ioo_subset_Ioo le_rfl ha1)]
  apply Classical.byContradiction
  intro hfinite
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ x⁻¹)
      (volume.restrict (Ioo 0 a)) := measurable_inv.aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 a)] (fun x : ℝ ↦ x⁻¹) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ (inv_pos.mpr hx.1).le
  have hi := (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hfinite
  have hr : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo 0 a) := by
    simpa only [IntegrableOn, Real.rpow_neg_one] using hi
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ha).mp hr
  exact (lt_irrefl (-1 : ℝ)) this

/-- Although absolutely continuous, this positive measure has infinite mass on
arbitrarily small intervals, so it fails the epsilon/delta criterion of 6.11. -/
theorem inverseDensity_fails_uniform_absoluteContinuity :
    ∀ δ : ℝ, 0 < δ → ∃ E : Set ℝ, MeasurableSet E ∧
      unitIntervalMeasure E < ENNReal.ofReal δ ∧ inverseDensityMeasure E = ∞ := by
  intro δ hδ
  let a := min (δ / 2) (1 / 2)
  have ha : 0 < a := lt_min (half_pos hδ) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have had : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨Ioo 0 a, measurableSet_Ioo, ?_, inverseDensity_Ioo ha ha1⟩
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo le_rfl ha1), Real.volume_Ioo, sub_zero]
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr had

#print axioms inverseDensity_absolutelyContinuous
#print axioms inverseDensity_Ioo
#print axioms inverseDensity_fails_uniform_absoluteContinuity
end RudinRCA.Chapter06
-- END SOURCE Scratch611Example.lean

-- BEGIN SOURCE Scratch610Discussion.lean







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
-- END SOURCE Scratch610Discussion.lean

-- BEGIN SOURCE Scratch611Completed.lean




noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RCA611Completed

open RCA610Discussion RudinRCA.Chapter06

/-- The inclusion from the completed open interval into the real line is
measurable: the completed domain sigma algebra contains the Borel sets. -/
theorem measurable_interval_val :
    Measurable (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) :=
  ((measurable_subtype_coe : Measurable (fun x : Ioo (0 : ℝ) 1 ↦ x.val)).nullMeasurable
    (μ := openIntervalVolume)).measurable'

/-- Completion and restriction give precisely the ambient restricted Lebesgue
measure under the inclusion map. This is the transfer bridge for the example. -/
theorem interval_val_measurePreserving :
    MeasurePreserving (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ))
      openIntervalLebesgue unitIntervalMeasure where
  measurable := measurable_interval_val
  map_eq := by
    ext E hE
    rw [Measure.map_apply measurable_interval_val hE, openIntervalLebesgue_apply,
      unitIntervalMeasure, Measure.restrict_apply hE, image_preimage_eq_inter_range]
    have hrange : Set.range (fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) =
        Ioo (0 : ℝ) 1 := Subtype.range_coe
    rw [hrange]

/-- The reciprocal density on the Lebesgue-completed open interval, as in the
discussion following Rudin 6.11. -/
def completedInverseDensity : Measure CompletedOpenUnitInterval :=
  openIntervalLebesgue.withDensity (fun x ↦ ENNReal.ofReal (x.val⁻¹))

theorem completedInverseDensity_absolutelyContinuous :
    completedInverseDensity ≪ openIntervalLebesgue :=
  withDensity_absolutelyContinuous _ _

/-- On every Borel test set, the density measure agrees with the ambient
inverse-density example under the inclusion. -/
theorem completedInverseDensity_preimage {E : Set ℝ} (hE : MeasurableSet E) :
    completedInverseDensity ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E) =
      inverseDensityMeasure E := by
  rw [completedInverseDensity,
    withDensity_apply _ (hE.preimage measurable_interval_val),
    inverseDensityMeasure, withDensity_apply _ hE]
  exact interval_val_measurePreserving.setLIntegral_comp_preimage hE
    measurable_inv.ennreal_ofReal

theorem completedInverseDensity_Ioo {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    completedInverseDensity
      ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' Ioo 0 a) = ∞ :=
  (completedInverseDensity_preimage measurableSet_Ioo).trans (inverseDensity_Ioo ha ha1)

/-- The exact completed-space counterexample: the positive measure is absolutely
continuous, but its mass is infinite on sets of arbitrarily small Lebesgue mass. -/
theorem completedInverseDensity_fails_uniform_absoluteContinuity :
    completedInverseDensity ≪ openIntervalLebesgue ∧
      ∀ δ : ℝ, 0 < δ → ∃ E : Set CompletedOpenUnitInterval, MeasurableSet E ∧
        openIntervalLebesgue E < ENNReal.ofReal δ ∧ completedInverseDensity E = ∞ := by
  refine ⟨completedInverseDensity_absolutelyContinuous, ?_⟩
  intro δ hδ
  obtain ⟨E, hE, hsmall, hinfty⟩ := inverseDensity_fails_uniform_absoluteContinuity δ hδ
  refine ⟨(fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E,
    hE.preimage measurable_interval_val, ?_, ?_⟩
  · have hmass : openIntervalLebesgue
        ((fun x : CompletedOpenUnitInterval ↦ (x.val : ℝ)) ⁻¹' E) = unitIntervalMeasure E := by
      rw [← Measure.map_apply measurable_interval_val hE, interval_val_measurePreserving.map_eq]
    exact hmass.symm ▸ hsmall
  · exact (completedInverseDensity_preimage hE).trans hinfty

#print axioms measurable_interval_val
#print axioms interval_val_measurePreserving
#print axioms completedInverseDensity_absolutelyContinuous
#print axioms completedInverseDensity_preimage
#print axioms completedInverseDensity_Ioo
#print axioms completedInverseDensity_fails_uniform_absoluteContinuity

end RCA611Completed
-- END SOURCE Scratch611Completed.lean

-- BEGIN SOURCE Scratch616.lean





/-!
Auxiliary construction for Rudin 6.16, for a finite positive measure.
This file proves only the construction of the absolutely continuous complex
measure E ↦ Φ(χ_E); it does not assert the Lp dual representation theorem.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff Function Classical

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The indicator of a measurable set in `Lp`, extended by zero on
nonmeasurable sets to conform to the vector-measure convention. -/
def finiteLpIndicator (E : Set X) : Lp ℂ p μ :=
  if hE : MeasurableSet E then
    indicatorConstLp p hE (measure_ne_top μ E) 1
  else 0

theorem finiteLpIndicator_measurable {E : Set X} (hE : MeasurableSet E) :
    finiteLpIndicator μ p E = indicatorConstLp p hE (measure_ne_top μ E) 1 := by
  simp only [finiteLpIndicator, dite_eq_left hE]

@[simp] theorem finiteLpIndicator_empty : finiteLpIndicator μ p ∅ = 0 := by
  rw [finiteLpIndicator_measurable μ p MeasurableSet.empty]
  exact indicatorConstLp_empty

theorem finiteLpIndicator_disjoint_union {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : Disjoint E F) :
    finiteLpIndicator μ p (E ∪ F) =
      finiteLpIndicator μ p E + finiteLpIndicator μ p F := by
  rw [finiteLpIndicator_measurable μ p (hE.union hF),
    finiteLpIndicator_measurable μ p hE, finiteLpIndicator_measurable μ p hF]
  exact indicatorConstLp_disjoint_union hE hF (measure_ne_top μ E)
    (measure_ne_top μ F) hEF 1

theorem finiteLpIndicator_finset_iUnion {E : ℕ → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (Disjoint on E)) (F : Finset ℕ) :
    finiteLpIndicator μ p (⋃ i ∈ F, E i) = ∑ i ∈ F, finiteLpIndicator μ p (E i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      have hU : MeasurableSet (⋃ j ∈ F, E j) :=
        MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hE j
      have hd : Disjoint (E i) (⋃ j ∈ F, E j) := by
        apply disjoint_iUnion_right.mpr
        intro j
        apply disjoint_iUnion_right.mpr
        intro hj
        exact hdisj (by intro hij; subst j; exact hi hj)
      have hset : (⋃ j ∈ insert i F, E j) = E i ∪ ⋃ j ∈ F, E j := by
        ext x
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨j, hj, hxj⟩
          rcases hj with rfl | hj
          · exact Or.inl hxj
          · exact Or.inr ⟨j, hj, hxj⟩
        · rintro (hxi | ⟨j, hj, hxj⟩)
          · exact ⟨i, Or.inl rfl, hxi⟩
          · exact ⟨j, Or.inr hj, hxj⟩
      rw [hset, finiteLpIndicator_disjoint_union μ p (hE i) hU hd, ih,
        Finset.sum_insert hi]

/-- Countable additivity of `Lp` indicators when `p < ∞`.
The proof uses convergence over all finite subsets, so the conclusion is
unconditional summability, as required by `VectorMeasure`. -/
theorem finiteLpIndicator_hasSum (hp : p ≠ ∞) {E : ℕ → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (Disjoint on E)) :
    HasSum (fun i => finiteLpIndicator μ p (E i))
      (finiteLpIndicator μ p (⋃ i, E i)) := by
  classical
  let U : Finset ℕ → Set X := fun F => ⋃ i ∈ F, E i
  let A : Set X := ⋃ i, E i
  have hA : MeasurableSet A := MeasurableSet.iUnion hE
  have hU : ∀ F, MeasurableSet (U F) := fun F =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hE i
  have hsub : ∀ F, U F ⊆ A := fun F =>
    iUnion₂_subset fun i _ => subset_iUnion E i
  have hmono : Monotone U := by
    intro F G hFG
    exact biUnion_subset_biUnion_left hFG
  have hanti : Antitone (fun F => A \ U F) := by
    intro F G hFG x hx
    exact ⟨hx.1, fun hxF => hx.2 (hmono hFG hxF)⟩
  have hinter : (⋂ F : Finset ℕ, A \ U F) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxA := (mem_iInter.mp hx ∅).1
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
    exact (mem_iInter.mp hx {i}).2 (by simpa [U] using hxi)
  have hlim : Tendsto (fun F : Finset ℕ => μ (A \ U F)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (μ := μ) (fun F => (hA.diff (hU F)).nullMeasurableSet) hanti
      ⟨∅, measure_ne_top μ _⟩
    simpa only [hinter, measure_empty, Function.comp_def] using h
  have hsymm : Tendsto (fun F : Finset ℕ => μ (U F ∆ A)) atTop (𝓝 0) := by
    simpa only [symmDiff_of_le (hsub _)] using hlim
  have hind := tendsto_indicatorConstLp_set
    (p := p) (μ := μ) (c := (1 : ℂ)) (hs := hA)
    (hμs := measure_ne_top μ A) (ht := hU)
    (hμt := fun F => measure_ne_top μ (U F)) hp hsymm
  change Tendsto (fun F : Finset ℕ => ∑ i ∈ F, finiteLpIndicator μ p (E i))
    atTop (𝓝 (finiteLpIndicator μ p A))
  have hsum : (fun F : Finset ℕ => ∑ i ∈ F, finiteLpIndicator μ p (E i)) =
      fun F => indicatorConstLp p (hU F) (measure_ne_top μ (U F)) (1 : ℂ) := by
    funext F
    rw [← finiteLpIndicator_finset_iUnion μ p hE hdisj F]
    exact finiteLpIndicator_measurable μ p (hU F)
  rw [hsum, finiteLpIndicator_measurable μ p hA]
  exact hind

/-- The vector measure taking a measurable set to its `Lp` indicator. -/
def finiteLpIndicatorVectorMeasure (hp : p ≠ ∞) : VectorMeasure X (Lp ℂ p μ) where
  measureOf' := finiteLpIndicator μ p
  empty' := finiteLpIndicator_empty μ p
  not_measurable' E hE := by simp only [finiteLpIndicator, dite_eq_right hE]
  m_iUnion' E hE hd := finiteLpIndicator_hasSum μ p hp hE hd

/-- The auxiliary complex measure in the finite-measure proof of Rudin 6.16. -/
def finiteLpFunctionalMeasure (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) : ComplexMeasure X :=
  VectorMeasure.mapRangeL Φ (finiteLpIndicatorVectorMeasure μ p hp)

theorem finiteLpFunctionalMeasure_apply (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {E : Set X} (hE : MeasurableSet E) :
    finiteLpFunctionalMeasure μ p hp Φ E =
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) := by
  change Φ (finiteLpIndicator μ p E) = _
  rw [finiteLpIndicator_measurable μ p hE]

theorem finiteLpFunctionalMeasure_norm_le (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {E : Set X} (hE : MeasurableSet E) :
    ‖finiteLpFunctionalMeasure μ p hp Φ E‖ ≤ ‖Φ‖ * μ.real E ^ (1 / p.toReal) := by
  rw [finiteLpFunctionalMeasure_apply μ p hp Φ hE]
  have hp0 : p ≠ 0 := (one_pos.trans_le (Fact.out : 1 ≤ p)).ne'
  calc
    ‖Φ (indicatorConstLp p hE (measure_ne_top μ E) 1)‖ ≤
        ‖Φ‖ * ‖indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ)‖ := Φ.le_opNorm _
    _ = ‖Φ‖ * μ.real E ^ (1 / p.toReal) := by rw [norm_indicatorConstLp hp0 hp]; simp

theorem finiteLpIndicator_eq_zero_of_measure_zero {E : Set X}
    (hE : MeasurableSet E) (hμE : μ E = 0) : finiteLpIndicator μ p E = 0 := by
  rw [finiteLpIndicator_measurable μ p hE]
  have heq := (indicatorConstLp_inj (p := p) hE (measure_ne_top μ E)
    MeasurableSet.empty (by simp : μ ∅ ≠ ∞) (one_ne_zero : (1 : ℂ) ≠ 0)).mpr
    (ae_eq_empty.mpr hμE)
  exact heq.trans indicatorConstLp_empty

theorem finiteLpFunctionalMeasure_absolutelyContinuous (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    finiteLpFunctionalMeasure μ p hp Φ ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro E hE hμE
  rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hμE
  change Φ (finiteLpIndicator μ p E) = 0
  rw [finiteLpIndicator_eq_zero_of_measure_zero μ p hE hμE, map_zero]

#print axioms finiteLpIndicator_hasSum
#print axioms finiteLpFunctionalMeasure_norm_le
#print axioms finiteLpFunctionalMeasure_absolutelyContinuous

end RudinRCA.Chapter06
-- END SOURCE Scratch616.lean

-- BEGIN SOURCE Scratch616B.lean




/-!
Auxiliary bounded-test extension for Rudin 6.16.
The indicator identity here is intended to be supplied by the complex
Radon–Nikodym theorem applied to `finiteLpFunctionalMeasure`.
No Lp dual representation theorem is claimed by this helper.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem lpFunctional_eq_simple_of_indicator
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ)
    (f : SimpleFunc X ℂ) :
    Φ ((f.memLp_of_isFiniteMeasure p μ).toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  have hint : ∀ k : SimpleFunc X ℂ, Integrable (fun x => k x * g x) μ := by
    intro k
    obtain ⟨C, hC⟩ := k.exists_forall_norm_le
    exact hg.bdd_mul k.aestronglyMeasurable (ae_of_all μ hC)
  induction f using SimpleFunc.induction with
  | @const c E hE =>
      let k : SimpleFunc X ℂ :=
        SimpleFunc.piecewise E hE (SimpleFunc.const X c) (SimpleFunc.const X 0)
      have hk : (k.memLp_of_isFiniteMeasure p μ).toLp k =
          c • indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ) := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (k.memLp_of_isFiniteMeasure p μ),
          Lp.coeFn_smul c (indicatorConstLp p hE (measure_ne_top μ E) (1 : ℂ)),
          (indicatorConstLp_coeFn (p := p) (hs := hE)
            (hμs := measure_ne_top μ E) (c := (1 : ℂ)))] with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃]
        by_cases hx : x ∈ E <;> simp [k, hx]
      change Φ ((k.memLp_of_isFiniteMeasure p μ).toLp k) = _
      rw [hk, map_smul, hind E hE, smul_eq_mul]
      have hfun : (fun x => k x * g x) = E.indicator (fun x => c * g x) := by
        funext x
        by_cases hx : x ∈ E <;> simp [k, hx]
      change c * (∫ x in E, g x ∂μ) = ∫ x, k x * g x ∂μ
      rw [hfun, integral_indicator hE, integral_const_mul]
  | @add f k hfk hf hk =>
      have hadd : ((f + k).memLp_of_isFiniteMeasure p μ).toLp (f + k) =
          (f.memLp_of_isFiniteMeasure p μ).toLp f +
            (k.memLp_of_isFiniteMeasure p μ).toLp k := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((f + k).memLp_of_isFiniteMeasure p μ),
          Lp.coeFn_add ((f.memLp_of_isFiniteMeasure p μ).toLp f)
            ((k.memLp_of_isFiniteMeasure p μ).toLp k),
          MemLp.coeFn_toLp (f.memLp_of_isFiniteMeasure p μ),
          MemLp.coeFn_toLp (k.memLp_of_isFiniteMeasure p μ)] with x h₁ h₂ h₃ h₄
        rw [h₁, h₂, Pi.add_apply, h₃, h₄]
        rfl
      rw [hadd, map_add, hf, hk]
      have hfun : (fun x => (f + k) x * g x) =
          (fun x => f x * g x + k x * g x) := by
        funext x
        exact add_mul (f x) (k x) (g x)
      rw [hfun, integral_add (hint f) (hint k)]

/-- Extend a functional's indicator identity to bounded measurable tests.
This does not assume that the candidate density is in the conjugate Lq space. -/
theorem lpFunctional_eq_bounded_of_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ)
    {f : X → ℂ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hfLp : MemLp f p μ) :
    Φ (hfLp.toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  let s : Set ℂ := range f ∪ {0}
  have h0 : (0 : ℂ) ∈ s := by simp [s]
  let F : ℕ → SimpleFunc X ℂ := fun n => SimpleFunc.approxOn f hf s 0 h0 n
  have hFp : ∀ n, MemLp (F n) p μ := fun n =>
    SimpleFunc.memLp_approxOn_range hf hfLp n
  have hLp : Tendsto (fun n => (hFp n).toLp (F n)) atTop (𝓝 (hfLp.toLp f)) :=
    SimpleFunc.tendsto_approxOn_range_Lp hp hf hfLp
  have hΦ := Φ.continuous.continuousAt.tendsto.comp hLp
  have hbound : ∀ n, ∀ x, ‖F n x‖ ≤ C + C := by
    intro n x
    exact (SimpleFunc.norm_approxOn_zero_le hf h0 x n).trans (add_le_add (hC x) (hC x))
  have hIntegral : Tendsto (fun n => ∫ x, F n x * g x ∂μ) atTop
      (𝓝 (∫ x, f x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (C + C) * ‖g x‖)
    · intro n
      exact (F n).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · exact hg.norm.const_mul (C + C)
    · intro n
      exact ae_of_all μ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)
    · apply ae_of_all
      intro x
      have hx : f x ∈ closure s := subset_closure (by simp [s])
      exact (SimpleFunc.tendsto_approxOn hf h0 hx).mul tendsto_const_nhds
  have hEq : ∀ n, Φ ((hFp n).toLp (F n)) = ∫ x, F n x * g x ∂μ := fun n =>
    lpFunctional_eq_simple_of_indicator μ p Φ hg hind (F n)
  exact tendsto_nhds_unique (hΦ.congr' (Eventually.of_forall hEq)) hIntegral

#print axioms lpFunctional_eq_simple_of_indicator
#print axioms lpFunctional_eq_bounded_of_indicator

end RudinRCA.Chapter06
-- END SOURCE Scratch616B.lean

-- BEGIN SOURCE Scratch616C.lean




/-! The finite-measure p = 1 bound in the proof of Rudin 6.16. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- The bounded complex phase that turns z into its norm by multiplication. -/
def dualityPhase (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

theorem dualityPhase_mul (z : ℂ) : dualityPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [dualityPhase, hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [dualityPhase, div_mul_eq_mul_div, div_eq_iff hn]
  simpa only [pow_two] using Complex.conj_mul' z

theorem norm_dualityPhase_le (z : ℂ) : ‖dualityPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [dualityPhase, hz]
  simp [dualityPhase, norm_div, norm_ne_zero_iff.mpr hz]

theorem measurable_dualityPhase : Measurable dualityPhase := by
  unfold dualityPhase
  fun_prop

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A density representing an L1 functional on indicators is essentially
bounded by the norm of the functional. -/
theorem lpOneFunctional_density_ae_bound
    (Φ : Lp ℂ 1 μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp 1 hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖Φ‖ := by
  apply ae_le_of_forall_setIntegral_le hg.norm (integrable_const ‖Φ‖)
  intro E hE hμE
  let f : X → ℂ := E.indicator (fun x => dualityPhase (g x))
  have hfm : Measurable f := (measurable_dualityPhase.comp hgm).indicator hE
  have hfbound : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E
    · simpa only [f, indicator_of_mem hx] using norm_dualityPhase_le (g x)
    · simp [f, hx]
  have hfp : MemLp f 1 μ := MemLp.of_bound hfm.aestronglyMeasurable 1 (ae_of_all μ hfbound)
  let F := hfp.toLp f
  have hFnorm : ‖F‖ ≤ μ.real E := by
    have hle : ‖F‖ ≤ ‖indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [MemLp.coeFn_toLp hfp,
        (indicatorConstLp_coeFn (p := 1) (hs := hE)
          (hμs := measure_ne_top μ E) (c := (1 : ℂ)))] with x h₁ h₂
      change ‖hfp.toLp f x‖ ≤ ‖indicatorConstLp 1 hE (measure_ne_top μ E) (1 : ℂ) x‖
      rw [h₁, h₂]
      by_cases hx : x ∈ E
      · simpa [hx] using hfbound x
      · simp [f, hx]
    simpa [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top] using hle
  have hΦF : Φ F = Complex.ofReal (∫ x in E, ‖g x‖ ∂μ) := by
    have hrep := lpFunctional_eq_bounded_of_indicator μ 1 ENNReal.one_ne_top Φ hg hind
      hfm 1 hfbound hfp
    have hprod : (fun x => f x * g x) = E.indicator (fun x => (‖g x‖ : ℂ)) := by
      funext x
      by_cases hx : x ∈ E
      · simpa only [f, indicator_of_mem hx] using dualityPhase_mul (g x)
      · simp [f, hx]
    change Φ (hfp.toLp f) = _
    rw [hrep, hprod, integral_indicator hE, integral_complex_ofReal]
  have hnonneg : 0 ≤ ∫ x in E, ‖g x‖ ∂μ := integral_nonneg fun x => norm_nonneg _
  calc
    (∫ x in E, ‖g x‖ ∂μ) = ‖Φ F‖ := by
      rw [hΦF, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ ≤ ‖Φ‖ * ‖F‖ := Φ.le_opNorm F
    _ ≤ ‖Φ‖ * μ.real E := mul_le_mul_of_nonneg_left hFnorm (norm_nonneg _)
    _ = ∫ x in E, ‖Φ‖ ∂μ := by simp [mul_comm]

theorem lpOneFunctional_density_memLp_top
    (Φ : Lp ℂ 1 μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp 1 hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    MemLp g ∞ μ :=
  memLp_top_of_bound hg.aestronglyMeasurable ‖Φ‖
    (lpOneFunctional_density_ae_bound μ Φ hgm hg hind)

#print axioms dualityPhase_mul
#print axioms norm_dualityPhase_le
#print axioms measurable_dualityPhase
#print axioms lpOneFunctional_density_ae_bound
#print axioms lpOneFunctional_density_memLp_top

end RudinRCA.Chapter06
-- END SOURCE Scratch616C.lean

-- BEGIN SOURCE Scratch616D.lean





/-! The finite-measure strict-exponent bound in the proof of Rudin 6.16. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem duality_root_bound {r s A C : ℝ} (hrs : r.HolderConjugate s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (h : A ≤ C * A ^ r⁻¹) : A ^ s⁻¹ ≤ C := by
  by_cases hA0 : A = 0
  · simpa [hA0, Real.zero_rpow hrs.symm.inv_ne_zero] using hC
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hrootpos : 0 < A ^ r⁻¹ := Real.rpow_pos_of_pos hApos _
  apply (mul_le_mul_iff_left₀ hrootpos).mp
  calc
    A ^ s⁻¹ * A ^ r⁻¹ = A := by
      rw [← Real.rpow_add hApos, hrs.symm.inv_add_inv_eq_one, Real.rpow_one]
    _ ≤ C * A ^ r⁻¹ := h

theorem norm_dualityPhase_of_ne_zero {z : ℂ} (hz : z ≠ 0) : ‖dualityPhase z‖ = 1 := by
  simp [dualityPhase, norm_div, norm_ne_zero_iff.mpr hz]

variable (μ : Measure X) [IsFiniteMeasure μ] (p q : ℝ≥0∞)
variable [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

/-- The bounded-test estimate forces a finite-measure RN density into Lq
for the strict-exponent case. Both finite exponents are explicit here;
the p = 1 endpoint is handled separately. -/
theorem lpFunctional_density_eLpNorm_le_of_finite_conjugates
    (hp : p ≠ ∞) (hq : q ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    eLpNorm g q μ ≤ ENNReal.ofReal ‖Φ‖ := by
  classical
  have hconj : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hp0 : p ≠ 0 := (one_pos.trans_le (Fact.out : 1 ≤ p)).ne'
  have hq0 : q ≠ 0 := by
    intro hz
    have hqpos := hconj.symm.pos
    simpa [hz] using hqpos
  let E : ℕ → Set X := fun n => {x | ‖g x‖ ≤ (n : ℝ)}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le hgm.norm measurable_const
  let U : ℕ → X → ℂ := fun n => (E n).indicator g
  have hUm : ∀ n, Measurable (U n) := fun n => hgm.indicator (hE n)
  have hUnorm : ∀ n x, ‖U n x‖ ≤ (n : ℝ) := by
    intro n x
    by_cases hx : x ∈ E n
    · have hx' : ‖g x‖ ≤ (n : ℝ) := hx
      simpa only [U, indicator_of_mem hx] using hx'
    · simp [U, hx]
  have hUq : ∀ n, MemLp (U n) q μ := fun n =>
    MemLp.of_bound (hUm n).aestronglyMeasurable (n : ℝ) (ae_of_all μ (hUnorm n))
  let F : ℕ → X → ℂ := fun n x =>
    Complex.ofReal (‖U n x‖ ^ (q.toReal - 1)) * dualityPhase (U n x)
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact ((hUm n).norm.pow_const _).complex_ofReal.mul
      (measurable_dualityPhase.comp (hUm n))
  have hFnorm : ∀ n x, ‖F n x‖ = ‖U n x‖ ^ (q.toReal - 1) := by
    intro n x
    by_cases hx : U n x = 0
    · simp [F, hx, dualityPhase, Real.zero_rpow hconj.symm.sub_one_ne_zero]
    · dsimp only [F]
      rw [norm_mul, norm_dualityPhase_of_ne_zero hx, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hFbound : ∀ n x, ‖F n x‖ ≤ (n : ℝ) ^ (q.toReal - 1) := by
    intro n x
    rw [hFnorm]
    exact Real.rpow_le_rpow (norm_nonneg _) (hUnorm n x) hconj.symm.sub_one_pos.le
  have hFp : ∀ n, MemLp (F n) p μ := fun n =>
    MemLp.of_bound (hFm n).aestronglyMeasurable ((n : ℝ) ^ (q.toReal - 1))
      (ae_of_all μ (hFbound n))
  have hpower : ∀ n x, ‖F n x‖ ^ p.toReal = ‖U n x‖ ^ q.toReal := by
    intro n x
    rw [hFnorm, ← Real.rpow_mul (norm_nonneg _), hconj.symm.sub_one_mul_conj]
  have hprod : ∀ n x, F n x * g x = Complex.ofReal (‖U n x‖ ^ q.toReal) := by
    intro n x
    by_cases hx : x ∈ E n
    · simp only [F, U, indicator_of_mem hx]
      rw [mul_assoc, dualityPhase_mul, ← Complex.ofReal_mul]
      congr 1
      have h := Real.rpow_add_one' (norm_nonneg (g x))
        (y := q.toReal - 1) (by simpa using hconj.symm.ne_zero)
      simpa only [sub_add_cancel] using h.symm
    · simp [F, U, hx, dualityPhase, Real.zero_rpow hconj.symm.ne_zero]
  have hUbound : ∀ n, eLpNorm (U n) q μ ≤ ENNReal.ofReal ‖Φ‖ := by
    intro n
    let integralMass : ℝ := ∫ x, ‖U n x‖ ^ q.toReal ∂μ
    have hI : 0 ≤ integralMass := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have hPhi : Φ ((hFp n).toLp (F n)) = (integralMass : ℂ) := by
      rw [lpFunctional_eq_bounded_of_indicator μ p hp Φ hg hind (hFm n)
        ((n : ℝ) ^ (q.toReal - 1)) (hFbound n) (hFp n)]
      simp_rw [hprod n]
      exact integral_complex_ofReal
    have hFnormLp : ‖(hFp n).toLp (F n)‖ = integralMass ^ p.toReal⁻¹ := by
      rw [Lp.norm_toLp, (hFp n).eLpNorm_eq_integral_rpow_norm hp0 hp,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg
          (fun x => Real.rpow_nonneg (norm_nonneg _) _)) _)]
      congr 1
      apply integral_congr_ae
      exact ae_of_all μ (hpower n)
    have hineq : integralMass ≤ ‖Φ‖ * integralMass ^ p.toReal⁻¹ := by
      have h := Φ.le_opNorm ((hFp n).toLp (F n))
      rw [hPhi, Complex.norm_real, Real.norm_of_nonneg hI, hFnormLp] at h
      exact h
    have hroot := duality_root_bound hconj hI (norm_nonneg Φ) hineq
    rw [(hUq n).eLpNorm_eq_integral_rpow_norm hq0 hq]
    exact ENNReal.ofReal_le_ofReal hroot
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (Eventually.of_forall hUbound)
    (fun n => (hUm n).aestronglyMeasurable) hg.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hevent : (fun n : ℕ => U n x) =ᶠ[atTop] (fun _ => g x) := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖g x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    apply indicator_of_mem
    exact hN.le.trans (by exact_mod_cast hn)
  exact tendsto_const_nhds.congr' hevent.symm

theorem lpFunctional_density_memLp_of_finite_conjugates
    (hp : p ≠ ∞) (hq : q ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    MemLp g q μ :=
  (lpFunctional_density_eLpNorm_le_of_finite_conjugates μ p q hp hq Φ hgm hg hind).trans_lt
    ENNReal.ofReal_lt_top

#print axioms duality_root_bound
#print axioms norm_dualityPhase_of_ne_zero
#print axioms lpFunctional_density_eLpNorm_le_of_finite_conjugates
#print axioms lpFunctional_density_memLp_of_finite_conjugates

end RudinRCA.Chapter06
-- END SOURCE Scratch616D.lean

-- BEGIN SOURCE Scratch616E.lean






/-!
Finite-measure assembly of Rudin 6.16, plus uniqueness for sigma-finite measures.
The sigma-finite existence reduction remains a separate required step.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

theorem integral_indicatorConstLp_mul (μ : Measure X) (p : ℝ≥0∞)
    {E : Set X} (hE : MeasurableSet E) (hμE : μ E ≠ ∞) (g : X → ℂ) :
    (∫ x, indicatorConstLp p hE hμE (1 : ℂ) x * g x ∂μ) = ∫ x in E, g x ∂μ := by
  have hfun : (fun x => indicatorConstLp p hE hμE (1 : ℂ) x * g x) =ᵐ[μ]
      E.indicator g := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE)
      (c := (1 : ℂ))] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [hxE]
  rw [integral_congr_ae hfun, integral_indicator hE]

/-- Injectivity of the bilinear Lp–Lq integral pairing, including q = ∞. -/
theorem lp_integral_pairing_unique (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (g h : Lp ℂ q μ)
    (heq : ∀ f : Lp ℂ p μ, (∫ x, f x * g x ∂μ) = ∫ x, f x * h x ∂μ) : g = h := by
  have hint : ∀ k : Lp ℂ q μ, ∀ E, MeasurableSet E → μ E < ∞ → IntegrableOn k E μ := by
    intro k E hE hμE
    letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hμE⟩
    exact ((Lp.memLp k).restrict E).integrable (Fact.out : 1 ≤ q)
  apply Lp.ext
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (hint g) (hint h)
  intro E hE hμE
  have ht := heq (indicatorConstLp p hE hμE.ne (1 : ℂ))
  simpa only [integral_indicatorConstLp_mul μ p hE hμE.ne] using ht

variable (μ : Measure X) [IsFiniteMeasure μ]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- Once the RN density lies in Lq, density of simple functions extends the
identity from indicators to every Lp class. -/
theorem lpFunctional_eq_of_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) (G : Lp ℂ q μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, G x ∂μ) :
    ∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Ψ : Lp ℂ p μ →L[ℂ] ℂ := B.lpPairing μ q p G
  have hΨ : ∀ f, Ψ f = ∫ x, f x * G x ∂μ := by
    intro f
    simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral G f
  have hGint : Integrable G μ := (Lp.memLp G).integrable (Fact.out : 1 ≤ q)
  have hsimple : (fun f : Lp.simpleFunc ℂ p μ => Φ (f : Lp ℂ p μ)) =
      (fun f : Lp.simpleFunc ℂ p μ => Ψ (f : Lp ℂ p μ)) := by
    funext f
    let s := Lp.simpleFunc.toSimpleFunc f
    have hs : (s.memLp_of_isFiniteMeasure p μ).toLp s = (f : Lp ℂ p μ) := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp (s.memLp_of_isFiniteMeasure p μ)).trans
        (Lp.simpleFunc.toSimpleFunc_eq_toFun f)
    have h := lpFunctional_eq_simple_of_indicator μ p Φ hGint hind s
    rw [hs] at h
    rw [h, hΨ]
    apply integral_congr_ae
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun f] with x hx
    rw [hx]
  have hmaps : (Φ : Lp ℂ p μ → ℂ) = Ψ :=
    (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) hp).equalizer Φ.continuous Ψ.continuous hsimple
  intro f
  rw [congr_fun hmaps f, hΨ]

theorem finiteLpFunctional_density_memLp_and_norm (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) {g : X → ℂ} (hgm : Measurable g) (hg : Integrable g μ)
    (hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ) :
    ∃ hqg : MemLp g q μ, ‖hqg.toLp g‖ ≤ ‖Φ‖ := by
  by_cases hq : q = ∞
  · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
    subst p
    subst q
    have hbound := lpOneFunctional_density_ae_bound μ Φ hgm hg hind
    have hmem := lpOneFunctional_density_memLp_top μ Φ hgm hg hind
    refine ⟨hmem, ?_⟩
    have hbound' : ∀ᵐ x ∂μ, ‖hmem.toLp g x‖ ≤ ‖Φ‖ := by
      filter_upwards [MemLp.coeFn_toLp hmem, hbound] with x hx hb
      simpa only [hx] using hb
    simpa using Lp.norm_le_of_ae_bound (p := ∞) (norm_nonneg Φ) hbound'
  · have hbound := lpFunctional_density_eLpNorm_le_of_finite_conjugates μ p q hp hq
      Φ hgm hg hind
    have hmem := lpFunctional_density_memLp_of_finite_conjugates μ p q hp hq Φ hgm hg hind
    refine ⟨hmem, ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg Φ) hbound

/-- The finite-positive-measure case of Rudin 6.16, with uniqueness and exact norm.
This is explicitly not yet the sigma-finite theorem printed in the book. -/
theorem theorem_6_16_finite (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃! G : Lp ℂ q μ, (∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ) ∧ ‖Φ‖ = ‖G‖ := by
  let c := finiteLpFunctionalMeasure μ p hp Φ
  obtain ⟨g, hgm, hgi, hsets, huniq⟩ := theorem_6_10_radon_nikodym c μ
    (finiteLpFunctionalMeasure_absolutelyContinuous μ p hp Φ)
  have hind : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, g x ∂μ := by
    intro E hE
    rw [← finiteLpFunctionalMeasure_apply μ p hp Φ hE]
    exact hsets E hE
  obtain ⟨hgp, hgnorm⟩ := finiteLpFunctional_density_memLp_and_norm μ p q hp Φ hgm hgi hind
  let G : Lp ℂ q μ := hgp.toLp g
  have hindG : ∀ E (hE : MeasurableSet E),
      Φ (indicatorConstLp p hE (measure_ne_top μ E) 1) = ∫ x in E, G x ∂μ := by
    intro E hE
    rw [hind E hE]
    apply setIntegral_congr_ae hE
    exact (MemLp.coeFn_toLp hgp).symm.mono fun x hx _ => hx
  have hrep := lpFunctional_eq_of_indicator μ p q hp Φ G hindG
  obtain ⟨Ψ, hΨ, hΨnorm⟩ := theorem_6_15 μ p q G
  have hΦΨ : Φ = Ψ := by
    ext f
    exact (hrep f).trans (hΨ f).symm
  have hnorm : ‖Φ‖ = ‖G‖ := le_antisymm (by rw [hΦΨ]; exact hΨnorm) hgnorm
  refine ⟨G, ⟨hrep, hnorm⟩, ?_⟩
  intro H hH
  exact lp_integral_pairing_unique μ p q H G fun f => (hH.1 f).symm.trans (hrep f)

#print axioms lp_integral_pairing_unique
#print axioms lpFunctional_eq_of_indicator
#print axioms finiteLpFunctional_density_memLp_and_norm
#print axioms theorem_6_16_finite

end RudinRCA.Chapter06
-- END SOURCE Scratch616E.lean

-- BEGIN SOURCE Scratch616F.lean



/-! Zero extension from a measurable restriction, for the sigma-finite Lp duality proof. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]

set_option maxHeartbeats 800000 in
/-- Zero extension is a complex-linear isometry from Lp of a measurable
restriction into Lp of the ambient measure. -/
def lpZeroExtend {S : Set X} (hS : MeasurableSet S) :
    Lp ℂ p (μ.restrict S) →ₗᵢ[ℂ] Lp ℂ p μ where
  toFun f := ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (f + g))),
        Lp.coeFn_add
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f))
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp g)).toLp (S.indicator g)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp g)),
        (ae_eq_restrict_iff_indicator_ae_eq hS).mp (Lp.coeFn_add f g)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₂, Pi.add_apply, h₃, h₄, h₅]
    by_cases hx : x ∈ S <;> simp [hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (c • f))),
        Lp.coeFn_smul c
          (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp (S.indicator f)),
        MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)),
        (ae_eq_restrict_iff_indicator_ae_eq hS).mp (Lp.coeFn_smul c f)]
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.smul_apply, h₃, h₄]
    by_cases hx : x ∈ S <;> simp [hx]
  norm_map' f := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hS]

theorem lpZeroExtend_coeFn {S : Set X} (hS : MeasurableSet S)
    (f : Lp ℂ p (μ.restrict S)) :
    lpZeroExtend μ p hS f =ᵐ[μ] S.indicator f :=
  MemLp.coeFn_toLp _

/-- Restrict a functional by applying it to zero extensions. -/
def lpFunctionalOnRestriction (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {S : Set X} (hS : MeasurableSet S) : Lp ℂ p (μ.restrict S) →L[ℂ] ℂ :=
  Φ.comp (lpZeroExtend μ p hS).toContinuousLinearMap

theorem lpFunctionalOnRestriction_norm_le (Φ : Lp ℂ p μ →L[ℂ] ℂ)
    {S : Set X} (hS : MeasurableSet S) :
    ‖lpFunctionalOnRestriction μ p Φ hS‖ ≤ ‖Φ‖ := by
  calc
    _ ≤ ‖Φ‖ * ‖(lpZeroExtend μ p hS).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left
      (lpZeroExtend μ p hS).norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = ‖Φ‖ := mul_one _

theorem lpZeroExtend_indicatorConstLp {S E : Set X} (hS : MeasurableSet S)
    (hE : MeasurableSet E) (hES : E ⊆ S) (hμE : μ E ≠ ∞) (c : ℂ) :
    lpZeroExtend μ p hS
      (indicatorConstLp p hE (ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) c) =
        indicatorConstLp p hE hμE c := by
  apply Lp.ext
  have hlocal := (ae_eq_restrict_iff_indicator_ae_eq hS).mp
    (indicatorConstLp_coeFn (p := p) (μ := μ.restrict S) (hs := hE)
      (hμs := ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) (c := c))
  filter_upwards [lpZeroExtend_coeFn μ p hS
    (indicatorConstLp p hE (ne_top_of_le_ne_top hμE (Measure.restrict_le_self E)) c),
      hlocal, (indicatorConstLp_coeFn (p := p) (μ := μ) (hs := hE) (hμs := hμE) (c := c))]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ E
  · simp [hx, hES hx]
  · simp [hx]

#print axioms lpZeroExtend
#print axioms lpZeroExtend_coeFn
#print axioms lpFunctionalOnRestriction
#print axioms lpFunctionalOnRestriction_norm_le
#print axioms lpZeroExtend_indicatorConstLp

end RudinRCA.Chapter06
-- END SOURCE Scratch616F.lean

-- BEGIN SOURCE Scratch616G.lean




/-! Gluing compatible local densities along a sigma-finite exhaustion. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Uniformly Lq-bounded compatible local densities glue to a global density.
Compatibility is expressed on every pairwise overlap modulo a null set. -/
theorem sigmaFinite_glue_densities (μ : Measure X) [SigmaFinite μ] (q : ℝ≥0∞)
    (g : ℕ → X → ℂ) (hgm : ∀ n, Measurable (g n))
    (hcompat : ∀ n m, ∀ᵐ x ∂μ,
      x ∈ spanningSets μ n → x ∈ spanningSets μ m → g n x = g m x)
    (C : ℝ≥0∞)
    (hbound : ∀ n, eLpNorm ((spanningSets μ n).indicator (g n)) q μ ≤ C) :
    ∃ G : X → ℂ, Measurable G ∧ eLpNorm G q μ ≤ C ∧
      ∀ n, G =ᵐ[μ.restrict (spanningSets μ n)] g n := by
  let G : X → ℂ := fun x => g (spanningSetsIndex μ x) x
  have hGm : Measurable G := by
    have hfamily : Measurable (fun z : X × ℕ => g z.2 z.1) :=
      measurable_from_prod_countable_left hgm
    exact hfamily.comp (measurable_id.prodMk (measurableSet_spanningSetsIndex μ))
  have hlocal : ∀ n, G =ᵐ[μ.restrict (spanningSets μ n)] g n := by
    intro n
    apply (ae_restrict_iff' (measurableSet_spanningSets μ n)).mpr
    have hall : ∀ᵐ x ∂μ, ∀ m, x ∈ spanningSets μ n →
        x ∈ spanningSets μ m → g n x = g m x := ae_all_iff.mpr (hcompat n)
    filter_upwards [hall] with x hx
    intro hxn
    exact (hx (spanningSetsIndex μ x) hxn (mem_spanningSetsIndex μ x)).symm
  have hboundG : ∀ n, eLpNorm ((spanningSets μ n).indicator G) q μ ≤ C := by
    intro n
    rw [eLpNorm_congr_ae ((ae_eq_restrict_iff_indicator_ae_eq
      (measurableSet_spanningSets μ n)).mp (hlocal n))]
    exact hbound n
  have hGbound : eLpNorm G q μ ≤ C := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (Eventually.of_forall hboundG)
      (fun n => (hGm.indicator (measurableSet_spanningSets μ n)).aestronglyMeasurable)
      hGm.aestronglyMeasurable
    apply ae_of_all
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_spanningSets μ x] with n hn
    simp only [indicator_of_mem hn]
  exact ⟨G, hGm, hGbound, hlocal⟩

#print axioms sigmaFinite_glue_densities

end RudinRCA.Chapter06
-- END SOURCE Scratch616G.lean

-- BEGIN SOURCE Scratch616H.lean



/-! Finite-indicator density and convergence along sigma-finite spanning sets. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate p q]

/-- Equality on finite-measure indicators determines a bounded Lp functional
for arbitrary positive measures when p is finite. -/
theorem lpFunctional_eq_of_finite_indicator (hp : p ≠ ∞)
    (Φ : Lp ℂ p μ →L[ℂ] ℂ) (G : Lp ℂ q μ)
    (hind : ∀ E (hE : MeasurableSet E) (hμE : μ E ≠ ∞),
      Φ (indicatorConstLp p hE hμE 1) = ∫ x in E, G x ∂μ) :
    ∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  let Ψ : Lp ℂ p μ →L[ℂ] ℂ := B.lpPairing μ q p G
  have hΨ : ∀ f, Ψ f = ∫ x, f x * G x ∂μ := by
    intro f
    simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
      B.lpPairing_eq_integral G f
  have hmaps : ∀ f : Lp ℂ p μ, Φ f = Ψ f := by
    apply Lp.induction hp (fun f => Φ f = Ψ f)
    · intro c E hE hμE
      change Φ (indicatorConstLp p hE hμE.ne c) = Ψ (indicatorConstLp p hE hμE.ne c)
      have hsmul : indicatorConstLp p hE hμE.ne c =
          c • indicatorConstLp p hE hμE.ne (1 : ℂ) := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE.ne) (c := c),
          Lp.coeFn_smul c (indicatorConstLp p hE hμE.ne (1 : ℂ)),
          indicatorConstLp_coeFn (p := p) (hs := hE) (hμs := hμE.ne) (c := (1 : ℂ))]
          with x h₁ h₂ h₃
        rw [h₁, h₂, Pi.smul_apply, h₃]
        by_cases hx : x ∈ E <;> simp [hx]
      rw [hsmul, map_smul, map_smul, hind E hE hμE.ne, hΨ,
        integral_indicatorConstLp_mul μ p hE hμE.ne]
    · intro f g hf hg hfg hΦf hΦg
      rw [map_add, map_add, hΦf, hΦg]
    · exact isClosed_eq Φ.continuous Ψ.continuous
  intro f
  exact (hmaps f).trans (hΨ f)

variable [SigmaFinite μ]

/-- Indicators of the intersections with a sigma-finite exhaustion converge
in Lp to any fixed finite-measure indicator. -/
theorem tendsto_indicatorConstLp_spanningSets (hp : p ≠ ∞)
    {E : Set X} (hE : MeasurableSet E) (hμE : μ E ≠ ∞) :
    Tendsto (fun n => indicatorConstLp p (hE.inter (measurableSet_spanningSets μ n))
      (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) atTop
      (𝓝 (indicatorConstLp p hE hμE (1 : ℂ))) := by
  let R : ℕ → Set X := fun n => E \ (E ∩ spanningSets μ n)
  have hRm : ∀ n, MeasurableSet (R n) := fun n =>
    hE.diff (hE.inter (measurableSet_spanningSets μ n))
  have hRanti : Antitone R := by
    intro n m hnm x hx
    exact ⟨hx.1, fun hy => hx.2 ⟨hy.1, spanningSets_mono hnm hy.2⟩⟩
  have hRinter : (⋂ n, R n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxE := (mem_iInter.mp hx 0).1
    exact (mem_iInter.mp hx (spanningSetsIndex μ x)).2 ⟨hxE, mem_spanningSetsIndex μ x⟩
  have hlim : Tendsto (fun n => μ (R n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hRm n).nullMeasurableSet)
      hRanti ⟨0, ne_top_of_le_ne_top hμE (measure_mono diff_subset)⟩
    simpa only [hRinter, measure_empty, Function.comp_def] using h
  apply tendsto_indicatorConstLp_set hp
  simpa only [symmDiff_of_le (inter_subset_left : E ∩ spanningSets μ _ ⊆ E)] using hlim

#print axioms lpFunctional_eq_of_finite_indicator
#print axioms tendsto_indicatorConstLp_spanningSets

end RudinRCA.Chapter06
-- END SOURCE Scratch616H.lean

-- BEGIN SOURCE Scratch616I.lean




/-! Sigma-finite assembly of the Lp dual representation theorem. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]

/-- Rudin 6.16: the complex bilinear integral pairing identifies Lq
isometrically with the continuous dual of Lp for sigma-finite measures,
including p = 1 and q = ∞. -/
theorem theorem_6_16 (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (Φ : Lp ℂ p μ →L[ℂ] ℂ) :
    ∃! G : Lp ℂ q μ, (∀ f : Lp ℂ p μ, Φ f = ∫ x, f x * G x ∂μ) ∧ ‖Φ‖ = ‖G‖ := by
  classical
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let S := spanningSets μ
  have hS : ∀ n, MeasurableSet (S n) := measurableSet_spanningSets μ
  let ρ : ℕ → Measure X := fun n => μ.restrict (S n)
  have hρ : ∀ n, IsFiniteMeasure (ρ n) := fun n =>
    ⟨by simpa [ρ] using measure_spanningSets_lt_top μ n⟩
  let Φn : ∀ n, Lp ℂ p (ρ n) →L[ℂ] ℂ := fun n => lpFunctionalOnRestriction μ p Φ (hS n)
  have hlocalExists : ∀ n, ∃ G : Lp ℂ q (ρ n),
      (∀ f : Lp ℂ p (ρ n), Φn n f = ∫ x, f x * G x ∂ρ n) ∧ ‖Φn n‖ = ‖G‖ := by
    intro n
    letI := hρ n
    exact (theorem_6_16_finite (ρ n) p q hp (Φn n)).exists
  choose gn hgn using hlocalExists
  have hgnm : ∀ n, Measurable (gn n : X → ℂ) := fun n => (Lp.stronglyMeasurable (gn n)).measurable
  have hgnint : ∀ n, IntegrableOn (gn n : X → ℂ) (S n) μ := by
    intro n
    letI := hρ n
    exact (Lp.memLp (gn n)).integrable (Fact.out : 1 ≤ q)
  have hfinite : ∀ n E, E ⊆ S n → μ E ≠ ∞ := by
    intro n E hES
    exact ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne (measure_mono hES)
  have hsets : ∀ n E (hE : MeasurableSet E) (hES : E ⊆ S n),
      Φ (indicatorConstLp p hE (hfinite n E hES) 1) = ∫ x in E, gn n x ∂μ := by
    intro n E hE hES
    letI := hρ n
    have hr := (hgn n).1 (indicatorConstLp p hE (measure_ne_top (ρ n) E) (1 : ℂ))
    change Φ (lpZeroExtend μ p (hS n)
      (indicatorConstLp p hE (measure_ne_top (ρ n) E) (1 : ℂ))) = _ at hr
    rw [lpZeroExtend_indicatorConstLp μ p (hS n) hE hES (hfinite n E hES) 1,
      integral_indicatorConstLp_mul (ρ n) p hE (measure_ne_top (ρ n) E)] at hr
    simpa only [ρ, Measure.restrict_restrict hE, inter_eq_left.mpr hES] using hr
  have hcompat : ∀ n m, ∀ᵐ x ∂μ, x ∈ S n → x ∈ S m → gn n x = gn m x := by
    intro n m
    let H := S n ∩ S m
    have hH : MeasurableSet H := (hS n).inter (hS m)
    have hnH : Integrable (gn n : X → ℂ) (μ.restrict H) :=
      (hgnint n).mono_set inter_subset_left
    have hmH : Integrable (gn m : X → ℂ) (μ.restrict H) :=
      (hgnint m).mono_set inter_subset_right
    have hEq : (gn n : X → ℂ) =ᵐ[μ.restrict H] gn m := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hnH hmH
      intro E hE hμE
      rw [Measure.restrict_restrict hE]
      have hEn : E ∩ H ⊆ S n := fun x hx => hx.2.1
      have hEm : E ∩ H ⊆ S m := fun x hx => hx.2.2
      exact (hsets n (E ∩ H) (hE.inter hH) hEn).symm.trans
        (hsets m (E ∩ H) (hE.inter hH) hEm)
    have hEq' := (ae_restrict_iff' hH).mp hEq
    filter_upwards [hEq'] with x hx
    intro hxn hxm
    exact hx ⟨hxn, hxm⟩
  have hbound : ∀ n, eLpNorm ((S n).indicator (gn n : X → ℂ)) q μ ≤ ENNReal.ofReal ‖Φ‖ := by
    intro n
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hS n)]
    change eLpNorm (gn n) q (ρ n) ≤ ENNReal.ofReal ‖Φ‖
    rw [← Lp.enorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖gn n‖ = ‖Φn n‖ := (hgn n).2.symm
      _ ≤ ‖Φ‖ := lpFunctionalOnRestriction_norm_le μ p Φ (hS n)
  obtain ⟨g, hgm, hgbound, hglocal⟩ := sigmaFinite_glue_densities μ q
    (fun n => (gn n : X → ℂ)) hgnm hcompat (ENNReal.ofReal ‖Φ‖) hbound
  have hgp : MemLp g q μ := hgbound.trans_lt ENNReal.ofReal_lt_top
  let G : Lp ℂ q μ := hgp.toLp g
  have hGlocal : ∀ n, (G : X → ℂ) =ᵐ[μ.restrict (S n)] gn n := by
    intro n
    have hGae : (G : X → ℂ) =ᵐ[μ.restrict (S n)] g :=
      ae_restrict_of_ae (MemLp.coeFn_toLp hgp)
    exact hGae.trans (hglocal n)
  have hGnorm : ‖G‖ ≤ ‖Φ‖ := by
    change ‖hgp.toLp g‖ ≤ ‖Φ‖
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg Φ) hgbound
  obtain ⟨Ψ, hΨ, hΨnorm⟩ := theorem_6_15 μ p q G
  have hagree : ∀ n E (hE : MeasurableSet E) (hES : E ⊆ S n),
      Φ (indicatorConstLp p hE (hfinite n E hES) 1) =
        Ψ (indicatorConstLp p hE (hfinite n E hES) 1) := by
    intro n E hE hES
    rw [hsets n E hE hES, hΨ,
      integral_indicatorConstLp_mul μ p hE (hfinite n E hES)]
    apply setIntegral_congr_ae hE
    have hl := (ae_restrict_iff' (hS n)).mp (hGlocal n)
    filter_upwards [hl] with x hx
    intro hxE
    exact (hx (hES hxE)).symm
  have hind : ∀ E (hE : MeasurableSet E) (hμE : μ E ≠ ∞),
      Φ (indicatorConstLp p hE hμE 1) = ∫ x in E, G x ∂μ := by
    intro E hE hμE
    have hlim := tendsto_indicatorConstLp_spanningSets μ p hp hE hμE
    have hΦlim := Φ.continuous.continuousAt.tendsto.comp hlim
    have hΨlim := Ψ.continuous.continuousAt.tendsto.comp hlim
    have hvals : ∀ n, Φ (indicatorConstLp p (hE.inter (hS n))
        (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) =
        Ψ (indicatorConstLp p (hE.inter (hS n))
        (ne_top_of_le_ne_top hμE (measure_mono inter_subset_left)) (1 : ℂ)) := by
      intro n
      exact hagree n (E ∩ S n) (hE.inter (hS n)) inter_subset_right
    have heq := tendsto_nhds_unique (hΦlim.congr' (Eventually.of_forall hvals)) hΨlim
    exact heq.trans ((hΨ _).trans (integral_indicatorConstLp_mul μ p hE hμE G))
  have hrep := lpFunctional_eq_of_finite_indicator μ p q hp Φ G hind
  have hΦΨ : Φ = Ψ := by
    ext f
    exact (hrep f).trans (hΨ f).symm
  have hnorm : ‖Φ‖ = ‖G‖ := le_antisymm (by rw [hΦΨ]; exact hΨnorm) hGnorm
  refine ⟨G, ⟨hrep, hnorm⟩, ?_⟩
  intro H hH
  exact lp_integral_pairing_unique μ p q H G fun f => (hH.1 f).symm.trans (hrep f)

#print axioms theorem_6_16

end RudinRCA.Chapter06
-- END SOURCE Scratch616I.lean

-- BEGIN SOURCE Scratch616J.lean


/-! The linear isometric equivalence asserted after Rudin 6.16. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter06

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [SigmaFinite μ]
variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate p q]

/-- The complex bilinear integral pairing as a linear isometry into the dual. -/
def lpDualityLinearIsometry (hp : p ≠ ∞) :
    Lp ℂ q μ →ₗᵢ[ℂ] (Lp ℂ p μ →L[ℂ] ℂ) :=
  { ((ContinuousLinearMap.mul ℂ ℂ).lpPairing μ q p).toLinearMap with
    norm_map' := by
      intro G
      let B := ContinuousLinearMap.mul ℂ ℂ
      let Ψ := B.lpPairing μ q p G
      obtain ⟨H, ⟨hH, hnorm⟩, _⟩ := theorem_6_16 μ p q hp Ψ
      have hHG : H = G := by
        apply lp_integral_pairing_unique μ p q H G
        intro f
        calc
          (∫ x, f x * H x ∂μ) = Ψ f := (hH f).symm
          _ = ∫ x, f x * G x ∂μ := by
            simpa only [Ψ, B, ContinuousLinearMap.mul_apply', mul_comm] using
              B.lpPairing_eq_integral G f
      exact hnorm.trans (congrArg norm hHG) }

theorem lpDualityLinearIsometry_apply (hp : p ≠ ∞)
    (G : Lp ℂ q μ) (f : Lp ℂ p μ) :
    lpDualityLinearIsometry μ p q hp G f = ∫ x, f x * G x ∂μ := by
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ q p G f = _
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral G f

theorem lpDualityLinearIsometry_surjective (hp : p ≠ ∞) :
    Function.Surjective (lpDualityLinearIsometry μ p q hp) := by
  intro Φ
  obtain ⟨G, ⟨hrep, _⟩, _⟩ := theorem_6_16 μ p q hp Φ
  refine ⟨G, ?_⟩
  ext f
  exact (lpDualityLinearIsometry_apply μ p q hp G f).trans (hrep f).symm

omit [Fact (1 ≤ q)] in
/-- Rudin 6.16, the attached isometric-isomorphism assertion: every complex
continuous linear functional on Lp is uniquely an integral against an Lq class.
The conjugate exponent's lower bound follows from Hölder conjugacy. -/
def theorem_6_16_linearIsometryEquiv (hp : p ≠ ∞) :
    letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
    Lp ℂ q μ ≃ₗᵢ[ℂ] (Lp ℂ p μ →L[ℂ] ℂ) := by
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact LinearIsometryEquiv.ofSurjective (lpDualityLinearIsometry μ p q hp)
    (lpDualityLinearIsometry_surjective μ p q hp)

omit [Fact (1 ≤ q)] in
theorem theorem_6_16_linearIsometryEquiv_apply (hp : p ≠ ∞)
    (G : Lp ℂ q μ) (f : Lp ℂ p μ) :
    theorem_6_16_linearIsometryEquiv μ p q hp G f = ∫ x, f x * G x ∂μ := by
  letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  change lpDualityLinearIsometry μ p q hp G f = _
  exact lpDualityLinearIsometry_apply μ p q hp G f

#print axioms lpDualityLinearIsometry
#print axioms lpDualityLinearIsometry_apply
#print axioms lpDualityLinearIsometry_surjective
#print axioms theorem_6_16_linearIsometryEquiv
#print axioms theorem_6_16_linearIsometryEquiv_apply

end RudinRCA.Chapter06
-- END SOURCE Scratch616J.lean

-- BEGIN SOURCE Scratch619Regular.lean





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
-- END SOURCE Scratch619Regular.lean

-- BEGIN SOURCE Scratch619Density.lean



noncomputable section
open MeasureTheory TopologicalSpace ContinuousMap Set Bornology
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace RudinRCA.Chapter06
variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞}

/- Adapted from pinned Mathlib ContinuousMapDense.lean. Compact inner approximation
allows the compact/closed Urysohn lemma, avoiding any NormalSpace hypothesis. -/
theorem lch_exists_continuous_eLpNorm_sub_le_of_compact [μ.OuterRegular] (hp : p ≠ ∞) {s u : Set α}
    (s_compact : IsCompact s) (u_open : IsOpen u) (hsu : s ⊆ u) (hs : μ s ≠ ∞) (c : E) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ f : α → E,
      Continuous f ∧
        eLpNorm (fun x => f x - s.indicator (fun _y => c) x) p μ ≤ ε ∧
          (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f p μ := by
  have s_closed := s_compact.isClosed
  obtain ⟨η, η_pos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ ε :=
    exists_eLpNorm_indicator_le hp c hε
  have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : Set α), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
    s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
  let v := u ∩ V
  have hsv : s ⊆ v := subset_inter hsu sV
  have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
  obtain ⟨g, hgv, hgs, hg_range⟩ :=
    exists_continuous_zero_one_of_isCompact' s_compact (u_open.inter V_open).isClosed_compl
      (disjoint_compl_left_iff.2 hsv).symm
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `v \ s`, which has small measure.
  have g_norm : ∀ x, ‖g x‖ = g x := fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
    intro x
    simp only [norm_smul, g_norm x]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (hg_range x).2
  have gc_bd :
      ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
    intro x
    by_cases hv : x ∈ v
    · rw [← Set.sdiff_union_of_subset hsv] at hv
      rcases hv with hsv | hs
      · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
          Set.indicator_of_mem] using gc_bd0 x
      · simp [hgs hs, hs]
    · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
  have gc_support : (Function.support fun x : α => g x • c) ⊆ v := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [hgv hx, Pi.zero_apply, zero_smul]
  have gc_mem : MemLp (fun x => g x • c) p μ := by
    refine MemLp.smul ?_ (memLp_top_const _) (p := p) (q := ∞)
    have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
    have : eLpNorm (v.indicator fun _x => (1 : ℝ)) p μ < ∞ :=
      (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
        simp [lt_top_iff_ne_top, hμv.ne]
    refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
    by_cases hx : x ∈ v
    · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
        indicator_of_mem, CStarRing.norm_one]
    · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
  refine ⟨fun x ↦ g x • c, by fun_prop,
    (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator s_closed.measurableSet)) gc_bd).trans ?_, gc_bd0,
      gc_support.trans inter_subset_left, gc_mem⟩
  exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
    ((u_open.measurableSet.inter V_open.measurableSet).diff
      s_closed.measurableSet).nullMeasurableSet

theorem lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le
    [μ.Regular]
    (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H :
      ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    rcases H with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and consists of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  -- stability under addition
  · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_eLpNorm_sub_le_of_closed`.
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_compact, s_closed, μs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set α, IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases lch_exists_continuous_eLpNorm_sub_le_of_compact hp s_compact isOpen_interior sk hsμ.ne c δpos.ne'
    with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert! (hδ _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (f_support hx)



/-- L1 density of compactly supported continuous functions on every locally
compact Hausdorff space with a regular measure, without normality. -/
theorem lch_integrable_exists_hasCompactSupport_integral_sub_le [μ.Regular]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E, HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧
      Continuous g ∧ Integrable g μ := by
  obtain ⟨g, hg_support, hg, hg_cont, hg_mem⟩ :=
    lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hf) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hg_mem
  refine ⟨g, hg_support, ?_, hg_cont, hgi⟩
  have hfg := (hf.sub hgi).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hfg] at hg
  change (∫ x, ‖(f - g) x‖ ∂μ) ≤ ε
  rw [integral_norm_eq_lintegral_enorm hfg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  simpa only [ENNReal.toReal_ofReal hε.le, Pi.sub_apply] using hh

#print axioms lch_exists_continuous_eLpNorm_sub_le_of_compact
#print axioms lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le
#print axioms lch_integrable_exists_hasCompactSupport_integral_sub_le
end RudinRCA.Chapter06
-- END SOURCE Scratch619Density.lean

-- BEGIN SOURCE Scratch619Clip.lean





noncomputable section
open MeasureTheory Set

namespace RudinRCA.Chapter06

/-- Radial truncation to the closed unit disk, preserving zero. -/
def unitClip (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

@[simp] theorem unitClip_zero : unitClip 0 = 0 := by simp [unitClip]

theorem continuous_unitClip : Continuous unitClip := by
  unfold unitClip
  exact ((continuous_const.max continuous_norm).inv₀
    (fun z ↦ (zero_lt_one.trans_le (le_max_left 1 ‖z‖)).ne')).smul continuous_id

theorem norm_unitClip_le (z : ℂ) : ‖unitClip z‖ ≤ 1 := by
  have hn : 0 < max 1 ‖z‖ := zero_lt_one.trans_le (le_max_left _ _)
  rw [unitClip, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  exact (inv_mul_le_one₀ hn).mpr (le_max_right _ _)

theorem unitClip_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : unitClip z = z := by
  simp [unitClip, max_eq_left hz]

/-- Truncating an approximation loses at most a factor two in its error
relative to a point in the closed unit disk. -/
theorem unitClip_error_le (z w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖unitClip z - w‖ ≤ 2 * ‖z - w‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [unitClip_eq_self hz]
    linarith [norm_nonneg (z - w)]
  have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
  have hn : 0 < ‖z‖ := zero_lt_one.trans hz1
  have hdiff : ‖unitClip z - z‖ = ‖z‖ - 1 := by
    rw [norm_sub_rev, unitClip, max_eq_right hz1.le]
    have heq : z - ‖z‖⁻¹ • z = (1 - ‖z‖⁻¹) • z := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_of_nonneg
      (sub_nonneg.mpr (inv_le_one_of_one_le₀ hz1.le))]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hn.ne']
  have hdist : ‖z‖ - 1 ≤ ‖z - w‖ := by
    linarith [norm_sub_norm_le z w]
  calc
    ‖unitClip z - w‖ = ‖(unitClip z - z) + (z - w)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖unitClip z - z‖ + ‖z - w‖ := norm_add_le _ _
    _ ≤ 2 * ‖z - w‖ := by rw [hdiff]; linarith

/-- A compact-support L1 approximation property also provides approximations
within the unit ball. The approximation hypothesis is explicit: the pinned
library's standard density wrapper carries an additional normality hypothesis. -/
theorem exists_unitBounded_compactSupport_approx
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    {f : X → ℂ} (hf : Integrable f μ) (hn : ∀ x, ‖f x‖ ≤ 1)
    (happrox : ∀ η : ℝ, 0 < η → ∃ g : X → ℂ,
      HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ η ∧
      Continuous g ∧ Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℂ, HasCompactSupport g ∧ Continuous g ∧
      (∀ x, ‖g x‖ ≤ 1) ∧ Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨g, hgc, hge, hgcont, hgi⟩ :=
    happrox (ε / 2) (half_pos hε)
  let k := unitClip ∘ g
  have hkc : HasCompactSupport k := hgc.comp_left unitClip_zero
  have hkcont : Continuous k := continuous_unitClip.comp hgcont
  have hkn : ∀ x, ‖k x‖ ≤ 1 := fun x ↦ norm_unitClip_le (g x)
  have hki : Integrable k μ := Integrable.of_bound hkcont.aestronglyMeasurable 1 (ae_of_all μ hkn)
  refine ⟨k, hkc, hkcont, hkn, hki, ?_⟩
  calc
    (∫ x, ‖f x - k x‖ ∂μ) ≤ ∫ x, 2 * ‖f x - g x‖ ∂μ := by
      apply integral_mono (hf.sub hki).norm ((hf.sub hgi).norm.const_mul 2)
      intro x
      simpa only [k, Pi.sub_apply, Function.comp_apply, norm_sub_rev] using
        unitClip_error_le (g x) (f x) (hn x)
    _ = 2 * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul _ _
    _ ≤ ε := by linarith

#print axioms unitClip_error_le
#print axioms exists_unitBounded_compactSupport_approx
end RudinRCA.Chapter06
-- END SOURCE Scratch619Clip.lean

-- BEGIN SOURCE Scratch619Uniqueness.lean







noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace RudinRCA.Chapter06

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

private theorem integrable_conj_polar (c : ComplexMeasure X) {h : X → ℂ}
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1) :
    Integrable (fun x ↦ star (h x)) c.variation := by
  apply Integrable.of_bound (continuous_star.measurable.comp hm).aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by simp [hn]

/-- The elementary estimate used in the uniqueness and norm arguments of 6.19. -/
theorem polar_mass_le_integral_add_error (c : ComplexMeasure X) (h : X → ℂ)
    (hm : Measurable h) (hn : ∀ x, ‖h x‖ = 1)
    (hi : Integrable h c.variation) (hr : c.variation.withDensityᵥ h = c)
    {g : X → ℂ} (hg : Integrable g c.variation) :
    c.variation.real univ ≤ ‖complexIntegral c g‖ +
      ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
  have hc := integrable_conj_polar c hm hn
  have hb : ∀ᵐ x ∂c.variation, ‖h x‖ ≤ 1 := ae_of_all _ fun x ↦ (hn x).le
  have he := (hc.sub hg).mul_bdd hm.aestronglyMeasurable hb
  have hgh := hg.mul_bdd hm.aestronglyMeasurable hb
  have hid : (∫ x, (star (h x) - g x) * h x ∂c.variation) +
      (∫ x, g x * h x ∂c.variation) = (c.variation.real univ : ℂ) := by
    rw [← integral_add he hgh]
    calc
      (∫ x, (star (h x) - g x) * h x + g x * h x ∂c.variation) =
          ∫ _ : X, (1 : ℂ) ∂c.variation := by
        apply integral_congr_ae
        exact ae_of_all _ fun x ↦ by
          rw [sub_mul, sub_add_cancel, Complex.conj_mul', hn]
          norm_num
      _ = _ := by simp
  have herror : ‖∫ x, (star (h x) - g x) * h x ∂c.variation‖ ≤
      ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
    have := norm_integral_le_integral_norm (f := fun x ↦ (star (h x) - g x) * h x)
      (μ := c.variation)
    simpa only [norm_mul, hn, mul_one] using this
  have hnative := vectorIntegral_eq_polar c h hm hn hi hr hg
  change complexIntegral c g = _ at hnative
  calc
    c.variation.real univ = ‖(c.variation.real univ : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    _ = ‖(∫ x, (star (h x) - g x) * h x ∂c.variation) +
        (∫ x, g x * h x ∂c.variation)‖ := congrArg norm hid.symm
    _ ≤ ‖∫ x, (star (h x) - g x) * h x ∂c.variation‖ +
        ‖∫ x, g x * h x ∂c.variation‖ := norm_add_le _ _
    _ ≤ ‖complexIntegral c g‖ + ∫ x, ‖star (h x) - g x‖ ∂c.variation := by
      rw [← hnative]
      linarith

/-- The exact norm assertion of 6.19 for any regular complex measure representing
a bounded complex functional. The existence of a representing measure is separate. -/
theorem theorem_6_19_norm (c : ComplexMeasure X) [c.variation.Regular]
    (Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ)
    (hΦ : ∀ f, Φ f = complexIntegral c f) : ‖Φ‖ = c.variation.real univ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro f
    rw [hΦ]
    simpa only [mul_comm, measureReal_def] using
      theorem_6_18_bound c f ‖f‖ (norm_nonneg f) (fun x ↦ f.toBCF.norm_coe_le_norm x)
  · obtain ⟨h, hm, hn, hi, hr⟩ := theorem_6_12 c
    have hc := integrable_conj_polar c hm hn
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hgc, hgcont, hgn, hgi, hge⟩ :=
      exists_unitBounded_compactSupport_approx c.variation hc
        (fun x ↦ by simp [hn])
        (fun η hη ↦ lch_integrable_exists_hasCompactSupport_integral_sub_le hc hη) hε
    let G : ZeroAtInftyContinuousMap X ℂ :=
      { toFun := g, continuous_toFun := hgcont, zero_at_infty' := hgc.is_zero_at_infty }
    have hG : ‖G‖ ≤ 1 := (BoundedContinuousFunction.norm_le (f := G.toBCF) zero_le_one).mpr hgn
    have hval : ‖complexIntegral c g‖ ≤ ‖Φ‖ := by
      change ‖complexIntegral c G‖ ≤ ‖Φ‖
      rw [← hΦ]
      exact (Φ.le_opNorm G).trans (mul_le_of_le_one_right (norm_nonneg Φ) hG)
    have hmass := polar_mass_le_integral_add_error c h hm hn hi hr hgi
    linarith

/-- A regular complex measure vanishes if every C0 integral vanishes. -/
theorem theorem_6_19_zero (c : ComplexMeasure X) [c.variation.Regular]
    (hc : ∀ f : ZeroAtInftyContinuousMap X ℂ, complexIntegral c f = 0) : c = 0 := by
  have hmass : c.variation.real univ = 0 :=
    (theorem_6_19_norm c 0 (fun f ↦ (hc f).symm)).symm.trans
      (norm_zero : ‖(0 : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ)‖ = 0)
  apply VectorMeasure.variation_eq_zero.mp
  apply Measure.measure_univ_eq_zero.mp
  exact (measureReal_eq_zero_iff (measure_ne_top c.variation univ)).mp hmass

/-- Uniqueness of the regular complex Borel representing measure in 6.19. -/
theorem theorem_6_19_unique (c d : ComplexMeasure X)
    [c.variation.Regular] [d.variation.Regular]
    (h : ∀ f : ZeroAtInftyContinuousMap X ℂ, complexIntegral c f = complexIntegral d f) : c = d := by
  letI : (c - d).variation.Regular := complex_variation_sub_regular c d
  apply sub_eq_zero.mp
  apply theorem_6_19_zero (c - d)
  intro f
  have hc : c.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  have hd : d.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  change (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; c - d]) = 0
  rw [VectorMeasure.integral_sub_vectorMeasure hc hd]
  exact sub_eq_zero.mpr (h f)

#print axioms polar_mass_le_integral_add_error
#print axioms theorem_6_19_norm
#print axioms theorem_6_19_zero
#print axioms theorem_6_19_unique
end RudinRCA.Chapter06
-- END SOURCE Scratch619Uniqueness.lean

-- BEGIN SOURCE Scratch619PositivePart.lean








noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ENNReal

namespace RCA619PositivePart

variable {X : Type*} [TopologicalSpace X]

abbrev Values (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : Set ℝ :=
  L '' Icc 0 f.toReal

theorem values_nonempty (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) :
    (Values L f).Nonempty :=
  ⟨0, 0, ⟨le_rfl, CompactlySupportedContinuousMap.toReal_nonneg⟩, map_zero L⟩

/-- The upper positive part on the cone of nonnegative compactly supported functions. -/
def posSup (L : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : ℝ := sSup (Values L f)

variable (L : C_c(X, ℝ) →ₗ[ℝ] ℝ)
variable (hbdd : ∀ f : C_c(X, ℝ≥0), BddAbove (Values L f))

include hbdd in
theorem le_posSup {f : C_c(X, ℝ≥0)} {g : C_c(X, ℝ)}
    (hg0 : 0 ≤ g) (hgf : g ≤ f.toReal) : L g ≤ posSup L f :=
  le_csSup (hbdd f) ⟨g, ⟨hg0, hgf⟩, rfl⟩

include hbdd in
theorem posSup_nonneg (f : C_c(X, ℝ≥0)) : 0 ≤ posSup L f := by
  simpa only [map_zero] using le_posSup L hbdd (f := f) (g := 0)
    le_rfl CompactlySupportedContinuousMap.toReal_nonneg

theorem posSup_le {f : C_c(X, ℝ≥0)} {B : ℝ}
    (hB : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f.toReal → L g ≤ B) : posSup L f ≤ B := by
  apply csSup_le (values_nonempty L f)
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact hB g hg0 hgf

include hbdd in
theorem posSup_zero : posSup L 0 = 0 := by
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hg
    have hg' : g ≤ 0 := by
      intro x
      simpa using hg x
    rw [le_antisymm hg' hg0, map_zero]
  · exact posSup_nonneg L hbdd 0

include hbdd in
theorem posSup_add (f h : C_c(X, ℝ≥0)) :
    posSup L (f + h) = posSup L f + posSup L h := by
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hgf
    let g₁ : C_c(X, ℝ) := g ⊓ f.toReal
    let g₂ : C_c(X, ℝ) := g - g₁
    have hg₁0 : 0 ≤ g₁ := le_inf hg0 CompactlySupportedContinuousMap.toReal_nonneg
    have hg₁f : g₁ ≤ f.toReal := inf_le_right
    have hg₂0 : 0 ≤ g₂ := by
      intro x
      change 0 ≤ g x - min (g x) (f.toReal x)
      exact sub_nonneg.mpr (min_le_left _ _)
    have hg₂h : g₂ ≤ h.toReal := by
      intro x
      have hgfx := hgf x
      have hh0 : 0 ≤ (h.toReal x) := CompactlySupportedContinuousMap.toReal_nonneg x
      rw [CompactlySupportedContinuousMap.toReal_add,
        CompactlySupportedContinuousMap.add_apply] at hgfx
      change g x - min (g x) (f.toReal x) ≤ h.toReal x
      rcases le_total (g x) (f.toReal x) with hx | hx
      · rw [min_eq_left hx, sub_self]
        exact hh0
      · rw [min_eq_right hx]
        linarith
    have h₁ := le_posSup L hbdd hg₁0 hg₁f
    have h₂ := le_posSup L hbdd hg₂0 hg₂h
    have hsplit : L g₂ = L g - L g₁ := map_sub L g g₁
    linarith
  · have hfirst : posSup L f ≤ posSup L (f + h) - posSup L h := by
      apply posSup_le
      intro g hg0 hgf
      have hsecond : posSup L h ≤ posSup L (f + h) - L g := by
        apply posSup_le
        intro k hk0 hkh
        have hsum0 : 0 ≤ g + k := fun x ↦ add_nonneg (hg0 x) (hk0 x)
        have hsum : g + k ≤ (f + h).toReal := by
          intro x
          rw [CompactlySupportedContinuousMap.toReal_add,
            CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.add_apply]
          exact add_le_add (hgf x) (hkh x)
        have hle := le_posSup L hbdd hsum0 hsum
        rw [map_add] at hle
        linarith
      linarith
    linarith

include hbdd in
theorem posSup_smul (r : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    posSup L (r • f) = (r : ℝ) * posSup L f := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_smul, posSup_zero L hbdd, NNReal.coe_zero, zero_mul]
  have hrpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  apply le_antisymm
  · apply posSup_le
    intro g hg0 hgf
    let k : C_c(X, ℝ) := (r : ℝ)⁻¹ • g
    have hk0 : 0 ≤ k := fun x ↦ mul_nonneg (inv_nonneg.mpr hrpos.le) (hg0 x)
    have hkf : k ≤ f.toReal := by
      intro x
      have hx : g x ≤ (r : ℝ) * f.toReal x := by
        simpa only [CompactlySupportedContinuousMap.toReal_apply,
          CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
          NNReal.coe_mul] using hgf x
      change (r : ℝ)⁻¹ * g x ≤ f.toReal x
      exact (inv_mul_le_iff₀ hrpos).mpr hx
    have hle := le_posSup L hbdd hk0 hkf
    have hmap : L k = (r : ℝ)⁻¹ * L g := map_smul L _ g
    rw [hmap] at hle
    exact (inv_mul_le_iff₀ hrpos).mp hle
  · have hle : posSup L f ≤ (r : ℝ)⁻¹ * posSup L (r • f) := by
      apply posSup_le
      intro g hg0 hgf
      have hrg0 : 0 ≤ (r : ℝ) • g := fun x ↦ mul_nonneg hrpos.le (hg0 x)
      have hrgf : (r : ℝ) • g ≤ (r • f).toReal := by
        intro x
        simpa only [CompactlySupportedContinuousMap.toReal_apply,
          CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
          NNReal.coe_mul] using mul_le_mul_of_nonneg_left (hgf x) hrpos.le
      have hbound := le_posSup L hbdd hrg0 hrgf
      rw [map_smul] at hbound
      change (r : ℝ) * L g ≤ posSup L (r • f) at hbound
      exact (le_inv_mul_iff₀ hrpos).mpr hbound
    exact (le_inv_mul_iff₀ hrpos).mp hle

/-- The additive, homogeneous positive part on the nonnegative cone. -/
def positiveConeLinear : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨posSup L f, posSup_nonneg L hbdd f⟩
  map_add' f g := by
    apply NNReal.eq
    exact posSup_add L hbdd f g
  map_smul' r f := by
    apply NNReal.eq
    exact posSup_smul L hbdd r f

/-- Extending the cone map by positive and negative parts gives a positive
real-linear functional on all real-valued compactly supported functions. -/
def positivePart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  CompactlySupportedContinuousMap.toRealPositiveLinear (positiveConeLinear L hbdd)

theorem positivePart_toReal (f : C_c(X, ℝ≥0)) :
    positivePart L hbdd f.toReal = posSup L f :=
  CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal _ _

theorem le_positivePart {f : C_c(X, ℝ)} (hf : 0 ≤ f) : L f ≤ positivePart L hbdd f := by
  have hfreal : f.nnrealPart.toReal = f := by
    ext x
    simp only [CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal' ]
    exact max_eq_left (hf x)
  rw [← hfreal, positivePart_toReal]
  apply le_posSup L hbdd
  · exact CompactlySupportedContinuousMap.toReal_nonneg
  · exact le_rfl

/-- The complementary positive functional. -/
def negativePart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((positivePart L hbdd).toLinearMap - L)
    (fun f hf ↦ sub_nonneg.mpr (le_positivePart L hbdd hf))

theorem positivePart_sub_negativePart (f : C_c(X, ℝ)) :
    positivePart L hbdd f - negativePart L hbdd f = L f := by
  change positivePart L hbdd f - (positivePart L hbdd f - L f) = L f
  linarith

theorem norm_le_of_nonneg_le {g f : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    ‖g.toBoundedContinuousFunction‖ ≤ ‖f.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f.toBoundedContinuousFunction)).mpr
  intro x
  change ‖g x‖ ≤ ‖f.toBoundedContinuousFunction‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
  exact (hgf x).trans (BoundedContinuousFunction.apply_le_norm f.toBoundedContinuousFunction x)

/-- A uniform bound for the original functional supplies the order boundedness
needed by the supremum construction. -/
theorem values_bddAbove_of_bound {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖)
    (f : C_c(X, ℝ≥0)) : BddAbove (Values L f) := by
  refine ⟨C * ‖f.toReal.toBoundedContinuousFunction‖, ?_⟩
  rintro _ ⟨g, ⟨hg0, hgf⟩, rfl⟩
  exact (le_abs_self _).trans ((hL g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_nonneg_le hg0 hgf) hC))

theorem positivePart_bound {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    positivePart L hbdd f ≤ C * ‖f.toBoundedContinuousFunction‖ := by
  have hfreal : f.nnrealPart.toReal = f := by
    ext x
    simp only [CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal']
    exact max_eq_left (hf x)
  conv_lhs => rw [← hfreal, positivePart_toReal]
  apply posSup_le
  intro g hg0 hgf
  rw [hfreal] at hgf
  exact (le_abs_self _).trans ((hL g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_nonneg_le hg0 hgf) hC))

/-- Every bounded real linear functional on compactly supported functions is
the difference of two positive linear functionals. Their bounds on positive
functions make both representing RMK measures finite on arbitrary LCH spaces. -/
theorem exists_positive_decomposition {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ P Q : C_c(X, ℝ) →ₚ[ℝ] ℝ,
      (∀ f : C_c(X, ℝ), L f = P f - Q f) ∧
      (∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) ∧
      (∀ f : C_c(X, ℝ), 0 ≤ f → Q f ≤ (2 * C) * ‖f.toBoundedContinuousFunction‖) := by
  let hb : ∀ f : C_c(X, ℝ≥0), BddAbove (Values L f) := values_bddAbove_of_bound L hC hL
  refine ⟨positivePart L hb, negativePart L hb, ?_, ?_, ?_⟩
  · intro f
    exact (positivePart_sub_negativePart L hb f).symm
  · intro f hf
    exact positivePart_bound L hb hC hL hf
  · intro f hf
    change positivePart L hb f - L f ≤ (2 * C) * ‖f.toBoundedContinuousFunction‖
    have hP := positivePart_bound L hb hC hL hf
    have hF := (abs_le.mp (hL f)).1
    linarith

#print axioms posSup_add
#print axioms posSup_smul
#print axioms exists_positive_decomposition

section FiniteRMK

variable [LocallyCompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The positive RMK measure of a bounded functional is finite even when the
locally compact Hausdorff space is not sigma compact. -/
theorem rieszMeasure_univ_le (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) :
    RealRMK.rieszMeasure P univ ≤ ENNReal.ofReal C := by
  rw [isOpen_univ.measure_eq_iSup_isCompact (RealRMK.rieszMeasure P)]
  refine iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨φ, hφK, hφcomp, _, hφrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f : C_c(X, ℝ) := ⟨φ, hφcomp⟩
  have hf0 : 0 ≤ f := fun x ↦ (hφrange x).1
  have hfnorm : ‖f.toBoundedContinuousFunction‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro x
    change ‖φ x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hφrange x).1]
    exact (hφrange x).2
  have hPf : P f ≤ C := (hP f hf0).trans (by nlinarith)
  exact (RealRMK.rieszMeasure_le_of_eq_one P hf0 hK hφK).trans
    (ENNReal.ofReal_le_ofReal hPf)

theorem rieszMeasure_isFiniteMeasure (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ f : C_c(X, ℝ), 0 ≤ f → P f ≤ C * ‖f.toBoundedContinuousFunction‖) :
    MeasureTheory.IsFiniteMeasure (RealRMK.rieszMeasure P) := by
  constructor
  exact (rieszMeasure_univ_le P hC hP).trans_lt ENNReal.ofReal_lt_top

/-- The two finite positive measures representing a bounded real functional,
stated with ordinary Bochner integrals for complex-measure assembly. -/
theorem exists_finite_measure_representation {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.Regular ∧ ν.Regular ∧
      ∀ f : C_c(X, ℝ), L f = (∫ x, f x ∂μ) - ∫ x, f x ∂ν := by
  obtain ⟨P, Q, hdiff, hP, hQ⟩ := exists_positive_decomposition L hC hL
  let μ : Measure X := RealRMK.rieszMeasure P
  let ν : Measure X := RealRMK.rieszMeasure Q
  letI : IsFiniteMeasure μ := rieszMeasure_isFiniteMeasure P hC hP
  letI : IsFiniteMeasure ν := rieszMeasure_isFiniteMeasure Q (by linarith) hQ
  refine ⟨μ, ν, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro f
  simpa only [μ, ν, RealRMK.integral_rieszMeasure] using hdiff f

/-- Real representation assembled from the positive parts. The accompanying
finite regular measures dominate the signed measure's variation, allowing the
general regularity-under-domination lemma to establish its regularity. -/
theorem exists_signed_representation {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : C_c(X, ℝ), |L g| ≤ C * ‖g.toBoundedContinuousFunction‖) :
    ∃ s : SignedMeasure X, ∃ μ ν : Measure X,
      IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.Regular ∧ ν.Regular ∧
      s.variation ≤ μ + ν ∧
      ∀ f : C_c(X, ℝ), L f = ∫ᵛ x, f x ∂<•s := by
  obtain ⟨P, Q, hdiff, hP, hQ⟩ := exists_positive_decomposition L hC hL
  let μ : Measure X := RealRMK.rieszMeasure P
  let ν : Measure X := RealRMK.rieszMeasure Q
  letI : IsFiniteMeasure μ := rieszMeasure_isFiniteMeasure P hC hP
  letI : IsFiniteMeasure ν := rieszMeasure_isFiniteMeasure Q (by linarith) hQ
  let s : SignedMeasure X := μ.toSignedMeasure - ν.toSignedMeasure
  refine ⟨s, μ, ν, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · simpa only [s, Measure.variation_toSignedMeasure] using
      (VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := ν.toSignedMeasure))
  · intro f
    have hfμ : μ.toSignedMeasure.Integrable f := by
      simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
        ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport : Integrable f μ)
    have hfν : ν.toSignedMeasure.Integrable f := by
      simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
        ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport : Integrable f ν)
    rw [show s = μ.toSignedMeasure - ν.toSignedMeasure from rfl,
      VectorMeasure.integral_sub_vectorMeasure hfμ hfν,
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
    exact (hdiff f).trans (by
      rw [show μ = RealRMK.rieszMeasure P from rfl,
        show ν = RealRMK.rieszMeasure Q from rfl,
        RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure])

#print axioms rieszMeasure_univ_le
#print axioms rieszMeasure_isFiniteMeasure
#print axioms exists_finite_measure_representation
#print axioms exists_signed_representation

end FiniteRMK

end RCA619PositivePart
-- END SOURCE Scratch619PositivePart.lean

-- BEGIN SOURCE Scratch619Assembly.lean





noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace RudinRCA.Chapter06

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

/-- A positive measure with a constant complex density of modulus one. -/
def unitComplexMeasure (μ : Measure X) (z : ℂ) : ComplexMeasure X :=
  μ.withDensityᵥ (fun _ ↦ z)

theorem unitComplexMeasure_variation (μ : Measure X) [IsFiniteMeasure μ]
    (z : ℂ) (hz : ‖z‖ = 1) : (unitComplexMeasure μ z).variation = μ := by
  rw [unitComplexMeasure, Measure.variation_withDensityᵥ (integrable_const z)]
  have hn : (fun _ : X ↦ ‖z‖ₑ) = (1 : X → ℝ≥0∞) := by
    funext x
    rw [← ofReal_norm, hz]
    simp
  rw [hn, withDensity_one]

theorem unitComplexMeasure_integral (μ : Measure X) [IsFiniteMeasure μ]
    (z : ℂ) (hz : ‖z‖ = 1) (f : ZeroAtInftyContinuousMap X ℂ) :
    complexIntegral (unitComplexMeasure μ z) f = (∫ x, f x ∂μ) * z := by
  let c := unitComplexMeasure μ z
  have hv : c.variation = μ := unitComplexMeasure_variation μ z hz
  have hi : Integrable (fun _ : X ↦ z) c.variation := by rw [hv]; exact integrable_const z
  have hr : c.variation.withDensityᵥ (fun _ : X ↦ z) = c := by rw [hv]; rfl
  have hf : Integrable (fun x ↦ f x) c.variation :=
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  calc
    complexIntegral c f = ∫ x, f x * z ∂c.variation :=
      vectorIntegral_eq_polar c (fun _ ↦ z) measurable_const (fun _ ↦ hz) hi hr hf
    _ = (∫ x, f x ∂μ) * z := by rw [hv, integral_mul_const]

private theorem complexIntegral_sub_C0 (a b : ComplexMeasure X)
    (f : ZeroAtInftyContinuousMap X ℂ) :
    complexIntegral (a - b) f = complexIntegral a f - complexIntegral b f := by
  have ha : a.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  have hb : b.Integrable f := Integrable.of_bound f.continuous.measurable.aestronglyMeasurable
    ‖f‖ (ae_of_all _ fun x ↦ f.toBCF.norm_coe_le_norm x)
  exact VectorMeasure.integral_sub_vectorMeasure ha hb

/-- Inclusion of real compactly supported functions into complex C0. -/
def realCcToComplexC0 : C_c(X, ℝ) →ₗ[ℝ] ZeroAtInftyContinuousMap X ℂ where
  toFun g :=
    { toFun := fun x ↦ (g x : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp g.continuous
      zero_at_infty' := (g.hasCompactSupport.comp_left (map_zero Complex.ofRealHom)).is_zero_at_infty }
  map_add' f g := by ext x; simp
  map_smul' r f := by ext x; simp

theorem realCcToComplexC0_norm_le (g : C_c(X, ℝ)) :
    ‖realCcToComplexC0 g‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
  change ‖(realCcToComplexC0 g).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  change ‖(g x : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  exact g.toBoundedContinuousFunction.norm_coe_le_norm x

/-- Rudin 6.19: existence, uniqueness, and exact norm, for every locally compact
Hausdorff space. No sigma-compactness, normality, or countability is assumed. -/
theorem theorem_6_19 (Φ : ZeroAtInftyContinuousMap X ℂ →L[ℂ] ℂ) :
    ∃ c : ComplexMeasure X, IsRegularComplexMeasure c ∧
      (∀ f, Φ f = complexIntegral c f) ∧ ‖Φ‖ = c.variation.real univ ∧
      ∀ d : ComplexMeasure X, IsRegularComplexMeasure d →
        (∀ f, Φ f = complexIntegral d f) → d = c := by
  let J := realCcToComplexC0 (X := X)
  let Lr : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    Complex.reCLM.toLinearMap.comp ((Φ.restrictScalars ℝ).toLinearMap.comp J)
  let Li : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    Complex.imCLM.toLinearMap.comp ((Φ.restrictScalars ℝ).toLinearMap.comp J)
  have hLr (g : C_c(X, ℝ)) : |Lr g| ≤ ‖Φ‖ * ‖g.toBoundedContinuousFunction‖ := by
    change |(Φ (J g)).re| ≤ _
    exact (Complex.abs_re_le_norm _).trans ((Φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (realCcToComplexC0_norm_le g) (norm_nonneg Φ)))
  have hLi (g : C_c(X, ℝ)) : |Li g| ≤ ‖Φ‖ * ‖g.toBoundedContinuousFunction‖ := by
    change |(Φ (J g)).im| ≤ _
    exact (Complex.abs_im_le_norm _).trans ((Φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (realCcToComplexC0_norm_le g) (norm_nonneg Φ)))
  obtain ⟨μr, νr, hμrf, hνrf, hμrr, hνrr, hR⟩ :=
    RCA619PositivePart.exists_finite_measure_representation Lr (norm_nonneg Φ) hLr
  obtain ⟨μi, νi, hμif, hνif, hμir, hνir, hI⟩ :=
    RCA619PositivePart.exists_finite_measure_representation Li (norm_nonneg Φ) hLi
  letI : IsFiniteMeasure μr := hμrf
  letI : IsFiniteMeasure νr := hνrf
  letI : IsFiniteMeasure μi := hμif
  letI : IsFiniteMeasure νi := hνif
  letI : μr.Regular := hμrr
  letI : νr.Regular := hνrr
  letI : μi.Regular := hμir
  letI : νi.Regular := hνir
  let a := unitComplexMeasure μr 1
  let b := unitComplexMeasure νr 1
  let d := unitComplexMeasure μi Complex.I
  let e := unitComplexMeasure νi Complex.I
  let c := (a - b) + (d - e)
  have ha : a.variation = μr := unitComplexMeasure_variation μr 1 (by simp)
  have hb : b.variation = νr := unitComplexMeasure_variation νr 1 (by simp)
  have hd : d.variation = μi := unitComplexMeasure_variation μi Complex.I (by simp)
  have he : e.variation = νi := unitComplexMeasure_variation νi Complex.I (by simp)
  have hdom : c.variation ≤ (μr + νr) + (μi + νi) := by
    calc
      c.variation ≤ (a - b).variation + (d - e).variation := VectorMeasure.variation_add_le
      _ ≤ (a.variation + b.variation) + (d.variation + e.variation) :=
        add_le_add VectorMeasure.variation_sub_le VectorMeasure.variation_sub_le
      _ = _ := by rw [ha, hb, hd, he]
  letI : c.variation.Regular := regular_of_le_finite_regular ((μr + νr) + (μi + νi)) _ hdom
  obtain ⟨Ψ, hΨ, _⟩ := theorem_6_18_functional c
  have hreal (g : C_c(X, ℝ)) : Φ (J g) = Ψ (J g) := by
    rw [hΨ]
    change Φ (J g) = complexIntegral ((a - b) + (d - e)) (J g)
    rw [theorem_6_18_add (a - b) (d - e) (J g) (J g).continuous.measurable
      ‖J g‖ (fun x ↦ (J g).toBCF.norm_coe_le_norm x),
      complexIntegral_sub_C0, complexIntegral_sub_C0]
    rw [show a = unitComplexMeasure μr 1 from rfl,
      show b = unitComplexMeasure νr 1 from rfl,
      show d = unitComplexMeasure μi Complex.I from rfl,
      show e = unitComplexMeasure νi Complex.I from rfl,
      unitComplexMeasure_integral μr 1 (by simp), unitComplexMeasure_integral νr 1 (by simp),
      unitComplexMeasure_integral μi Complex.I (by simp),
      unitComplexMeasure_integral νi Complex.I (by simp)]
    have hexp : Φ (J g) = (Lr g : ℂ) + (Li g : ℂ) * Complex.I :=
      (Complex.re_add_im (Φ (J g))).symm
    rw [hexp, hR, hI]
    have hJ : (J g : X → ℂ) = fun x ↦ (g x : ℂ) := rfl
    simp only [hJ, integral_ofReal, mul_one, Complex.ofReal_sub, sub_mul]
  have hΦΨ : Φ = Ψ := by
    apply DFunLike.ext'
    apply Φ.continuous.ext_on (RCA618.dense_compactSupport X) Ψ.continuous
    intro f hf
    let fr : C_c(X, ℝ) :=
      ⟨⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩,
        hf.comp_left (by simp)⟩
    let fi : C_c(X, ℝ) :=
      ⟨⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩,
        hf.comp_left (by simp)⟩
    have hsplit : f = J fr + Complex.I • J fi := by
      ext x
      change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
      simpa only [mul_comm] using (Complex.re_add_im (f x)).symm
    rw [hsplit, map_add, map_smul, map_add, map_smul, hreal fr, hreal fi]
  have hrep (f) : Φ f = complexIntegral c f := by rw [hΦΨ]; exact hΨ f
  refine ⟨c, (show IsRegularComplexMeasure c from (inferInstance : c.variation.Regular)),
    hrep, theorem_6_19_norm c Φ hrep, ?_⟩
  intro d hd hrepd
  letI : d.variation.Regular := hd
  exact theorem_6_19_unique d c (fun f ↦ (hrepd f).symm.trans (hrep f))

#print axioms unitComplexMeasure_variation
#print axioms unitComplexMeasure_integral
#print axioms realCcToComplexC0_norm_le
#print axioms theorem_6_19
end RudinRCA.Chapter06
-- END SOURCE Scratch619Assembly.lean

