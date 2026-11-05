import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.MutuallySingular

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
