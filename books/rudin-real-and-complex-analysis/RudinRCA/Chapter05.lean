import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import RudinRCA.Chapter04

/-! Rudin RCA Chapter 5. See INVENTORY-B.md and SCOPING-B.md. -/

/- BEGIN Chapter05Foundations.lean -/
section







/-! Chapter 5, §§5.1–5.7 and the first assertion of §5.13.
Sections 5.1 and 5.5 are introductory prose; the declarations below cover their
subsequent mathematical definitions and statements. See SCOPING-B.md for the
nonempty-space correction at 5.7 and 5.13. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal ZeroAtInfty

namespace RudinRCA.Chapter05

section NormedSpaces

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- 5.2(a–c), simultaneously over the real and complex scalars. -/
theorem normed_space_axioms (a : 𝕜) (x y : X) :
    0 ≤ ‖x‖ ∧ ‖x + y‖ ≤ ‖x‖ + ‖y‖ ∧
      ‖a • x‖ = ‖a‖ * ‖x‖ ∧ (‖x‖ = 0 ↔ x = 0) :=
  ⟨norm_nonneg _, norm_add_le _ _, norm_smul _ _, norm_eq_zero⟩

/-- 5.2: the metric induced by the norm and its triangle inequality. -/
theorem norm_induced_metric (x y z : X) :
    dist x y = ‖x - y‖ ∧ ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
  exact ⟨dist_eq_norm _ _, by simpa only [dist_eq_norm] using dist_triangle x z y⟩

/-- 5.3(1), including the value infinity for an unbounded algebraic linear map. -/
def extendedOperatorNorm (A : X →ₗ[𝕜] Y) : ℝ≥0∞ :=
  ⨆ x : {x : X // ‖x‖ ≤ 1}, (‖A x‖₊ : ℝ≥0∞)

/-- A real global norm bound, without presupposing continuity. -/
def IsBoundedLinear (A : X →ₗ[𝕜] Y) : Prop :=
  ∃ C : ℝ, ∀ x : X, ‖A x‖ ≤ C * ‖x‖

/-- Finiteness in the printed definition is equivalent to a global norm bound. -/
theorem finite_extendedOperatorNorm_iff (A : X →ₗ[𝕜] Y) :
    extendedOperatorNorm A < ⊤ ↔ IsBoundedLinear A := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := ENNReal.iSup_coe_lt_top.mp h
    apply A.bound_of_ball_bound (r := 1) zero_lt_one (C : ℝ)
    intro z hz
    have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hb := hC (Set.mem_range_self (⟨z, hz'⟩ : {x : X // ‖x‖ ≤ 1}))
    exact_mod_cast hb
  · rintro ⟨C, hC⟩
    let B : X →L[𝕜] Y := A.mkContinuous C hC
    apply ENNReal.iSup_coe_lt_top.mpr
    refine ⟨‖B‖₊, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact B.unit_le_opNorm x x.property

/-- 5.3: unit vectors give the same extended supremum even for an unbounded
algebraic linear map. The empty supremum is zero for the zero space. -/
theorem extendedOperatorNorm_sphere (A : X →ₗ[𝕜] Y) :
    extendedOperatorNorm A =
      ⨆ x : {x : X // ‖x‖ = 1}, (‖A x‖₊ : ℝ≥0∞) := by
  unfold extendedOperatorNorm
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : (x : X) = 0
    · simp [hx]
    have hn : 0 < ‖(x : X)‖ := norm_pos_iff.mpr hx
    let y : X := ((‖(x : X)‖ : 𝕜)⁻¹) • (x : X)
    have hy : ‖y‖ = 1 := by
      simp only [y, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg (x : X))]
      exact inv_mul_cancel₀ hn.ne'
    have hm : ‖A y‖ * ‖(x : X)‖ = ‖A x‖ := by
      simp only [y, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg (x : X))]
      field_simp [hn.ne']
    have hb : ‖A x‖ ≤ ‖A y‖ := by
      calc
        ‖A x‖ = ‖A y‖ * ‖(x : X)‖ := hm.symm
        _ ≤ ‖A y‖ * 1 := mul_le_mul_of_nonneg_left x.property (norm_nonneg _)
        _ = ‖A y‖ := mul_one _
    have hb' : ‖A x‖₊ ≤ ‖A y‖₊ := by exact_mod_cast hb
    exact (ENNReal.coe_le_coe.mpr hb').trans
      (le_iSup (fun z : {z : X // ‖z‖ = 1} => (‖A z‖₊ : ℝ≥0∞)) ⟨y, hy⟩)
  · apply iSup_le
    intro x
    exact le_iSup_of_le (⟨(x : X), x.property.le⟩ : {x : X // ‖x‖ ≤ 1}) le_rfl

/-- The pointwise operator bound also holds in the extended nonnegative reals. -/
theorem apply_le_extendedOperatorNorm (A : X →ₗ[𝕜] Y) (x : X) :
    (‖A x‖₊ : ℝ≥0∞) ≤ extendedOperatorNorm A * (‖x‖₊ : ℝ≥0∞) := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : X := ((‖x‖ : 𝕜)⁻¹) • x
  have hy : ‖y‖ = 1 := by
    simp only [y, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x)]
    exact inv_mul_cancel₀ hn.ne'
  have hm : ‖A y‖ * ‖x‖ = ‖A x‖ := by
    simp only [y, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x)]
    field_simp [hn.ne']
  have hm' : ‖A x‖₊ = ‖A y‖₊ * ‖x‖₊ := by
    apply Subtype.ext
    exact hm.symm
  rw [hm', ENNReal.coe_mul]
  exact mul_le_mul_left
    (le_iSup (fun z : {z : X // ‖z‖ ≤ 1} => (‖A z‖₊ : ℝ≥0∞)) ⟨y, hy.le⟩) _

/-- 5.3(3), with no boundedness premise: the extended norm is the least
extended scalar giving a pointwise norm bound. -/
theorem extendedOperatorNorm_least (A : X →ₗ[𝕜] Y) :
    IsLeast {C : ℝ≥0∞ | ∀ x, (‖A x‖₊ : ℝ≥0∞) ≤ C * (‖x‖₊ : ℝ≥0∞)}
      (extendedOperatorNorm A) := by
  refine ⟨apply_le_extendedOperatorNorm A, ?_⟩
  intro C hC
  apply iSup_le
  intro x
  have hx : (‖(x : X)‖₊ : ℝ≥0∞) ≤ 1 := by exact_mod_cast x.property
  exact (hC x).trans ((mul_le_mul_right hx C).trans_eq (mul_one C))

/-- 5.3(1): the bounded operator norm is exactly the closed-unit-ball supremum. -/
theorem operator_norm_closed_ball (A : X →L[𝕜] Y) :
    sSup ((fun x => ‖A x‖₊) '' Metric.closedBall 0 1) = ‖A‖₊ :=
  A.sSup_unitClosedBall_eq_nnnorm

/-- 5.3: unit vectors give the same supremum. The NNReal empty supremum is zero,
so this statement also covers the zero-dimensional domain. -/
theorem operator_norm_sphere (A : X →L[𝕜] Y) :
    sSup ((fun x => ‖A x‖₊) '' Metric.sphere 0 1) = ‖A‖₊ :=
  A.sSup_sphere_eq_nnnorm

/-- 5.3(2): scalar homogeneity for an algebraic linear map. -/
theorem linear_map_norm_smul (A : X →ₗ[𝕜] Y) (a : 𝕜) (x : X) :
    ‖A (a • x)‖ = ‖a‖ * ‖A x‖ := by rw [map_smul, norm_smul]

/-- 5.3(3): the operator norm is the least nonnegative bound. -/
theorem operator_norm_least (A : X →L[𝕜] Y) :
    IsLeast {C : ℝ≥0 | ∀ x, ‖A x‖₊ ≤ C * ‖x‖₊} ‖A‖₊ :=
  A.isLeast_opNNNorm

/-- 5.3(4): the image of the closed unit ball is in the indicated closed ball. -/
theorem operator_maps_unit_ball (A : X →L[𝕜] Y) :
    MapsTo A (Metric.closedBall 0 1) (Metric.closedBall 0 ‖A‖) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx ⊢
  exact A.unit_le_opNorm x hx

/-- 5.4(a) iff (b); completeness is unnecessary. -/
theorem bounded_iff_continuous (A : X →ₗ[𝕜] Y) :
    IsBoundedLinear A ↔ Continuous A := by
  constructor
  · rintro ⟨C, hC⟩
    exact (A.mkContinuous C hC).continuous
  · intro h
    let B : X →L[𝕜] Y := ⟨A, h⟩
    exact ⟨‖B‖, B.le_opNorm⟩

/-- 5.4(c) implies continuity everywhere, at an arbitrary chosen point. -/
theorem linear_continuous_of_continuousAt (A : X →ₗ[𝕜] Y) (x₀ : X)
    (h : ContinuousAt A x₀) : Continuous A := by
  apply continuous_of_continuousAt_zero A
  have hshift : ContinuousAt (fun x : X => A (x + x₀)) 0 :=
    h.comp_of_eq (continuousAt_id.add continuousAt_const) (zero_add x₀)
  simpa only [ContinuousAt, map_add, add_sub_cancel_right] using hshift.sub_const (A x₀)

/-- 5.4: the three printed conditions are equivalent. -/
theorem bounded_continuous_at_one_point (A : X →ₗ[𝕜] Y) :
    (extendedOperatorNorm A < ⊤ ↔ Continuous A) ∧
      (Continuous A ↔ ∃ x₀ : X, ContinuousAt A x₀) := by
  refine ⟨(finite_extendedOperatorNorm_iff A).trans (bounded_iff_continuous A), ?_⟩
  exact ⟨fun h => ⟨0, h.continuousAt⟩,
    fun ⟨x₀, h⟩ => linear_continuous_of_continuousAt A x₀ h⟩

end NormedSpaces

/-- 5.2: a Hilbert space has the required complete norm metric. -/
theorem hilbert_is_banach {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : CompleteSpace H := inferInstance

/-- 5.2: the Lp examples use equivalence classes modulo almost-everywhere equality. -/
theorem lp_is_banach {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : CompleteSpace (Lp ℂ p μ) := inferInstance

/-- 5.2: continuous functions vanishing at infinity, with the supremum norm. -/
theorem vanishing_at_infinity_is_banach {X : Type*} [TopologicalSpace X] :
    CompleteSpace C₀(X, ℂ) := inferInstance

/-- 5.2: the scalar complex field is a Banach space. -/
theorem complex_is_banach : CompleteSpace ℂ := inferInstance

/-- The warning in the proof of 5.6 holds even at a positive radius:
in the complete discrete metric space ℤ, the open unit ball is already closed. -/
theorem closure_ball_ne_closedBall :
    0 < (1 : ℝ) ∧ closure (Metric.ball (0 : ℤ) 1) ≠ Metric.closedBall (0 : ℤ) 1 := by
  refine ⟨zero_lt_one, ?_⟩
  rw [(isClosed_discrete (Metric.ball (0 : ℤ) 1)).closure_eq]
  intro h
  have hm : (1 : ℤ) ∈ Metric.closedBall (0 : ℤ) 1 := by
    norm_num [Metric.mem_closedBall, dist_eq_norm]
  rw [← h] at hm
  norm_num [Metric.mem_ball, dist_eq_norm] at hm

section Category

variable {X ι : Type*} [MetricSpace X] [CompleteSpace X]

/-- 5.6: Baire's theorem, with every countable index type. -/
theorem baire_dense_intersection [Countable ι] (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hd : ∀ i, Dense (U i)) :
    Dense (⋂ i, U i) := dense_iInter_of_isOpen ho hd

/-- The explicitly nonempty conclusion in 5.6. -/
theorem baire_nonempty_intersection [Nonempty X] [Countable ι]
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hd : ∀ i, Dense (U i)) :
    (⋂ i, U i).Nonempty := (baire_dense_intersection U ho hd).nonempty

/-- The corollary in 5.6, retaining both density and the Gδ property. -/
theorem baire_dense_gdelta_intersection [Countable ι] (U : ι → Set X)
    (hg : ∀ i, IsGδ (U i)) (hd : ∀ i, Dense (U i)) :
    IsGδ (⋂ i, U i) ∧ Dense (⋂ i, U i) :=
  ⟨IsGδ.iInter hg, dense_iInter_of_Gδ hg hd⟩

omit [CompleteSpace X] in
/-- 5.7: nowhere dense means that the interior of the closure is empty. -/
theorem nowhere_dense_definition (E : Set X) :
    IsNowhereDense E ↔ interior (closure E) = ∅ := Iff.rfl

omit [CompleteSpace X] in
/-- 5.7: first category is precisely a countable union of nowhere dense sets. -/
theorem first_category_definition (E : Set X) :
    IsMeagre E ↔ ∃ S : Set (Set X), S.Countable ∧
      (∀ t ∈ S, IsNowhereDense t) ∧ E = ⋃₀ S := by
  constructor
  · intro h
    obtain ⟨S, hS, hc, hsub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp h
    refine ⟨(fun t => E ∩ t) '' S, hc.image _, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hS t ht).mono inter_subset_right
    · ext x
      simp only [mem_sUnion, mem_image, exists_exists_and_eq_and, mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp (hsub hx)
        exact ⟨t, ht, hx, hxt⟩
      · rintro ⟨t, ht, hx, hxt⟩
        exact hx
  · rintro ⟨S, hc, hS, rfl⟩
    exact isMeagre_iff_countable_union_isNowhereDense.mpr ⟨S, hS, hc, Subset.rfl⟩

/-- 5.7 corrected: a nonempty complete metric space is not of first category. -/
theorem complete_space_not_first_category [Nonempty X] :
    ¬ IsMeagre (univ : Set X) :=
  not_isMeagre_of_isGδ_of_dense isOpen_univ.isGδ dense_univ

end Category

/-- The pinned library supplies a metric on `Empty`; transport it to the universe-polymorphic
empty type used in the counterexamples below. -/
local instance pemptyMetricSpace : MetricSpace PEmpty :=
  MetricSpace.induced (fun x : PEmpty => (x.elim : Empty))
    (fun x => x.elim) inferInstance

/-- The literal 5.7 assertion fails for the empty complete metric space. -/
theorem empty_complete_space_first_category :
    CompleteSpace PEmpty ∧ IsMeagre (univ : Set PEmpty) := by
  refine ⟨inferInstance, ?_⟩
  exact IsMeagre.empty.mono (by rintro x hx; exact x.elim)

section CountableDense

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [PerfectSpace X]

omit [CompleteSpace X] in
/-- Countable sets are meagre in a space with no isolated points. -/
theorem countable_is_meagre (E : Set X) (hc : E.Countable) : IsMeagre E := by
  have hs (x : X) : IsMeagre ({x} : Set X) :=
    (isClosed_singleton.isNowhereDense_iff.mpr (interior_singleton x)).isMeagre
  have h := isMeagre_biUnion hc (fun x (_ : x ∈ E) => hs x)
  simpa only [biUnion_of_singleton] using h

/-- 5.13, corrected by the necessary nonempty-space hypothesis. -/
theorem countable_dense_not_gdelta [Nonempty X] (E : Set X)
    (hc : E.Countable) (hd : Dense E) : ¬ IsGδ E := by
  intro hg
  exact not_isMeagre_of_isGδ_of_dense hg hd (countable_is_meagre E hc)

end CountableDense

/-- Empty-space counterexample to the literal wording of 5.13. -/
theorem empty_countable_dense_gdelta :
    CompleteSpace PEmpty ∧ PerfectSpace PEmpty ∧
      (univ : Set PEmpty).Countable ∧ Dense (univ : Set PEmpty) ∧
      IsGδ (univ : Set PEmpty) := by
  refine ⟨inferInstance, ⟨by rintro x hx; exact x.elim⟩, ?_, dense_univ, isOpen_univ.isGδ⟩
  exact Set.to_countable _

end RudinRCA.Chapter05
end
end
/- END Chapter05Foundations.lean -/

/- BEGIN Chapter05Banach.lean -/
section













noncomputable section
open Set Filter Metric
open scoped Topology ENNReal ComplexConjugate

namespace RudinRCA.Chapter05

section UniformBoundedness

variable {𝕜 X Y ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

omit [CompleteSpace X] in
/-- The extended supremum appearing in the proof of 5.8 is lower semicontinuous. -/
theorem operator_orbit_lowerSemicontinuous (A : ι → X →L[𝕜] Y) :
    LowerSemicontinuous (fun x => ⨆ i, (‖A i x‖₊ : ℝ≥0∞)) := by
  apply lowerSemicontinuous_iSup
  intro i
  exact (A i).continuous.enorm.lowerSemicontinuous

omit [CompleteSpace X] in
/-- The exact exceptional set in Rudin 5.8 is a countable intersection of open threshold sets,
even when the family of operators has an arbitrary index type. -/
theorem unbounded_orbit_eq_iInter (A : ι → X →L[𝕜] Y) :
    {x | ¬ BddAbove (Set.range fun i => ‖A i x‖)} =
      ⋂ n : ℕ, {x | ∃ i, (n : ℝ) < ‖A i x‖} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hx n
    by_contra! hn
    exact hx ⟨n, by rintro _ ⟨i, rfl⟩; exact hn i⟩
  · intro hx ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_gt C
    obtain ⟨i, hi⟩ := hx n
    exact (not_lt_of_ge (hC (Set.mem_range_self i))) (hn.trans hi)

/-- Rudin 5.8, residual alternative stated for the entire set of points with unbounded orbit.
Only the domain is complete; the operator family may have any index type. -/
theorem theorem_5_8_unbounded_residual (A : ι → X →L[𝕜] Y)
    (hA : ¬ BddAbove (Set.range fun i => ‖A i‖)) :
    Dense {x | ¬ BddAbove (Set.range fun i => ‖A i x‖)} ∧
      IsGδ {x | ¬ BddAbove (Set.range fun i => ‖A i x‖)} := by
  have hv : ∃ v : X, ¬ BddAbove (Set.range fun i => ‖A i v‖) := by
    by_contra! h
    apply hA
    obtain ⟨C, hC⟩ := banach_steinhaus (g := A) (fun x => by
      obtain ⟨C, hC⟩ := h x
      exact ⟨C, fun i => hC (Set.mem_range_self i)⟩)
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩
  obtain ⟨v, hv⟩ := hv
  have hv' (R : ℝ) : ∃ i, R < ‖A i v‖ := by
    by_contra! h
    exact hv ⟨R, by rintro _ ⟨i, rfl⟩; exact h i⟩
  let U : ℕ → Set X := fun n => {x | ∃ i, (n : ℝ) < ‖A i x‖}
  have ho (n : ℕ) : IsOpen (U n) := by
    change IsOpen {x | ∃ i, (n : ℝ) < ‖A i x‖}
    simpa only [Set.ofPred_exists] using
      isOpen_iUnion (fun i => isOpen_lt continuous_const (A i).continuous.norm)
  have hd (n : ℕ) : Dense (U n) := by
    apply Metric.dense_iff.mpr
    intro g r hr
    by_cases hg : ∃ i, (n : ℝ) < ‖A i g‖
    · exact ⟨g, Metric.mem_ball_self hr, hg⟩
    have hg' (i : ι) : ‖A i g‖ ≤ n := by
      by_contra! h
      exact hg ⟨i, h⟩
    let t : ℝ := r / (2 * (‖v‖ + 1))
    have ht : 0 < t := div_pos hr (by positivity)
    have htr : t * ‖v‖ < r := by
      dsimp [t]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).mpr
      exact mul_lt_mul_of_pos_left (by linarith [norm_nonneg v]) hr
    obtain ⟨i, hi⟩ := hv' ((2 * (n : ℝ)) / t)
    have hi' : 2 * (n : ℝ) < ‖A i ((t : 𝕜) • v)‖ := by
      rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos ht]
      exact (div_lt_iff₀ ht).mp hi |>.trans_eq (mul_comm _ _)
    refine ⟨g + (t : 𝕜) • v, ?_, i, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        RCLike.norm_ofReal, abs_of_pos ht] using htr
    · have htri : ‖A i ((t : 𝕜) • v)‖ ≤
          ‖A i (g + (t : 𝕜) • v)‖ + ‖A i g‖ := by
        calc
          ‖A i ((t : 𝕜) • v)‖ = ‖A i (g + (t : 𝕜) • v) - A i g‖ := by
            rw [map_add, add_sub_cancel_left]
          _ ≤ _ := norm_sub_le _ _
      linarith [hg' i]
  rw [unbounded_orbit_eq_iInter A]
  exact ⟨dense_iInter_of_isOpen ho hd, IsGδ.iInter_of_isOpen ho⟩

omit [CompleteSpace X] in
/-- Rudin's notation `sup ‖Aᵢx‖ = ∞`, expressed by an ENNReal supremum. -/
theorem unbounded_orbit_iSup_eq_top (A : ι → X →L[𝕜] Y) (x : X)
    (hx : ¬ BddAbove (Set.range fun i => ‖A i x‖)) :
    (⨆ i, (‖A i x‖₊ : ℝ≥0∞)) = ⊤ := by
  by_contra h
  have hb := ENNReal.iSup_coe_lt_top.mp (lt_top_iff_ne_top.mpr h)
  apply hx
  obtain ⟨C, hC⟩ := hb
  refine ⟨(C : ℝ), ?_⟩
  rintro _ ⟨i, rfl⟩
  exact_mod_cast hC (Set.mem_range_self i)

/-- Rudin 5.8: either the operator norms are uniformly bounded, or pointwise unboundedness
holds on a dense Gδ set. -/
theorem theorem_5_8 (A : ι → X →L[𝕜] Y) :
    (∃ M : ℝ, ∀ i, ‖A i‖ ≤ M) ∨
      ∃ E : Set X, Dense E ∧ IsGδ E ∧
        ∀ x ∈ E, (⨆ i, (‖A i x‖₊ : ℝ≥0∞)) = ⊤ := by
  by_cases hA : BddAbove (Set.range fun i => ‖A i‖)
  · obtain ⟨M, hM⟩ := hA
    exact Or.inl ⟨M, fun i => hM (Set.mem_range_self i)⟩
  · obtain ⟨hd, hg⟩ := theorem_5_8_unbounded_residual A hA
    exact Or.inr ⟨_, hd, hg, fun x hx => unbounded_orbit_iSup_eq_top A x hx⟩

end UniformBoundedness

section OpenMapping

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- Rudin 5.9, including the quantitative unit-ball assertion and openness. -/
theorem theorem_5_9 (A : X →L[𝕜] Y) (hA : Function.Surjective A) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ y : Y, ‖y‖ < δ → ∃ x : X, ‖x‖ < 1 ∧ A x = y) ∧
      IsOpenMap A := by
  refine ⟨?_, A.isOpenMap hA⟩
  obtain ⟨C, hC, hpre⟩ := A.exists_preimage_norm_le hA
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro y hy
  obtain ⟨x, hxy, hx⟩ := hpre y
  refine ⟨x, hx.trans_lt ?_, hxy⟩
  calc
    C * ‖y‖ < C * C⁻¹ := mul_lt_mul_of_pos_left hy hC
    _ = 1 := mul_inv_cancel₀ hC.ne'

/-- The bounded inverse supplied by Rudin 5.10. -/
def banachInverseEquiv (A : X →L[𝕜] Y) (hA : Function.Bijective A) : X ≃L[𝕜] Y :=
  (LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquivOfContinuous A.continuous

theorem banachInverseEquiv_apply (A : X →L[𝕜] Y) (hA : Function.Bijective A) (x : X) :
    banachInverseEquiv A hA x = A x := rfl

/-- Rudin 5.10: a positive lower bound and a bounded linear two-sided inverse. -/
theorem theorem_5_10 (A : X →L[𝕜] Y) (hA : Function.Bijective A) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ x : X, δ * ‖x‖ ≤ ‖A x‖) ∧
      ∃ B : Y →L[𝕜] X, (∀ x, B (A x) = x) ∧ (∀ y, A (B y) = y) ∧ ‖B‖ ≤ δ⁻¹ := by
  let e := banachInverseEquiv A hA
  let B := e.symm.toContinuousLinearMap
  let C : ℝ := ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : ‖B‖ ≤ C := by dsimp [C]; linarith
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_, B, ?_, ?_, ?_⟩
  · intro x
    have hx : ‖x‖ ≤ C * ‖A x‖ := by
      calc
        ‖x‖ = ‖B (A x)‖ := by change ‖x‖ = ‖e.symm (e x)‖; rw [e.symm_apply_apply]
        _ ≤ ‖B‖ * ‖A x‖ := B.le_opNorm _
        _ ≤ C * ‖A x‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
    calc
      C⁻¹ * ‖x‖ ≤ C⁻¹ * (C * ‖A x‖) := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hC.le)
      _ = ‖A x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  · exact e.symm_apply_apply
  · exact e.apply_symm_apply
  · simpa only [inv_inv] using hB

end OpenMapping

section HahnBanach

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Rudin 5.16, valid over both ℝ and ℂ and without any closedness assumption on M. -/
theorem theorem_5_16 (M : Submodule 𝕜 X) (f : M →L[𝕜] 𝕜) :
    ∃ F : X →L[𝕜] 𝕜, (∀ x : M, F x = f x) ∧ ‖F‖ = ‖f‖ :=
  exists_extension_norm_eq M f

/-- The domain-specific norm formula emphasized after Rudin 5.16. -/
theorem theorem_5_16_norm_formula (M : Submodule 𝕜 X) (f : M →L[𝕜] 𝕜) :
    ‖f‖ = sSup ((fun x : M => ‖f x‖) '' Metric.closedBall 0 1) :=
  f.sSup_unitClosedBall_eq_norm.symm

/-- The norm-preserving extension established in the proof node 5.18. -/
theorem theorem_5_18 (M : Submodule 𝕜 X) (f : M →L[𝕜] 𝕜) :
    ∃ F : X →L[𝕜] 𝕜, (∀ x : M, F x = f x) ∧ ‖F‖ = ‖f‖ :=
  theorem_5_16 M f

/-- The normalized separation assertion proved in Rudin 5.19. -/
theorem theorem_5_19_separate (M : Submodule 𝕜 X) (x₀ : X)
    (hx : x₀ ∉ closure (M : Set X)) :
    ∃ f : X →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) ∧ f x₀ = 1 := by
  let S := M.topologicalClosure
  let : IsClosed (S : Set X) := M.isClosed_topologicalClosure
  have hq : S.mkQL x₀ ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero S).mp h)
  obtain ⟨g, hg⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hq
  refine ⟨g.comp S.mkQL, ?_, hg⟩
  intro x hxM
  have hxS : x ∈ S := M.le_topologicalClosure hxM
  have hzero : S.mkQL x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hxS
  simp only [ContinuousLinearMap.comp_apply, hzero, map_zero]

/-- Rudin 5.19: closure is detected by all annihilating bounded linear functionals. -/
theorem theorem_5_19 (M : Submodule 𝕜 X) (x₀ : X) :
    x₀ ∈ closure (M : Set X) ↔
      ¬ ∃ f : X →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) ∧ f x₀ ≠ 0 := by
  constructor
  · intro hx ⟨f, hf, hne⟩
    apply hne
    have hm : M ≤ f.ker := fun x hxM => hf x hxM
    exact M.topologicalClosure_minimal hm f.isClosed_ker hx
  · intro h
    by_contra hx
    obtain ⟨f, hf, hfx⟩ := theorem_5_19_separate M x₀ hx
    exact h ⟨f, hf, by rw [hfx]; exact one_ne_zero⟩

/-- Rudin 5.20: a nonzero vector has a norm-one supporting functional. -/
theorem theorem_5_20 (x₀ : X) (hx : x₀ ≠ 0) :
    ∃ f : X →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x₀ = (‖x₀‖ : 𝕜) :=
  exists_dual_vector 𝕜 x₀ (norm_ne_zero_iff.mpr hx)

/-- Rudin 5.21: the continuous dual is Banach even when X is not complete. -/
theorem theorem_5_21_dual_complete : CompleteSpace (X →L[𝕜] 𝕜) := inferInstance

/-- Rudin 5.21: a nontrivial normed space has a nontrivial continuous dual. -/
theorem theorem_5_21_dual_nontrivial [Nontrivial X] : Nontrivial (X →L[𝕜] 𝕜) :=
  inferInstance

/-- Rudin 5.21: bounded linear functionals separate distinct points. -/
theorem theorem_5_21_separates {x y : X} (hxy : x ≠ y) :
    ∃ f : X →L[𝕜] 𝕜, f x ≠ f y :=
  SeparatingDual.exists_separating_of_ne hxy

/-- Rudin 5.21: evaluation on the dual is a bounded linear functional of the stated norm. -/
theorem theorem_5_21_evaluation (x : X) :
    ∃ F : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜, (∀ f, F f = f x) ∧ ‖F‖ = ‖x‖ := by
  refine ⟨NormedSpace.inclusionInDoubleDual 𝕜 X x, fun _ => rfl, ?_⟩
  exact (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)).norm_map x

/-- Rudin 5.21: the norm is the supremum of the values of norm-one functionals.
Mathlib's real supremum assigns zero to the empty set, covering the zero vector space too. -/
theorem theorem_5_21_norm_supremum (x : X) :
    ‖x‖ = sSup ((fun f : X →L[𝕜] 𝕜 => ‖f x‖) '' {f | ‖f‖ = 1}) := by
  calc
    ‖x‖ = ‖NormedSpace.inclusionInDoubleDual 𝕜 X x‖ :=
      ((NormedSpace.inclusionInDoubleDualLi 𝕜 (E := X)).norm_map x).symm
    _ = _ := by
      simpa only [Metric.sphere, dist_zero_right, NormedSpace.dual_def] using
        (NormedSpace.inclusionInDoubleDual 𝕜 X x).sSup_sphere_eq_norm.symm

end HahnBanach

section RealComplexFunctional

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- The real part of a complex-linear functional is real-linear, as stated before 5.17. -/
def realPartFunctional (f : V →ₗ[ℂ] ℂ) : V →ₗ[ℝ] ℝ :=
  RCLike.reLm.comp (f.restrictScalars ℝ)

theorem realPartFunctional_apply (f : V →ₗ[ℂ] ℂ) (x : V) :
    realPartFunctional f x = (f x).re := rfl

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
/-- Rudin 5.17(a), in an arbitrary complex vector space with its compatible real scalar action. -/
theorem theorem_5_17a (f : V →ₗ[ℂ] ℂ) (x : V) :
    f x = ((f x).re : ℂ) - Complex.I * ((f (Complex.I • x)).re : ℂ) := by
  rw [map_smul, smul_eq_mul]
  apply Complex.ext <;> simp

/-- Rudin 5.17(b): every real-linear functional has the prescribed complex-linear extension. -/
theorem theorem_5_17b (u : V →ₗ[ℝ] ℝ) :
    ∃ f : V →ₗ[ℂ] ℂ, ∀ x,
      f x = (u x : ℂ) - Complex.I * (u (Complex.I • x) : ℂ) :=
  ⟨Module.Dual.extendRCLike u, fun _ => rfl⟩

end RealComplexFunctional

section RealComplexNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]

/-- Rudin 5.17(c), preserving the norm when the real functional is made complex-linear. -/
theorem theorem_5_17c (u : X →L[ℝ] ℝ) (f : X →L[ℂ] ℂ)
    (h : ∀ x, f x = (u x : ℂ) - Complex.I * (u (Complex.I • x) : ℂ)) : ‖f‖ = ‖u‖ := by
  have heq : f = StrongDual.extendRCLike u := ContinuousLinearMap.ext h
  rw [heq]
  exact StrongDual.norm_extendRCLike u

/-- The full 5.17(c) statement for algebraic functionals, including infinite norms.
No continuity or boundedness is assumed for either functional. -/
theorem theorem_5_17c_extended (u : X →ₗ[ℝ] ℝ) (f : X →ₗ[ℂ] ℂ)
    (h : ∀ x, f x = (u x : ℂ) - Complex.I * (u (Complex.I • x) : ℂ)) :
    extendedOperatorNorm f = extendedOperatorNorm u := by
  have heq : f = Module.Dual.extendRCLike u := LinearMap.ext h
  have hre (x : X) : u x = (f x).re := by
    rw [heq]
    exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) u x).symm
  unfold extendedOperatorNorm
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hz : f x = 0
    · simp [hz]
    have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let y : X := (‖f x‖⁻¹ : ℝ) • (conj (f x) • (x : X))
    have hy : ‖y‖ ≤ 1 := by
      dsimp [y]
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        Complex.norm_conj, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
      exact x.property
    have huy : u y = ‖f x‖ := by
      dsimp [y]
      rw [map_smul, smul_eq_mul]
      have hs : u (conj (f x) • (x : X)) = ‖f x‖ ^ 2 := by
        rw [heq]
        exact (Module.Dual.norm_extendRCLike_apply_sq (𝕜 := ℂ) u (x : X)).symm
      rw [hs, pow_two, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    have hnorm : ‖u y‖₊ = ‖f x‖₊ := by
      apply NNReal.eq
      simp only [coe_nnnorm, huy, Real.norm_of_nonneg (norm_nonneg _)]
    rw [← hnorm]
    exact le_iSup (fun z : {z : X // ‖z‖ ≤ 1} => (‖u z‖₊ : ℝ≥0∞)) ⟨y, hy⟩
  · apply iSup_le
    intro x
    apply le_trans _ (le_iSup (fun z : {z : X // ‖z‖ ≤ 1} => (‖f z‖₊ : ℝ≥0∞)) x)
    exact_mod_cast (show ‖u x‖ ≤ ‖f x‖ by
      rw [hre, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _)

end RealComplexNorm

end RudinRCA.Chapter05

























end
end
/- END Chapter05Banach.lean -/

/- BEGIN Chapter05Perfect.lean -/
section




/-! The nonempty perfect-set conclusion appended to Rudin 5.13.
The construction works in every nonempty complete metric space without isolated
points; separability and local compactness are not assumed. -/

noncomputable section

open Set Filter Metric Function CantorScheme
open scoped Topology ENNReal

namespace RudinRCA.Chapter05

section Splitting

variable {X : Type*} [MetricSpace X]

/-- A small open neighborhood whose closure remains in a prescribed open set. -/
theorem small_open_closure {V : Set X} (hV : IsOpen V) {x : X} (hx : x ∈ V)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set X, IsOpen W ∧ W.Nonempty ∧ closure W ⊆ V ∧ ediam W ≤ ε := by
  have he : x ∈ eball x (ε / 2) := by
    apply mem_eball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨hε.ne', by simp⟩
  obtain ⟨W, ⟨hxW, hoW⟩, hW⟩ :=
    (hasBasis_opens_closure x).mem_iff.mp
      ((hV.inter isOpen_eball).mem_nhds ⟨hx, he⟩)
  refine ⟨W, hoW, ⟨x, hxW⟩, hW.trans inter_subset_left, ?_⟩
  calc
    ediam W ≤ ediam (eball x (ε / 2)) :=
      ediam_mono (subset_closure.trans (hW.trans inter_subset_right))
    _ ≤ ε := by
      convert ediam_eball_le (x := x) (r := ε / 2) using 1
      rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num

/-- Two disjoint small open children, with their closures inside the parent. -/
theorem open_small_diam_splitting [PerfectSpace X] {V : Set X}
    (hV : IsOpen V) (hne : V.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W₀ W₁ : Set X,
      (IsOpen W₀ ∧ W₀.Nonempty ∧ closure W₀ ⊆ V ∧ ediam W₀ ≤ ε) ∧
      (IsOpen W₁ ∧ W₁.Nonempty ∧ closure W₁ ⊆ V ∧ ediam W₁ ≤ ε) ∧
      Disjoint W₀ W₁ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp hV.preperfect x hx V
    (hV.mem_nhds hx)
  obtain ⟨U₀, U₁, ho₀, ho₁, hx₀, hy₁, hd⟩ := t2_separation hyx.symm
  obtain ⟨W₀, hW₀, hn₀, hs₀, he₀⟩ :=
    small_open_closure (hV.inter ho₀) ⟨hx, hx₀⟩ hε
  obtain ⟨W₁, hW₁, hn₁, hs₁, he₁⟩ :=
    small_open_closure (hV.inter ho₁) ⟨hy.1, hy₁⟩ hε
  exact ⟨W₀, W₁, ⟨hW₀, hn₀, hs₀.trans inter_subset_left, he₀⟩,
    ⟨hW₁, hn₁, hs₁.trans inter_subset_left, he₁⟩,
    hd.mono (subset_closure.trans (hs₀.trans inter_subset_right))
      (subset_closure.trans (hs₁.trans inter_subset_right))⟩

end Splitting

/-- Cantor space has no isolated points: change one unused coordinate of a cylinder. -/
theorem cantor_preperfect : Preperfect (univ : Set (ℕ → Bool)) := by
  apply preperfect_iff_nhds.mpr
  intro x hx U hU
  obtain ⟨V, hVU, hoV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, ⟨z, n, rfl⟩, hxW, hWV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open hxV hoV
  have hcx : PiNat.cylinder x n = PiNat.cylinder z n :=
    PiNat.mem_cylinder_iff_eq.mp hxW
  let y := Function.update x n (!(x n))
  have hy : y ∈ PiNat.cylinder z n := by
    rw [← hcx]
    exact PiNat.update_mem_cylinder x n (!(x n))
  refine ⟨y, ⟨hVU (hWV hy), mem_univ _⟩, ?_⟩
  intro h
  have he := congrFun h n
  simp only [y, Function.update_self] at he
  cases hxn : x n <;> simp [hxn] at he

section PerfectSubset

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
  [Nonempty X] [PerfectSpace X]

/-- A continuous injection of Cantor space into any countable intersection of
dense open sets. The open-node invariant is essential in a nonseparable space. -/
theorem dense_open_intersection_cantor_injection (U : ℕ → Set X)
    (ho : ∀ n, IsOpen (U n)) (hd : ∀ n, Dense (U n)) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ ⋂ n, U n ∧ Continuous f ∧ Injective f := by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let P := {E : Set X // IsOpen E ∧ E.Nonempty}
  choose C₀ C₁ h₀ h₁ hdisj using
    fun {C : Set X} (hC : IsOpen C) (hne : C.Nonempty) (n : ℕ)
      {ε : ℝ≥0∞} (hε : 0 < ε) =>
      open_small_diam_splitting (hC.inter (ho n))
        ((hd n).inter_open_nonempty C hC hne) hε
  let DP : List Bool → P := fun l => by
    induction l with
    | nil => exact ⟨univ, isOpen_univ, Set.univ_nonempty⟩
    | cons a l ih =>
      cases a
      · exact ⟨C₀ ih.property.1 ih.property.2 l.length (upos (l.length + 1)),
          (h₀ _ _ _ _).1, (h₀ _ _ _ _).2.1⟩
      · exact ⟨C₁ ih.property.1 ih.property.2 l.length (upos (l.length + 1)),
          (h₁ _ _ _ _).1, (h₁ _ _ _ _).2.1⟩
  let D : List Bool → Set X := fun l => (DP l).val
  have hanti : ClosureAntitone D := by
    intro l a
    cases a
    · exact ((h₀ _ _ _ _).2.2.1).trans inter_subset_left
    · exact ((h₁ _ _ _ _).2.2.1).trans inter_subset_left
  have hlayer (l : List Bool) (a : Bool) : D (a :: l) ⊆ U l.length := by
    cases a
    · exact subset_closure.trans (((h₀ _ _ _ _).2.2.1).trans inter_subset_right)
    · exact subset_closure.trans (((h₁ _ _ _ _).2.2.1).trans inter_subset_right)
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m (hm : 1 ≤ m) => ?_⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    dsimp
    cases x n
    · convert (h₀ _ _ _ _).2.2.2 using 1 <;> rw [PiNat.res_length]
    · convert (h₁ _ _ _ _).2.2.2 using 1 <;> rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _ _
    · exact (hdisj _ _ _ _).symm
  have hdom : ∀ {x : ℕ → Bool}, x ∈ (inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam fun l => (DP l).property.2]
    exact mem_univ _
  refine ⟨fun x => (inducedMap D).2 ⟨x, hdom⟩, ?_, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    rw [mem_iInter]
    intro n
    have hm := map_mem (A := D) ⟨x, hdom⟩ (n + 1)
    rw [PiNat.res_succ] at hm
    simpa only [PiNat.res_length] using hlayer (PiNat.res x n) (x n) hm
  · exact hdiam.map_continuous.comp (by fun_prop)
  · intro x y hxy
    simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy

/-- 5.13, final assertion: a dense Gδ contains a nonempty perfect set. -/
theorem dense_gdelta_contains_nonempty_perfect (E : Set X) (hE : IsGδ E)
    (hd : Dense E) : ∃ P : Set X, P.Nonempty ∧ Perfect P ∧ P ⊆ E := by
  obtain ⟨U, ho, hEU⟩ := hE.eq_iInter_nat
  have hdU (n : ℕ) : Dense (U n) := hd.mono (by
    rw [hEU]
    exact iInter_subset U n)
  obtain ⟨f, hfU, hf, hinj⟩ := dense_open_intersection_cantor_injection U ho hdU
  refine ⟨range f, ⟨f (fun _ => false), mem_range_self _⟩, ?_, ?_⟩
  · refine ⟨(isCompact_range hf).isClosed, ?_⟩
    rintro y ⟨x, rfl⟩
    have h := (cantor_preperfect x (mem_univ _)).map hf.continuousAt hinj
    simpa only [Filter.map_principal, image_univ] using h
  · simpa only [← hEU] using hfU

end PerfectSubset

end RudinRCA.Chapter05
end
end
/- END Chapter05Perfect.lean -/

/- BEGIN Chapter05Fourier.lean -/
section
















/-! Rudin RCA 5.11–5.12 and 5.14–5.15: ordinary Fourier sums and the L¹ transform. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Real ComplexConjugate Topology ZeroAtInfty
open RudinRCA.Chapter04

namespace RudinRCA.Chapter05

abbrev CircleL1 := CircleLp 1

/-- The Dirichlet kernel is the actual symmetric exponential polynomial. -/
def dirichletKernel (N : ℕ) : C(FourierCircle, ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), trigMonomial n

theorem dirichletKernel_apply (N : ℕ) (t : FourierCircle) :
    dirichletKernel N t = fejerDirichlet N t := by
  simp only [dirichletKernel, fejerDirichlet, ContinuousMap.sum_apply, trigMonomial]

/-- Every L¹ representative is integrable against normalized Haar measure. -/
theorem circleL1_integrable (f : CircleL1) : Integrable f circleMeasure :=
  memLp_one_iff_integrable.mp (Lp.memLp f)

/-- 5.11(1): convolution gives the ordinary partial sums for every integrable function. -/
theorem circleFourierPartialSum_convolution (f : FourierCircle → ℂ)
    (hf : Integrable f circleMeasure) (N : ℕ) (x : FourierCircle) :
    circleFourierPartialSum f N x =
      ∫ t, dirichletKernel N t * f (x - t) ∂circleMeasure := by
  have hmono (n : ℤ) :
      (∫ t, fourier n t * f (x - t) ∂circleMeasure) =
        fourierCoeff f n * fourier n x := by
    have h := integral_sub_left_eq_self
      (fun t : FourierCircle => fourier n t * f (x - t)) circleMeasure x
    simp only [sub_sub_cancel] at h
    rw [← h]
    simp_rw [fejerFourier_argument_sub, mul_assoc]
    rw [integral_const_mul]
    simp only [fourierCoeff, smul_eq_mul, mul_comm]
  simp_rw [dirichletKernel, ContinuousMap.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum]
  · simp only [hmono, circleFourierPartialSum, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul, circleFourierCoeff, trigMonomial]
  · intro n hn
    simpa only [smul_eq_mul] using (hf.comp_sub_left x).fourier_smul n

/-- The normalized real-variable convolution formula printed in 5.11(1). -/
theorem circleFourierPartialSum_interval (f : FourierCircle → ℂ)
    (hf : Integrable f circleMeasure) (N : ℕ) (x : ℝ) :
    circleFourierPartialSum f N (x : FourierCircle) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t in -Real.pi..Real.pi,
        dirichletKernel N (t : FourierCircle) * f ((x - t : ℝ) : FourierCircle) := by
  rw [circleFourierPartialSum_convolution f hf, circleIntegral_interval]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat, AddCircle.coe_sub]

/-- 5.11: a subsequence of the actual Fourier polynomials converges almost everywhere. -/
theorem fourierPartialSum_subsequence_ae (f : CircleL2) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂circleMeasure,
        Tendsto (fun k => circleFourierPartialSum f (ns k) x) atTop (𝓝 (f x)) := by
  have hm := tendstoInMeasure_of_tendsto_Lp (fourierPartialSum_tendsto f)
  exact (hm.congr_left (fun N => fourierPartialSum_ae f N)).exists_seq_tendsto_ae

theorem continuousFourierPartialSum_subsequence_ae (f : C(FourierCircle, ℂ)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂circleMeasure,
        Tendsto (fun k => circleFourierPartialSum f (ns k) x) atTop (𝓝 (f x)) := by
  let F : CircleL2 := ContinuousMap.toLp 2 circleMeasure ℂ f
  have hF : F =ᵐ[circleMeasure] f := ContinuousMap.coeFn_toLp circleMeasure f
  have hp (N : ℕ) : circleFourierPartialSum F N = circleFourierPartialSum f N := by
    simp only [circleFourierPartialSum, circleFourierCoeff, fourierCoeff_congr_ae hF]
  obtain ⟨ns, hns, hlim⟩ := fourierPartialSum_subsequence_ae F
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, hF] with x hx hFx
  simpa only [hp, hFx] using hx

/-- Fourier coefficient functionals have norm at most one on L¹. -/
theorem norm_fourierCoeff_le_L1 (f : CircleL1) (n : ℤ) :
    ‖circleFourierCoeff f n‖ ≤ ‖f‖ := by
  calc
    ‖circleFourierCoeff f n‖ ≤ ∫ t, ‖fourier (-n) t * f t‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ t, ‖f t‖ ∂circleMeasure := by
      congr 1
      ext t
      simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

def fourierCoeffL1Linear (n : ℤ) : CircleL1 →ₗ[ℂ] ℂ where
  toFun f := circleFourierCoeff f n
  map_add' f g := by
    change fourierCoeff (⇑(f + g)) n = fourierCoeff f n + fourierCoeff g n
    rw [fourierCoeff_congr_ae (Lp.coeFn_add f g)]
    exact congrFun (fourierCoeff.add (circleL1_integrable f) (circleL1_integrable g)) n
  map_smul' c f := by
    change fourierCoeff (⇑(c • f)) n = c * fourierCoeff f n
    rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f)]
    exact fourierCoeff.const_smul f c n

/-- The coefficient at a fixed integer is a bounded complex linear functional on L¹. -/
def fourierCoeffL1 (n : ℤ) : CircleL1 →L[ℂ] ℂ :=
  (fourierCoeffL1Linear n).mkContinuous 1 fun f => by
    change ‖circleFourierCoeff f n‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_fourierCoeff_le_L1 f n

@[simp] theorem fourierCoeffL1_apply (n : ℤ) (f : CircleL1) :
    fourierCoeffL1 n f = circleFourierCoeff f n := rfl

theorem fourierCoeffL1_norm_le (n : ℤ) : ‖fourierCoeffL1 n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_fourierCoeff_le_L1 f n

@[simp] theorem fourierCoeffL1_toLp (n : ℤ) (f : C(FourierCircle, ℂ)) :
    fourierCoeffL1 n (ContinuousMap.toLp 1 circleMeasure ℂ f) = circleFourierCoeff f n := by
  exact congrFun (fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp circleMeasure f)) n

/-- 5.11(5): evaluation of the Nth partial sum is a bounded linear functional. -/
def fourierPartialSumFunctional (N : ℕ) (x : FourierCircle) : C(FourierCircle, ℂ) →L[ℂ] ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    trigMonomial n x • (fourierCoeffL1 n).comp (ContinuousMap.toLp 1 circleMeasure ℂ)

@[simp] theorem fourierPartialSumFunctional_apply (N : ℕ) (x : FourierCircle)
    (f : C(FourierCircle, ℂ)) :
    fourierPartialSumFunctional N x f = circleFourierPartialSum f N x := by
  simp only [fourierPartialSumFunctional, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fourierCoeffL1_toLp, circleFourierPartialSum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, mul_comm]

/-- The L¹ mass of the Dirichlet kernel, with Rudin's normalization. -/
def lebesgueConstant (N : ℕ) : ℝ := ∫ t, ‖dirichletKernel N t‖ ∂circleMeasure

theorem lebesgueConstant_nonneg (N : ℕ) : 0 ≤ lebesgueConstant N :=
  integral_nonneg fun _ => norm_nonneg _

theorem fourierPartialSumFunctional_norm_le (N : ℕ) (x : FourierCircle) :
    ‖fourierPartialSumFunctional N x‖ ≤ lebesgueConstant N := by
  apply ContinuousLinearMap.opNorm_le_bound _ (lebesgueConstant_nonneg N)
  intro f
  rw [fourierPartialSumFunctional_apply,
    circleFourierPartialSum_convolution f (fejer_integrable_of_continuous f.continuous)]
  calc
    ‖∫ t, dirichletKernel N t * f (x - t) ∂circleMeasure‖ ≤
        ∫ t, ‖dirichletKernel N t * f (x - t)‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖dirichletKernel N t‖ * ‖f‖ ∂circleMeasure := by
      apply integral_mono
      · exact (fejer_integrable_of_continuous
          ((dirichletKernel N).continuous.mul
            (f.continuous.comp (continuous_const.sub continuous_id)))).norm
      · exact (fejer_integrable_of_continuous (dirichletKernel N).continuous.norm).mul_const _
      · intro t
        change ‖dirichletKernel N t * f (x - t)‖ ≤ ‖dirichletKernel N t‖ * ‖f‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
    _ = lebesgueConstant N * ‖f‖ := integral_mul_const _ _

/-- The maximal ordinary partial sum, allowing the value infinity as in 5.11(4). -/
def fourierMaximal (f : FourierCircle → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖circleFourierPartialSum f N (x : FourierCircle)‖ₑ

/-- 5.11: the maximal partial-sum function is lower semicontinuous. -/
theorem fourierMaximal_lowerSemicontinuous (f : FourierCircle → ℂ) :
    LowerSemicontinuous (fourierMaximal f) := by
  apply lowerSemicontinuous_iSup
  intro N
  exact ((continuous_circleFunction (circleFourierPartialSum f N)).enorm).lowerSemicontinuous

/-- Shifting a symmetric frequency interval produces precisely the positive frequencies. -/
theorem dirichletKernel_shift (N : ℕ) (x : FourierCircle) :
    dirichletKernel N x * trigMonomial ((N : ℤ) + 1) x =
      ∑ k ∈ Finset.range (2 * N + 1), trigMonomial ((k : ℤ) + 1) x := by
  simp only [dirichletKernel, ContinuousMap.sum_apply, Finset.sum_mul, trigMonomial,
    ← fourier_add]
  symm
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ) - N)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n + N).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rw [show (k : ℤ) - (N : ℤ) + ((N : ℤ) + 1) = (k : ℤ) + 1 by ring]

def positiveSineSum (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 * N + 1), Real.sin (((k : ℝ) + 1) * t)

theorem dirichletKernel_shift_im (N : ℕ) (t : ℝ) :
    (dirichletKernel N (t : FourierCircle) *
      trigMonomial ((N : ℤ) + 1) (t : FourierCircle)).im = positiveSineSum N t := by
  rw [dirichletKernel_shift]
  simp only [Complex.im_sum, positiveSineSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [trigMonomial_apply_real]
  simp [Complex.exp_im]

theorem positiveSineSum_le_dirichlet_norm (N : ℕ) (t : ℝ) :
    positiveSineSum N t ≤ ‖dirichletKernel N (t : FourierCircle)‖ := by
  rw [← dirichletKernel_shift_im]
  calc
    _ ≤ ‖dirichletKernel N (t : FourierCircle) *
        trigMonomial ((N : ℤ) + 1) (t : FourierCircle)‖ := Complex.im_le_norm _
    _ = _ := by simp only [norm_mul, trigMonomial, fourier_apply, Circle.norm_coe, mul_one]

theorem integral_positive_sine (k : ℕ) :
    (∫ t in 0..Real.pi, Real.sin (((k : ℝ) + 1) * t)) =
      (1 - (-1 : ℝ) ^ (k + 1)) / ((k : ℝ) + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hk, integral_sin]
  simp only [mul_zero, Real.cos_zero, smul_eq_mul]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.cos_nat_mul_pi]
  ring

theorem integral_positiveSineSum (N : ℕ) :
    (∫ t in 0..Real.pi, positiveSineSum N t) =
      ∑ k ∈ Finset.range (N + 1), 2 / (2 * (k : ℝ) + 1) := by
  unfold positiveSineSum
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_positive_sine]
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ (fun k : ℕ => 2 / (2 * (k : ℝ) + 1)) (N + 1)]
      rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [pow_add, pow_mul]
      norm_num
      push_cast
      ring
  · intro k hk
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- A harmonic lower bound, obtained by integrating the shifted kernel on half a period. -/
theorem lebesgueConstant_harmonic_lower (N : ℕ) :
    (1 / (2 * Real.pi)) * (∑ k ∈ Finset.range (N + 1), (1 / ((k : ℝ) + 1))) ≤
      lebesgueConstant N := by
  have hc : Continuous (fun t : ℝ => ‖dirichletKernel N (t : FourierCircle)‖) :=
    (continuous_circleFunction (dirichletKernel N)).norm
  have hs : Continuous (positiveSineSum N) := by unfold positiveSineSum; fun_prop
  have hh : (∑ k ∈ Finset.range (N + 1), (1 / ((k : ℝ) + 1))) ≤
      ∫ t in 0..Real.pi, positiveSineSum N t := by
    rw [integral_positiveSineSum]
    apply Finset.sum_le_sum
    intro k hk
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hm : (∫ t in 0..Real.pi, positiveSineSum N t) ≤
      ∫ t in -Real.pi..Real.pi, ‖dirichletKernel N (t : FourierCircle)‖ := by
    calc
      _ ≤ ∫ t in 0..Real.pi, ‖dirichletKernel N (t : FourierCircle)‖ :=
        intervalIntegral.integral_mono_on Real.pi_pos.le (hs.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _) (fun t ht => positiveSineSum_le_dirichlet_norm N t)
      _ ≤ _ := intervalIntegral.integral_mono_interval (by linarith [Real.pi_pos])
        Real.pi_pos.le le_rfl (ae_of_all _ fun t => norm_nonneg _) (hc.intervalIntegrable _ _)
  rw [lebesgueConstant, circleIntegral_interval]
  exact mul_le_mul_of_nonneg_left (hh.trans hm) (by positivity)

/-- 5.11(8): the normalized L¹ norms of the Dirichlet kernels tend to infinity. -/
theorem lebesgueConstant_tendsto : Tendsto lebesgueConstant atTop atTop := by
  have hh := Real.tendsto_sum_range_one_div_nat_succ_atTop.comp (tendsto_add_atTop_nat 1)
  have hm := hh.const_mul_atTop (by positivity : 0 < 1 / (2 * Real.pi))
  exact tendsto_atTop_mono lebesgueConstant_harmonic_lower hm

theorem regularized_norm_pos (a δ : ℝ) (hδ : 0 < δ) :
    0 < Real.sqrt (a ^ 2 + δ ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg a, sq_pos_of_pos hδ]

theorem regularized_norm_ge (a δ : ℝ) (ha : 0 ≤ a) :
    a ≤ Real.sqrt (a ^ 2 + δ ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ a ^ 2 + δ ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (a ^ 2 + δ ^ 2)
  nlinarith [sq_nonneg δ]

/-- A quantitative form of the smooth-sign approximation, including zeros of the kernel. -/
theorem regularized_sign_error (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) :
    a - δ ≤ a ^ 2 / Real.sqrt (a ^ 2 + δ ^ 2) := by
  let s := Real.sqrt (a ^ 2 + δ ^ 2)
  have hs : 0 < s := regularized_norm_pos a δ hδ
  have has : a ≤ s := regularized_norm_ge a δ ha
  have hsa : s ≤ a + δ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith
  have hd : a - a ^ 2 / s = (a / s) * (s - a) := by field_simp [hs.ne']
  have hratio : a / s ≤ 1 := (div_le_one hs).2 has
  have hprod := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr has)
  rw [← hd] at hprod
  nlinarith

/-- Continuous approximate phases attaining the norm of Dirichlet convolution. -/
def dirichletNormTest (N : ℕ) (x : FourierCircle) (δ : ℝ) (hδ : 0 < δ) :
    C(FourierCircle, ℂ) where
  toFun y := conj (dirichletKernel N (x - y)) /
    (Real.sqrt (‖dirichletKernel N (x - y)‖ ^ 2 + δ ^ 2) : ℂ)
  continuous_toFun := by
    have hc : Continuous (fun y => dirichletKernel N (x - y)) :=
      (dirichletKernel N).continuous.comp (continuous_const.sub continuous_id)
    apply hc.star.div
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((hc.norm.pow 2).add continuous_const)))
    intro y
    change (Real.sqrt (‖dirichletKernel N (x - y)‖ ^ 2 + δ ^ 2) : ℂ) ≠ 0
    exact_mod_cast (regularized_norm_pos ‖dirichletKernel N (x - y)‖ δ hδ).ne'

theorem dirichletNormTest_norm_le (N : ℕ) (x : FourierCircle) (δ : ℝ) (hδ : 0 < δ) :
    ‖dirichletNormTest N x δ hδ‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro y
  change ‖conj (dirichletKernel N (x - y)) /
    (Real.sqrt (‖dirichletKernel N (x - y)‖ ^ 2 + δ ^ 2) : ℂ)‖ ≤ 1
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (regularized_norm_pos _ δ hδ)]
  exact (div_le_one (regularized_norm_pos _ δ hδ)).2
    (regularized_norm_ge _ δ (norm_nonneg _))

theorem fourierPartialSumFunctional_normTest (N : ℕ) (x : FourierCircle)
    (δ : ℝ) (hδ : 0 < δ) :
    fourierPartialSumFunctional N x (dirichletNormTest N x δ hδ) =
      ((∫ t, ‖dirichletKernel N t‖ ^ 2 /
        Real.sqrt (‖dirichletKernel N t‖ ^ 2 + δ ^ 2) ∂circleMeasure) : ℂ) := by
  rw [fourierPartialSumFunctional_apply,
    circleFourierPartialSum_convolution _
      (fejer_integrable_of_continuous (dirichletNormTest N x δ hδ).continuous)]
  simp only [dirichletNormTest, ContinuousMap.coe_mk, sub_sub_cancel,
    ← mul_div_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div]

/-- Equality in 5.11(6), at every point, rather than only at the origin. -/
theorem fourierPartialSumFunctional_norm (N : ℕ) (x : FourierCircle) :
    ‖fourierPartialSumFunctional N x‖ = lebesgueConstant N := by
  apply le_antisymm (fourierPartialSumFunctional_norm_le N x)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let f := dirichletNormTest N x δ hδ
  let g : FourierCircle → ℝ := fun t => ‖dirichletKernel N t‖ ^ 2 /
    Real.sqrt (‖dirichletKernel N t‖ ^ 2 + δ ^ 2)
  have hg : Continuous g := by
    apply ((dirichletKernel N).continuous.norm.pow 2).div
      (Real.continuous_sqrt.comp (((dirichletKernel N).continuous.norm.pow 2).add
        continuous_const))
    intro t
    exact (regularized_norm_pos _ δ hδ).ne'
  have hnorm := fejer_integrable_of_continuous (dirichletKernel N).continuous.norm
  have hi := integral_mono
    (hnorm.sub (integrable_const δ)) (fejer_integrable_of_continuous hg)
    (fun t => regularized_sign_error ‖dirichletKernel N t‖ δ (norm_nonneg _) hδ)
  have hi' : lebesgueConstant N - δ ≤ ∫ t, g t ∂circleMeasure := by
    change (∫ t, ‖dirichletKernel N t‖ - δ ∂circleMeasure) ≤
      ∫ t, g t ∂circleMeasure at hi
    rw [integral_sub hnorm (integrable_const δ)] at hi
    simpa [g, lebesgueConstant, Measure.real] using hi
  have hb : (∫ t, g t ∂circleMeasure) ≤ ‖fourierPartialSumFunctional N x‖ := by
    calc
      _ = (fourierPartialSumFunctional N x f).re := by
        simpa only [f, g, ← Complex.ofReal_pow, ← Complex.ofReal_div,
          integral_complex_ofReal, Complex.ofReal_re] using
          (congrArg Complex.re (fourierPartialSumFunctional_normTest N x δ hδ)).symm
      _ ≤ ‖fourierPartialSumFunctional N x f‖ := Complex.re_le_norm _
      _ ≤ ‖fourierPartialSumFunctional N x‖ * ‖f‖ :=
        (fourierPartialSumFunctional N x).le_opNorm f
      _ ≤ ‖fourierPartialSumFunctional N x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (dirichletNormTest_norm_le N x δ hδ)
  linarith

/-- 5.11(7): partial-sum evaluation functionals have norms tending to infinity. -/
theorem fourierPartialSumFunctional_norm_tendsto (x : FourierCircle) :
    Tendsto (fun N => ‖fourierPartialSumFunctional N x‖) atTop atTop := by
  simpa only [fourierPartialSumFunctional_norm] using lebesgueConstant_tendsto

/-- The equality `s*(f;x)=∞` means that the actual partial-sum norms are unbounded. -/
theorem fourierMaximal_eq_top_iff (f : FourierCircle → ℂ) (x : ℝ) :
    fourierMaximal f x = ∞ ↔
      ¬ BddAbove (Set.range fun N => ‖circleFourierPartialSum f N (x : FourierCircle)‖) := by
  change (⨆ N : ℕ, (‖circleFourierPartialSum f N (x : FourierCircle)‖₊ : ℝ≥0∞)) = ⊤ ↔ _
  simpa only [← NNReal.bddAbove_coe, ← Set.range_comp, Function.comp_def, coe_nnnorm] using
    (ENNReal.iSup_coe_eq_top (f := fun N : ℕ =>
      ‖circleFourierPartialSum f N (x : FourierCircle)‖₊))

def fourierDivergenceFunctions (x : ℝ) : Set C(FourierCircle, ℂ) :=
  {f | ¬ BddAbove (Set.range fun N => ‖circleFourierPartialSum f N (x : FourierCircle)‖)}

/-- 5.11: at each prescribed point, unbounded Fourier sums occur on a dense Gδ. -/
theorem fourierDivergenceFunctions_dense_Gδ (x : ℝ) :
    Dense (fourierDivergenceFunctions x) ∧ IsGδ (fourierDivergenceFunctions x) := by
  have hA := not_bddAbove_of_tendsto_atTop
    (fourierPartialSumFunctional_norm_tendsto (x : FourierCircle))
  simpa only [fourierDivergenceFunctions, fourierPartialSumFunctional_apply] using
    theorem_5_8_unbounded_residual (fun N => fourierPartialSumFunctional N (x : FourierCircle)) hA

/-- Unbounded partial sums cannot converge to any complex number. -/
theorem fourierDivergenceFunctions_not_tendsto (x : ℝ) (f : C(FourierCircle, ℂ))
    (hf : f ∈ fourierDivergenceFunctions x) (z : ℂ) :
    ¬ Tendsto (fun N => circleFourierPartialSum f N (x : FourierCircle)) atTop (𝓝 z) := by
  intro h
  exact hf h.norm.bddAbove_range

/-- The same residual statement holds simultaneously at any countable family of points. -/
theorem fourierDivergence_countable {ι : Type*} [Countable ι] (x : ι → ℝ) :
    Dense (⋂ i, fourierDivergenceFunctions (x i)) ∧
      IsGδ (⋂ i, fourierDivergenceFunctions (x i)) := by
  constructor
  · exact dense_iInter_of_Gδ (fun i => (fourierDivergenceFunctions_dense_Gδ (x i)).2)
      (fun i => (fourierDivergenceFunctions_dense_Gδ (x i)).1)
  · exact IsGδ.iInter (fun i => (fourierDivergenceFunctions_dense_Gδ (x i)).2)

/-- The full set of real points of divergence, with all periodic translates included. -/
def fourierDivergencePoints (f : FourierCircle → ℂ) : Set ℝ :=
  {x | ¬ BddAbove (Set.range fun N => ‖circleFourierPartialSum f N (x : FourierCircle)‖)}

theorem fourierDivergencePoints_eq_iInter (f : FourierCircle → ℂ) :
    fourierDivergencePoints f = ⋂ m : ℕ, ⋃ N : ℕ,
      {x : ℝ | (m : ℝ) < ‖circleFourierPartialSum f N (x : FourierCircle)‖} := by
  ext x
  simp only [fourierDivergencePoints, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro h m
    obtain ⟨v, ⟨N, rfl⟩, hv⟩ := not_bddAbove_iff.mp h (m : ℝ)
    exact ⟨N, hv⟩
  · intro h hb
    obtain ⟨C, hC⟩ := hb
    obtain ⟨m, hm⟩ := exists_nat_gt C
    obtain ⟨N, hN⟩ := h m
    have hbN := hC (Set.mem_range_self N)
    linarith

/-- The divergence set is Gδ for every f, including functions outside the residual family. -/
theorem fourierDivergencePoints_isGδ (f : FourierCircle → ℂ) :
    IsGδ (fourierDivergencePoints f) := by
  rw [fourierDivergencePoints_eq_iInter]
  apply IsGδ.iInter_of_isOpen
  intro m
  apply isOpen_iUnion
  intro N
  exact isOpen_lt continuous_const (continuous_circleFunction (circleFourierPartialSum f N)).norm

/-- 5.12: a residual set of functions has a residual set of real divergence points. -/
theorem theorem_5_12 :
    ∃ E : Set C(FourierCircle, ℂ), Dense E ∧ IsGδ E ∧
      ∀ f ∈ E, Dense (fourierDivergencePoints f) ∧ IsGδ (fourierDivergencePoints f) := by
  let E : Set C(FourierCircle, ℂ) := ⋂ q : ℚ, fourierDivergenceFunctions (q : ℝ)
  have hE := fourierDivergence_countable (fun q : ℚ => (q : ℝ))
  refine ⟨E, hE.1, hE.2, ?_⟩
  intro f hf
  refine ⟨?_, fourierDivergencePoints_isGδ f⟩
  apply (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).mono
  rintro x ⟨q, rfl⟩
  exact Set.mem_iInter.mp hf q

@[simp] theorem fourierCoeffL1_monomial (n m : ℤ) :
    fourierCoeffL1 n (fourierLp 1 m) = if n = m then 1 else 0 := by
  rw [fourierCoeffL1_apply]
  change fourierCoeff (fourierLp 1 m) n = _
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 m), fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

/-- 5.14: the Riemann–Lebesgue lemma for every L¹ function, along both ends of Z. -/
theorem fourierCoeff_tendsto_cofinite (f : CircleL1) :
    Tendsto (circleFourierCoeff f) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hf : f ∈ (Submodule.span ℂ (Set.range (@fourierLp (2 * Real.pi) _ 1 _))).topologicalClosure := by
    rw [trigonometricSystem_dense_Lp 1 (by simp)]
    trivial
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  have hpzero (n : ℤ) (hn : n ∉ c.support) : fourierCoeffL1 n p = 0 := by
    rw [← hc]
    simp only [Finsupp.sum, map_sum, map_smul, fourierCoeffL1_monomial]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by intro h; subst j; exact hn hj)]
    simp
  filter_upwards [c.support.finite_toSet.compl_mem_cofinite] with n hn
  have hb := norm_fourierCoeff_le_L1 (f - p) n
  rw [← fourierCoeffL1_apply, map_sub, hpzero n hn, sub_zero] at hb
  have hd : ‖f - p‖ < ε := by simpa [dist_eq_norm, norm_sub_rev] using hdist
  simpa only [dist_zero_right, fourierCoeffL1_apply] using hb.trans_lt hd

theorem fourierCoeff_tendsto_both_ends (f : CircleL1) :
    Tendsto (circleFourierCoeff f) atBot (𝓝 0) ∧
      Tendsto (circleFourierCoeff f) atTop (𝓝 0) := by
  have h := fourierCoeff_tendsto_cofinite f
  rw [Int.cofinite_eq] at h
  exact ⟨h.mono_left le_sup_left, h.mono_left le_sup_right⟩

/-- Rudin's c₀ is exactly the complex continuous functions on discrete Z vanishing at infinity. -/
abbrev FourierC0 := C₀(ℤ, ℂ)

theorem fourierC0_complete : CompleteSpace FourierC0 := inferInstance

theorem fourierC0_norm_formula (a : FourierC0) : ‖a‖ = ⨆ n : ℤ, ‖a n‖ :=
  a.toBCF.norm_eq_iSup_norm

def fourierToC0 (f : CircleL1) : FourierC0 where
  toFun := circleFourierCoeff f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    exact fourierCoeff_tendsto_cofinite f

@[simp] theorem fourierToC0_apply (f : CircleL1) (n : ℤ) :
    fourierToC0 f n = circleFourierCoeff f n := rfl

theorem fourierToC0_norm_le (f : CircleL1) : ‖fourierToC0 f‖ ≤ ‖f‖ := by
  change ‖(fourierToC0 f).toBCF‖ ≤ ‖f‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  exact fun n => norm_fourierCoeff_le_L1 f n

def fourierTransformL1Linear : CircleL1 →ₗ[ℂ] FourierC0 where
  toFun := fourierToC0
  map_add' f g := by
    ext n
    exact map_add (fourierCoeffL1 n) f g
  map_smul' c f := by
    ext n
    exact map_smul (fourierCoeffL1 n) c f

/-- 5.15: the bounded complex-linear Fourier coefficient map from L¹ into c₀. -/
def fourierTransformL1 : CircleL1 →L[ℂ] FourierC0 :=
  fourierTransformL1Linear.mkContinuous 1 fun f => by
    change ‖fourierToC0 f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using fourierToC0_norm_le f

@[simp] theorem fourierTransformL1_apply (f : CircleL1) (n : ℤ) :
    fourierTransformL1 f n = circleFourierCoeff f n := rfl

theorem fourierTransformL1_norm_le : ‖fourierTransformL1‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    change ‖fourierToC0 f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using fourierToC0_norm_le f

theorem fourierCoeff_constant_one_zero :
    circleFourierCoeff (Lp.const 1 circleMeasure (1 : ℂ)) 0 = 1 := by
  change fourierCoeff (Lp.const 1 circleMeasure (1 : ℂ)) 0 = 1
  rw [fourierCoeff_congr_ae (Lp.coeFn_const 1 circleMeasure (1 : ℂ))]
  simp [fourierCoeff]

/-- The Fourier coefficient map has norm exactly one; the constant function attains it. -/
theorem fourierTransformL1_norm : ‖fourierTransformL1‖ = 1 := by
  apply le_antisymm fourierTransformL1_norm_le
  let f : CircleL1 := Lp.const 1 circleMeasure (1 : ℂ)
  calc
    1 = ‖fourierTransformL1 f 0‖ := by
      rw [fourierTransformL1_apply, fourierCoeff_constant_one_zero]
      simp
    _ ≤ ‖fourierTransformL1 f‖ := (fourierTransformL1 f).toBCF.norm_coe_le_norm 0
    _ ≤ ‖fourierTransformL1‖ * ‖f‖ := fourierTransformL1.le_opNorm f
    _ = ‖fourierTransformL1‖ := by
      rw [circleLp_constant_one_norm 1 (by simp), mul_one]

theorem circleL1Product_integrable (f : CircleL1) (g : C(FourierCircle, ℂ)) :
    Integrable (fun t => g t * f t) circleMeasure :=
  (circleL1_integrable f).bdd_mul g.continuous.aestronglyMeasurable
    (ae_of_all _ fun t => g.norm_coe_le_norm t)

theorem circleL1Product_integral_norm_le (f : CircleL1) (g : C(FourierCircle, ℂ)) :
    ‖∫ t, g t * f t ∂circleMeasure‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    _ ≤ ∫ t, ‖g t * f t‖ ∂circleMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g‖ * ‖f t‖ ∂circleMeasure := by
      apply integral_mono (circleL1Product_integrable f g).norm
        ((circleL1_integrable f).norm.const_mul ‖g‖)
      intro t
      change ‖g t * f t‖ ≤ ‖g‖ * ‖f t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg _)
    _ = ‖f‖ * ‖g‖ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm, mul_comm]

def circleL1PairingLinear (f : CircleL1) : C(FourierCircle, ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∫ t, g t * f t ∂circleMeasure
  map_add' g h := by
    simp only [ContinuousMap.add_apply, add_mul]
    exact integral_add (circleL1Product_integrable f g) (circleL1Product_integrable f h)
  map_smul' c g := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul,
      RingHom.id_apply]

def circleL1Pairing (f : CircleL1) : C(FourierCircle, ℂ) →L[ℂ] ℂ :=
  (circleL1PairingLinear f).mkContinuous ‖f‖ (circleL1Product_integral_norm_le f)

/-- Vanishing Fourier coefficients imply vanishing integrals against every continuous function. -/
theorem integral_continuous_mul_eq_zero_of_fourierCoeff (f : CircleL1)
    (hf : ∀ n : ℤ, circleFourierCoeff f n = 0) (g : C(FourierCircle, ℂ)) :
    ∫ t, g t * f t ∂circleMeasure = 0 := by
  let B := circleL1Pairing f
  have hs : Submodule.span ℂ (Set.range (@fourier (2 * Real.pi))) ≤ B.ker := by
    apply Submodule.span_le.2
    rintro p ⟨n, rfl⟩
    change (∫ t, fourier n t * f t ∂circleMeasure) = 0
    simpa only [circleFourierCoeff, fourierCoeff, neg_neg, smul_eq_mul] using hf (-n)
  have hg : g ∈ (Submodule.span ℂ (Set.range (@fourier (2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  exact closure_minimal hs B.isClosed_ker hg

/-- Closed indicators are pointwise limits of uniformly bounded continuous functions. -/
def circleClosedApprox (S : Set FourierCircle) (j : ℕ) : C(FourierCircle, ℂ) where
  toFun t := ((thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) S t : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (NNReal.continuous_coe.comp (thickenedIndicator
      (show 0 < 1 / ((j : ℝ) + 1) by positivity) S).continuous)

theorem circleClosedApprox_norm_le (S : Set FourierCircle) (j : ℕ) (t : FourierCircle) :
    ‖circleClosedApprox S j t‖ ≤ 1 := by
  change ‖((thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) S t : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast thickenedIndicator_le_one
    (show 0 < 1 / ((j : ℝ) + 1) by positivity) S t

theorem circleClosedApprox_tendsto (S : Set FourierCircle) (hS : IsClosed S)
    (t : FourierCircle) :
    Tendsto (fun j => circleClosedApprox S j t) atTop
      (𝓝 (S.indicator (fun _ => (1 : ℂ)) t)) := by
  have hp (j : ℕ) : 0 < 1 / ((j : ℝ) + 1) := by positivity
  have hh := thickenedIndicator_tendsto_indicator_closure hp
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1))
      atTop (𝓝 0)) S
  have ht := tendsto_pi_nhds.mp hh t
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp ht
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  by_cases hm : t ∈ S <;>
    simpa [circleClosedApprox, hS.closure_eq, hm, Function.comp_def] using hcomplex

/-- The second approximation step in 5.15: all Fourier coefficients zero forces f=0 a.e. -/
theorem ae_eq_zero_of_fourierCoeff (f : CircleL1)
    (hf : ∀ n : ℤ, circleFourierCoeff f n = 0) : f =ᵐ[circleMeasure] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero (circleL1_integrable f)
  intro S hS
  have hd := tendsto_integral_of_dominated_convergence (f := S.indicator (⇑f)) (fun t => ‖f t‖)
    (fun j => (circleL1Product_integrable f (circleClosedApprox S j)).aestronglyMeasurable)
    (circleL1_integrable f).norm
    (fun j => ae_of_all _ fun t => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (circleClosedApprox_norm_le S j t))
    (ae_of_all _ fun t => by
      have h := (circleClosedApprox_tendsto S hS t).mul_const (f t)
      by_cases ht : t ∈ S <;> simpa [ht] using h)
  have hz : (fun j => ∫ t, circleClosedApprox S j t * f t ∂circleMeasure) =
      fun _ : ℕ => (0 : ℂ) := by
    funext j
    exact integral_continuous_mul_eq_zero_of_fourierCoeff f hf _
  rw [hz] at hd
  have hi : (∫ t, S.indicator (⇑f) t ∂circleMeasure) = 0 :=
    tendsto_nhds_unique hd tendsto_const_nhds
  simpa only [integral_indicator hS.measurableSet] using hi

/-- 5.15: the L¹ Fourier transform is one-to-one. -/
theorem fourierTransformL1_injective : Function.Injective fourierTransformL1 := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply Lp.ext
  have hz := ae_eq_zero_of_fourierCoeff (f - g) (fun n => by
    change fourierCoeffL1 n (f - g) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun a : FourierC0 => a n) hfg))
  exact hz.trans (Lp.coeFn_zero ℂ 1 circleMeasure).symm

def dirichletL1 (N : ℕ) : CircleL1 :=
  ContinuousMap.toLp 1 circleMeasure ℂ (dirichletKernel N)

theorem dirichletL1_norm (N : ℕ) : ‖dirichletL1 N‖ = lebesgueConstant N := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ℝ≥0∞))
    circleMeasure (dirichletKernel N)] with t ht
  exact congrArg norm ht

/-- The Dirichlet kernel has exactly the coefficient sequence 1 on [-N,N], 0 elsewhere. -/
theorem fourierTransformL1_dirichlet (N : ℕ) (n : ℤ) :
    fourierTransformL1 (dirichletL1 N) n =
      if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 1 else 0 := by
  change fourierCoeffL1 n (dirichletL1 N) = _
  simp only [dirichletL1, dirichletKernel, map_sum]
  change (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeffL1 n (fourierLp 1 k)) = _
  simp only [fourierCoeffL1_monomial]
  simp [eq_comm]

theorem fourierTransformL1_dirichlet_norm (N : ℕ) :
    ‖fourierTransformL1 (dirichletL1 N)‖ = 1 := by
  apply le_antisymm
  · change ‖(fourierTransformL1 (dirichletL1 N)).toBCF‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le zero_le_one).2
    intro n
    change ‖fourierTransformL1 (dirichletL1 N) n‖ ≤ 1
    rw [fourierTransformL1_dirichlet]
    split_ifs <;> norm_num
  · calc
      1 = ‖fourierTransformL1 (dirichletL1 N) 0‖ := by
        rw [fourierTransformL1_dirichlet]
        simp
      _ ≤ _ := (fourierTransformL1 (dirichletL1 N)).toBCF.norm_coe_le_norm 0

/-- 5.15: c₀ contains sequences which are not the Fourier coefficients of an L¹ function. -/
theorem fourierTransformL1_not_surjective : ¬ Function.Surjective fourierTransformL1 := by
  intro hs
  let e : CircleL1 ≃L[ℂ] FourierC0 := ContinuousLinearEquiv.ofBijective fourierTransformL1
    (LinearMap.ker_eq_bot.mpr fourierTransformL1_injective) (LinearMap.range_eq_top.mpr hs)
  have hb : BddAbove (Set.range lebesgueConstant) := by
    refine ⟨‖e.symm.toContinuousLinearMap‖, ?_⟩
    rintro r ⟨N, rfl⟩
    have hN := e.symm.toContinuousLinearMap.le_opNorm (e (dirichletL1 N))
    change ‖e.symm (e (dirichletL1 N))‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * ‖e (dirichletL1 N)‖ at hN
    rw [e.symm_apply_apply] at hN
    change ‖dirichletL1 N‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      ‖fourierTransformL1 (dirichletL1 N)‖ at hN
    simpa only [dirichletL1_norm, fourierTransformL1_dirichlet_norm, mul_one] using hN
  exact not_bddAbove_of_tendsto_atTop lebesgueConstant_tendsto hb

theorem exists_null_sequence_not_fourierCoefficients :
    ∃ a : ℤ → ℂ, Tendsto a cofinite (𝓝 0) ∧
      ∀ f : CircleL1, ∃ n : ℤ, circleFourierCoeff f n ≠ a n := by
  have hns := fourierTransformL1_not_surjective
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨a, ha⟩ := hns
  refine ⟨a, ?_, ?_⟩
  · simpa only [Filter.cocompact_eq_cofinite] using (zero_at_infty a)
  · intro f
    by_contra! hf
    apply ha f
    ext n
    exact hf n

theorem dirichletKernel_cosine (N : ℕ) (t : ℝ) :
    dirichletKernel N (t : FourierCircle) =
      ((1 + 2 * ∑ k ∈ Finset.range N, Real.cos (((k : ℝ) + 1) * t)) : ℝ) := by
  rw [dirichletKernel_apply, fejerDirichlet_pair]
  simp_rw [fourier_neg, Complex.add_conj]
  have hre (k : ℕ) : (fourier ((k : ℤ) + 1) (t : FourierCircle)).re =
      Real.cos (((k : ℝ) + 1) * t) := by
    change (trigMonomial ((k : ℤ) + 1) (t : FourierCircle)).re = _
    rw [trigMonomial_apply_real]
    simp [Complex.exp_re]
  simp_rw [hre]
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]

/-- The identity before division is valid even at the zeros of sin(t/2). -/
theorem dirichlet_cosine_sin_mul (N : ℕ) (t : ℝ) :
    Real.sin (t / 2) *
      (1 + 2 * ∑ k ∈ Finset.range N, Real.cos (((k : ℝ) + 1) * t)) =
      Real.sin (((N : ℝ) + 1 / 2) * t) := by
  have hs := Real.sin_mul_sum_cos N t t
  have hsum : (∑ k ∈ Finset.range N, Real.cos (t * k + t)) =
      ∑ k ∈ Finset.range N, Real.cos (((k : ℝ) + 1) * t) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  rw [hsum] at hs
  have ht := Real.two_mul_sin_mul_cos ((N : ℝ) * t / 2) (((N : ℝ) - 1) * t / 2 + t)
  rw [show (N : ℝ) * t / 2 - (((N : ℝ) - 1) * t / 2 + t) = -(t / 2) by ring,
    show (N : ℝ) * t / 2 + (((N : ℝ) - 1) * t / 2 + t) = ((N : ℝ) + 1 / 2) * t by ring,
    Real.sin_neg] at ht
  nlinarith

/-- 5.11(9): the sine quotient for the Dirichlet kernel away from its removable singularities. -/
theorem dirichletKernel_sine_quotient (N : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel N (t : FourierCircle) =
      ((Real.sin (((N : ℝ) + 1 / 2) * t) / Real.sin (t / 2)) : ℝ) := by
  rw [dirichletKernel_cosine]
  apply congrArg (fun r : ℝ => (r : ℂ))
  apply (eq_div_iff ht).2
  simpa only [mul_comm] using dirichlet_cosine_sin_mul N t

theorem dirichletKernel_zero (N : ℕ) : dirichletKernel N 0 = (2 * N + 1 : ℂ) := by
  have h := dirichletKernel_cosine N 0
  simpa [AddCircle.coe_zero, mul_comm, add_comm] using h

/-- The residual function family in 5.12 and every one of its divergence sets are uncountable. -/
theorem theorem_5_12_uncountable :
    ∃ E : Set C(FourierCircle, ℂ), Dense E ∧ IsGδ E ∧ ¬ E.Countable ∧
      ∀ f ∈ E, Dense (fourierDivergencePoints f) ∧ IsGδ (fourierDivergencePoints f) ∧
        ¬ (fourierDivergencePoints f).Countable := by
  letI : PerfectSpace C(FourierCircle, ℂ) := perfectSpace_of_module ℂ _
  obtain ⟨E, hd, hg, hE⟩ := theorem_5_12
  refine ⟨E, hd, hg, ?_, ?_⟩
  · intro hc
    exact countable_dense_not_gdelta E hc hd hg
  · intro f hf
    obtain ⟨hdf, hgf⟩ := hE f hf
    refine ⟨hdf, hgf, ?_⟩
    intro hc
    exact countable_dense_not_gdelta (fourierDivergencePoints f) hc hdf hgf

end RudinRCA.Chapter05
end
end
/- END Chapter05Fourier.lean -/

/- BEGIN Chapter05Boundary.lean -/
section

















/-! Rudin RCA 5.22–5.25. The boundary representation and final Poisson theorem
apply to arbitrary complex vector subspaces with the printed boundary norm property. -/

noncomputable section

open Set MeasureTheory Metric Filter ComplexOrder
open scoped ComplexConjugate CompactlySupported Topology ENNReal

namespace RudinRCA.Chapter05

section Representation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Real continuous functions embedded into complex continuous functions. -/
def ofRealContinuous : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun f := ⟨fun x => (f x : ℂ), by fun_prop⟩
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp] theorem ofRealContinuous_apply (f : C(X, ℝ)) (x : X) :
    ofRealContinuous f x = (f x : ℂ) := rfl

/-- 5.22: a norm-one unital functional on `C(X)` is positive. -/
theorem normOne_unital_positive (Λ : C(X, ℂ) →L[ℂ] ℂ)
    (hnorm : ‖Λ‖ = 1) (hone : Λ 1 = 1) : Monotone Λ :=
  ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr (by simp [hnorm, hone])

def positiveRealPart (Λ : C(X, ℂ) →L[ℂ] ℂ) (hΛ : Monotone Λ) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := (Λ (ofRealContinuous f.toContinuousMap)).re
      map_add' f g := by
        change (Λ (ofRealContinuous (f.toContinuousMap + g.toContinuousMap))).re = _
        simp only [map_add, Complex.add_re]
      map_smul' a f := by
        change (Λ (ofRealContinuous (a • f.toContinuousMap))).re = _
        simp only [map_smul, ContinuousLinearMap.map_smul_of_tower, Complex.smul_re,
          RingHom.id_apply, smul_eq_mul] }
    (fun f hf => by
      have h : (0 : C(X, ℂ)) ≤ ofRealContinuous f.toContinuousMap := by
        intro x
        exact Complex.nonneg_iff.mpr ⟨hf x, rfl⟩
      have hp : (0 : ℂ) ≤ Λ (ofRealContinuous f.toContinuousMap) := by
        simpa using hΛ h
      exact (Complex.nonneg_iff.mp hp).1)

/-- A positive complex functional is real on real-valued continuous functions. -/
theorem positive_real_value (Λ : C(X, ℂ) →L[ℂ] ℂ) (hΛ : Monotone Λ)
    (f : C(X, ℝ)) : (Λ (ofRealContinuous f)).im = 0 := by
  let L : C(X, ℂ) →ₚ[ℂ] ℂ := { Λ.toLinearMap with monotone' := hΛ }
  have hf : IsSelfAdjoint (ofRealContinuous f) := by
    change star (ofRealContinuous f) = ofRealContinuous f
    ext x
    simp
  exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (hf.map' L)

/-- The complex-valued version of real Riesz–Markov, with explicit positive measure. -/
theorem positiveFunctional_representation (Λ : C(X, ℂ) →L[ℂ] ℂ)
    (hΛ : Monotone Λ) :
    ∃ μ : Measure X, μ.Regular ∧ IsFiniteMeasure μ ∧
      ∀ f : C(X, ℂ), (∫ x, f x ∂μ) = Λ f := by
  let L := positiveRealPart Λ hΛ
  let μ := RealRMK.rieszMeasure L
  letI : μ.Regular := RealRMK.regular_rieszMeasure L
  letI : IsFiniteMeasure μ := inferInstance
  refine ⟨μ, inferInstance, inferInstance, ?_⟩
  have hreal (u : C(X, ℝ)) : (∫ x, (u x : ℂ) ∂μ) = Λ (ofRealContinuous u) := by
    have hr := RealRMK.integral_rieszMeasure L
      (CompactlySupportedContinuousMap.continuousMapEquiv u)
    change (∫ x, u x ∂μ) = (Λ (ofRealContinuous u)).re at hr
    rw [integral_complex_ofReal, hr]
    apply Complex.ext
    · simp
    · simpa using (positive_real_value Λ hΛ u).symm
  intro f
  let u : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let v : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have hf : f = ofRealContinuous u + Complex.I • ofRealContinuous v := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ofRealContinuous_apply,
      smul_eq_mul, u, v]
    simpa [mul_comm] using (Complex.re_add_im (f x)).symm
  have hu : Integrable (fun x => (u x : ℂ)) μ :=
    (ofRealContinuous u).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv : Integrable (fun x => Complex.I • (v x : ℂ)) μ :=
    ((ofRealContinuous v).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).smul Complex.I
  rw [hf, map_add, map_smul]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ofRealContinuous_apply]
  rw [integral_add hu hv, integral_smul, hreal u, hreal v]

/-- A positive functional taking one to one is integration against a regular probability. -/
theorem unital_positiveFunctional_probability (Λ : C(X, ℂ) →L[ℂ] ℂ)
    (hΛ : Monotone Λ) (hone : Λ 1 = 1) :
    ∃ μ : Measure X, μ.Regular ∧ IsProbabilityMeasure μ ∧
      ∀ f : C(X, ℂ), (∫ x, f x ∂μ) = Λ f := by
  obtain ⟨μ, hreg, hfin, hrep⟩ := positiveFunctional_representation Λ hΛ
  letI := hreg
  letI := hfin
  have hmass : μ.real univ = 1 := by
    have h := congrArg Complex.re (hrep 1)
    simpa [hone, integral_const] using h
  exact ⟨μ, hreg, isProbabilityMeasure_iff_real.mpr hmass, hrep⟩

/-- A fixed positive functional determines its finite regular representing measure uniquely. -/
theorem positiveFunctional_measure_unique (Λ : C(X, ℂ) →L[ℂ] ℂ)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (hμ : ∀ f : C(X, ℂ), (∫ x, f x ∂μ) = Λ f)
    (hν : ∀ f : C(X, ℂ), (∫ x, f x ∂ν) = Λ f) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have h := (hμ (ofRealContinuous f.toContinuousMap)).trans
    (hν (ofRealContinuous f.toContinuousMap)).symm
  simpa only [ofRealContinuous_apply, integral_complex_ofReal, Complex.ofReal_inj,
    CompactlySupportedContinuousMap.coe_toContinuousMap] using h

end Representation

section Boundary

variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [MeasurableSpace B] [BorelSpace B]

/-- Restriction along a compact boundary parametrization, as an isometric linear injection. -/
def boundaryRestriction (b : C(B, K)) (A : Submodule ℂ C(K, ℂ))
    (hboundary : ∀ f : A, ‖(f : C(K, ℂ)).comp b‖ = ‖(f : C(K, ℂ))‖) :
    A →ₗᵢ[ℂ] C(B, ℂ) where
  toLinearMap := (ContinuousMap.compCLM ℂ ℂ b).toLinearMap.comp A.subtype
  norm_map' f := hboundary f

/-- 5.22, allowing an arbitrary compact parametrization of the boundary. -/
theorem boundary_probability_representation (b : C(B, K)) (A : Submodule ℂ C(K, ℂ))
    (hone : (1 : C(K, ℂ)) ∈ A)
    (hboundary : ∀ f : A, ‖(f : C(K, ℂ)).comp b‖ = ‖(f : C(K, ℂ))‖)
    (x : K) :
    ∃ μ : Measure B, μ.Regular ∧ IsProbabilityMeasure μ ∧
      ∀ f : A, (∫ y, (f : C(K, ℂ)) (b y) ∂μ) = (f : C(K, ℂ)) x := by
  letI : Nonempty K := ⟨x⟩
  let R := boundaryRestriction b A hboundary
  let e := R.equivRange
  let E : R.toLinearMap.range →ₗ[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ x).toLinearMap.comp (A.subtype.comp e.symm.toLinearEquiv.toLinearMap)
  have hE (g : R.toLinearMap.range) : ‖E g‖ ≤ 1 * ‖g‖ := by
    calc
      ‖E g‖ ≤ ‖((e.symm g : A) : C(K, ℂ))‖ :=
        ContinuousMap.norm_coe_le_norm _ x
      _ = 1 * ‖g‖ := by
        change ‖e.symm g‖ = 1 * ‖g‖
        rw [one_mul]
        exact e.symm.norm_map g
  let Ec := E.mkContinuous 1 hE
  have hEc (f : A) : Ec (e f) = (f : C(K, ℂ)) x := by
    change ((e.symm (e f) : A) : C(K, ℂ)) x = _
    rw [e.symm_apply_apply]
  have he_coe (f : A) : (e f : C(B, ℂ)) = (f : C(K, ℂ)).comp b := rfl
  have he_one : (e ⟨1, hone⟩ : C(B, ℂ)) = 1 := by ext y; rfl
  have he_one_norm : ‖e ⟨1, hone⟩‖ = 1 := by
    rw [e.norm_map]
    change ‖(1 : C(K, ℂ))‖ = 1
    exact norm_one
  have hn : ‖Ec‖ = 1 := by
    apply le_antisymm (E.mkContinuous_norm_le zero_le_one hE)
    have h := Ec.le_opNorm (e ⟨1, hone⟩)
    simpa only [hEc, ContinuousMap.one_apply, norm_one, he_one_norm, mul_one] using h
  obtain ⟨Λ, hext, hnorm⟩ := exists_extension_norm_eq R.toLinearMap.range Ec
  have hΛone : Λ 1 = 1 := by
    have h := hext (e ⟨1, hone⟩)
    simpa only [he_one, hEc, ContinuousMap.one_apply] using h
  have hΛnorm : ‖Λ‖ = 1 := hnorm.trans hn
  obtain ⟨μ, hreg, hprob, hrep⟩ := unital_positiveFunctional_probability Λ
    (normOne_unital_positive Λ hΛnorm hΛone) hΛone
  refine ⟨μ, hreg, hprob, fun f => ?_⟩
  have h := hext (e f)
  have hr := hrep ((f : C(K, ℂ)).comp b)
  exact hr.trans (by simpa only [he_coe, hEc] using h)

/-- 5.22 in the printed compact-subset form. -/
theorem theorem_5_22 [MeasurableSpace K] [BorelSpace K]
    (H : Set K) [CompactSpace H] (A : Submodule ℂ C(K, ℂ))
    (hone : (1 : C(K, ℂ)) ∈ A)
    (hboundary : ∀ f : A, ‖(f : C(K, ℂ)).restrict H‖ = ‖(f : C(K, ℂ))‖)
    (x : K) :
    ∃ μ : Measure H, μ.Regular ∧ IsProbabilityMeasure μ ∧
      ∀ f : A, (∫ y : H, (f : C(K, ℂ)) y ∂μ) = (f : C(K, ℂ)) x := by
  exact boundary_probability_representation ⟨Subtype.val, continuous_subtype_val⟩
    A hone hboundary x

end Boundary

section Disc

open RudinRCA.Chapter04

abbrev UnitDisc := closedBall (0 : ℂ) 1

instance unitDiscCompact : CompactSpace UnitDisc :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)

/-- The circle's complex coordinate, using the same normalized parameter space as Chapter 4. -/
abbrev circleCoordinate : C(FourierCircle, ℂ) := trigMonomial 1

@[simp] theorem circleCoordinate_real (t : ℝ) :
    circleCoordinate (t : FourierCircle) = Complex.exp (t * Complex.I) := by
  change trigMonomial 1 (t : FourierCircle) = _
  rw [trigMonomial_apply_real]
  norm_num

@[simp] theorem circleCoordinate_norm (t : FourierCircle) : ‖circleCoordinate t‖ = 1 := by
  simp only [circleCoordinate, trigMonomial, fourier_apply, Circle.norm_coe]

theorem circleCoordinate_homeomorphism (t : FourierCircle) :
    circleCoordinate t = (fourierCircleHomeomorphism t : ℂ) := by
  induction t using QuotientAddGroup.induction_on with
  | H t => rw [circleCoordinate_real, fourierCircleHomeomorphism_apply]

/-- The boundary inclusion as a continuous map into the closed unit disc. -/
def discBoundary : C(FourierCircle, UnitDisc) where
  toFun t := ⟨circleCoordinate t, by simp [mem_closedBall, dist_zero_right]⟩
  continuous_toFun := circleCoordinate.continuous.subtype_mk
    (fun t => by simp only [mem_closedBall, dist_zero_right, circleCoordinate_norm, le_refl])

@[simp] theorem discBoundary_coe (t : FourierCircle) :
    (discBoundary t : ℂ) = circleCoordinate t := rfl

def discPolynomial (p : Polynomial ℂ) : C(UnitDisc, ℂ) :=
  ⟨fun z => p.eval z, p.continuous.comp continuous_subtype_val⟩

@[simp] theorem discPolynomial_apply (p : Polynomial ℂ) (z : UnitDisc) :
    discPolynomial p z = p.eval (z : ℂ) := rfl

/-- 5.23: polynomial supremum norms on the closed disc and the circle coincide. -/
theorem polynomial_boundary_norm (p : Polynomial ℂ) :
    ‖(discPolynomial p).comp discBoundary‖ = ‖discPolynomial p‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact (discPolynomial p).norm_coe_le_norm (discBoundary t)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 1)) p.differentiable.diffContOnCl
    · intro w hw
      rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
      let c : Circle := ⟨w, hw⟩
      let t := fourierCircleHomeomorphism.symm c
      have ht : circleCoordinate t = w := by
        rw [circleCoordinate_homeomorphism]
        exact congrArg (fun u : Circle => (u : ℂ))
          (fourierCircleHomeomorphism.apply_symm_apply c)
      simpa only [ContinuousMap.comp_apply, discPolynomial_apply, discBoundary_coe, ht]
        using ((discPolynomial p).comp discBoundary).norm_coe_le_norm t
    · simpa only [closure_ball (0 : ℂ) one_ne_zero] using z.property

/-- 5.23: an interior maximum forces the polynomial itself to be constant. -/
theorem polynomial_constant_of_interior_max (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1)
    (hmax : ∀ w ∈ closedBall (0 : ℂ) 1, ‖p.eval w‖ ≤ ‖p.eval z‖) :
    p = Polynomial.C (p.eval z) := by
  have heq := Complex.eq_const_of_exists_max p.differentiableOn hz
    (fun w hw => hmax w (ball_subset_closedBall hw))
  apply p.eq_of_infinite_eval_eq
  apply (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds (0 : ℂ) zero_lt_one)).mono
  intro w hw
  simpa using heq hw

/-- Continuity identifies the polynomial supremum on the open and closed discs. -/
theorem polynomial_open_disc_sup (p : Polynomial ℂ) :
    sSup ((fun z : ℂ => ‖p.eval z‖) '' ball (0 : ℂ) 1) = ‖discPolynomial p‖ := by
  have hbound (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖p.eval z‖ ≤ ‖discPolynomial p‖ :=
    (discPolynomial p).norm_coe_le_norm ⟨z, ball_subset_closedBall hz⟩
  have hbd : BddAbove ((fun z : ℂ => ‖p.eval z‖) '' ball (0 : ℂ) 1) :=
    ⟨‖discPolynomial p‖, by rintro _ ⟨z, hz, rfl⟩; exact hbound z hz⟩
  have hne : (((fun z : ℂ => ‖p.eval z‖) '' ball (0 : ℂ) 1) : Set ℝ).Nonempty :=
    (nonempty_ball.mpr zero_lt_one).image _
  apply le_antisymm
  · exact csSup_le hne (by rintro _ ⟨z, hz, rfl⟩; exact hbound z hz)
  · have hnonneg : 0 ≤ sSup ((fun z : ℂ => ‖p.eval z‖) '' ball (0 : ℂ) 1) :=
      (norm_nonneg (p.eval 0)).trans
        (le_csSup hbd ⟨0, mem_ball_self zero_lt_one, rfl⟩)
    apply (ContinuousMap.norm_le _ hnonneg).mpr
    intro z
    have hc := closure_minimal
      (show ball (0 : ℂ) 1 ⊆ {w | ‖p.eval w‖ ≤
          sSup ((fun z : ℂ => ‖p.eval z‖) '' ball (0 : ℂ) 1)} from
        fun w hw => le_csSup hbd ⟨w, hw, rfl⟩)
      (isClosed_le p.continuous.norm continuous_const)
    apply hc
    simpa only [closure_ball (0 : ℂ) one_ne_zero] using z.property

/-- Integration on continuous functions, with continuity in the supremum norm. -/
def continuousIntegral {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := ∫ x, f x ∂μ
      map_add' f g := integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' c f := integral_smul c f }
    (μ.real univ) (fun f => by
      change ‖∫ x, f x ∂μ‖ ≤ μ.real univ * ‖f‖
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x))

@[simp] theorem continuousIntegral_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) : continuousIntegral μ f = ∫ x, f x ∂μ := rfl

/-- 5.24: finite regular circle measures are determined by all their integer moments. -/
theorem circle_measure_eq_of_moments (μ ν : Measure FourierCircle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ n : ℤ, (∫ t, trigMonomial n t ∂μ) = ∫ t, trigMonomial n t ∂ν) : μ = ν := by
  have hd : Dense (Submodule.span ℂ (Set.range (trigMonomial : ℤ → C(FourierCircle, ℂ))) :
      Set C(FourierCircle, ℂ)) := by
    rw [dense_iff_closure_eq]
    change ((Submodule.span ℂ (Set.range (trigMonomial : ℤ → C(FourierCircle, ℂ)))).topologicalClosure :
      Set C(FourierCircle, ℂ)) = Set.univ
    rw [span_fourier_closure_eq_top]
    rfl
  have hi : continuousIntegral μ = continuousIntegral ν :=
    ContinuousLinearMap.ext_on hd (by rintro _ ⟨n, rfl⟩; exact h n)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have he := congrArg (fun L : C(FourierCircle, ℂ) →L[ℂ] ℂ =>
    L (ofRealContinuous f.toContinuousMap)) hi
  simpa only [continuousIntegral_apply, ofRealContinuous_apply, integral_complex_ofReal,
    Complex.ofReal_inj, CompactlySupportedContinuousMap.coe_toContinuousMap] using he

theorem circleCoordinate_pow (n : ℕ) (t : FourierCircle) :
    trigMonomial (n : ℤ) t = circleCoordinate t ^ n := by
  induction n with
  | zero => simp [trigMonomial]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- A representing measure agrees with evaluation on every polynomial monomial. -/
theorem representing_polynomial_moments (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (z : UnitDisc) (μ : Measure FourierCircle)
    (hrep : ∀ f : A, (∫ t, (f : C(UnitDisc, ℂ)) (discBoundary t) ∂μ) = (f : C(UnitDisc, ℂ)) z)
    (n : ℕ) : (∫ t, trigMonomial (n : ℤ) t ∂μ) = (z : ℂ) ^ n := by
  have h := hrep ⟨discPolynomial (Polynomial.X ^ n), hpoly _⟩
  simpa only [discPolynomial_apply, Polynomial.eval_pow, Polynomial.eval_X,
    discBoundary_coe, circleCoordinate_pow] using h

/-- Nonnegative moments determine all integer moments for positive circle measures. -/
theorem circle_moments_of_nonnegative (μ : Measure FourierCircle) (z : ℂ)
    (h : ∀ n : ℕ, (∫ t, trigMonomial (n : ℤ) t ∂μ) = z ^ n) :
    ∀ n : ℤ, (∫ t, trigMonomial n t ∂μ) =
      if 0 ≤ n then z ^ n.toNat else conj (z ^ n.natAbs) := by
  intro n
  cases n with
  | ofNat n => simpa using h n
  | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
      rw [hn, if_neg (by omega : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ))]
      simp only [Int.natAbs_neg, Int.natAbs_natCast, trigMonomial, fourier_neg]
      rw [integral_conj, h (n + 1)]

/-- Uniqueness of the positive representing measure under the polynomial hypothesis. -/
theorem representing_measure_unique (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A) (z : UnitDisc)
    (μ ν : Measure FourierCircle) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ f : A, (∫ t, (f : C(UnitDisc, ℂ)) (discBoundary t) ∂μ) = (f : C(UnitDisc, ℂ)) z)
    (hν : ∀ f : A, (∫ t, (f : C(UnitDisc, ℂ)) (discBoundary t) ∂ν) = (f : C(UnitDisc, ℂ)) z) : μ = ν := by
  apply circle_measure_eq_of_moments
  intro n
  rw [circle_moments_of_nonnegative μ (z : ℂ)
    (representing_polynomial_moments A hpoly z μ hμ),
    circle_moments_of_nonnegative ν (z : ℂ)
    (representing_polynomial_moments A hpoly z ν hν)]

/-- Normalized integration over our additive circle is the usual geometric circle average. -/
theorem circleIntegral_eq_circleAverage (f : ℂ → ℂ) :
    (∫ t, f (circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp only [zero_add, Real.circleAverage_def, circleCoordinate_real,
    circleMap, Complex.ofReal_one, one_mul]

theorem circleCoordinate_ne_interior (z : ℂ) (hz : ‖z‖ < 1) (t : FourierCircle) :
    circleCoordinate t - z ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [circleCoordinate_norm] at he
  linarith

/-- The positive continuous Poisson density at an interior point. -/
def poissonDensity (z : ℂ) (hz : ‖z‖ < 1) : C(FourierCircle, ℝ) where
  toFun t := (1 - ‖z‖ ^ 2) / ‖circleCoordinate t - z‖ ^ 2
  continuous_toFun := continuous_const.div
    ((circleCoordinate.continuous.sub continuous_const).norm.pow 2)
    (fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (circleCoordinate_ne_interior z hz t)))

theorem poissonDensity_pos (z : ℂ) (hz : ‖z‖ < 1) (t : FourierCircle) :
    0 < poissonDensity z hz t := by
  apply div_pos
  · nlinarith [norm_nonneg z]
  · exact sq_pos_of_pos (norm_pos_iff.mpr (circleCoordinate_ne_interior z hz t))

theorem poissonDensity_eq_kernel (z : ℂ) (hz : ‖z‖ < 1) (t : FourierCircle) :
    poissonDensity z hz t = poissonKernel 0 z (circleCoordinate t) := by
  simp [poissonDensity, poissonKernel, circleCoordinate_norm]

/-- Polynomial monomials, used only to compute the explicit density's moments. -/
theorem poissonDensity_moment (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    (∫ t, poissonDensity z hz t • circleCoordinate t ^ n ∂circleMeasure) = z ^ n := by
  have hf : DiffContOnCl ℂ (fun w : ℂ => w ^ n) (ball (0 : ℂ) 1) :=
    (differentiable_id.pow n : Differentiable ℂ (fun w : ℂ => w ^ n)).diffContOnCl
  have h := hf.circleAverage_poissonKernel_smul
    (show z ∈ ball (0 : ℂ) 1 by simpa [mem_ball, dist_zero_right] using hz)
  rw [← circleIntegral_eq_circleAverage] at h
  simpa only [Pi.smul_apply', poissonDensity_eq_kernel] using h

theorem integral_poissonDensity (z : ℂ) (hz : ‖z‖ < 1) :
    (∫ t, poissonDensity z hz t ∂circleMeasure) = 1 := by
  have h := poissonDensity_moment z hz 0
  simp only [pow_zero, Complex.real_smul, mul_one, integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using h)

/-- The normalized angular measure weighted by the Poisson density. -/
def poissonMeasure (z : ℂ) (hz : ‖z‖ < 1) : Measure FourierCircle :=
  circleMeasure.withDensity (fun t => ENNReal.ofReal (poissonDensity z hz t))

instance poissonMeasure_finite (z : ℂ) (hz : ‖z‖ < 1) :
    IsFiniteMeasure (poissonMeasure z hz) :=
  isFiniteMeasure_withDensity_ofReal
    ((poissonDensity z hz).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

/-- The kernel has mass one, so its measure is a probability. -/
instance poissonMeasure_probability (z : ℂ) (hz : ‖z‖ < 1) :
    IsProbabilityMeasure (poissonMeasure z hz) where
  measure_univ := by
    rw [poissonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        ((poissonDensity z hz).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (Filter.Eventually.of_forall fun t => (poissonDensity_pos z hz t).le),
      integral_poissonDensity]
    simp

/-- Integration against the explicit measure is weighted angular integration. -/
theorem integral_poissonMeasure (z : ℂ) (hz : ‖z‖ < 1) (f : FourierCircle → ℂ) :
    (∫ t, f t ∂poissonMeasure z hz) =
      ∫ t, poissonDensity z hz t • f t ∂circleMeasure := by
  rw [poissonMeasure, integral_withDensity_eq_integral_toReal_smul
    (poissonDensity z hz).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  congr 1
  ext t
  rw [ENNReal.toReal_ofReal (poissonDensity_pos z hz t).le]

theorem poissonMeasure_moment (z : ℂ) (hz : ‖z‖ < 1) (n : ℕ) :
    (∫ t, trigMonomial (n : ℤ) t ∂poissonMeasure z hz) = z ^ n := by
  rw [integral_poissonMeasure]
  simp only [circleCoordinate_pow]
  exact poissonDensity_moment z hz n

/-- 5.24: the representing measure is uniquely the explicit Poisson probability. -/
theorem representing_measure_eq_poisson (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (z : UnitDisc) (hz : ‖(z : ℂ)‖ < 1) (μ : Measure FourierCircle)
    [IsProbabilityMeasure μ]
    (hrep : ∀ f : A, (∫ t, (f : C(UnitDisc, ℂ)) (discBoundary t) ∂μ) = (f : C(UnitDisc, ℂ)) z) :
    μ = poissonMeasure z hz := by
  apply circle_measure_eq_of_moments
  intro n
  rw [circle_moments_of_nonnegative μ (z : ℂ)
    (representing_polynomial_moments A hpoly z μ hrep),
    circle_moments_of_nonnegative (poissonMeasure z hz) (z : ℂ)
    (poissonMeasure_moment z hz)]

/-- 5.25 at the exact printed generality: no analytic assumption on `A` or `f`. -/
theorem poisson_representation (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (hboundary : ∀ f : A, ‖(f : C(UnitDisc, ℂ)).comp discBoundary‖ = ‖(f : C(UnitDisc, ℂ))‖)
    (z : UnitDisc) (hz : ‖(z : ℂ)‖ < 1) (f : A) :
    (f : C(UnitDisc, ℂ)) z =
      ∫ t, poissonDensity z hz t • (f : C(UnitDisc, ℂ)) (discBoundary t) ∂circleMeasure := by
  have hone : (1 : C(UnitDisc, ℂ)) ∈ A := by
    have heq : discPolynomial 1 = (1 : C(UnitDisc, ℂ)) := by
      ext z
      simp only [discPolynomial_apply, Polynomial.eval_one, ContinuousMap.one_apply]
    rw [← heq]
    exact hpoly 1
  obtain ⟨μ, hreg, hprob, hrep⟩ :=
    boundary_probability_representation discBoundary A hone hboundary z
  letI := hprob
  have heq := representing_measure_eq_poisson A hpoly z hz μ hrep
  have h := hrep f
  rw [heq, integral_poissonMeasure] at h
  exact h.symm

/-- The normalized angular integral form of 5.25. -/
theorem theorem_5_25 (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (hboundary : ∀ f : A, ‖(f : C(UnitDisc, ℂ)).comp discBoundary‖ = ‖(f : C(UnitDisc, ℂ))‖)
    (z : UnitDisc) (hz : ‖(z : ℂ)‖ < 1) (f : A) :
    (f : C(UnitDisc, ℂ)) z = (1 / (2 * Real.pi) : ℝ) •
      ∫ t in -Real.pi..Real.pi,
        poissonDensity z hz (t : FourierCircle) •
          (f : C(UnitDisc, ℂ)) (discBoundary (t : FourierCircle)) := by
  rw [poisson_representation A hpoly hboundary z hz f, circleIntegral_interval]

/-- The denominator of the Poisson kernel in polar coordinates. -/
theorem poisson_denominator_polar (r θ t : ℝ) :
    ‖Complex.exp (t * Complex.I) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 =
      1 - 2 * r * Real.cos (θ - t) + r ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I, one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one,
    map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub]
  ring

/-- 5.24: the rational cosine form of the positive kernel. -/
theorem poissonDensity_polar (r θ t : ℝ) (hr : 0 ≤ r)
    (hz : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ < 1) :
    poissonDensity ((r : ℂ) * Complex.exp (θ * Complex.I)) hz (t : FourierCircle) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - t) + r ^ 2) := by
  change (1 - ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2) /
    ‖circleCoordinate (t : FourierCircle) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = _
  rw [circleCoordinate_real, poisson_denominator_polar]
  simp [norm_mul, Complex.norm_real, abs_of_nonneg hr]

/-- 5.25 with the printed rational kernel and normalized angular integral. -/
theorem poisson_formula_polar (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (hboundary : ∀ f : A, ‖(f : C(UnitDisc, ℂ)).comp discBoundary‖ = ‖(f : C(UnitDisc, ℂ))‖)
    (z : UnitDisc) (hz : ‖(z : ℂ)‖ < 1) (r θ : ℝ) (hr : 0 ≤ r)
    (hzpolar : (z : ℂ) = (r : ℂ) * Complex.exp (θ * Complex.I)) (f : A) :
    (f : C(UnitDisc, ℂ)) z = (1 / (2 * Real.pi) : ℝ) •
      ∫ t in -Real.pi..Real.pi,
        ((1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - t) + r ^ 2)) •
          (f : C(UnitDisc, ℂ)) (discBoundary (t : FourierCircle)) := by
  rw [theorem_5_25 A hpoly hboundary z hz f]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hp : poissonDensity z hz (t : FourierCircle) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - t) + r ^ 2) := by
    simpa only [hzpolar] using
      poissonDensity_polar r θ t hr (show ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 by
        simpa only [← hzpolar] using hz)
  change poissonDensity z hz (t : FourierCircle) •
    (f : C(UnitDisc, ℂ)) (discBoundary (t : FourierCircle)) = _
  rw [hp]

/-- The integer Fourier modes of the Poisson kernel. -/
def poissonMode (z : ℂ) (n : ℤ) : C(FourierCircle, ℂ) :=
  if 0 ≤ n then z ^ n.toNat • trigMonomial (-n)
  else conj (z ^ n.natAbs) • trigMonomial (-n)

theorem trigMonomial_norm (n : ℤ) : ‖trigMonomial n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp [trigMonomial, fourier_apply]

theorem poissonMode_norm (z : ℂ) (n : ℤ) : ‖poissonMode z n‖ = ‖z‖ ^ n.natAbs := by
  cases n with
  | ofNat n => simp [poissonMode, norm_smul, trigMonomial_norm]
  | negSucc n => simp [poissonMode, norm_smul, trigMonomial_norm]

/-- Absolute convergence in the supremum norm, hence uniform absolute convergence. -/
theorem poissonMode_summable_norm (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℤ => ‖poissonMode z n‖) := by
  simp only [poissonMode_norm]
  have hg := summable_geometric_of_lt_one (norm_nonneg z) hz
  apply Summable.of_nat_of_neg_add_one
  · simpa using hg
  · have hneg (n : ℕ) : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl,
        Int.natAbs_neg, Int.natAbs_natCast]
    simpa only [hneg, pow_succ] using hg.mul_right ‖z‖

theorem poissonMode_nat (z : ℂ) (n : ℕ) (t : FourierCircle) :
    poissonMode z (n : ℤ) t = (z * conj (circleCoordinate t)) ^ n := by
  rw [poissonMode, if_pos (Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast, ContinuousMap.smul_apply, smul_eq_mul]
  rw [fourier_neg, circleCoordinate_pow, map_pow, mul_pow]

theorem poissonMode_neg_nat (z : ℂ) (n : ℕ) (t : FourierCircle) :
    poissonMode z (-((n + 1 : ℕ) : ℤ)) t =
      conj (z * conj (circleCoordinate t)) ^ (n + 1) := by
  rw [poissonMode, if_neg (by omega : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ))]
  simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_neg,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [circleCoordinate_pow]
  simp only [map_mul, map_pow, starRingEnd_self_apply, mul_pow]

/-- The sum of the two scalar geometric series, in norm form. -/
theorem poisson_geometric_identity (q : ℂ) (hq : ‖q‖ < 1) :
    (1 - q)⁻¹ + conj q * (1 - conj q)⁻¹ =
      (((1 - ‖q‖ ^ 2) / ‖1 - q‖ ^ 2 : ℝ) : ℂ) := by
  have hne : 1 - q ≠ 0 := by
    intro h
    have he : q = 1 := (sub_eq_zero.mp h).symm
    simpa [he] using hq
  have hne' : 1 - conj q ≠ 0 := by
    intro h
    apply hne
    have hc := congrArg conj h
    simpa using hc
  rw [← Complex.normSq_eq_norm_sq q, ← Complex.normSq_eq_norm_sq (1 - q),
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_one]
  field_simp [hne, hne']
  <;> ring

/-- The scalar integer series has the Poisson density as its sum. -/
theorem poissonMode_hasSum_apply (z : ℂ) (hz : ‖z‖ < 1) (t : FourierCircle) :
    HasSum (fun n : ℤ => poissonMode z n t) (poissonDensity z hz t : ℂ) := by
  let w := circleCoordinate t
  let q := z * conj w
  have hw : ‖w‖ = 1 := circleCoordinate_norm t
  have hqnorm : ‖q‖ = ‖z‖ := by
    change ‖z * conj w‖ = ‖z‖
    rw [norm_mul, Complex.norm_conj, hw, mul_one]
  have hq : ‖q‖ < 1 := by simpa only [hqnorm] using hz
  have hp : HasSum (fun n : ℕ => poissonMode z (n : ℤ) t) (1 - q)⁻¹ := by
    simpa only [poissonMode_nat, q, w] using hasSum_geometric_of_norm_lt_one hq
  have hm : HasSum (fun n : ℕ => poissonMode z (-((n + 1 : ℕ) : ℤ)) t)
      (conj q * (1 - conj q)⁻¹) := by
    simpa only [poissonMode_neg_nat, q, w, pow_succ, mul_comm] using
      (hasSum_geometric_of_norm_lt_one (show ‖conj q‖ < 1 by simpa using hq)).mul_left (conj q)
  have hs : HasSum (fun n : ℤ => poissonMode z n t)
      ((1 - q)⁻¹ + conj q * (1 - conj q)⁻¹) :=
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => poissonMode z n t) hp
      (by simpa only [Nat.cast_add, Nat.cast_one] using hm)
  have hunit : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    simp
  have hmul : (w - z) * conj w = 1 - q := by
    dsimp [q]
    rw [sub_mul, hunit]
  have hden : ‖1 - q‖ = ‖w - z‖ := by
    rw [← hmul, norm_mul, Complex.norm_conj, hw, mul_one]
  have heq : (1 - q)⁻¹ + conj q * (1 - conj q)⁻¹ = (poissonDensity z hz t : ℂ) := by
    rw [poisson_geometric_identity q hq, hqnorm, hden]
    rfl
  exact heq ▸ hs

/-- 5.24: the Fourier series converges in the uniform norm to the explicit kernel. -/
theorem poissonKernel_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (poissonMode z) (ofRealContinuous (poissonDensity z hz)) := by
  have hs := (poissonMode_summable_norm z hz).of_norm
  have heq : (∑' n : ℤ, poissonMode z n) = ofRealContinuous (poissonDensity z hz) := by
    ext t
    exact ((ContinuousMap.evalCLM ℂ t).hasSum hs.hasSum).unique
      (poissonMode_hasSum_apply z hz t)
  exact heq ▸ hs.hasSum

/-- The symmetric integer partial sums of the Poisson series converge uniformly. -/
theorem poissonKernel_uniform_series (z : ℂ) (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), poissonMode z n)
      atTop (𝓝 (ofRealContinuous (poissonDensity z hz))) :=
  (poissonKernel_hasSum z hz).comp (Finset.tendsto_Icc_neg (R := ℤ))

theorem polar_power (r θ : ℝ) (n : ℕ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ n =
      (r : ℂ) ^ n * Complex.exp ((n : ℂ) * θ * Complex.I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem conj_polar_power (r θ : ℝ) (n : ℕ) :
    conj (((r : ℂ) * Complex.exp (θ * Complex.I)) ^ n) =
      (r : ℂ) ^ n * Complex.exp (-((n : ℂ) * θ * Complex.I)) := by
  rw [polar_power, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  congr 1
  simp

/-- 5.24: the moments in the book's polar-coordinate notation, for every integer. -/
theorem representing_moments_polar (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (z : UnitDisc) (μ : Measure FourierCircle)
    (hrep : ∀ f : A, (∫ t, (f : C(UnitDisc, ℂ)) (discBoundary t) ∂μ) = (f : C(UnitDisc, ℂ)) z)
    (r θ : ℝ) (hzpolar : (z : ℂ) = (r : ℂ) * Complex.exp (θ * Complex.I)) (n : ℤ) :
    (∫ t, trigMonomial n t ∂μ) =
      (r : ℂ) ^ n.natAbs * Complex.exp ((n : ℂ) * θ * Complex.I) := by
  rw [circle_moments_of_nonnegative μ (z : ℂ)
    (representing_polynomial_moments A hpoly z μ hrep), hzpolar]
  cases n with
  | ofNat n =>
      change (if 0 ≤ (n : ℤ) then _ else _) = _
      rw [if_pos (Int.natCast_nonneg n)]
      simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, Int.natAbs_natCast, Int.cast_natCast] using
        polar_power r θ n
  | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      rw [if_neg (by omega : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ))]
      simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
      rw [conj_polar_power]
      congr 2 <;> ring

theorem polar_circle_difference (r θ t : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) * conj (circleCoordinate (t : FourierCircle)) =
      (r : ℂ) * Complex.exp ((θ - t) * Complex.I) := by
  rw [circleCoordinate_real, mul_assoc, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

/-- The exact exponential terms appearing in the printed Poisson-kernel series. -/
theorem poissonMode_polar (r θ t : ℝ) (n : ℤ) :
    poissonMode ((r : ℂ) * Complex.exp (θ * Complex.I)) n (t : FourierCircle) =
      (r : ℂ) ^ n.natAbs * Complex.exp ((n : ℂ) * (θ - t) * Complex.I) := by
  cases n with
  | ofNat n =>
      change poissonMode ((r : ℂ) * Complex.exp (θ * Complex.I)) (n : ℤ) (t : FourierCircle) =
        (r : ℂ) ^ n * Complex.exp ((n : ℂ) * (θ - t) * Complex.I)
      rw [poissonMode_nat, polar_circle_difference]
      simpa only [Complex.ofReal_sub] using polar_power r (θ - t) n
  | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega,
        poissonMode_neg_nat, polar_circle_difference, ← map_pow]
      simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
      calc
        _ = (r : ℂ) ^ (n + 1) * Complex.exp (-((n + 1 : ℂ) * (θ - t) * Complex.I)) := by
          simpa only [Complex.ofReal_sub, Nat.cast_add, Nat.cast_one] using
            conj_polar_power r (θ - t) (n + 1)
        _ = _ := by congr 2 <;> push_cast <;> ring

/-- The printed scalar Fourier series sums to the rational Poisson kernel. -/
theorem poisson_kernel_series_polar (r θ t : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => (r : ℂ) ^ n.natAbs *
      Complex.exp ((n : ℂ) * (θ - t) * Complex.I))
      (((1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - t) + r ^ 2) : ℝ) : ℂ) := by
  have hz : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 := by
    simpa [norm_mul, Complex.norm_real, abs_of_nonneg hr] using hr1
  simpa only [poissonMode_polar, poissonDensity_polar r θ t hr hz] using
    poissonMode_hasSum_apply ((r : ℂ) * Complex.exp (θ * Complex.I)) hz (t : FourierCircle)

/-- At a boundary point the unique representing probability is the point mass. -/
theorem representing_boundary_dirac (A : Submodule ℂ C(UnitDisc, ℂ))
    (hpoly : ∀ p : Polynomial ℂ, discPolynomial p ∈ A)
    (t : FourierCircle) (μ : Measure FourierCircle) [IsProbabilityMeasure μ]
    (hrep : ∀ f : A, (∫ u, (f : C(UnitDisc, ℂ)) (discBoundary u) ∂μ) =
      (f : C(UnitDisc, ℂ)) (discBoundary t)) :
    μ = Measure.dirac t := by
  apply representing_measure_unique A hpoly (discBoundary t) μ (Measure.dirac t) hrep
  intro f
  simp

end Disc

end RudinRCA.Chapter05























































end
end
/- END Chapter05Boundary.lean -/

/- Axiom audit: every theorem/lemma declared in this chapter. -/
#print axioms RudinRCA.Chapter05.normed_space_axioms
#print axioms RudinRCA.Chapter05.norm_induced_metric
#print axioms RudinRCA.Chapter05.finite_extendedOperatorNorm_iff
#print axioms RudinRCA.Chapter05.extendedOperatorNorm_sphere
#print axioms RudinRCA.Chapter05.apply_le_extendedOperatorNorm
#print axioms RudinRCA.Chapter05.extendedOperatorNorm_least
#print axioms RudinRCA.Chapter05.operator_norm_closed_ball
#print axioms RudinRCA.Chapter05.operator_norm_sphere
#print axioms RudinRCA.Chapter05.linear_map_norm_smul
#print axioms RudinRCA.Chapter05.operator_norm_least
#print axioms RudinRCA.Chapter05.operator_maps_unit_ball
#print axioms RudinRCA.Chapter05.bounded_iff_continuous
#print axioms RudinRCA.Chapter05.linear_continuous_of_continuousAt
#print axioms RudinRCA.Chapter05.bounded_continuous_at_one_point
#print axioms RudinRCA.Chapter05.hilbert_is_banach
#print axioms RudinRCA.Chapter05.lp_is_banach
#print axioms RudinRCA.Chapter05.vanishing_at_infinity_is_banach
#print axioms RudinRCA.Chapter05.complex_is_banach
#print axioms RudinRCA.Chapter05.closure_ball_ne_closedBall
#print axioms RudinRCA.Chapter05.baire_dense_intersection
#print axioms RudinRCA.Chapter05.baire_nonempty_intersection
#print axioms RudinRCA.Chapter05.baire_dense_gdelta_intersection
#print axioms RudinRCA.Chapter05.nowhere_dense_definition
#print axioms RudinRCA.Chapter05.first_category_definition
#print axioms RudinRCA.Chapter05.complete_space_not_first_category
#print axioms RudinRCA.Chapter05.empty_complete_space_first_category
#print axioms RudinRCA.Chapter05.countable_is_meagre
#print axioms RudinRCA.Chapter05.countable_dense_not_gdelta
#print axioms RudinRCA.Chapter05.empty_countable_dense_gdelta
#print axioms RudinRCA.Chapter05.operator_orbit_lowerSemicontinuous
#print axioms RudinRCA.Chapter05.unbounded_orbit_eq_iInter
#print axioms RudinRCA.Chapter05.theorem_5_8_unbounded_residual
#print axioms RudinRCA.Chapter05.unbounded_orbit_iSup_eq_top
#print axioms RudinRCA.Chapter05.theorem_5_8
#print axioms RudinRCA.Chapter05.theorem_5_9
#print axioms RudinRCA.Chapter05.banachInverseEquiv_apply
#print axioms RudinRCA.Chapter05.theorem_5_10
#print axioms RudinRCA.Chapter05.theorem_5_16
#print axioms RudinRCA.Chapter05.theorem_5_16_norm_formula
#print axioms RudinRCA.Chapter05.theorem_5_18
#print axioms RudinRCA.Chapter05.theorem_5_19_separate
#print axioms RudinRCA.Chapter05.theorem_5_19
#print axioms RudinRCA.Chapter05.theorem_5_20
#print axioms RudinRCA.Chapter05.theorem_5_21_dual_complete
#print axioms RudinRCA.Chapter05.theorem_5_21_dual_nontrivial
#print axioms RudinRCA.Chapter05.theorem_5_21_separates
#print axioms RudinRCA.Chapter05.theorem_5_21_evaluation
#print axioms RudinRCA.Chapter05.theorem_5_21_norm_supremum
#print axioms RudinRCA.Chapter05.realPartFunctional_apply
#print axioms RudinRCA.Chapter05.theorem_5_17a
#print axioms RudinRCA.Chapter05.theorem_5_17b
#print axioms RudinRCA.Chapter05.theorem_5_17c
#print axioms RudinRCA.Chapter05.theorem_5_17c_extended
#print axioms RudinRCA.Chapter05.small_open_closure
#print axioms RudinRCA.Chapter05.open_small_diam_splitting
#print axioms RudinRCA.Chapter05.cantor_preperfect
#print axioms RudinRCA.Chapter05.dense_open_intersection_cantor_injection
#print axioms RudinRCA.Chapter05.dense_gdelta_contains_nonempty_perfect
#print axioms RudinRCA.Chapter05.dirichletKernel_apply
#print axioms RudinRCA.Chapter05.circleL1_integrable
#print axioms RudinRCA.Chapter05.circleFourierPartialSum_convolution
#print axioms RudinRCA.Chapter05.circleFourierPartialSum_interval
#print axioms RudinRCA.Chapter05.fourierPartialSum_subsequence_ae
#print axioms RudinRCA.Chapter05.continuousFourierPartialSum_subsequence_ae
#print axioms RudinRCA.Chapter05.norm_fourierCoeff_le_L1
#print axioms RudinRCA.Chapter05.fourierCoeffL1_apply
#print axioms RudinRCA.Chapter05.fourierCoeffL1_norm_le
#print axioms RudinRCA.Chapter05.fourierCoeffL1_toLp
#print axioms RudinRCA.Chapter05.fourierPartialSumFunctional_apply
#print axioms RudinRCA.Chapter05.lebesgueConstant_nonneg
#print axioms RudinRCA.Chapter05.fourierPartialSumFunctional_norm_le
#print axioms RudinRCA.Chapter05.fourierMaximal_lowerSemicontinuous
#print axioms RudinRCA.Chapter05.dirichletKernel_shift
#print axioms RudinRCA.Chapter05.dirichletKernel_shift_im
#print axioms RudinRCA.Chapter05.positiveSineSum_le_dirichlet_norm
#print axioms RudinRCA.Chapter05.integral_positive_sine
#print axioms RudinRCA.Chapter05.integral_positiveSineSum
#print axioms RudinRCA.Chapter05.lebesgueConstant_harmonic_lower
#print axioms RudinRCA.Chapter05.lebesgueConstant_tendsto
#print axioms RudinRCA.Chapter05.regularized_norm_pos
#print axioms RudinRCA.Chapter05.regularized_norm_ge
#print axioms RudinRCA.Chapter05.regularized_sign_error
#print axioms RudinRCA.Chapter05.dirichletNormTest_norm_le
#print axioms RudinRCA.Chapter05.fourierPartialSumFunctional_normTest
#print axioms RudinRCA.Chapter05.fourierPartialSumFunctional_norm
#print axioms RudinRCA.Chapter05.fourierPartialSumFunctional_norm_tendsto
#print axioms RudinRCA.Chapter05.fourierMaximal_eq_top_iff
#print axioms RudinRCA.Chapter05.fourierDivergenceFunctions_dense_Gδ
#print axioms RudinRCA.Chapter05.fourierDivergenceFunctions_not_tendsto
#print axioms RudinRCA.Chapter05.fourierDivergence_countable
#print axioms RudinRCA.Chapter05.fourierDivergencePoints_eq_iInter
#print axioms RudinRCA.Chapter05.fourierDivergencePoints_isGδ
#print axioms RudinRCA.Chapter05.theorem_5_12
#print axioms RudinRCA.Chapter05.fourierCoeffL1_monomial
#print axioms RudinRCA.Chapter05.fourierCoeff_tendsto_cofinite
#print axioms RudinRCA.Chapter05.fourierCoeff_tendsto_both_ends
#print axioms RudinRCA.Chapter05.fourierC0_complete
#print axioms RudinRCA.Chapter05.fourierC0_norm_formula
#print axioms RudinRCA.Chapter05.fourierToC0_apply
#print axioms RudinRCA.Chapter05.fourierToC0_norm_le
#print axioms RudinRCA.Chapter05.fourierTransformL1_apply
#print axioms RudinRCA.Chapter05.fourierTransformL1_norm_le
#print axioms RudinRCA.Chapter05.fourierCoeff_constant_one_zero
#print axioms RudinRCA.Chapter05.fourierTransformL1_norm
#print axioms RudinRCA.Chapter05.circleL1Product_integrable
#print axioms RudinRCA.Chapter05.circleL1Product_integral_norm_le
#print axioms RudinRCA.Chapter05.integral_continuous_mul_eq_zero_of_fourierCoeff
#print axioms RudinRCA.Chapter05.circleClosedApprox_norm_le
#print axioms RudinRCA.Chapter05.circleClosedApprox_tendsto
#print axioms RudinRCA.Chapter05.ae_eq_zero_of_fourierCoeff
#print axioms RudinRCA.Chapter05.fourierTransformL1_injective
#print axioms RudinRCA.Chapter05.dirichletL1_norm
#print axioms RudinRCA.Chapter05.fourierTransformL1_dirichlet
#print axioms RudinRCA.Chapter05.fourierTransformL1_dirichlet_norm
#print axioms RudinRCA.Chapter05.fourierTransformL1_not_surjective
#print axioms RudinRCA.Chapter05.exists_null_sequence_not_fourierCoefficients
#print axioms RudinRCA.Chapter05.dirichletKernel_cosine
#print axioms RudinRCA.Chapter05.dirichlet_cosine_sin_mul
#print axioms RudinRCA.Chapter05.dirichletKernel_sine_quotient
#print axioms RudinRCA.Chapter05.dirichletKernel_zero
#print axioms RudinRCA.Chapter05.theorem_5_12_uncountable
#print axioms RudinRCA.Chapter05.ofRealContinuous_apply
#print axioms RudinRCA.Chapter05.normOne_unital_positive
#print axioms RudinRCA.Chapter05.positive_real_value
#print axioms RudinRCA.Chapter05.positiveFunctional_representation
#print axioms RudinRCA.Chapter05.unital_positiveFunctional_probability
#print axioms RudinRCA.Chapter05.positiveFunctional_measure_unique
#print axioms RudinRCA.Chapter05.boundary_probability_representation
#print axioms RudinRCA.Chapter05.theorem_5_22
#print axioms RudinRCA.Chapter05.circleCoordinate_real
#print axioms RudinRCA.Chapter05.circleCoordinate_norm
#print axioms RudinRCA.Chapter05.circleCoordinate_homeomorphism
#print axioms RudinRCA.Chapter05.discBoundary_coe
#print axioms RudinRCA.Chapter05.discPolynomial_apply
#print axioms RudinRCA.Chapter05.polynomial_boundary_norm
#print axioms RudinRCA.Chapter05.polynomial_constant_of_interior_max
#print axioms RudinRCA.Chapter05.polynomial_open_disc_sup
#print axioms RudinRCA.Chapter05.continuousIntegral_apply
#print axioms RudinRCA.Chapter05.circle_measure_eq_of_moments
#print axioms RudinRCA.Chapter05.circleCoordinate_pow
#print axioms RudinRCA.Chapter05.representing_polynomial_moments
#print axioms RudinRCA.Chapter05.circle_moments_of_nonnegative
#print axioms RudinRCA.Chapter05.representing_measure_unique
#print axioms RudinRCA.Chapter05.circleIntegral_eq_circleAverage
#print axioms RudinRCA.Chapter05.circleCoordinate_ne_interior
#print axioms RudinRCA.Chapter05.poissonDensity_pos
#print axioms RudinRCA.Chapter05.poissonDensity_eq_kernel
#print axioms RudinRCA.Chapter05.poissonDensity_moment
#print axioms RudinRCA.Chapter05.integral_poissonDensity
#print axioms RudinRCA.Chapter05.integral_poissonMeasure
#print axioms RudinRCA.Chapter05.poissonMeasure_moment
#print axioms RudinRCA.Chapter05.representing_measure_eq_poisson
#print axioms RudinRCA.Chapter05.poisson_representation
#print axioms RudinRCA.Chapter05.theorem_5_25
#print axioms RudinRCA.Chapter05.poisson_denominator_polar
#print axioms RudinRCA.Chapter05.poissonDensity_polar
#print axioms RudinRCA.Chapter05.poisson_formula_polar
#print axioms RudinRCA.Chapter05.trigMonomial_norm
#print axioms RudinRCA.Chapter05.poissonMode_norm
#print axioms RudinRCA.Chapter05.poissonMode_summable_norm
#print axioms RudinRCA.Chapter05.poissonMode_nat
#print axioms RudinRCA.Chapter05.poissonMode_neg_nat
#print axioms RudinRCA.Chapter05.poisson_geometric_identity
#print axioms RudinRCA.Chapter05.poissonMode_hasSum_apply
#print axioms RudinRCA.Chapter05.poissonKernel_hasSum
#print axioms RudinRCA.Chapter05.poissonKernel_uniform_series
#print axioms RudinRCA.Chapter05.polar_power
#print axioms RudinRCA.Chapter05.conj_polar_power
#print axioms RudinRCA.Chapter05.representing_moments_polar
#print axioms RudinRCA.Chapter05.polar_circle_difference
#print axioms RudinRCA.Chapter05.poissonMode_polar
#print axioms RudinRCA.Chapter05.poisson_kernel_series_polar
#print axioms RudinRCA.Chapter05.representing_boundary_dirac
#print axioms RudinRCA.Chapter05.poissonMeasure_finite
#print axioms RudinRCA.Chapter05.poissonMeasure_probability
