import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sets.Opens

/-! Rudin RCA Chapter 4. See INVENTORY-B.md and SCOPING-B.md. -/

/- BEGIN Chapter04Base.lean -/
section





/-!
# Rudin, Real and Complex Analysis, Chapter 4

The convention in this chapter is linearity in the first argument:
`rudinInner x y = inner ℂ y x`. Numbered statements refer to the third edition.
The source-to-declaration ledger is maintained separately; a declaration for one
part of a numbered item does not certify its remaining parts.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace RudinRCA.Chapter04

/-- 4.1: the book's inner-product convention, linear in the first variable. -/
def rudinInner {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) : ℂ := inner ℂ y x

section InnerProduct

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_conjugate_symmetry (x y : H) :
    rudinInner y x = conj (rudinInner x y) := (inner_conj_symm x y).symm

theorem inner_add_first (x y z : H) :
    rudinInner (x + y) z = rudinInner x z + rudinInner y z := inner_add_right _ _ _

theorem inner_smul_first (a : ℂ) (x y : H) :
    rudinInner (a • x) y = a * rudinInner x y := inner_smul_right _ _ _

theorem inner_self_real_nonnegative (x : H) :
    (rudinInner x x).im = 0 ∧ 0 ≤ (rudinInner x x).re :=
  ⟨inner_self_im (𝕜 := ℂ) x, inner_self_nonneg (𝕜 := ℂ) (x := x)⟩

theorem inner_zero_first (y : H) : rudinInner 0 y = 0 := inner_zero_right _

theorem inner_smul_second (a : ℂ) (x y : H) :
    rudinInner x (a • y) = conj a * rudinInner x y := inner_smul_left _ _ _

theorem inner_add_second (x y z : H) :
    rudinInner x (y + z) = rudinInner x y + rudinInner x z := inner_add_left _ _ _

/-- 4.1(f): the norm is exactly the square root specified in the book. -/
theorem norm_from_inner (x : H) : ‖x‖ = Real.sqrt (rudinInner x x).re :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) x

theorem norm_squared_inner (x : H) : (‖x‖ : ℂ) ^ 2 = rudinInner x x :=
  (inner_self_eq_norm_sq_to_K x).symm

/-- The first-slot functional appearing immediately after the defining axioms. -/
def innerFunctional (y : H) : H →ₗ[ℂ] ℂ := innerₛₗ ℂ y

theorem innerFunctional_apply (x y : H) : innerFunctional y x = rudinInner x y := rfl

/-- 4.2: no positive-definiteness assumption is needed. -/
theorem schwarz (x y : H) : ‖rudinInner x y‖ ≤ ‖x‖ * ‖y‖ := by
  simpa only [rudinInner, mul_comm] using norm_inner_le_norm (𝕜 := ℂ) y x

omit [InnerProductSpace ℂ H] in
/-- 4.3, still valid for a semidefinite inner product. -/
theorem triangle (x y : H) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y

end InnerProduct

section Metric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- 4.1(e): positive definiteness. -/
theorem inner_self_zero_iff (x : H) : rudinInner x x = 0 ↔ x = 0 := inner_self_eq_zero

omit [InnerProductSpace ℂ H] in
/-- 4.4: the induced metric is the norm of the difference. -/
theorem hilbert_distance (x y : H) : dist x y = ‖x - y‖ := dist_eq_norm x y

omit [InnerProductSpace ℂ H] in
theorem difference_triangle (x y z : H) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ :=
  norm_sub_le_norm_sub_add_norm_sub x y z

omit [InnerProductSpace ℂ H] in
/-- 4.4: completeness gives precisely convergence of every Cauchy sequence. -/
theorem hilbert_cauchy [CompleteSpace H] (u : ℕ → H) (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (𝓝 x) := cauchySeq_tendsto_of_complete hu

/-- 4.6: both inner-product functions and the norm are continuous. -/
theorem continuous_inner_and_norm (y : H) :
    Continuous (fun x : H => rudinInner x y) ∧
    Continuous (fun x : H => rudinInner y x) ∧ Continuous (fun x : H => ‖x‖) :=
  ⟨continuous_const.inner continuous_id, continuous_id.inner continuous_const, continuous_norm⟩

/-- The stronger, uniform continuity asserted in the proof of 4.6. -/
theorem inner_first_lipschitz (y : H) :
    LipschitzWith ‖y‖₊ (fun x : H => rudinInner x y) := by
  refine LipschitzWith.of_dist_le_mul fun x z => ?_
  simpa [dist_eq_norm, rudinInner, ← inner_sub_right, mul_comm] using
    norm_inner_le_norm (𝕜 := ℂ) y (x - z)

theorem inner_second_lipschitz (y : H) :
    LipschitzWith ‖y‖₊ (fun x : H => rudinInner y x) := by
  refine LipschitzWith.of_dist_le_mul fun x z => ?_
  simpa [dist_eq_norm, rudinInner, ← inner_sub_left, mul_comm] using
    norm_inner_le_norm (𝕜 := ℂ) (x - z) y

omit [InnerProductSpace ℂ H] in
theorem norm_lipschitz : LipschitzWith 1 (fun x : H => ‖x‖) := lipschitzWith_one_norm

end Metric

/-- 4.5(a): finite-dimensional complex Euclidean space is complete. -/
theorem finite_euclidean_complete (n : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin n)) :=
  inferInstance

theorem finite_euclidean_inner (n : ℕ) (x y : EuclideanSpace ℂ (Fin n)) :
    rudinInner x y = ∑ j, x j * conj (y j) := by
  simp [rudinInner, PiLp.inner_apply, RCLike.inner_apply]

/-- 4.5(b): L² is complete for an arbitrary positive measure. -/
theorem l2_complete {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    CompleteSpace (Lp ℂ 2 μ) := inferInstance

theorem l2_inner {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : Lp ℂ 2 μ) :
    rudinInner f g = ∫ x, f x * conj (g x) ∂μ := by
  simp only [rudinInner, L2.inner_def, RCLike.inner_apply]

theorem l2_product_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : Lp ℂ 2 μ) : Integrable (fun x => f x * conj (g x)) μ := by
  simpa only [RCLike.inner_apply] using L2.integrable_inner (𝕜 := ℂ) g f

/-- 4.7: the necessary nonemptiness condition is made explicit.
See the disclosure in SCOPING-B.md and the empty-set counterexample below. -/
theorem subspace_criterion (𝕜 : Type*) [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (s : Set V) :
    (∃ M : Submodule 𝕜 V, (M : Set V) = s) ↔
      s.Nonempty ∧ (∀ x ∈ s, ∀ y ∈ s, x + y ∈ s) ∧
        (∀ a : 𝕜, ∀ x ∈ s, a • x ∈ s) := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨⟨0, M.zero_mem⟩, fun _ hx _ hy => M.add_mem hx hy,
      fun a _ hx => M.smul_mem a hx⟩
  · rintro ⟨⟨x, hx⟩, hadd, hsmul⟩
    let M : Submodule 𝕜 V := {
      carrier := s
      zero_mem' := by simpa only [zero_smul] using hsmul 0 x hx
      add_mem' := fun hx hy => hadd _ hx _ hy
      smul_mem' := fun a _ hx => hsmul a _ hx }
    exact ⟨M, rfl⟩

/-- The unqualified closure criterion printed in 4.7 fails on the empty set. -/
theorem empty_set_not_subspace (𝕜 : Type*) [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] :
    (∀ x ∈ (∅ : Set V), ∀ y ∈ (∅ : Set V), x + y ∈ (∅ : Set V)) ∧
    (∀ a : 𝕜, ∀ x ∈ (∅ : Set V), a • x ∈ (∅ : Set V)) ∧
    ¬ ∃ M : Submodule 𝕜 V, (M : Set V) = ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨M, hM⟩
  have : (0 : V) ∈ (∅ : Set V) := hM ▸ M.zero_mem
  exact this

/-- 4.7: bounded complex-valued functions form a vector subspace. -/
def boundedFunctions (S : Type*) : Submodule ℂ (S → ℂ) where
  carrier := {f | ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f g ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x => (norm_add_le (f x) (g x)).trans (add_le_add (hC x) (hD x))⟩
  smul_mem' := by
    rintro a f ⟨C, hC⟩
    exact ⟨‖a‖ * C, fun x => by
      simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)⟩

/-- The bounded-by-one set in 4.7 is not a subspace on a nonempty domain.
The domain condition is necessary: on the empty domain it is the zero space. -/
theorem unit_bounded_not_subspace (S : Type*) [Nonempty S] :
    ¬ ∃ M : Submodule ℂ (S → ℂ), (M : Set (S → ℂ)) = {f | ∀ x, ‖f x‖ ≤ 1} := by
  rintro ⟨M, hM⟩
  have h1 : (fun _ : S => (1 : ℂ)) ∈ M := by
    change (fun _ : S => (1 : ℂ)) ∈ (M : Set (S → ℂ))
    rw [hM]
    simp
  have h2 := M.smul_mem (2 : ℂ) h1
  change (2 • fun _ : S => (1 : ℂ)) ∈ (M : Set (S → ℂ)) at h2
  rw [hM] at h2
  have hx := h2 (Classical.choice ‹Nonempty S›)
  norm_num at hx

/-- 4.7: the dimension classification of real subspaces of three-space.
Dimension one is a line through zero; dimension two is a plane through zero. -/
theorem real_three_subspace_dimensions (M : Submodule ℝ (Fin 3 → ℝ)) :
    Module.finrank ℝ M = 0 ∨ Module.finrank ℝ M = 1 ∨
      Module.finrank ℝ M = 2 ∨ Module.finrank ℝ M = 3 := by
  have h : Module.finrank ℝ M ≤ 3 := by simpa using Submodule.finrank_le M
  omega

theorem real_three_subspace_classification (M : Submodule ℝ (Fin 3 → ℝ)) :
    M = ⊥ ∨ Module.finrank ℝ M = 1 ∨ Module.finrank ℝ M = 2 ∨ M = ⊤ := by
  rcases real_three_subspace_dimensions M with h | h | h | h
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Submodule.eq_top_of_finrank_eq (by simpa using h))))

section Subspaces

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- 4.7: the closure of a subspace is a subspace, with exactly the closure carrier. -/
theorem closure_subspace (M : Submodule ℂ H) :
    ∃ N : Submodule ℂ H, (N : Set H) = closure (M : Set H) :=
  ⟨M.topologicalClosure, rfl⟩

end Subspaces

section Convexity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- 4.8: the book's open-segment definition agrees with `Convex`. -/
theorem convex_criterion (s : Set V) :
    Convex ℝ s ↔ ∀ x ∈ s, ∀ y ∈ s, ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) • x + t • y ∈ s := by
  rw [convex_iff_forall_pos]
  constructor
  · intro h x hx y hy t ht ht1
    exact h hx hy (sub_pos.mpr ht1) ht (sub_add_cancel 1 t)
  · intro h x hx y hy a b ha hb hab
    have ha' : a = 1 - b := by linarith
    rw [ha']
    exact h x hx y hy b hb (by linarith)

theorem subspace_convex (M : Submodule ℝ V) : Convex ℝ (M : Set V) := M.convex

theorem convex_translate (s : Set V) (hs : Convex ℝ s) (x : V) :
    Convex ℝ ((fun y => y + x) '' s) := by
  simpa only [add_comm] using hs.translate x

end Convexity

/-- The same convexity assertion for an arbitrary complex vector space, without
requiring a topology or choosing an additional real-module instance. -/
theorem complex_subspace_convex_combinations {V : Type*} [AddCommGroup V]
    [Module ℂ V] (M : Submodule ℂ V) {x y : V} (hx : x ∈ M) (hy : y ∈ M) (t : ℝ) :
    (((1 - t : ℝ) : ℂ) • x + (t : ℂ) • y) ∈ M :=
  M.add_mem (M.smul_mem _ hx) (M.smul_mem _ hy)

section Subspaces

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- 4.9: orthogonality is symmetric. -/
theorem orthogonal_symmetric (x y : H) : rudinInner x y = 0 ↔ rudinInner y x = 0 :=
  inner_eq_zero_symm

theorem orthogonal_complement_closed (M : Submodule ℂ H) :
    IsClosed (Mᗮ : Set H) := M.isClosed_orthogonal

theorem orthogonal_complement_membership (M : Submodule ℂ H) (y : H) :
    y ∈ Mᗮ ↔ ∀ x ∈ M, rudinInner x y = 0 := by
  simp only [Submodule.mem_orthogonal, rudinInner, inner_eq_zero_symm]

/-- The set of vectors perpendicular to a fixed vector is a closed subspace. -/
def vectorOrthogonal (x : H) : Submodule ℂ H :=
  (innerFunctional x).ker

theorem vectorOrthogonal_carrier (x : H) :
    (vectorOrthogonal x : Set H) = {y | rudinInner x y = 0} := by
  ext y
  simp [vectorOrthogonal, innerFunctional, rudinInner, inner_eq_zero_symm]

theorem vectorOrthogonal_closed (x : H) : IsClosed (vectorOrthogonal x : Set H) := by
  rw [vectorOrthogonal_carrier]
  exact isClosed_eq (continuous_inner_and_norm x).2.1 continuous_const

theorem orthogonal_as_intersection (M : Submodule ℂ H) :
    (Mᗮ : Set H) = ⋂ x ∈ M, (vectorOrthogonal x : Set H) := by
  ext y
  simp only [mem_iInter, vectorOrthogonal_carrier, mem_ofPred_eq]
  exact orthogonal_complement_membership M y

end Subspaces

end RudinRCA.Chapter04

/- Axiom audit: every theorem family in the basic chapter segment. -/









































end
end
/- END Chapter04Base.lean -/

/- BEGIN Chapter04Example.lean -/
section








noncomputable section
open MeasureTheory Set Filter
open scoped unitInterval Topology ComplexConjugate
namespace RudinRCA.Chapter04

/-- The inclusion of continuous interval functions into L². Its range carries
the integral norm, whereas its domain has the ordinary supremum norm. -/
abbrev intervalToL2 : C(I, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure I) :=
  ContinuousMap.toLp 2 volume ℂ

/-- Continuous functions on the interval are uniquely determined by their
Lebesgue almost-everywhere equivalence class, including endpoint values. -/
theorem intervalToL2_injective : Function.Injective intervalToL2 := by
  intro f g hfg
  have hclass : (intervalToL2 f : I → ℂ) =ᵐ[volume] g := by
    rw [hfg]
    exact g.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
  have hae : (f : I → ℂ) =ᵐ[volume] g :=
    (f.coeFn_toLp (p := 2) (𝕜 := ℂ) volume).symm.trans hclass
  let F : ℝ → ℂ := fun x => f (projIcc 0 1 zero_le_one x)
  let G : ℝ → ℂ := fun x => g (projIcc 0 1 zero_le_one x)
  have hF : Continuous F := f.continuous.comp continuous_projIcc
  have hG : Continuous G := g.continuous.comp continuous_projIcc
  have hFG : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] G := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply (ae_map_iff (μ := (volume : Measure I))
      unitInterval.measurableEmbedding_coe.measurable.aemeasurable
      (isClosed_eq hF hG).measurableSet).mpr
    filter_upwards [hae] with x hx
    simpa only [F, G, projIcc_val] using hx
  have h := Measure.eqOn_Icc_of_ae_eq volume (zero_ne_one : (0 : ℝ) ≠ 1)
    hFG hF.continuousOn hG.continuousOn
  ext x
  simpa only [F, G, projIcc_val] using h x.property

/-- Every continuous interval function corresponds to exactly one vector in
the integral-norm model, and every vector in that model comes from one. -/
def continuousIntervalIntegralEquiv : C(I, ℂ) ≃ₗ[ℂ] intervalToL2.range :=
  LinearEquiv.ofInjective intervalToL2.toLinearMap intervalToL2_injective

theorem continuousIntervalIntegralEquiv_apply (f : C(I, ℂ)) :
    (continuousIntervalIntegralEquiv f : Lp ℂ 2 (volume : Measure I)) = intervalToL2 f := rfl

/-- 4.5(c): the integral inner product on continuous interval functions,
transported along their injective inclusion into L². -/
theorem interval_integral_inner (f g : C(I, ℂ)) :
    inner ℂ (intervalToL2 g) (intervalToL2 f) = ∫ x : I, f x * conj (g x) :=
  ContinuousMap.inner_toLp volume g f

/-- The continuous functions x ↦ xⁿ have value one at the right endpoint and
their L² norms tend to zero. -/
def intervalSpike (n : ℕ) : C(I, ℂ) where
  toFun x := (x.val : ℂ) ^ n
  continuous_toFun := (Complex.continuous_ofReal.comp continuous_subtype_val).pow n

theorem intervalSpike_one (n : ℕ) : intervalSpike n 1 = 1 := by
  simp [intervalSpike]

theorem intervalSpike_L2_norm_tendsto :
    Tendsto (fun n => ‖intervalToL2 (intervalSpike n)‖) atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun n => ∫ x : I, intervalSpike n x * conj (intervalSpike n x)) atTop (𝓝 (0 : ℂ)) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure I)) (fun _ : I => (1 : ℝ))
      (F := fun n x => intervalSpike n x * conj (intervalSpike n x))
      (f := fun _ => (0 : ℂ))
      (fun n => ((intervalSpike n).continuous.mul
        (Complex.continuous_conj.comp (intervalSpike n).continuous)).aestronglyMeasurable)
      (integrable_const 1) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      filter_upwards with x
      have hx : ‖intervalSpike n x‖ ≤ 1 := by
        simpa [intervalSpike, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg x.property.1] using pow_le_one₀ x.property.1 x.property.2 (n := n)
      simpa only [norm_mul, Complex.norm_conj, one_mul] using mul_le_mul hx hx (norm_nonneg _) zero_le_one
    · have hae : ∀ᵐ x : I, x ≠ 1 := Measure.ae_ne volume 1
      filter_upwards [hae] with x hx
      have hlt : x.val < 1 := lt_of_le_of_ne x.property.2 (by
        intro he; apply hx; exact Subtype.ext he)
      have hxnorm : ‖(x.val : ℂ)‖ < 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg x.property.1] using hlt
      have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hxnorm
      simpa only [intervalSpike, ContinuousMap.coe_mk, Function.comp_apply,
        map_zero, mul_zero] using
        hp.mul (Complex.continuous_conj.tendsto 0 |>.comp hp)
  have h := Real.continuous_sqrt.tendsto 0 |>.comp (Complex.continuous_re.tendsto 0 |>.comp hlim)
  have hnorm (n : ℕ) : ‖intervalToL2 (intervalSpike n)‖ =
      Real.sqrt (∫ x : I, intervalSpike n x * conj (intervalSpike n x)).re := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    change Real.sqrt (inner ℂ (intervalToL2 (intervalSpike n))
      (intervalToL2 (intervalSpike n))).re = _
    rw [interval_integral_inner]
  simp_rw [hnorm]
  simpa only [Function.comp_def, Complex.zero_re, Real.sqrt_zero] using h

/-- 4.5(c): the space of continuous complex interval functions, with its
integral norm (the inherited norm on its L² range), is not complete.

Proof: if the range were complete, the open mapping theorem would make its
inverse to C([0,1]) bounded. The functions xⁿ contradict that bound. -/
theorem continuous_interval_integral_not_complete :
    ¬ CompleteSpace intervalToL2.range := by
  intro hc
  let : CompleteSpace intervalToL2.range := hc
  have hclosed : IsClosed (Set.range intervalToL2) :=
    (completeSpace_coe_iff_isComplete.mp hc).isClosed
  let e := intervalToL2.equivRange intervalToL2_injective hclosed
  have hbound (n : ℕ) : 1 ≤ ‖e.symm.toContinuousLinearMap‖ *
      ‖intervalToL2 (intervalSpike n)‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm
      (⟨intervalToL2 (intervalSpike n), intervalToL2.mem_range_self _⟩ : intervalToL2.range)
    have h1 : 1 ≤ ‖intervalSpike n‖ := by
      simpa only [intervalSpike_one, norm_one] using (intervalSpike n).norm_coe_le_norm 1
    apply h1.trans
    simpa [e] using h
  have ht := intervalSpike_L2_norm_tendsto.const_mul ‖e.symm.toContinuousLinearMap‖
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa only [mul_zero] using ge_of_tendsto ht (Eventually.of_forall hbound)
  exact (not_le_of_gt zero_lt_one) hbad








end RudinRCA.Chapter04
end
end
/- END Chapter04Example.lean -/

/- BEGIN Chapter04Core.lean -/
section






noncomputable section

open scoped BigOperators InnerProductSpace ComplexConjugate Topology ENNReal lp
open Set Filter

namespace RudinRCA.Chapter04

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Rudin 4.10: a nonempty closed convex set has exactly one element of minimum norm. -/
theorem theorem_4_10 [CompleteSpace H] {E : Set H} (hne : E.Nonempty)
    (hclosed : IsClosed E) (hconvex : Convex ℝ E) :
    ∃! x : H, x ∈ E ∧ ∀ y ∈ E, ‖x‖ ≤ ‖y‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨x, hx, hxmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete
    hconvex (0 : H)
  have hbound (y : H) (hy : y ∈ E) : (⨅ w : E, ‖(0 : H) - w‖) ≤ ‖y‖ := by
    simpa using (ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨y, hy⟩ : E))
  refine ⟨x, ⟨hx, fun y hy => ?_⟩, ?_⟩
  · simpa using hxmin.le.trans (hbound y hy)
  · rintro y ⟨hy, hymin⟩
    have hxy : ‖x‖ = ‖y‖ := le_antisymm (by simpa using hxmin.le.trans (hbound y hy))
      (hymin x hx)
    have hyinf : ‖(0 : H) - y‖ = ⨅ w : E, ‖(0 : H) - w‖ := by
      simpa only [zero_sub, norm_neg] using hxy.symm.trans (by simpa using hxmin)
    have hxinner := (norm_eq_iInf_iff_real_inner_le_zero hconvex hx).mp hxmin y hy
    have hyinner := (norm_eq_iInf_iff_real_inner_le_zero hconvex hy).mp hyinf x hx
    have hz : inner ℝ (x - y) (x - y) ≤ 0 := by
      simp only [zero_sub, inner_neg_left, inner_sub_left, inner_sub_right,
        real_inner_comm y x] at hxinner hyinner ⊢
      linarith
    exact (sub_eq_zero.mp (real_inner_self_nonpos.mp hz)).symm

/-- Rudin 4.11(a–d): complementary continuous linear orthogonal projections, their unique
decompositions, their minimizing properties, and the Pythagorean identity. -/
theorem theorem_4_11 [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    ∃ P Q : H →L[ℂ] H,
      (∀ x, P x ∈ M ∧ Q x ∈ Mᗮ ∧ x = P x + Q x) ∧
      (∀ x p q, p ∈ M → q ∈ Mᗮ → x = p + q → p = P x ∧ q = Q x) ∧
      (∀ x y, y ∈ M → ‖x - P x‖ ≤ ‖x - y‖) ∧
      (∀ x y, y ∈ Mᗮ → ‖x - Q x‖ ≤ ‖x - y‖) ∧
      (∀ x, ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  refine ⟨M.starProjection, Mᗮ.starProjection, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨M.starProjection_apply_mem x, Mᗮ.starProjection_apply_mem x,
      (Submodule.starProjection_add_starProjection_orthogonal (K := M) x).symm⟩
  · intro x p q hp hq hx
    have hP := Submodule.eq_starProjection_of_mem_orthogonal' (K := M) hp hq hx
    refine ⟨hP.symm, ?_⟩
    rw [Submodule.starProjection_orthogonal_val (K := M), hP, hx, add_sub_cancel_left]
  · intro x y hy
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨y, hy⟩ : M)
  · intro x y hy
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨y, hy⟩ : Mᗮ)
  · exact fun x => Submodule.norm_sq_eq_add_norm_sq_starProjection x M

/-- The corollary printed after Rudin 4.11. -/
theorem corollary_4_11 [CompleteSpace H] (M : Submodule ℂ H)
    (hM : IsClosed (M : Set H)) (hne : M ≠ ⊤) : ∃ y : H, y ≠ 0 ∧ y ∈ Mᗮ := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  have : Mᗮ ≠ ⊥ := mt (Submodule.orthogonal_eq_bot_iff (K := M)).mp hne
  obtain ⟨y, hy, hne⟩ := (Submodule.ne_bot_iff Mᗮ).mp this
  exact ⟨y, hne, hy⟩

/-- The nearest point in each closed subspace in Rudin 4.11(b) is unique. Applying this to
`Mᗮ` gives the identical assertion for the complementary projection. -/
theorem theorem_4_11_nearest_unique [CompleteSpace H] (M : Submodule ℂ H)
    (hM : IsClosed (M : Set H)) (x : H) :
    ∃! p : H, p ∈ M ∧ ∀ y ∈ M, ‖x - p‖ ≤ ‖x - y‖ := by
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  have hp : ∀ y ∈ M, ‖x - M.starProjection x‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨y, hy⟩ : M)
  refine ⟨M.starProjection x, ⟨M.starProjection_apply_mem x, hp⟩, ?_⟩
  rintro p ⟨hpmem, hpmin⟩
  have heq : ‖x - p‖ = ‖x - M.starProjection x‖ :=
    le_antisymm (hpmin _ (M.starProjection_apply_mem x)) (hp p hpmem)
  have hinner := (M.norm_eq_iInf_iff_inner_eq_zero hpmem).mp
    (heq.trans (Submodule.starProjection_minimal x))
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hpmem hinner).symm

/-- Rudin 4.12. The order `inner ℂ y x` implements Rudin's convention, linear in `x`. -/
theorem theorem_4_12 [CompleteSpace H] (L : H →L[ℂ] ℂ) :
    ∃! y : H, ∀ x, L x = inner ℂ y x := by
  refine ⟨(InnerProductSpace.toDual ℂ H).symm L, ?_, ?_⟩
  · intro x
    exact InnerProductSpace.toDual_symm_apply.symm
  · intro y hy
    apply ext_inner_right ℂ
    intro x
    exact (hy x).symm.trans InnerProductSpace.toDual_symm_apply.symm

/-- Rudin 4.13: finite linear combinations of an indexed family. -/
def finiteLinearCombination {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (u : ι → V) (F : Finset ι) (c : ι → ℂ) : V :=
  ∑ i ∈ F, c i • u i

/-- Rudin's Fourier coefficient `(x,uᵢ)`, with the book's first-variable-linear convention. -/
def fourierCoefficient {ι : Type*} (u : ι → H) (x : H) (i : ι) : ℂ := inner ℂ (u i) x

/-- Rudin 4.13: the span is the least linear subspace containing a set. -/
theorem span_least {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set V) (M : Submodule ℂ V) :
    Submodule.span ℂ S ≤ M ↔ S ⊆ M := Submodule.span_le

/-- Rudin 4.13: membership in the span is precisely being a finite linear combination. -/
theorem span_iff_finite_linear_combination {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set V) (x : V) :
    x ∈ Submodule.span ℂ S ↔
      ∃ c : S →₀ ℂ, Finsupp.linearCombination ℂ ((↑) : S → V) c = x :=
  Finsupp.mem_span_iff_linearCombination ℂ S x

/-- The independence clause of Rudin 4.13 in finitely supported notation. -/
theorem independent_iff_finite_combinations {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (u : ι → V) :
    LinearIndependent ℂ u ↔ ∀ c : ι →₀ ℂ, Finsupp.linearCombination ℂ u c = 0 → c = 0 := by
  rw [linearIndependent_iff]

/-- The orthogonality relation in Rudin 4.13(1). -/
theorem orthonormal_iff_rudin {ι : Type*} [DecidableEq ι] (u : ι → H) :
    Orthonormal ℂ u ↔ ∀ i j, inner ℂ (u j) (u i) = if i = j then 1 else 0 := by
  rw [orthonormal_iff_ite]
  constructor <;> intro h i j <;> simpa [eq_comm] using h j i

/-- Rudin 4.14(a), membership of the prescribed finite Fourier sum in its span. -/
theorem finiteLinearCombination_mem {ι : Type*} (u : ι → H) (F : Finset ι) (c : ι → ℂ) :
    finiteLinearCombination u F c ∈ Submodule.span ℂ (u '' (F : Set ι)) := by
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- Rudin 4.14(a), coefficients everywhere, including outside the finite set. -/
theorem theorem_4_14a_coefficients {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u)
    (F : Finset ι) (c : ι → ℂ) (hc : ∀ i ∉ F, c i = 0) :
    ∀ i, fourierCoefficient u (finiteLinearCombination u F c) i = c i := by
  classical
  intro i
  by_cases hi : i ∈ F
  · exact hu.inner_right_sum c hi
  · simp only [fourierCoefficient, finiteLinearCombination, inner_sum, inner_smul_right]
    rw [hc i hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu.inner_eq_zero (ne_of_mem_of_not_mem hj hi).symm, mul_zero]

/-- Rudin 4.14(a), the exact finite Pythagorean formula. -/
theorem theorem_4_14a_norm {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u)
    (F : Finset ι) (c : ι → ℂ) :
    ‖finiteLinearCombination u F c‖ ^ 2 = ∑ i ∈ F, ‖c i‖ ^ 2 := by
  simpa only [finiteLinearCombination, LinearIsometry.toSpanSingleton_apply] using
    hu.orthogonalFamily.norm_sum c F

/-- Rudin 4.14(b), Bessel's finite inequality. -/
theorem theorem_4_14b_bessel {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u)
    (F : Finset ι) (x : H) : ∑ i ∈ F, ‖fourierCoefficient u x i‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hu.sum_inner_products_le x

/-- The residual of a finite Fourier sum is orthogonal to its entire finite span. -/
theorem finiteFourierSum_residual_orthogonal {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) (F : Finset ι) (x : H) :
    x - finiteLinearCombination u F (fourierCoefficient u x) ∈
      (Submodule.span ℂ (u '' (F : Set ι)))ᗮ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [inner_sub_right]
      exact sub_eq_zero.mpr (hu.inner_right_sum (fourierCoefficient u x) hi).symm
  | zero => simp
  | add y z hy hz hy0 hz0 => simp [inner_add_left, hy0, hz0]
  | smul a y hy hy0 => simp [inner_smul_left, hy0]

/-- Rudin 4.14(b), the Pythagorean remainder formula (6). -/
theorem theorem_4_14b_remainder {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u)
    (F : Finset ι) (x s : H) (hs : s ∈ Submodule.span ℂ (u '' (F : Set ι))) :
    ‖x - s‖ ^ 2 = ‖x - finiteLinearCombination u F (fourierCoefficient u x)‖ ^ 2 +
      ‖finiteLinearCombination u F (fourierCoefficient u x) - s‖ ^ 2 := by
  have horth := finiteFourierSum_residual_orthogonal hu F x
  have hm := (Submodule.span ℂ (u '' (F : Set ι))).sub_mem
    (finiteLinearCombination_mem u F (fourierCoefficient u x)) hs
  have heq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (x - finiteLinearCombination u F (fourierCoefficient u x))
    (finiteLinearCombination u F (fourierCoefficient u x) - s)
    (Submodule.inner_left_of_mem_orthogonal hm horth)
  simpa only [sub_add_sub_cancel, pow_two] using heq

/-- Rudin 4.14(b), strict best approximation unless the competitor is the Fourier sum itself. -/
theorem theorem_4_14b_best {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u)
    (F : Finset ι) (x s : H) (hs : s ∈ Submodule.span ℂ (u '' (F : Set ι)))
    (hne : s ≠ finiteLinearCombination u F (fourierCoefficient u x)) :
    ‖x - finiteLinearCombination u F (fourierCoefficient u x)‖ < ‖x - s‖ := by
  have heq := theorem_4_14b_remainder hu F x s hs
  have hp : 0 < ‖finiteLinearCombination u F (fourierCoefficient u x) - s‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  nlinarith [norm_nonneg (x - finiteLinearCombination u F (fourierCoefficient u x)),
    norm_nonneg (x - s)]

/-- Rudin 4.15: an arbitrary nonnegative sum is the supremum of its finite subsums. -/
theorem theorem_4_15_nonnegative_sum {ι : Type*} (f : ι → ℝ≥0∞) :
    ∑' i, f i = ⨆ F : Finset ι, ∑ i ∈ F, f i := ENNReal.tsum_eq_iSup_sum

/-- Rudin 4.15: the same sum is integration against counting measure. -/
theorem theorem_4_15_counting_integral {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (f : ι → ℝ≥0∞) :
    ∫⁻ i, f i ∂MeasureTheory.Measure.count = ∑' i, f i :=
  MeasureTheory.lintegral_count f

/-- Rudin 4.15: membership of a scalar family in `ℓ²` is square summability. -/
theorem theorem_4_15_membership {ι : Type*} (f : ι → ℂ) :
    Memℓp f 2 ↔ Summable (fun i => ‖f i‖ ^ 2) := by
  simp [Memℓp]

/-- Rudin 4.15(2), explicitly using the possibly infinite nonnegative sum from 4.15(1). -/
theorem theorem_4_15_membership_sum {ι : Type*} (f : ι → ℂ) :
    Memℓp f 2 ↔ (∑' i, (‖f i‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  rw [theorem_4_15_membership, lt_top_iff_ne_top]
  simp only [← ENNReal.coe_pow, ENNReal.tsum_coe_ne_top_iff_summable_coe,
    NNReal.coe_pow, coe_nnnorm]

/-- Rudin 4.15: `ℓ²` is complete; its inner-product structure is the canonical `lp` instance. -/
theorem theorem_4_15_complete {ι : Type*} : CompleteSpace ℓ²(ι, ℂ) := inferInstance

/-- Rudin 4.15: the Hilbert-space norm on `ℓ²`. -/
theorem theorem_4_15_norm {ι : Type*} (f : ℓ²(ι, ℂ)) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by simp) f

/-- Rudin 4.15: the inner-product series exists and agrees with the Hilbert inner product,
in Rudin's first-variable-linear convention. -/
theorem theorem_4_15_inner {ι : Type*} (f g : ℓ²(ι, ℂ)) :
    Summable (fun i => ‖f i * conj (g i)‖) ∧
      Summable (fun i => f i * conj (g i)) ∧
      inner ℂ g f = ∑' i, f i * conj (g i) := by
  have hs : Summable (fun i => f i * conj (g i)) := by
    simpa only [RCLike.inner_apply] using lp.summable_inner (𝕜 := ℂ) g f
  exact ⟨hs.norm, hs, by
    simpa only [RCLike.inner_apply] using lp.inner_eq_tsum (𝕜 := ℂ) g f⟩

/-- Rudin 4.15: every square-summable family has at most countable support. -/
theorem theorem_4_15_countable_support {ι : Type*} (f : ℓ²(ι, ℂ)) :
    (Function.support f).Countable := by
  have hs : Summable (fun i => ‖f i‖ ^ 2) := by
    simpa using (lp.memℓp f).summable (by simp : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Function.support] using hs.countable_support

/-- Rudin 4.15: the finitely supported families are dense in `ℓ²`. -/
theorem theorem_4_15_finite_dense {ι : Type*} :
    Dense {f : ℓ²(ι, ℂ) | ∃ F : Finset ι, ∀ i ∉ F, f i = 0} := by
  classical
  intro f
  apply mem_closure_of_tendsto (lp.hasSum_single (by simp) f)
  apply Filter.Eventually.of_forall
  intro F
  refine ⟨F, ?_⟩
  intro i hi
  simp only [lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun j hj => by
    simp [lp.single_apply, ne_of_mem_of_not_mem hj hi]

/-- Rudin 4.16: continuity extends a dense isometry, and completeness makes its dense range all
of the target. No completeness of the target is assumed. -/
theorem theorem_4_16 {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X]
    (f : X → Y) (hf : Continuous f) (X₀ : Set X) (hdense : Dense X₀)
    (hiso : ∀ x ∈ X₀, ∀ y ∈ X₀, dist (f x) (f y) = dist x y)
    (hrange : Dense (f '' X₀)) : Isometry f ∧ Function.Surjective f := by
  have hi : Isometry f := Isometry.of_dist_eq fun x y =>
    eqOn_closure₂ hiso ((hf.comp continuous_fst).dist (hf.comp continuous_snd))
      (continuous_fst.dist continuous_snd) x (hdense x) y (hdense y)
  refine ⟨hi, Set.range_eq_univ.mp ?_⟩
  have hd : Dense (Set.range f) := hrange.mono (Set.image_subset_range f X₀)
  exact hi.isClosedEmbedding.isClosed_range.closure_eq.symm.trans hd.closure_eq

/-- Synthesis of an arbitrary square-summable family, used in Rudin 4.17. -/
def fourierSynthesis [CompleteSpace H] {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u) :
    ℓ²(ι, ℂ) →ₗᵢ[ℂ] H := hu.orthogonalFamily.linearIsometry

/-- The continuous linear Fourier coefficient map of Rudin 4.17. -/
def fourierAnalysis [CompleteSpace H] {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u) :
    H →L[ℂ] ℓ²(ι, ℂ) := (fourierSynthesis hu).toContinuousLinearMap.adjoint

theorem fourierAnalysis_coefficient [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) (x : H) (i : ι) :
    fourierAnalysis hu x i = fourierCoefficient u x i := by
  classical
  have h := (fourierSynthesis hu).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 i (1 : ℂ)) x
  simpa [fourierAnalysis, fourierSynthesis, fourierCoefficient, lp.inner_single_left,
    LinearIsometry.toSpanSingleton_apply] using h

theorem fourierAnalysis_synthesis [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) (f : ℓ²(ι, ℂ)) :
    fourierAnalysis hu (fourierSynthesis hu f) = f := by
  apply ext_inner_right ℂ
  intro g
  exact ((fourierSynthesis hu).toContinuousLinearMap.adjoint_inner_left g
    (fourierSynthesis hu f)).trans ((fourierSynthesis hu).inner_map_map f g)

theorem fourierSynthesis_range [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) :
    (fourierSynthesis hu).toLinearMap.range =
      (Submodule.span ℂ (Set.range u)).topologicalClosure := by
  simpa only [fourierSynthesis, LinearIsometry.coe_toSpanSingleton,
    LinearMap.range_toSpanSingleton, ← Submodule.span_range_eq_iSup] using
    hu.orthogonalFamily.range_linearIsometry

/-- Rudin 4.17, including onto-ness of the coefficient map and onto-ness and isometry of its
restriction to the closed linear span. -/
theorem theorem_4_17 [CompleteSpace H] {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u) :
    (∀ x, Summable (fun i => ‖fourierCoefficient u x i‖ ^ 2) ∧
      ∑' i, ‖fourierCoefficient u x i‖ ^ 2 ≤ ‖x‖ ^ 2) ∧
    (∀ x i, fourierAnalysis hu x i = fourierCoefficient u x i) ∧
    Function.Surjective (fourierAnalysis hu) ∧
    (∀ x ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure,
      ∀ y ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure,
        dist (fourierAnalysis hu x) (fourierAnalysis hu y) = dist x y) ∧
    (∀ f : ℓ²(ι, ℂ), ∃ x ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure,
      fourierAnalysis hu x = f) := by
  refine ⟨fun x => ⟨hu.inner_products_summable x, hu.tsum_inner_products_le x⟩,
    fourierAnalysis_coefficient hu, ?_, ?_, ?_⟩
  · exact fun f => ⟨fourierSynthesis hu f, fourierAnalysis_synthesis hu f⟩
  · intro x hx y hy
    rw [← fourierSynthesis_range hu] at hx hy
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    change dist (fourierAnalysis hu (fourierSynthesis hu f))
      (fourierAnalysis hu (fourierSynthesis hu g)) =
        dist (fourierSynthesis hu f) (fourierSynthesis hu g)
    rw [fourierAnalysis_synthesis, fourierAnalysis_synthesis]
    exact ((fourierSynthesis hu).isometry.dist_eq f g).symm
  · intro f
    refine ⟨fourierSynthesis hu f, ?_, fourierAnalysis_synthesis hu f⟩
    rw [← fourierSynthesis_range hu]
    exact ⟨f, rfl⟩

/-- The maximality condition in Rudin 4.18(i), stated for the actual set of vectors. -/
def MaximalOrthonormalSet (S : Set H) : Prop :=
  ∀ T ⊇ S, Orthonormal ℂ ((↑) : T → H) → T = S

/-- Vanishing of all Fourier coefficients detects zero precisely when the linear span is dense. -/
theorem dense_span_of_fourier_detection [CompleteSpace H] {ι : Type*} {u : ι → H}
    (h : ∀ x : H, (∀ i, fourierCoefficient u x i = 0) → x = 0) :
    (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm
  · intro x hx
    apply h x
    intro i
    exact hx (u i) (Submodule.subset_span (Set.mem_range_self i))
  · exact bot_le

/-- Rudin 4.18(i) iff (ii). -/
theorem theorem_4_18_maximal_iff_dense [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) :
    MaximalOrthonormalSet (Set.range u) ↔
      (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ := by
  exact (maximal_orthonormal_iff_orthogonalComplement_eq_bot hu.toSubtypeRange).trans
    Submodule.topologicalClosure_eq_top_iff.symm

/-- Rudin 4.18(ii) iff (iii), the norm identity for all vectors. -/
theorem theorem_4_18_dense_iff_norm [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) :
    (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ ↔
      ∀ x : H, ∑' i, ‖fourierCoefficient u x i‖ ^ 2 = ‖x‖ ^ 2 := by
  constructor
  · intro hd x
    let b : HilbertBasis ι ℂ H := HilbertBasis.mk hu hd.ge
    have hc : ∀ i, b.repr x i = fourierCoefficient u x i := by
      intro i
      simpa only [b, HilbertBasis.coe_mk, fourierCoefficient] using b.repr_apply_apply x i
    rw [← b.repr.norm_map x, theorem_4_15_norm]
    simp only [hc]
  · intro hn
    apply dense_span_of_fourier_detection
    intro x hx
    have hz : ‖x‖ ^ 2 = 0 := by simpa [hx] using (hn x).symm
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Rudin 4.18(ii) iff (iv), Parseval's identity in the book's coefficient convention. -/
theorem theorem_4_18_dense_iff_parseval [CompleteSpace H] {ι : Type*} {u : ι → H}
    (hu : Orthonormal ℂ u) :
    (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ ↔
      ∀ x y : H,
        ∑' i, fourierCoefficient u x i * conj (fourierCoefficient u y i) = inner ℂ y x := by
  constructor
  · intro hd x y
    let b : HilbertBasis ι ℂ H := HilbertBasis.mk hu hd.ge
    simpa only [fourierCoefficient, inner_conj_symm, mul_comm, b,
      HilbertBasis.coe_mk] using b.tsum_inner_mul_inner y x
  · intro hp
    apply dense_span_of_fourier_detection
    intro x hx
    have hz : inner ℂ x x = 0 := by simpa [hx] using (hp x x).symm
    exact inner_self_eq_zero.mp hz

/-- Rudin 4.18: all four printed conditions are equivalent, with actual set maximality,
density of the finite span, the norm identity, and Parseval's identity. -/
theorem theorem_4_18 [CompleteSpace H] {ι : Type*} {u : ι → H} (hu : Orthonormal ℂ u) :
    (MaximalOrthonormalSet (Set.range u) ↔
      (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤) ∧
    ((Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ ↔
      ∀ x : H, ∑' i, ‖fourierCoefficient u x i‖ ^ 2 = ‖x‖ ^ 2) ∧
    ((Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ ↔
      ∀ x y : H,
        ∑' i, fourierCoefficient u x i * conj (fourierCoefficient u y i) = inner ℂ y x) :=
  ⟨theorem_4_18_maximal_iff_dense hu, theorem_4_18_dense_iff_norm hu,
    theorem_4_18_dense_iff_parseval hu⟩

end RudinRCA.Chapter04




































end
end
/- END Chapter04Core.lean -/

/- BEGIN Chapter04Order.lean -/
section





/-!
# Rudin RCA, Chapter 4, nodes 4.19–4.22

The assertion in 4.20 that all positive-radius origin-centered open discs constitute
a maximal chain of all open subsets of the plane is false: the whole plane is
comparable with every finite-radius disc and belongs to none. The empty open set
also gives a counterexample under the positive-radius convention. Both are proved
below. No corrected maximality assertion is silently substituted.
-/

open Set
open scoped InnerProductSpace ENNReal lp

namespace RudinRCA.Chapter04

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- 4.19: the coefficient map associated to a Hilbert basis is an isometric linear
bijection, and its coordinates are the book's first-linear inner products. -/
theorem hilbertBasis_isomorphism {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ∃ e : H ≃ₗᵢ[ℂ] ℓ²(ι, ℂ), ∀ x i, e x i = inner ℂ (b i) x :=
  ⟨b.repr, b.repr_apply_apply⟩

/-- 4.19 directly in terms of a maximal orthonormal family, with its original
index set and Fourier coefficients. -/
theorem maximal_orthonormal_coefficient_isomorphism [CompleteSpace H]
    {ι : Type*} {v : ι → H} (hv : Orthonormal ℂ v)
    (hmax : ∀ s ⊇ Set.range v, Orthonormal ℂ (Subtype.val : s → H) → s = Set.range v) :
    ∃ e : H ≃ₗᵢ[ℂ] ℓ²(ι, ℂ), ∀ x i, e x i = inner ℂ (v i) x := by
  have hbot : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ :=
    (maximal_orthonormal_iff_orthogonalComplement_eq_bot hv.toSubtypeRange).mp hmax
  let b : HilbertBasis ι ℂ H := HilbertBasis.mkOfOrthogonalEqBot hv hbot
  refine ⟨b.repr, fun x i => ?_⟩
  rw [b.repr_apply_apply]
  have hb : (b : ι → H) = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hbot
  rw [hb]

/-- A complex linear isometric equivalence preserves the book's inner product. -/
theorem hilbert_isomorphism_preserves_inner {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (e : H ≃ₗᵢ[ℂ] K) (x y : H) :
    inner ℂ (e y) (e x) = inner ℂ y x :=
  e.inner_map_map y x

/-- 4.19: every complete complex inner product space is isomorphic to an ℓ² space.
The empty index set also covers the trivial space. -/
theorem hilbertSpace_exists_l2_isomorphism [CompleteSpace H] :
    ∃ s : Set H, Nonempty (H ≃ₗᵢ[ℂ] ℓ²(s, ℂ)) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨s, ⟨b.repr⟩⟩

/-- Square-summable coefficient families have countable support, even over arbitrary
index sets. This is also the support assertion in 4.15. -/
theorem hilbertBasis_coefficients_countable {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    {i | b.repr x i ≠ 0}.Countable := by
  have hs := (lp.memℓp (b.repr x)).summable (by simp : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Function.support, Real.rpow_two] using hs.countable_support

universe u

/-- The cardinality of any Hilbert basis is bounded by that of any other infinite
Hilbert basis. Each vector has countably many nonzero coefficients, and symmetry
of orthogonality makes those supports cover the first index set. -/
theorem hilbertBasis_card_le_infinite {ι κ : Type u} [Infinite κ]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) :
    Cardinal.mk ι ≤ Cardinal.mk κ := by
  classical
  let S : κ → Set ι := fun j => {i | b.repr (c j) i ≠ 0}
  have hcount : ∀ j, (S j).Countable := fun j =>
    hilbertBasis_coefficients_countable b (c j)
  have hcover : (⋃ j, S j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    simp only [Set.mem_iUnion, S, Set.mem_ofPred_eq]
    by_contra! hz
    have he : c.repr (b i) = 0 := by
      ext j
      simp only [HilbertBasis.repr_apply_apply, lp.coeFn_zero, Pi.zero_apply]
      exact inner_eq_zero_symm.mpr (by
        simpa only [HilbertBasis.repr_apply_apply] using hz j)
    have hi : b i = 0 := c.repr.injective (by simpa using he)
    have hn := b.orthonormal.1 i
    simp [hi] at hn
  calc
    Cardinal.mk ι = Cardinal.mk (⋃ j, S j) := by rw [hcover, Cardinal.mk_univ]
    _ ≤ Cardinal.mk κ * (⨆ j, Cardinal.mk (S j)) := Cardinal.mk_iUnion_le S
    _ ≤ Cardinal.mk κ * Cardinal.aleph0 :=
      mul_le_mul' le_rfl (ciSup_le' fun j =>
        Cardinal.le_aleph0_iff_set_countable.mpr (hcount j))
    _ = Cardinal.mk κ := Cardinal.mk_mul_aleph0_eq

/-- Hilbert bases have the same cardinality. The finite case is ordinary algebraic
basis cardinality; the infinite case uses the countable support argument. -/
theorem hilbertBasis_card_eq {ι κ : Type u}
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H) :
    Cardinal.mk ι = Cardinal.mk κ := by
  classical
  have hle : ∀ {α β : Type u}, HilbertBasis α ℂ H → HilbertBasis β ℂ H →
      Cardinal.mk α ≤ Cardinal.mk β := by
    intro α β b' c'
    cases fintypeOrInfinite β
    · exact linearIndependent_le_basis c'.toOrthonormalBasis.toBasis b'
        b'.orthonormal.linearIndependent
    · exact hilbertBasis_card_le_infinite b' c'
  exact le_antisymm (hle b c) (hle c b)

/-- An equivalence of index sets gives a Hilbert isomorphism of the corresponding
ℓ² spaces, including empty and finite index sets. -/
theorem l2_isomorphism_of_equiv {ι κ : Type u} (e : ι ≃ κ) :
    Nonempty (ℓ²(ι, ℂ) ≃ₗᵢ[ℂ] ℓ²(κ, ℂ)) := by
  classical
  let b : HilbertBasis ι ℂ ℓ²(ι, ℂ) := default
  have hrange : Set.range (b ∘ e.symm) = Set.range b := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩
  let c : HilbertBasis κ ℂ ℓ²(ι, ℂ) :=
    HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
      rw [hrange, b.dense_span])
  exact ⟨c.repr⟩

/-- 4.19's printed classification assertion, whose proof Rudin omits:
ℓ² spaces are Hilbert-isomorphic exactly when the index cardinals coincide. -/
theorem l2_isomorphism_iff_card_eq {ι κ : Type u} :
    Nonempty (ℓ²(ι, ℂ) ≃ₗᵢ[ℂ] ℓ²(κ, ℂ)) ↔ Cardinal.mk ι = Cardinal.mk κ := by
  constructor
  · rintro ⟨e⟩
    exact hilbertBasis_card_eq (default : HilbertBasis ι ℂ ℓ²(ι, ℂ))
      (HilbertBasis.ofRepr e)
  · intro h
    exact l2_isomorphism_of_equiv (Classical.choice (Cardinal.eq.mp h))

/-- 4.20: the standard three partial-order laws. -/
theorem partialOrder_laws {α : Type*} [PartialOrder α] (a b c : α) :
    (a ≤ b → b ≤ c → a ≤ c) ∧ a ≤ a ∧ (a ≤ b → b ≤ a → a = b) :=
  ⟨le_trans, le_rfl, le_antisymm⟩

/-- The open origin-centered discs used in Rudin's 4.20 example. -/
def originDiscChain : Set (TopologicalSpace.Opens ℂ) :=
  {U | ∃ r : ℝ, 0 < r ∧ U = ⟨Metric.ball 0 r, Metric.isOpen_ball⟩}

/-- 4.20's disc family really is a chain, so the error is specifically maximality. -/
theorem originDiscChain_isChain : IsChain (· ≤ ·) originDiscChain := by
  rintro U ⟨r, hr, rfl⟩ V ⟨s, hs, rfl⟩ _
  rcases le_total r s with h | h
  · exact Or.inl (Metric.ball_subset_ball h)
  · exact Or.inr (Metric.ball_subset_ball h)

/-- Counterexample to the maximality assertion in printed 4.20: the empty open
set is not any positive-radius disc. -/
theorem empty_not_mem_originDiscChain :
    (⊥ : TopologicalSpace.Opens ℂ) ∉ originDiscChain := by
  rintro ⟨r, hr, h⟩
  have hz : (0 : ℂ) ∈ (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ) := by
    simpa using hr
  rw [← h] at hz
  exact hz

/-- The whole plane is also outside every finite-radius origin disc. This gives
another endpoint that can be adjoined to the printed chain. -/
theorem univ_not_mem_originDiscChain :
    (⊤ : TopologicalSpace.Opens ℂ) ∉ originDiscChain := by
  rintro ⟨r, hr, h⟩
  have hz : (r : ℂ) ∈ (⊤ : TopologicalSpace.Opens ℂ) := trivial
  rw [h] at hz
  have hlt : ‖(r : ℂ)‖ < r := by
    change dist (r : ℂ) 0 < r at hz
    simpa only [dist_zero_right] using hz
  simp [Complex.norm_real, abs_of_pos hr] at hlt

/-- 4.20, disclosed counterexample: the printed family is not a maximal chain
among all open subsets of the plane. -/
theorem originDiscChain_not_maximal : ¬ IsMaxChain (· ≤ ·) originDiscChain := by
  intro h
  exact univ_not_mem_originDiscChain h.top_mem

/-- A concrete proper chain extension witnesses the 4.20 correction. -/
theorem originDiscChain_extend_by_empty :
    IsChain (· ≤ ·) (insert (⊥ : TopologicalSpace.Opens ℂ) originDiscChain) ∧
    originDiscChain ⊂ insert ⊥ originDiscChain := by
  refine ⟨originDiscChain_isChain.insert (fun _ _ _ => Or.inl bot_le), ?_⟩
  exact Set.ssubset_insert empty_not_mem_originDiscChain

/-- The whole plane gives a proper chain extension independently of any
convention about allowing zero-radius discs. -/
theorem originDiscChain_extend_by_univ :
    IsChain (· ≤ ·) (insert (⊤ : TopologicalSpace.Opens ℂ) originDiscChain) ∧
    originDiscChain ⊂ insert ⊤ originDiscChain := by
  refine ⟨originDiscChain_isChain.insert (fun _ _ _ => Or.inr le_top), ?_⟩
  exact Set.ssubset_insert univ_not_mem_originDiscChain

/-- 4.21: Hausdorff maximality, with the stronger extension form. -/
theorem hausdorff_maximality {α : Type*} [PartialOrder α] {c : Set α}
    (hc : IsChain (· ≤ ·) c) :
    ∃ M : Set α, IsMaxChain (· ≤ ·) M ∧ c ⊆ M :=
  hc.exists_maxChain

/-- 4.21's stated nonempty-poset conclusion. -/
theorem exists_maximal_chain {α : Type*} [PartialOrder α] [Nonempty α] :
    ∃ M : Set α, IsMaxChain (· ≤ ·) M ∧ M.Nonempty := by
  obtain ⟨M, hM, _⟩ := (IsChain.empty (r := fun a b : α => a ≤ b)).exists_maxChain
  exact ⟨M, hM, hM.nonempty_iff.mp inferInstance⟩

/-- 4.21: a nontrivial Hilbert space has a unit vector. -/
theorem exists_unit_vector [Nontrivial H] : ∃ u : H, ‖u‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, ?_⟩
  simp [norm_smul, norm_ne_zero_iff.mpr hx]

/-- 4.22: every specified orthonormal set extends to a maximal one. -/
theorem orthonormal_set_extension {s : Set H}
    (hs : Orthonormal ℂ (Subtype.val : s → H)) :
    ∃ w ⊇ s, Orthonormal ℂ (Subtype.val : w → H) ∧
      ∀ u ⊇ w, Orthonormal ℂ (Subtype.val : u → H) → u = w :=
  exists_maximal_orthonormal hs

end RudinRCA.Chapter04


























end
/- END Chapter04Order.lean -/

/- BEGIN Chapter04Fourier.lean -/
section






/-! Fourier-theoretic claims in Rudin RCA §§4.23–4.26.
The additive circle is identified explicitly with the geometric unit circle.
All Lp spaces below use Haar measure normalized to mass one, as in Rudin. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Real ComplexConjugate Topology lp

namespace RudinRCA.Chapter04

/-- 4.23: the circle parameter space with period `2π`. -/
abbrev FourierCircle := AddCircle (2 * Real.pi)

instance fourierPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Identification with the complex unit circle. -/
def fourierCircleHomeomorphism : FourierCircle ≃ₜ Circle := AddCircle.homeomorphCircle'

/-- The parameterization is precisely `exp(it)`. -/
theorem fourierCircleHomeomorphism_apply (t : ℝ) :
    (fourierCircleHomeomorphism (t : FourierCircle) : ℂ) = Complex.exp (t * Complex.I) := by
  rfl

/-- Every function on the circle pulls back to a `2π`-periodic function. -/
theorem circleFunction_periodic (f : FourierCircle → ℂ) :
    Function.Periodic (fun t : ℝ => f (t : FourierCircle)) (2 * Real.pi) := by
  intro t
  change f ((t + 2 * Real.pi : ℝ) : FourierCircle) = f (t : FourierCircle)
  rw [AddCircle.coe_add_period]

/-- Conversely, periodic functions descend to the circle. -/
theorem periodicFunction_descends (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) :
    ∃ F : FourierCircle → ℂ, ∀ t : ℝ, F (t : FourierCircle) = f t :=
  ⟨hf.lift, fun t => hf.lift_coe t⟩

/-- Continuous functions on the circle pull back to continuous periodic functions. -/
theorem continuous_circleFunction (f : C(FourierCircle, ℂ)) :
    Continuous (fun t : ℝ => f (t : FourierCircle)) :=
  f.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))

/-- Conversely a continuous periodic function defines a continuous function on the circle. -/
theorem continuous_periodicFunction_descends (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    ∃ F : C(FourierCircle, ℂ), ∀ t : ℝ, F (t : FourierCircle) = f t :=
  ⟨⟨hp.lift, hf.quotient_liftOn' _⟩, fun t => hp.lift_coe t⟩

/-- The probability measure used in all circle norms and integrals. -/
abbrev circleMeasure : Measure FourierCircle := AddCircle.haarAddCircle

/-- Rudin's circle `Lᵖ` space consists of almost-everywhere equivalence classes. -/
abbrev CircleLp (p : ℝ≥0∞) := Lp ℂ p circleMeasure

abbrev CircleL2 := CircleLp 2

/-- Integrals against the normalized circle measure are the normalized interval integrals. -/
theorem circleIntegral_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : FourierCircle → E) :
    (∫ t, f t ∂circleMeasure) = (1 / (2 * Real.pi) : ℝ) •
      ∫ t in -Real.pi..Real.pi, f (t : FourierCircle) := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi) f]
  congr 2 <;> ring

/-- 4.23(2): the normalized `Lᵖ` norm, for finite nonzero `p`. -/
theorem circleLp_norm_formula (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (f : CircleLp p) :
    ‖f‖ = ((1 / (2 * Real.pi)) *
      ∫ t in -Real.pi..Real.pi, ‖f (t : FourierCircle)‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp0 hptop,
    ENNReal.toReal_ofReal (by positivity), circleIntegral_interval]
  rfl

/-- At exponent infinity the norm is the essential supremum. -/
theorem circleLp_infty_norm_formula (f : CircleLp ∞) :
    ‖f‖ = (essSup (fun t => ‖f t‖ₑ) circleMeasure).toReal := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  rfl

/-- 4.23(3): the continuous-function norm is the supremum norm. -/
theorem circleContinuous_norm_formula (f : C(FourierCircle, ℂ)) :
    ‖f‖ = ⨆ t : FourierCircle, ‖f t‖ := f.norm_eq_iSup_norm

/-- The constant function one has norm one for every nonzero `p`, including infinity. -/
theorem circleLp_constant_one_norm (p : ℝ≥0∞) (hp : p ≠ 0) :
    ‖Lp.const p circleMeasure (1 : ℂ)‖ = 1 := by
  rw [Lp.norm_const p circleMeasure (1 : ℂ) hp]
  simp [Measure.real]

/-- On the normalized circle every square-integrable function is integrable. -/
theorem circleL2_integrable (f : CircleL2) : Integrable f circleMeasure :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))

/-- The exponential monomials `uₙ(t)=exp(int)`. -/
abbrev trigMonomial (n : ℤ) : C(FourierCircle, ℂ) := fourier n

/-- The trigonometric system in `L²(T)`. -/
abbrev trigMonomialL2 (n : ℤ) : CircleL2 := fourierLp 2 n

/-- Finite trigonometric sums, with integer frequencies and complex coefficients. -/
def trigPolynomial (c : ℤ →₀ ℂ) : C(FourierCircle, ℂ) :=
  c.sum fun n a => a • trigMonomial n

/-- The exponential formula agrees with the convention in the book. -/
theorem trigMonomial_apply_real (n : ℤ) (t : ℝ) :
    trigMonomial n (t : FourierCircle) = Complex.exp (n * t * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- 4.23(8): the trigonometric system is orthonormal. -/
theorem trigonometricSystem_orthonormal : Orthonormal ℂ trigMonomialL2 :=
  orthonormal_fourier

/-- 4.23(8), with Rudin's inner product linear in its first variable. -/
theorem trigonometricSystem_inner (n m : ℤ) :
    inner ℂ (trigMonomialL2 m) (trigMonomialL2 n) = if n = m then 1 else 0 := by
  simpa [eq_comm] using (orthonormal_iff_ite.mp trigonometricSystem_orthonormal m n)

/-- The `L²` inner product is the integral of `f · conj g`. -/
theorem circleL2_inner (f g : CircleL2) :
    inner ℂ g f = ∫ t, f t * conj (g t) ∂circleMeasure := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', mul_comm]

/-- Continuous functions are dense in `L²(T)`, as used at the start of 4.24. -/
theorem circleContinuous_dense_L2 :
    DenseRange (ContinuousMap.toLp 2 circleMeasure ℂ : C(FourierCircle, ℂ) → CircleL2) :=
  ContinuousMap.toLp_denseRange ℂ circleMeasure ℂ (by simp)

set_option maxHeartbeats 800000 in
/-- The normalized `L²` norm of a continuous function is bounded by its supremum norm. -/
theorem circleContinuous_L2_norm_le (f : C(FourierCircle, ℂ)) :
    ‖ContinuousMap.toLp 2 circleMeasure ℂ f‖ ≤ ‖f‖ := by
  have h : ‖(ContinuousMap.toLp 2 circleMeasure ℂ :
      C(FourierCircle, ℂ) →L[ℂ] CircleL2)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using ContinuousMap.toLp_norm_le (p := 2) (𝕜 := ℂ) (E := ℂ) circleMeasure
  simpa using (ContinuousMap.toLp 2 circleMeasure ℂ).le_of_opNorm_le h f

/-- 4.24: finite trigonometric sums are dense in `L²(T)`. -/
theorem trigonometricSystem_complete :
    (Submodule.span ℂ (Set.range trigMonomialL2)).topologicalClosure = ⊤ :=
  span_fourierLp_closure_eq_top (by simp)

/-- In fact trigonometric polynomials are dense in every finite `Lᵖ(T)`, `p ≥ 1`. -/
theorem trigonometricSystem_dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (Submodule.span ℂ (Set.range (@fourierLp (2 * Real.pi) _ p _))).topologicalClosure = ⊤ :=
  span_fourierLp_closure_eq_top hp

/-- 4.25: every continuous function is uniformly approximated by trigonometric polynomials. -/
theorem uniform_trigonometric_approximation (f : C(FourierCircle, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ‖f - trigPolynomial c‖ < ε := by
  have hf : f ∈ (Submodule.span ℂ (Set.range (@fourier (2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  exact ⟨c, by simpa [trigPolynomial, dist_eq_norm, norm_sub_rev] using hdist⟩

/-- The pointwise formulation in 4.25, on the real parameter line. -/
theorem uniform_trigonometric_approximation_pointwise (f : C(FourierCircle, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ∀ t : ℝ, ‖f (t : FourierCircle) - trigPolynomial c (t : FourierCircle)‖ < ε := by
  obtain ⟨c, hc⟩ := uniform_trigonometric_approximation f ε hε
  refine ⟨c, fun t => lt_of_le_of_lt ?_ hc⟩
  exact ContinuousMap.norm_coe_le_norm (f - trigPolynomial c) (t : FourierCircle)

/-- Every finite-frequency sum has the symmetric finite-sum form used in 4.23(5). -/
theorem trigPolynomial_symmetric_form (c : ℤ →₀ ℂ) :
    ∃ N : ℕ, ∀ t : ℝ, trigPolynomial c (t : FourierCircle) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * Complex.exp (n * t * Complex.I) := by
  classical
  let N := c.support.sup Int.natAbs
  have hsub : c.support ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    have hnat : n.natAbs ≤ N := Finset.le_sup hn
    have habs : |n| ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnat
    exact Finset.mem_Icc.mpr ((abs_le.mp habs))
  refine ⟨N, fun t => ?_⟩
  simp only [trigPolynomial, Finsupp.sum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, trigMonomial_apply_real]
  apply Finset.sum_subset hsub
  intro n hn hnot
  simp [Finsupp.notMem_support_iff.mp hnot]

/-- 4.25, verbatim symmetric-exponential-polynomial formulation. -/
theorem uniform_trigonometric_approximation_exp (f : C(FourierCircle, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (c : ℤ → ℂ), ∀ t : ℝ,
      ‖f (t : FourierCircle) -
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * Complex.exp (n * t * Complex.I)‖ < ε := by
  obtain ⟨c, hc⟩ := uniform_trigonometric_approximation_pointwise f ε hε
  obtain ⟨N, hN⟩ := trigPolynomial_symmetric_form c
  refine ⟨N, c, fun t => ?_⟩
  rw [← hN t]
  exact hc t

/-- Group the positive and negative modes of a symmetric finite sum. -/
theorem sum_symmetric_modes (v : ℤ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), v n) =
      v 0 + ∑ k ∈ Finset.range N, (v ((k : ℤ) + 1) + v (-((k : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints, Finset.sum_range_succ, ih]
    ring

/-- Euler's identities give the exact change of coefficients for a positive/negative pair. -/
theorem paired_exponentials_eq_cos_sin (a b : ℂ) (t : ℝ) :
    a * Complex.exp ((t : ℂ) * Complex.I) + b * Complex.exp (-(t : ℂ) * Complex.I) =
      (a + b) * (Real.cos t : ℂ) + (Complex.I * (a - b)) * (Real.sin t : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- 4.23(4) and 4.23(5) describe precisely the same finite trigonometric polynomials. -/
theorem trigPolynomial_sineCosine_iff (f : ℝ → ℂ) :
    (∃ (N : ℕ) (a b : ℕ → ℂ), ∀ t : ℝ, f t = a 0 +
      ∑ k ∈ Finset.range N, (a (k + 1) * (Real.cos ((k + 1 : ℕ) * t) : ℂ) +
        b (k + 1) * (Real.sin ((k + 1 : ℕ) * t) : ℂ))) ↔
    (∃ (N : ℕ) (c : ℤ → ℂ), ∀ t : ℝ, f t =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * Complex.exp (n * t * Complex.I)) := by
  constructor
  · rintro ⟨N, a, b, hf⟩
    let c : ℤ → ℂ := fun n => if n = 0 then a 0 else if 0 < n then
      (a n.natAbs - Complex.I * b n.natAbs) / 2 else
      (a n.natAbs + Complex.I * b n.natAbs) / 2
    refine ⟨N, c, fun t => ?_⟩
    rw [hf, sum_symmetric_modes]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show c 0 = a 0 by simp [c]]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hp : (0 : ℤ) < (k + 1 : ℕ) := by omega
    have hn : ¬(0 : ℤ) < -((k + 1 : ℕ) : ℤ) := by omega
    rw [show (k : ℤ) + 1 = (k + 1 : ℕ) by omega]
    have hpair := paired_exponentials_eq_cos_sin
      (c ((k + 1 : ℕ) : ℤ)) (c (-((k + 1 : ℕ) : ℤ))) (((k + 1 : ℕ) : ℝ) * t)
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast,
      Int.cast_natCast, Int.cast_neg, neg_mul] at hpair ⊢
    rw [hpair]
    have hcpos : c ((k + 1 : ℕ) : ℤ) =
        (a (k + 1) - Complex.I * b (k + 1)) / 2 := by
      simp only [c, if_neg (ne_of_gt hp), if_pos hp, Int.natAbs_natCast]
    have hcneg : c (-((k + 1 : ℕ) : ℤ)) =
        (a (k + 1) + Complex.I * b (k + 1)) / 2 := by
      simp only [c, if_neg (neg_ne_zero.mpr (ne_of_gt hp)), if_neg hn,
        Int.natAbs_neg, Int.natAbs_natCast]
    rw [hcpos, hcneg]
    ring_nf <;> simp [Complex.I_sq]
  · rintro ⟨N, c, hf⟩
    let a : ℕ → ℂ := fun n => if n = 0 then c 0 else c n + c (-n)
    let b : ℕ → ℂ := fun n => Complex.I * (c n - c (-n))
    refine ⟨N, a, b, fun t => ?_⟩
    rw [hf, sum_symmetric_modes]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show a 0 = c 0 by simp [a]]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (k : ℤ) + 1 = (k + 1 : ℕ) by omega]
    have hpair := paired_exponentials_eq_cos_sin
      (c ((k + 1 : ℕ) : ℤ)) (c (-((k + 1 : ℕ) : ℤ))) (((k + 1 : ℕ) : ℝ) * t)
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast,
      Int.cast_natCast, Int.cast_neg, neg_mul] at hpair ⊢
    simpa [a, b] using hpair

/-- 4.26(1): the Fourier coefficient, using normalized measure. -/
abbrev circleFourierCoeff (f : FourierCircle → ℂ) (n : ℤ) := fourierCoeff f n

/-- The normalized integral over `[-π,π]` in the printed coefficient formula. -/
theorem circleFourierCoeff_integral (f : FourierCircle → ℂ) (n : ℤ) :
    circleFourierCoeff f n = (1 / (2 * Real.pi) : ℝ) •
      ∫ t in -Real.pi..Real.pi,
        Complex.exp (-(n : ℂ) * t * Complex.I) * f (t : FourierCircle) := by
  have h := fourierCoeff_eq_intervalIntegral f n (-Real.pi)
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he] at h
  simpa only [circleFourierCoeff, smul_eq_mul, trigMonomial_apply_real, Int.cast_neg] using h

/-- 4.26(3): the symmetric partial sum of the Fourier series in `L²`. -/
def fourierPartialSum (f : CircleL2) (N : ℕ) : CircleL2 :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), circleFourierCoeff f n • trigMonomialL2 n

/-- 4.26(3) for arbitrary functions, in particular for every `L¹(T)` function. -/
def circleFourierPartialSum (f : FourierCircle → ℂ) (N : ℕ) : C(FourierCircle, ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), circleFourierCoeff f n • trigMonomial n

/-- The pointwise expression of the `L¹` Fourier partial sums. -/
theorem circleFourierPartialSum_apply (f : FourierCircle → ℂ) (N : ℕ) (t : ℝ) :
    circleFourierPartialSum f N (t : FourierCircle) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        circleFourierCoeff f n * Complex.exp (n * t * Complex.I) := by
  simp only [circleFourierPartialSum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, trigMonomial_apply_real]

/-- The pointwise and `L²` partial-sum definitions represent the same element. -/
theorem circleFourierPartialSum_toLp (f : CircleL2) (N : ℕ) :
    ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPartialSum f N) =
      fourierPartialSum f N := by
  simp only [circleFourierPartialSum, fourierPartialSum, map_sum, map_smul]

/-- Their representatives agree almost everywhere. -/
theorem fourierPartialSum_ae (f : CircleL2) (N : ℕ) :
    fourierPartialSum f N =ᵐ[circleMeasure] circleFourierPartialSum f N := by
  rw [← circleFourierPartialSum_toLp]
  exact ContinuousMap.coeFn_toLp circleMeasure _

/-- The Fourier transform is an isometric Hilbert-space isomorphism onto `ℓ²(ℤ)`. -/
def circleFourierIsometry : CircleL2 ≃ₗᵢ[ℂ] ℓ²(ℤ, ℂ) := fourierBasis.repr

/-- Its coordinates are the integral Fourier coefficients. -/
theorem circleFourierIsometry_apply (f : CircleL2) (n : ℤ) :
    circleFourierIsometry f n = circleFourierCoeff f n := fourierBasis_repr f n

/-- Riesz–Fischer, with the printed square-summability hypothesis. -/
theorem fourier_riesz_fischer (c : ℤ → ℂ) (hc : Summable fun n => ‖c n‖ ^ 2) :
    ∃ f : CircleL2, ∀ n : ℤ, circleFourierCoeff f n = c n := by
  have hc' : Memℓp c 2 := memℓp_gen (by simpa using hc)
  let a : ℓ²(ℤ, ℂ) := ⟨c, hc'⟩
  refine ⟨circleFourierIsometry.symm a, fun n => ?_⟩
  rw [← circleFourierIsometry_apply, circleFourierIsometry.apply_symm_apply]

/-- Parseval's bilinear identity, including convergence of the series. -/
theorem fourier_parseval (f g : CircleL2) :
    HasSum (fun n : ℤ => circleFourierCoeff f n * conj (circleFourierCoeff g n))
      (inner ℂ g f) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (circleFourierIsometry g) (circleFourierIsometry f)
  simpa only [RCLike.inner_apply', circleFourierIsometry_apply,
    circleFourierIsometry.inner_map_map, mul_comm] using h

/-- The series in the bilinear Parseval identity converges absolutely. -/
theorem fourier_parseval_absolute (f g : CircleL2) :
    Summable (fun n : ℤ => ‖circleFourierCoeff f n * conj (circleFourierCoeff g n)‖) :=
  (fourier_parseval f g).summable.norm

/-- The integral version of the printed bilinear Parseval identity. -/
theorem fourier_parseval_integral (f g : CircleL2) :
    ∑' n : ℤ, circleFourierCoeff f n * conj (circleFourierCoeff g n) =
      ∫ t, f t * conj (g t) ∂circleMeasure := by
  rw [← circleL2_inner]
  exact (fourier_parseval f g).tsum_eq

/-- The Hilbert-space Fourier expansion. -/
theorem fourier_expansion (f : CircleL2) :
    HasSum (fun n : ℤ => circleFourierCoeff f n • trigMonomialL2 n) f :=
  hasSum_fourier_series_L2 f

/-- 4.26(7): the actual symmetric partial sums converge in `L²(T)`. -/
theorem fourierPartialSum_tendsto (f : CircleL2) :
    Tendsto (fourierPartialSum f) atTop (𝓝 f) :=
  (fourier_expansion f).comp (Finset.tendsto_Icc_neg (R := ℤ))

/-- 4.26(7), stated as convergence of the error norm to zero. -/
theorem fourierPartialSum_error_tendsto (f : CircleL2) :
    Tendsto (fun N => ‖f - fourierPartialSum f N‖) atTop (𝓝 0) := by
  simpa using ((tendsto_const_nhds (x := f)).sub (fourierPartialSum_tendsto f)).norm

/-- Fourier coordinates of each basis monomial. -/
theorem circleFourierIsometry_monomial (n : ℤ) :
    circleFourierIsometry (trigMonomialL2 n) = lp.single 2 n (1 : ℂ) := by
  change fourierBasis.repr (fourierLp 2 n) = _
  rw [← coe_fourierBasis]
  exact fourierBasis.repr_self n

/-- Parseval's norm-square form. -/
theorem fourier_parseval_norm (f : CircleL2) :
    HasSum (fun n : ℤ => ‖circleFourierCoeff f n‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (circleFourierIsometry f)
  simpa [circleFourierIsometry_apply] using h

/-- The coordinates of the symmetric partial sum retain precisely the indicated modes. -/
theorem circleFourierIsometry_partialSum (f : CircleL2) (N : ℕ) :
    circleFourierIsometry (fourierPartialSum f N) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), lp.single 2 n (circleFourierIsometry f n) := by
  simp only [fourierPartialSum, map_sum, map_smul, circleFourierIsometry_monomial,
    circleFourierIsometry_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← lp.single_smul]
  simp

/-- Finite Pythagoras for Fourier partial sums. -/
theorem fourierPartialSum_error_sq (f : CircleL2) (N : ℕ) :
    ‖f - fourierPartialSum f N‖ ^ 2 = ‖f‖ ^ 2 -
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖circleFourierCoeff f n‖ ^ 2 := by
  have h := lp.norm_compl_sum_single (p := 2) (by norm_num)
    (circleFourierIsometry f) (Finset.Icc (-(N : ℤ)) (N : ℤ))
  rw [← circleFourierIsometry_partialSum, ← map_sub] at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, circleFourierIsometry.norm_map,
    circleFourierIsometry_apply] using h

/-- 4.26(8): the squared error is exactly the sum of the omitted squared coefficients.
The subtype indexes the integers outside `[-N,N]`, equivalently those with `|n| > N`. -/
theorem fourierPartialSum_error_tail (f : CircleL2) (N : ℕ) :
    ‖f - fourierPartialSum f N‖ ^ 2 =
      ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)},
        ‖circleFourierCoeff f n‖ ^ 2 := by
  have h := (fourier_parseval_norm f).summable.sum_add_tsum_subtype_compl
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
  rw [(fourier_parseval_norm f).tsum_eq] at h
  rw [fourierPartialSum_error_sq]
  linarith

end RudinRCA.Chapter04



















































end
end
/- END Chapter04Fourier.lean -/

/- BEGIN Chapter04Fejer.lean -/
section






noncomputable section
open MeasureTheory Filter
open scoped Real ComplexConjugate Topology ENNReal

namespace RudinRCA.Chapter04

section Fejer
variable {T : ℝ} [Fact (0 < T)]

/-- Symmetric Dirichlet polynomial. -/
def fejerDirichlet (N : ℕ) (t : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourier n t

/-- One-sided geometric polynomial. -/
def fejerGeometric (N : ℕ) (t : AddCircle T) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) t

/-- Fejér's nonnegative kernel. -/
def fejerKernel (N : ℕ) (t : AddCircle T) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * ‖fejerGeometric N t‖ ^ 2

theorem fejerKernel_nonneg (N : ℕ) (t : AddCircle T) : 0 ≤ fejerKernel N t := by
  unfold fejerKernel
  positivity

theorem continuous_fejerGeometric (N : ℕ) : Continuous (@fejerGeometric T N) := by
  unfold fejerGeometric
  fun_prop

theorem continuous_fejerKernel (N : ℕ) : Continuous (@fejerKernel T N) := by
  exact continuous_const.mul ((continuous_fejerGeometric N).norm.pow 2)

theorem fejerDirichlet_pair (N : ℕ) (t : AddCircle T) :
    fejerDirichlet N t = 1 + ∑ k ∈ Finset.range N,
      (fourier ((k : ℤ) + 1) t + fourier (-((k : ℤ) + 1)) t) := by
  induction N with
  | zero => simp [fejerDirichlet, fourier_zero]
  | succ N ih =>
    unfold fejerDirichlet at *
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints,
      Finset.sum_range_succ, ih]
    ring

theorem fejerGeometric_cross (N : ℕ) (t : AddCircle T) :
    fourier ((N : ℤ) + 1) t * conj (fejerGeometric N t) =
      ∑ k ∈ Finset.range (N + 1), fourier ((k : ℤ) + 1) t := by
  unfold fejerGeometric
  rw [map_sum, Finset.mul_sum]
  simp_rw [← fourier_neg, ← fourier_add]
  rw [← Finset.sum_range_reflect (fun k => fourier ((k : ℤ) + 1) t) (N + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  have hk' : k < N + 1 := Finset.mem_range.mp hk
  omega

/-- The nonnegative square is the sum of the first Dirichlet kernels. -/
theorem fejerGeometric_mul_conj (N : ℕ) (t : AddCircle T) :
    fejerGeometric N t * conj (fejerGeometric N t) =
      ∑ k ∈ Finset.range (N + 1), fejerDirichlet k t := by
  induction N with
  | zero => simp [fejerGeometric, fejerDirichlet, fourier_zero]
  | succ N ih =>
    have hcross := fejerGeometric_cross N t
    have hcross' : fejerGeometric N t * conj (fourier ((N : ℤ) + 1) t) =
        ∑ k ∈ Finset.range (N + 1), fourier (-((k : ℤ) + 1)) t := by
      have h := congrArg conj hcross
      simpa only [map_mul, map_sum, starRingEnd_self_apply, ← fourier_neg, mul_comm] using h
    have hone : fourier ((N : ℤ) + 1) t * conj (fourier ((N : ℤ) + 1) t) = 1 := by
      rw [← fourier_neg, ← fourier_add]
      simp [fourier_zero]
    have hgeom : fejerGeometric (N + 1) t =
        fejerGeometric N t + fourier ((N : ℤ) + 1) t := by
      simp only [fejerGeometric, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [hgeom, map_add, add_mul, mul_add, mul_add, ih, hcross, hcross', hone,
      Finset.sum_range_succ (fun k => fejerDirichlet k t) (N + 1)]
    rw [fejerDirichlet_pair, Finset.sum_add_distrib]
    ring

/-- Fejér kernel as the arithmetic mean of the Dirichlet kernels. -/
theorem fejerKernel_complex (N : ℕ) (t : AddCircle T) :
    (fejerKernel N t : ℂ) = ((N + 1 : ℕ) : ℂ)⁻¹ *
      ∑ k ∈ Finset.range (N + 1), fejerDirichlet k t := by
  rw [← fejerGeometric_mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [fejerKernel]

/-- Continuous functions on the compact circle are integrable. -/
theorem fejer_integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {g : AddCircle T → E} (hg : Continuous g) : Integrable g AddCircle.haarAddCircle :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem integral_fourier_monomial (n : ℤ) :
    (∫ t : AddCircle T, fourier n t ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

theorem integral_fejerDirichlet (N : ℕ) :
    (∫ t : AddCircle T, fejerDirichlet N t ∂AddCircle.haarAddCircle) = 1 := by
  unfold fejerDirichlet
  rw [integral_finsetSum]
  · simp_rw [integral_fourier_monomial]
    simp
  · intro n hn
    exact fejer_integrable_of_continuous (fourier n).continuous

/-- Fejér kernels have normalized integral one. -/
theorem integral_fejerKernel (N : ℕ) :
    (∫ t : AddCircle T, fejerKernel N t ∂AddCircle.haarAddCircle) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [fejerKernel_complex]
  rw [integral_const_mul, integral_finsetSum]
  · simp only [integral_fejerDirichlet, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Complex.ofReal_one]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero N))
  · intro k hk
    apply fejer_integrable_of_continuous
    unfold fejerDirichlet
    fun_prop

theorem fejerFourier_nat (n : ℕ) (t : AddCircle T) :
    fourier (n : ℤ) t = fourier 1 t ^ n := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem fejerFourier_norm (n : ℤ) (t : AddCircle T) : ‖fourier n t‖ = 1 :=
  Circle.norm_coe _

/-- A uniform geometric-sum bound before dividing by the distance to `1`. -/
theorem fejerGeometric_bound (N : ℕ) (t : AddCircle T) :
    ‖fejerGeometric N t‖ * ‖fourier 1 t - 1‖ ≤ 2 := by
  have hgeom : fejerGeometric N t * (fourier 1 t - 1) =
      fourier 1 t ^ (N + 1) - 1 := by
    simp only [fejerGeometric, fejerFourier_nat]
    exact geom_sum_mul _ _
  calc
    ‖fejerGeometric N t‖ * ‖fourier 1 t - 1‖ =
        ‖fourier 1 t ^ (N + 1) - 1‖ := by rw [← norm_mul, hgeom]
    _ ≤ ‖fourier 1 t ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, fejerFourier_norm]; norm_num

theorem fejerFourier_one_eq_one_iff (t : AddCircle T) : fourier 1 t = 1 ↔ t = 0 := by
  constructor
  · intro h
    apply (AddCircle.injective_toCircle (show T ≠ 0 from (Fact.out : 0 < T).ne')).eq_iff.mp
    apply Subtype.ext
    simpa [fourier_one] using h
  · rintro rfl
    exact fourier_eval_zero 1

/-- Fejér kernels tend uniformly to zero on the complement of any neighborhood of zero. -/
theorem fejerKernel_tendstoUniformly_away (u : Set (AddCircle T))
    (hu : IsOpen u) (hzero : (0 : AddCircle T) ∈ u) :
    TendstoUniformlyOn fejerKernel 0 atTop uᶜ := by
  by_cases hempty : uᶜ = ∅
  · rw [hempty]
    exact tendstoUniformlyOn_empty
  have hne : uᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨t₀, ht₀, hmin⟩ := hu.isClosed_compl.isCompact.exists_isMinOn hne
    (((fourier 1).continuous.sub continuous_const).norm.continuousOn)
  let δ := ‖fourier 1 t₀ - 1‖
  have hδ : 0 < δ := by
    apply norm_pos_iff.mpr
    intro h
    have htzero := (fejerFourier_one_eq_one_iff t₀).mp (sub_eq_zero.mp h)
    exact ht₀ (htzero.symm ▸ hzero)
  have hb : ∀ N, ∀ t ∈ uᶜ, fejerKernel N t ≤
      ((N + 1 : ℕ) : ℝ)⁻¹ * (2 / δ) ^ 2 := by
    intro N t ht
    have hle : δ ≤ ‖fourier 1 t - 1‖ := hmin ht
    have hg : ‖fejerGeometric N t‖ ≤ 2 / δ := by
      apply (le_div_iff₀ hδ).mpr
      exact (mul_le_mul_of_nonneg_left hle (norm_nonneg _)).trans (fejerGeometric_bound N t)
    unfold fejerKernel
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg 2) (by positivity)
  have hlim : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹ * (2 / δ) ^ 2)
      atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_inv_atTop_zero.comp hn).mul_const ((2 / δ) ^ 2)
  refine Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with N hN t ht
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (fejerKernel_nonneg N t)]
    using (hb N t ht).trans_lt hN

/-- Translation as a continuous map into the Banach space `C(T)`. -/
def fejerTranslation (f : C(AddCircle T, ℂ)) : C(AddCircle T, C(AddCircle T, ℂ)) :=
  ContinuousMap.curry ⟨fun p => f (p.2 - p.1), by fun_prop⟩

@[simp] theorem fejerTranslation_apply (f : C(AddCircle T, ℂ)) (t x : AddCircle T) :
    fejerTranslation f t x = f (x - t) := rfl

@[simp] theorem fejerTranslation_zero (f : C(AddCircle T, ℂ)) :
    fejerTranslation f 0 = f := by
  ext x
  simp

/-- The approximate-identity proof takes place in the supremum-norm space itself. -/
theorem fejerConvolution_tendsto (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N : ℕ => ∫ t : AddCircle T,
      fejerKernel N t • fejerTranslation f t ∂AddCircle.haarAddCircle) atTop (𝓝 f) := by
  have h := tendsto_integral_peak_smul_of_integrable_of_tendsto
    (μ := AddCircle.haarAddCircle) (t := Set.univ) (x₀ := (0 : AddCircle T))
    MeasurableSet.univ (by simp) (by simp)
    (Filter.Eventually.of_forall fun N t => fejerKernel_nonneg N t)
    fejerKernel_tendstoUniformly_away
    (by simpa only [Measure.restrict_univ, integral_fejerKernel] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
    (Filter.Eventually.of_forall fun N => (continuous_fejerKernel N).aestronglyMeasurable)
    (fejer_integrable_of_continuous (fejerTranslation f).continuous)
    (fejerTranslation f).continuous.continuousAt
  simpa using h

theorem fejerFourier_argument_sub (n : ℤ) (x t : AddCircle T) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  simp only [fourier_apply]
  rw [zsmul_sub, sub_eq_add_neg, AddCircle.toCircle_add]
  simp only [Circle.coe_mul, neg_zsmul]

theorem integral_fejerFourier_translate (f : C(AddCircle T, ℂ))
    (n : ℤ) (x : AddCircle T) :
    (∫ t, fourier n t * f (x - t) ∂AddCircle.haarAddCircle) =
      fourierCoeff f n * fourier n x := by
  have h := integral_sub_left_eq_self
    (fun t : AddCircle T => fourier n t * f (x - t)) AddCircle.haarAddCircle x
  simp only [sub_sub_cancel] at h
  rw [← h]
  simp_rw [fejerFourier_argument_sub, mul_assoc]
  rw [integral_const_mul]
  simp only [fourierCoeff, smul_eq_mul, mul_comm]

/-- The ordinary symmetric Fourier partial sum in the space of continuous functions. -/
def fejerFourierPartialSum (f : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n

theorem integral_fejerDirichlet_translate (f : C(AddCircle T, ℂ))
    (N : ℕ) (x : AddCircle T) :
    (∫ t, fejerDirichlet N t * f (x - t) ∂AddCircle.haarAddCircle) =
      fejerFourierPartialSum f N x := by
  simp_rw [fejerDirichlet, Finset.sum_mul]
  rw [integral_finsetSum]
  · simp only [integral_fejerFourier_translate, fejerFourierPartialSum,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  · intro n hn
    exact fejer_integrable_of_continuous ((fourier n).continuous.mul
      (f.continuous.comp (continuous_const.sub continuous_id)))

/-- Fejér means are the arithmetic means of the ordinary symmetric Fourier partial sums. -/
def fejerMean (f : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  (((N + 1 : ℕ) : ℂ)⁻¹) • ∑ k ∈ Finset.range (N + 1), fejerFourierPartialSum f k

/-- Integral representation of the arithmetic means. -/
theorem fejerConvolution_eq_mean (f : C(AddCircle T, ℂ)) (N : ℕ) :
    (∫ t : AddCircle T, fejerKernel N t • fejerTranslation f t
      ∂AddCircle.haarAddCircle) = fejerMean f N := by
  ext x
  have hint : Integrable (fun t : AddCircle T => fejerKernel N t • fejerTranslation f t)
      AddCircle.haarAddCircle :=
    fejer_integrable_of_continuous
      ((continuous_fejerKernel N).smul (fejerTranslation f).continuous)
  rw [ContinuousMap.integral_apply hint]
  change (∫ t : AddCircle T, fejerKernel N t • f (x - t) ∂AddCircle.haarAddCircle) = _
  simp_rw [Complex.real_smul, fejerKernel_complex, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum]
  · simp only [integral_fejerDirichlet_translate, fejerMean,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  · intro k hk
    apply fejer_integrable_of_continuous
    unfold fejerDirichlet
    fun_prop

/-- Fejér's theorem in 4.25: the arithmetic means of the symmetric Fourier partial sums
of every continuous function converge in the supremum norm to that function. -/
theorem fejerMean_tendsto (f : C(AddCircle T, ℂ)) :
    Tendsto (fejerMean f) atTop (𝓝 f) := by
  simpa only [fejerConvolution_eq_mean] using fejerConvolution_tendsto f

/-- The error in Fejér's theorem tends uniformly to zero. -/
theorem fejerMean_error_tendsto (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N : ℕ => ‖fejerMean f N - f‖) atTop (𝓝 0) := by
  simpa using ((fejerMean_tendsto f).sub (tendsto_const_nhds (x := f))).norm

end Fejer
end RudinRCA.Chapter04











end
end
/- END Chapter04Fejer.lean -/

/- BEGIN Chapter04AxiomBridge.lean -/
section
/-!
Append-only bridge for Rudin 4.2–4.3. The surrounding chapter already imports
`Mathlib.Analysis.InnerProductSpace.PiL2`, which provides the Core construction.
No norm, seminorm, topology, metric, or positive-definiteness is assumed on V.
Mathlib's `b.inner y x` is Rudin's inner product `(x,y)`, linear in x.
-/

namespace RudinRCA.Chapter04

section AlgebraicInnerProduct

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Rudin 4.2 directly from the algebraic inner-product axioms 4.1(a–d).
The two square roots define the seminorm; no triangle inequality is assumed. -/
theorem schwarz_from_axioms (b : PreInnerProductSpace.Core ℂ V) (x y : V) :
    ‖b.inner y x‖ ≤ Real.sqrt (b.inner x x).re * Real.sqrt (b.inner y y).re := by
  letI : PreInnerProductSpace.Core ℂ V := b
  have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) y x
  change ‖b.inner y x‖ ≤ Real.sqrt (b.inner y y).re * Real.sqrt (b.inner x x).re at h
  exact h.trans_eq (mul_comm _ _)

/-- Rudin 4.3 directly from the same algebraic axioms, before any normed-space
structure has been assumed. The Core construction proves its own triangle law
from Schwarz and the inner-product expansion. -/
theorem triangle_from_axioms (b : PreInnerProductSpace.Core ℂ V) (x y : V) :
    Real.sqrt (b.inner (x + y) (x + y)).re ≤
      Real.sqrt (b.inner x x).re + Real.sqrt (b.inner y y).re := by
  letI : PreInnerProductSpace.Core ℂ V := b
  letI : SeminormedAddCommGroup V :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)
  exact norm_add_le x y

end AlgebraicInnerProduct

end RudinRCA.Chapter04



end
/- END Chapter04AxiomBridge.lean -/

/- Axiom audit: every theorem/lemma declared in this chapter. -/
#print axioms RudinRCA.Chapter04.inner_conjugate_symmetry
#print axioms RudinRCA.Chapter04.inner_add_first
#print axioms RudinRCA.Chapter04.inner_smul_first
#print axioms RudinRCA.Chapter04.inner_self_real_nonnegative
#print axioms RudinRCA.Chapter04.inner_zero_first
#print axioms RudinRCA.Chapter04.inner_smul_second
#print axioms RudinRCA.Chapter04.inner_add_second
#print axioms RudinRCA.Chapter04.norm_from_inner
#print axioms RudinRCA.Chapter04.norm_squared_inner
#print axioms RudinRCA.Chapter04.innerFunctional_apply
#print axioms RudinRCA.Chapter04.schwarz
#print axioms RudinRCA.Chapter04.triangle
#print axioms RudinRCA.Chapter04.inner_self_zero_iff
#print axioms RudinRCA.Chapter04.hilbert_distance
#print axioms RudinRCA.Chapter04.difference_triangle
#print axioms RudinRCA.Chapter04.hilbert_cauchy
#print axioms RudinRCA.Chapter04.continuous_inner_and_norm
#print axioms RudinRCA.Chapter04.inner_first_lipschitz
#print axioms RudinRCA.Chapter04.inner_second_lipschitz
#print axioms RudinRCA.Chapter04.norm_lipschitz
#print axioms RudinRCA.Chapter04.finite_euclidean_complete
#print axioms RudinRCA.Chapter04.finite_euclidean_inner
#print axioms RudinRCA.Chapter04.l2_complete
#print axioms RudinRCA.Chapter04.l2_inner
#print axioms RudinRCA.Chapter04.l2_product_integrable
#print axioms RudinRCA.Chapter04.subspace_criterion
#print axioms RudinRCA.Chapter04.empty_set_not_subspace
#print axioms RudinRCA.Chapter04.unit_bounded_not_subspace
#print axioms RudinRCA.Chapter04.real_three_subspace_dimensions
#print axioms RudinRCA.Chapter04.real_three_subspace_classification
#print axioms RudinRCA.Chapter04.closure_subspace
#print axioms RudinRCA.Chapter04.convex_criterion
#print axioms RudinRCA.Chapter04.subspace_convex
#print axioms RudinRCA.Chapter04.convex_translate
#print axioms RudinRCA.Chapter04.complex_subspace_convex_combinations
#print axioms RudinRCA.Chapter04.orthogonal_symmetric
#print axioms RudinRCA.Chapter04.orthogonal_complement_closed
#print axioms RudinRCA.Chapter04.orthogonal_complement_membership
#print axioms RudinRCA.Chapter04.vectorOrthogonal_carrier
#print axioms RudinRCA.Chapter04.vectorOrthogonal_closed
#print axioms RudinRCA.Chapter04.orthogonal_as_intersection
#print axioms RudinRCA.Chapter04.intervalToL2_injective
#print axioms RudinRCA.Chapter04.continuousIntervalIntegralEquiv_apply
#print axioms RudinRCA.Chapter04.interval_integral_inner
#print axioms RudinRCA.Chapter04.intervalSpike_one
#print axioms RudinRCA.Chapter04.intervalSpike_L2_norm_tendsto
#print axioms RudinRCA.Chapter04.continuous_interval_integral_not_complete
#print axioms RudinRCA.Chapter04.theorem_4_10
#print axioms RudinRCA.Chapter04.theorem_4_11
#print axioms RudinRCA.Chapter04.corollary_4_11
#print axioms RudinRCA.Chapter04.theorem_4_11_nearest_unique
#print axioms RudinRCA.Chapter04.theorem_4_12
#print axioms RudinRCA.Chapter04.span_least
#print axioms RudinRCA.Chapter04.span_iff_finite_linear_combination
#print axioms RudinRCA.Chapter04.independent_iff_finite_combinations
#print axioms RudinRCA.Chapter04.orthonormal_iff_rudin
#print axioms RudinRCA.Chapter04.finiteLinearCombination_mem
#print axioms RudinRCA.Chapter04.theorem_4_14a_coefficients
#print axioms RudinRCA.Chapter04.theorem_4_14a_norm
#print axioms RudinRCA.Chapter04.theorem_4_14b_bessel
#print axioms RudinRCA.Chapter04.finiteFourierSum_residual_orthogonal
#print axioms RudinRCA.Chapter04.theorem_4_14b_remainder
#print axioms RudinRCA.Chapter04.theorem_4_14b_best
#print axioms RudinRCA.Chapter04.theorem_4_15_nonnegative_sum
#print axioms RudinRCA.Chapter04.theorem_4_15_counting_integral
#print axioms RudinRCA.Chapter04.theorem_4_15_membership
#print axioms RudinRCA.Chapter04.theorem_4_15_membership_sum
#print axioms RudinRCA.Chapter04.theorem_4_15_complete
#print axioms RudinRCA.Chapter04.theorem_4_15_norm
#print axioms RudinRCA.Chapter04.theorem_4_15_inner
#print axioms RudinRCA.Chapter04.theorem_4_15_countable_support
#print axioms RudinRCA.Chapter04.theorem_4_15_finite_dense
#print axioms RudinRCA.Chapter04.theorem_4_16
#print axioms RudinRCA.Chapter04.fourierAnalysis_coefficient
#print axioms RudinRCA.Chapter04.fourierAnalysis_synthesis
#print axioms RudinRCA.Chapter04.fourierSynthesis_range
#print axioms RudinRCA.Chapter04.theorem_4_17
#print axioms RudinRCA.Chapter04.dense_span_of_fourier_detection
#print axioms RudinRCA.Chapter04.theorem_4_18_maximal_iff_dense
#print axioms RudinRCA.Chapter04.theorem_4_18_dense_iff_norm
#print axioms RudinRCA.Chapter04.theorem_4_18_dense_iff_parseval
#print axioms RudinRCA.Chapter04.theorem_4_18
#print axioms RudinRCA.Chapter04.hilbertBasis_isomorphism
#print axioms RudinRCA.Chapter04.maximal_orthonormal_coefficient_isomorphism
#print axioms RudinRCA.Chapter04.hilbert_isomorphism_preserves_inner
#print axioms RudinRCA.Chapter04.hilbertSpace_exists_l2_isomorphism
#print axioms RudinRCA.Chapter04.hilbertBasis_coefficients_countable
#print axioms RudinRCA.Chapter04.hilbertBasis_card_le_infinite
#print axioms RudinRCA.Chapter04.hilbertBasis_card_eq
#print axioms RudinRCA.Chapter04.l2_isomorphism_of_equiv
#print axioms RudinRCA.Chapter04.l2_isomorphism_iff_card_eq
#print axioms RudinRCA.Chapter04.partialOrder_laws
#print axioms RudinRCA.Chapter04.originDiscChain_isChain
#print axioms RudinRCA.Chapter04.empty_not_mem_originDiscChain
#print axioms RudinRCA.Chapter04.univ_not_mem_originDiscChain
#print axioms RudinRCA.Chapter04.originDiscChain_not_maximal
#print axioms RudinRCA.Chapter04.originDiscChain_extend_by_empty
#print axioms RudinRCA.Chapter04.originDiscChain_extend_by_univ
#print axioms RudinRCA.Chapter04.hausdorff_maximality
#print axioms RudinRCA.Chapter04.exists_maximal_chain
#print axioms RudinRCA.Chapter04.exists_unit_vector
#print axioms RudinRCA.Chapter04.orthonormal_set_extension
#print axioms RudinRCA.Chapter04.fourierCircleHomeomorphism_apply
#print axioms RudinRCA.Chapter04.circleFunction_periodic
#print axioms RudinRCA.Chapter04.periodicFunction_descends
#print axioms RudinRCA.Chapter04.continuous_circleFunction
#print axioms RudinRCA.Chapter04.continuous_periodicFunction_descends
#print axioms RudinRCA.Chapter04.circleIntegral_interval
#print axioms RudinRCA.Chapter04.circleLp_norm_formula
#print axioms RudinRCA.Chapter04.circleLp_infty_norm_formula
#print axioms RudinRCA.Chapter04.circleContinuous_norm_formula
#print axioms RudinRCA.Chapter04.circleLp_constant_one_norm
#print axioms RudinRCA.Chapter04.circleL2_integrable
#print axioms RudinRCA.Chapter04.trigMonomial_apply_real
#print axioms RudinRCA.Chapter04.trigonometricSystem_orthonormal
#print axioms RudinRCA.Chapter04.trigonometricSystem_inner
#print axioms RudinRCA.Chapter04.circleL2_inner
#print axioms RudinRCA.Chapter04.circleContinuous_dense_L2
#print axioms RudinRCA.Chapter04.circleContinuous_L2_norm_le
#print axioms RudinRCA.Chapter04.trigonometricSystem_complete
#print axioms RudinRCA.Chapter04.trigonometricSystem_dense_Lp
#print axioms RudinRCA.Chapter04.uniform_trigonometric_approximation
#print axioms RudinRCA.Chapter04.uniform_trigonometric_approximation_pointwise
#print axioms RudinRCA.Chapter04.trigPolynomial_symmetric_form
#print axioms RudinRCA.Chapter04.uniform_trigonometric_approximation_exp
#print axioms RudinRCA.Chapter04.sum_symmetric_modes
#print axioms RudinRCA.Chapter04.paired_exponentials_eq_cos_sin
#print axioms RudinRCA.Chapter04.trigPolynomial_sineCosine_iff
#print axioms RudinRCA.Chapter04.circleFourierCoeff_integral
#print axioms RudinRCA.Chapter04.circleFourierPartialSum_apply
#print axioms RudinRCA.Chapter04.circleFourierPartialSum_toLp
#print axioms RudinRCA.Chapter04.fourierPartialSum_ae
#print axioms RudinRCA.Chapter04.circleFourierIsometry_apply
#print axioms RudinRCA.Chapter04.fourier_riesz_fischer
#print axioms RudinRCA.Chapter04.fourier_parseval
#print axioms RudinRCA.Chapter04.fourier_parseval_absolute
#print axioms RudinRCA.Chapter04.fourier_parseval_integral
#print axioms RudinRCA.Chapter04.fourier_expansion
#print axioms RudinRCA.Chapter04.fourierPartialSum_tendsto
#print axioms RudinRCA.Chapter04.fourierPartialSum_error_tendsto
#print axioms RudinRCA.Chapter04.circleFourierIsometry_monomial
#print axioms RudinRCA.Chapter04.fourier_parseval_norm
#print axioms RudinRCA.Chapter04.circleFourierIsometry_partialSum
#print axioms RudinRCA.Chapter04.fourierPartialSum_error_sq
#print axioms RudinRCA.Chapter04.fourierPartialSum_error_tail
#print axioms RudinRCA.Chapter04.fejerKernel_nonneg
#print axioms RudinRCA.Chapter04.continuous_fejerGeometric
#print axioms RudinRCA.Chapter04.continuous_fejerKernel
#print axioms RudinRCA.Chapter04.fejerDirichlet_pair
#print axioms RudinRCA.Chapter04.fejerGeometric_cross
#print axioms RudinRCA.Chapter04.fejerGeometric_mul_conj
#print axioms RudinRCA.Chapter04.fejerKernel_complex
#print axioms RudinRCA.Chapter04.fejer_integrable_of_continuous
#print axioms RudinRCA.Chapter04.integral_fourier_monomial
#print axioms RudinRCA.Chapter04.integral_fejerDirichlet
#print axioms RudinRCA.Chapter04.integral_fejerKernel
#print axioms RudinRCA.Chapter04.fejerFourier_nat
#print axioms RudinRCA.Chapter04.fejerFourier_norm
#print axioms RudinRCA.Chapter04.fejerGeometric_bound
#print axioms RudinRCA.Chapter04.fejerFourier_one_eq_one_iff
#print axioms RudinRCA.Chapter04.fejerKernel_tendstoUniformly_away
#print axioms RudinRCA.Chapter04.fejerTranslation_apply
#print axioms RudinRCA.Chapter04.fejerTranslation_zero
#print axioms RudinRCA.Chapter04.fejerConvolution_tendsto
#print axioms RudinRCA.Chapter04.fejerFourier_argument_sub
#print axioms RudinRCA.Chapter04.integral_fejerFourier_translate
#print axioms RudinRCA.Chapter04.integral_fejerDirichlet_translate
#print axioms RudinRCA.Chapter04.fejerConvolution_eq_mean
#print axioms RudinRCA.Chapter04.fejerMean_tendsto
#print axioms RudinRCA.Chapter04.fejerMean_error_tendsto
#print axioms RudinRCA.Chapter04.schwarz_from_axioms
#print axioms RudinRCA.Chapter04.triangle_from_axioms
