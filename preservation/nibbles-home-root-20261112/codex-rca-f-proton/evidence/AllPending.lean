import RudinRCA.Chapter13
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Algebra.Algebra.Pi
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Ring
import Mathlib.Topology.Subpath
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false

/- Source: InfinityBridge.lean -/
noncomputable section Source0
open Set Filter Metric
open scoped Topology
namespace RudinRCA.Chapter13
/-- The exterior-domain and punctured inverse-chart definitions of isolation agree. -/
theorem hasIsolatedSingularityAtInfinity_iff {f : ℂ → ℂ} :
    HasIsolatedSingularityAtInfinity f ↔
      ∀ᶠ z : ℂ in 𝓝[≠] 0, DifferentiableAt ℂ (fun w : ℂ => f w⁻¹) z := by
  constructor
  · rintro ⟨r, _, hf⟩
    have hext : ∀ᶠ z : ℂ in 𝓝[≠] 0, r < ‖z⁻¹‖ :=
      (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero).eventually_gt_atTop r
    filter_upwards [hext, self_mem_nhdsWithin] with z hz hz0
    exact (hf.differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)).comp z
        (differentiableAt_inv hz0)
  · intro h
    have hback := (tendsto_inv₀_cobounded' (α := ℂ)).eventually h
    have hext : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, 0 < ‖z‖ :=
      tendsto_norm_cobounded_atTop.eventually_gt_atTop 0
    have hd : ∀ᶠ z : ℂ in cocompact ℂ, DifferentiableAt ℂ f z := by
      rw [← Metric.cobounded_eq_cocompact]
      filter_upwards [hback, hext] with z hz hz0
      simpa only [Function.comp_def, inv_inv] using
        hz.comp z (differentiableAt_inv (norm_pos_iff.mp hz0))
    obtain ⟨K, hK, hKd⟩ := mem_cocompact.mp hd
    obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨r, hr, fun z hz => (hKd ?_).differentiableWithinAt⟩
    exact fun hzK => (not_lt_of_ge (hKr z hzK)) hz

theorem pole_hasIsolatedSingularityAtInfinity {f : ℂ → ℂ} {m : ℕ}
    (h : HasPoleAtInfinity f m) : HasIsolatedSingularityAtInfinity f := by
  apply hasIsolatedSingularityAtInfinity_iff.mpr
  exact h.2.1.eventually_analyticAt.mono fun _ hz => hz.differentiableAt


#print axioms hasIsolatedSingularityAtInfinity_iff
#print axioms pole_hasIsolatedSingularityAtInfinity
end RudinRCA.Chapter13
end Source0

/- Source: RationalPartialFractions.lean -/
noncomputable section Source1

/-!
Scratch development for Rudin RCA 13.2.  This file develops algebraic partial fractions in the rational function field,
reduced representations, and analytic orders of reduced-denominator roots.
The grouped identity is also interpreted pointwise off the reduced denominator roots,
with the same fixed polynomials. Behavior at infinity is handled separately in node 13.1.
This is a scratch artifact; completion depends on successful compilation and integration.
-/

open Polynomial
open scoped BigOperators Topology

namespace RudinRCA.Chapter13

/-- A complex rational function has a monic reduced denominator and a coprime numerator. -/
theorem rational_reduced_representation (f : RatFunc ℂ) :
    f.denom.Monic ∧ f.denom ≠ 0 ∧ IsCoprime f.num f.denom ∧
      algebraMap ℂ[X] (RatFunc ℂ) f.num / algebraMap ℂ[X] (RatFunc ℂ) f.denom = f :=
  ⟨f.monic_denom, f.denom_ne_zero, f.isCoprime_num_denom, f.num_div_denom⟩

/-- Linear-factor partial fractions, with coefficients constant rather than polynomial. -/
theorem rational_partial_fractions_coefficients (f : RatFunc ℂ) :
    ∃ (q : ℂ[X]) (c : (a : ℂ) → Fin (f.denom.rootMultiplicity a) → ℂ),
      f = algebraMap ℂ[X] (RatFunc ℂ) q +
        ∑ a ∈ f.denom.roots.toFinset, ∑ j,
          algebraMap ℂ[X] (RatFunc ℂ) (C (c a j)) *
            (algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹ ^ (j.val + 1) := by
  classical
  let g : ℂ → ℂ[X] := fun a => X - C a
  let gi : ℂ → RatFunc ℂ := fun a => (algebraMap ℂ[X] (RatFunc ℂ) (g a))⁻¹
  have hg : ∀ a ∈ f.denom.roots.toFinset, (g a).Monic :=
    fun a _ => monic_X_sub_C a
  have hgg : Set.Pairwise (f.denom.roots.toFinset : Set ℂ)
      (fun a b => IsCoprime (g a) (g b)) := by
    intro a _ b _ hab
    exact pairwise_coprime_X_sub_C Function.injective_id hab
  have hgi : ∀ a ∈ f.denom.roots.toFinset,
      gi a * algebraMap ℂ[X] (RatFunc ℂ) (g a) = 1 := by
    intro a _
    exact inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
  obtain ⟨q, r, hr, hf⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse f.num hg hgg
      f.denom.rootMultiplicity hgi
  have hrC : ∀ a ∈ f.denom.roots.toFinset, ∀ j, r a j = C ((r a j).coeff 0) := by
    intro a ha j
    apply eq_C_of_degree_le_zero
    have hd := hr a ha j
    simp only [g, degree_X_sub_C] at hd
    by_cases hz : r a j = 0
    · simp [hz]
    · have hn : (r a j).natDegree < 1 := (natDegree_lt_iff_degree_lt hz).2 hd
      exact degree_le_of_natDegree_le (Nat.le_of_lt_succ hn)
  have hdenom : f.denom = ∏ a ∈ f.denom.roots.toFinset,
      (X - C a) ^ f.denom.rootMultiplicity a := by
    rw [← prod_multiset_root_eq_finset_root]
    exact (IsAlgClosed.splits f.denom).eq_prod_roots_of_monic f.monic_denom
  refine ⟨q, fun a j => (r a j).coeff 0, ?_⟩
  have hprod : (∏ a ∈ f.denom.roots.toFinset, gi a ^ f.denom.rootMultiplicity a) =
      (algebraMap ℂ[X] (RatFunc ℂ) f.denom)⁻¹ := by
    conv_rhs => rw [hdenom, map_prod]
    simp only [map_pow, gi, g, inv_pow, Finset.prod_inv_distrib]
  rw [hprod, ← div_eq_mul_inv, f.num_div_denom] at hf
  refine hf.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j _
  rw [hrC a ha j]

/-- Rudin's grouped partial-fractions shape: each polynomial in the reciprocal
has zero constant term, and the finite poles used are roots of the reduced denominator. -/
theorem rational_partial_fractions_polynomials (f : RatFunc ℂ) :
    ∃ (q : ℂ[X]) (A : ℂ → ℂ[X]),
      (∀ a, (A a).coeff 0 = 0) ∧
      f = algebraMap ℂ[X] (RatFunc ℂ) q +
        ∑ a ∈ f.denom.roots.toFinset,
          aeval ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹) (A a) := by
  classical
  obtain ⟨q, c, hf⟩ := rational_partial_fractions_coefficients f
  let A : ℂ → ℂ[X] := fun a =>
    ∑ j : Fin (f.denom.rootMultiplicity a), C (c a j) * X ^ (j.val + 1)
  refine ⟨q, A, ?_, ?_⟩
  · intro a
    simp [A]
  · refine hf.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [A, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    apply Finset.sum_congr rfl
    intro j _
    congr 1

/-- Linear-denominator partial fractions in any polynomial algebra containing
the required inverses. Choosing a function algebra fixes the coefficients for all points. -/
theorem linear_partial_fractions_in_algebra {B : Type*} [CommRing B] [Algebra ℂ[X] B]
    (P : ℂ[X]) (s : Finset ℂ) (n : ℂ → ℕ) (gi : ℂ → B)
    (hi : ∀ a ∈ s, gi a * algebraMap ℂ[X] B (X - C a) = 1) :
    ∃ (q : ℂ[X]) (c : (a : ℂ) → Fin (n a) → ℂ),
      algebraMap ℂ[X] B P * ∏ a ∈ s, gi a ^ n a =
        algebraMap ℂ[X] B q + ∑ a ∈ s, ∑ j,
          algebraMap ℂ[X] B (C (c a j)) * gi a ^ (j.val + 1) := by
  classical
  have hg : ∀ a ∈ s, (X - C a : ℂ[X]).Monic := fun a _ => monic_X_sub_C a
  have hgg : Set.Pairwise (s : Set ℂ)
      (fun a b => IsCoprime (X - C a : ℂ[X]) (X - C b)) := by
    intro a _ b _ hab
    exact pairwise_coprime_X_sub_C Function.injective_id hab
  obtain ⟨q, r, hr, hf⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse P hg hgg n hi
  refine ⟨q, fun a j => (r a j).coeff 0, hf.trans ?_⟩
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j _
  have hrC : r a j = C ((r a j).coeff 0) := by
    apply eq_C_of_degree_le_zero
    have hd := hr a ha j
    simp only [degree_X_sub_C] at hd
    by_cases hz : r a j = 0
    · simp [hz]
    · have hn : (r a j).natDegree < 1 := (natDegree_lt_iff_degree_lt hz).2 hd
      exact degree_le_of_natDegree_le (Nat.le_of_lt_succ hn)
  rw [hrC]

/-- The same fixed polynomials give the rational-field identity and its pointwise
interpretation at every point outside the reduced denominator's zero set. -/
theorem rational_partial_fractions_with_evaluation (f : RatFunc ℂ) :
    ∃ (q : ℂ[X]) (A : ℂ → ℂ[X]), (∀ a, (A a).coeff 0 = 0) ∧
      (f = algebraMap ℂ[X] (RatFunc ℂ) q +
        ∑ a ∈ f.denom.roots.toFinset,
          aeval ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹) (A a)) ∧
      ∀ z : ℂ, f.denom.eval z ≠ 0 →
        f.num.eval z / f.denom.eval z =
          q.eval z + ∑ a ∈ f.denom.roots.toFinset, (A a).eval ((z - a)⁻¹) := by
  classical
  let D := {z : ℂ // f.denom.eval z ≠ 0}
  let ev : ℂ[X] →+* (D → ℂ) := RingHom.pi fun z => evalRingHom z.val
  let : Algebra ℂ[X] (D → ℂ) := ev.toAlgebra
  let B := RatFunc ℂ × (D → ℂ)
  let s := f.denom.roots.toFinset
  let n : ℂ → ℕ := f.denom.rootMultiplicity
  let gi : ℂ → B := fun a =>
    ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹, fun z => (z.val - a)⁻¹)
  have hi : ∀ a ∈ s, gi a * algebraMap ℂ[X] B (X - C a) = 1 := by
    intro a ha
    apply Prod.ext
    · exact inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
    · funext z
      change (z.val - a)⁻¹ * (X - C a).eval z.val = 1
      simp only [eval_sub, eval_X, eval_C]
      apply inv_mul_cancel₀
      apply sub_ne_zero.mpr
      intro heq
      have haroot : f.denom.eval a = 0 :=
        (mem_roots f.denom_ne_zero).1 (Multiset.mem_toFinset.mp ha)
      exact z.property (by simpa only [heq] using haroot)
  obtain ⟨q, c, hf⟩ := linear_partial_fractions_in_algebra f.num s n gi hi
  let A : ℂ → ℂ[X] := fun a => ∑ j : Fin (n a), C (c a j) * X ^ (j.val + 1)
  have hdenom : f.denom = ∏ a ∈ s, (X - C a) ^ n a := by
    rw [← prod_multiset_root_eq_finset_root]
    exact (IsAlgClosed.splits f.denom).eq_prod_roots_of_monic f.monic_denom
  refine ⟨q, A, fun a => by simp [A], ?_, ?_⟩
  · have h := congrArg (RingHom.fst (RatFunc ℂ) (D → ℂ)) hf
    simp only [map_mul, map_prod, map_pow, map_add, map_sum] at h
    change algebraMap ℂ[X] (RatFunc ℂ) f.num *
      (∏ a ∈ s, ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹) ^ n a) =
        algebraMap ℂ[X] (RatFunc ℂ) q + ∑ a ∈ s, ∑ j,
          algebraMap ℂ[X] (RatFunc ℂ) (C (c a j)) *
            ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹) ^ (j.val + 1) at h
    have hp : (∏ a ∈ s, ((algebraMap ℂ[X] (RatFunc ℂ) (X - C a))⁻¹) ^ n a) =
        (algebraMap ℂ[X] (RatFunc ℂ) f.denom)⁻¹ := by
      conv_rhs => rw [hdenom, map_prod]
      simp only [map_pow, inv_pow, Finset.prod_inv_distrib]
    rw [hp, ← div_eq_mul_inv, f.num_div_denom] at h
    refine h.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [A, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  · intro z hz
    let ez : B →+* ℂ := (Pi.evalRingHom (fun _ : D => ℂ) ⟨z, hz⟩).comp
      (RingHom.snd (RatFunc ℂ) (D → ℂ))
    have h := congrArg ez hf
    simp only [map_mul, map_prod, map_pow, map_add, map_sum] at h
    change f.num.eval z * (∏ a ∈ s, (z - a)⁻¹ ^ n a) =
      q.eval z + ∑ a ∈ s, ∑ j, (C (c a j)).eval z * (z - a)⁻¹ ^ (j.val + 1) at h
    simp only [eval_C] at h
    have hd : f.denom.eval z = ∏ a ∈ s, (z - a) ^ n a := by
      conv_lhs => rw [hdenom]
      simp only [eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    have hp : (∏ a ∈ s, (z - a)⁻¹ ^ n a) = (f.denom.eval z)⁻¹ := by
      conv_rhs => rw [hd]
      simp only [inv_pow, Finset.prod_inv_distrib]
    rw [hp, ← div_eq_mul_inv] at h
    refine h.trans ?_
    simp only [A, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rfl

/-- Each summand in the partial-fractions formula is the corresponding
principal part: after subtracting it, the remaining germ extends analytically. -/
theorem rational_principal_part_remainder (f : RatFunc ℂ) (q : ℂ[X]) (A : ℂ → ℂ[X])
    (hrep : ∀ z : ℂ, f.denom.eval z ≠ 0 →
      f.num.eval z / f.denom.eval z =
        q.eval z + ∑ b ∈ f.denom.roots.toFinset, (A b).eval ((z - b)⁻¹))
    (a : ℂ) (ha : a ∈ f.denom.roots.toFinset) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a,
        f.num.eval z / f.denom.eval z - (A a).eval ((z - a)⁻¹) = g z := by
  classical
  let g : ℂ → ℂ := fun z => q.eval z +
    ∑ b ∈ f.denom.roots.toFinset.erase a, (A b).eval ((z - b)⁻¹)
  refine ⟨g, ?_, ?_⟩
  · apply ((AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ a)).add
    apply Finset.analyticAt_fun_sum
    intro b hb
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - b) a :=
      analyticAt_id.sub analyticAt_const
    have hab : a - b ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm
    exact (hsub.inv hab).aeval_polynomial (A b)
  · have he := (Polynomial.eventually_eval_ne_zero_cofinite f.denom_ne_zero).filter_mono
      (nhdsNE_le_cofinite a)
    filter_upwards [he] with z hz
    rw [hrep z hz]
    dsimp only [g]
    rw [← Finset.sum_erase_add f.denom.roots.toFinset
      (fun b => (A b).eval ((z - b)⁻¹)) ha]
    ring

/-- Reduction of a quotient does not change its value where the original
polynomial denominator is nonzero. Thus the preceding theorem applies to every P/Q. -/
theorem rational_quotient_evaluation (P Q : ℂ[X]) (z : ℂ) (hz : Q.eval z ≠ 0) :
    let f := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q
    f.denom.eval z ≠ 0 ∧ f.num.eval z / f.denom.eval z = P.eval z / Q.eval z := by
  let f := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q
  have hQ : Q ≠ 0 := by
    intro h
    apply hz
    simp [h]
  have hd : f.denom.eval z ≠ 0 := by
    intro h
    obtain ⟨R, hR⟩ := RatFunc.denom_div_dvd P Q
    apply hz
    rw [hR, eval_mul]
    change f.denom.eval z * R.eval z = 0
    rw [h, zero_mul]
  refine ⟨hd, (div_eq_div_iff hd hz).2 ?_⟩
  have hc : f.num * Q = P * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hQ).2 rfl
  simpa only [eval_mul] using congrArg (fun p : ℂ[X] => p.eval z) hc

/-- Algebraic root multiplicity agrees with the analytic order of a nonzero polynomial. -/
theorem polynomial_meromorphic_order (P : ℂ[X]) (hP : P ≠ 0) (a : ℂ) :
    meromorphicOrderAt (fun z => P.eval z) a = (P.rootMultiplicity a : ℤ) := by
  have hPa : AnalyticAt ℂ (fun z => P.eval z) a :=
    (AnalyticOnNhd.eval_polynomial P) a (Set.mem_univ a)
  apply (meromorphicOrderAt_eq_int_iff hPa.meromorphicAt).2
  let Q := P /ₘ (X - C a) ^ P.rootMultiplicity a
  refine ⟨fun z => Q.eval z,
    (AnalyticOnNhd.eval_polynomial Q) a (Set.mem_univ a),
    eval_divByMonic_pow_rootMultiplicity_ne_zero a hP, ?_⟩
  apply Filter.Eventually.of_forall
  intro z
  have h := congrArg (fun R : ℂ[X] => R.eval z) (P.pow_mul_divByMonic_rootMultiplicity_eq a)
  simpa [Q, eval_mul, eval_pow, eval_sub, eval_X, eval_C, zpow_natCast,
    Algebra.smul_def] using h.symm

/-- At a root of the reduced denominator, a rational function has exactly the
negative order of that root, hence a pole with precisely that multiplicity. -/
theorem rational_pole_order (f : RatFunc ℂ) (a : ℂ) (ha : f.denom.eval a = 0) :
    meromorphicOrderAt (fun z => f.num.eval z / f.denom.eval z) a =
      -(f.denom.rootMultiplicity a : ℤ) := by
  have hnum : f.num.eval a ≠ 0 := by
    have h := Polynomial.aeval_ne_zero_of_isCoprime f.isCoprime_num_denom a
    change f.num.eval a ≠ 0 ∨ f.denom.eval a ≠ 0 at h
    exact h.resolve_right (not_not.mpr ha)
  have hn : AnalyticAt ℂ (fun z => f.num.eval z) a :=
    (AnalyticOnNhd.eval_polynomial f.num) a (Set.mem_univ a)
  have hd : AnalyticAt ℂ (fun z => f.denom.eval z) a :=
    (AnalyticOnNhd.eval_polynomial f.denom) a (Set.mem_univ a)
  have hno : meromorphicOrderAt (fun z => f.num.eval z) a = (0 : ℤ) := by
    apply (meromorphicOrderAt_eq_int_iff hn.meromorphicAt).2
    exact ⟨fun z => f.num.eval z, hn, hnum, Filter.Eventually.of_forall (by simp)⟩
  rw [fun_meromorphicOrderAt_div hn.meromorphicAt hd.meromorphicAt, hno,
    polynomial_meromorphic_order f.denom f.denom_ne_zero a]
  simp

/-- Every reduced-denominator root is an actual pole: the quotient escapes
all bounded subsets as the argument approaches that root through punctured neighborhoods. -/
theorem rational_tendsto_cobounded_at_pole (f : RatFunc ℂ) (a : ℂ)
    (ha : f.denom.eval a = 0) :
    Filter.Tendsto (fun z => f.num.eval z / f.denom.eval z)
      (𝓝[≠] a) (Bornology.cobounded ℂ) := by
  apply tendsto_cobounded_of_meromorphicOrderAt_neg
  rw [rational_pole_order f a ha]
  have hm : 0 < f.denom.rootMultiplicity a :=
    (rootMultiplicity_pos f.denom_ne_zero).2 ha
  have hmz : 0 < (f.denom.rootMultiplicity a : ℤ) := by exact_mod_cast hm
  exact_mod_cast (neg_neg_of_pos hmz)

/-- Away from its denominator roots, the reduced quotient is holomorphic. -/
theorem rational_differentiableAt_of_denom_ne_zero (f : RatFunc ℂ) (a : ℂ)
    (ha : f.denom.eval a ≠ 0) :
    DifferentiableAt ℂ (fun z => f.num.eval z / f.denom.eval z) a :=
  f.num.differentiableAt.div f.denom.differentiableAt ha

#print axioms rational_reduced_representation
#print axioms rational_partial_fractions_coefficients
#print axioms rational_partial_fractions_polynomials
#print axioms linear_partial_fractions_in_algebra
#print axioms rational_partial_fractions_with_evaluation
#print axioms rational_principal_part_remainder
#print axioms rational_quotient_evaluation
#print axioms polynomial_meromorphic_order
#print axioms rational_pole_order
#print axioms rational_tendsto_cobounded_at_pole
#print axioms rational_differentiableAt_of_denom_ne_zero

end RudinRCA.Chapter13
end Source1

/- Source: StripComponents.lean -/
noncomputable section Source2

open Set

namespace RudinRCA.Chapter13

private theorem strip_component_avoids_half {z w : ℂ}
    (hw : w ∈ connectedComponentIn horizontalStripᶜ z) : w.im ≠ 1 / 2 := by
  have hn := connectedComponentIn_subset horizontalStripᶜ z hw
  change ¬ (0 < w.im ∧ w.im < 1) at hn
  intro heq
  apply hn
  constructor <;> linarith

theorem strip_component_lower {z : ℂ} (hz : z.im ≤ 0) :
    connectedComponentIn horizontalStripᶜ z = {w : ℂ | w.im ≤ 0} := by
  have hzout : z ∈ horizontalStripᶜ := fun h => (not_lt_of_ge hz) h.1
  apply Subset.antisymm
  · intro w hw
    have hside := isPreconnected_connectedComponentIn.gt_of_ne
      Complex.continuous_im.continuousOn
      (fun w hw => strip_component_avoids_half hw)
      ⟨z, mem_connectedComponentIn hzout, by linarith⟩ hw
    have hn := connectedComponentIn_subset horizontalStripᶜ z hw
    change ¬ (0 < w.im ∧ w.im < 1) at hn
    by_contra hpos
    apply hn
    exact ⟨lt_of_not_ge hpos, by linarith⟩
  · exact (convex_halfSpace_le (.mk Complex.add_im Complex.smul_im) 0).isPreconnected
      |>.subset_connectedComponentIn hz (fun w hw h => (not_lt_of_ge hw) h.1)

theorem strip_component_upper {z : ℂ} (hz : 1 ≤ z.im) :
    connectedComponentIn horizontalStripᶜ z = {w : ℂ | 1 ≤ w.im} := by
  have hzout : z ∈ horizontalStripᶜ := fun h => (not_lt_of_ge hz) h.2
  apply Subset.antisymm
  · intro w hw
    have hside := isPreconnected_connectedComponentIn.lt_of_ne
      Complex.continuous_im.continuousOn
      (fun w hw => strip_component_avoids_half hw)
      ⟨z, mem_connectedComponentIn hzout, by linarith⟩ hw
    have hn := connectedComponentIn_subset horizontalStripᶜ z hw
    change ¬ (0 < w.im ∧ w.im < 1) at hn
    by_contra hlt
    apply hn
    exact ⟨by linarith, lt_of_not_ge hlt⟩
  · exact (convex_halfSpace_ge (.mk Complex.add_im Complex.smul_im) 1).isPreconnected
      |>.subset_connectedComponentIn hz (fun w hw h => (not_lt_of_ge hw) h.2)

/-- The planar complement has exactly the two closed half-plane components. -/
theorem horizontalStrip_components :
    {s : Set ℂ | ∃ z ∈ horizontalStripᶜ, s = connectedComponentIn horizontalStripᶜ z} =
      {{w : ℂ | w.im ≤ 0}, {w : ℂ | 1 ≤ w.im}} := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ¬ (0 < z.im ∧ z.im < 1) at hz
    by_cases hlow : z.im ≤ 0
    · simp [strip_component_lower hlow]
    · have hhigh : 1 ≤ z.im := le_of_not_gt (fun h => hz ⟨lt_of_not_ge hlow, h⟩)
      simp [strip_component_upper hhigh]
  · intro hs
    rcases (show s = {w : ℂ | w.im ≤ 0} ∨ s = {w : ℂ | 1 ≤ w.im} from by simpa using hs)
      with rfl | rfl
    · exact ⟨0, by simp [horizontalStrip], (strip_component_lower (by simp)).symm⟩
    · exact ⟨Complex.I, by simp [horizontalStrip], (strip_component_upper (by simp)).symm⟩

#print axioms strip_component_avoids_half
#print axioms strip_component_lower
#print axioms strip_component_upper
#print axioms horizontalStrip_components

end RudinRCA.Chapter13
end Source2

/- Source: BalancedCycles.lean -/
noncomputable section Source3

open Function Equiv

namespace RudinRCA.Chapter13Scratch

universe u v

variable {E : Type u} {V : Type v} [Fintype E]

/-- Counting individual interval indices, rather than their endpoint pairs, preserves multiplicity. -/
theorem balanced_exists_successor [DecidableEq V] (initial terminal : E → V)
    (hbalanced : ∀ v, Fintype.card {e // initial e = v} =
      Fintype.card {e // terminal e = v}) :
    ∃ σ : Equiv.Perm E, ∀ e, terminal e = initial (σ e) := by
  let fibers : ∀ v, {e // terminal e = v} ≃ {e // initial e = v} :=
    fun v => Fintype.equivOfCardEq (hbalanced v).symm
  exact ⟨Equiv.ofFiberEquiv fibers, fun e => (Equiv.ofFiberEquiv_map fibers e).symm⟩

/-- A cyclic successor on a nonempty finite interval of indices. -/
def cycleNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

noncomputable def permutationOrbit (σ : Equiv.Perm E) (e : E) : Finset E := by
  classical
  exact Finset.univ.filter (σ.SameCycle e)

@[simp] theorem mem_permutationOrbit (σ : Equiv.Perm E) (e x : E) :
    x ∈ permutationOrbit σ e ↔ σ.SameCycle e x := by
  classical
  simp [permutationOrbit]

theorem permutationOrbit_nonempty (σ : Equiv.Perm E) (e : E) :
    (permutationOrbit σ e).Nonempty := by
  exact ⟨e, (mem_permutationOrbit σ e e).mpr Equiv.Perm.SameCycle.rfl⟩

theorem permutationOrbit_eq_of_sameCycle (σ : Equiv.Perm E) {e f : E}
    (h : σ.SameCycle e f) : permutationOrbit σ e = permutationOrbit σ f := by
  ext x
  simp only [mem_permutationOrbit]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

theorem isCycleOn_permutationOrbit (σ : Equiv.Perm E) (e : E) :
    σ.IsCycleOn (permutationOrbit σ e : Set E) := by
  refine ⟨σ.bijOn ?_, ?_⟩
  · intro x
    simp only [Finset.mem_coe, mem_permutationOrbit, Equiv.Perm.sameCycle_apply_right]
  · intro x hx y hy
    exact (mem_permutationOrbit σ e x |>.mp hx).symm.trans
      (mem_permutationOrbit σ e y |>.mp hy)

/-- A finite permutation orbit is explicitly enumerated without repetition, with cyclic successor. -/
theorem enumerate_permutationOrbit (σ : Equiv.Perm E) (a : E) :
    ∃ hpos : 0 < (permutationOrbit σ a).card,
      ∃ edge : Fin (permutationOrbit σ a).card → E,
        Injective edge ∧
        (∀ x, x ∈ permutationOrbit σ a ↔ ∃ i, edge i = x) ∧
        ∀ i, σ (edge i) = edge (cycleNext hpos i) := by
  classical
  let s := permutationOrbit σ a
  have ha : a ∈ s := (mem_permutationOrbit σ a a).mpr Equiv.Perm.SameCycle.rfl
  have hs : σ.IsCycleOn (s : Set E) := isCycleOn_permutationOrbit σ a
  have hp : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  let edge : Fin s.card → E := fun i => (σ ^ (i : ℕ)) a
  refine ⟨hp, edge, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hmod := (hs.pow_apply_eq_pow_apply ha).mp hij
    change (i : ℕ) % s.card = (j : ℕ) % s.card at hmod
    rw [Nat.mod_eq_of_lt (show (i : ℕ) < s.card from i.isLt),
      Nat.mod_eq_of_lt (show (j : ℕ) < s.card from j.isLt)] at hmod
    exact hmod
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi, heq⟩ := hs.exists_pow_eq ha hx
      exact ⟨⟨i, hi⟩, heq⟩
    · rintro ⟨i, rfl⟩
      exact hs.1.mapsTo.perm_pow _ ha
  · intro i
    change σ ((σ ^ (i : ℕ)) a) = (σ ^ (((i : ℕ) + 1) % s.card)) a
    have heq : (σ ^ (((i : ℕ) + 1) % s.card)) a = (σ ^ ((i : ℕ) + 1)) a :=
      (hs.pow_apply_eq_pow_apply ha).mpr (Nat.mod_modEq _ _)
    rw [heq, pow_succ', Equiv.Perm.mul_apply]

/-- Rudin RCA 13.4: a balanced finite family of directed intervals decomposes into finitely
many closed polygonal edge sequences. Each supplied index occurs in exactly one component,
and each component's enumeration is injective and covers its support.

Take `V = ℂ` to obtain the printed result for oriented complex line intervals. Distinct indices
may have the same endpoints, so the theorem retains interval multiplicities. -/
theorem balanced_closed_cycle_partition [DecidableEq E] [DecidableEq V]
    (initial terminal : E → V)
    (hbalanced : ∀ v, Fintype.card {e // initial e = v} =
      Fintype.card {e // terminal e = v}) :
    ∃ cycles : Finset (Finset E),
      (∀ e : E, ∃! s : Finset E, s ∈ cycles ∧ e ∈ s) ∧
      ∀ s ∈ cycles, ∃ hpos : 0 < s.card, ∃ edge : Fin s.card → E,
        Injective edge ∧ (∀ e, e ∈ s ↔ ∃ i, edge i = e) ∧
        ∀ i, terminal (edge i) = initial (edge (cycleNext hpos i)) := by
  classical
  obtain ⟨σ, hσ⟩ := balanced_exists_successor initial terminal hbalanced
  let cycles := Finset.univ.image (permutationOrbit σ)
  refine ⟨cycles, ?_, ?_⟩
  · intro e
    refine ⟨permutationOrbit σ e, ⟨?_,
      (mem_permutationOrbit σ e e).mpr Equiv.Perm.SameCycle.rfl⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    · intro s hs
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs.1
      exact permutationOrbit_eq_of_sameCycle σ ((mem_permutationOrbit σ a e).mp hs.2)
  · intro s hs
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hpos, edge, hinj, hcover, hnext⟩ := enumerate_permutationOrbit σ a
    refine ⟨hpos, edge, hinj, hcover, ?_⟩
    intro i
    rw [hσ, hnext]

#print axioms balanced_exists_successor
#print axioms mem_permutationOrbit
#print axioms permutationOrbit_nonempty
#print axioms permutationOrbit_eq_of_sameCycle
#print axioms isCycleOn_permutationOrbit
#print axioms enumerate_permutationOrbit
#print axioms balanced_closed_cycle_partition

end RudinRCA.Chapter13Scratch
end Source3

/- Source: Exhaustion.lean -/
noncomputable section Source4

open Set Filter Metric
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- The explicit compact exhaustion in 13.3, with the book's positive index shifted by one. -/
def exhaustionLevel (Ω : Set ℂ) (n : ℕ) : Set ℂ :=
  closedBall 0 ((n : ℝ) + 1) ∩
    {z | ∀ a ∉ Ω, ((n : ℝ) + 1)⁻¹ ≤ dist z a}

theorem exhaustionLevel_subset (Ω : Set ℂ) (n : ℕ) : exhaustionLevel Ω n ⊆ Ω := by
  intro z hz
  by_contra hzΩ
  have hh := hz.2 z hzΩ
  simp only [dist_self] at hh
  have hp : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

theorem exhaustionLevel_isCompact (Ω : Set ℂ) (n : ℕ) : IsCompact (exhaustionLevel Ω n) := by
  apply (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)).inter_right
  simp only [ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem exhaustionLevel_mono (Ω : Set ℂ) : Monotone (exhaustionLevel Ω) := by
  intro n m hnm z hz
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
  refine ⟨closedBall_subset_closedBall hnm' hz.1, fun a ha ↦ ?_⟩
  exact (inv_anti₀ (by positivity) hnm').trans (hz.2 a ha)

theorem exhaustionLevel_subset_interior_succ (Ω : Set ℂ) (n : ℕ) :
    exhaustionLevel Ω n ⊆ interior (exhaustionLevel Ω (n + 1)) := by
  intro z hz
  let r : ℝ := min 1 (((n : ℝ) + 1)⁻¹ - (((n + 1 : ℕ) : ℝ) + 1)⁻¹)
  have hstep : (n : ℝ) + 1 < ((n + 1 : ℕ) : ℝ) + 1 := by norm_num
  have hinv : (((n + 1 : ℕ) : ℝ) + 1)⁻¹ < ((n : ℝ) + 1)⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by positivity)).2 hstep
  have hr : 0 < r := lt_min zero_lt_one (sub_pos.mpr hinv)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrd : r ≤ ((n : ℝ) + 1)⁻¹ - (((n + 1 : ℕ) : ℝ) + 1)⁻¹ := min_le_right _ _
  refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, ?_⟩)
  intro w hw
  have hwz : dist w z < r := hw
  refine ⟨?_, fun a ha ↦ ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    have htri : ‖w‖ ≤ dist w z + ‖z‖ := by
      simpa [dist_eq_norm] using norm_add_le (w - z) z
    have hzn : ‖z‖ ≤ (n : ℝ) + 1 := by simpa [mem_closedBall] using hz.1
    norm_num at hstep ⊢
    linarith
  · have htri := dist_triangle z w a
    rw [dist_comm z w] at htri
    have hza := hz.2 a ha
    linarith

theorem exists_mem_exhaustionLevel {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    ∃ n, z ∈ exhaustionLevel Ω n := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ δ⁻¹)
  have hnz : ‖z‖ < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnδ : δ⁻¹ < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnδ' : ((n : ℝ) + 1)⁻¹ ≤ δ := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    have hnδdiv : 1 / δ < (n : ℝ) := by simpa only [one_div] using hnδ
    have hd : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hnδdiv
    nlinarith
  refine ⟨n, ?_, fun a ha ↦ hnδ'.trans ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    linarith
  · by_contra hdist
    have : a ∈ ball z δ := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hdist
    exact ha (hball this)

theorem iUnion_exhaustionLevel {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ⋃ n, exhaustionLevel Ω n = Ω := by
  ext z
  simp only [mem_iUnion]
  exact ⟨fun ⟨n, hz⟩ ↦ exhaustionLevel_subset Ω n hz,
    fun hz ↦ exists_mem_exhaustionLevel hΩ hz⟩

theorem compact_subset_exhaustionLevel {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ n, K ⊆ exhaustionLevel Ω n := by
  have hmono : Monotone (fun n ↦ interior (exhaustionLevel Ω n)) :=
    fun _ _ hnm ↦ interior_mono (exhaustionLevel_mono Ω hnm)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n ↦ interior (exhaustionLevel Ω n))
    (fun _ ↦ isOpen_interior) (fun z hz ↦ by
      obtain ⟨n, hn⟩ := exists_mem_exhaustionLevel hΩ (hKΩ hz)
      exact mem_iUnion.mpr ⟨n + 1, exhaustionLevel_subset_interior_succ Ω n hn⟩)
    hmono.directed_le
  exact ⟨n, hn.trans interior_subset⟩

/-- Local connected pieces meeting `A` ensure that each component of `T` contains
    a component of `A`. -/
theorem component_contains_component_of_local_pieces {X : Type*} [TopologicalSpace X]
    {A T : Set X} (hAT : A ⊆ T)
    (hpieces : ∀ x ∈ T, ∃ S : Set X, x ∈ S ∧ S ⊆ T ∧ IsPreconnected S ∧ (S ∩ A).Nonempty) :
    ∀ x ∈ T, ∃ a ∈ A, connectedComponentIn A a ⊆ connectedComponentIn T x := by
  intro x hx
  obtain ⟨S, hxS, hST, hS, a, haS, haA⟩ := hpieces x hx
  refine ⟨a, haA, ?_⟩
  have haT := hS.subset_connectedComponentIn hxS hST haS
  rw [connectedComponentIn_eq haT]
  exact connectedComponentIn_mono a hAT

/-- The forward radial ray from a nonzero complex point is connected and unbounded. -/
theorem radialRay_connected_unbounded (z : ℂ) (hz : z ≠ 0) :
    IsConnected ((fun t : ℝ ↦ t • z) '' Ici 1) ∧
    (∀ r > 0, ∃ w ∈ ((fun t : ℝ ↦ t • z) '' Ici 1), r < ‖w‖) := by
  refine ⟨isConnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn, ?_⟩
  intro r hr
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let t : ℝ := r / ‖z‖ + 1
  have ht : 1 ≤ t := by
    dsimp [t]
    linarith [div_nonneg hr.le hzpos.le]
  refine ⟨t • z, mem_image_of_mem _ ht, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
  dsimp [t]
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hzpos), one_mul]
  linarith

theorem exhaustionLevel_complement_components (Ω : Set ℂ) (n : ℕ) :
    ∀ x ∈ (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ,
      ∃ a ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
        connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ a ⊆
          connectedComponentIn (((↑) : ℂ → RiemannSphere) '' exhaustionLevel Ω n)ᶜ x := by
  apply component_contains_component_of_local_pieces
  · exact compl_subset_compl.mpr (image_mono (exhaustionLevel_subset Ω n))
  intro x hx
  induction x using OnePoint.rec with
  | infty =>
    refine ⟨{∞}, by simp, ?_, isPreconnected_singleton, ?_⟩
    · simpa using hx
    · exact ⟨∞, by simp, by simp⟩
  | coe z =>
    have hzK : z ∉ exhaustionLevel Ω n := by simpa using hx
    by_cases hzlarge : (n : ℝ) + 1 < ‖z‖
    · let S : Set ℂ := (fun t : ℝ ↦ t • z) '' Ici 1
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity : 0 < (n : ℝ) + 1) hzlarge.le
      obtain ⟨hS, huS⟩ := radialRay_connected_unbounded z (norm_pos_iff.mp hzpos)
      refine ⟨insert ∞ ((↑) '' S), ?_, ?_,
        (isConnected_insert_infinity hS huS).isPreconnected, ?_⟩
      · apply mem_insert_of_mem
        exact mem_image_of_mem _ ⟨1, by simp, by simp⟩
      · intro y hy
        rcases hy with rfl | ⟨w, ⟨t, ht, rfl⟩, rfl⟩
        · simp
        · simp only [mem_compl_iff, OnePoint.coe_injective.mem_set_image]
          intro hw
          have hnorm : ‖t • z‖ = t * ‖z‖ :=
            by rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
          have hlarge : (n : ℝ) + 1 < ‖t • z‖ := by
            rw [hnorm]
            exact hzlarge.trans_le (le_mul_of_one_le_left hzpos.le ht)
          exact (not_lt_of_ge (by simpa [mem_closedBall] using hw.1)) hlarge
      · exact ⟨∞, by simp, by simp⟩
    · have hznorm : ‖z‖ ≤ (n : ℝ) + 1 := le_of_not_gt hzlarge
      have hsep : ¬∀ a ∉ Ω, ((n : ℝ) + 1)⁻¹ ≤ dist z a := by
        intro h
        exact hzK ⟨by simpa [mem_closedBall] using hznorm, h⟩
      push_neg at hsep
      obtain ⟨a, haΩ, hza⟩ := hsep
      let S : Set ℂ := ball a ((n : ℝ) + 1)⁻¹
      refine ⟨((↑) : ℂ → RiemannSphere) '' S, mem_image_of_mem _ hza, ?_,
        isPreconnected_ball.image _ OnePoint.continuous_coe.continuousOn, ?_⟩
      · rintro y ⟨w, hw, rfl⟩
        simp only [mem_compl_iff, OnePoint.coe_injective.mem_set_image]
        intro hwK
        exact not_lt_of_ge (hwK.2 a haΩ) hw
      · refine ⟨(a : RiemannSphere), mem_image_of_mem _ (mem_ball_self (by positivity)), ?_⟩
        simpa using haΩ

/-- Rudin 13.3, all clauses including the spherical complement component condition. -/
theorem compact_exhaustion_with_spherical_complement_components {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set ℂ,
      (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ Ω) ∧
      (⋃ n, K n) = Ω ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ Ω → ∃ n, L ⊆ K n) ∧
      (∀ n x, x ∈ (((↑) : ℂ → RiemannSphere) '' K n)ᶜ →
        ∃ a ∈ (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ,
          connectedComponentIn (((↑) : ℂ → RiemannSphere) '' Ω)ᶜ a ⊆
            connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K n)ᶜ x) :=
  ⟨exhaustionLevel Ω, exhaustionLevel_isCompact Ω, exhaustionLevel_subset Ω,
    iUnion_exhaustionLevel hΩ, exhaustionLevel_subset_interior_succ Ω,
    fun _ hL hLΩ ↦ compact_subset_exhaustionLevel hΩ hL hLΩ,
    exhaustionLevel_complement_components Ω⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.compact_exhaustion_with_spherical_complement_components
end Source4

/- Source: PolynomialObstruction.lean -/
noncomputable section Source5

open Set Filter Metric
open scoped Topology OnePoint
namespace RudinRCA.Chapter13

/-- The spherical complementary components, represented as sets rather than a choice of labels. -/
def sphericalComplementComponents (K : Set ℂ) : Set (Set RiemannSphere) :=
  {C | ∃ x ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
    C = connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ x}

/-- The countability observation in13.6. Closedness is enough for this assertion. -/
theorem countable_spherical_complement_components {K : Set ℂ} (hK : IsClosed K) :
    (sphericalComplementComponents K).Countable := by
  let T : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  let B : Set (Set RiemannSphere) :=
    {C | C ∈ sphericalComplementComponents K ∧ (((↑) : ℂ → RiemannSphere) ⁻¹' C).Nonempty}
  have hdis : B.PairwiseDisjoint (fun C => ((↑) : ℂ → RiemannSphere) ⁻¹' C) := by
    intro C hC D hD hne
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    apply hne
    obtain ⟨x, _, rfl⟩ := hC.1
    obtain ⟨y, _, rfl⟩ := hD.1
    exact (connectedComponentIn_eq hzC).trans (connectedComponentIn_eq hzD).symm
  have hopen : ∀ C ∈ B, IsOpen (((↑) : ℂ → RiemannSphere) ⁻¹' C) := by
    intro C hC
    obtain ⟨x, _, rfl⟩ := hC.1
    rw [OnePoint.continuous_coe.continuousOn.preimage_connectedComponentIn]
    apply isOpen_biUnion
    intro a _
    have heq : ((↑) : ℂ → RiemannSphere) ⁻¹' T = Kᶜ := by
      ext z
      simp [T]
    change IsOpen (connectedComponentIn (((↑) : ℂ → RiemannSphere) ⁻¹' T) a)
    rw [heq]
    exact hK.isOpen_compl.connectedComponentIn
  have hB : B.Countable := hdis.countable_of_isOpen hopen (fun _ h => h.2)
  apply (hB.insert {∞}).mono
  intro C hC
  by_cases hfinite : (((↑) : ℂ → RiemannSphere) ⁻¹' C).Nonempty
  · exact mem_insert_of_mem _ ⟨hC, hfinite⟩
  · left
    apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
    constructor
    · obtain ⟨x, hx, rfl⟩ := hC
      exact ⟨x, mem_connectedComponentIn hx⟩
    · intro x hx
      induction x using OnePoint.rec with
      | infty => rfl
      | coe z => exact False.elim (hfinite ⟨z, hx⟩)

/-- A disconnected spherical complement has a bounded component in the finite chart. -/
theorem exists_bounded_complement_component {K : Set ℂ}
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ a ∉ K, Bornology.IsBounded (connectedComponentIn Kᶜ a) := by
  by_contra! hall
  apply hdisc
  let T : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  have hinf : (∞ : RiemannSphere) ∈ T := by simp [T]
  have hsub : T ⊆ connectedComponentIn T ∞ := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact mem_connectedComponentIn hinf
    | coe a =>
      have ha : a ∉ K := by simpa [T] using hx
      have hu : ∀ r > 0, ∃ z ∈ connectedComponentIn Kᶜ a, r < ‖z‖ := by
        intro r _
        by_contra! hr
        exact hall a ha (isBounded_iff_forall_norm_le.mpr ⟨r, hr⟩)
      have hc := isConnected_insert_infinity
        (isConnected_connectedComponentIn_iff.mpr ha) hu
      have hCT : insert (∞ : RiemannSphere)
          (((↑) : ℂ → RiemannSphere) '' connectedComponentIn Kᶜ a) ⊆ T := by
        intro y hy
        rcases hy with rfl | ⟨z, hz, rfl⟩
        · exact hinf
        · simpa [T] using connectedComponentIn_subset Kᶜ a hz
      have hC := hc.isPreconnected.subset_connectedComponentIn (mem_insert _ _) hCT
      exact hC (mem_insert_of_mem _ (mem_image_of_mem _ (mem_connectedComponentIn ha)))
  have heq : connectedComponentIn T ∞ = T := (connectedComponentIn_subset _ _).antisymm hsub
  change IsConnected T
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr hinf

/-- The boundary of a component of the complement of a closed planar set lies in that set. -/
theorem frontier_complement_component_subset {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  intro z hz
  by_contra hzK
  have hzopen : IsOpen (connectedComponentIn Kᶜ z) := hK.isOpen_compl.connectedComponentIn
  have hzC : z ∈ connectedComponentIn Kᶜ z := mem_connectedComponentIn hzK
  obtain ⟨w, hwz, hwa⟩ := _root_.mem_closure_iff.mp hz.1 _ hzopen hzC
  have heq : connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ z :=
    (connectedComponentIn_eq hwa).trans (connectedComponentIn_eq hwz).symm
  have haopen : IsOpen (connectedComponentIn Kᶜ a) := hK.isOpen_compl.connectedComponentIn
  apply hz.2
  rw [haopen.interior_eq, heq]
  exact hzC

/-- Maximum-modulus obstruction underlying13.8, for any holomorphic candidate on the
closure of the omitted complementary component. In particular this applies to every polynomial. -/
theorem reciprocal_approximation_obstruction {K V : Set ℂ} {a : ℂ} {m : ℝ}
    (hV : Bornology.IsBounded V) (haV : a ∈ V) (haK : a ∉ K)
    (hfront : frontier V ⊆ K) (hm : 0 < m)
    (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g V) :
    ¬ ∀ z ∈ K, ‖g z - (z - a)⁻¹‖ < m⁻¹ := by
  intro happrox
  let F : ℂ → ℂ := fun z => (z - a) * g z - 1
  have hF : DiffContOnCl ℂ F V :=
    ((differentiable_id.sub_const a).diffContOnCl.smul hg).sub_const 1
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hV ⟨a, haV⟩ hF
  have hwK := hfront hw
  have hwa : w - a ≠ 0 := sub_ne_zero.mpr (fun h => haK (h ▸ hwK))
  have heq : F w = (w - a) * (g w - (w - a)⁻¹) := by
    dsimp [F]
    rw [mul_sub, mul_inv_cancel₀ hwa]
  have hsmall : ‖F w‖ < 1 := by
    rw [heq, norm_mul]
    calc
      ‖w - a‖ * ‖g w - (w - a)⁻¹‖ < ‖w - a‖ * m⁻¹ :=
        mul_lt_mul_of_pos_left (happrox w hwK) (norm_pos_iff.mpr hwa)
      _ ≤ m * m⁻¹ := mul_le_mul_of_nonneg_right (hbound w hwK) (inv_nonneg.mpr hm.le)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hm)
  have hamax : ‖F a‖ ≤ ‖F w‖ := hmax (subset_closure haV)
  have hFa : ‖F a‖ = 1 := by simp [F]
  linarith

/-- Quantitative polynomial obstruction with any positive upper bound on distances to `a`. -/
theorem polynomial_approximation_obstruction {K : Set ℂ} (hK : IsClosed K)
    {a : ℂ} (ha : a ∉ K) (hb : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ z ∈ K, ‖z - a‖ ≤ m) (p : Polynomial ℂ) :
    ¬ ∀ z ∈ K, ‖p.eval z - (z - a)⁻¹‖ < m⁻¹ :=
  reciprocal_approximation_obstruction hb (mem_connectedComponentIn ha) ha
    (frontier_complement_component_subset hK a) hm hbound p.differentiable.diffContOnCl

/-- Printed13.8: a disconnected spherical complement yields a reciprocal function and
its exact positive maximum distance on `K`, with the stated obstruction for every polynomial. -/
theorem disconnected_spherical_complement_polynomial_obstruction {K : Set ℂ}
    (hK : IsCompact K)
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ a ∉ K, ∃ m > 0,
      (∃ z ∈ K, ‖z - a‖ = m) ∧ (∀ z ∈ K, ‖z - a‖ ≤ m) ∧
      ∀ p : Polynomial ℂ, ¬ ∀ z ∈ K, ‖p.eval z - (z - a)⁻¹‖ < m⁻¹ := by
  obtain ⟨a, ha, hb⟩ := exists_bounded_complement_component hdisc
  have hfront := frontier_complement_component_subset hK.isClosed a
  obtain ⟨w, hw, _⟩ := Complex.exists_mem_frontier_isMaxOn_norm hb
    ⟨a, mem_connectedComponentIn ha⟩ (differentiable_const (1 : ℂ)).diffContOnCl
  have hne : K.Nonempty := ⟨w, hfront hw⟩
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun w : ℂ => ‖w - a‖) K from
      (continuous_id.sub continuous_const).norm.continuousOn)
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hz))
  refine ⟨a, ha, ‖z - a‖, norm_pos_iff.mpr hza, ⟨z, hz, rfl⟩, ?_, ?_⟩
  · exact fun y hy => hmax hy
  · exact fun p => polynomial_approximation_obstruction hK.isClosed ha hb
      (norm_pos_iff.mpr hza) (fun y hy => hmax hy) p

/-- The counterexample in13.8 is holomorphic on an open neighborhood of `K` and is
not a uniform limit of polynomial functions on `K`. -/
theorem exists_holomorphic_not_polynomial_uniform_limit {K : Set ℂ}
    (hK : IsCompact K)
    (hdisc : ¬ IsConnected (((↑) : ℂ → RiemannSphere) '' K)ᶜ) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ K ⊆ Ω ∧ ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f Ω ∧
      ¬ ∃ p : ℕ → Polynomial ℂ,
        TendstoUniformlyOn (fun n z => (p n).eval z) f atTop K := by
  obtain ⟨a, ha, m, hm, _, _, hobstruct⟩ :=
    disconnected_spherical_complement_polynomial_obstruction hK hdisc
  refine ⟨{a}ᶜ, isClosed_singleton.isOpen_compl, ?_, fun z => (z - a)⁻¹, ?_, ?_⟩
  · intro z hz hza
    exact ha ((mem_singleton_iff.mp hza) ▸ hz)
  · intro z hz
    exact ((differentiableAt_id.sub_const a).inv
      (sub_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff, id_eq] using hz))).differentiableWithinAt
  · rintro ⟨p, hp⟩
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hp m⁻¹ (inv_pos.mpr hm)).exists
    apply hobstruct (p n)
    intro z hz
    simpa only [dist_eq_norm, norm_sub_rev] using hn z hz

#print axioms sphericalComplementComponents
#print axioms countable_spherical_complement_components
#print axioms exists_bounded_complement_component
#print axioms frontier_complement_component_subset
#print axioms reciprocal_approximation_obstruction
#print axioms polynomial_approximation_obstruction
#print axioms disconnected_spherical_complement_polynomial_obstruction
#print axioms exists_holomorphic_not_polynomial_uniform_limit
end RudinRCA.Chapter13
end Source5

/- Source: SquareKernel.lean -/
noncomputable section Source6

open Complex intervalIntegral

namespace RudinRCA.Chapter13Scratch

theorem square_kernel_integrand (t : ℝ) :
    ((t : ℂ) - I)⁻¹ - ((t : ℂ) + I)⁻¹ +
      I * (1 + (t : ℂ) * I)⁻¹ - I * (-1 + (t : ℂ) * I)⁻¹ =
      4 * I * ((1 / (1 + t ^ 2) : ℝ) : ℂ) := by
  have h₁ : (t : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h₂ : (t : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h₃ : 1 + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h₄ : -1 + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h₅ : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + t ^ 2 by positivity))
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq, pow_succ]
  <;> ring

/-- The positively oriented unit-square boundary integral of `1 / z` is `2πi`.
The four summands are bottom, top (reversed), right, and left (reversed). -/
theorem unit_square_kernel :
    (∫ t : ℝ in -1..1, ((t : ℂ) - I)⁻¹) -
      (∫ t : ℝ in -1..1, ((t : ℂ) + I)⁻¹) +
      I * (∫ t : ℝ in -1..1, (1 + (t : ℂ) * I)⁻¹) -
      I * (∫ t : ℝ in -1..1, (-1 + (t : ℂ) * I)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  have h₁ : Continuous (fun t : ℝ => ((t : ℂ) - I)⁻¹) := by
    refine (Complex.continuous_ofReal.sub continuous_const).inv₀ ?_
    intro t h
    have := congrArg Complex.im h
    norm_num at this
  have h₂ : Continuous (fun t : ℝ => ((t : ℂ) + I)⁻¹) := by
    refine (Complex.continuous_ofReal.add continuous_const).inv₀ ?_
    intro t h
    have := congrArg Complex.im h
    norm_num at this
  have h₃ : Continuous (fun t : ℝ => (1 + (t : ℂ) * I)⁻¹) := by
    refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
    intro t h
    have := congrArg Complex.re h
    norm_num at this
  have h₄ : Continuous (fun t : ℝ => (-1 + (t : ℂ) * I)⁻¹) := by
    refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
    intro t h
    have := congrArg Complex.re h
    norm_num at this
  have hi₁ : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - I)⁻¹)
      MeasureTheory.volume (-1) 1 := h₁.intervalIntegrable (-1) 1
  have hi₂ : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + I)⁻¹)
      MeasureTheory.volume (-1) 1 := h₂.intervalIntegrable (-1) 1
  have hi₃ : IntervalIntegrable (fun t : ℝ => I * (1 + (t : ℂ) * I)⁻¹)
      MeasureTheory.volume (-1) 1 := (h₃.intervalIntegrable (-1) 1).const_mul I
  have hi₄ : IntervalIntegrable (fun t : ℝ => I * (-1 + (t : ℂ) * I)⁻¹)
      MeasureTheory.volume (-1) 1 := (h₄.intervalIntegrable (-1) 1).const_mul I
  calc
    _ = ∫ t : ℝ in -1..1, (((t : ℂ) - I)⁻¹ - ((t : ℂ) + I)⁻¹ +
        I * (1 + (t : ℂ) * I)⁻¹ - I * (-1 + (t : ℂ) * I)⁻¹) := by
      rw [integral_sub ((hi₁.sub hi₂).add hi₃) hi₄,
        integral_add (hi₁.sub hi₂) hi₃, integral_sub hi₁ hi₂,
        integral_const_mul, integral_const_mul]
    _ = ∫ t : ℝ in -1..1, 4 * I * ((1 / (1 + t ^ 2) : ℝ) : ℂ) := by
      apply integral_congr
      intro t ht
      exact square_kernel_integrand t
    _ = 2 * (Real.pi : ℂ) * I := by
      rw [integral_const_mul, intervalIntegral.integral_ofReal, integral_one_div_one_add_sq,
        Real.arctan_neg, Real.arctan_one]
      push_cast
      ring

#print axioms square_kernel_integrand
#print axioms unit_square_kernel

theorem integral_scaled_affine_inv {r : ℝ} (hr : r ≠ 0) (a b : ℂ) :
    (∫ t : ℝ in -r..r, ((r : ℂ) * a + (t : ℂ) * b)⁻¹) =
      ∫ t : ℝ in -1..1, (a + (t : ℂ) * b)⁻¹ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have h := smul_integral_comp_mul_left
    (fun t : ℝ => ((r : ℂ) * a + (t : ℂ) * b)⁻¹) (a := -1) (b := 1) r
  simp only [mul_neg_one, mul_one] at h
  rw [← h, ← integral_smul]
  apply integral_congr
  intro t ht
  change (r : ℂ) * ((r : ℂ) * a + ((r * t : ℝ) : ℂ) * b)⁻¹ = _
  push_cast
  rw [show (r : ℂ) * a + (r : ℂ) * (t : ℂ) * b =
    (r : ℂ) * (a + (t : ℂ) * b) by ring, mul_inv_rev]
  calc
    _ = ((a + (t : ℂ) * b)⁻¹) * ((r : ℂ) * (r : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hrC, mul_one]

/-- Positively oriented boundary integral of the centered square with side length `2r`.
This is the local normalization needed in the polygonal Cauchy construction. -/
theorem centered_square_kernel {r : ℝ} (hr : r ≠ 0) :
    (∫ t : ℝ in -r..r, ((t : ℂ) - (r : ℂ) * I)⁻¹) -
      (∫ t : ℝ in -r..r, ((t : ℂ) + (r : ℂ) * I)⁻¹) +
      I * (∫ t : ℝ in -r..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) -
      I * (∫ t : ℝ in -r..r, (-(r : ℂ) + (t : ℂ) * I)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  have hb : (∫ t : ℝ in -r..r, ((t : ℂ) - (r : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, ((t : ℂ) - I)⁻¹ := by
    simpa [sub_eq_add_neg, add_comm] using integral_scaled_affine_inv hr (-I) 1
  have ht : (∫ t : ℝ in -r..r, ((t : ℂ) + (r : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, ((t : ℂ) + I)⁻¹ := by
    simpa [add_comm] using integral_scaled_affine_inv hr I 1
  have hr' : (∫ t : ℝ in -r..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, (1 + (t : ℂ) * I)⁻¹ := by
    simpa using integral_scaled_affine_inv hr 1 I
  have hl : (∫ t : ℝ in -r..r, (-(r : ℂ) + (t : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, (-1 + (t : ℂ) * I)⁻¹ := by
    simpa using integral_scaled_affine_inv hr (-1) I
  rw [hb, ht, hr', hl]
  exact unit_square_kernel

/-- Counterclockwise boundary integral on an axis-parallel rectangle. -/
noncomputable def rectangleIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
    (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * I)) -
      (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * I)) +
      I * (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * I))

theorem rectangleIntegral_eq_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectangleIntegral f a b c d = 0 := by
  simpa [rectangleIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) (by simpa using hf)

theorem rectangle_kernel_zero_of_horizontal (a b c d : ℝ)
    (h : (0 : ℝ) ∉ Set.uIcc c d) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  apply differentiableOn_id.inv
  intro z hz heq
  apply h
  simpa [heq] using hz.2

theorem rectangle_kernel_zero_of_vertical (a b c d : ℝ)
    (h : (0 : ℝ) ∉ Set.uIcc a b) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  apply differentiableOn_id.inv
  intro z hz heq
  apply h
  simpa [heq] using hz.1

#print axioms integral_scaled_affine_inv
#print axioms centered_square_kernel
#print axioms rectangleIntegral_eq_zero
#print axioms rectangle_kernel_zero_of_horizontal
#print axioms rectangle_kernel_zero_of_vertical

theorem rectangleIntegral_split_vertical (f : ℂ → ℂ) (a b c d e : ℝ)
    (ha : Continuous (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)))
    (hb : Continuous (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I))) :
    rectangleIntegral f a b c e =
      rectangleIntegral f a b c d + rectangleIntegral f a b d e := by
  have hA := integral_add_adjacent_intervals
    (ha.intervalIntegrable (μ := MeasureTheory.volume) (a := c) (b := d))
    (ha.intervalIntegrable (μ := MeasureTheory.volume) (a := d) (b := e))
  have hB := integral_add_adjacent_intervals
    (hb.intervalIntegrable (μ := MeasureTheory.volume) (a := c) (b := d))
    (hb.intervalIntegrable (μ := MeasureTheory.volume) (a := d) (b := e))
  dsimp [rectangleIntegral]
  rw [← hA, ← hB]
  ring

theorem rectangleIntegral_split_horizontal (f : ℂ → ℂ) (a b c d e : ℝ)
    (hc : Continuous (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)))
    (hd : Continuous (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))) :
    rectangleIntegral f a e c d =
      rectangleIntegral f a b c d + rectangleIntegral f b e c d := by
  have hC := integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b))
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (a := b) (b := e))
  have hD := integral_add_adjacent_intervals
    (hd.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b))
    (hd.intervalIntegrable (μ := MeasureTheory.volume) (a := b) (b := e))
  dsimp [rectangleIntegral]
  rw [← hC, ← hD]
  ring

theorem continuous_horizontal_kernel {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I)⁻¹) := by
  refine (Complex.continuous_ofReal.add continuous_const).inv₀ ?_
  intro t h
  apply hc
  simpa using congrArg Complex.im h

theorem continuous_vertical_kernel {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I)⁻¹) := by
  refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
  intro t h
  apply hc
  simpa using congrArg Complex.re h

/-- Kernel normalization on every axis-parallel rectangle containing the origin in its interior.
The proof excises a smaller centered square using four rectangles avoiding the singularity. -/
theorem rectangle_kernel {a b c d : ℝ} (ha : a < 0) (hb : 0 < b)
    (hc : c < 0) (hd : 0 < d) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  let r := min (min (-a) b) (min (-c) d) / 2
  have hmin : 0 < min (min (-a) b) (min (-c) d) :=
    lt_min (lt_min (neg_pos.mpr ha) hb) (lt_min (neg_pos.mpr hc) hd)
  have hr : 0 < r := half_pos hmin
  have hsmall : r < min (min (-a) b) (min (-c) d) := half_lt_self hmin
  have hra : a < -r := by
    have := hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hrb : r < b := hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrc : c < -r := by
    have := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hrd : r < d := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hV₁ := rectangleIntegral_split_vertical (fun z : ℂ => z⁻¹) a b c (-r) d
    (continuous_vertical_kernel (ne_of_lt ha)) (continuous_vertical_kernel (ne_of_gt hb))
  have hV₂ := rectangleIntegral_split_vertical (fun z : ℂ => z⁻¹) a b (-r) r d
    (continuous_vertical_kernel (ne_of_lt ha)) (continuous_vertical_kernel (ne_of_gt hb))
  have hH₁ := rectangleIntegral_split_horizontal (fun z : ℂ => z⁻¹) a (-r) (-r) r b
    (continuous_horizontal_kernel (neg_ne_zero.mpr (ne_of_gt hr)))
    (continuous_horizontal_kernel (ne_of_gt hr))
  have hH₂ := rectangleIntegral_split_horizontal (fun z : ℂ => z⁻¹) (-r) r (-r) r b
    (continuous_horizontal_kernel (neg_ne_zero.mpr (ne_of_gt hr)))
    (continuous_horizontal_kernel (ne_of_gt hr))
  have hbottom : rectangleIntegral (fun z : ℂ => z⁻¹) a b c (-r) = 0 := by
    apply rectangle_kernel_zero_of_horizontal
    rw [Set.uIcc_of_le hrc.le]
    intro h
    linarith [h.2]
  have htop : rectangleIntegral (fun z : ℂ => z⁻¹) a b r d = 0 := by
    apply rectangle_kernel_zero_of_horizontal
    rw [Set.uIcc_of_le hrd.le]
    intro h
    linarith [h.1]
  have hleft : rectangleIntegral (fun z : ℂ => z⁻¹) a (-r) (-r) r = 0 := by
    apply rectangle_kernel_zero_of_vertical
    rw [Set.uIcc_of_le hra.le]
    intro h
    linarith [h.2]
  have hright : rectangleIntegral (fun z : ℂ => z⁻¹) r b (-r) r = 0 := by
    apply rectangle_kernel_zero_of_vertical
    rw [Set.uIcc_of_le hrb.le]
    intro h
    linarith [h.1]
  rw [hV₁, hV₂, hH₁, hH₂, hbottom, htop, hleft, hright]
  simpa [rectangleIntegral, sub_eq_add_neg] using centered_square_kernel (ne_of_gt hr)

#print axioms rectangleIntegral_split_vertical
#print axioms rectangleIntegral_split_horizontal
#print axioms continuous_horizontal_kernel
#print axioms continuous_vertical_kernel
#print axioms rectangle_kernel

theorem rectangleIntegral_translate (f : ℂ → ℂ) (a b c d : ℝ) (z : ℂ) :
    rectangleIntegral (fun w => f (w + z)) a b c d =
      rectangleIntegral f (a + z.re) (b + z.re) (c + z.im) (d + z.im) := by
  have hh (q : ℝ) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (q : ℂ) * I + z)) =
      ∫ x : ℝ in a + z.re..b + z.re, f ((x : ℂ) + ((q + z.im : ℝ) : ℂ) * I) := by
    calc
      _ = ∫ x : ℝ in a..b,
          f (((x + z.re : ℝ) : ℂ) + ((q + z.im : ℝ) : ℂ) * I) := by
        apply integral_congr
        intro x hx
        apply congrArg f
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right
        (fun x : ℝ => f ((x : ℂ) + ((q + z.im : ℝ) : ℂ) * I)) (a := a) (b := b) z.re
  have hv (q : ℝ) :
      (∫ y : ℝ in c..d, f ((q : ℂ) + (y : ℂ) * I + z)) =
      ∫ y : ℝ in c + z.im..d + z.im, f (((q + z.re : ℝ) : ℂ) + (y : ℂ) * I) := by
    calc
      _ = ∫ y : ℝ in c..d,
          f (((q + z.re : ℝ) : ℂ) + ((y + z.im : ℝ) : ℂ) * I) := by
        apply integral_congr
        intro y hy
        apply congrArg f
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right
        (fun y : ℝ => f (((q + z.re : ℝ) : ℂ) + (y : ℂ) * I)) (a := c) (b := d) z.im
  dsimp [rectangleIntegral]
  rw [hh, hh, hv, hv]

theorem rectangle_kernel_at {a b c d : ℝ} {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleIntegral (fun w : ℂ => (w - z)⁻¹) a b c d =
      2 * (Real.pi : ℂ) * I := by
  have ht := rectangleIntegral_translate (fun w : ℂ => (w - z)⁻¹)
    (a - z.re) (b - z.re) (c - z.im) (d - z.im) z
  simp only [add_sub_cancel_right, sub_add_cancel] at ht
  rw [← ht]
  exact rectangle_kernel (by linarith) (by linarith) (by linarith) (by linarith)

#print axioms rectangleIntegral_translate
#print axioms rectangle_kernel_at

structure RectangleBoundaryIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I))
    MeasureTheory.volume a b
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))
    MeasureTheory.volume a b
  right : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I))
    MeasureTheory.volume c d
  left : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I))
    MeasureTheory.volume c d

theorem rectangleBoundaryIntegrable_of_continuousOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    RectangleBoundaryIntegrable f a b c d := by
  have hh (q : ℝ) (hq : q ∈ Set.uIcc c d) :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + (q : ℂ) * I)) (Set.uIcc a b) := by
    refine hf.comp (by fun_prop) ?_
    intro x hx
    simpa [Complex.mem_reProdIm] using And.intro hx hq
  have hv (q : ℝ) (hq : q ∈ Set.uIcc a b) :
      ContinuousOn (fun y : ℝ => f ((q : ℂ) + (y : ℂ) * I)) (Set.uIcc c d) := by
    refine hf.comp (by fun_prop) ?_
    intro y hy
    simpa [Complex.mem_reProdIm] using And.intro hq hy
  exact ⟨(hh c (Set.left_mem_uIcc)).intervalIntegrable,
    (hh d (Set.right_mem_uIcc)).intervalIntegrable,
    (hv b (Set.right_mem_uIcc)).intervalIntegrable,
    (hv a (Set.left_mem_uIcc)).intervalIntegrable⟩

theorem rectangle_kernel_boundaryIntegrable {a b c d : ℝ} {z : ℂ}
    (ha : a ≠ z.re) (hb : b ≠ z.re) (hc : c ≠ z.im) (hd : d ≠ z.im) :
    RectangleBoundaryIntegrable (fun w : ℂ => (w - z)⁻¹) a b c d := by
  have hh (q : ℝ) (hq : q ≠ z.im) :
      Continuous (fun x : ℝ => ((x : ℂ) + (q : ℂ) * I - z)⁻¹) := by
    refine ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀ ?_
    intro x h
    apply hq
    have h' := congrArg Complex.im h
    have : q - z.im = 0 := by simpa using h'
    exact sub_eq_zero.mp this
  have hv (q : ℝ) (hq : q ≠ z.re) :
      Continuous (fun y : ℝ => ((q : ℂ) + (y : ℂ) * I - z)⁻¹) := by
    refine ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
      continuous_const).inv₀ ?_
    intro y h
    apply hq
    have h' := congrArg Complex.re h
    have : q - z.re = 0 := by simpa using h'
    exact sub_eq_zero.mp this
  exact ⟨(hh c hc).intervalIntegrable a b, (hh d hd).intervalIntegrable a b,
    (hv b hb).intervalIntegrable c d, (hv a ha).intervalIntegrable c d⟩

theorem rectangleIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleBoundaryIntegrable f a b c d)
    (hg : RectangleBoundaryIntegrable g a b c d) :
    rectangleIntegral (fun w => f w + g w) a b c d =
      rectangleIntegral f a b c d + rectangleIntegral g a b c d := by
  dsimp [rectangleIntegral]
  rw [integral_add hf.bottom hg.bottom, integral_add hf.top hg.top,
    integral_add hf.right hg.right, integral_add hf.left hg.left]
  ring

theorem rectangleIntegral_mul_const (f : ℂ → ℂ) (a b c d : ℝ) (v : ℂ) :
    rectangleIntegral (fun w => f w * v) a b c d = rectangleIntegral f a b c d * v := by
  simp only [rectangleIntegral, integral_mul_const]
  ring

theorem rectangleIntegral_congr_off_interiorPoint {f g : ℂ → ℂ} {a b c d : ℝ} {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d)
    (hfg : ∀ w ≠ z, f w = g w) : rectangleIntegral f a b c d = rectangleIntegral g a b c d := by
  have hh (q : ℝ) (hq : q ≠ z.im) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (q : ℂ) * I)) =
      ∫ x : ℝ in a..b, g ((x : ℂ) + (q : ℂ) * I) := by
    apply integral_congr
    intro x hx
    apply hfg
    intro h
    apply hq
    simpa using congrArg Complex.im h
  have hv (q : ℝ) (hq : q ≠ z.re) :
      (∫ y : ℝ in c..d, f ((q : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in c..d, g ((q : ℂ) + (y : ℂ) * I) := by
    apply integral_congr
    intro y hy
    apply hfg
    intro h
    apply hq
    simpa using congrArg Complex.re h
  dsimp [rectangleIntegral]
  rw [hh c (ne_of_lt hc), hh d (ne_of_gt hd), hv b (ne_of_gt hb), hv a (ne_of_lt ha)]

/-- Cauchy's evaluation formula on a positively oriented rectangle compactly contained in an
open holomorphy domain. The integrals are the ordinary four oriented edge integrals. -/
theorem rectangle_cauchy_formula {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {a b c d : ℝ}
    (hrect : Set.uIcc a b ×ℂ Set.uIcc c d ⊆ Ω) {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleIntegral (fun w => f w / (w - z)) a b c d =
      2 * (Real.pi : ℂ) * I * f z := by
  have hz : z ∈ Ω := hrect ⟨Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩),
    Set.mem_uIcc.mpr (Or.inl ⟨hc.le, hd.le⟩)⟩
  have hg : DifferentiableOn ℂ (dslope f z) Ω :=
    (Complex.differentiableOn_dslope (hΩ.mem_nhds hz)).mpr hf
  have hgint := rectangleBoundaryIntegrable_of_continuousOn (hg.continuousOn.mono hrect)
  have hkint := rectangle_kernel_boundaryIntegrable
    (ne_of_lt ha) (ne_of_gt hb) (ne_of_lt hc) (ne_of_gt hd)
  have hkmul : RectangleBoundaryIntegrable (fun w : ℂ => (w - z)⁻¹ * f z) a b c d :=
    ⟨hkint.bottom.mul_const _, hkint.top.mul_const _,
      hkint.right.mul_const _, hkint.left.mul_const _⟩
  have hdecomp : rectangleIntegral (fun w => f w / (w - z)) a b c d =
      rectangleIntegral (fun w => dslope f z w + (w - z)⁻¹ * f z) a b c d := by
    apply rectangleIntegral_congr_off_interiorPoint ha hb hc hd
    intro w hw
    rw [dslope_of_ne f hw, slope_def_field]
    simp only [div_eq_mul_inv]
    ring
  rw [hdecomp, rectangleIntegral_add hgint hkmul,
    rectangleIntegral_eq_zero (dslope f z) a b c d (hg.mono hrect), zero_add,
    rectangleIntegral_mul_const, rectangle_kernel_at ha hb hc hd]

#print axioms rectangleBoundaryIntegrable_of_continuousOn
#print axioms rectangle_kernel_boundaryIntegrable
#print axioms rectangleIntegral_add
#print axioms rectangleIntegral_mul_const
#print axioms rectangleIntegral_congr_off_interiorPoint
#print axioms rectangle_cauchy_formula

/-- The same rectangle integral vanishes when the evaluation point lies outside the closed
rectangle. Together with the interior formula this supplies the two cases in a square-grid sum. -/
theorem rectangle_cauchy_formula_of_not_mem {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {a b c d : ℝ}
    (hrect : Set.uIcc a b ×ℂ Set.uIcc c d ⊆ Ω) {z : ℂ}
    (hz : z ∉ Set.uIcc a b ×ℂ Set.uIcc c d) :
    rectangleIntegral (fun w => f w / (w - z)) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  refine (hf.mono hrect).div (differentiableOn_id.sub_const z) ?_
  intro w hw
  apply sub_ne_zero.mpr
  intro hwz
  exact hz (hwz ▸ hw)

#print axioms rectangle_cauchy_formula_of_not_mem

end RudinRCA.Chapter13Scratch
end Source6

/- Source: HolomorphicLog.lean -/
noncomputable section Source7

/-!
Scratch development of implications in Rudin RCA 13.11:
simple connectedness gives holomorphic logarithms, and holomorphic logarithms
give holomorphic square roots. This does not establish all nine equivalences.
-/

open Set Filter
open scoped Topology

namespace RudinRCA.Chapter13

/-- A continuous local logarithm of a complex differentiable function is
itself complex differentiable. The local inverse theorem for the exponential
supplies the analytic information missing from a purely continuous lift. -/
theorem differentiableAt_of_continuousAt_exp {g : ℂ → ℂ} {a : ℂ}
    (hg : ContinuousAt g a)
    (he : DifferentiableAt ℂ (Complex.exp ∘ g) a) : DifferentiableAt ℂ g a := by
  have hx := Complex.hasStrictDerivAt_exp (g a)
  have hne := Complex.exp_ne_zero (g a)
  let L := hx.localInverse Complex.exp (Complex.exp (g a)) (g a) hne
  have hL : DifferentiableAt ℂ L (Complex.exp (g a)) :=
    (hx.to_localInverse hne).hasDerivAt.differentiableAt
  have hleft : (fun w => L (Complex.exp w)) =ᶠ[𝓝 (g a)] id :=
    hx.eventually_left_inverse hne
  have hback : g =ᶠ[𝓝 a] (L ∘ (Complex.exp ∘ g)) :=
    (hleft.comp_tendsto hg).symm
  exact (hL.comp a he).congr_of_eventuallyEq hback

/-- On an open set, every continuous logarithm of a holomorphic function is
holomorphic. -/
theorem holomorphic_of_continuous_log {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hg : ContinuousOn g Ω)
    (hlog : EqOn (Complex.exp ∘ g) f Ω) : DifferentiableOn ℂ g Ω := by
  intro a ha
  have hnhds := hΩ.mem_nhds ha
  have heq : (Complex.exp ∘ g) =ᶠ[𝓝 a] f := by
    filter_upwards [hnhds] with z hz
    exact hlog hz
  exact (differentiableAt_of_continuousAt_exp (hg.continuousAt hnhds)
    ((hf.differentiableAt hnhds).congr_of_eventuallyEq heq)).differentiableWithinAt

/-- Rudin 13.11, implication (b) to (h): a zero-free holomorphic function on
an open simply connected plane set admits a holomorphic logarithm. -/
theorem exists_holomorphic_log_of_simply_connected {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ EqOn (Complex.exp ∘ g) f Ω := by
  have hnot : 0 ∉ f '' Ω := by
    rintro ⟨z, hz, heq⟩
    exact hzero z hz heq
  obtain ⟨g, hgc, hg⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hsc hΩ hf.continuousOn hnot
  exact ⟨g, holomorphic_of_continuous_log hΩ hf hgc hg, hg⟩

/-- Rudin 13.11, implication (h) to (j), for one function: exponentiating
half of a holomorphic logarithm gives a holomorphic square root. -/
theorem exists_holomorphic_sqrt_of_holomorphic_log {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hlog : EqOn (Complex.exp ∘ g) f Ω) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ ∀ z ∈ Ω, (h z) ^ 2 = f z := by
  refine ⟨fun z => Complex.exp (g z / 2), (hg.div_const 2).cexp, ?_⟩
  intro z hz
  calc
    Complex.exp (g z / 2) ^ 2 = Complex.exp (2 * (g z / 2)) :=
      (Complex.exp_nat_mul (g z / 2) 2).symm
    _ = Complex.exp (g z) := by congr 1; ring
    _ = f z := hlog hz

/-- In particular, a zero-free holomorphic function on an open simply
connected plane set admits a holomorphic square root. -/
theorem exists_holomorphic_sqrt_of_simply_connected {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ ∀ z ∈ Ω, (h z) ^ 2 = f z := by
  obtain ⟨g, hg, hlog⟩ := exists_holomorphic_log_of_simply_connected hΩ hsc hf hzero
  exact exists_holomorphic_sqrt_of_holomorphic_log hg hlog

#print axioms differentiableAt_of_continuousAt_exp
#print axioms holomorphic_of_continuous_log
#print axioms exists_holomorphic_log_of_simply_connected
#print axioms exists_holomorphic_sqrt_of_holomorphic_log
#print axioms exists_holomorphic_sqrt_of_simply_connected

end RudinRCA.Chapter13
end Source7

/- Source: PrimitiveLog.lean -/
noncomputable section Source8

/-!
Scratch development of Rudin RCA 13.11 (g) implies (h): if every holomorphic
function has a primitive on a plane region, every zero-free holomorphic
function has a holomorphic logarithm. This is one implication, not the full
nine-way equivalence.
-/

open Set

namespace RudinRCA.Chapter13

/-- A primitive of the logarithmic derivative determines a holomorphic
logarithm, after an additive constant is chosen. -/
theorem exists_holomorphic_log_of_primitive_logDeriv {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0)
    (hg : DifferentiableOn ℂ g Ω)
    (hprim : ∀ z ∈ Ω, deriv g z = deriv f z / f z) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (Complex.exp ∘ h) f Ω := by
  have he : DifferentiableOn ℂ (Complex.exp ∘ g) Ω := hg.cexp
  have hder : EqOn (logDeriv f) (logDeriv (Complex.exp ∘ g)) Ω := by
    intro z hz
    calc
      logDeriv f z = deriv g z := (hprim z hz).symm
      _ = logDeriv (Complex.exp ∘ g) z := by
        rw [logDeriv_comp Complex.differentiableAt_exp
          (hg.differentiableAt (hΩ.mem_nhds hz))]
        simp [logDeriv_apply, Complex.deriv_exp, Complex.exp_ne_zero]
  obtain ⟨c, hc, hcf⟩ := (logDeriv_eqOn_iff hf he hΩ hconn
    (fun z _ => Complex.exp_ne_zero (g z)) hzero).1 hder
  refine ⟨fun z => Complex.log c + g z,
    (differentiableOn_const (Complex.log c)).add hg, ?_⟩
  intro z hz
  change Complex.exp (Complex.log c + g z) = f z
  rw [Complex.exp_add, Complex.exp_log hc]
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] using (hcf hz).symm

/-- Rudin 13.11, implication (g) to (h), with the universal primitive
property stated explicitly. -/
theorem primitives_imply_holomorphic_logarithms {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hprimitives : ∀ k : ℂ → ℂ, DifferentiableOn ℂ k Ω →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, deriv g z = k z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (Complex.exp ∘ h) f Ω := by
  have hquot : DifferentiableOn ℂ (fun z => deriv f z / f z) Ω :=
    (hf.deriv hΩ).div hf hzero
  obtain ⟨g, hg, hprim⟩ := hprimitives (fun z => deriv f z / f z) hquot
  exact exists_holomorphic_log_of_primitive_logDeriv hΩ hconn hf hzero hg hprim

#print axioms exists_holomorphic_log_of_primitive_logDeriv
#print axioms primitives_imply_holomorphic_logarithms

end RudinRCA.Chapter13
end Source8

/- Source: RungeFunctional.lean -/
noncomputable section Source9

open Set Filter
open scoped Topology

namespace RudinRCA.Chapter13

/-- Hahn–Banach separation in the form needed for rational approximation. -/
theorem mem_closed_submodule_of_annihilators {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) {x : E}
    (h : ∀ L : E →L[ℂ] ℂ, (∀ y ∈ M, L y = 0) → L x = 0) : x ∈ M := by
  let : IsClosed (M : Set E) := hM
  have hx : M.mkQL x = 0 := by
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro L
    apply h (L.comp M.mkQL)
    intro y hy
    have hyq : M.mkQL y = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hy
    simp [hyq]
  exact (Submodule.Quotient.mk_eq_zero M).mp hx

/-- Closure of a linear space is detected by all continuous linear annihilators. -/
theorem mem_submodule_closure_iff_annihilators {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (M : Submodule ℂ E) (x : E) :
    x ∈ M.topologicalClosure ↔
      ∀ L : E →L[ℂ] ℂ, (∀ y ∈ M, L y = 0) → L x = 0 := by
  constructor
  · intro hx L hL
    exact M.topologicalClosure_minimal (fun y hy ↦ hL y hy) L.isClosed_ker hx
  · intro h
    apply mem_closed_submodule_of_annihilators M.topologicalClosure M.isClosed_topologicalClosure
    intro L hL
    exact h L (fun y hy ↦ hL y (M.le_topologicalClosure hy))

/-- The complex coordinate viewed in the Banach algebra of continuous functions on K. -/
def compactCoordinate (K : Set ℂ) : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

theorem spectrum_compactCoordinate (K : Set ℂ) :
    spectrum ℂ (compactCoordinate K) = K := by
  rw [ContinuousMap.spectrum_eq_range]
  exact Subtype.range_coe

/-- A continuous linear functional applied to a resolvent is holomorphic off the spectrum. -/
theorem differentiableOn_dual_resolvent {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (resolvent a z)) (spectrum ℂ a)ᶜ := by
  intro z hz
  have hz' : z ∈ resolventSet ℂ a := by simpa only [spectrum, compl_compl] using hz
  exact (L.differentiableAt.comp z
    (spectrum.hasDerivAt_resolvent_const_left hz').differentiableAt).differentiableWithinAt

/-- The C(K)-valued resolvent evaluates to the usual Cauchy kernel. -/
theorem compactCoordinate_resolvent_apply (K : Set ℂ) {z : ℂ} (hz : z ∉ K) (x : K) :
    resolvent (compactCoordinate K) z x = (z - (x : ℂ))⁻¹ := by
  have hz' : z ∈ resolventSet ℂ (compactCoordinate K) := by
    apply spectrum.notMem_iff.mp
    rwa [spectrum_compactCoordinate]
  have hh := congrArg (fun g : C(K, ℂ) ↦ g x)
    (Ring.inverse_mul_cancel (algebraMap ℂ C(K, ℂ) z - compactCoordinate K) hz')
  have hm : resolvent (compactCoordinate K) z x * (z - (x : ℂ)) = 1 := by
    simpa [resolvent, compactCoordinate] using hh
  exact eq_inv_of_mul_eq_one_left hm

/-- This Cauchy transform uses a bounded linear functional directly, without a measure representation. -/
theorem differentiableOn_compact_cauchy_transform (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (resolvent (compactCoordinate K) z)) Kᶜ := by
  simpa only [spectrum_compactCoordinate] using differentiableOn_dual_resolvent (compactCoordinate K) L

/-- Resolvent expansion around any point outside the spectrum. -/
theorem resolvent_shift {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : A) {α : ℂ} (hα : α ∈ resolventSet ℂ a) (β : ℂ) :
    resolvent a β = resolvent a α *
      Ring.inverse (1 - (α - β) • resolvent a α) := by
  have hfactor : algebraMap ℂ A β - a =
      (algebraMap ℂ A α - a) * (1 - (α - β) • resolvent a α) := by
    rw [mul_sub, mul_one, mul_smul_comm]
    rw [resolvent, Ring.mul_inverse_cancel _ hα]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  conv_lhs => rw [resolvent, hfactor]
  rw [Ring.inverse_mul (Or.inl hα), mul_comm]
  rfl

/-- An annihilator of all powers kills the convergent geometric resolvent expansion. -/
theorem dual_geometric_inverse_eq_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (L : A →L[ℂ] ℂ) (a b : A) (w : ℂ)
    (hsmall : ‖w • a‖ < 1) (h : ∀ n : ℕ, L (b * a ^ n) = 0) :
    L (b * Ring.inverse (1 - w • a)) = 0 := by
  have hs := L.hasSum ((hasSum_geom_series_inverse (w • a) hsmall).mul_left b)
  have hz : HasSum (fun _ : ℕ ↦ (0 : ℂ)) (L (b * Ring.inverse (1 - w • a))) := by
    simpa only [smul_pow, mul_smul_comm, L.map_smul, h, smul_zero] using hs
  exact hz.unique hasSum_zero

/-- Vanishing on the principal parts at α forces the Cauchy transform to vanish near α. -/
theorem dual_resolvent_eventually_eq_zero {A : Type*} [NormedCommRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ)
    {α : ℂ} (hα : α ∈ resolventSet ℂ a)
    (h : ∀ n : ℕ, L (resolvent a α ^ (n + 1)) = 0) :
    (fun β ↦ L (resolvent a β)) =ᶠ[𝓝 α] 0 := by
  have hc : Continuous (fun β : ℂ ↦ ‖(α - β) • resolvent a α‖) := by fun_prop
  have hsmall : ∀ᶠ β in 𝓝 α, ‖(α - β) • resolvent a α‖ < 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  filter_upwards [hsmall] with β hβ
  rw [resolvent_shift a hα β]
  apply dual_geometric_inverse_eq_zero L _ _ _ hβ
  intro n
  simpa only [pow_succ, mul_comm] using h n

/-- The inverse chart gives a holomorphic extension of the Cauchy transform at infinity. -/
theorem analyticAt_dual_inverseChart_resolvent {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun w : ℂ ↦ L (w • Ring.inverse (1 - w • a))) 0 := by
  have hi : AnalyticAt ℂ (fun w : ℂ ↦ Ring.inverse (1 - w • a)) 0 :=
    (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).analyticAt
  exact (L.analyticAt _).comp (analyticAt_id.smul hi)

/-- The inverse-chart expression agrees with the resolvent away from its chart center. -/
theorem inverseChart_resolvent_eq {A : Type*} [Ring A] [Algebra ℂ A]
    (a : A) {w : ℂ} (hw : w ≠ 0) :
    resolvent a w⁻¹ = w • Ring.inverse (1 - w • a) := by
  have h := congrArg (fun v : A ↦ w • v)
    (spectrum.units_smul_resolvent_self (r := (Units.mk0 w hw)⁻¹) (a := a))
  simpa [resolvent, smul_smul, hw] using h

/-- Annihilation of polynomial restrictions gives local vanishing at infinity. -/
theorem dual_inverseChart_resolvent_eventually_eq_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (L : A →L[ℂ] ℂ)
    (h : ∀ n : ℕ, L (a ^ n) = 0) :
    (fun w : ℂ ↦ L (w • Ring.inverse (1 - w • a))) =ᶠ[𝓝 0] 0 := by
  have hc : Continuous (fun w : ℂ ↦ ‖w • a‖) := by fun_prop
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w • a‖ < 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  filter_upwards [hsmall] with w hw
  have hz : L (Ring.inverse (1 - w • a)) = 0 := by
    simpa only [one_mul] using
      dual_geometric_inverse_eq_zero L a 1 w hw (fun n ↦ by simpa only [one_mul] using h n)
  simp [hz]

/-- Isolated-zero dichotomy makes the set of zero germs clopen. -/
theorem isClopen_zeroGerms {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hiso : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    IsClopen {x | ∀ᶠ y in 𝓝 x, f y = 0} := by
  refine ⟨?_, isOpen_setOfPred_eventually_nhds⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ¬∀ᶠ y in 𝓝 x, f y = 0 := hx
  have hn := (hiso x).resolve_left hx'
  rw [eventually_nhdsWithin_iff] at hn
  filter_upwards [hn] with y hy
  intro hyzero
  by_cases hyx : y = x
  · exact hx' (hyx ▸ hyzero)
  · exact hy hyx hyzero.self_of_nhds

/-- Local vanishing at one point of every connected component implies global vanishing. -/
theorem eq_zero_of_zeroGerm_in_each_component {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hiso : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0)
    (hpoints : ∀ x, ∃ a ∈ connectedComponent x, ∀ᶠ y in 𝓝 a, f y = 0) :
    ∀ x, f x = 0 := by
  intro x
  obtain ⟨a, ha, hzero⟩ := hpoints x
  have hx : x ∈ connectedComponent a := by
    rw [← connectedComponent_eq ha]
    exact mem_connectedComponent
  exact ((isClopen_zeroGerms f hiso).connectedComponent_subset hzero hx).self_of_nhds

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.mem_submodule_closure_iff_annihilators
#print axioms RudinRCA.Chapter13.compactCoordinate_resolvent_apply
#print axioms RudinRCA.Chapter13.differentiableOn_compact_cauchy_transform
#print axioms RudinRCA.Chapter13.dual_resolvent_eventually_eq_zero
#print axioms RudinRCA.Chapter13.analyticAt_dual_inverseChart_resolvent
#print axioms RudinRCA.Chapter13.dual_inverseChart_resolvent_eventually_eq_zero
#print axioms RudinRCA.Chapter13.eq_zero_of_zeroGerm_in_each_component
end Source9

/- Source: GridBoundary.lean -/
noncomputable section Source10

open Function
namespace RudinRCA.Chapter13

private def swapSubtypeConditions {E : Type*} (p q : E → Prop) :
    {e : {e // p e} // q e.1} ≃ {e : {e // q e} // p e.1} where
  toFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  invFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_fiber_complement {E V : Type*} [Fintype E] (p : E → Prop)
    (f : E → V) (v : V) :
    Nat.card {e : {e // ¬p e} // f e.1 = v} =
      Nat.card {e // f e = v} - Nat.card {e : {e // p e} // f e.1 = v} := by
  classical
  simp only [Nat.card_eq_fintype_card]
  calc
    _ = Fintype.card {e : {e // f e = v} // ¬p e.1} :=
      Fintype.card_congr (swapSubtypeConditions (fun e => ¬p e) (fun e => f e = v))
    _ = Fintype.card {e // f e = v} -
        Fintype.card {e : {e // f e = v} // p e.1} := Fintype.card_subtype_compl _
    _ = _ := congrArg (fun n => Fintype.card {e // f e = v} - n)
      (Fintype.card_congr (swapSubtypeConditions (fun e => f e = v) p))

/-- Deleting a balanced subfamily from a finite balanced directed family preserves balance. -/
theorem balanced_complement {E V : Type*} [Fintype E] (initial terminal : E → V)
    (p : E → Prop)
    (htotal : ∀ v, Nat.card {e // initial e = v} = Nat.card {e // terminal e = v})
    (hpart : ∀ v, Nat.card {e : {e // p e} // initial e.1 = v} =
      Nat.card {e : {e // p e} // terminal e.1 = v}) :
    ∀ v, Nat.card {e : {e // ¬p e} // initial e.1 = v} =
      Nat.card {e : {e // ¬p e} // terminal e.1 = v} := by
  intro v
  rw [card_fiber_complement, card_fiber_complement, htotal v, hpart v]

/-- A successor permutation certifies balance, preserving edge multiplicities. -/
theorem balanced_of_successor {E V : Type*} [Fintype E] (initial terminal : E → V)
    (σ : Equiv.Perm E) (hσ : ∀ e, terminal e = initial (σ e)) :
    ∀ v, Nat.card {e // initial e = v} = Nat.card {e // terminal e = v} := by
  intro v
  exact (Nat.card_congr (σ.subtypeEquiv
    (p := fun e => terminal e = v) (q := fun e => initial e = v)
      (fun e => by rw [hσ e]))).symm

abbrev GridCell := ℤ × ℤ

def gridCorner (i : Fin 4) : GridCell := ![(0, 0), (1, 0), (1, 1), (0, 1)] i

def gridVertex (c : GridCell) (i : Fin 4) : GridCell := c + gridCorner i

def gridNeighbor (c : GridCell) (i : Fin 4) : GridCell :=
  c + ![(0, -1), (1, 0), (0, 1), (-1, 0)] i

theorem gridNeighbor_reverse (c : GridCell) (i : Fin 4) :
    gridNeighbor (gridNeighbor c i) (i + 2) = c := by
  fin_cases i <;> ext <;> simp [gridNeighbor]

theorem gridVertex_reverse_initial (c : GridCell) (i : Fin 4) :
    gridVertex (gridNeighbor c i) (i + 2) = gridVertex c (i + 1) := by
  fin_cases i <;> ext <;> simp [gridNeighbor, gridVertex, gridCorner]

theorem gridVertex_reverse_terminal (c : GridCell) (i : Fin 4) :
    gridVertex (gridNeighbor c i) (i + 2 + 1) = gridVertex c i := by
  fin_cases i <;> ext <;> simp [gridNeighbor, gridVertex, gridCorner]

abbrev GridEdge (S : Finset GridCell) := S × Fin 4

def gridEdgeInitial {S : Finset GridCell} (e : GridEdge S) : GridCell :=
  gridVertex e.1.1 e.2

def gridEdgeTerminal {S : Finset GridCell} (e : GridEdge S) : GridCell :=
  gridVertex e.1.1 (e.2 + 1)

def gridEdgeInternal {S : Finset GridCell} (e : GridEdge S) : Prop :=
  gridNeighbor e.1.1 e.2 ∈ S

def gridInternalReverse (S : Finset GridCell)
    (e : {e : GridEdge S // gridEdgeInternal e}) :
    {e : GridEdge S // gridEdgeInternal e} :=
  ⟨(⟨gridNeighbor e.1.1.1 e.1.2, e.2⟩, e.1.2 + 2), by
    change gridNeighbor (gridNeighbor e.1.1.1 e.1.2) (e.1.2 + 2) ∈ S
    rw [gridNeighbor_reverse]
    exact e.1.1.2⟩

theorem gridInternalReverse_involutive (S : Finset GridCell) :
    Involutive (gridInternalReverse S) := by
  intro e
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact gridNeighbor_reverse _ _
  · change e.1.2 + 2 + 2 = e.1.2
    exact (show ∀ i : Fin 4, i + 2 + 2 = i from by decide) e.1.2

/-- The external edges of a finite union of grid cells form a balanced family. -/
theorem gridBoundary_balanced (S : Finset GridCell) :
    ∀ v, Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      gridEdgeInitial e.1 = v} =
      Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      gridEdgeTerminal e.1 = v} := by
  classical
  apply balanced_complement
  · apply balanced_of_successor _ _ ((Equiv.refl S).prodCongr (finRotate 4))
    intro e
    simp [gridEdgeTerminal, gridEdgeInitial, finRotate_apply]
  · apply balanced_of_successor _ _
      ({ toFun := gridInternalReverse S, invFun := gridInternalReverse S,
         left_inv := gridInternalReverse_involutive S,
         right_inv := gridInternalReverse_involutive S } : Equiv.Perm _)
    intro e
    exact (gridVertex_reverse_initial _ _).symm

#print axioms balanced_complement
#print axioms balanced_of_successor
#print axioms gridNeighbor_reverse
#print axioms gridVertex_reverse_initial
#print axioms gridVertex_reverse_terminal
#print axioms gridInternalReverse_involutive
#print axioms gridBoundary_balanced
end RudinRCA.Chapter13
end Source10

/- Source: ContourContinuity.lean -/
noncomputable section Source11

open Set Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace RudinRCA.Chapter13Scratch

/-- A fixed parameterized contour integral with a Cauchy denominator is continuous in the
evaluation point when a positive lower bound on distance to the contour is available. -/
theorem continuousAt_kernel_intervalIntegral_of_bounds
    {γ g : ℝ → ℂ} {a b : ℝ} {z : ℂ} {δ M : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hsep : ∀ t ∈ uIcc a b, δ ≤ ‖γ t - z‖)
    (hbound : ∀ t ∈ uIcc a b, ‖g t‖ ≤ M) :
    ContinuousAt (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w)) z := by
  have hn : ∀ᶠ w : ℂ in 𝓝 z, ‖w - z‖ < δ / 2 := by
    filter_upwards [Metric.ball_mem_nhds z (half_pos hδ)] with w hw
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hden {w : ℂ} (hw : ‖w - z‖ < δ / 2) {t : ℝ} (ht : t ∈ uIcc a b) :
      δ / 2 ≤ ‖γ t - w‖ := by
    have htri : ‖γ t - z‖ ≤ ‖γ t - w‖ + ‖w - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (γ t - w) (w - z)
    have hs := hsep t ht
    linarith
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ : ℝ => M / (δ / 2))
  · filter_upwards [hn] with w hw
    have hc : ContinuousOn (fun t : ℝ => g t / (γ t - w)) (uIcc a b) :=
      hg.div (hγ.sub continuousOn_const) fun t ht =>
        norm_pos_iff.mp ((half_pos hδ).trans_le (hden hw ht))
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hn] with w hw
    exact Filter.Eventually.of_forall fun t ht => by
      rw [norm_div]
      exact div_le_div₀ hM (hbound t (Ioc_subset_Icc_self ht))
        (half_pos hδ) (hden hw (Ioc_subset_Icc_self ht))
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht =>
      continuousAt_const.div (continuousAt_const.sub continuousAt_id)
        (norm_pos_iff.mp (hδ.trans_le (hsep t (Ioc_subset_Icc_self ht))))

/-- A Cauchy-type integral over a compact parameter interval depends continuously on every
evaluation point outside the contour image. The numerator may include the contour velocity. -/
theorem continuousAt_kernel_intervalIntegral
    {γ g : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hz : z ∉ γ '' uIcc a b) :
    ContinuousAt (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w)) z := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_uIcc.exists_isMinOn
    (show (uIcc a b).Nonempty from ⟨a, left_mem_uIcc⟩)
    (hγ.sub continuousOn_const).norm
  have hsep : 0 < ‖γ t₀ - z‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro h
    exact hz ⟨t₀, ht₀, h⟩
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    (show (uIcc a b).Nonempty from ⟨a, left_mem_uIcc⟩) hg.norm
  exact continuousAt_kernel_intervalIntegral_of_bounds hγ hg hsep (norm_nonneg _)
    (fun t ht => hmin ht) (fun t ht => hmax ht)

theorem continuousOn_kernel_intervalIntegral
    {γ g : ℝ → ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hg : ContinuousOn g (uIcc a b)) :
    ContinuousOn (fun w : ℂ => ∫ t : ℝ in a..b, g t / (γ t - w))
      (γ '' uIcc a b)ᶜ := by
  intro z hz
  exact (continuousAt_kernel_intervalIntegral hγ hg hz).continuousWithinAt

#print axioms continuousAt_kernel_intervalIntegral_of_bounds
#print axioms continuousAt_kernel_intervalIntegral
#print axioms continuousOn_kernel_intervalIntegral

end RudinRCA.Chapter13Scratch
end Source11

/- Source: SegmentIntegralBridge.lean -/
noncomputable section Source12

open Complex intervalIntegral
open scoped Topology

namespace RudinRCA.Chapter13Scratch

/-- Complex line integration over an oriented segment, using its affine parametrization. -/
noncomputable def complexSegmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, f (AffineMap.lineMap a b t) * (b - a)

/-- The explicit affine-parameter integral is Mathlib's curve integral of the complex 1-form
`f(z) dz` over `Path.segment a b`. -/
theorem curveIntegral_segment_eq_complexSegmentIntegral (f : ℂ → ℂ) (a b : ℂ) :
    curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (Path.segment a b) =
      complexSegmentIntegral f a b := by
  simpa only [complexSegmentIntegral, ContinuousLinearMap.mul_apply'] using
    curveIntegral_segment (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) a b

/-- Horizontal segment integration agrees with an ordinary oriented real interval integral. -/
theorem complexSegmentIntegral_horizontal (f : ℂ → ℂ) (a b c : ℝ) :
    complexSegmentIntegral f ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (c : ℂ) * I) =
      ∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * I) := by
  have hdelta : ((b : ℂ) + (c : ℂ) * I) - ((a : ℂ) + (c : ℂ) * I) =
      ((b - a : ℝ) : ℂ) := by push_cast; ring
  have hline (t : ℝ) :
      AffineMap.lineMap ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (c : ℂ) * I) t =
      (((b - a) * t + a : ℝ) : ℂ) + (c : ℂ) * I := by
    rw [AffineMap.lineMap_apply_module', hdelta]
    change (t : ℂ) * ((b - a : ℝ) : ℂ) + ((a : ℂ) + (c : ℂ) * I) = _
    push_cast
    ring
  calc
    _ = (b - a) • (∫ t : ℝ in 0..1,
        f ((((b - a) * t + a : ℝ) : ℂ) + (c : ℂ) * I)) := by
      rw [← integral_smul]
      apply integral_congr
      intro t ht
      rw [hline, hdelta]
      change _ = ((b - a : ℝ) : ℂ) * _
      ring
    _ = ∫ x : ℝ in (b - a) * 0 + a..(b - a) * 1 + a,
        f ((x : ℂ) + (c : ℂ) * I) :=
      smul_integral_comp_mul_add (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)) (b - a) a
    _ = _ := by simp

/-- Vertical segment integration agrees with `I` times an ordinary oriented interval integral. -/
theorem complexSegmentIntegral_vertical (f : ℂ → ℂ) (a b c : ℝ) :
    complexSegmentIntegral f ((c : ℂ) + (a : ℂ) * I) ((c : ℂ) + (b : ℂ) * I) =
      I * ∫ y : ℝ in a..b, f ((c : ℂ) + (y : ℂ) * I) := by
  have hdelta : ((c : ℂ) + (b : ℂ) * I) - ((c : ℂ) + (a : ℂ) * I) =
      ((b - a : ℝ) : ℂ) * I := by push_cast; ring
  have hline (t : ℝ) :
      AffineMap.lineMap ((c : ℂ) + (a : ℂ) * I) ((c : ℂ) + (b : ℂ) * I) t =
      (c : ℂ) + (((b - a) * t + a : ℝ) : ℂ) * I := by
    rw [AffineMap.lineMap_apply_module', hdelta]
    change (t : ℂ) * (((b - a : ℝ) : ℂ) * I) + ((c : ℂ) + (a : ℂ) * I) = _
    push_cast
    ring
  calc
    _ = I * ((b - a) • (∫ t : ℝ in 0..1,
        f ((c : ℂ) + (((b - a) * t + a : ℝ) : ℂ) * I))) := by
      rw [← integral_smul, ← integral_const_mul]
      apply integral_congr
      intro t ht
      rw [hline, hdelta]
      change _ = I * (((b - a : ℝ) : ℂ) * _)
      ring
    _ = I * (∫ y : ℝ in (b - a) * 0 + a..(b - a) * 1 + a,
        f ((c : ℂ) + (y : ℂ) * I)) := by
      rw [smul_integral_comp_mul_add]
    _ = _ := by simp

theorem complexSegmentIntegral_symm (f : ℂ → ℂ) (a b : ℂ) :
    complexSegmentIntegral f b a = -complexSegmentIntegral f a b := by
  rw [← curveIntegral_segment_eq_complexSegmentIntegral,
    ← curveIntegral_segment_eq_complexSegmentIntegral]
  simpa using curveIntegral_symm (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (Path.segment a b)

#print axioms curveIntegral_segment_eq_complexSegmentIntegral
#print axioms complexSegmentIntegral_horizontal
#print axioms complexSegmentIntegral_vertical
#print axioms complexSegmentIntegral_symm

end RudinRCA.Chapter13Scratch
end Source12

/- Source: PolygonalConcat.lean -/
noncomputable section Source13

namespace RudinRCA.Chapter13Scratch

theorem curveIntegrable_concat (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, CurveIntegrable ω (F i)) : CurveIntegrable ω (Path.concat p F) := by
  induction n generalizing p with
  | zero => simpa using CurveIntegrable.refl ω (p 0)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) (fun i => hF i.castSucc)).trans
      (hF (Fin.last n))

/-- Integration over a finite concatenation is the sum of the individual path integrals. -/
theorem curveIntegral_concat (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hF : ∀ i, CurveIntegrable ω (F i)) :
    curveIntegral ω (Path.concat p F) = ∑ i : Fin n, curveIntegral ω (F i) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Path.concat_succ, curveIntegral_trans
      (curveIntegrable_concat ω (p ∘ Fin.castSucc) (fun i => F i.castSucc)
        (fun i => hF i.castSucc)) (hF (Fin.last n))]
    rw [ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) (fun i => hF i.castSucc)]
    exact (Fin.sum_univ_castSucc (fun i : Fin (n + 1) => curveIntegral ω (F i))).symm

theorem concat_range_subset {n : ℕ} (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) {U : Set ℂ}
    (hstart : p 0 ∈ U) (hF : ∀ i, Set.range (F i) ⊆ U) :
    Set.range (Path.concat p F) ⊆ U := by
  induction n generalizing p with
  | zero =>
    rintro x ⟨t, rfl⟩
    simpa using hstart
  | succ n ih =>
    rw [Path.concat_succ, Path.trans_range]
    exact Set.union_subset
      (ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) hstart (fun i => hF i.castSucc))
      (hF (Fin.last n))

/-- A finite compatible family with equal first and last vertices gives an actual closed path,
retaining both the range restriction and the sum of the edge integrals. For polygonal paths take
each `F i` to be `Path.segment (p i.castSucc) (p i.succ)`. -/
theorem closed_concat_integral (ω : ℂ → ℂ →L[ℂ] ℂ) {n : ℕ}
    (p : Fin (n + 1) → ℂ)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hclosed : p (Fin.last n) = p 0) {U : Set ℂ}
    (hstart : p 0 ∈ U) (hFrange : ∀ i, Set.range (F i) ⊆ U)
    (hF : ∀ i, CurveIntegrable ω (F i)) :
    ∃ γ : Path (p 0) (p 0), Set.range γ ⊆ U ∧ CurveIntegrable ω γ ∧
      curveIntegral ω γ = ∑ i : Fin n, curveIntegral ω (F i) := by
  let γ := (Path.concat p F).cast rfl hclosed.symm
  refine ⟨γ, ?_, ?_, ?_⟩
  · simpa [γ] using concat_range_subset p F hstart hFrange
  · exact (curveIntegrable_cast_iff rfl hclosed.symm).mpr (curveIntegrable_concat ω p F hF)
  · simpa [γ] using curveIntegral_concat ω p F hF

#print axioms curveIntegrable_concat
#print axioms curveIntegral_concat
#print axioms concat_range_subset
#print axioms closed_concat_integral

end RudinRCA.Chapter13Scratch
end Source13

/- Source: CyclicVertices.lean -/
noncomputable section Source14

namespace RudinRCA.Chapter13Scratch

/-- Repeat the first vertex at the end of a cyclic `Fin n` vertex list. -/
def cyclicPolygonalVertices {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  fun j => v ⟨j.val % n, Nat.mod_lt _ hn⟩

theorem cyclicPolygonalVertices_castSucc {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (i : Fin n) :
    cyclicPolygonalVertices hn v i.castSucc = v i := by
  apply congrArg v
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem cyclicPolygonalVertices_succ {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (i : Fin n) :
    cyclicPolygonalVertices hn v i.succ = v ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ := rfl

theorem cyclicPolygonalVertices_zero {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    cyclicPolygonalVertices hn v 0 = v ⟨0, hn⟩ := by
  apply congrArg v
  apply Fin.ext
  exact Nat.zero_mod n

theorem cyclicPolygonalVertices_last {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    cyclicPolygonalVertices hn v (Fin.last n) = v ⟨0, hn⟩ := by
  apply congrArg v
  apply Fin.ext
  exact Nat.mod_self n

universe u
variable {E : Type u} {n : ℕ}

/-- Compatible cyclic edges determine a finite vertex sequence with exactly their original
initial and terminal endpoints, and with first vertex equal to last vertex. -/
theorem closed_vertices_of_cyclic_edges (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) :
    ∃ p : Fin (n + 1) → ℂ,
      p 0 = initial (edge ⟨0, hn⟩) ∧ p (Fin.last n) = p 0 ∧
      ∀ i, p i.castSucc = initial (edge i) ∧ p i.succ = terminal (edge i) := by
  let v := fun i => initial (edge i)
  refine ⟨cyclicPolygonalVertices hn v, cyclicPolygonalVertices_zero hn v, ?_, ?_⟩
  · rw [cyclicPolygonalVertices_last, cyclicPolygonalVertices_zero]
  · intro i
    exact ⟨cyclicPolygonalVertices_castSucc hn v i,
      (cyclicPolygonalVertices_succ hn v i).trans (hnext i).symm⟩

/-- A supplied directed edge, cast to the corresponding consecutive vertices. -/
noncomputable def cyclicPolygonalEdgePath (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) (i : Fin n) :
    Path (cyclicPolygonalVertices hn (fun j => initial (edge j)) i.castSucc)
      (cyclicPolygonalVertices hn (fun j => initial (edge j)) i.succ) :=
  (Path.segment (initial (edge i)) (terminal (edge i))).cast
    (cyclicPolygonalVertices_castSucc hn (fun j => initial (edge j)) i)
    ((cyclicPolygonalVertices_succ hn (fun j => initial (edge j)) i).trans (hnext i).symm)

/-- The actual closed polygonal path chosen from cyclic edge geometry. The definition has no
integrand parameter; it is chosen once and works simultaneously for all admissible functions. -/
noncomputable def cyclicPolygonalPath (hn : 0 < n) (initial terminal : E → ℂ)
    (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) :
    Path (initial (edge ⟨0, hn⟩)) (initial (edge ⟨0, hn⟩)) :=
  (Path.concat (cyclicPolygonalVertices hn (fun j => initial (edge j)))
      (cyclicPolygonalEdgePath hn initial terminal edge hnext)).cast
    (cyclicPolygonalVertices_zero hn (fun j => initial (edge j))).symm
    (cyclicPolygonalVertices_last hn (fun j => initial (edge j))).symm

theorem curveIntegral_cyclicPolygonalEdgePath (ω : ℂ → ℂ →L[ℂ] ℂ)
    (hn : 0 < n) (initial terminal : E → ℂ) (edge : Fin n → E)
    (hnext : ∀ i, terminal (edge i) =
      initial (edge ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) (i : Fin n) :
    curveIntegral ω (cyclicPolygonalEdgePath hn initial terminal edge hnext i) =
      curveIntegral ω (Path.segment (initial (edge i)) (terminal (edge i))) := by
  simp [cyclicPolygonalEdgePath]

#print axioms cyclicPolygonalVertices_castSucc
#print axioms cyclicPolygonalVertices_succ
#print axioms cyclicPolygonalVertices_zero
#print axioms cyclicPolygonalVertices_last
#print axioms closed_vertices_of_cyclic_edges
#print axioms curveIntegral_cyclicPolygonalEdgePath

end RudinRCA.Chapter13Scratch
end Source14

/- Source: SimplyConnectedImplications.lean -/
noncomputable section Source15

/-!
Scratch development of Rudin RCA 13.11 (a) implies (b).
The hypothesis is an actual homeomorphism onto the open unit disc.
This file does not assert the remaining directions of the equivalence.
-/

open Set Metric

namespace RudinRCA.Chapter13

/-- The open complex unit disc is simply connected, since it is nonempty
and convex and hence contractible. -/
theorem simply_connected_open_unit_disc :
    IsSimplyConnected (Metric.ball (0 : ℂ) 1) := by
  let : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace
      ⟨0, mem_ball_self zero_lt_one⟩
  infer_instance

/-- Rudin 13.11 (a) implies (b): a plane set homeomorphic to the open
unit disc is simply connected. -/
theorem simply_connected_of_homeomorphic_to_unit_disc {Ω : Set ℂ}
    (hhomeo : Nonempty (Ω ≃ₜ Metric.ball (0 : ℂ) 1)) : IsSimplyConnected Ω := by
  obtain ⟨e⟩ := hhomeo
  let : SimplyConnectedSpace (Metric.ball (0 : ℂ) 1) := simply_connected_open_unit_disc
  exact e.toHomotopyEquiv.simplyConnectedSpace

#print axioms simply_connected_open_unit_disc
#print axioms simply_connected_of_homeomorphic_to_unit_disc

end RudinRCA.Chapter13
end Source15

/- Source: PrimitiveCurveIntegral.lean -/
noncomputable section Source16

/-!
Scratch development of Rudin 13.11 (g) implies (f). Paths may have finitely
many C¹ pieces, with arbitrary partition points. The conclusion uses Mathlib's
actual curveIntegral, not only a separately defined sum of piece integrals.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RudinRCA.Chapter13

/-- A finite C¹ partition of a path's parameter interval. Repeated partition
points are harmless; arbitrary positive-length pieces are permitted. -/
def IsPiecewiseC1Path {a b : ℂ} (γ : Path a b) : Prop :=
  ∃ (n : ℕ) (t : ℕ → ℝ), Monotone t ∧ t 0 = 0 ∧ t n = 1 ∧
    ∀ k < n, ContDiffOn ℝ 1 γ.extend (Icc (t k) (t (k + 1)))

theorem intervalIntegrable_deriv_of_contDiffOn_interval {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable (deriv ψ) volume a b := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hc := (hψ.derivWithin (m := 0) (uniqueDiffOn_Icc hab') (by simp)).continuousOn
  apply (hc.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
  simp only [hab, uIoc_of_le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

/-- Primitive FTC on one C¹ piece, including integrability. -/
theorem primitive_integral_on_c1_interval {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F f : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hder : ∀ z ∈ Ω, deriv F z = f z) {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) (hab : a ≤ b)
    (hmap : MapsTo ψ (Icc a b) Ω) :
    IntervalIntegrable (fun t => f (ψ t) * deriv ψ t) volume a b ∧
      (∫ t in a..b, f (ψ t) * deriv ψ t) = F (ψ b) - F (ψ a) := by
  have hFc : ContDiffOn ℝ 1 F Ω := (hF.contDiffOn hΩ).restrict_scalars ℝ
  have hcomp : ContDiffOn ℝ 1 (F ∘ ψ) (Icc a b) := hFc.comp hψ hmap
  have hchain (t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (F ∘ ψ) t = f (ψ t) * deriv ψ t := by
    have hψt : DifferentiableAt ℝ ψ t :=
      ((hψ t (Ioo_subset_Icc_self ht)).differentiableWithinAt one_ne_zero).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hFt := hF.differentiableAt (hΩ.mem_nhds (hmap (Ioo_subset_Icc_self ht)))
    rw [← hder (ψ t) (hmap (Ioo_subset_Icc_self ht))]
    exact (hFt.hasDerivAt.comp t hψt.hasDerivAt).deriv
  have hae : (fun t => f (ψ t) * deriv ψ t) =ᵐ[volume.restrict (uIoc a b)]
      deriv (F ∘ ψ) := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact (hchain t ht).symm
  refine ⟨(intervalIntegrable_deriv_of_contDiffOn_interval hcomp hab).congr_ae hae.symm, ?_⟩
  calc
    (∫ t in a..b, f (ψ t) * deriv ψ t) = ∫ t in a..b, deriv (F ∘ ψ) t :=
      intervalIntegral.integral_congr_ae_restrict hae
    _ = F (ψ b) - F (ψ a) := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcomp hab

/-- The integral of a holomorphic primitive's derivative along any finitely
piecewise C¹ path is its endpoint difference. -/
theorem curveIntegral_eq_sub_of_primitive {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F f : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hder : ∀ z ∈ Ω, deriv F z = f z) {a b : ℂ} (γ : Path a b)
    (hγΩ : ∀ t, γ t ∈ Ω) (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = F b - F a := by
  obtain ⟨n, t, ht, ht0, htn, hpieces⟩ := hγ
  have hmap (s : ℝ) : γ.extend s ∈ Ω := by
    have hs : γ.extend s ∈ Set.range γ := γ.extend_range ▸ Set.mem_range_self s
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact hγΩ u
  have hp (k : ℕ) (hk : k < n) := primitive_integral_on_c1_interval hΩ hF hder
    (hpieces k hk) (ht (Nat.le_succ k)) (fun s _ => hmap s)
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  have hadd := intervalIntegral.sum_integral_adjacent_intervals (fun k hk => (hp k hk).1)
  rw [ht0, htn] at hadd
  rw [← hadd]
  calc
    (∑ k ∈ Finset.range n, ∫ s in t k..t (k + 1),
      f (γ.extend s) * deriv γ.extend s) =
        ∑ k ∈ Finset.range n, (F (γ.extend (t (k + 1))) - F (γ.extend (t k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hp k (Finset.mem_range.mp hk)).2
    _ = F (γ.extend (t n)) - F (γ.extend (t 0)) :=
      Finset.sum_range_sub (fun k => F (γ.extend (t k))) n
    _ = F b - F a := by simp [ht0, htn]

/-- Rudin 13.11 (g) implies (f), for the full finite piecewise C¹ path class. -/
theorem primitives_imply_zero_closed_piecewise_integrals {Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (hprimitives : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, deriv F z = f z)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {a : ℂ} (γ : Path a a)
    (hγΩ : ∀ t, γ t ∈ Ω) (hγ : IsPiecewiseC1Path γ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  obtain ⟨F, hF, hder⟩ := hprimitives f hf
  rw [curveIntegral_eq_sub_of_primitive hΩ hF hder γ hγΩ hγ]
  exact sub_self _

#print axioms intervalIntegrable_deriv_of_contDiffOn_interval
#print axioms primitive_integral_on_c1_interval
#print axioms curveIntegral_eq_sub_of_primitive
#print axioms primitives_imply_zero_closed_piecewise_integrals

end RudinRCA.Chapter13
end Source16

/- Source: CauchyTransformSphere.lean -/
noncomputable section Source17

/- This scratch file depends on the declarations in RungeFunctional.lean.
   It is intended for the parent's aggregate check after that source. -/
open Set Filter Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- Transfer a punctured inverse-chart property to the exterior of every compact set. -/
theorem eventually_cobounded_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    {P : ℂ → Prop} (hg : ∀ᶠ w in 𝓝[≠] (0 : ℂ), P (g w)) :
    ∀ᶠ z in Bornology.cobounded ℂ, P (H (z : RiemannSphere)) := by
  have h := (tendsto_inv₀_cobounded' (α := ℂ)).eventually hg
  filter_upwards [h, isBounded_singleton (x := (0 : ℂ))] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  simpa only [heq z⁻¹ (inv_ne_zero hz0'), inv_inv] using hz

/-- The punctured neighborhoods of infinity are exactly the cofinite-compact planar filter. -/
theorem eventually_nhdsNE_infty_iff_cobounded {P : RiemannSphere → Prop} :
    (∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), P p) ↔
      ∀ᶠ z in Bornology.cobounded ℂ, P (z : RiemannSphere) := by
  rw [OnePoint.nhdsNE_infty_eq, Filter.eventually_map,
    coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]

/-- A zero inverse-chart germ is a zero germ at infinity. -/
theorem zeroGerm_infty_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (h∞ : H ∞ = 0)
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    (hg : ∀ᶠ w in 𝓝 (0 : ℂ), g w = 0) :
    ∀ᶠ p in 𝓝 (∞ : RiemannSphere), H p = 0 := by
  have hext := eventually_cobounded_of_inverseChart heq (hg.filter_mono inf_le_left)
  have hpunct : ∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), H p = 0 :=
    eventually_nhdsNE_infty_iff_cobounded.mpr hext
  rw [← nhdsNE_sup_pure (∞ : RiemannSphere), Filter.eventually_sup]
  exact ⟨hpunct, by simpa using h∞⟩

/-- An analytic inverse chart supplies the isolated-zero dichotomy at infinity. -/
theorem zero_dichotomy_infty_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (h∞ : H ∞ = 0)
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    (hg : AnalyticAt ℂ g 0) :
    (∀ᶠ p in 𝓝 (∞ : RiemannSphere), H p = 0) ∨
      ∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), H p ≠ 0 := by
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · exact Or.inl (zeroGerm_infty_of_inverseChart h∞ heq hz)
  · exact Or.inr (eventually_nhdsNE_infty_iff_cobounded.mpr
      (eventually_cobounded_of_inverseChart heq hn))

/-- The finite complex chart transports the analytic isolated-zero dichotomy. -/
theorem zero_dichotomy_coe {H : RiemannSphere → ℂ} {z : ℂ}
    (hz : AnalyticAt ℂ (fun w : ℂ ↦ H (w : RiemannSphere)) z) :
    (∀ᶠ p in 𝓝 (z : RiemannSphere), H p = 0) ∨
      ∀ᶠ p in 𝓝[≠] (z : RiemannSphere), H p ≠ 0 := by
  rcases hz.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · left
    rwa [OnePoint.nhds_coe_eq, Filter.eventually_map]
  · right
    simpa [OnePoint.nhdsWithin_coe, Filter.eventually_map, preimage, OnePoint.coe_eq_coe] using hne

/-- Restriction to a subspace preserves the isolated-zero dichotomy. -/
theorem zero_dichotomy_subtype {X : Type*} [TopologicalSpace X] (H : X → ℂ)
    (D : Set X) (h : ∀ x ∈ D,
      (∀ᶠ y in 𝓝 x, H y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, H y ≠ 0) (x : D) :
    (∀ᶠ y in 𝓝 x, H y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, H y ≠ 0 := by
  rcases h x x.property with hz | hn
  · exact Or.inl (continuous_subtype_val.continuousAt.tendsto.eventually hz)
  · right
    have ht : Tendsto (Subtype.val : D → X) (𝓝[≠] x) (𝓝[≠] (x : X)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact fun heq ↦ hy (Subtype.ext heq)
    exact ht.eventually hn

/-- The Cauchy transform on the Riemann sphere, with value zero at infinity. -/
def sphereCauchyTransform (K : Set ℂ) [CompactSpace K] (L : C(K, ℂ) →L[ℂ] ℂ) :
    RiemannSphere → ℂ :=
  fun p ↦ OnePoint.elim p 0 (fun z ↦ L (resolvent (compactCoordinate K) z))

@[simp] theorem sphereCauchyTransform_infty (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) : sphereCauchyTransform K L ∞ = 0 := rfl

@[simp] theorem sphereCauchyTransform_coe (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    sphereCauchyTransform K L z = L (resolvent (compactCoordinate K) z) := rfl

/-- The sphere Cauchy transform has isolated zeros or a zero germ at every point off K. -/
theorem sphereCauchyTransform_zero_dichotomy (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) :
    ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      (∀ᶠ q in 𝓝 p, sphereCauchyTransform K L q = 0) ∨
        ∀ᶠ q in 𝓝[≠] p, sphereCauchyTransform K L q ≠ 0 := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    apply zero_dichotomy_infty_of_inverseChart (g := fun w : ℂ ↦
      L (w • Ring.inverse (1 - w • compactCoordinate K))) (by rfl)
    · intro w hw
      rw [sphereCauchyTransform_coe, inverseChart_resolvent_eq _ hw]
    · exact analyticAt_dual_inverseChart_resolvent _ L
  | coe z =>
    apply zero_dichotomy_coe
    have hz : z ∈ Kᶜ := by simpa using hp
    have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
    exact ((differentiableOn_compact_cauchy_transform K L).analyticOnNhd
      hK.isClosed.isOpen_compl) z hz

/-- Prescribed finite poles and infinity each supply the required zero germ. -/
theorem sphereCauchyTransform_zeroGerm_at_prescribed_point (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, L (resolvent (compactCoordinate K) α ^ (n + 1)) = 0)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, L (compactCoordinate K ^ n) = 0) :
    ∀ a ∈ A, ∀ᶠ p in 𝓝 a, sphereCauchyTransform K L p = 0 := by
  intro a ha
  induction a using OnePoint.rec with
  | infty =>
    apply zeroGerm_infty_of_inverseChart (g := fun w : ℂ ↦
      L (w • Ring.inverse (1 - w • compactCoordinate K))) (by rfl)
    · intro w hw
      rw [sphereCauchyTransform_coe, inverseChart_resolvent_eq _ hw]
    · exact dual_inverseChart_resolvent_eventually_eq_zero _ L (hinfty ha)
  | coe α =>
    have hα : α ∈ resolventSet ℂ (compactCoordinate K) := by
      apply spectrum.notMem_iff.mp
      rw [spectrum_compactCoordinate]
      simpa using hA ha
    have hz := dual_resolvent_eventually_eq_zero (compactCoordinate K) L hα (hfinite α ha)
    simpa [OnePoint.nhds_coe_eq, Filter.eventually_map, sphereCauchyTransform] using hz

/-- The analytic core of Runge: annihilating principal parts at a point in every
    spherical complement component annihilates every Cauchy kernel off K. -/
theorem compact_cauchy_transform_eq_zero (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, L (resolvent (compactCoordinate K) α ^ (n + 1)) = 0)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, L (compactCoordinate K ^ n) = 0) :
    ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0 := by
  let D : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  let H : D → ℂ := fun p ↦ sphereCauchyTransform K L p
  have hiso : ∀ p : D, (∀ᶠ q in 𝓝 p, H q = 0) ∨ ∀ᶠ q in 𝓝[≠] p, H q ≠ 0 :=
    zero_dichotomy_subtype _ D (sphereCauchyTransform_zero_dichotomy K L)
  have hall : ∀ p : D, H p = 0 := by
    apply eq_zero_of_zeroGerm_in_each_component H hiso
    intro p
    obtain ⟨a, ha, hac⟩ := hcomponents p p.property
    let aD : D := ⟨a, hA ha⟩
    have hac' : aD ∈ connectedComponent p := by
      rw [connectedComponentIn_eq_image p.property] at hac
      obtain ⟨b, hb, hba⟩ := hac
      have hba' : b = aD := Subtype.ext hba
      simpa only [hba'] using hb
    refine ⟨aD, hac', ?_⟩
    exact continuous_subtype_val.continuousAt.tendsto.eventually
      (sphereCauchyTransform_zeroGerm_at_prescribed_point K L A hA hfinite hinfty a ha)
  intro z hz
  have hzd : (z : RiemannSphere) ∈ D := by simpa [D] using hz
  exact hall ⟨z, hzd⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.compact_cauchy_transform_eq_zero
end Source17

/- Source: ContourAnnihilator.lean -/
noncomputable section Source18

/- This scratch file depends on RungeFunctional.lean. It is intended for the
   aggregate check after that source; it does not postulate a contour formula. -/
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace RudinRCA.Chapter13

/-- A weighted Cauchy kernel as a C(K)-valued function of the contour parameter. -/
def contourResolventKernel (K : Set ℂ) [CompactSpace K] (γ w : ℝ → ℂ) (t : ℝ) : C(K, ℂ) :=
  w t • resolvent (compactCoordinate K) (γ t)

/-- The C(K)-valued kernel is continuous wherever the contour stays off K. -/
theorem continuousOn_contourResolventKernel (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) :
    ContinuousOn (contourResolventKernel K γ w) [[a, b]] := by
  have hr : ContinuousOn (resolvent (compactCoordinate K)) Kᶜ := by
    intro z hz
    have hz' : z ∈ resolventSet ℂ (compactCoordinate K) := by
      apply spectrum.notMem_iff.mp
      rwa [spectrum_compactCoordinate]
    exact (spectrum.hasDerivAt_resolvent_const_left hz').continuousAt.continuousWithinAt
  exact hw.smul (hr.comp hγ havoid)

/-- Compact contour parameter intervals give Bochner integrability in C(K). -/
theorem intervalIntegrable_contourResolventKernel (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) :
    IntervalIntegrable (contourResolventKernel K γ w) volume a b :=
  (continuousOn_contourResolventKernel K γ w hγ hw havoid).intervalIntegrable

/-- Evaluating a C(K)-valued contour integral gives the ordinary scalar Cauchy integral. -/
theorem contourResolventKernel_integral_apply (K : Set ℂ) [CompactSpace K]
    (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K) (x : K) :
    (∫ t in a..b, contourResolventKernel K γ w t) x =
      ∫ t in a..b, w t / (γ t - (x : ℂ)) := by
  have hi := intervalIntegrable_contourResolventKernel K γ w hγ hw havoid
  calc
    (∫ t in a..b, contourResolventKernel K γ w t) x =
        ∫ t in a..b, (contourResolventKernel K γ w t) x :=
      ((ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hi).symm
    _ = ∫ t in a..b, w t / (γ t - (x : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [contourResolventKernel, ContinuousMap.smul_apply, smul_eq_mul,
        compactCoordinate_resolvent_apply K (havoid t ht) x, div_eq_mul_inv]

/-- An annihilator of all off-K resolvents annihilates every weighted contour integral. -/
theorem dual_contourResolventKernel_integral_eq_zero (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ [[a, b]]) (hw : ContinuousOn w [[a, b]])
    (havoid : ∀ t ∈ [[a, b]], γ t ∉ K)
    (hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0) :
    L (∫ t in a..b, contourResolventKernel K γ w t) = 0 := by
  have hi := intervalIntegrable_contourResolventKernel K γ w hγ hw havoid
  rw [← L.intervalIntegral_comp_comm hi]
  calc
    (∫ t in a..b, L (contourResolventKernel K γ w t)) = ∫ _ in a..b, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [contourResolventKernel, L.map_smul, hL (γ t) (havoid t ht), smul_zero]
    _ = 0 := by simp

/-- A genuine finite contour representation implies annihilation of F.
    The representation is an explicit hypothesis to be supplied by 13.5. -/
theorem dual_eq_zero_of_finite_contour_representation {ι : Type*} [Fintype ι]
    (K : Set ℂ) [CompactSpace K] (F : C(K, ℂ)) (L : C(K, ℂ) →L[ℂ] ℂ)
    (γ w : ι → ℝ → ℂ) (a b : ι → ℝ) (c : ℂ)
    (hγ : ∀ i, ContinuousOn (γ i) [[a i, b i]])
    (hw : ∀ i, ContinuousOn (w i) [[a i, b i]])
    (havoid : ∀ i t, t ∈ [[a i, b i]] → γ i t ∉ K)
    (hrepresentation : ∀ x : K,
      F x = c * ∑ i, ∫ t in a i..b i, w i t / (γ i t - (x : ℂ)))
    (hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0) :
    L F = 0 := by
  classical
  have hval : ∀ i (x : K),
      (∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t) x =
        ∫ t in a i..b i, w i t / (γ i t - (x : ℂ)) :=
    fun i x ↦ contourResolventKernel_integral_apply K _ _ (hγ i) (hw i) (havoid i) x
  have hF : F = c • ∑ i, ∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t := by
    ext x
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sum_apply, hval] using
      hrepresentation x
  rw [hF, L.map_smul, map_sum]
  have hz : ∀ i, L (∫ t in a i..b i, contourResolventKernel K (γ i) (w i) t) = 0 :=
    fun i ↦ dual_contourResolventKernel_integral_eq_zero K L _ _ (hγ i) (hw i) (havoid i) hL
  simp only [hz, Finset.sum_const_zero, smul_zero]

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.contourResolventKernel_integral_apply
#print axioms RudinRCA.Chapter13.dual_eq_zero_of_finite_contour_representation
end Source18

/- Source: RungeRationalWitness.lean -/
noncomputable section Source19

/-!
Scratch packaging for Rudin 13.6. In the aggregate check this file follows
RungeFunctional.lean (compactCoordinate and its resolvent evaluation) and
RationalPartialFractions.lean (the reduced quotient evaluation bridge).
No global ring-homomorphism property of totalized rational evaluation is used.
-/

open Set Polynomial Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- The linear generators allowed by a prescribed set of spherical poles. -/
def rungeGenerators (K : Set ℂ) (A : Set (OnePoint ℂ)) : Set C(K, ℂ) :=
  {g | g = 1 ∨
    (∃ α : ℂ, (α : OnePoint ℂ) ∈ A ∧ ∃ n : ℕ,
      g = (resolvent (compactCoordinate K) α) ^ (n + 1)) ∨
    ((∞ : OnePoint ℂ) ∈ A ∧ ∃ n : ℕ, g = compactCoordinate K ^ n)}

/-- Finite complex linear combinations of the permitted rational generators. -/
def rungeSpace (K : Set ℂ) (A : Set (OnePoint ℂ)) : Submodule ℂ C(K, ℂ) :=
  Submodule.span ℂ (rungeGenerators K A)

/-- A quotient model whose possible finite poles are prescribed. Equality is
only asserted where the model denominator is nonzero. -/
def HasRungeQuotient (A : Set (OnePoint ℂ)) (F : ℂ → ℂ) : Prop :=
  ∃ P Q : ℂ[X], Q ≠ 0 ∧
    (∀ z : ℂ, Q.eval z = 0 → (z : OnePoint ℂ) ∈ A) ∧
    ∀ z : ℂ, Q.eval z ≠ 0 → P.eval z / Q.eval z = F z

/-- Holomorphic removability in the inverse chart at infinity. -/
def RungeRemovableAtInfinity (F : ℂ → ℂ) : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), F w⁻¹ = h w

theorem hasRungeQuotient_const (A : Set (OnePoint ℂ)) (c : ℂ) :
    HasRungeQuotient A (fun _ => c) := by
  refine ⟨C c, 1, one_ne_zero, ?_, ?_⟩ <;> simp

theorem hasRungeQuotient_add {A : Set (OnePoint ℂ)} {F G : ℂ → ℂ}
    (hF : HasRungeQuotient A F) (hG : HasRungeQuotient A G) :
    HasRungeQuotient A (fun z => F z + G z) := by
  obtain ⟨P, Q, hQ, hrootsQ, heqF⟩ := hF
  obtain ⟨R, S, hS, hrootsS, heqG⟩ := hG
  refine ⟨P * S + R * Q, Q * S, mul_ne_zero hQ hS, ?_, ?_⟩
  · intro z hz
    rw [eval_mul] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hrootsQ z hz
    · exact hrootsS z hz
  · intro z hz
    rw [eval_mul] at hz
    have hQz := (mul_ne_zero_iff.mp hz).1
    have hSz := (mul_ne_zero_iff.mp hz).2
    rw [← heqF z hQz, ← heqG z hSz]
    simp only [eval_add, eval_mul]
    field_simp [hQz, hSz] <;> ring

theorem hasRungeQuotient_smul {A : Set (OnePoint ℂ)} {F : ℂ → ℂ}
    (c : ℂ) (hF : HasRungeQuotient A F) :
    HasRungeQuotient A (fun z => c * F z) := by
  obtain ⟨P, Q, hQ, hroots, heq⟩ := hF
  refine ⟨C c * P, Q, hQ, hroots, ?_⟩
  intro z hz
  rw [eval_mul, eval_C, ← heq z hz]
  ring

theorem rungeRemovableAtInfinity_const (c : ℂ) :
    RungeRemovableAtInfinity (fun _ => c) :=
  ⟨fun _ => c, analyticAt_const, Filter.Eventually.of_forall (fun _ => rfl)⟩

theorem rungeRemovableAtInfinity_add {F G : ℂ → ℂ}
    (hF : RungeRemovableAtInfinity F) (hG : RungeRemovableAtInfinity G) :
    RungeRemovableAtInfinity (fun z => F z + G z) := by
  obtain ⟨f, hf, heqf⟩ := hF
  obtain ⟨g, hg, heqg⟩ := hG
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [heqf, heqg] with w hwf hwg
  rw [hwf, hwg]

theorem rungeRemovableAtInfinity_smul {F : ℂ → ℂ} (c : ℂ)
    (hF : RungeRemovableAtInfinity F) :
    RungeRemovableAtInfinity (fun z => c * F z) := by
  obtain ⟨f, hf, heq⟩ := hF
  refine ⟨fun w => c * f w, analyticAt_const.mul hf, ?_⟩
  filter_upwards [heq] with w hw
  rw [hw]

theorem hasRungeQuotient_reciprocal_power {A : Set (OnePoint ℂ)} (α : ℂ)
    (hα : (α : OnePoint ℂ) ∈ A) (n : ℕ) :
    HasRungeQuotient A (fun z => (α - z)⁻¹ ^ (n + 1)) := by
  have hlinear : (C α - X : ℂ[X]) ≠ 0 := by
    simpa only [neg_sub] using neg_ne_zero.mpr (X_sub_C_ne_zero α)
  refine ⟨1, (C α - X) ^ (n + 1), pow_ne_zero _ hlinear, ?_, ?_⟩
  · intro z hz
    have haz : α = z := by
      by_contra hne
      apply pow_ne_zero (n + 1) (sub_ne_zero.mpr hne)
      simpa only [eval_pow, eval_sub, eval_C, eval_X] using hz
    simpa only [← haz] using hα
  · intro z _
    simp only [eval_one, eval_pow, eval_sub, eval_C, eval_X, one_div, inv_pow]

/-- Every finite principal-part generator is holomorphic at infinity after
the inverse-chart value at zero is supplied. -/
theorem rungeRemovableAtInfinity_reciprocal_power (α : ℂ) (n : ℕ) :
    RungeRemovableAtInfinity (fun z => (α - z)⁻¹ ^ (n + 1)) := by
  have hd : AnalyticAt ℂ (fun w : ℂ => α * w - 1) 0 :=
    (analyticAt_const.mul analyticAt_id).sub analyticAt_const
  have hfrac : AnalyticAt ℂ (fun w : ℂ => w / (α * w - 1)) 0 :=
    analyticAt_id.div hd (by simp)
  refine ⟨fun w => (w / (α * w - 1)) ^ (n + 1), hfrac.pow _, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := by simpa using hw
  have hfactor : α - w⁻¹ = (α * w - 1) / w := by field_simp [hw0]; ring
  rw [hfactor, inv_div]

theorem hasRungeQuotient_coordinate_power (A : Set (OnePoint ℂ)) (n : ℕ) :
    HasRungeQuotient A (fun z => z ^ n) := by
  refine ⟨X ^ n, 1, one_ne_zero, ?_, ?_⟩ <;> simp

/-- Every permitted finite linear combination admits an explicit quotient
model, with a removable point at infinity whenever infinity is not allowed. -/
theorem rungeSpace_quotient_model (K : Set ℂ) (A : Set (OnePoint ℂ))
    (hA : A ⊆ ((fun z : ℂ => (z : OnePoint ℂ)) '' K)ᶜ)
    {g : C(K, ℂ)} (hg : g ∈ rungeSpace K A) :
    ∃ F : ℂ → ℂ, HasRungeQuotient A F ∧
      (∀ x : K, F x = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A → RungeRemovableAtInfinity F) := by
  classical
  apply Submodule.span_induction (p := fun g _ =>
    ∃ F : ℂ → ℂ, HasRungeQuotient A F ∧
      (∀ x : K, F x = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A → RungeRemovableAtInfinity F)) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with rfl | ⟨α, hα, n, rfl⟩ | ⟨hinf, n, rfl⟩
    · exact ⟨fun _ => 1, hasRungeQuotient_const A 1,
        fun _ => rfl, fun _ => rungeRemovableAtInfinity_const 1⟩
    · have hαK : α ∉ K := fun hαK => hA hα ⟨α, hαK, rfl⟩
      refine ⟨fun z => (α - z)⁻¹ ^ (n + 1),
        hasRungeQuotient_reciprocal_power α hα n, ?_,
        fun _ => rungeRemovableAtInfinity_reciprocal_power α n⟩
      intro x
      simp only [ContinuousMap.pow_apply, compactCoordinate_resolvent_apply K hαK]
    · refine ⟨fun z => z ^ n, hasRungeQuotient_coordinate_power A n,
        fun _ => rfl, ?_⟩
      exact fun hnot => (hnot hinf).elim
  · exact ⟨fun _ => 0, hasRungeQuotient_const A 0,
      fun _ => rfl, fun _ => rungeRemovableAtInfinity_const 0⟩
  · intro g h _ _ hg hh
    obtain ⟨F, hF, heqF, hinfF⟩ := hg
    obtain ⟨G, hG, heqG, hinfG⟩ := hh
    refine ⟨fun z => F z + G z, hasRungeQuotient_add hF hG, ?_, ?_⟩
    · intro x
      simp only [heqF, heqG, ContinuousMap.add_apply]
    · exact fun hnot => rungeRemovableAtInfinity_add (hinfF hnot) (hinfG hnot)
  · intro c g _ hg
    obtain ⟨F, hF, heqF, hinfF⟩ := hg
    refine ⟨fun z => c * F z, hasRungeQuotient_smul c hF, ?_, ?_⟩
    · intro x
      simp only [heqF, ContinuousMap.smul_apply, smul_eq_mul]
    · exact fun hnot => rungeRemovableAtInfinity_smul c (hinfF hnot)

/-- A nonzero polynomial denominator has no zeros sufficiently near infinity. -/
theorem eventually_polynomial_eval_inv_ne_zero (Q : ℂ[X]) (hQ : Q ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), Q.eval w⁻¹ ≠ 0 :=
  (Filter.tendsto_inv₀_nhdsNE_zero.mono_right (Bornology.le_cofinite ℂ)).eventually
    (Polynomial.eventually_eval_ne_zero_cofinite hQ)

/-- A member of the Runge generator space is the restriction of an actual
rational function, with no finite poles outside A and no pole at infinity
when infinity is not in A. -/
theorem rungeSpace_ratFunc_witness (K : Set ℂ) (A : Set (OnePoint ℂ))
    (hA : A ⊆ ((fun z : ℂ => (z : OnePoint ℂ)) '' K)ᶜ)
    {g : C(K, ℂ)} (hg : g ∈ rungeSpace K A) :
    ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : OnePoint ℂ) ∈ A) ∧
      (∀ x : K, RatFunc.eval (RingHom.id ℂ) x R = g x) ∧
      ((∞ : OnePoint ℂ) ∉ A →
        RungeRemovableAtInfinity (fun z => RatFunc.eval (RingHom.id ℂ) z R)) := by
  obtain ⟨F, ⟨P, Q, hQ, hroots, heq⟩, hFK, hinf⟩ := rungeSpace_quotient_model K A hA hg
  let R : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q
  have heval (z : ℂ) (hz : Q.eval z ≠ 0) : RatFunc.eval (RingHom.id ℂ) z R = F z := by
    exact (rational_quotient_evaluation P Q z hz).2.trans (heq z hz)
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z hz
    apply hroots
    obtain ⟨S, hS⟩ := RatFunc.denom_div_dvd P Q
    rw [hS, eval_mul]
    change R.denom.eval z * S.eval z = 0
    rw [hz, zero_mul]
  · intro x
    have hQx : Q.eval x ≠ 0 := fun hx => hA (hroots x hx) ⟨x, x.property, rfl⟩
    exact (heval x hQx).trans (hFK x)
  · intro hnot
    obtain ⟨h, hh, heqh⟩ := hinf hnot
    refine ⟨h, hh, ?_⟩
    filter_upwards [heqh, eventually_polynomial_eval_inv_ne_zero Q hQ] with w hw hQw
    exact (heval w⁻¹ hQw).trans hw

#print axioms hasRungeQuotient_const
#print axioms hasRungeQuotient_add
#print axioms hasRungeQuotient_smul
#print axioms rungeRemovableAtInfinity_const
#print axioms rungeRemovableAtInfinity_add
#print axioms rungeRemovableAtInfinity_smul
#print axioms hasRungeQuotient_reciprocal_power
#print axioms rungeRemovableAtInfinity_reciprocal_power
#print axioms hasRungeQuotient_coordinate_power
#print axioms rungeSpace_quotient_model
#print axioms eventually_polynomial_eval_inv_ne_zero
#print axioms rungeSpace_ratFunc_witness

end RudinRCA.Chapter13
end Source19

/- Source: RungePolynomialWitness.lean -/
noncomputable section Source20

/-!
Scratch companion to RungeRationalWitness.lean. In an aggregate this file
follows the definitions of compactCoordinate, rungeGenerators, and rungeSpace.
It supplies the polynomial witness needed when infinity is the only permitted
pole, as in Rudin 13.7.
-/

open Set Polynomial
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- When infinity is the only permitted pole, every element of the Runge
generator span is the restriction of a complex polynomial. -/
theorem rungeSpace_polynomial_witness (K : Set ℂ) {g : C(K, ℂ)}
    (hg : g ∈ rungeSpace K {(∞ : OnePoint ℂ)}) :
    ∃ P : ℂ[X], ∀ x : K, P.eval x = g x := by
  classical
  apply Submodule.span_induction (p := fun g _ =>
    ∃ P : ℂ[X], ∀ x : K, P.eval x = g x) ?_ ?_ ?_ ?_ hg
  · intro g hg
    rcases hg with rfl | ⟨α, hα, n, rfl⟩ | ⟨_, n, rfl⟩
    · exact ⟨1, fun _ => by simp⟩
    · simp at hα
    · exact ⟨X ^ n, fun x => by simp [compactCoordinate]⟩
  · exact ⟨0, fun _ => by simp⟩
  · intro g h _ _ hg hh
    obtain ⟨P, hP⟩ := hg
    obtain ⟨Q, hQ⟩ := hh
    refine ⟨P + Q, ?_⟩
    intro x
    simp only [eval_add, hP, hQ, ContinuousMap.add_apply]
  · intro c g _ hg
    obtain ⟨P, hP⟩ := hg
    refine ⟨C c * P, ?_⟩
    intro x
    simp only [eval_mul, eval_C, hP, ContinuousMap.smul_apply, smul_eq_mul]

#print axioms rungeSpace_polynomial_witness

end RudinRCA.Chapter13
end Source20

/- Source: RungeAssembly.lean -/
noncomputable section Source21

/- Prerequisites, in order: RungeFunctional.lean, CauchyTransformSphere.lean,
   ContourAnnihilator.lean, RungeRationalWitness.lean. This file does not assert existence of the 13.5
   contour; it packages the exact universal representation needed as input. -/
open Set Filter MeasureTheory
open scoped Topology Interval BigOperators OnePoint

namespace RudinRCA.Chapter13

/-- The finite integral data extracted from a 13.5 cycle. The image of every
    edge lies in Ω\K, and the Cauchy identity holds for every holomorphic f. -/
structure FiniteCauchyRepresentation (K Ω : Set ℂ) where
  edgeCount : ℕ
  lower upper : Fin edgeCount → ℝ
  path density : Fin edgeCount → ℝ → ℂ
  subset_domain : K ⊆ Ω
  path_continuous : ∀ i, ContinuousOn (path i) [[lower i, upper i]]
  density_continuous : ∀ i, ContinuousOn (density i) [[lower i, upper i]]
  path_mem : ∀ i t, t ∈ [[lower i, upper i]] → path i t ∈ Ω \ K
  cauchy_identity : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f Ω → ∀ z ∈ K,
    f z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∑ i, ∫ t in lower i..upper i, (f (path i t) * density i t) / (path i t - z)

/-- Restriction of a holomorphic function to a compact subset of its domain. -/
def holomorphicRestriction (K Ω : Set ℂ) (hKΩ : K ⊆ Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) : C(K, ℂ) :=
  ⟨fun z ↦ f z, continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono hKΩ)⟩

/-- The 13.5 representation and one prescribed point per spherical complement
    component place every holomorphic restriction in the closure of any
    submodule containing the corresponding principal parts and polynomials. -/
theorem FiniteCauchyRepresentation.restriction_mem_submodule_closure
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere) (M : Submodule ℂ C(K, ℂ))
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ M)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, compactCoordinate K ^ n ∈ M)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    holomorphicRestriction K Ω C.subset_domain f hf ∈ M.topologicalClosure := by
  apply (mem_submodule_closure_iff_annihilators M _).mpr
  intro L hLM
  have hL : ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0 :=
    compact_cauchy_transform_eq_zero K L A hA hcomponents
      (fun α hα n ↦ hLM _ (hfinite α hα n))
      (fun h∞ n ↦ hLM _ (hinfty h∞ n))
  apply dual_eq_zero_of_finite_contour_representation K _ L C.path
    (fun i t ↦ f (C.path i t) * C.density i t) C.lower C.upper
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) C.path_continuous
  · intro i
    exact (hf.continuousOn.comp (C.path_continuous i)
      (fun t ht ↦ (C.path_mem i t ht).1)).mul (C.density_continuous i)
  · intro i t ht
    exact (C.path_mem i t ht).2
  · intro x
    exact C.cauchy_identity f hf x x.property
  · exact hL

/-- Quantitative approximation follows from closure in the C(K) norm.
    The rational-function witness is supplied separately by the generator algebra. -/
theorem FiniteCauchyRepresentation.exists_submodule_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere) (M : Submodule ℂ C(K, ℂ))
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ M)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, compactCoordinate K ^ n ∈ M)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ M, ∀ x : K, ‖f x - g x‖ < ε := by
  let F : C(K, ℂ) := holomorphicRestriction K Ω C.subset_domain f hf
  have hF : F ∈ closure (M : Set C(K, ℂ)) :=
    C.restriction_mem_submodule_closure A M hA hcomponents hfinite hinfty f hf
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hF ε hε
  refine ⟨g, hg, fun x ↦ ?_⟩
  have hp := ContinuousMap.dist_apply_le_dist (f := F) (g := g) x
  simpa only [dist_eq_norm] using hp.trans_lt hdist

/-- Full rational-approximation conclusion from an explicitly supplied universal
    13.5 representation. Existence of that representation is proved separately. -/
theorem FiniteCauchyRepresentation.exists_rational_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ K, ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < ε := by
  have hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ rungeSpace K A := by
    intro α hα n
    exact Submodule.subset_span (Or.inr (Or.inl ⟨α, hα, n, rfl⟩))
  have hinfty : (∞ : RiemannSphere) ∈ A →
      ∀ n : ℕ, compactCoordinate K ^ n ∈ rungeSpace K A := by
    intro h∞ n
    exact Submodule.subset_span (Or.inr (Or.inr ⟨h∞, n, rfl⟩))
  obtain ⟨g, hg, herror⟩ :=
    C.exists_submodule_approximation A (rungeSpace K A) hA hcomponents hfinite hinfty f hf hε
  obtain ⟨R, hRfinite, hReval, hRinfty⟩ := rungeSpace_ratFunc_witness K A hA hg
  refine ⟨R, hRfinite, hRinfty, ?_⟩
  intro z hz
  simpa only [← hReval ⟨z, hz⟩] using herror ⟨z, hz⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.restriction_mem_submodule_closure
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_submodule_approximation
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_rational_approximation
end Source21

/- Source: RungeUniformSequences.lean -/
noncomputable section Source22

/- Prerequisites: RungeAssembly.lean and RungePolynomialWitness.lean.
   These are conditional consequences of an actual universal finite Cauchy
   representation; this file does not assert that representation exists. -/
open Set Filter
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- With connected spherical complement the only prescribed pole can be infinity. -/
theorem FiniteCauchyRepresentation.exists_polynomial_approximation
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' K)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  have hA : {(∞ : RiemannSphere)} ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ := by
    intro p hp
    have hp' : p = ∞ := hp
    subst p
    simp
  have hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ ({∞} : Set RiemannSphere),
        a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p := by
    intro p hp
    refine ⟨∞, by simp, ?_⟩
    rw [hconn.isPreconnected.connectedComponentIn hp]
    simp
  have hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ ({∞} : Set RiemannSphere) →
      ∀ n : ℕ, resolvent (compactCoordinate K) α ^ (n + 1) ∈ rungeSpace K {∞} := by
    intro α hα
    simp at hα
  have hinfty : (∞ : RiemannSphere) ∈ ({∞} : Set RiemannSphere) →
      ∀ n : ℕ, compactCoordinate K ^ n ∈ rungeSpace K {∞} := by
    intro h∞ n
    exact Submodule.subset_span (Or.inr (Or.inr ⟨h∞, n, rfl⟩))
  obtain ⟨g, hg, herror⟩ := C.exists_submodule_approximation {∞}
    (rungeSpace K {∞}) hA hcomponents hfinite hinfty f hf hε
  obtain ⟨P, hP⟩ := rungeSpace_polynomial_witness K hg
  refine ⟨P, fun z hz ↦ ?_⟩
  simpa only [← hP ⟨z, hz⟩] using herror ⟨z, hz⟩

/-- The quantitative polynomial approximations can be chosen as a uniformly
    convergent sequence, the conclusion printed in Rudin 13.7. -/
theorem FiniteCauchyRepresentation.exists_polynomial_uniform_sequence
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (hconn : IsConnected ((((↑) : ℂ → RiemannSphere) '' K)ᶜ))
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ (P n).eval z) f atTop K := by
  have hex : ∀ n : ℕ, ∃ P : Polynomial ℂ,
      ∀ z ∈ K, ‖f z - P.eval z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact C.exists_polynomial_approximation hconn f hf (by positivity)
  choose P hP using hex
  refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  intro z hz
  simpa only [dist_eq_norm] using (hP n z hz).trans hn

/-- The rational approximation conclusion of 13.6 includes a sequence with
    the prescribed spherical pole restriction at every index. -/
theorem FiniteCauchyRepresentation.exists_rational_uniform_sequence
    {K Ω : Set ℂ} [CompactSpace K] (C : FiniteCauchyRepresentation K Ω)
    (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) :
    ∃ R : ℕ → RatFunc ℂ,
      (∀ n z, (R n).denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A → ∀ n,
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z (R n))) ∧
      TendstoUniformlyOn (fun n z ↦ RatFunc.eval (RingHom.id ℂ) z (R n)) f atTop K := by
  have hex : ∀ n : ℕ, ∃ R : RatFunc ℂ,
      (∀ z : ℂ, R.denom.eval z = 0 → (z : RiemannSphere) ∈ A) ∧
      ((∞ : RiemannSphere) ∉ A →
        RungeRemovableAtInfinity (fun z ↦ RatFunc.eval (RingHom.id ℂ) z R)) ∧
      ∀ z ∈ K, ‖f z - RatFunc.eval (RingHom.id ℂ) z R‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact C.exists_rational_approximation A hA hcomponents f hf (by positivity)
  choose R hRfinite hRinfty herror using hex
  refine ⟨R, hRfinite, fun h∞ n ↦ hRinfty n h∞,
    Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  intro z hz
  simpa only [dist_eq_norm] using (herror n z hz).trans hn

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_polynomial_approximation
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_polynomial_uniform_sequence
#print axioms RudinRCA.Chapter13.FiniteCauchyRepresentation.exists_rational_uniform_sequence
end Source22

/- Source: GridGeometry.lean -/
noncomputable section Source23

open Set Metric
namespace RudinRCA.Chapter13

/-- A closed square of the axis-parallel grid with positive mesh `δ`. -/
def gridClosedCell (δ : ℝ) (c : ℤ × ℤ) : Set ℂ :=
  Icc (δ * c.1) (δ * (c.1 + 1)) ×ℂ Icc (δ * c.2) (δ * (c.2 + 1))

theorem gridClosedCell_isCompact (δ : ℝ) (c : ℤ × ℤ) :
    IsCompact (gridClosedCell δ c) := isCompact_Icc.reProdIm isCompact_Icc

theorem exists_mem_gridClosedCell {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ∃ c : ℤ × ℤ, z ∈ gridClosedCell δ c := by
  refine ⟨(⌊z.re / δ⌋, ⌊z.im / δ⌋), ?_⟩
  change (δ * (⌊z.re / δ⌋ : ℝ) ≤ z.re ∧ z.re ≤ δ * ((⌊z.re / δ⌋ : ℝ) + 1)) ∧
    (δ * (⌊z.im / δ⌋ : ℝ) ≤ z.im ∧ z.im ≤ δ * ((⌊z.im / δ⌋ : ℝ) + 1))
  constructor
  · exact ⟨by simpa [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.re / δ)),
      by simpa [mul_comm] using (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.re / δ)).le⟩
  · exact ⟨by simpa [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.im / δ)),
      by simpa [mul_comm] using (div_le_iff₀ hδ).mp (Int.lt_floor_add_one (z.im / δ)).le⟩

theorem dist_le_two_mesh_of_mem_gridClosedCell {δ : ℝ} {c : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ gridClosedCell δ c) (hw : w ∈ gridClosedCell δ c) :
    dist z w ≤ 2 * δ := by
  change (_ ≤ z.re ∧ z.re ≤ _) ∧ (_ ≤ z.im ∧ z.im ≤ _) at hz
  change (_ ≤ w.re ∧ w.re ≤ _) ∧ (_ ≤ w.im ∧ w.im ≤ _) at hw
  have hre : |z.re - w.re| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.1.1, hw.1.2],
    by nlinarith [hz.1.2, hw.1.1]⟩
  have him : |z.im - w.im| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.2.1, hw.2.2],
    by nlinarith [hz.2.2, hw.2.1]⟩
  rw [dist_eq_norm]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hnorm
  linarith

theorem finite_gridCells_meeting_compact {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    {c : ℤ × ℤ | (gridClosedCell δ c ∩ K).Nonempty}.Finite := by
  obtain ⟨M, _, hM⟩ := hK.isBounded.exists_pos_norm_le
  let lo : ℤ := ⌊-M / δ⌋ - 1
  let hi : ℤ := ⌈M / δ⌉
  apply ((Set.finite_Icc lo hi).prod (Set.finite_Icc lo hi)).subset
  rintro c ⟨z, hzc, hzK⟩
  change (_ ≤ z.re ∧ z.re ≤ _) ∧ (_ ≤ z.im ∧ z.im ≤ _) at hzc
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans (hM z hzK))
  have him := abs_le.mp ((Complex.abs_im_le_norm z).trans (hM z hzK))
  have hcoord : ∀ (n : ℤ) (x : ℝ), -M ≤ x → x ≤ M →
      δ * n ≤ x → x ≤ δ * ((n : ℝ) + 1) → n ∈ Icc lo hi := by
    intro n x hx₁ hx₂ hn₁ hn₂
    have hu : (n : ℝ) ≤ M / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
    have hl : -M / δ ≤ (n : ℝ) + 1 := (div_le_iff₀ hδ).mpr (by nlinarith)
    constructor
    · have hh := Int.floor_le (-M / δ)
      dsimp [lo]
      exact_mod_cast (show (⌊-M / δ⌋ : ℝ) - 1 ≤ (n : ℝ) by linarith)
    · exact_mod_cast hu.trans (Int.le_ceil (M / δ))
  exact ⟨hcoord c.1 z.re hre.1 hre.2 hzc.1.1 hzc.1.2,
    hcoord c.2 z.im him.1 him.2 hzc.2.1 hzc.2.2⟩

/-- A compact set has a finite grid-square cover lying inside any prescribed open neighborhood. -/
theorem finite_grid_cover {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∃ S : Finset (ℤ × ℤ),
      (∀ c, c ∈ S ↔ (gridClosedCell δ c ∩ K).Nonempty) ∧
      K ⊆ ⋃ c ∈ S, gridClosedCell δ c ∧
      ∀ c ∈ S, gridClosedCell δ c ⊆ Ω := by
  classical
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S := (finite_gridCells_meeting_compact hK hδ).toFinset
  have hS : ∀ c, c ∈ S ↔ (gridClosedCell δ c ∩ K).Nonempty := by
    intro c
    exact Set.Finite.mem_toFinset _
  refine ⟨δ, hδ, S, hS, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, hc⟩ := exists_mem_gridClosedCell hδ z
    exact mem_iUnion₂.mpr ⟨c, (hS c).mpr ⟨z, hc, hz⟩, hc⟩
  · intro c hc z hz
    obtain ⟨w, hwc, hwK⟩ := (hS c).mp hc
    apply hεΩ
    apply mem_cthickening_of_dist_le z w ε K hwK
    have hd := dist_le_two_mesh_of_mem_gridClosedCell hz hwc
    dsimp [δ] at hd
    linarith

/-- The grid cover can be chosen to contain a whole neighborhood of the compact set.
The enlarged compact set used in the construction avoids any assumption that `K` has interior. -/
theorem finite_grid_neighborhood {K Ω : Set ℂ} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, ∃ S : Finset (ℤ × ℤ),
      K ⊆ interior (⋃ c ∈ S, gridClosedCell δ c) ∧
      (∀ c, (gridClosedCell δ c ∩ K).Nonempty → c ∈ S) ∧
      ∀ c ∈ S, gridClosedCell δ c ⊆ Ω := by
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening ε K
  have hL : IsCompact L := hK.cthickening
  have hKL : K ⊆ interior L :=
    (self_subset_thickening hε K).trans (thickening_subset_interior_cthickening ε K)
  obtain ⟨δ, hδ, S, hS, hcover, hinside⟩ := finite_grid_cover hL hΩ hεΩ
  refine ⟨δ, hδ, S, hKL.trans (interior_mono hcover), ?_, hinside⟩
  rintro c ⟨z, hzc, hzK⟩
  exact (hS c).mpr ⟨z, hzc, interior_subset (hKL hzK)⟩

#print axioms gridClosedCell_isCompact
#print axioms exists_mem_gridClosedCell
#print axioms dist_le_two_mesh_of_mem_gridClosedCell
#print axioms finite_gridCells_meeting_compact
#print axioms finite_grid_cover
#print axioms finite_grid_neighborhood
end RudinRCA.Chapter13
end Source23

/- Source: GridSupport.lean -/
noncomputable section Source24

/-! Pending scratch; compile after GridBoundary.lean and GridGeometry.lean. -/
open Set Function
namespace RudinRCA.Chapter13

def gridPoint (δ : ℝ) (c : ℤ × ℤ) : ℂ :=
  ((δ * c.1 : ℝ) : ℂ) + ((δ * c.2 : ℝ) : ℂ) * Complex.I

theorem gridClosedCell_convex (δ : ℝ) (c : ℤ × ℤ) : Convex ℝ (gridClosedCell δ c) :=
  ((convex_Icc (δ * c.1) (δ * (c.1 + 1))).linear_preimage Complex.reLm).inter
    ((convex_Icc (δ * c.2) (δ * (c.2 + 1))).linear_preimage Complex.imLm)

theorem gridVertex_mem_cell {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridPoint δ (gridVertex c i) ∈ gridClosedCell δ c := by
  fin_cases i <;>
    simp [gridPoint, gridVertex, gridCorner, gridClosedCell] <;>
    constructor <;> nlinarith

def gridEdgeSupport (δ : ℝ) (c : ℤ × ℤ) (i : Fin 4) : Set ℂ :=
  segment ℝ (gridPoint δ (gridVertex c i)) (gridPoint δ (gridVertex c (i + 1)))

theorem gridEdgeSupport_subset_cell {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridEdgeSupport δ c i ⊆ gridClosedCell δ c :=
  (gridClosedCell_convex δ c).segment_subset (gridVertex_mem_cell hδ c i)
    (gridVertex_mem_cell hδ c (i + 1))

theorem gridEdgeSupport_subset_neighbor {δ : ℝ} (hδ : 0 ≤ δ) (c : ℤ × ℤ) (i : Fin 4) :
    gridEdgeSupport δ c i ⊆ gridClosedCell δ (gridNeighbor c i) := by
  apply (gridClosedCell_convex δ (gridNeighbor c i)).segment_subset
  · rw [← gridVertex_reverse_terminal c i]
    exact gridVertex_mem_cell hδ _ _
  · rw [← gridVertex_reverse_initial c i]
    exact gridVertex_mem_cell hδ _ _

/-- Every uncancelled edge lies in the open domain and avoids the original compact set. -/
theorem gridBoundary_support_subset {K Ω : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    {S : Finset (ℤ × ℤ)}
    (hcover : ∀ c, (gridClosedCell δ c ∩ K).Nonempty → c ∈ S)
    (hinside : ∀ c ∈ S, gridClosedCell δ c ⊆ Ω)
    {c : ℤ × ℤ} (hc : c ∈ S) {i : Fin 4} (hout : gridNeighbor c i ∉ S) :
    gridEdgeSupport δ c i ⊆ Ω \ K := by
  intro z hz
  refine ⟨hinside c hc (gridEdgeSupport_subset_cell hδ c i hz), ?_⟩
  intro hzK
  exact hout (hcover _ ⟨z, gridEdgeSupport_subset_neighbor hδ c i hz, hzK⟩)

def complexGridInitial {S : Finset (ℤ × ℤ)} (δ : ℝ) (e : GridEdge S) : ℂ :=
  gridPoint δ (gridEdgeInitial e)

def complexGridTerminal {S : Finset (ℤ × ℤ)} (δ : ℝ) (e : GridEdge S) : ℂ :=
  gridPoint δ (gridEdgeTerminal e)

/-- Balance after passing from lattice vertices to actual complex endpoints. -/
theorem complexGridBoundary_balanced (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    ∀ v : ℂ, Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      complexGridInitial δ e.1 = v} =
      Nat.card {e : {e : GridEdge S // ¬gridEdgeInternal e} //
      complexGridTerminal δ e.1 = v} := by
  classical
  apply balanced_complement
  · apply balanced_of_successor _ _ ((Equiv.refl S).prodCongr (finRotate 4))
    intro e
    simp [complexGridTerminal, complexGridInitial, gridEdgeTerminal, gridEdgeInitial,
      finRotate_apply]
  · apply balanced_of_successor _ _
      ({ toFun := gridInternalReverse S, invFun := gridInternalReverse S,
         left_inv := gridInternalReverse_involutive S,
         right_inv := gridInternalReverse_involutive S } : Equiv.Perm _)
    intro e
    exact congrArg (gridPoint δ) (gridVertex_reverse_initial _ _).symm

#print axioms gridClosedCell_convex
#print axioms gridVertex_mem_cell
#print axioms gridEdgeSupport_subset_cell
#print axioms gridEdgeSupport_subset_neighbor
#print axioms gridBoundary_support_subset
#print axioms complexGridBoundary_balanced
end RudinRCA.Chapter13
end Source24

