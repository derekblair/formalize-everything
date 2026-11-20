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
  exact hz.2 (by simpa only [haopen.interior_eq, heq] using hzC)

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
      (sub_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using hz))).differentiableWithinAt
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
  calc
    _ = ∫ t : ℝ in -1..1, (((t : ℂ) - I)⁻¹ - ((t : ℂ) + I)⁻¹ +
        I * (1 + (t : ℂ) * I)⁻¹ - I * (-1 + (t : ℂ) * I)⁻¹) := by
      rw [integral_sub (((h₁.sub h₂).add (continuous_const.mul h₃)).intervalIntegrable (-1) 1)
          ((continuous_const.mul h₄).intervalIntegrable (-1) 1),
        integral_add ((h₁.sub h₂).intervalIntegrable (-1) 1)
          ((continuous_const.mul h₃).intervalIntegrable (-1) 1),
        integral_sub (h₁.intervalIntegrable (-1) 1) (h₂.intervalIntegrable (-1) 1),
        integral_const_mul, integral_const_mul]
    _ = ∫ t : ℝ in -1..1, 4 * I * ((1 / (1 + t ^ 2) : ℝ) : ℂ) := by
      apply integral_congr
      intro t ht
      exact square_kernel_integrand t
    _ = 2 * (Real.pi : ℂ) * I := by
      rw [integral_const_mul, integral_ofReal, integral_one_div_one_add_sq,
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
    (ha.intervalIntegrable (a := c) (b := d)) (ha.intervalIntegrable (a := d) (b := e))
  have hB := integral_add_adjacent_intervals
    (hb.intervalIntegrable (a := c) (b := d)) (hb.intervalIntegrable (a := d) (b := e))
  dsimp [rectangleIntegral]
  rw [← hA, ← hB]
  ring

theorem rectangleIntegral_split_horizontal (f : ℂ → ℂ) (a b c d e : ℝ)
    (hc : Continuous (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)))
    (hd : Continuous (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))) :
    rectangleIntegral f a e c d =
      rectangleIntegral f a b c d + rectangleIntegral f b e c d := by
  have hC := integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := a) (b := b)) (hc.intervalIntegrable (a := b) (b := e))
  have hD := integral_add_adjacent_intervals
    (hd.intervalIntegrable (a := a) (b := b)) (hd.intervalIntegrable (a := b) (b := e))
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
    min_pos (min_pos (neg_pos.mpr ha) hb) (min_pos (neg_pos.mpr hc) hd)
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
        congr 1
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right _ z.re
  have hv (q : ℝ) :
      (∫ y : ℝ in c..d, f ((q : ℂ) + (y : ℂ) * I + z)) =
      ∫ y : ℝ in c + z.im..d + z.im, f (((q + z.re : ℝ) : ℂ) + (y : ℂ) * I) := by
    calc
      _ = ∫ y : ℝ in c..d,
          f (((q + z.re : ℝ) : ℂ) + ((y + z.im : ℝ) : ℂ) * I) := by
        apply integral_congr
        intro y hy
        congr 1
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right _ z.im
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
  refine ⟨fun z => Complex.log c + g z, differentiableOn_const.add hg, ?_⟩
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
  letI : IsClosed (M : Set E) := hM
  have hx : M.mkQL x = 0 := by
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero
    intro L
    apply h (L.comp M.mkQL)
    intro y hy
    have hyq : M.mkQL y = 0 := Submodule.Quotient.mk_eq_zero.mpr hy
    simp [hyq]
  exact Submodule.Quotient.mk_eq_zero.mp hx

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
    DifferentiableOn ℂ (fun z ↦ L (spectrum.resolvent a z)) (spectrum ℂ a)ᶜ := by
  intro z hz
  have hz' : z ∈ resolventSet ℂ a := by simpa only [spectrum, compl_compl] using hz
  exact (L.differentiableAt.comp z
    (spectrum.hasDerivAt_resolvent_const_left hz').differentiableAt).differentiableWithinAt

/-- The C(K)-valued resolvent evaluates to the usual Cauchy kernel. -/
theorem compactCoordinate_resolvent_apply (K : Set ℂ) {z : ℂ} (hz : z ∉ K) (x : K) :
    spectrum.resolvent (compactCoordinate K) z x = (z - (x : ℂ))⁻¹ := by
  have hz' : z ∈ resolventSet ℂ (compactCoordinate K) := by
    apply spectrum.notMem_iff.mp
    rwa [spectrum_compactCoordinate]
  have hh := congrArg (fun g : C(K, ℂ) ↦ g x)
    (Ring.inverse_mul_cancel (algebraMap ℂ C(K, ℂ) z - compactCoordinate K) hz')
  have hm : spectrum.resolvent (compactCoordinate K) z x * (z - (x : ℂ)) = 1 := by
    simpa [spectrum.resolvent, compactCoordinate] using hh
  exact eq_inv_of_mul_eq_one_left hm

/-- This Cauchy transform uses a bounded linear functional directly, without a measure representation. -/
theorem differentiableOn_compact_cauchy_transform (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z ↦ L (spectrum.resolvent (compactCoordinate K) z)) Kᶜ := by
  simpa only [spectrum_compactCoordinate] using differentiableOn_dual_resolvent (compactCoordinate K) L

/-- Resolvent expansion around any point outside the spectrum. -/
theorem resolvent_shift {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : A) {α : ℂ} (hα : α ∈ resolventSet ℂ a) (β : ℂ) :
    spectrum.resolvent a β = spectrum.resolvent a α *
      Ring.inverse (1 - (α - β) • spectrum.resolvent a α) := by
  have hfactor : algebraMap ℂ A β - a =
      (algebraMap ℂ A α - a) * (1 - (α - β) • spectrum.resolvent a α) := by
    rw [mul_sub, mul_one, mul_smul_comm]
    rw [spectrum.resolvent, Ring.mul_inverse_cancel _ hα]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  conv_lhs => rw [spectrum.resolvent, hfactor]
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
    (h : ∀ n : ℕ, L (spectrum.resolvent a α ^ (n + 1)) = 0) :
    (fun β ↦ L (spectrum.resolvent a β)) =ᶠ[𝓝 α] 0 := by
  have hc : Continuous (fun β : ℂ ↦ ‖(α - β) • spectrum.resolvent a α‖) := by fun_prop
  have hsmall : ∀ᶠ β in 𝓝 α, ‖(α - β) • spectrum.resolvent a α‖ < 1 :=
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
    spectrum.resolvent a w⁻¹ = w • Ring.inverse (1 - w • a) := by
  have h := congrArg (fun v : A ↦ w • v)
    (spectrum.units_smul_resolvent_self (r := (Units.mk0 w hw)⁻¹) (a := a))
  simpa [spectrum.resolvent, smul_smul, hw] using h

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
  rw [isClosed_iff_compl_open, isOpen_iff_mem_nhds]
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
      (Equiv.ofInvolutive (gridInternalReverse S) (gridInternalReverse_involutive S))
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

