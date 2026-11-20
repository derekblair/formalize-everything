import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Algebra.Algebra.Pi

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
