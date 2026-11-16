import Garling.Chapter01
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter07
import Garling.Chapter09
import Garling.Chapter10
import Garling.Chapter11
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Chapter 12: Finite fields

Formalization of Chapter 12 (*Finite fields*, printed pp. 101–106 / PDF pp. 109–114) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
unnumbered chapter preamble, all five sections (`§12.1`–`§12.5`), all 10 main-text
theorem/corollary items (`Theorem 12.1`–`Theorem 12.4` + `6` corollaries), all 11 numbered
exercises (`Exercise 12.1`–`Exercise 12.11`), and all unnumbered prose definitions, deductions,
and worked examples in exact source order.

Note: Chapter 12 imports only `Garling.Chapter01`, `Chapter03`, `Garling.Chapter04`,
`Garling.Chapter07`, `Garling.Chapter09`, `Garling.Chapter10`, and `Garling.Chapter11`
(zero Chapter 8 algebraic-closure material and zero later chapters).
-/

namespace Garling.Chapter12

open Garling.Chapter01 Garling.Chapter03 Garling.Chapter04
open Garling.Chapter07 Garling.Chapter09 Garling.Chapter10 Garling.Chapter11
open scoped BigOperators Polynomial IntermediateField DirectSum

universe u v w

/-! ## §12.1 A description of the finite fields (printed pp. 101–102, PDF pp. 109–110) -/

/-- Garling's inline prose definition of a *finite field* (§12.1, printed p. 101 / PDF p. 109):
*"Suppose that `K` is a finite field: that is, a field with only finitely many elements."* -/
def IsGarlingFiniteField (K : Type*) [Field K] : Prop :=
  setOrder K < ⊤

/-- Bridge between `IsGarlingFiniteField K` (`setOrder K < ⊤`) and `Finite K`. -/
theorem isGarlingFiniteField_iff (K : Type*) [Field K] :
    IsGarlingFiniteField K ↔ Finite K := by
  unfold IsGarlingFiniteField setOrder
  rw [ENat.card_lt_top]

/-- Helper: `setOrder X = (m : ℕ)` iff `Finite X ∧ Nat.card X = m`. -/
private theorem setOrder_eq_natCast_iff {X : Type*} {m : ℕ} :
    setOrder X = (m : ℕ) ↔ Finite X ∧ Nat.card X = m := by
  constructor
  · intro h
    have hfin : Finite X := by
      rw [← ENat.card_lt_top]
      change setOrder X < ⊤
      rw [h]
      exact ENat.natCast_lt_top m
    let _ : Fintype X := Fintype.ofFinite X
    rw [setOrder, ENat.card_eq_coe_fintype_card] at h
    exact ⟨hfin, (Nat.card_eq_fintype_card).trans (Nat.cast_injective h)⟩
  · rintro ⟨hfin, hcard⟩
    let _ : Fintype X := Fintype.ofFinite X
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard]

/-- Helper: for any commutative nontrivial ring `R` and `1 < m`, `X^m - X` is monic of degree `m`. -/
private theorem monic_and_natDegree_X_pow_sub_X (R : Type*) [CommRing R] [Nontrivial R]
    {m : ℕ} (hm : 1 < m) :
    (Polynomial.X ^ m - Polynomial.X : R[X]).Monic ∧
    (Polynomial.X ^ m - Polynomial.X : R[X]).natDegree = m := by
  have hdeg_lt : (Polynomial.X : R[X]).degree < (m : WithBot ℕ) := by
    rw [Polynomial.degree_X]
    exact WithBot.coe_lt_coe.mpr hm
  have hmon : (Polynomial.X ^ m - Polynomial.X : R[X]).Monic :=
    Polynomial.monic_X_pow_sub hdeg_lt
  have hnat_lt : (Polynomial.X : R[X]).natDegree < (Polynomial.X ^ m : R[X]).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    exact hm
  have hdeg : (Polynomial.X ^ m - Polynomial.X : R[X]).natDegree = m := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hnat_lt, Polynomial.natDegree_X_pow]
  exact ⟨hmon, hdeg⟩

/-- Helper: if `m, g : K[X]` are monic, `Irreducible g`, `¬ IsUnit m`, and `m ∣ g`, then `m = g`. -/
private theorem eq_of_monic_dvd_irreducible {K : Type*} [Field K] {m g : K[X]}
    (hm_mon : m.Monic) (hg_mon : g.Monic) (hm_nu : ¬ IsUnit m) (hg_irr : Irreducible g)
    (hdvd : m ∣ g) : m = g := by
  obtain ⟨q, hq⟩ := hdvd
  have hq_u : IsUnit q := (hg_irr.isUnit_or_isUnit hq).resolve_left hm_nu
  have hq_deg : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hq_u
  have hq_mon : q.Monic := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, hg_mon.leadingCoeff, hm_mon.leadingCoeff, one_mul] at hlc
    exact hlc.symm
  rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]

/-- Helper extracting a root in `L` from `GarlingSplitsOver K L g` when `1 ≤ g.natDegree`. -/
private theorem exists_root_of_garlingSplitsOver {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {g : K[X]}
    (hsp : GarlingSplitsOver K L g) (hdeg : 1 ≤ g.natDegree) :
    ∃ α : L, Polynomial.aeval α g = 0 := by
  obtain ⟨m, lam, α, hexp⟩ := hsp
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · exfalso
    have hd := congrArg Polynomial.natDegree hexp
    rw [Polynomial.natDegree_map (algebraMap K L)] at hd
    simp at hd
    omega
  · refine ⟨α ⟨0, hm_pos⟩, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
      Polynomial.eval_prod]
    rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, hm_pos⟩) (by simp), mul_zero]

/-- Helper: if `p, q` are primes and `p ^ m = q ^ n` with `0 < m`, then `p = q` and `m = n`. -/
private theorem eq_and_exp_eq_of_prime_pow_eq {p q m n : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hm : 0 < m) (h : p ^ m = q ^ n) :
    p = q ∧ m = n := by
  have hdvd : p ∣ q ^ n := ⟨p ^ (m - 1), by rw [← pow_succ', Nat.sub_add_cancel hm, h]⟩
  have hpq_dvd : p ∣ q := hp.dvd_of_dvd_pow hdvd
  have hpq : p = q := (hq.eq_one_or_self_of_dvd p hpq_dvd).resolve_left hp.ne_one
  subst hpq
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

/-- Helper extracting `ringChar L = p` when `p` is prime and `((p : ℕ) : L) = 0`. -/
private theorem ringChar_eq_of_prime_natCast_eq_zero {L : Type*} [Field L] {p : ℕ}
    (hp : Nat.Prime p) (h0 : ((p : ℕ) : L) = 0) : ringChar L = p := by
  have hdvd : ringChar L ∣ p := (ringChar.spec L p).mp h0
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | heq
  · exfalso
    have h10 : ((1 : ℕ) : L) = 0 := by
      rw [← h1]
      exact ringChar.Nat.cast_ringChar
    rw [Nat.cast_one] at h10
    exact one_ne_zero h10
  · exact heq

/-- Introductory prose deduction of §12.1 (printed p. 101 / PDF p. 109):
*"Suppose that `K` is a finite field: that is, a field with only finitely many elements. Then
`char K = p > 0`, and we can identify `ℤ_p` and the prime subfield of `K`. As `K` is finite,
`[K : ℤ_p]` must be finite. If `[K : ℤ_p] = n`, then `K` is an `n`-dimensional vector space over
`ℤ_p`, and as a vector space, `K` is isomorphic to `(ℤ_p)^n`. Thus `|K| = p^n`."* -/
theorem finite_field_char_and_prime_power (K : Type u) [Field K] [Finite K] :
    let p := ringChar K
    let n := Module.finrank (primeSubfield K) K
    0 < p ∧
    Nat.Prime p ∧
    Nonempty (primeSubfield K ≃+* ZMod p) ∧
    IsFiniteExtension (primeSubfield K) K ∧
    0 < n ∧
    extDegree (primeSubfield K) K = n ∧
    Nonempty (K ≃ₗ[primeSubfield K] Kn n (primeSubfield K)) ∧
    Nat.card K = p ^ n ∧
    setOrder K = (p ^ n : ℕ) := by
  intro p n
  have hp_ne0 : p ≠ 0 := by
    intro h0
    obtain ⟨eQ⟩ := (theorem_3_17 K).1 h0
    have _ : Finite (primeSubfield K) :=
      Finite.of_injective (primeSubfield K).subtype Subtype.val_injective
    have _ : Finite ℚ := Finite.of_equiv (primeSubfield K) eQ.toEquiv
    exact not_finite ℚ
  obtain ⟨hp_prime, ⟨eZp⟩⟩ := (theorem_3_17 K).2 hp_ne0
  have hfin_ext : IsFiniteExtension (primeSubfield K) K :=
    (isFiniteExtension_iff_moduleFinite (primeSubfield K) K).mpr inferInstance
  have hn_pos : 0 < n := Module.finrank_pos
  have hext : extDegree (primeSubfield K) K = n :=
    extDegree_eq_finrank (primeSubfield K) K
  let b : Module.Basis (Fin n) (primeSubfield K) K := Module.finBasis (primeSubfield K) K
  let linEquiv : K ≃ₗ[primeSubfield K] Kn n (primeSubfield K) := b.equivFun
  have _ : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hcard_prime : Nat.card (primeSubfield K) = p := by
    rw [Nat.card_congr eZp.toEquiv, Nat.card_zmod]
  have hcard_K : Nat.card K = p ^ n := by
    rw [Nat.card_congr linEquiv.toEquiv, Kn, Nat.card_fun, hcard_prime, Nat.card_fin]
  have hset_K : setOrder K = (p ^ n : ℕ) :=
    setOrder_eq_natCast_iff.mpr ⟨inferInstance, hcard_K⟩
  exact ⟨hp_prime.pos, hp_prime, ⟨eZp⟩, hfin_ext, hn_pos, hext, ⟨linEquiv⟩, hcard_K, hset_K⟩

/-- Ring-homomorphism power iterate of `garlingFrobenius` (`α ↦ α^{p^d}`). -/
def garlingFrobeniusPowHom (K : Type*) [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) : ℕ → (K →+* K)
  | 0 => RingHom.id K
  | d + 1 => (garlingFrobenius K hchar hp0).comp (garlingFrobeniusPowHom K hchar hp0 d)

@[simp]
theorem garlingFrobeniusPowHom_apply {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) (d : ℕ) (α : K) :
    garlingFrobeniusPowHom K hchar hp0 d α = α ^ (p ^ d) := by
  induction d with
  | zero => simp [garlingFrobeniusPowHom]
  | succ d ih =>
    simp only [garlingFrobeniusPowHom, RingHom.comp_apply, ih, garlingFrobenius_apply,
      ← pow_mul, pow_succ]

theorem garlingFrobenius_iterate_apply {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) (d : ℕ) (α : K) :
    (garlingFrobenius K hchar hp0)^[d] α = α ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, garlingFrobenius_apply, ← pow_mul, pow_succ]

/-- Subfield `{α : K | φ^d(α) = α} = {α : K | α^{p^d} = α}` fixed by `φ^d` (`Theorem 12.1` proof,
printed p. 101 / PDF p. 109). -/
def frobeniusIterFixedSubfield (K : Type*) [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) (d : ℕ) : Subfield K where
  carrier := {α : K | garlingFrobeniusPowHom K hchar hp0 d α = α}
  mul_mem' {a b} ha hb := by
    change garlingFrobeniusPowHom K hchar hp0 d (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one _
  add_mem' {a b} ha hb := by
    change garlingFrobeniusPowHom K hchar hp0 d (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := map_zero _
  neg_mem' {a} ha := by
    change garlingFrobeniusPowHom K hchar hp0 d (-a) = -a
    rw [map_neg, ha]
  inv_mem' {a} ha := by
    change garlingFrobeniusPowHom K hchar hp0 d a⁻¹ = a⁻¹
    rw [map_inv₀, ha]

@[simp]
theorem mem_frobeniusIterFixedSubfield_iff {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) (d : ℕ) (α : K) :
    α ∈ frobeniusIterFixedSubfield K hchar hp0 d ↔ α ^ (p ^ d) = α := by
  change garlingFrobeniusPowHom K hchar hp0 d α = α ↔ α ^ (p ^ d) = α
  rw [garlingFrobeniusPowHom_apply]

/-- Helper: if `L` is a finite field with `Fintype.card L = m` and `∀ x : L, x^m = x`,
then `(X^m - X : L[X]) = ∏ a : L, (X - C a)`. -/
private theorem poly_X_pow_card_sub_X_eq_prod (L : Type u) [Field L] [Fintype L]
    {m : ℕ} (hcard : Fintype.card L = m) (hpow : ∀ x : L, x ^ m = x) :
    (Polynomial.X ^ m - Polynomial.X : L[X]) =
      ∏ a : L, (Polynomial.X - Polynomial.C a) := by
  classical
  have hm_gt1 : 1 < m := by
    rw [← hcard]
    exact Fintype.one_lt_card_iff.mpr ⟨0, 1, zero_ne_one⟩
  obtain ⟨hf_mon, hf_deg⟩ := monic_and_natDegree_X_pow_sub_X L hm_gt1
  let gL : L[X] := ∏ a : L, (Polynomial.X - Polynomial.C a)
  have hgL_mon : gL.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hgL_deg : gL.natDegree = m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)]
    simp [hcard]
  have hdvd : gL ∣ (Polynomial.X ^ m - Polynomial.X : L[X]) := by
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun a _ => ?_)
    · exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
    · rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, hpow a, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hf_mon.ne_zero hq
  have hq_deg : q.natDegree = 0 := by
    have hd := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hgL_mon.ne_zero hq0, hf_deg, hgL_deg] at hd
    omega
  have hq_mon : q.Monic := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, hf_mon.leadingCoeff, hgL_mon.leadingCoeff, one_mul] at hlc
    exact hlc.symm
  rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]

/-- Second paragraph of Garling's proof of `Theorem 12.1` (printed pp. 101–102 / PDF pp. 109–110):
if `L` is any field of order `p^n` (`p` prime), then `0 < n`, `ringChar L = p`, every `λ ∈ L`
satisfies `λ^{p^n} = λ`, and `L` is a splitting field for `x^{p^n} - x` over its prime subfield. -/
theorem finite_field_isSplittingField_primeSubfield {L : Type u} [Field L] {p n : ℕ}
    (hp : Nat.Prime p) (hcard : Nat.card L = p ^ n) :
    0 < n ∧
    Finite L ∧
    ringChar L = p ∧
    Module.finrank (primeSubfield L) L = n ∧
    (∀ x : L, x ^ (p ^ n) = x) ∧
    IsGarlingSplittingFieldExtension (primeSubfield L) L
      (Polynomial.X ^ (p ^ n) - Polynomial.X) := by
  have hfinL : Finite L := by
    by_contra hinf
    have h0 : Nat.card L = 0 := @Nat.card_eq_zero_of_infinite L (not_finite_iff_infinite.mp hinf)
    exact pow_ne_zero n hp.ne_zero (hcard.symm.trans h0)
  let _ : Finite L := hfinL
  let _ : Fintype L := Fintype.ofFinite L
  have hfintype_card : Fintype.card L = p ^ n := Nat.card_eq_fintype_card.symm.trans hcard
  have hcard_ge2 : 2 ≤ p ^ n := by
    rw [← hfintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨0, 1, zero_ne_one⟩
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hcard_ge2
    · exact hpos
  obtain ⟨_, hq_prime, _, _, hm_pos, _, _, hcard_qm, _⟩ := finite_field_char_and_prime_power L
  obtain ⟨hq_eq_p, hm_eq_n⟩ :=
    eq_and_exp_eq_of_prime_pow_eq hq_prime hp hm_pos (hcard_qm.symm.trans hcard)
  -- Lagrange on `Lˣ`: `|Lˣ| = p^n - 1`, so `u^{p^n - 1} = 1` for all `u ∈ Lˣ`, hence `x^{p^n} = x`.
  have hpow_self : ∀ x : L, x ^ (p ^ n) = x := by
    intro x
    classical
    by_cases hx : x = 0
    · rw [hx, zero_pow (pow_ne_zero n hp.ne_zero)]
    · let u : Lˣ := Units.mk0 x hx
      have hcard_units : Fintype.card Lˣ = p ^ n - 1 := by
        rw [Fintype.card_units, hfintype_card]
      have hu_pow : u ^ (p ^ n - 1) = 1 := by
        rw [← hcard_units]
        exact pow_card_eq_one
      have hx_pow1 : x ^ (p ^ n - 1) = 1 := by
        simpa [u] using congrArg Units.val hu_pow
      have hpn_pos : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
      calc x ^ (p ^ n) = x ^ (p ^ n - 1) * x := by
            rw [← pow_succ, Nat.sub_add_cancel hpn_pos]
        _ = 1 * x := by rw [hx_pow1]
        _ = x := one_mul x
  -- Show `L` is a splitting field for `X^{p^n} - X` over `primeSubfield L`.
  let fP : (primeSubfield L)[X] := Polynomial.X ^ (p ^ n) - Polynomial.X
  have hfP_map : fP.map (algebraMap (primeSubfield L) L) = Polynomial.X ^ (p ^ n) - Polynomial.X := by
    simp [fP]
  have hfP_ne0 : fP ≠ 0 :=
    (monic_and_natDegree_X_pow_sub_X (primeSubfield L) (by omega : 1 < p ^ n)).1.ne_zero
  have hsf : IsGarlingSplittingFieldExtension (primeSubfield L) L fP := by
    classical
    rw [isGarlingSplittingFieldExtension_iff]
    refine ⟨?_, ?_⟩
    · rw [hfP_map, poly_X_pow_card_sub_X_eq_prod L hfintype_card hpow_self]
      exact Polynomial.Splits.prod fun a _ => Polynomial.Splits.X_sub_C a
    · rw [eq_top_iff]
      intro x _
      apply Algebra.subset_adjoin
      rw [Polynomial.mem_rootSet_of_ne hfP_ne0, Polynomial.aeval_def, ← Polynomial.eval_map,
        hfP_map, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hpow_self x, sub_self]
  exact ⟨hn_pos, hfinL, hq_eq_p, hm_eq_n, hpow_self, hsf⟩

/-- **Theorem 12.1** (§12.1, printed p. 101 / PDF p. 109; proof pp. 101–102):
*"For each prime number `p` and each positive integer `n` there is a field `K` with `|K| = p^n`.
The field `K` is a splitting field for `f = x^{p^n} - x` over its prime subfield. If `K` and `K'`
are two fields of order `p^n` then `K` and `K'` are isomorphic."* -/
theorem theorem_12_1 {p n : ℕ} (hp : Nat.Prime p) (hn : 0 < n) :
    (∃ (K : Type) (_ : Field K),
      setOrder K = (p ^ n : ℕ) ∧
      Nat.card K = p ^ n ∧
      IsGarlingSplittingFieldExtension (primeSubfield K) K
        (Polynomial.X ^ (p ^ n) - Polynomial.X)) ∧
    (∀ (K₁ : Type u) (K₂ : Type v) [Field K₁] [Field K₂],
      setOrder K₁ = (p ^ n : ℕ) → setOrder K₂ = (p ^ n : ℕ) →
      Nonempty (K₁ ≃+* K₂)) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  let f₀ : (ZMod p)[X] := Polynomial.X ^ (p ^ n) - Polynomial.X
  obtain ⟨K, instFieldK, instAlgK, hsfK, _⟩ := theorem_7_3_natDegree f₀
  let _ : Field K := instFieldK
  let _ : Algebra (ZMod p) K := instAlgK
  have hcharK : ringChar K = p :=
    ringChar_eq_of_prime_natCast_eq_zero hp
      (by rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_self, map_zero])
  have hpn_gt1 : 1 < p ^ n := one_lt_pow₀ hp.one_lt hn.ne'
  obtain ⟨hf₀_mon, hf₀_deg⟩ := monic_and_natDegree_X_pow_sub_X (ZMod p) hpn_gt1
  have hf₀_ne0 : f₀ ≠ 0 := hf₀_mon.ne_zero
  -- `D(f₀) = -1` in `(ZMod p)[X]`, so `f₀` is separable with `p^n` distinct roots in `K`.
  have hderiv_f₀ : garlingDeriv f₀ = -1 := by
    rw [garlingDeriv_eq_derivative]
    dsimp [f₀]
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    have hcast0 : ((p ^ n : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (p ^ n) p).mpr (dvd_pow_self p hn.ne')
    simp [hcast0]
  let R : Subfield K := frobeniusIterFixedSubfield K hcharK hp.ne_zero n
  have hmemR_iff : ∀ α : K, α ∈ R ↔ Polynomial.aeval α f₀ = 0 := by
    intro α
    rw [mem_frobeniusIterFixedSubfield_iff]
    change α ^ (p ^ n) = α ↔ Polynomial.aeval α (Polynomial.X ^ (p ^ n) - Polynomial.X) = 0
    simp [sub_eq_zero]
  have hncard_R : (R : Set K).ncard = p ^ n := by
    have hsp : (f₀.map (algebraMap (ZMod p) K)).Splits :=
      ((isGarlingSplittingFieldExtension_iff (ZMod p) K f₀).mp hsfK).1
    have hsep : f₀.Separable := by
      rw [Polynomial.Separable, ← garlingDeriv_eq_derivative, hderiv_f₀]
      exact ⟨0, -1, by ring⟩
    have hcard_roots : Fintype.card (f₀.rootSet K) = p ^ n :=
      (Polynomial.card_rootSet_eq_natDegree hsep hsp).trans hf₀_deg
    have hset_eq : (R : Set K) = f₀.rootSet K := by
      ext α
      rw [SetLike.mem_coe, hmemR_iff, Polynomial.mem_rootSet_of_ne hf₀_ne0]
    rw [hset_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard_roots]
  -- `R` is an intermediate field over `ZMod p` over which `f₀` splits, so `R = ⊤`, giving `|K| = p^n`.
  let R_int : IntermediateField (ZMod p) K :=
    { R with
      algebraMap_mem' := fun c => by
        change algebraMap (ZMod p) K c ∈ R
        rw [mem_frobeniusIterFixedSubfield_iff, ← map_pow]
        congr 1
        have h1 : ∀ k : ℕ, c ^ (p ^ k) = c := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, pow_mul, ZMod.pow_card, ih]
        exact h1 n }
  have hf₀_splits_R : GarlingSplitsOver (ZMod p) R_int f₀ := by
    rw [garlingSplitsOver_iff_splits]
    obtain ⟨n', lam, α', hexp⟩ := hsfK.1
    have hroot_mem : ∀ i : Fin n', α' i ∈ R_int := by
      intro i
      change α' i ∈ R
      rw [hmemR_iff, Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
        Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp), mul_zero]
    let β' : Fin n' → R_int := fun i => ⟨α' i, hroot_mem i⟩
    have hexpR :
        f₀.map (algebraMap (ZMod p) R_int) =
          Polynomial.C (algebraMap (ZMod p) R_int lam) *
            ∏ i : Fin n', (Polynomial.X - Polynomial.C (β' i)) := by
      apply Polynomial.map_injective R_int.val.toRingHom R_int.val.injective
      rw [Polynomial.map_map]
      have halg : R_int.val.toRingHom.comp (algebraMap (ZMod p) R_int) = algebraMap (ZMod p) K := rfl
      rw [halg, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [β']
    rw [hexpR]
    exact Polynomial.Splits.mul (Polynomial.Splits.C _)
      (Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _)
  have hR_top : R_int = ⊤ := by
    by_contra hne
    exact hsfK.2 R_int hne hf₀_splits_R
  have hcardK : Nat.card K = p ^ n := by
    have htop_set : (R : Set K) = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      change x ∈ R_int
      rw [hR_top]
      exact IntermediateField.mem_top
    rw [← Set.ncard_univ, ← htop_set, hncard_R]
  obtain ⟨_, hfinK, _, _, _, hsfPrimeK⟩ := finite_field_isSplittingField_primeSubfield hp hcardK
  have hsetK : setOrder K = (p ^ n : ℕ) := setOrder_eq_natCast_iff.mpr ⟨hfinK, hcardK⟩
  refine ⟨⟨K, instFieldK, hsetK, hcardK, hsfPrimeK⟩, ?_⟩
  -- Uniqueness up to ring isomorphism across arbitrary universes `u, v`:
  intro K₁ K₂ _ _ hset₁ hset₂
  obtain ⟨_, hcard₁⟩ := setOrder_eq_natCast_iff.mp hset₁
  obtain ⟨_, hcard₂⟩ := setOrder_eq_natCast_iff.mp hset₂
  obtain ⟨_, _, hchar₁, _, _, hsf₁⟩ := finite_field_isSplittingField_primeSubfield hp hcard₁
  obtain ⟨_, _, hchar₂, _, _, hsf₂⟩ := finite_field_isSplittingField_primeSubfield hp hcard₂
  obtain ⟨_, ⟨e₁⟩⟩ := (theorem_3_17 K₁).2 (hchar₁.symm ▸ hp.ne_zero)
  obtain ⟨_, ⟨e₂⟩⟩ := (theorem_3_17 K₂).2 (hchar₂.symm ▸ hp.ne_zero)
  let eZ : ZMod (ringChar K₁) ≃+* ZMod (ringChar K₂) :=
    hchar₁.symm ▸ hchar₂.symm ▸ RingEquiv.refl (ZMod p)
  let i₀ : primeSubfield K₁ ≃+* primeSubfield K₂ := (e₁.trans eZ).trans e₂.symm
  have hmap_poly :
      garlingMapPoly i₀.toRingHom (Polynomial.X ^ (p ^ n) - Polynomial.X) =
        (Polynomial.X ^ (p ^ n) - Polynomial.X : (primeSubfield K₂)[X]) := by
    simp [garlingMapPoly]
  have hsf₂' : IsGarlingSplittingFieldExtension (primeSubfield K₂) K₂
      (garlingMapPoly i₀.toRingHom (Polynomial.X ^ (p ^ n) - Polynomial.X)) := by
    rwa [hmap_poly]
  obtain ⟨j, _⟩ := corollary_1_to_theorem_7_5_equiv i₀ _ hsf₁ hsf₂'
  exact ⟨j⟩

/-- `Nat.card` companion to **Theorem 12.1** (§12.1, p. 101): any two fields of cardinality `p^n`
(`p` prime, `0 < n`) are isomorphic. -/
theorem theorem_12_1_natCard {p n : ℕ} (hp : Nat.Prime p) (hn : 0 < n)
    (K₁ : Type u) (K₂ : Type v) [Field K₁] [Field K₂]
    (h₁ : Nat.card K₁ = p ^ n) (h₂ : Nat.card K₂ = p ^ n) :
    Nonempty (K₁ ≃+* K₂) := by
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have hfin₁ : Finite K₁ := Nat.finite_of_card_ne_zero (by omega)
  have hfin₂ : Finite K₂ := Nat.finite_of_card_ne_zero (by omega)
  exact (theorem_12_1 hp hn).2 K₁ K₂
    (setOrder_eq_natCast_iff.mpr ⟨hfin₁, h₁⟩)
    (setOrder_eq_natCast_iff.mpr ⟨hfin₂, h₂⟩)

/-- **Corollary 1** [to Theorem 12.1] (§12.1, printed p. 102 / PDF p. 110):
*"If `K` is a finite field, with prime subfield `ℤ_p`, then `K : ℤ_p` is a Galois extension."*

Proved directly from `Theorem 12.1` (`finite_field_isSplittingField_primeSubfield`), `Corollary 1`
to `Theorem 9.1` (`corollary_1_to_theorem_9_1`), and the `Corollary` to `Theorem 10.8`
(`corollary_to_theorem_10_8`), matching Garling's 2-line justification on p. 102. -/
theorem corollary_1_to_theorem_12_1 (K : Type u) [Field K] [Finite K] :
    IsGarlingGaloisExtension (primeSubfield K) K := by
  obtain ⟨_, hp_prime, _, hfin, _, _, _, hcard, _⟩ := finite_field_char_and_prime_power K
  obtain ⟨_, _, _, _, _, hsf⟩ := finite_field_isSplittingField_primeSubfield hp_prime hcard
  have hnorm : IsGarlingNormal (primeSubfield K) K :=
    (corollary_1_to_theorem_9_1 hfin).mpr ⟨_, hsf⟩
  have halg : IsAlgebraicExtension (primeSubfield K) K :=
    (isAlgebraicExtension_iff (primeSubfield K) K).mpr inferInstance
  have _ : Finite (primeSubfield K) :=
    Finite.of_injective (primeSubfield K).subtype Subtype.val_injective
  obtain ⟨hpP_pos, _, _, _, _, _, _, _, _⟩ :=
    finite_field_char_and_prime_power (primeSubfield K)
  have halgP : IsAlgebraicExtension (primeSubfield (primeSubfield K)) (primeSubfield K) :=
    (isAlgebraicExtension_iff _ _).mpr inferInstance
  have hsep : IsGarlingSeparableExtension (primeSubfield K) K :=
    fun α => ⟨halg α, corollary_to_theorem_10_8 rfl hpP_pos halgP (minpoly (primeSubfield K) α)⟩
  exact ⟨hfin, hnorm, hsep⟩

/-- **Corollary 2** [to Theorem 12.1] (§12.1, printed p. 102 / PDF p. 110):
*"If `L : K` is an extension and `L` is finite, then `L : K` is a Galois extension."*

Proved directly from `Corollary 1` (`corollary_1_to_theorem_12_1`), `Corollary 3` to `Theorem 9.1`
(`corollary_3_to_theorem_9_1_tower`), and `Theorem 10.1` (`theorem_10_1_tower`), exactly as stated
on lines 4–5 of printed p. 102. -/
theorem corollary_2_to_theorem_12_1 (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Finite L] :
    IsGarlingGaloisExtension K L := by
  have hfinKL : IsFiniteExtension K L :=
    (isFiniteExtension_iff_moduleFinite K L).mpr inferInstance
  have hgalPL : IsGarlingGaloisExtension (primeSubfield L) L := corollary_1_to_theorem_12_1 L
  have hP_le_K : primeSubfield L ≤ (algebraMap K L).fieldRange := by
    rw [primeSubfield_eq_bot]; exact bot_le
  let iPK : primeSubfield L →+* K :=
    { toFun := fun x => Classical.choose (hP_le_K x.2)
      map_one' := (algebraMap K L).injective
        ((Classical.choose_spec (hP_le_K (primeSubfield L).one_mem)).trans (map_one _).symm)
      map_mul' := fun x y => (algebraMap K L).injective (by
        rw [map_mul, Classical.choose_spec (hP_le_K x.2), Classical.choose_spec (hP_le_K y.2),
          ← Classical.choose_spec (hP_le_K ((primeSubfield L).mul_mem x.2 y.2))])
      map_zero' := (algebraMap K L).injective
        ((Classical.choose_spec (hP_le_K (primeSubfield L).zero_mem)).trans (map_zero _).symm)
      map_add' := fun x y => (algebraMap K L).injective (by
        rw [map_add, Classical.choose_spec (hP_le_K x.2), Classical.choose_spec (hP_le_K y.2),
          ← Classical.choose_spec (hP_le_K ((primeSubfield L).add_mem x.2 y.2))]) }
  let _ : Algebra (primeSubfield L) K := iPK.toAlgebra
  have _ : IsScalarTower (primeSubfield L) K L :=
    IsScalarTower.of_algebraMap_eq fun x => (Classical.choose_spec (hP_le_K x.2)).symm
  have hnormKL : IsGarlingNormal K L :=
    corollary_3_to_theorem_9_1_tower (K := primeSubfield L) (M := K) (L := L) hgalPL.2.1
  have hsepKL : IsGarlingSeparableExtension K L :=
    (theorem_10_1_tower (K := primeSubfield L) (M := K) (L := L) hgalPL.2.2).1
  exact ⟨hfinKL, hnormKL, hsepKL⟩

/-- `ZMod p`-algebra companion to **Corollary 1** [to Theorem 12.1] (§12.1, p. 102). -/
theorem corollary_1_to_theorem_12_1_zmod {p : ℕ} [Fact p.Prime]
    (K : Type u) [Field K] [Finite K] [Algebra (ZMod p) K] :
    IsGarlingGaloisExtension (ZMod p) K :=
  corollary_2_to_theorem_12_1 (ZMod p) K

/-- Subfield companion to **Corollary 2** [to Theorem 12.1] (§12.1, p. 102). -/
theorem corollary_2_to_theorem_12_1_subfield {L : Type u} [Field L] [Finite L] (K : Subfield L) :
    IsGarlingGaloisExtension K L :=
  corollary_2_to_theorem_12_1 K L

/-- Extension-triple companion to **Corollary 2** [to Theorem 12.1] (§12.1, p. 102). -/
theorem corollary_2_to_theorem_12_1_triple {K : Type u} {L : Type v} [Field K] [Field L]
    [Finite L] (ext : FieldExtensionTriple K L) :
    IsGarlingGaloisExtensionTriple ext := by
  let _ : Algebra K L := ext.hom.toAlgebra
  exact corollary_2_to_theorem_12_1 K L

/-! ### §12.1 Exercises 12.1–12.3 (printed p. 102, PDF p. 110) -/

/-- Helper: for any finite field `K` of order `q` (`Nat.card K = q`) and positive integer `n`,
there exists a splitting field extension `L : K` of `X^{q^n} - X ∈ K[X]` in the same universe as `K`
with `Nat.card L = q^n`, `Module.finrank K L = n`, and `extDegree K L = n`. -/
theorem exists_extension_card_pow_of_finite_field (K : Type u) [Field K] [Finite K]
    {q n : ℕ} (hq : Nat.card K = q) (hn : 0 < n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Finite L ∧
      IsFiniteExtension K L ∧
      Nat.card L = q ^ n ∧
      Module.finrank K L = n ∧
      extDegree K L = n ∧
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ (q ^ n) - Polynomial.X) := by
  obtain ⟨_, hp_prime, _, _, hm_pos, _, _, hcard_pm, _⟩ := finite_field_char_and_prime_power K
  let p := ringChar K
  let m := Module.finrank (primeSubfield K) K
  have hq_eq : q = p ^ m := hq.symm.trans hcard_pm
  have hqn_eq : q ^ n = p ^ (m * n) := by rw [hq_eq, pow_mul]
  have hmn_pos : 0 < m * n := Nat.mul_pos hm_pos hn
  let f : K[X] := Polynomial.X ^ (q ^ n) - Polynomial.X
  obtain ⟨L, instFL, instAKL, hsfL, _⟩ := theorem_7_3_natDegree f
  let _ : Field L := instFL
  let _ : Algebra K L := instAKL
  have hcharL : ringChar L = p :=
    ringChar_eq_of_prime_natCast_eq_zero hp_prime
      (by rw [← map_natCast (algebraMap K L), ringChar.Nat.cast_ringChar, map_zero])
  have hqn_gt1 : 1 < q ^ n := by
    rw [hqn_eq]
    exact one_lt_pow₀ hp_prime.one_lt hmn_pos.ne'
  obtain ⟨hf_mon, hf_deg⟩ := monic_and_natDegree_X_pow_sub_X K hqn_gt1
  have hf_ne0 : f ≠ 0 := hf_mon.ne_zero
  have hderiv_f : garlingDeriv f = -1 := by
    rw [garlingDeriv_eq_derivative]
    dsimp [f]
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    have hp_dvd : p ∣ q ^ n := by rw [hqn_eq]; exact dvd_pow_self p hmn_pos.ne'
    have hcast0 : ((q ^ n : ℕ) : K) = 0 := (ringChar.spec K (q ^ n)).mpr hp_dvd
    simp [hcast0]
  let R : Subfield L := frobeniusIterFixedSubfield L hcharL hp_prime.ne_zero (m * n)
  have hmemR_iff : ∀ α : L, α ∈ R ↔ Polynomial.aeval α f = 0 := by
    intro α
    rw [mem_frobeniusIterFixedSubfield_iff, ← hqn_eq]
    change α ^ (q ^ n) = α ↔ Polynomial.aeval α (Polynomial.X ^ (q ^ n) - Polynomial.X) = 0
    simp [sub_eq_zero]
  have hncard_R : (R : Set L).ncard = q ^ n := by
    have hsp : (f.map (algebraMap K L)).Splits :=
      ((isGarlingSplittingFieldExtension_iff K L f).mp hsfL).1
    have hsep : f.Separable := by
      rw [Polynomial.Separable, ← garlingDeriv_eq_derivative, hderiv_f]
      exact ⟨0, -1, by ring⟩
    have hcard_roots : Fintype.card (f.rootSet L) = q ^ n :=
      (Polynomial.card_rootSet_eq_natDegree hsep hsp).trans hf_deg
    have hset_eq : (R : Set L) = f.rootSet L := by
      ext α
      rw [SetLike.mem_coe, hmemR_iff, Polynomial.mem_rootSet_of_ne hf_ne0]
    rw [hset_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard_roots]
  -- `K` is fixed by `x ↦ x^q`, hence by `x ↦ x^{q^n}`, so `R` contains `algebraMap K L`.
  obtain ⟨_, _, _, _, hpowK, _⟩ := finite_field_isSplittingField_primeSubfield hp_prime hcard_pm
  have hpowK_qn : ∀ c : K, c ^ (q ^ n) = c := by
    intro c
    have hcq : c ^ q = c := hq_eq ▸ hpowK c
    have hiter : ∀ k : ℕ, c ^ (q ^ k) = c := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, pow_mul, ih, hcq]
    exact hiter n
  let R_int : IntermediateField K L :=
    { R with
      algebraMap_mem' := fun c => by
        change algebraMap K L c ∈ R
        rw [mem_frobeniusIterFixedSubfield_iff, ← hqn_eq, ← map_pow, hpowK_qn c] }
  have hf_splits_R : GarlingSplitsOver K R_int f := by
    rw [garlingSplitsOver_iff_splits]
    obtain ⟨n', lam, α', hexp⟩ := hsfL.1
    have hroot_mem : ∀ i : Fin n', α' i ∈ R_int := by
      intro i
      change α' i ∈ R
      rw [hmemR_iff, Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
        Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp), mul_zero]
    let β' : Fin n' → R_int := fun i => ⟨α' i, hroot_mem i⟩
    have hexpR :
        f.map (algebraMap K R_int) =
          Polynomial.C (algebraMap K R_int lam) *
            ∏ i : Fin n', (Polynomial.X - Polynomial.C (β' i)) := by
      apply Polynomial.map_injective R_int.val.toRingHom R_int.val.injective
      rw [Polynomial.map_map]
      have halg : R_int.val.toRingHom.comp (algebraMap K R_int) = algebraMap K L := rfl
      rw [halg, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [β']
    rw [hexpR]
    exact Polynomial.Splits.mul (Polynomial.Splits.C _)
      (Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _)
  have hR_top : R_int = ⊤ := by
    by_contra hne
    exact hsfL.2 R_int hne hf_splits_R
  have hcardL : Nat.card L = q ^ n := by
    have htop_set : (R : Set L) = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      change x ∈ R_int
      rw [hR_top]
      exact IntermediateField.mem_top
    rw [← Set.ncard_univ, ← htop_set, hncard_R]
  have hfinL : Finite L := Nat.finite_of_card_ne_zero (by rw [hcardL, hqn_eq]; positivity)
  let _ : Finite L := hfinL
  have hfinKL : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsfL).1
  let bKL : Module.Basis (Fin (Module.finrank K L)) K L := Module.finBasis K L
  have hcard_finrank : q ^ Module.finrank K L = q ^ n := by
    calc q ^ Module.finrank K L
        = (Nat.card K) ^ (Nat.card (Fin (Module.finrank K L))) := by rw [hq, Nat.card_fin]
      _ = Nat.card (Fin (Module.finrank K L) → K) := (Nat.card_fun).symm
      _ = Nat.card L := (Nat.card_congr bKL.equivFun.toEquiv).symm
      _ = q ^ n := hcardL
  have hq_ge2 : 2 ≤ q := by
    rw [hq_eq]
    calc 2 ≤ p ^ 1 := by simpa using hp_prime.two_le
      _ ≤ p ^ m := Nat.pow_le_pow_right hp_prime.pos hm_pos
  have hfinrank : Module.finrank K L = n := Nat.pow_right_injective hq_ge2 hcard_finrank
  have hext : extDegree K L = n := (extDegree_eq_finrank K L).trans (congrArg Nat.cast hfinrank)
  exact ⟨L, instFL, instAKL, hfinL, hfinKL, hcardL, hfinrank, hext, hsfL⟩

/-- **Exercise 12.1** (§12.1, printed p. 102 / PDF p. 110):
*"Show that if `K` is a finite field of order `q` and `p` is a prime then there are exactly
`(q^p - q) / p` monic irreducible polynomials of degree `p` over `K`."* -/
theorem exercise_12_1 {K : Type u} [Field K] {q p : ℕ}
    (hq : setOrder K = (q : ℕ)) (hp : Nat.Prime p) :
    let S := {g : K[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p}
    S.Finite ∧
    p ∣ (q ^ p - q) ∧
    S.ncard = (q ^ p - q) / p ∧
    setOrder S = ((q ^ p - q) / p : ℕ) := by
  classical
  intro S
  obtain ⟨hfinK, hcardK⟩ := setOrder_eq_natCast_iff.mp hq
  let _ : Finite K := hfinK
  let _ : Fintype K := Fintype.ofFinite K
  have hq_ge2 : 2 ≤ q := by
    rw [← hcardK, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨0, 1, zero_ne_one⟩
  obtain ⟨L, instFL, instAKL, hfinL, _, hcardL, hdegKL, hextKL, hsfL⟩ :=
    exists_extension_card_pow_of_finite_field K hcardK hp.pos
  let _ : Field L := instFL
  let _ : Algebra K L := instAKL
  let _ : Finite L := hfinL
  let _ : Fintype L := Fintype.ofFinite L
  let T : Set L := Set.univ \ Set.range (algebraMap K L)
  have hrange_ncard : (Set.range (algebraMap K L)).ncard = q := by
    rw [Set.ncard_range_of_injective (algebraMap K L).injective, hcardK]
  have hT_ncard : T.ncard = q ^ p - q := by
    rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, hcardL, hrange_ncard]
  have hmin_mem_S : ∀ α ∈ T, minpoly K α ∈ S := by
    rintro α ⟨_, hα⟩
    have hint : IsIntegral K α := IsIntegral.of_finite K α
    have hm_mon : (minpoly K α).Monic := minpoly.monic hint
    have hm_irr : Irreducible (minpoly K α) := minpoly.irreducible hint
    have hKα_ne_bot : IntermediateField.adjoin K {α} ≠ ⊥ := by
      intro hbot
      have hα_mem : α ∈ (⊥ : IntermediateField K L) :=
        hbot ▸ IntermediateField.mem_adjoin_simple_self K α
      rw [IntermediateField.mem_bot] at hα_mem
      exact hα hα_mem
    have hKα_top : IntermediateField.adjoin K {α} = ⊤ :=
      ((exercise_4_1 hp hextKL).2 (IntermediateField.adjoin K {α})).resolve_left hKα_ne_bot
    have hdeg_α : (minpoly K α).natDegree = p := by
      have h1 := IntermediateField.adjoin.finrank hint
      have h2 : Module.finrank K (IntermediateField.adjoin K {α}) = Module.finrank K L := by
        rw [hKα_top]
        exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
      omega
    exact ⟨hm_mon, hm_irr, hdeg_α⟩
  have hg_roots_in_T : ∀ g ∈ S,
      ({α ∈ T | minpoly K α = g}).ncard = p := by
    rintro g ⟨hg_mon, hg_irr, hg_deg⟩
    have _ : Fact (Irreducible g) := ⟨hg_irr⟩
    let E := AdjoinRoot g
    let pbE : PowerBasis K E := AdjoinRoot.powerBasis hg_mon.ne_zero
    have _ : Module.Finite K E := pbE.finite
    have hdegE : Module.finrank K E = p := pbE.finrank.trans hg_deg
    let bKE := Module.finBasis K E
    have hcardE : Nat.card E = q ^ p := by
      rw [Nat.card_congr bKE.equivFun.toEquiv, Nat.card_fun, hcardK, Nat.card_fin, hdegE]
    have _ : Finite E := Nat.finite_of_card_ne_zero (by rw [hcardE]; positivity)
    obtain ⟨_, hpE_prime, _, _, _, _, _, hcardE_pm, _⟩ :=
      finite_field_char_and_prime_power E
    obtain ⟨_, _, _, _, hpowE, _⟩ := finite_field_isSplittingField_primeSubfield hpE_prime hcardE_pm
    have hpowE_qp : ∀ x : E, x ^ (q ^ p) = x := by
      intro x; rw [← hcardE, hcardE_pm]; exact hpowE x
    let rE : E := AdjoinRoot.root g
    have hrE_min : minpoly K rE = g := (AdjoinRoot.minpoly_root hg_mon.ne_zero).trans (by
      rw [hg_mon.leadingCoeff, inv_one, map_one, mul_one])
    have hg_dvd : g ∣ (Polynomial.X ^ (q ^ p) - Polynomial.X : K[X]) := by
      rw [← hrE_min]
      refine minpoly.dvd K rE ?_
      simp [hpowE_qp rE]
    have hgt_qp : 1 < q ^ p := one_lt_pow₀ (by omega) hp.ne_zero
    have hf_ne0 : (Polynomial.X ^ (q ^ p) - Polynomial.X : K[X]) ≠ 0 :=
      (monic_and_natDegree_X_pow_sub_X K hgt_qp).1.ne_zero
    have hsp_f : ((Polynomial.X ^ (q ^ p) - Polynomial.X : K[X]).map (algebraMap K L)).Splits :=
      ((isGarlingSplittingFieldExtension_iff K L _).mp hsfL).1
    have hg_spL : (g.map (algebraMap K L)).Splits :=
      hsp_f.of_dvd ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf_ne0)
        (Polynomial.map_dvd (algebraMap K L) hg_dvd)
    obtain ⟨hpK_pos, _, _, _, _, _, _, _, _⟩ := finite_field_char_and_prime_power K
    have halgPK : IsAlgebraicExtension (primeSubfield K) K :=
      (isAlgebraicExtension_iff _ _).mpr inferInstance
    have hg_sep : g.Separable :=
      (isGarlingSeparablePoly_of_irreducible_iff hg_irr).mp
        (corollary_to_theorem_10_8 rfl hpK_pos halgPK g)
    have hcard_roots : Fintype.card (g.rootSet L) = p :=
      (Polynomial.card_rootSet_eq_natDegree hg_sep hg_spL).trans hg_deg
    have hfiber_eq : {α ∈ T | minpoly K α = g} = (g.rootSet L : Set L) := by
      ext α
      rw [Set.mem_sep_iff, Polynomial.mem_rootSet_of_ne hg_mon.ne_zero]
      constructor
      · rintro ⟨_, rfl⟩
        exact minpoly.aeval K α
      · intro haev
        have hint : IsIntegral K α := IsIntegral.of_finite K α
        have hmin_eq : minpoly K α = g :=
          eq_of_monic_dvd_irreducible (minpoly.monic hint) hg_mon
            (minpoly.irreducible hint).not_isUnit hg_irr (minpoly.dvd K α haev)
        refine ⟨⟨trivial, ?_⟩, hmin_eq⟩
        rintro ⟨c, rfl⟩
        have hdeg1 : (minpoly K (algebraMap K L c)).natDegree = 1 := by
          rw [minpoly.eq_X_sub_C_of_algebraMap_inj c (algebraMap K L).injective]
          exact Polynomial.natDegree_X_sub_C c
        rw [hmin_eq, hg_deg] at hdeg1
        exact hp.ne_one hdeg1
    rw [hfiber_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard_roots]
  have hS_eq_img : S = (fun α : L => minpoly K α) '' T := by
    ext g
    constructor
    · intro hg
      have hpos : 0 < ({α ∈ T | minpoly K α = g}).ncard := by
        rw [hg_roots_in_T g hg]; exact hp.pos
      obtain ⟨α, hαT, hmin⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
      exact ⟨α, hαT, hmin⟩
    · rintro ⟨α, hαT, rfl⟩
      exact hmin_mem_S α hαT
  have hS_fin : S.Finite := by
    rw [hS_eq_img]
    exact (Set.toFinite T).image _
  let TS : Finset L := T.toFinset
  let SS : Finset K[X] := hS_fin.toFinset
  have hfib : TS.card = ∑ g ∈ SS, (TS.filter (fun α => minpoly K α = g)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun α hα => ?_
    exact hS_fin.mem_toFinset.mpr (hmin_mem_S α (Set.mem_toFinset.mp hα))
  have hfib_each : ∀ g ∈ SS, (TS.filter (fun α => minpoly K α = g)).card = p := by
    intro g hg
    have hgS : g ∈ S := hS_fin.mem_toFinset.mp hg
    have hcoe : ((TS.filter (fun α => minpoly K α = g) : Finset L) : Set L) =
        {α ∈ T | minpoly K α = g} := by
      ext α; simp [TS]
    rw [← Set.ncard_coe_finset, hcoe, hg_roots_in_T g hgS]
  have hmul_eq : SS.card * p = q ^ p - q := by
    have hsum : ∑ g ∈ SS, (TS.filter (fun α => minpoly K α = g)).card = SS.card * p := by
      rw [Finset.sum_congr rfl hfib_each, Finset.sum_const, smul_eq_mul]
    have hTS_card : TS.card = q ^ p - q := by
      rw [← Set.ncard_coe_finset, Set.coe_toFinset, hT_ncard]
    omega
  have hdvd_qp : p ∣ q ^ p - q := ⟨SS.card, by rw [← hmul_eq, mul_comm]⟩
  have hS_ncard : S.ncard = (q ^ p - q) / p := by
    have h1 : S.ncard = SS.card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      exact (Set.Finite.coe_toFinset hS_fin).symm
    rw [h1, ← hmul_eq, Nat.mul_div_cancel _ hp.pos]
  have hS_setOrder : setOrder S = ((q ^ p - q) / p : ℕ) :=
    setOrder_eq_natCast_iff.mpr ⟨hS_fin.to_subtype, (Nat.card_coe_set_eq S).trans hS_ncard⟩
  exact ⟨hS_fin, hdvd_qp, hS_ncard, hS_setOrder⟩

/-- `Nat.card` + `IsGarlingIrreducible` companion to **Exercise 12.1** (§12.1, p. 102). -/
theorem exercise_12_1_garling {K : Type u} [Field K] [Finite K] {q p : ℕ}
    (hq : Nat.card K = q) (hp : Nat.Prime p) :
    {g : K[X] | g.Monic ∧ IsGarlingIrreducible g ∧ g.natDegree = p}.ncard = (q ^ p - q) / p := by
  have heq : {g : K[X] | g.Monic ∧ IsGarlingIrreducible g ∧ g.natDegree = p} =
      {g : K[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p} := by
    ext g
    exact and_congr_right fun _ => and_congr_left fun _ => isGarlingIrreducible_iff g
  rw [heq]
  exact (exercise_12_1 (setOrder_eq_natCast_iff.mpr ⟨inferInstance, hq⟩) hp).2.2.1

/-- Helper: any extension `E : K` of a finite field `K` (`Nat.card K = q`) with `extDegree K E = n`
(`0 < n`) has `Nat.card E = q^n` and is a splitting field of `X^{q^n} - X ∈ K[X]` over `K`. -/
private theorem isSplittingField_of_extDegree_eq {K : Type u} {E : Type v}
    [Field K] [Finite K] [Field E] [Algebra K E] {n : ℕ} (hn : 0 < n)
    (hextE : extDegree K E = n) :
    IsGarlingSplittingFieldExtension K E
      (Polynomial.X ^ ((Nat.card K) ^ n) - Polynomial.X) := by
  let q := Nat.card K
  let f : K[X] := Polynomial.X ^ (q ^ n) - Polynomial.X
  have hfinKE : IsFiniteExtension K E := by
    rw [IsFiniteExtension, hextE]
    exact ENat.natCast_lt_top n
  have _ : Module.Finite K E := (isFiniteExtension_iff_moduleFinite K E).mp hfinKE
  have hdegE : Module.finrank K E = n :=
    Nat.cast_injective ((extDegree_eq_finrank K E).symm.trans hextE)
  let bKE := Module.finBasis K E
  have hcardE : Nat.card E = q ^ n := by
    rw [Nat.card_congr bKE.equivFun.toEquiv, Nat.card_fun, Nat.card_fin, hdegE]
  obtain ⟨_, hp_prime, _, _, hm_pos, _, _, hcard_pm, _⟩ := finite_field_char_and_prime_power K
  have hq_pm : q = (ringChar K) ^ (Module.finrank (primeSubfield K) K) := hcard_pm
  have hcardE_pm : Nat.card E = (ringChar K) ^ (Module.finrank (primeSubfield K) K * n) := by
    rw [hcardE, hq_pm, ← pow_mul]
  obtain ⟨_, hfinE, _, _, hpowE, _⟩ :=
    finite_field_isSplittingField_primeSubfield hp_prime hcardE_pm
  let _ : Finite E := hfinE
  let _ : Fintype E := Fintype.ofFinite E
  have hpowE_qn : ∀ x : E, x ^ (q ^ n) = x := by
    intro x; rw [hq_pm, ← pow_mul]; exact hpowE x
  have hqn_gt1 : 1 < q ^ n := by
    rw [hq_pm, ← pow_mul]
    exact one_lt_pow₀ hp_prime.one_lt (Nat.mul_pos hm_pos hn).ne'
  obtain ⟨hf_mon, _⟩ := monic_and_natDegree_X_pow_sub_X K hqn_gt1
  have hfintypeE : Fintype.card E = q ^ n := Nat.card_eq_fintype_card.symm.trans hcardE
  have hfE_prod : f.map (algebraMap K E) = ∏ a : E, (Polynomial.X - Polynomial.C a) := by
    have hmap : f.map (algebraMap K E) = Polynomial.X ^ (q ^ n) - Polynomial.X := by simp [f]
    rw [hmap]
    exact poly_X_pow_card_sub_X_eq_prod E hfintypeE hpowE_qn
  rw [isGarlingSplittingFieldExtension_iff]
  refine ⟨?_, ?_⟩
  · rw [hfE_prod]
    exact Polynomial.Splits.prod fun a _ => Polynomial.Splits.X_sub_C a
  · rw [eq_top_iff]
    intro x _
    apply Algebra.subset_adjoin
    rw [Polynomial.mem_rootSet_of_ne hf_mon.ne_zero]
    simp [hpowE_qn x]

/-- **Exercise 12.2** (§12.1, printed p. 102 / PDF p. 110):
*"Show that if `K` is a finite field and `n` is a positive integer then there exists an
(essentially unique) extension `L : K` with `[L : K] = n`."* -/
theorem exercise_12_2 (K : Type u) [Field K] [Finite K] {n : ℕ} (hn : 0 < n) :
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Finite L ∧ IsFiniteExtension K L ∧ extDegree K L = n ∧ Module.finrank K L = n) ∧
    (∀ (L₁ : Type v) (L₂ : Type w) [Field L₁] [Algebra K L₁] [Field L₂] [Algebra K L₂],
      extDegree K L₁ = n → extDegree K L₂ = n →
      Nonempty (L₁ ≃ₐ[K] L₂)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨L, instFL, instAKL, hfinL, hfinKL, _, hdeg, hext, _⟩ :=
      exists_extension_card_pow_of_finite_field K rfl hn
    exact ⟨L, instFL, instAKL, hfinL, hfinKL, hext, hdeg⟩
  · intro L₁ L₂ _ _ _ _ hext₁ hext₂
    exact splitting_field_unique_up_to_algEquiv
      (isSplittingField_of_extDegree_eq hn hext₁)
      (isSplittingField_of_extDegree_eq hn hext₂)

/-- Extension-triple companion to **Exercise 12.2** (§12.1, p. 102). -/
theorem exercise_12_2_triple {K : Type u} [Field K] [Finite K] {n : ℕ} (hn : 0 < n)
    {L₁ : Type v} {L₂ : Type w} [Field L₁] [Field L₂]
    (e₁ : FieldExtensionTriple K L₁) (e₂ : FieldExtensionTriple K L₂)
    (h₁ : letI : Algebra K L₁ := e₁.hom.toAlgebra; extDegree K L₁ = n)
    (h₂ : letI : Algebra K L₂ := e₂.hom.toAlgebra; extDegree K L₂ = n) :
    ∃ j : L₁ ≃+* L₂, j.toRingHom.comp e₁.hom = e₂.hom := by
  let _ : Algebra K L₁ := e₁.hom.toAlgebra
  let _ : Algebra K L₂ := e₂.hom.toAlgebra
  obtain ⟨eAlg⟩ := (exercise_12_2 K hn).2 L₁ L₂ h₁ h₂
  exact ⟨eAlg.toRingEquiv, RingHom.ext fun k => eAlg.commutes k⟩

/-- Polynomial divisibility helper for **Exercise 12.3** (§12.1, p. 102): over any commutative ring
`R`, if `d ∣ n` and `1 ≤ p`, then `(X^{p^d} - X) ∣ (X^{p^n} - X)` in `R[X]`. -/
theorem poly_X_pow_sub_X_dvd {R : Type*} [CommRing R] {p d n : ℕ}
    (hp : 1 ≤ p) (hdn : d ∣ n) :
    (Polynomial.X ^ (p ^ d) - Polynomial.X : R[X]) ∣
      (Polynomial.X ^ (p ^ n) - Polynomial.X : R[X]) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · rcases hdn with ⟨k, hk⟩
    simp at hk
    subst hk
    exact dvd_refl _
  · rcases eq_or_lt_of_le hp with rfl | hp_gt1
    · simp
    · obtain ⟨k, rfl⟩ := hdn
      have hpd_gt1 : 1 < p ^ d := one_lt_pow₀ hp_gt1 hd_pos.ne'
      have hexp_dvd : (p ^ d - 1) ∣ (p ^ (d * k) - 1) := by
        rw [pow_mul]
        have geom_nat : ∀ (a t : ℕ), 1 ≤ a → (a - 1) ∣ (a ^ t - 1) := by
          intro a t ha1
          induction t with
          | zero => simp
          | succ t iht =>
            obtain ⟨q, hq⟩ := iht
            have hat_pos : 1 ≤ a ^ t := Nat.one_le_pow t a ha1
            refine ⟨a * q + 1, ?_⟩
            zify [ha1, hat_pos, Nat.one_le_pow (t + 1) a ha1] at hq ⊢
            calc (a : ℤ) ^ (t + 1) - 1
                = (a : ℤ) * ((a : ℤ) ^ t - 1) + ((a : ℤ) - 1) := by ring
              _ = (a : ℤ) * (((a : ℤ) - 1) * q) + ((a : ℤ) - 1) := by rw [hq]
              _ = ((a : ℤ) - 1) * ((a : ℤ) * q + 1) := by ring
        exact geom_nat (p ^ d) k (le_of_lt hpd_gt1)
      obtain ⟨m, hm⟩ := hexp_dvd
      have hpos_dk : 1 ≤ p ^ (d * k) := Nat.one_le_pow _ _ hp
      have h1 : (Polynomial.X ^ (p ^ (d * k)) - Polynomial.X : R[X]) =
          Polynomial.X * ((Polynomial.X ^ (p ^ d - 1)) ^ m - 1) := by
        rw [← pow_mul, ← hm, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpos_dk]
      have h2 : (Polynomial.X ^ (p ^ d) - Polynomial.X : R[X]) =
          Polynomial.X * (Polynomial.X ^ (p ^ d - 1) - 1) := by
        rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (le_of_lt hpd_gt1)]
      rw [h1, h2]
      refine mul_dvd_mul_left Polynomial.X ?_
      have geom_poly : ∀ (A : R[X]) (t : ℕ), (A - 1) ∣ (A ^ t - 1) := by
        intro A t
        induction t with
        | zero => simp
        | succ t iht =>
          obtain ⟨q, hq⟩ := iht
          refine ⟨A * q + 1, ?_⟩
          calc A ^ (t + 1) - 1 = A * (A ^ t - 1) + (A - 1) := by ring
            _ = A * ((A - 1) * q) + (A - 1) := by rw [hq]
            _ = (A - 1) * (A * q + 1) := by ring
      exact geom_poly _ m

/-- Counterexample for **Exercise 12.3** without `Nat.Prime p` (`QUEUE.md` fidelity hold):
taking `p = 4` (composite), `n = 1`, `L = 𝔽₄ = AdjoinRoot (X^2 + X + 1 : (ZMod 2)[X])`, and
`K = 𝔽₂ = ZMod 2`, `L : K` is an extension and `L` has `4^1 = 4` elements, yet `|K| = 2` is not of
the form `4^d` for any `d : ℕ` (in particular, not for any `d ∣ 1`). -/
theorem exercise_12_3_nonprime_counterexample :
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L),
      Nat.card L = 4 ^ 1 ∧
      setOrder L = (4 ^ 1 : ℕ) ∧
      ¬ ∃ d : ℕ, d ∣ 1 ∧ Nat.card K = 4 ^ d := by
  let g : (ZMod 2)[X] := zmod2IrredQuad
  have hg_irr : Irreducible g := zmod2IrredQuad_irreducible
  have _ : Fact (Irreducible g) := ⟨hg_irr⟩
  let L := AdjoinRoot g
  have hg_deg : g.natDegree = 2 := by dsimp [g, zmod2IrredQuad]; compute_degree!
  have hg_ne0 : g ≠ 0 := hg_irr.ne_zero
  let pb : PowerBasis (ZMod 2) L := AdjoinRoot.powerBasis hg_ne0
  have _ : Module.Finite (ZMod 2) L := pb.finite
  have hdegL : Module.finrank (ZMod 2) L = 2 := pb.finrank.trans hg_deg
  let b := Module.finBasis (ZMod 2) L
  have hcardL : Nat.card L = 4 := by
    rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hdegL]
    norm_num
  have hfinL : Finite L := Nat.finite_of_card_ne_zero (by rw [hcardL]; decide)
  have hsetL : setOrder L = (4 ^ 1 : ℕ) := setOrder_eq_natCast_iff.mpr ⟨hfinL, hcardL⟩
  refine ⟨ZMod 2, L, inferInstance, inferInstance, inferInstance, hcardL, hsetL, ?_⟩
  rintro ⟨d, hd1, hcard2⟩
  rw [Nat.card_zmod] at hcard2
  have hd_le1 : d ≤ 1 := Nat.le_of_dvd Nat.one_pos hd1
  interval_cases d <;> omega

/-- **Exercise 12.3** (§12.1, printed p. 102 / PDF p. 110; see `QUEUE.md` on implicit `Nat.Prime p`):
*"Suppose that `L : K` is an extension and that `L` has `p^n` elements. Show that `|K| = p^d`, where
`d ∣ n`. Conversely, if `d ∣ n`, show that `(x^{p^d} - x) ∣ (x^{p^n} - x)` and deduce that `L` has
exactly one subfield with `p^d` elements."* -/
theorem exercise_12_3 {L : Type u} [Field L] {p n : ℕ}
    (hp : Nat.Prime p) (hL : Nat.card L = p ^ n) :
    (∀ (K : Type v) [Field K] [Algebra K L],
      ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ Nat.card K = p ^ d ∧ setOrder K = (p ^ d : ℕ)) ∧
    (∀ {d : ℕ}, d ∣ n →
      (Polynomial.X ^ (p ^ d) - Polynomial.X : (ZMod p)[X]) ∣
        (Polynomial.X ^ (p ^ n) - Polynomial.X : (ZMod p)[X]) ∧
      (Polynomial.X ^ (p ^ d) - Polynomial.X : L[X]) ∣
        (Polynomial.X ^ (p ^ n) - Polynomial.X : L[X]) ∧
      (∃! F : Subfield L, Nat.card F = p ^ d) ∧
      (∃! F : Subfield L, setOrder F = (p ^ d : ℕ))) := by
  obtain ⟨hn_pos, hfinL, hcharL, _, hpowL, _⟩ :=
    finite_field_isSplittingField_primeSubfield hp hL
  let _ : Finite L := hfinL
  let _ : Fintype L := Fintype.ofFinite L
  refine ⟨?_, ?_⟩
  · intro K _ _
    have _ : Finite K := Finite.of_injective (algebraMap K L) (algebraMap K L).injective
    have hcharK : ringChar K = p :=
      ringChar_eq_of_prime_natCast_eq_zero hp ((algebraMap K L).injective (by
        rw [map_natCast, map_zero]
        exact (ringChar.spec L p).mpr (hcharL ▸ dvd_refl _)))
    obtain ⟨_, _, _, _, hd_pos, _, _, hcardK, hsetK⟩ := finite_field_char_and_prime_power K
    let d := Module.finrank (primeSubfield K) K
    have hcardK_pd : Nat.card K = p ^ d := hcharK ▸ hcardK
    have hsetK_pd : setOrder K = (p ^ d : ℕ) := hcharK ▸ hsetK
    let bKL := Module.finBasis K L
    have hcardL_eq : p ^ (d * Module.finrank K L) = p ^ n := by
      calc p ^ (d * Module.finrank K L)
          = (p ^ d) ^ Module.finrank K L := pow_mul p d _
        _ = (Nat.card K) ^ (Nat.card (Fin (Module.finrank K L))) := by rw [hcardK_pd, Nat.card_fin]
        _ = Nat.card (Fin (Module.finrank K L) → K) := (Nat.card_fun).symm
        _ = Nat.card L := (Nat.card_congr bKL.equivFun.toEquiv).symm
        _ = p ^ n := hL
    have hdn : d ∣ n := ⟨Module.finrank K L, (Nat.pow_right_injective hp.two_le hcardL_eq).symm⟩
    exact ⟨d, hd_pos, hdn, hcardK_pd, hsetK_pd⟩
  · intro d hdn
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn_pos
    have hdvd_Zp :
        (Polynomial.X ^ (p ^ d) - Polynomial.X : (ZMod p)[X]) ∣
          (Polynomial.X ^ (p ^ n) - Polynomial.X : (ZMod p)[X]) :=
      poly_X_pow_sub_X_dvd hp.pos hdn
    have hdvd_L :
        (Polynomial.X ^ (p ^ d) - Polynomial.X : L[X]) ∣
          (Polynomial.X ^ (p ^ n) - Polynomial.X : L[X]) :=
      poly_X_pow_sub_X_dvd hp.pos hdn
    let Fd : Subfield L := frobeniusIterFixedSubfield L hcharL hp.ne_zero d
    have hpd_gt1 : 1 < p ^ d := one_lt_pow₀ hp.one_lt hd_pos.ne'
    let gd : L[X] := Polynomial.X ^ (p ^ d) - Polynomial.X
    let gn : L[X] := Polynomial.X ^ (p ^ n) - Polynomial.X
    obtain ⟨hgd_mon, hgd_deg⟩ := monic_and_natDegree_X_pow_sub_X L hpd_gt1
    have hgd_ne0 : gd ≠ 0 := hgd_mon.ne_zero
    have hpn_gt1 : 1 < p ^ n := one_lt_pow₀ hp.one_lt hn_pos.ne'
    have hgn_ne0 : gn ≠ 0 := (monic_and_natDegree_X_pow_sub_X L hpn_gt1).1.ne_zero
    have hfintypeL : Fintype.card L = p ^ n := Nat.card_eq_fintype_card.symm.trans hL
    have hgn_sp : gn.Splits := by
      have hprod : gn = ∏ a : L, (Polynomial.X - Polynomial.C a) :=
        poly_X_pow_card_sub_X_eq_prod L hfintypeL hpowL
      rw [hprod]
      exact Polynomial.Splits.prod fun a _ => Polynomial.Splits.X_sub_C a
    have hgd_sp : gd.Splits := hgn_sp.of_dvd hgn_ne0 hdvd_L
    have hgd_sep : gd.Separable := by
      have hderiv : Polynomial.derivative gd = -1 := by
        dsimp [gd]
        rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
        have h0 : ((p ^ d : ℕ) : L) = 0 :=
          (ringChar.spec L (p ^ d)).mpr (hcharL ▸ dvd_pow_self p hd_pos.ne')
        simp [h0]
      rw [Polynomial.Separable, hderiv]
      exact ⟨0, -1, by ring⟩
    have hncard_Fd : (Fd : Set L).ncard = p ^ d := by
      have hmap_id : (gd.map (RingHom.id L)).Splits := by simpa using hgd_sp
      have hcard_roots : Fintype.card (gd.rootSet L) = p ^ d :=
        (Polynomial.card_rootSet_eq_natDegree hgd_sep hmap_id).trans hgd_deg
      have hset_eq : (Fd : Set L) = gd.rootSet L := by
        ext α
        rw [SetLike.mem_coe, mem_frobeniusIterFixedSubfield_iff, Polynomial.mem_rootSet_of_ne hgd_ne0]
        simp [gd, sub_eq_zero]
      rw [hset_eq, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard_roots]
    have hcard_Fd : Nat.card Fd = p ^ d := (Nat.card_coe_set_eq (Fd : Set L)).trans hncard_Fd
    have huniq_nat : ∀ F : Subfield L, Nat.card F = p ^ d → F = Fd := by
      intro F hF_card
      obtain ⟨_, _, _, _, hpowF, _⟩ := finite_field_isSplittingField_primeSubfield hp hF_card
      have hle : (F : Set L) ⊆ (Fd : Set L) := by
        intro x hx
        rw [SetLike.mem_coe, mem_frobeniusIterFixedSubfield_iff]
        exact congrArg Subtype.val (hpowF ⟨x, hx⟩)
      have hncard_F : (F : Set L).ncard = p ^ d :=
        (Nat.card_coe_set_eq (F : Set L)).symm.trans hF_card
      have hset_eq : (F : Set L) = (Fd : Set L) :=
        Set.eq_of_subset_of_ncard_le hle (by omega) (Set.toFinite _)
      exact SetLike.ext' hset_eq
    have hex_nat : ∃! F : Subfield L, Nat.card F = p ^ d := ⟨Fd, hcard_Fd, huniq_nat⟩
    have hset_iff : ∀ F : Subfield L, setOrder F = (p ^ d : ℕ) ↔ Nat.card F = p ^ d :=
      fun F => setOrder_eq_natCast_iff.trans (and_iff_right inferInstance)
    have hex_set : ∃! F : Subfield L, setOrder F = (p ^ d : ℕ) :=
      ⟨Fd, (hset_iff Fd).mpr hcard_Fd, fun F hF => huniq_nat F ((hset_iff F).mp hF)⟩
    exact ⟨hdvd_Zp, hdvd_L, hex_nat, hex_set⟩

/-- Unconditional converse companion to **Exercise 12.3** (§12.1, p. 102): even without assuming
`Nat.Prime p`, whenever a field `L` has `p^n` elements (`setOrder L = (p ^ n : ℕ)`) and `d ∣ n`,
both `(X^{p^d} - X) ∣ (X^{p^n} - X)` in `L[X]` and `∃! F : Subfield L, setOrder F = (p ^ d : ℕ)`
(and `Nat.card F = p ^ d`) hold. -/
theorem exercise_12_3_converse_unconditional {L : Type u} [Field L] {p n d : ℕ}
    (hL : setOrder L = (p ^ n : ℕ)) (hdn : d ∣ n) :
    (Polynomial.X ^ (p ^ d) - Polynomial.X : L[X]) ∣
      (Polynomial.X ^ (p ^ n) - Polynomial.X : L[X]) ∧
    (∃! F : Subfield L, Nat.card F = p ^ d) ∧
    (∃! F : Subfield L, setOrder F = (p ^ d : ℕ)) := by
  obtain ⟨hfinL, hcardL⟩ := setOrder_eq_natCast_iff.mp hL
  let _ : Finite L := hfinL
  let _ : Fintype L := Fintype.ofFinite L
  have hcard_ge2 : 2 ≤ p ^ n := by
    rw [← hcardL, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨0, 1, zero_ne_one⟩
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hcard_ge2
    · exact hpos
  have hp_ge2 : 2 ≤ p := by
    by_contra hlt
    interval_cases p
    · rw [zero_pow hn_pos.ne'] at hcard_ge2; omega
    · simp at hcard_ge2
  obtain ⟨_, hq_prime, _, _, _, _, _, hcard_qm, _⟩ := finite_field_char_and_prime_power L
  let q := ringChar L
  let m := Module.finrank (primeSubfield L) L
  have hp_pow_q : ∃ k : ℕ, p = q ^ k := by
    have hpow_eq : p ^ n = q ^ m := hcardL.symm.trans hcard_qm
    have aux : ∀ a : ℕ, 1 ≤ a → (∀ r : ℕ, Nat.Prime r → r ∣ a → r = q) → ∃ k : ℕ, a = q ^ k := by
      intro a
      refine Nat.strongRecOn a fun a ih ha1 hall => ?_
      rcases eq_or_lt_of_le ha1 with rfl | ha_gt1
      · exact ⟨0, by simp⟩
      · have hr_prime : Nat.Prime a.minFac := Nat.minFac_prime (by omega)
        have hr_dvd : a.minFac ∣ a := Nat.minFac_dvd a
        have hr_eq : a.minFac = q := hall a.minFac hr_prime hr_dvd
        obtain ⟨b, hb⟩ := hr_dvd
        have hb_pos : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with rfl | hpos
          · rw [mul_zero] at hb; omega
          · exact hpos
        have hb_lt : b < a := by
          calc b < q * b := lt_mul_of_one_lt_left hb_pos hq_prime.one_lt
            _ = a.minFac * b := by rw [hr_eq]
            _ = a := hb.symm
        have hba : b ∣ a := ⟨a.minFac, by rw [mul_comm]; exact hb⟩
        have hall_b : ∀ r : ℕ, Nat.Prime r → r ∣ b → r = q := fun r hr hrb =>
          hall r hr (dvd_trans hrb hba)
        obtain ⟨k, hbk⟩ := ih b hb_lt hb_pos hall_b
        exact ⟨k + 1, by rw [hb, hr_eq, hbk, pow_succ']⟩
    refine aux p (by omega) fun r hr hrp => ?_
    have hr_qn : r ∣ q ^ m := hpow_eq ▸ dvd_trans hrp (dvd_pow_self p hn_pos.ne')
    exact (hq_prime.eq_one_or_self_of_dvd r (hr.dvd_of_dvd_pow hr_qn)).resolve_left hr.ne_one
  obtain ⟨k, rfl⟩ := hp_pow_q
  have hcardL_qk : Nat.card L = q ^ (k * n) := by rw [hcardL, ← pow_mul]
  have hk_dvd : (k * d) ∣ (k * n) := mul_dvd_mul_left k hdn
  obtain ⟨_, _, hex_nat, hex_set⟩ := (exercise_12_3.{u, 0} hq_prime hcardL_qk).2 hk_dvd
  have hpd_eq : (q ^ k) ^ d = q ^ (k * d) := (pow_mul q k d).symm
  exact ⟨poly_X_pow_sub_X_dvd (by omega) hdn, hpd_eq ▸ hex_nat, hpd_eq ▸ hex_set⟩

/-! ## §12.2 An example (printed pp. 102–103, PDF pp. 110–111) -/

/-- Garling's §12.2 Artin–Schreier polynomial `x^p - x - j̄ ∈ ℤ_p[x]` (printed pp. 102–103 /
PDF pp. 110–111). -/
noncomputable def artinSchreierPoly (p : ℕ) (j : ZMod p) : (ZMod p)[X] :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C j

private theorem artinSchreierPoly_monic_and_deg {p : ℕ} (hp : Nat.Prime p) (j : ZMod p) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    (artinSchreierPoly p j).Monic ∧ (artinSchreierPoly p j).natDegree = p := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨?_, ?_⟩
  · dsimp [artinSchreierPoly]; rw [sub_sub]
    refine Polynomial.monic_X_pow_sub ?_
    calc (Polynomial.X + Polynomial.C j).degree
        ≤ max Polynomial.X.degree (Polynomial.C j).degree := Polynomial.degree_add_le _ _
      _ ≤ 1 := max_le (by simp) (le_trans Polynomial.degree_C_le (by decide))
      _ < (p : WithBot ℕ) := WithBot.coe_lt_coe.mpr hp.one_lt
  · dsimp [artinSchreierPoly]; rw [sub_sub]
    have hlt : (Polynomial.X + Polynomial.C j).natDegree <
        (Polynomial.X ^ p : (ZMod p)[X]).natDegree := by
      calc (Polynomial.X + Polynomial.C j).natDegree
          ≤ max Polynomial.X.natDegree (Polynomial.C j).natDegree := Polynomial.natDegree_add_le _ _
        _ = 1 := by simp
        _ < p := hp.one_lt
        _ = (Polynomial.X ^ p : (ZMod p)[X]).natDegree := (Polynomial.natDegree_X_pow p).symm
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]

/-- Helper: in any commutative ring `R`, for any non-empty `S : Finset ι` and `r : ι → R`, the
degree-`(|S| - 1)` coefficient of `∏ i ∈ S, (X - C (r i))` is `- ∑ i ∈ S, r i`. -/
private theorem coeff_pred_prod_X_sub_C {ι R : Type*} [DecidableEq ι] [CommRing R] [Nontrivial R]
    (S : Finset ι) (r : ι → R) (hS : S.Nonempty) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (r i))).coeff (S.card - 1) = - ∑ i ∈ S, r i := by
  induction S using Finset.cons_induction with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | cons a T haT ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    · have hT_card_pos : 1 ≤ T.card := Finset.card_pos.mpr hT
      let Q : R[X] := ∏ i ∈ T, (Polynomial.X - Polynomial.C (r i))
      have hQ_mon : Q.Monic :=
        Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (r i)
      have hQ_deg : Q.natDegree = T.card := by
        rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i)),
          Finset.sum_congr rfl (fun i _ => Polynomial.natDegree_X_sub_C (r i)),
          Finset.sum_const, smul_eq_mul, mul_one]
      have hQ_top : Q.coeff T.card = 1 := by
        rw [← hQ_deg, ← Polynomial.leadingCoeff, hQ_mon.leadingCoeff]
      have hQ_sub : Q.coeff (T.card - 1) = - ∑ i ∈ T, r i := ih hT
      rw [Finset.prod_cons, Finset.card_cons, Nat.add_sub_cancel, Finset.sum_cons]
      change ((Polynomial.X - Polynomial.C (r a)) * Q).coeff T.card = -(r a + ∑ i ∈ T, r i)
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      have hX_coeff : (Polynomial.X * Q).coeff T.card = Q.coeff (T.card - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hT_card_pos]
        exact Polynomial.coeff_X_mul Q (T.card - 1)
      rw [hX_coeff, hQ_sub, hQ_top]
      ring

/-- Irreducibility of `x^p - x - j̄ ∈ ℤ_p[x]` for prime `p` and `j ≠ 0` (§12.2, printed pp. 102–103 /
PDF pp. 110–111), proved directly via Garling's degree-`(d - 1)` coefficient argument on pp. 102–103.
-/
theorem artinSchreierPoly_irreducible {p : ℕ} [Fact p.Prime] {j : ZMod p} (hj : j ≠ 0) :
    Irreducible (artinSchreierPoly p j) ∧ IsGarlingIrreducible (artinSchreierPoly p j) := by
  classical
  have hp : Nat.Prime p := Fact.out
  let g := artinSchreierPoly p j
  obtain ⟨hg_mon, hg_deg⟩ := artinSchreierPoly_monic_and_deg hp j
  have hno_root : ∀ a : ZMod p, g.eval a = -j ∧ g.eval a ≠ 0 := by
    intro a
    have hev : g.eval a = -j := by dsimp [g, artinSchreierPoly]; simp [ZMod.pow_card]
    exact ⟨hev, hev ▸ neg_ne_zero.mpr hj⟩
  obtain ⟨L, instFL, instAZL, hsfL, _⟩ := theorem_7_3_natDegree g
  let _ : Field L := instFL
  let _ : Algebra (ZMod p) L := instAZL
  let ι := algebraMap (ZMod p) L
  have hcharL : ringChar L = p :=
    ringChar_eq_of_prime_natCast_eq_zero hp
      (by rw [← map_natCast ι, ZMod.natCast_self, map_zero])
  have hdeg_map : (g.map ι).natDegree = p := (hg_mon.natDegree_map ι).trans hg_deg
  obtain ⟨α, hα_root⟩ :=
    exists_root_of_garlingSplitsOver hsfL.1 (by change 1 ≤ (artinSchreierPoly p j).natDegree; rw [hg_deg]; exact hp.pos)
  have hα_pow : α ^ p = α + ι j := by
    have h1 : α ^ p - α - ι j = 0 := by simpa [g, artinSchreierPoly] using hα_root
    linear_combination h1
  have hshift_root : ∀ k : ZMod p, Polynomial.IsRoot (g.map ι) (α + ι k) := by
    intro k
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
    dsimp [g, artinSchreierPoly]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    have hpow_add : (α + ι k) ^ p = α ^ p + (ι k) ^ p :=
      (garlingFrobenius L hcharL hp.ne_zero).map_add α (ι k)
    have hk_pow : (ι k) ^ p = ι k := by rw [← map_pow, ZMod.pow_card]
    rw [hpow_add, hk_pow, hα_pow]
    ring
  have hg_map_prod : g.map ι = ∏ k : ZMod p, (Polynomial.X - Polynomial.C (α + ι k)) := by
    let P : L[X] := ∏ k : ZMod p, (Polynomial.X - Polynomial.C (α + ι k))
    have hP_mon : P.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
    have hP_deg : P.natDegree = p := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun k _ => Polynomial.natDegree_X_sub_C _),
        Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ZMod.card]
    have hdvd : P ∣ g.map ι := by
      refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun k _ => ?_)
      · refine Polynomial.pairwise_coprime_X_sub_C (fun x y hxy => ?_) hab
        exact ι.injective (add_left_cancel hxy)
      · exact Polynomial.dvd_iff_isRoot.mpr (hshift_root k)
    obtain ⟨q, hq⟩ := hdvd
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact (hg_mon.map ι).ne_zero hq
    have hq_deg : q.natDegree = 0 := by
      have hd := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul hP_mon.ne_zero hq0, hdeg_map, hP_deg] at hd
      omega
    have hq_mon : q.Monic := by
      have hlc := congrArg Polynomial.leadingCoeff hq
      rw [Polynomial.leadingCoeff_mul, (hg_mon.map ι).leadingCoeff, hP_mon.leadingCoeff, one_mul] at hlc
      exact hlc.symm
    rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]
  have hirr : Irreducible g := by
    refine ⟨?_, ?_⟩
    · intro hu
      have hd0 : (artinSchreierPoly p j).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      exact hp.ne_zero (hg_deg.symm.trans hd0)
    · intro a b hab
      by_contra hboth
      obtain ⟨ha_nu, hb_nu⟩ := not_or.mp hboth
      have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hab; exact hg_mon.ne_zero hab
      have hb0 : b ≠ 0 := fun h0 => by rw [h0, mul_zero] at hab; exact hg_mon.ne_zero hab
      have hadeg_pos : 1 ≤ a.natDegree := by
        by_contra hle
        have hd0 : a.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at ha_nu ha0
        have hc0 : a.coeff 0 ≠ 0 := fun hc => ha0 (by simp [hc])
        exact ha_nu ((IsUnit.mk0 (a.coeff 0) hc0).map Polynomial.C)
      have hbdeg_pos : 1 ≤ b.natDegree := by
        by_contra hle
        have hd0 : b.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at hb_nu hb0
        have hc0 : b.coeff 0 ≠ 0 := fun hc => hb0 (by simp [hc])
        exact hb_nu ((IsUnit.mk0 (b.coeff 0) hc0).map Polynomial.C)
      have hdeg_sum : a.natDegree + b.natDegree = p := by
        rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hg_deg]
      let u : ZMod p := a.leadingCoeff
      have hu0 : u ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
      let g₁ : (ZMod p)[X] := Polynomial.C u⁻¹ * a
      let g₂ : (ZMod p)[X] := Polynomial.C u * b
      have hg₁g₂ : g = g₁ * g₂ := by
        dsimp [g₁, g₂]
        calc g = a * b := hab
          _ = Polynomial.C 1 * (a * b) := by simp
          _ = Polynomial.C (u⁻¹ * u) * (a * b) := by rw [inv_mul_cancel₀ hu0]
          _ = (Polynomial.C u⁻¹ * a) * (Polynomial.C u * b) := by rw [map_mul]; ring
      have hg₁_mon : g₁.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          inv_mul_cancel₀ hu0]
      let d := g₁.natDegree
      have hd_eq : d = a.natDegree := Polynomial.natDegree_C_mul (inv_ne_zero hu0)
      have hd_ge1 : 1 ≤ d := by omega
      have hd_lt_p : d < p := by omega
      let S : Finset (ZMod p) := Finset.univ.filter fun k => (g₁.map ι).IsRoot (α + ι k)
      have hg₁_dvd_map : g₁.map ι ∣ g.map ι :=
        ⟨g₂.map ι, by rw [hg₁g₂, Polynomial.map_mul]⟩
      let PS : L[X] := ∏ k ∈ S, (Polynomial.X - Polynomial.C (α + ι k))
      let PSc : L[X] := ∏ k ∈ Finset.univ \ S, (Polynomial.X - Polynomial.C (α + ι k))
      have hPS_dvd : PS ∣ g₁.map ι := by
        refine Finset.prod_dvd_of_coprime (fun x _ y _ hxy => ?_) (fun k hk => ?_)
        · refine Polynomial.pairwise_coprime_X_sub_C (fun x' y' h => ?_) hxy
          exact ι.injective (add_left_cancel h)
        · exact Polynomial.dvd_iff_isRoot.mpr ((Finset.mem_filter.mp hk).2)
      have hprod_split : PS * PSc = g.map ι := by
        rw [hg_map_prod, mul_comm]
        exact Finset.prod_sdiff (Finset.subset_univ S)
      have hcop_PSc : IsCoprime (g₁.map ι) PSc := by
        refine IsCoprime.prod_right fun k hk => ?_
        have hk_not : ¬ (g₁.map ι).IsRoot (α + ι k) := fun hr =>
          (Finset.mem_sdiff.mp hk).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hr⟩)
        exact ((Polynomial.irreducible_X_sub_C (α + ι k)).coprime_iff_not_dvd.mpr
          (mt Polynomial.dvd_iff_isRoot.mp hk_not)).symm
      have hg₁_dvd_PS : g₁.map ι ∣ PS :=
        hcop_PSc.dvd_of_dvd_mul_right (hprod_split.symm ▸ hg₁_dvd_map)
      have hPS_mon : PS.Monic :=
        Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
      rcases id hg₁_dvd_PS with ⟨q, hq⟩
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hPS_mon.ne_zero hq
      have hq_deg : q.natDegree = 0 := by
        have hle1 := Polynomial.natDegree_le_of_dvd hg₁_dvd_PS hPS_mon.ne_zero
        have hle2 := Polynomial.natDegree_le_of_dvd hPS_dvd (hg₁_mon.map ι).ne_zero
        have hd_mul := congrArg Polynomial.natDegree hq
        rw [Polynomial.natDegree_mul (hg₁_mon.map ι).ne_zero hq0] at hd_mul
        omega
      have hq_mon : q.Monic := by
        have hlc := congrArg Polynomial.leadingCoeff hq
        rw [Polynomial.leadingCoeff_mul, hPS_mon.leadingCoeff, (hg₁_mon.map ι).leadingCoeff,
          one_mul] at hlc
        exact hlc.symm
      have hg₁_eq_PS : g₁.map ι = PS := by
        rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]
      have hS_card : S.card = d := by
        have hd_PS : PS.natDegree = S.card := by
          rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _),
            Finset.sum_congr rfl (fun k _ => Polynomial.natDegree_X_sub_C _),
            Finset.sum_const, smul_eq_mul, mul_one]
        rw [← hd_PS, ← hg₁_eq_PS, hg₁_mon.natDegree_map]
      have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hcoeff_eq : ι (g₁.coeff (d - 1)) = - ∑ k ∈ S, (α + ι k) := by
        have h1 : (g₁.map ι).coeff (d - 1) = ι (g₁.coeff (d - 1)) := Polynomial.coeff_map ι _
        rw [← h1, hg₁_eq_PS, ← hS_card]
        exact coeff_pred_prod_X_sub_C S (fun k => α + ι k) hS_ne
      have hsum_split : ∑ k ∈ S, (α + ι k) = (d : L) * α + ι (∑ k ∈ S, k) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hS_card, map_sum]
      have hdα : (d : L) * α = ι (-g₁.coeff (d - 1) - ∑ k ∈ S, k) := by
        rw [map_sub, map_neg, hcoeff_eq, hsum_split]
        ring
      have hd_zmod_ne0 : ((d : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        have hdvd_d : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp h0
        have hle := Nat.le_of_dvd hd_ge1 hdvd_d
        omega
      have hdL_eq : (d : L) = ι (d : ZMod p) := (map_natCast ι d).symm
      let c : ZMod p := ((d : ZMod p))⁻¹ * (-g₁.coeff (d - 1) - ∑ k ∈ S, k)
      have hιd_ne0 : ι (d : ZMod p) ≠ 0 :=
        fun h0 => hd_zmod_ne0 (ι.injective (h0.trans (map_zero ι).symm))
      have hα_c : α = ι c := by
        apply mul_left_cancel₀ hιd_ne0
        have hdc : (d : ZMod p) * c = -g₁.coeff (d - 1) - ∑ k ∈ S, k := by
          dsimp [c]
          rw [← mul_assoc, mul_inv_cancel₀ hd_zmod_ne0, one_mul]
        calc ι (d : ZMod p) * α = (d : L) * α := by rw [hdL_eq]
          _ = ι (-g₁.coeff (d - 1) - ∑ k ∈ S, k) := hdα
          _ = ι ((d : ZMod p) * c) := by rw [hdc]
          _ = ι (d : ZMod p) * ι c := map_mul ι _ _
      have hev_c : ι (g.eval c) = 0 := by
        have h1 : Polynomial.aeval (ι c) g = ι (g.eval c) := by
          dsimp [g, artinSchreierPoly]
          simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
            Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          rfl
        rw [← h1, ← hα_c, hα_root]
      exact (hno_root c).2 (ι.injective (hev_c.trans (map_zero ι).symm))
  exact ⟨hirr, (isGarlingIrreducible_iff g).mpr hirr⟩

/-- **§12.2 Worked Artin–Schreier Example** (printed pp. 102–103 / PDF pp. 110–111; noting printed
slip `K` for `ℤ_p` in `L = K(α)`, `[L:K] = p`, and `L:K is also a splitting field extension`):
for any prime `p` and any splitting field extension `L : ℤ_p` for `g = x^p - x - 1`, proves all
properties deduced in §12.2. -/
theorem section_12_2_artin_schreier_example {p : ℕ} [Fact p.Prime]
    (L : Type u) [Field L] [Algebra (ZMod p) L]
    (hsf : IsGarlingSplittingFieldExtension (ZMod p) L (artinSchreierPoly p 1)) :
    let g := artinSchreierPoly p 1
    (∀ a : ZMod p, g.eval a = -1 ∧ g.eval a ≠ 0) ∧
    Irreducible g ∧
    IsGarlingIrreducible g ∧
    (∃ α : L,
      Polynomial.aeval α g = 0 ∧
      IntermediateField.adjoin (ZMod p) {α} = ⊤ ∧
      (∀ j : ZMod p, j ≠ 0 →
        (artinSchreierPoly p j).map (algebraMap (ZMod p) L) =
          ∏ k : ZMod p,
            (Polynomial.X - Polynomial.C (algebraMap (ZMod p) L j * α + algebraMap (ZMod p) L k)))) ∧
    Module.finrank (ZMod p) L = p ∧
    Nat.card L = p ^ p ∧
    setOrder L = (p ^ p : ℕ) ∧
    IsGarlingSplittingFieldExtension (ZMod p) L (Polynomial.X ^ (p ^ p) - Polynomial.X) ∧
    (g ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X])) ∧
    (∀ j : ZMod p, j ≠ 0 →
      Irreducible (artinSchreierPoly p j) ∧
      (artinSchreierPoly p j ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X])) ∧
      IsGarlingSplittingFieldExtension (ZMod p) L (artinSchreierPoly p j)) := by
  classical
  have hp : Nat.Prime p := Fact.out
  intro g
  let ι := algebraMap (ZMod p) L
  have hno_root : ∀ a : ZMod p, g.eval a = -1 ∧ g.eval a ≠ 0 := fun a => by
    have hev : g.eval a = -1 := by dsimp [g, artinSchreierPoly]; simp [ZMod.pow_card]
    exact ⟨hev, hev ▸ neg_ne_zero.mpr one_ne_zero⟩
  obtain ⟨hirr_g, hgirr_g⟩ := artinSchreierPoly_irreducible (p := p) (one_ne_zero : (1 : ZMod p) ≠ 0)
  obtain ⟨hg_mon, hg_deg⟩ := artinSchreierPoly_monic_and_deg hp 1
  obtain ⟨α, hα_root⟩ :=
    exists_root_of_garlingSplitsOver hsf.1 (by change 1 ≤ (artinSchreierPoly p 1).natDegree; rw [hg_deg]; exact hp.pos)
  have hα_pow : α ^ p = α + 1 := by
    have h1 : α ^ p - α - 1 = 0 := by simpa [g, artinSchreierPoly] using hα_root
    linear_combination h1
  have hcharL : ringChar L = p :=
    ringChar_eq_of_prime_natCast_eq_zero hp
      (by rw [← map_natCast ι, ZMod.natCast_self, map_zero])
  have hfac_j : ∀ j : ZMod p, j ≠ 0 →
      (artinSchreierPoly p j).map ι =
        ∏ k : ZMod p, (Polynomial.X - Polynomial.C (ι j * α + ι k)) := by
    intro j hj
    let gj := artinSchreierPoly p j
    obtain ⟨hgj_mon, hgj_deg0⟩ := artinSchreierPoly_monic_and_deg hp j
    have hgj_deg : (gj.map ι).natDegree = p := (hgj_mon.natDegree_map ι).trans hgj_deg0
    let P : L[X] := ∏ k : ZMod p, (Polynomial.X - Polynomial.C (ι j * α + ι k))
    have hP_mon : P.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
    have hP_deg : P.natDegree = p := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun k _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun k _ => Polynomial.natDegree_X_sub_C _),
        Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ZMod.card]
    have hdvd : P ∣ gj.map ι := by
      refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun k _ => ?_)
      · refine Polynomial.pairwise_coprime_X_sub_C (fun x y hxy => ?_) hab
        exact ι.injective (add_left_cancel hxy)
      · rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map,
          ← Polynomial.aeval_def]
        dsimp [gj, artinSchreierPoly]
        simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        have hadd : (ι j * α + ι k) ^ p = (ι j * α) ^ p + (ι k) ^ p :=
          (garlingFrobenius L hcharL hp.ne_zero).map_add _ _
        rw [hadd, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hα_pow]
        ring
    obtain ⟨q, hq⟩ := hdvd
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact (hgj_mon.map ι).ne_zero hq
    have hq_deg : q.natDegree = 0 := by
      have hd := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul hP_mon.ne_zero hq0, hgj_deg, hP_deg] at hd
      omega
    have hq_mon : q.Monic := by
      have hlc := congrArg Polynomial.leadingCoeff hq
      rw [Polynomial.leadingCoeff_mul, (hgj_mon.map ι).leadingCoeff, hP_mon.leadingCoeff, one_mul] at hlc
      exact hlc.symm
    rw [hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]
  have hadj_top : IntermediateField.adjoin (ZMod p) {α} = ⊤ := by
    let M : IntermediateField (ZMod p) L := IntermediateField.adjoin (ZMod p) {α}
    have hspM : GarlingSplitsOver (ZMod p) M g := by
      rw [garlingSplitsOver_iff_splits]
      let βM : ZMod p → M := fun k =>
        ⟨α + ι k, M.add_mem (IntermediateField.mem_adjoin_simple_self _ α) (M.algebraMap_mem k)⟩
      have hmapM : g.map (algebraMap (ZMod p) M) = ∏ k : ZMod p, (Polynomial.X - Polynomial.C (βM k)) := by
        apply Polynomial.map_injective M.val.toRingHom M.val.injective
        rw [Polynomial.map_map]
        have halg : M.val.toRingHom.comp (algebraMap (ZMod p) M) = ι := rfl
        rw [halg, hfac_j 1 one_ne_zero, Polynomial.map_prod]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp [βM]
      rw [hmapM]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    by_contra hne
    exact hsf.2 M hne hspM
  have hfinKL : IsFiniteExtension (ZMod p) L := (corollary_to_theorem_7_1 hsf).1
  have _ : Module.Finite (ZMod p) L := (isFiniteExtension_iff_moduleFinite (ZMod p) L).mp hfinKL
  have hint_α : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  have hmin_α : minpoly (ZMod p) α = g :=
    eq_of_monic_dvd_irreducible (minpoly.monic hint_α) hg_mon
      (minpoly.irreducible hint_α).not_isUnit hirr_g (minpoly.dvd (ZMod p) α hα_root)
  have hdegL : Module.finrank (ZMod p) L = p := by
    have h1 := IntermediateField.adjoin.finrank hint_α
    have h2 : Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) =
        Module.finrank (ZMod p) L := by
      rw [hadj_top]
      exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
    rw [← h2, h1, hmin_α, hg_deg]
  let bZL := Module.finBasis (ZMod p) L
  have hcardL : Nat.card L = p ^ p := by
    rw [Nat.card_congr bZL.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hdegL]
  have hfinL : Finite L := Nat.finite_of_card_ne_zero (hcardL.symm ▸ pow_ne_zero p hp.ne_zero)
  let _ : Finite L := hfinL
  have hsetL : setOrder L = (p ^ p : ℕ) := setOrder_eq_natCast_iff.mpr ⟨hfinL, hcardL⟩
  have hextZL : extDegree (ZMod p) L = p :=
    (extDegree_eq_finrank (ZMod p) L).trans (congrArg Nat.cast hdegL)
  have hsf_Xpp : IsGarlingSplittingFieldExtension (ZMod p) L (Polynomial.X ^ (p ^ p) - Polynomial.X) := by
    simpa [Nat.card_zmod] using isSplittingField_of_extDegree_eq hp.pos hextZL
  have hall_j : ∀ j : ZMod p, j ≠ 0 →
      Irreducible (artinSchreierPoly p j) ∧
      (artinSchreierPoly p j ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X])) ∧
      IsGarlingSplittingFieldExtension (ZMod p) L (artinSchreierPoly p j) := by
    intro j hj
    obtain ⟨hirr_j, _⟩ := artinSchreierPoly_irreducible (p := p) hj
    let gj := artinSchreierPoly p j
    obtain ⟨hgj_mon, _⟩ := artinSchreierPoly_monic_and_deg hp j
    obtain ⟨_, _, _, _, hpowL_pp, _⟩ := finite_field_isSplittingField_primeSubfield hp hcardL
    have hjα_root : Polynomial.aeval (ι j * α) gj = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hfac_j j hj, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (0 : ZMod p)) (by simp)
    have hint_jα : IsIntegral (ZMod p) (ι j * α) := IsIntegral.of_finite (ZMod p) _
    have hmin_jα : minpoly (ZMod p) (ι j * α) = gj :=
      eq_of_monic_dvd_irreducible (minpoly.monic hint_jα) hgj_mon
        (minpoly.irreducible hint_jα).not_isUnit hirr_j (minpoly.dvd (ZMod p) (ι j * α) hjα_root)
    have hdvd_Xpp : gj ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) := by
      rw [← hmin_jα]
      refine minpoly.dvd (ZMod p) (ι j * α) ?_
      simp [hpowL_pp (ι j * α)]
    have hsf_gj : IsGarlingSplittingFieldExtension (ZMod p) L gj := by
      rw [isGarlingSplittingFieldExtension_iff]
      refine ⟨?_, ?_⟩
      · rw [hfac_j j hj]
        exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
      · rw [eq_top_iff]
        have hroot_mem : ι j * α ∈ gj.rootSet L :=
          (Polynomial.mem_rootSet_of_ne hgj_mon.ne_zero).mpr hjα_root
        have hα_in : α ∈ Algebra.adjoin (ZMod p) (gj.rootSet L : Set L) := by
          have hjα_in : ι j * α ∈ Algebra.adjoin (ZMod p) (gj.rootSet L : Set L) :=
            Algebra.subset_adjoin hroot_mem
          have hmul := Subalgebra.smul_mem (Algebra.adjoin (ZMod p) (gj.rootSet L : Set L)) hjα_in j⁻¹
          rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hj, map_one, one_mul] at hmul
          exact hmul
        intro x _
        have hx_M : x ∈ (IntermediateField.adjoin (ZMod p) {α}).toSubalgebra := by
          rw [hadj_top]; trivial
        rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_α.isAlgebraic] at hx_M
        exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hα_in) hx_M
    exact ⟨hirr_j, hdvd_Xpp, hsf_gj⟩
  exact ⟨hno_root, hirr_g, hgirr_g, ⟨α, hα_root, hadj_top, hfac_j⟩, hdegL, hcardL, hsetL,
    hsf_Xpp, (hall_j 1 one_ne_zero).2.1, hall_j⟩

/-- Lightweight finiteness proof for `{g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p}`
(injection into `Fin p → ZMod p` by lower coefficients), avoiding proof-term unfolding in `whnf`. -/
private theorem finite_monic_irred_deg_p (p : ℕ) [Fact p.Prime] :
    {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p}.Finite := by
  let S := {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p}
  let enc : S → (Fin p → ZMod p) := fun g i => g.1.coeff i
  have henc_inj : Function.Injective enc := by
    intro g₁ g₂ h
    apply Subtype.ext
    ext k
    rcases lt_trichotomy k p with hlt | heq | hgt
    · exact congrFun h ⟨k, hlt⟩
    · subst k
      have hc₁ : g₁.1.coeff g₁.1.natDegree = 1 := g₁.2.1.leadingCoeff
      have hc₂ : g₂.1.coeff g₂.1.natDegree = 1 := g₂.2.1.leadingCoeff
      rw [g₁.2.2.2] at hc₁
      rw [g₂.2.2.2] at hc₂
      rw [hc₁, hc₂]
    · have hk₁ : g₁.1.natDegree < k := by rw [g₁.2.2.2]; exact hgt
      have hk₂ : g₂.1.natDegree < k := by rw [g₂.2.2.2]; exact hgt
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk₁,
        Polynomial.coeff_eq_zero_of_natDegree_lt hk₂]
  have _ : Finite S := Finite.of_injective enc henc_inj
  exact Set.toFinite S

/-- Noncomputable finite set of all monic irreducible polynomials of degree `p` over `ℤ_p`
(`Exercise 12.4`, §12.2, printed p. 103 / PDF p. 111). -/
noncomputable def monicIrredDegPFinset (p : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  (finite_monic_irred_deg_p p).toFinset

@[simp]
theorem mem_monicIrredDegPFinset_iff {p : ℕ} [Fact p.Prime] (g : (ZMod p)[X]) :
    g ∈ monicIrredDegPFinset p ↔ g.Monic ∧ Irreducible g ∧ g.natDegree = p :=
  Set.Finite.mem_toFinset _

/-- **Exercise 12.4** (§12.2, printed p. 103 / PDF p. 111; see `QUEUE.md` on `"Factorize..."` prompt):
*"Factorize `x^{p^p} - x` over `ℤ_p`."* -/
theorem exercise_12_4 (p : ℕ) [Fact p.Prime] :
    let Lin : Finset (ZMod p)[X] :=
      Finset.univ.image (fun a : ZMod p => Polynomial.X - Polynomial.C a)
    let DegP : Finset (ZMod p)[X] := monicIrredDegPFinset p
    Disjoint Lin DegP ∧
    Lin.card = p ∧
    DegP.card = p ^ (p - 1) - 1 ∧
    DegP.card = (p ^ p - p) / p ∧
    (∀ h ∈ Lin ∪ DegP, h.Monic ∧ Irreducible h ∧ IsGarlingIrreducible h) ∧
    (∏ a : ZMod p, (Polynomial.X - Polynomial.C a) = (Polynomial.X ^ p - Polynomial.X : (ZMod p)[X])) ∧
    (∀ j : ZMod p, j ≠ 0 → artinSchreierPoly p j ∈ DegP) ∧
    ((Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) =
      (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)) * (∏ g ∈ DegP, g)) := by
  classical
  have hp : Nat.Prime p := Fact.out
  intro Lin DegP
  have hsetZ : setOrder (ZMod p) = (p : ℕ) :=
    setOrder_eq_natCast_iff.mpr ⟨inferInstance, Nat.card_zmod p⟩
  obtain ⟨_, _, hS_ncard, _⟩ := exercise_12_1 hsetZ hp
  have hDegP_card1 : DegP.card = (p ^ p - p) / p := by
    rw [← Set.ncard_coe_finset]
    have hcoe : (DegP : Set (ZMod p)[X]) =
        {g : (ZMod p)[X] | g.Monic ∧ Irreducible g ∧ g.natDegree = p} := by
      ext g; simp [DegP]
    rw [hcoe, hS_ncard]
  have hDegP_card2 : DegP.card = p ^ (p - 1) - 1 := by
    rw [hDegP_card1]
    have hpp : p ^ p - p = (p ^ (p - 1) - 1) * p := by
      calc p ^ p - p = p ^ (p - 1) * p - 1 * p := by
            rw [← pow_succ, Nat.sub_add_cancel hp.pos, one_mul]
        _ = (p ^ (p - 1) - 1) * p := (Nat.sub_mul _ _ _).symm
    rw [hpp, Nat.mul_div_cancel _ hp.pos]
  have hLin_card : Lin.card = p := by
    dsimp [Lin]
    rw [Finset.card_image_of_injective _ (fun a b hab => by
      have h := congrArg (fun q : (ZMod p)[X] => q.coeff 0) hab
      simp at h
      exact h), Finset.card_univ, ZMod.card]
  have hdisj : Disjoint Lin DegP := by
    rw [Finset.disjoint_left]
    intro h hhL hhD
    rcases Finset.mem_image.mp hhL with ⟨a, _, rfl⟩
    have hd := ((mem_monicIrredDegPFinset_iff _).mp hhD).2.2
    rw [Polynomial.natDegree_X_sub_C] at hd
    exact hp.ne_one hd.symm
  have hall_irr : ∀ h ∈ Lin ∪ DegP, h.Monic ∧ Irreducible h ∧ IsGarlingIrreducible h := by
    intro h hh
    rcases Finset.mem_union.mp hh with hhL | hhD
    · rcases Finset.mem_image.mp hhL with ⟨a, _, rfl⟩
      have hirr := Polynomial.irreducible_X_sub_C a
      exact ⟨Polynomial.monic_X_sub_C a, hirr, (isGarlingIrreducible_iff _).mpr hirr⟩
    · obtain ⟨hm, hi, _⟩ := (mem_monicIrredDegPFinset_iff h).mp hhD
      exact ⟨hm, hi, (isGarlingIrreducible_iff h).mpr hi⟩
  have hprod_Lin :
      ∏ a : ZMod p, (Polynomial.X - Polynomial.C a) =
        (Polynomial.X ^ p - Polynomial.X : (ZMod p)[X]) :=
    (poly_X_pow_card_sub_X_eq_prod (ZMod p) (ZMod.card p) ZMod.pow_card).symm
  have hAS_mem : ∀ j : ZMod p, j ≠ 0 → artinSchreierPoly p j ∈ DegP := by
    intro j hj
    obtain ⟨hm, hd⟩ := artinSchreierPoly_monic_and_deg hp j
    exact (mem_monicIrredDegPFinset_iff _).mpr ⟨hm, (artinSchreierPoly_irreducible hj).1, hd⟩
  have hDegP_dvd : ∀ g ∈ DegP, g ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) := by
    intro g hg
    obtain ⟨hg_mon, hg_irr, hg_deg⟩ := (mem_monicIrredDegPFinset_iff g).mp hg
    have _ : Fact (Irreducible g) := ⟨hg_irr⟩
    let E := AdjoinRoot g
    let pbE : PowerBasis (ZMod p) E := AdjoinRoot.powerBasis hg_mon.ne_zero
    have _ : Module.Finite (ZMod p) E := pbE.finite
    have hdegE : Module.finrank (ZMod p) E = p := pbE.finrank.trans hg_deg
    let bZE := Module.finBasis (ZMod p) E
    have hcardE : Nat.card E = p ^ p := by
      rw [Nat.card_congr bZE.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hdegE]
    obtain ⟨_, _, _, _, hpowE, _⟩ := finite_field_isSplittingField_primeSubfield hp hcardE
    let rE : E := AdjoinRoot.root g
    have hrE_min : minpoly (ZMod p) rE = g :=
      (AdjoinRoot.minpoly_root hg_mon.ne_zero).trans
        (by rw [hg_mon.leadingCoeff, inv_one, map_one, mul_one])
    rw [← hrE_min]
    refine minpoly.dvd (ZMod p) rE ?_
    simp [hpowE rE]
  have hprod_Lin_eq : ∏ h ∈ Lin, h = ∏ a : ZMod p, (Polynomial.X - Polynomial.C a) := by
    dsimp [Lin]
    exact Finset.prod_image fun a _ b _ hab => by
      have h := congrArg (fun q : (ZMod p)[X] => q.coeff 0) hab
      simp at h
      exact h
  have hRHS_eq_union :
      (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)) * (∏ g ∈ DegP, g) =
        ∏ h ∈ Lin ∪ DegP, h := by
    rw [← hprod_Lin_eq, Finset.prod_union hdisj]
  have hunion_dvd : (∏ h ∈ Lin ∪ DegP, h) ∣ (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) := by
    refine Finset.prod_dvd_of_coprime (fun h₁ hh₁ h₂ hh₂ hne => ?_) (fun h hh => ?_)
    · change IsCoprime h₁ h₂
      obtain ⟨hm₁, hi₁, _⟩ := hall_irr h₁ hh₁
      obtain ⟨hm₂, hi₂, _⟩ := hall_irr h₂ hh₂
      rw [hi₁.coprime_iff_not_dvd]
      intro hdvd
      exact hne (eq_of_monic_dvd_irreducible hm₁ hm₂ hi₁.not_isUnit hi₂ hdvd)
    · rcases Finset.mem_union.mp hh with hhL | hhD
      · rcases Finset.mem_image.mp hhL with ⟨a, _, rfl⟩
        have hlin_dvd : (Polynomial.X - Polynomial.C a) ∣ (Polynomial.X ^ p - Polynomial.X) := by
          rw [← hprod_Lin]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
        have hpow1_dvd :
            (Polynomial.X ^ p - Polynomial.X : (ZMod p)[X]) ∣
              (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) := by
          simpa [pow_one] using
            (poly_X_pow_sub_X_dvd (R := ZMod p) hp.pos (one_dvd p))
        exact dvd_trans hlin_dvd hpow1_dvd
      · exact hDegP_dvd h hhD
  have hunion_mon : (∏ h ∈ Lin ∪ DegP, h).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun h hh => (hall_irr h hh).1
  have hunion_deg : (∏ h ∈ Lin ∪ DegP, h).natDegree = p ^ p := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun h hh => (hall_irr h hh).1),
      Finset.sum_union hdisj]
    have hsumL : ∑ h ∈ Lin, h.natDegree = p := by
      have h1 : ∀ h ∈ Lin, h.natDegree = 1 := by
        intro h hh; rcases Finset.mem_image.mp hh with ⟨a, _, rfl⟩
        exact Polynomial.natDegree_X_sub_C a
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, hLin_card]
    have hsumD : ∑ g ∈ DegP, g.natDegree = p ^ p - p := by
      have h1 : ∀ g ∈ DegP, g.natDegree = p :=
        fun g hg => ((mem_monicIrredDegPFinset_iff g).mp hg).2.2
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, hDegP_card2]
      calc (p ^ (p - 1) - 1) * p = p ^ (p - 1) * p - 1 * p := Nat.sub_mul _ _ _
        _ = p ^ p - p := by rw [← pow_succ, Nat.sub_add_cancel hp.pos, one_mul]
    have hp_le_pp : p ≤ p ^ p := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ p := Nat.pow_le_pow_right hp.pos hp.pos
    omega
  obtain ⟨hf_mon, hf_deg⟩ :=
    monic_and_natDegree_X_pow_sub_X (ZMod p) (one_lt_pow₀ hp.one_lt hp.ne_zero)
  obtain ⟨q, hq⟩ := hunion_dvd
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hf_mon.ne_zero hq
  have hq_deg : q.natDegree = 0 := by
    have hd := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hunion_mon.ne_zero hq0, hf_deg, hunion_deg] at hd
    omega
  have hq_mon : q.Monic := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, hf_mon.leadingCoeff, hunion_mon.leadingCoeff, one_mul] at hlc
    exact hlc.symm
  have hfac_full :
      (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X]) =
        (∏ a : ZMod p, (Polynomial.X - Polynomial.C a)) * (∏ g ∈ DegP, g) := by
    rw [hRHS_eq_union, hq, Polynomial.eq_one_of_monic_natDegree_zero hq_mon hq_deg, mul_one]
  exact ⟨hdisj, hLin_card, hDegP_card2, hDegP_card1, hall_irr, hprod_Lin, hAS_mem, hfac_full⟩

/-- Explicit specialization of **Exercise 12.4** at `p = 2` (§12.2, p. 103):
`x^4 - x = x (x - 1) (x^2 - x - 1)` in `ℤ_2[x]`, with all three factors monic and irreducible. -/
theorem exercise_12_4_p2 :
    (Polynomial.X ^ (2 ^ 2) - Polynomial.X : (ZMod 2)[X]) =
      Polynomial.X * (Polynomial.X - 1) * (artinSchreierPoly 2 1) ∧
    Irreducible (Polynomial.X : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X - 1 : (ZMod 2)[X]) ∧
    Irreducible (artinSchreierPoly 2 1) := by
  have hirr_X : Irreducible (Polynomial.X : (ZMod 2)[X]) := by
    simpa using Polynomial.irreducible_X_sub_C (0 : ZMod 2)
  have hirr_X1 : Irreducible (Polynomial.X - 1 : (ZMod 2)[X]) := by
    simpa using Polynomial.irreducible_X_sub_C (1 : ZMod 2)
  have hirr_AS : Irreducible (artinSchreierPoly 2 1) :=
    (artinSchreierPoly_irreducible (p := 2) (by decide : (1 : ZMod 2) ≠ 0)).1
  refine ⟨?_, hirr_X, hirr_X1, hirr_AS⟩
  dsimp [artinSchreierPoly]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    change Polynomial.C (2 : ZMod 2) = 0
    have h2z : (2 : ZMod 2) = 0 := by decide
    rw [h2z, map_zero]
  calc (Polynomial.X ^ (2 ^ 2) - Polynomial.X : (ZMod 2)[X])
      = Polynomial.X ^ 4 - Polynomial.X - 2 * (Polynomial.X ^ 3 - Polynomial.X) := by
        rw [h2, zero_mul, sub_zero]; rfl
    _ = Polynomial.X * (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C 1) := by
        simp only [map_one]; ring

/-- Explicit refutation of `DOSSIER-GARLING.md` line 353's false formula for **Exercise 12.4**:
for **every** prime `p`, `x ∏_{j ∈ ℤ_p \ {0}} (x^p - x - j̄)` has degree `p^2 - p + 1 < p^p` and
therefore **never** equals `x^{p^p} - x` in `ℤ_p[x]`; moreover, for every odd prime `p ≥ 3`, even
`(x^p - x) ∏_{j ∈ ℤ_p \ {0}} (x^p - x - j̄) = x^{p^2} - x` has degree `p^2 < p^p` and does not equal
`x^{p^p} - x`. -/
theorem exercise_12_4_dossier_formula_false {p : ℕ} [Fact p.Prime] :
    (Polynomial.X * ∏ j ∈ Finset.univ.erase (0 : ZMod p), artinSchreierPoly p j ≠
      (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X])) ∧
    (3 ≤ p →
      (Polynomial.X ^ p - Polynomial.X) *
          ∏ j ∈ Finset.univ.erase (0 : ZMod p), artinSchreierPoly p j ≠
        (Polynomial.X ^ (p ^ p) - Polynomial.X : (ZMod p)[X])) := by
  have hp : Nat.Prime p := Fact.out
  let U : Finset (ZMod p) := Finset.univ.erase 0
  have hU_card : U.card = p - 1 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hAS_mon_deg : ∀ j ∈ U,
      (artinSchreierPoly p j).Monic ∧ (artinSchreierPoly p j).natDegree = p :=
    fun j _ => artinSchreierPoly_monic_and_deg hp j
  have hprod_mon : (∏ j ∈ U, artinSchreierPoly p j).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j hj => (hAS_mon_deg j hj).1
  have hprod_deg : (∏ j ∈ U, artinSchreierPoly p j).natDegree = (p - 1) * p := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j hj => (hAS_mon_deg j hj).1)]
    rw [Finset.sum_congr rfl (fun j hj => (hAS_mon_deg j hj).2), Finset.sum_const, smul_eq_mul,
      hU_card]
  obtain ⟨_, hf_deg⟩ :=
    monic_and_natDegree_X_pow_sub_X (ZMod p) (one_lt_pow₀ hp.one_lt hp.ne_zero)
  refine ⟨?_, ?_⟩
  · intro heq
    have hd := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hprod_mon.ne_zero, Polynomial.natDegree_X,
      hprod_deg, hf_deg] at hd
    rcases eq_or_lt_of_le hp.two_le with rfl | hp_gt2
    · norm_num at hd
    · have hp2_lt : p ^ 2 < p ^ p := Nat.pow_lt_pow_right hp.one_lt hp_gt2
      have h1 : (p - 1) * p + p = p ^ 2 := by
        calc (p - 1) * p + p = (p - 1) * p + 1 * p := by rw [one_mul]
          _ = (p - 1 + 1) * p := (Nat.add_mul _ _ _).symm
          _ = p ^ 2 := by rw [Nat.sub_add_cancel hp.pos, sq]
      omega
  · intro hp3 heq
    obtain ⟨hXp_mon, hXp_deg⟩ := monic_and_natDegree_X_pow_sub_X (ZMod p) hp.one_lt
    have hd := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_mul hXp_mon.ne_zero hprod_mon.ne_zero, hXp_deg, hprod_deg, hf_deg] at hd
    have hsum_p2 : p + (p - 1) * p = p ^ 2 := by
      calc p + (p - 1) * p = 1 * p + (p - 1) * p := by rw [one_mul]
        _ = (1 + (p - 1)) * p := (Nat.add_mul _ _ _).symm
        _ = p ^ 2 := by rw [Nat.add_sub_of_le hp.pos, sq]
    have hp2_lt : p ^ 2 < p ^ p := Nat.pow_lt_pow_right hp.one_lt (by omega : 2 < p)
    omega

/-! ## §12.3 Some abelian group theory (printed pp. 103–105, PDF pp. 111–113) -/

/-- Standard `s`-element generation predicate for an additive group `(G, +)` (§12.3, printed p. 103 /
PDF p. 111, matching line 26 of `Theorem 12.2`'s proof: *"generated by `s` elements: that is,
generated by at most `s` elements"*): there exist `s` elements `g₁, ..., g_s ∈ G` whose additive
closure is `G`. -/
def IsAddGeneratedBy (G : Type*) [AddGroup G] (s : ℕ) : Prop :=
  ∃ g : Fin s → G, AddSubgroup.closure (Set.range g) = ⊤

/-- Garling's §1.1 (printed p. 7 / PDF p. 15) non-empty generating-set predicate for `(G, +)`:
there exists a **non-empty** finite subset `A ⊆ G` with `|A| ≤ s` generating `G`. Note that
`IsGarlingAddGeneratedBy G s ↔ IsAddGeneratedBy G s` for every `s ≥ 1`, whereas
`IsGarlingAddGeneratedBy G 0` is always `False` even when `G` is trivial. -/
def IsGarlingAddGeneratedBy (G : Type*) [AddGroup G] (s : ℕ) : Prop :=
  ∃ A : Set G, A.Nonempty ∧ A.Finite ∧ A.ncard ≤ s ∧ AddSubgroup.closure A = ⊤

theorem not_isGarlingAddGeneratedBy_zero (G : Type*) [AddGroup G] :
    ¬ IsGarlingAddGeneratedBy G 0 := by
  rintro ⟨A, hne, hfin, hle, _⟩
  have hpos : 0 < A.ncard := (Set.ncard_pos hfin).mpr hne
  omega

theorem isGarlingAddGeneratedBy_iff_of_pos {G : Type*} [AddGroup G] {s : ℕ} (hs : 0 < s) :
    IsGarlingAddGeneratedBy G s ↔ IsAddGeneratedBy G s := by
  classical
  constructor
  · rintro ⟨A, ⟨a₀, ha₀⟩, hfin, hle, hcl⟩
    let F := hfin.toFinset
    have hF_card : F.card = A.ncard := by
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    let e : Fin F.card ≃ F := F.equivFin.symm
    let g : Fin s → G := fun i =>
      if h : (i : ℕ) < F.card then (e ⟨i, h⟩ : G) else a₀
    refine ⟨g, ?_⟩
    have hrange : Set.range g = A := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        dsimp [g]
        split_ifs with h
        · exact (Set.Finite.mem_toFinset hfin).mp (e ⟨i, h⟩).2
        · exact ha₀
      · intro hx
        have hxF : x ∈ F := (Set.Finite.mem_toFinset hfin).mpr hx
        let j : Fin F.card := e.symm ⟨x, hxF⟩
        have hj_lt : (j : ℕ) < s := lt_of_lt_of_le j.2 (hF_card ▸ hle)
        refine ⟨⟨j, hj_lt⟩, ?_⟩
        have hej : e ⟨(j : ℕ), j.2⟩ = ⟨x, hxF⟩ := e.apply_symm_apply ⟨x, hxF⟩
        simp [g, j.2, hej]
    rw [hrange, hcl]
  · rintro ⟨g, hcl⟩
    refine ⟨Set.range g, ⟨g ⟨0, hs⟩, ⟨⟨0, hs⟩, rfl⟩⟩, Set.finite_range g, ?_, hcl⟩
    have himg : Set.range g = g '' (Set.univ : Set (Fin s)) := Set.image_univ.symm
    rw [himg]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)

theorem addGroup_fg_iff_exists_isAddGeneratedBy (G : Type*) [AddGroup G] :
    AddGroup.FG G ↔ ∃ s : ℕ, IsAddGeneratedBy G s := by
  classical
  rw [AddGroup.fg_iff]
  constructor
  · rintro ⟨S, hcl, hfin⟩
    let F := hfin.toFinset
    let e : Fin F.card ≃ F := F.equivFin.symm
    refine ⟨F.card, fun i => (e i : G), ?_⟩
    have hrange : Set.range (fun i : Fin F.card => (e i : G)) = S := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (Set.Finite.mem_toFinset hfin).mp (e i).2
      · intro hx
        have hxF : x ∈ F := (Set.Finite.mem_toFinset hfin).mpr hx
        exact ⟨e.symm ⟨x, hxF⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hxF⟩)⟩
    rw [hrange, hcl]
  · rintro ⟨s, g, hcl⟩
    exact ⟨Set.range g, hcl, Set.finite_range g⟩

private theorem isAddGeneratedBy_of_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (hf : Function.Surjective f) {s : ℕ} (hg : IsAddGeneratedBy G s) :
    IsAddGeneratedBy H s := by
  rcases hg with ⟨g, hcl⟩
  refine ⟨f ∘ g, ?_⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  let K : AddSubgroup G := (AddSubgroup.closure (Set.range (f ∘ g))).comap f
  have hle : AddSubgroup.closure (Set.range g) ≤ K := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  exact hle (hcl ▸ AddSubgroup.mem_top x)

private theorem isAddGeneratedBy_congr {G H : Type*} [AddGroup G] [AddGroup H]
    (e : G ≃+ H) (s : ℕ) : IsAddGeneratedBy G s ↔ IsAddGeneratedBy H s :=
  ⟨isAddGeneratedBy_of_surjective e.toAddMonoidHom e.surjective,
   isAddGeneratedBy_of_surjective e.symm.toAddMonoidHom e.symm.surjective⟩

/-- Lower bound on generator count via a surjective homomorphism onto `(ℤ_p)^s` (`p` prime):
if `G` surjects onto `Fin s → ZMod p`, then `G` cannot be generated by `t` elements for any `t < s`.
-/
private theorem not_isAddGeneratedBy_of_surjective_zmod_pow {G : Type*} [AddCommGroup G]
    {p s t : ℕ} (hp : Nat.Prime p) (hts : t < s)
    (ψ : G →+ (Fin s → ZMod p)) (hψ : Function.Surjective ψ) :
    ¬ IsAddGeneratedBy G t := by
  classical
  have _ : Fact p.Prime := ⟨hp⟩
  intro hgen
  obtain ⟨h, hh⟩ := isAddGeneratedBy_of_surjective ψ hψ hgen
  let Φ : (Fin t → ZMod p) → (Fin s → ZMod p) := fun c => ∑ i : Fin t, c i • h i
  let S : AddSubgroup (Fin s → ZMod p) :=
    { carrier := Set.range Φ
      zero_mem' := ⟨0, by simp [Φ]⟩
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [Φ, add_smul, Finset.sum_add_distrib]⟩
      neg_mem' := by
        rintro _ ⟨c, rfl⟩
        exact ⟨-c, by simp [Φ, neg_smul, Finset.sum_neg_distrib]⟩ }
  have hle : AddSubgroup.closure (Set.range h) ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (1 : ZMod p), ?_⟩
    dsimp [Φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hΦ_surj : Function.Surjective Φ := fun v =>
    hle (hh ▸ AddSubgroup.mem_top v)
  have hcard_le := Fintype.card_le_of_surjective Φ hΦ_surj
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard_le
  exact not_lt_of_ge hcard_le (Nat.pow_lt_pow_right hp.one_lt hts)

/-- Standard `s`-element generation of a product of `s` cyclic additive groups. -/
private theorem isAddGeneratedBy_pi_of_zmultiples {s : ℕ} (M : Fin s → Type*)
    [∀ i, AddCommGroup (M i)] (u : ∀ i, M i)
    (hu : ∀ i, AddSubgroup.zmultiples (u i) = ⊤) :
    IsAddGeneratedBy ((i : Fin s) → M i) s := by
  classical
  let g : Fin s → ((i : Fin s) → M i) := fun i => Pi.single i (u i)
  refine ⟨g, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx_sum : x = ∑ i : Fin s, Pi.single i (x i) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact Pi.single_eq_of_ne hij.symm _
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hx_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have hxi : x i ∈ AddSubgroup.zmultiples (u i) := hu i ▸ AddSubgroup.mem_top (x i)
  rcases AddSubgroup.mem_zmultiples_iff.mp hxi with ⟨k, hk⟩
  rw [← hk]
  have hsingle_smul : Pi.single i (k • u i) = k • g i := by
    ext j
    by_cases hij : j = i
    · subst j; simp [g]
    · simp [g, Pi.single_eq_of_ne hij]
  rw [hsingle_smul]
  have hgi : g i ∈ AddSubgroup.closure (Set.range g) := AddSubgroup.subset_closure ⟨i, rfl⟩
  exact AddSubgroup.zsmul_mem _ hgi k

/-- Helper lifting integer multiplication `x ↦ c * x` to `Zn m →+ Zn n` when `n ∣ c * m`. -/
private def znLinearLift (m n : ℕ) (c : ℤ) (hdvd : (n : ℤ) ∣ c * (m : ℤ)) : Zn m →+ Zn n :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (n : ℤ))).comp (AddMonoidHom.mulLeft c))
    (by
      intro x hx
      rcases AddSubgroup.mem_zmultiples_iff.mp hx with ⟨k, rfl⟩
      rcases hdvd with ⟨q, hq⟩
      change QuotientAddGroup.mk (c * (k • (m : ℤ))) = (0 : Zn n)
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
      refine ⟨k * q, ?_⟩
      simp only [zsmul_eq_mul]
      calc k * q * (n : ℤ) = k * ((n : ℤ) * q) := by ring
        _ = k * (c * (m : ℤ)) := by rw [← hq]
        _ = c * (k * (m : ℤ)) := by ring)

/-- Explicit unimodular Bézout isomorphism `ℤ_a × ℤ_b ≃+ ℤ_d × ℤ_{ab/d}` (`d = gcd(a, b)`) for
positive integers `a, b` (`Exercise 12.5` & invariant-factor conversion for `Theorem 12.2`). -/
noncomputable def znProdAddEquivGcdLcm {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    (Zn a × Zn b) ≃+ (Zn (Nat.gcd a b) × Zn ((a * b) / Nat.gcd a b)) := by
  let d := Nat.gcd a b
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left b ha
  let a' := a / d
  let b' := b / d
  let L := (a * b) / d
  have ha_eq : d * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb_eq : d * b' = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hL_eq1 : L = a * b' := Nat.mul_div_assoc a (Nat.gcd_dvd_right a b)
  have hL_eq2 : L = b * a' := by
    dsimp [L, a']
    rw [Nat.mul_comm a b, ← Nat.mul_div_assoc b (Nat.gcd_dvd_left a b)]
  have hcop : Nat.gcd a' b' = 1 := by
    dsimp [a', b', d]
    rw [Nat.gcd_div (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b), Nat.div_self hd_pos]
  let u : ℤ := Int.gcdA (a' : ℤ) (b' : ℤ)
  let v : ℤ := Int.gcdB (a' : ℤ) (b' : ℤ)
  have hbez : (a' : ℤ) * u + (b' : ℤ) * v = 1 := by
    have h1 := (Int.gcd_eq_gcd_ab (a' : ℤ) (b' : ℤ)).symm
    rw [Int.gcd_natCast_natCast, hcop, Nat.cast_one] at h1
    exact h1
  have ha_int : (d : ℤ) * (a' : ℤ) = (a : ℤ) := by exact_mod_cast ha_eq
  have hb_int : (d : ℤ) * (b' : ℤ) = (b : ℤ) := by exact_mod_cast hb_eq
  have hL1_int : (L : ℤ) = (a : ℤ) * (b' : ℤ) := by exact_mod_cast hL_eq1
  have hL2_int : (L : ℤ) = (b : ℤ) * (a' : ℤ) := by exact_mod_cast hL_eq2
  let φ₁ : Zn a →+ Zn d :=
    znLinearLift a d u ⟨u * (a' : ℤ), by linear_combination -u * ha_int⟩
  let φ₂ : Zn b →+ Zn d :=
    znLinearLift b d v ⟨v * (b' : ℤ), by linear_combination -v * hb_int⟩
  let φ₃ : Zn a →+ Zn L :=
    znLinearLift a L (-(b' : ℤ)) ⟨-1, by linear_combination hL1_int⟩
  let φ₄ : Zn b →+ Zn L :=
    znLinearLift b L (a' : ℤ) ⟨1, by linear_combination -hL2_int⟩
  let ψ₁ : Zn d →+ Zn a :=
    znLinearLift d a (a' : ℤ) ⟨1, by linear_combination ha_int⟩
  let ψ₂ : Zn L →+ Zn a :=
    znLinearLift L a (-v) ⟨-v * (b' : ℤ), by linear_combination -v * hL1_int⟩
  let ψ₃ : Zn d →+ Zn b :=
    znLinearLift d b (b' : ℤ) ⟨1, by linear_combination hb_int⟩
  let ψ₄ : Zn L →+ Zn b :=
    znLinearLift L b u ⟨u * (a' : ℤ), by linear_combination u * hL2_int⟩
  let F : Zn a × Zn b →+ Zn d × Zn L := (φ₁.coprod φ₂).prod (φ₃.coprod φ₄)
  let G : Zn d × Zn L →+ Zn a × Zn b := (ψ₁.coprod ψ₂).prod (ψ₃.coprod ψ₄)
  refine
    { toFun := F
      invFun := G
      left_inv := ?_
      right_inv := ?_
      map_add' := F.map_add }
  · rintro ⟨p, q⟩
    induction p using Quotient.inductionOn with | h x =>
    induction q using Quotient.inductionOn with | h y =>
    apply Prod.ext
    · change QuotientAddGroup.mk ((a' : ℤ) * (u * x + v * y) + (-v) * (-(b' : ℤ) * x + (a' : ℤ) * y)) =
        (QuotientAddGroup.mk x : Zn a)
      exact congrArg QuotientAddGroup.mk (by linear_combination x * hbez)
    · change QuotientAddGroup.mk ((b' : ℤ) * (u * x + v * y) + u * (-(b' : ℤ) * x + (a' : ℤ) * y)) =
        (QuotientAddGroup.mk y : Zn b)
      exact congrArg QuotientAddGroup.mk (by linear_combination y * hbez)
  · rintro ⟨r, s⟩
    induction r using Quotient.inductionOn with | h z =>
    induction s using Quotient.inductionOn with | h w =>
    apply Prod.ext
    · change QuotientAddGroup.mk (u * ((a' : ℤ) * z + (-v) * w) + v * ((b' : ℤ) * z + u * w)) =
        (QuotientAddGroup.mk z : Zn d)
      exact congrArg QuotientAddGroup.mk (by linear_combination z * hbez)
    · change QuotientAddGroup.mk (-(b' : ℤ) * ((a' : ℤ) * z + (-v) * w) + (a' : ℤ) * ((b' : ℤ) * z + u * w)) =
        (QuotientAddGroup.mk w : Zn L)
      exact congrArg QuotientAddGroup.mk (by linear_combination w * hbez)

private def znCongr {a b : ℕ} (h : a = b) : Zn a ≃+ Zn b :=
  h ▸ AddEquiv.refl (Zn a)

private def piFinSuccSnocAddEquiv {u : ℕ} (A : Fin (u + 1) → Type*)
    [∀ i, AddCommGroup (A i)] :
    ((i : Fin (u + 1)) → A i) ≃+ (((i : Fin u) → A i.castSucc) × A (Fin.last u)) where
  toFun f := (fun i => f i.castSucc, f (Fin.last u))
  invFun p := Fin.snoc p.1 p.2
  left_inv f := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    rcases p with ⟨g, x⟩
    apply Prod.ext
    · ext i; simp
    · simp
  map_add' _ _ := rfl

private theorem zn_one_subsingleton : Subsingleton (Zn 1) := by
  refine ⟨fun x y => ?_⟩
  have hz : ∀ a : Zn 1, a = 0 := by
    intro a
    induction a using Quotient.inductionOn with | h z =>
    change QuotientAddGroup.mk z = (0 : Zn 1)
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    exact ⟨z, by simp⟩
  rw [hz x, hz y]

/-- Inductive invariant-factor insertion step: merges `Zn m` (`1 ≤ m`) into an ordered invariant-factor
chain `d₀ ∣ d₁ ∣ ⋯ ∣ d_{t-1}` (`1 < d_j`), preserving divisibility into any common multiple `M`. -/
private theorem invariantFactors_insert :
    ∀ (t : ℕ) (d : Fin t → ℕ),
      (∀ j, 1 < d j) →
      (∀ j k : Fin t, j < k → d j ∣ d k) →
      ∀ (m : ℕ), 1 ≤ m →
        ∃ (s : ℕ) (d' : Fin s → ℕ),
          (∀ j, 1 < d' j) ∧
          (∀ j k : Fin s, j < k → d' j ∣ d' k) ∧
          (∀ M : ℕ, (∀ j, d j ∣ M) → m ∣ M → ∀ j, d' j ∣ M) ∧
          Nonempty ((((j : Fin t) → Zn (d j)) × Zn m) ≃+ ((j : Fin s) → Zn (d' j))) := by
  intro t
  induction t with
  | zero =>
    intro d _ _ m hm
    rcases eq_or_lt_of_le hm with rfl | hm_gt1
    · refine ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
        fun _ _ _ j => j.elim0, ⟨?_⟩⟩
      exact
        { toFun := fun (_ : ((j : Fin 0) → Zn (d j)) × Zn 1) (k : Fin 0) => k.elim0
          invFun := fun _ => (fun j => j.elim0, 0)
          left_inv := fun ⟨f, z⟩ => Prod.ext (funext fun j => j.elim0) (zn_one_subsingleton.elim 0 z)
          right_inv := fun f => funext fun k => k.elim0
          map_add' := fun _ _ => funext fun k => k.elim0 }
    · refine ⟨1, fun _ => m, fun _ => hm_gt1, fun _ _ _ => dvd_refl m,
        fun _ _ hmM _ => hmM, ⟨?_⟩⟩
      exact
        { toFun := fun p _ => p.2
          invFun := fun f => (fun j => j.elim0, f 0)
          left_inv := fun ⟨g, x⟩ => Prod.ext (funext fun j => j.elim0) rfl
          right_inv := fun f => funext fun i => by rw [Subsingleton.elim i 0]
          map_add' := fun _ _ => rfl }
  | succ u ih =>
    intro d hd_gt1 hd_dvd m hm
    rcases eq_or_lt_of_le hm with rfl | hm_gt1
    · refine ⟨u + 1, d, hd_gt1, hd_dvd, fun M hdM _ => hdM, ⟨?_⟩⟩
      exact
        { toFun := fun p : ((j : Fin (u + 1)) → Zn (d j)) × Zn 1 => p.1
          invFun := fun f => (f, 0)
          left_inv := fun ⟨f, z⟩ => Prod.ext rfl (zn_one_subsingleton.elim 0 z)
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl }
    · let dInit : Fin u → ℕ := fun i => d i.castSucc
      let du : ℕ := d (Fin.last u)
      have hdu_gt1 : 1 < du := hd_gt1 (Fin.last u)
      let g : ℕ := Nat.gcd du m
      let L : ℕ := (du * m) / g
      have hg_pos : 1 ≤ g := Nat.gcd_pos_of_pos_left m (by omega)
      have hL_lcm : L = Nat.lcm du m := by
        have hlcm : g * Nat.lcm du m = du * m := Nat.gcd_mul_lcm du m
        exact Nat.div_eq_of_eq_mul_right hg_pos hlcm.symm
      have hdu_dvd_L : du ∣ L := hL_lcm ▸ Nat.dvd_lcm_left du m
      have hL_gt1 : 1 < L := lt_of_lt_of_le hdu_gt1
        (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega) |> fun h => hL_lcm ▸ h) hdu_dvd_L)
      obtain ⟨s₀, d₀, hd₀_gt1, hd₀_dvd, hd₀_M, ⟨e₀⟩⟩ :=
        ih dInit (fun i => hd_gt1 i.castSucc)
          (fun i j hij => hd_dvd i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij))
          g hg_pos
      let d' : Fin (s₀ + 1) → ℕ := Fin.lastCases L d₀
      have hd'_cast : ∀ i : Fin s₀, d' i.castSucc = d₀ i := fun i => by
        simp [d']
      have hd'_last : d' (Fin.last s₀) = L := by
        simp [d']
      have hd₀_dvd_L : ∀ i : Fin s₀, d₀ i ∣ L := by
        refine hd₀_M L (fun i => ?_) (dvd_trans (Nat.gcd_dvd_left du m) hdu_dvd_L)
        exact dvd_trans (hd_dvd i.castSucc (Fin.last u) (Fin.castSucc_lt_last i)) hdu_dvd_L
      refine ⟨s₀ + 1, d', ?_, ?_, ?_, ⟨?_⟩⟩
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [hd'_last]; exact hL_gt1
        · rw [hd'_cast]; exact hd₀_gt1 i
      · intro j k
        refine Fin.lastCases ?_ (fun k' => ?_) k
        · refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hjk; exact (lt_irrefl _ hjk).elim
          · intro _; rw [hd'_cast, hd'_last]; exact hd₀_dvd_L j'
        · refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hjk; exact (not_lt_of_ge (Fin.le_last _) hjk).elim
          · intro hjk; rw [hd'_cast, hd'_cast]
            exact hd₀_dvd j' k' (Fin.castSucc_lt_castSucc_iff.mp hjk)
      · intro M hdM hmM j
        have hL_dvd_M : L ∣ M := hL_lcm ▸ Nat.lcm_dvd (hdM (Fin.last u)) hmM
        have hg_dvd_M : g ∣ M := dvd_trans (Nat.gcd_dvd_left du m) (hdM (Fin.last u))
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [hd'_last]; exact hL_dvd_M
        · rw [hd'_cast]
          exact hd₀_M M (fun k => hdM k.castSucc) hg_dvd_M i
      · let eSplit := piFinSuccSnocAddEquiv (fun j : Fin (u + 1) => Zn (d j))
        let ePair : Zn du × Zn m ≃+ Zn g × Zn L := znProdAddEquivGcdLcm (by omega) (by omega)
        let eSnoc : (((i : Fin s₀) → Zn (d₀ i)) × Zn L) ≃+ ((j : Fin (s₀ + 1)) → Zn (d' j)) :=
          ((AddEquiv.piCongrRight fun i => znCongr (hd'_cast i).symm).prodCongr
            (znCongr hd'_last.symm)).trans
            (piFinSuccSnocAddEquiv (fun j : Fin (s₀ + 1) => Zn (d' j))).symm
        exact (((eSplit.prodCongr (AddEquiv.refl (Zn m))).trans
          AddEquiv.prodAssoc).trans
          ((AddEquiv.refl _).prodCongr ePair)).trans
          ((AddEquiv.prodAssoc.symm.trans
            (e₀.prodCongr (AddEquiv.refl (Zn L)))).trans eSnoc)

/-- Converts any finite product `((i : Fin r) → Zn (n i))` (`1 < n i`) into invariant factors
`((j : Fin s) → Zn (d j))` (`1 < d j`, `d j ∣ d k` for `j < k`). -/
private theorem invariantFactors_of_pi :
    ∀ (r : ℕ) (n : Fin r → ℕ),
      (∀ i, 1 < n i) →
        ∃ (s : ℕ) (d : Fin s → ℕ),
          (∀ j, 1 < d j) ∧
          (∀ j k : Fin s, j < k → d j ∣ d k) ∧
          Nonempty (((i : Fin r) → Zn (n i)) ≃+ ((j : Fin s) → Zn (d j))) := by
  intro r
  induction r with
  | zero =>
    intro n _
    refine ⟨0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, ⟨?_⟩⟩
    exact
      { toFun := fun (_ : (i : Fin 0) → Zn (n i)) (j : Fin 0) => j.elim0
        invFun := fun (_ : (j : Fin 0) → Zn j.elim0) (i : Fin 0) => i.elim0
        left_inv := fun _ => funext fun i => i.elim0
        right_inv := fun _ => funext fun j => j.elim0
        map_add' := fun _ _ => funext fun j => j.elim0 }
  | succ u ih =>
    intro n hn_gt1
    obtain ⟨t, d₀, hd₀_gt1, hd₀_dvd, ⟨e₀⟩⟩ := ih (fun i => n i.castSucc) (fun i => hn_gt1 i.castSucc)
    obtain ⟨s, d, hd_gt1, hd_dvd, _, ⟨eIns⟩⟩ :=
      invariantFactors_insert t d₀ hd₀_gt1 hd₀_dvd (n (Fin.last u)) (le_of_lt (hn_gt1 (Fin.last u)))
    refine ⟨s, d, hd_gt1, hd_dvd, ⟨?_⟩⟩
    exact ((piFinSuccSnocAddEquiv (fun i : Fin (u + 1) => Zn (n i))).trans
      (e₀.prodCongr (AddEquiv.refl _))).trans eIns

private def reindexPiAddEquiv {α β : Type*} (e : α ≃ β) (M : β → Type*)
    [∀ b, AddCommGroup (M b)] :
    ((b : β) → M b) ≃+ ((a : α) → M (e a)) where
  toFun f a := f (e a)
  invFun g b := Eq.mp (congrArg M (e.apply_symm_apply b)) (g (e.symm b))
  left_inv f := by
    ext b
    have aux : ∀ {b' : β} (h : b' = b), Eq.mp (congrArg M h) (f b') = f b := by
      rintro _ rfl; rfl
    exact aux (e.apply_symm_apply b)
  right_inv g := by
    ext a
    have aux : ∀ {a' : α} (_ : a' = a) (he : e a' = e a),
        Eq.mp (congrArg M he) (g a') = g a := by
      rintro _ rfl he; cases he; rfl
    exact aux (e.symm_apply_apply a) (e.apply_symm_apply (e a))
  map_add' _ _ := rfl

private theorem zn_zsmul_mk (m : ℕ) (k z : ℤ) :
    k • (QuotientAddGroup.mk z : Zn m) = QuotientAddGroup.mk (k * z) := by
  have h := map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (m : ℤ))) k z
  rw [zsmul_eq_mul] at h
  exact h.symm

private theorem zn_nsmul_mk (m k : ℕ) (z : ℤ) :
    k • (QuotientAddGroup.mk z : Zn m) = QuotientAddGroup.mk ((k : ℤ) * z) := by
  have h := map_nsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (m : ℤ))) k z
  rw [nsmul_eq_mul] at h
  exact h.symm

/-- **Theorem 12.2** (§12.3, printed p. 103 / PDF p. 111, proof pp. 103–104 / PDF pp. 111–112):
*"Suppose that `(G, +)` is a finite abelian group. `G` is isomorphic to a product of cyclic groups:
`G ≅ ℤ_{d_1} × ⋯ × ℤ_{d_s}`. Further the isomorphism can be chosen so that `d_j ∣ d_k` for
`1 ≤ j < k ≤ s`. The number `s` is characterized by the property that `G` is generated by `s`
elements, but it is not generated by `s - 1` elements."*

Stated unconditionally for all finite abelian groups `(G, +)` (`|G| ≥ 1`): at `|G| = 1`, `s = 0`
(the empty product `Fin 0 → _`), where both `"not generated by fewer than s elements"` (`∀ t < s`,
matching p. 103, l. 27) and integer-typed `s - 1 : ℤ` (`¬ ∃ t : ℕ, (t : ℤ) = (s : ℤ) - 1 ∧ ...`)
hold; see `theorem_12_2_nontrivial` and `theorem_12_2_garling_nonempty` for the `ℕ`-subtraction
`s - 1` companions. -/
theorem theorem_12_2 (G : Type u) [AddCommGroup G] [Finite G] :
    ∃ (s : ℕ) (d : Fin s → ℕ),
      (∀ j, 1 < d j) ∧
      (∀ j k : Fin s, j < k → d j ∣ d k) ∧
      Nonempty (G ≃+ ((j : Fin s) → Zn (d j))) ∧
      IsAddGeneratedBy G s ∧
      (∀ t < s, ¬ IsAddGeneratedBy G t) ∧
      (¬ ∃ t : ℕ, (t : ℤ) = (s : ℤ) - 1 ∧ IsAddGeneratedBy G t) ∧
      (∀ s' : ℕ, (IsAddGeneratedBy G s' ∧ ∀ t < s', ¬ IsAddGeneratedBy G t) ↔ s' = s) := by
  classical
  obtain ⟨ι, hι, n₀, hn₀_gt1, ⟨eDS⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let _ : Fintype ι := hι
  let r := Fintype.card ι
  let eqvFin : Fin r ≃ ι := (Fintype.equivFin ι).symm
  let n : Fin r → ℕ := fun i => n₀ (eqvFin i)
  have ePi : G ≃+ ((i : Fin r) → Zn (n i)) :=
    ((eDS.trans (DirectSum.addEquivProd _)).trans
      (reindexPiAddEquiv eqvFin (fun k : ι => ZMod (n₀ k)))).trans
      (AddEquiv.piCongrRight fun i => (znAddEquivZMod (n i)).symm)
  obtain ⟨s, d, hd_gt1, hd_dvd, ⟨eInv⟩⟩ := invariantFactors_of_pi r n (fun i => hn₀_gt1 (eqvFin i))
  let eG : G ≃+ ((j : Fin s) → Zn (d j)) := ePi.trans eInv
  have hgen_s : IsAddGeneratedBy G s := by
    rw [isAddGeneratedBy_congr eG s]
    refine isAddGeneratedBy_pi_of_zmultiples (fun j => Zn (d j))
      (fun _ => QuotientAddGroup.mk 1) fun j => ?_
    rw [eq_top_iff]
    intro x _
    induction x using Quotient.inductionOn with | h z =>
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨z, (zn_zsmul_mk (d j) z 1).trans (congrArg QuotientAddGroup.mk (mul_one z))⟩
  have hnot_lt : ∀ t < s, ¬ IsAddGeneratedBy G t := by
    intro t hts
    have hs_pos : 0 < s := by omega
    let j₀ : Fin s := ⟨0, hs_pos⟩
    let p : ℕ := (d j₀).minFac
    have hp_prime : Nat.Prime p := Nat.minFac_prime (ne_of_gt (hd_gt1 j₀))
    have _ : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd_all : ∀ j : Fin s, p ∣ d j := by
      intro j
      have hp_j0 : p ∣ d j₀ := Nat.minFac_dvd (d j₀)
      rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
      · have hj : j₀ = j := Fin.ext hj0.symm
        exact hj ▸ hp_j0
      · exact dvd_trans hp_j0 (hd_dvd j₀ j (Fin.lt_def.mpr hjpos))
    let proj : ∀ j : Fin s, Zn (d j) →+ ZMod p := fun j =>
      QuotientAddGroup.lift _ (Int.castAddHom (ZMod p)) (by
        intro z hz
        rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨k, rfl⟩
        rcases hp_dvd_all j with ⟨q, hq⟩
        change ((k • (d j : ℤ) : ℤ) : ZMod p) = 0
        rw [zsmul_eq_mul, hq, Nat.cast_mul, ← mul_assoc, mul_comm _ (p : ℤ), mul_assoc,
          Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul])
    have hproj_surj : ∀ j : Fin s, Function.Surjective (proj j) := by
      intro j a
      refine ⟨QuotientAddGroup.mk (a.val : ℤ), ?_⟩
      change ((a.val : ℤ) : ZMod p) = a
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    let π : ((j : Fin s) → Zn (d j)) →+ (Fin s → ZMod p) :=
      { toFun := fun x j => proj j (x j)
        map_zero' := by ext j; exact (proj j).map_zero
        map_add' := fun x y => by ext j; exact (proj j).map_add (x j) (y j) }
    have hπ_surj : Function.Surjective π := by
      intro v
      refine ⟨fun j => Classical.choose (hproj_surj j (v j)), ?_⟩
      ext j
      exact Classical.choose_spec (hproj_surj j (v j))
    exact not_isAddGeneratedBy_of_surjective_zmod_pow hp_prime hts
      (π.comp eG.toAddMonoidHom) (hπ_surj.comp eG.surjective)
  have hnot_int_pred : ¬ ∃ t : ℕ, (t : ℤ) = (s : ℤ) - 1 ∧ IsAddGeneratedBy G t := by
    rintro ⟨t, ht_eq, ht_gen⟩
    exact hnot_lt t (by omega) ht_gen
  have huniq : ∀ s' : ℕ, (IsAddGeneratedBy G s' ∧ ∀ t < s', ¬ IsAddGeneratedBy G t) ↔ s' = s := by
    intro s'
    constructor
    · rintro ⟨hgen', hnot'⟩
      rcases lt_trichotomy s' s with hlt | rfl | hgt
      · exact (hnot_lt s' hlt hgen').elim
      · rfl
      · exact (hnot' s hgt hgen_s).elim
    · rintro rfl
      exact ⟨hgen_s, hnot_lt⟩
  exact ⟨s, d, hd_gt1, hd_dvd, ⟨eG⟩, hgen_s, hnot_lt, hnot_int_pred, huniq⟩

/-- Nontrivial companion to **Theorem 12.2** (§12.3, p. 103): when `|G| > 1` (`[Nontrivial G]`),
`0 < s` and `¬ IsAddGeneratedBy G (s - 1)` holds directly under `ℕ` subtraction. -/
theorem theorem_12_2_nontrivial (G : Type u) [AddCommGroup G] [Finite G] [Nontrivial G] :
    ∃ (s : ℕ) (d : Fin s → ℕ),
      0 < s ∧
      (∀ j, 1 < d j) ∧
      (∀ j k : Fin s, j < k → d j ∣ d k) ∧
      Nonempty (G ≃+ ((j : Fin s) → Zn (d j))) ∧
      IsAddGeneratedBy G s ∧
      ¬ IsAddGeneratedBy G (s - 1) := by
  obtain ⟨s, d, hd_gt1, hd_dvd, ⟨eG⟩, hgen, hnot_lt, _, _⟩ := theorem_12_2 G
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exfalso
      obtain ⟨x, y, hxy⟩ := exists_pair_ne G
      exact hxy (eG.injective (funext fun j => j.elim0))
    · exact hpos
  exact ⟨s, d, hs_pos, hd_gt1, hd_dvd, ⟨eG⟩, hgen, hnot_lt (s - 1) (by omega)⟩

/-- Companion to **Theorem 12.2** under Garling's §1.1 (p. 7) non-empty generating-set predicate
`IsGarlingAddGeneratedBy`: holds literally with `ℕ` subtraction `s - 1` for **every** finite abelian
group `G` (including `|G| = 1`, where `s = 1, d_1 = 1` and `IsGarlingAddGeneratedBy G 0` is false). -/
theorem theorem_12_2_garling_nonempty (G : Type u) [AddCommGroup G] [Finite G] :
    ∃ (s : ℕ) (d : Fin s → ℕ),
      0 < s ∧
      (∀ j, 0 < d j) ∧
      (∀ j k : Fin s, j < k → d j ∣ d k) ∧
      Nonempty (G ≃+ ((j : Fin s) → Zn (d j))) ∧
      IsGarlingAddGeneratedBy G s ∧
      ¬ IsGarlingAddGeneratedBy G (s - 1) := by
  by_cases hnt : Nontrivial G
  · obtain ⟨s, d, hs_pos, hd_gt1, hd_dvd, ⟨eG⟩, hgen, hnot_pred⟩ := theorem_12_2_nontrivial G
    refine ⟨s, d, hs_pos, fun j => lt_trans Nat.zero_lt_one (hd_gt1 j), hd_dvd, ⟨eG⟩,
      (isGarlingAddGeneratedBy_iff_of_pos hs_pos).mpr hgen, ?_⟩
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs_pos) with heq | hgt1
    · have hs1 : s = 1 := heq.symm
      rw [hs1, Nat.sub_self]
      exact not_isGarlingAddGeneratedBy_zero G
    · exact mt (isGarlingAddGeneratedBy_iff_of_pos (by omega)).mp hnot_pred
  · have hsub : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨1, fun _ => 1, Nat.zero_lt_one, fun _ => Nat.zero_lt_one,
      fun _ _ _ => dvd_refl 1, ⟨?_⟩, ?_, ?_⟩
    · exact
        { toFun := fun _ _ => 0
          invFun := fun _ => 0
          left_inv := fun x => hsub.elim 0 x
          right_inv := fun f => funext fun i => zn_one_subsingleton.elim 0 (f i)
          map_add' := fun _ _ => rfl }
    · refine (isGarlingAddGeneratedBy_iff_of_pos Nat.zero_lt_one).mpr ⟨fun _ => 0, ?_⟩
      rw [eq_top_iff]
      intro x _
      rw [hsub.elim x 0]
      exact AddSubgroup.zero_mem _
    · exact not_isGarlingAddGeneratedBy_zero G

/-- Garling's §12.3 prose notation `o(g)` for the order of an element `g` in a finite group `G`
(printed p. 104 / PDF p. 112). -/
noncomputable def garlingElemOrder {G : Type*} [Group G] [Finite G] (g : G) : ℕ :=
  orderOf g

/-- Garling's §12.3 prose definition of the *exponent* `e(G)` of a finite group `G`
(printed p. 104 / PDF p. 112): *"the least positive integer `k` such that `g^k = e`, for all
`g` in `G`."* -/
noncomputable def garlingExponent (G : Type*) [Group G] [Finite G] : ℕ :=
  open Classical in
  Nat.find (⟨Nat.card G, Nat.card_pos, fun g => by
    let _ := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one⟩ : ∃ k : ℕ, 0 < k ∧ ∀ g : G, g ^ k = 1)

/-- All prose deductions on `e(G)` and `o(g)` in §12.3 (printed p. 104 / PDF p. 112):
`0 < e(G)`, `∀ g, g^{e(G)} = 1`, minimality of `e(G)`, agreement with `Monoid.exponent G`,
`e(G) ≤ |G|`, `e(G) ∣ |G|`, `o(g) ≤ e(G)`, and `o(g) ∣ e(G)`. -/
theorem garlingExponent_and_elemOrder_properties (G : Type*) [Group G] [Finite G] :
    0 < garlingExponent G ∧
    (∀ g : G, g ^ garlingExponent G = 1) ∧
    (∀ k : ℕ, 0 < k → (∀ g : G, g ^ k = 1) → garlingExponent G ≤ k) ∧
    (∀ k : ℕ, (∀ g : G, g ^ k = 1) ↔ garlingExponent G ∣ k) ∧
    garlingExponent G = Monoid.exponent G ∧
    garlingExponent G ≤ Nat.card G ∧
    garlingExponent G ∣ Nat.card G ∧
    (∀ g : G, 0 < garlingElemOrder g ∧
      garlingElemOrder g ≤ garlingExponent G ∧
      garlingElemOrder g ∣ garlingExponent G) := by
  classical
  have hcard_pow : ∀ g : G, g ^ Nat.card G = 1 := fun g => by
    let _ := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hex : ∃ k : ℕ, 0 < k ∧ ∀ g : G, g ^ k = 1 := ⟨Nat.card G, Nat.card_pos, hcard_pow⟩
  have hspec : 0 < garlingExponent G ∧ ∀ g : G, g ^ garlingExponent G = 1 := by
    unfold garlingExponent
    exact Nat.find_spec hex
  have hmin : ∀ k : ℕ, 0 < k → (∀ g : G, g ^ k = 1) → garlingExponent G ≤ k := by
    intro k hk hall
    unfold garlingExponent
    exact Nat.find_min' hex ⟨hk, hall⟩
  let e := garlingExponent G
  have hdvd_iff : ∀ k : ℕ, (∀ g : G, g ^ k = 1) ↔ e ∣ k := by
    intro k
    constructor
    · intro hall
      let r := k % e
      have hdiv : e * (k / e) + r = k := Nat.div_add_mod k e
      have hr_lt : r < e := Nat.mod_lt k hspec.1
      rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
      · exact Nat.dvd_of_mod_eq_zero hr0
      · exfalso
        have hall_r : ∀ g : G, g ^ r = 1 := by
          intro g
          have hk1 : g ^ (e * (k / e) + r) = 1 := hdiv.symm ▸ hall g
          rw [pow_add, pow_mul, hspec.2 g, one_pow, one_mul] at hk1
          exact hk1
        exact not_lt_of_ge (hmin r hr_pos hall_r) hr_lt
    · rintro ⟨q, rfl⟩ g
      rw [pow_mul, hspec.2 g, one_pow]
  have hexp_eq : e = Monoid.exponent G := by
    apply Nat.dvd_antisymm
    · exact (hdvd_iff (Monoid.exponent G)).mp (fun g => Monoid.pow_exponent_eq_one g)
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one hspec.2
  have hdvd_card : e ∣ Nat.card G := (hdvd_iff (Nat.card G)).mp hcard_pow
  have hle_card : e ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd_card
  have helem : ∀ g : G, 0 < garlingElemOrder g ∧ garlingElemOrder g ≤ e ∧ garlingElemOrder g ∣ e := by
    intro g
    have hpos : 0 < garlingElemOrder g :=
      (isOfFinOrder_of_finite g).orderOf_pos
    have hdvd : garlingElemOrder g ∣ e := orderOf_dvd_of_pow_eq_one (hspec.2 g)
    exact ⟨hpos, Nat.le_of_dvd hspec.1 hdvd, hdvd⟩
  exact ⟨hspec.1, hspec.2, hmin, hdvd_iff, hexp_eq, hle_card, hdvd_card, helem⟩

private theorem multiset_lcm_mem_of_sum_le_three (m : Multiset ℕ)
    (hge2 : ∀ c ∈ m, 2 ≤ c) (hsum : m.sum ≤ 3) :
    m.lcm ∈ ({1, 2, 3} : Set ℕ) := by
  induction m using Quotient.inductionOn with | h L =>
  change L.foldr Nat.lcm 1 ∈ ({1, 2, 3} : Set ℕ)
  have hge2L : ∀ c ∈ L, 2 ≤ c := fun c hc => hge2 c hc
  have hsumL : L.sum ≤ 3 := hsum
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · have ha2 : 2 ≤ a := hge2L a (by simp)
    have ha3 : a ≤ 3 := by simpa using hsumL
    have hlcm : [a].foldr Nat.lcm 1 = a := Nat.lcm_one_right a
    rw [hlcm]
    interval_cases a <;> simp
  · exfalso
    have ha2 : 2 ≤ a := hge2L a (by simp)
    have hb2 : 2 ≤ b := hge2L b (by simp)
    simp only [List.sum_cons] at hsumL
    omega

private theorem multiset_lcm_mem_of_sum_le_six (m : Multiset ℕ)
    (hge2 : ∀ c ∈ m, 2 ≤ c) (hsum : m.sum ≤ 6) :
    m.lcm ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ) := by
  induction m using Quotient.inductionOn with | h L =>
  change L.foldr Nat.lcm 1 ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ)
  have hge2L : ∀ c ∈ L, 2 ≤ c := fun c hc => hge2 c hc
  have hsumL : L.sum ≤ 6 := hsum
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp
  · have ha2 : 2 ≤ a := hge2L a (by simp)
    have ha6 : a ≤ 6 := by simpa using hsumL
    have hlcm : [a].foldr Nat.lcm 1 = a := Nat.lcm_one_right a
    rw [hlcm]
    interval_cases a <;> simp
  · have ha2 : 2 ≤ a := hge2L a (by simp)
    have hb2 : 2 ≤ b := hge2L b (by simp)
    simp only [List.sum_cons, List.sum_nil] at hsumL
    have ha4 : a ≤ 4 := by omega
    have hb4 : b ≤ 4 := by omega
    have hlcm : [a, b].foldr Nat.lcm 1 = Nat.lcm a b := by simp [Nat.lcm_one_right]
    rw [hlcm]
    interval_cases a <;> interval_cases b <;> first | omega | decide
  · have ha2 : 2 ≤ a := hge2L a (by simp)
    have hb2 : 2 ≤ b := hge2L b (by simp)
    have hc2 : 2 ≤ c := hge2L c (by simp)
    simp only [List.sum_cons, List.sum_nil] at hsumL
    have ha_eq : a = 2 := by omega
    have hb_eq : b = 2 := by omega
    have hc_eq : c = 2 := by omega
    subst ha_eq; subst hb_eq; subst hc_eq
    have hlcm : [2, 2, 2].foldr Nat.lcm 1 = 2 := by decide
    rw [hlcm]; simp
  · exfalso
    have ha2 : 2 ≤ a := hge2L a (by simp)
    have hb2 : 2 ≤ b := hge2L b (by simp)
    have hc2 : 2 ≤ c := hge2L c (by simp)
    have hd2 : 2 ≤ d := hge2L d (by simp)
    simp only [List.sum_cons] at hsumL
    omega

private theorem orderOf_eq_of_pow_eq_one_and_lt_ne_one {G : Type*} [Group G] {g : G}
    {n : ℕ} (hn : 0 < n) (hpow : g ^ n = 1)
    (hdiv : ∀ d : ℕ, 0 < d → d < n → d ∣ n → g ^ d ≠ 1) :
    orderOf g = n := by
  have hdvd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hdvd hn
  have hle : orderOf g ≤ n := Nat.le_of_dvd hn hdvd
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  · exact (hdiv (orderOf g) hpos hlt hdvd (pow_orderOf_eq_one g)).elim

private theorem exists_sigmaN_orderOf {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ σ : SigmaN n, garlingElemOrder σ = k := by
  rcases eq_or_lt_of_le hk1 with rfl | hk2
  · exact ⟨1, by simp [garlingElemOrder]⟩
  · let f := (Fin.castLEEmb hkn).toEquivRange
    refine ⟨Equiv.Perm.extendDomainHom f (finRotate k), ?_⟩
    rw [garlingElemOrder,
      orderOf_injective (Equiv.Perm.extendDomainHom f) (Equiv.Perm.extendDomainHom_injective f),
      ← Equiv.Perm.lcm_cycleType, cycleType_finRotate_of_le hk2,
      Multiset.lcm_singleton, normalize_eq]

/-- **§12.3 Concrete Symmetric-Group Examples** (printed p. 104 / PDF p. 112):
*"Some examples: in `Σ_3`, the elements have order `1, 2` or `3`; the exponent of `Σ_3` is `6`.
In `Σ_6`, the elements have order `1, 2, 3, 4, 5` or `6`: `e(G) = 60`, and `|G| = 720`."*
Proved algebraically via `Equiv.Perm.cycleType` and `finRotate` without brute-force enumeration. -/
theorem section_12_3_sigma_examples :
    ({k : ℕ | ∃ σ : SigmaN 3, garlingElemOrder σ = k} = {1, 2, 3}) ∧
    garlingExponent (SigmaN 3) = 6 ∧
    ({k : ℕ | ∃ σ : SigmaN 6, garlingElemOrder σ = k} = {1, 2, 3, 4, 5, 6}) ∧
    garlingExponent (SigmaN 6) = 60 ∧
    Nat.card (SigmaN 6) = 720 ∧
    setOrder (SigmaN 6) = 720 := by
  have hS3_set : {k : ℕ | ∃ σ : SigmaN 3, garlingElemOrder σ = k} = {1, 2, 3} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨σ, rfl⟩
      rw [garlingElemOrder, ← Equiv.Perm.lcm_cycleType]
      exact multiset_lcm_mem_of_sum_le_three σ.cycleType
        (fun _ => Equiv.Perm.two_le_of_mem_cycleType)
        (σ.sum_cycleType_le.trans (by simp))
    · intro k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl <;> exact exists_sigmaN_orderOf (by omega) (by omega)
  have hS3_exp : garlingExponent (SigmaN 3) = 6 := by
    obtain ⟨_, _, _, hdvd_iff, _, _, _, helem⟩ :=
      garlingExponent_and_elemOrder_properties (SigmaN 3)
    apply Nat.dvd_antisymm
    · refine (hdvd_iff 6).mp fun σ => ?_
      have hmem : garlingElemOrder σ ∈ ({1, 2, 3} : Set ℕ) := hS3_set ▸ ⟨σ, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      have hdvd6 : orderOf σ ∣ 6 := by
        change garlingElemOrder σ ∣ 6
        rcases hmem with h | h | h <;> rw [h] <;> decide
      rcases hdvd6 with ⟨q, hq⟩
      rw [hq, pow_mul, pow_orderOf_eq_one, one_pow]
    · obtain ⟨σ₂, hσ₂⟩ := exists_sigmaN_orderOf (n := 3) (k := 2) (by omega) (by omega)
      obtain ⟨σ₃, hσ₃⟩ := exists_sigmaN_orderOf (n := 3) (k := 3) (by omega) (by omega)
      have h2 : 2 ∣ garlingExponent (SigmaN 3) := by have hd := (helem σ₂).2.2; rwa [hσ₂] at hd
      have h3 : 3 ∣ garlingExponent (SigmaN 3) := by have hd := (helem σ₃).2.2; rwa [hσ₃] at hd
      exact Nat.lcm_dvd h2 h3
  have hS6_set : {k : ℕ | ∃ σ : SigmaN 6, garlingElemOrder σ = k} = {1, 2, 3, 4, 5, 6} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨σ, rfl⟩
      rw [garlingElemOrder, ← Equiv.Perm.lcm_cycleType]
      exact multiset_lcm_mem_of_sum_le_six σ.cycleType
        (fun _ => Equiv.Perm.two_le_of_mem_cycleType)
        (σ.sum_cycleType_le.trans (by simp))
    · intro k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact exists_sigmaN_orderOf (by omega) (by omega)
  have hS6_exp : garlingExponent (SigmaN 6) = 60 := by
    obtain ⟨_, _, _, hdvd_iff, _, _, _, helem⟩ :=
      garlingExponent_and_elemOrder_properties (SigmaN 6)
    apply Nat.dvd_antisymm
    · refine (hdvd_iff 60).mp fun σ => ?_
      have hmem : garlingElemOrder σ ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ) := hS6_set ▸ ⟨σ, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      have hdvd60 : orderOf σ ∣ 60 := by
        change garlingElemOrder σ ∣ 60
        rcases hmem with h | h | h | h | h | h <;> rw [h] <;> decide
      rcases hdvd60 with ⟨q, hq⟩
      rw [hq, pow_mul, pow_orderOf_eq_one, one_pow]
    · obtain ⟨σ₃, hσ₃⟩ := exists_sigmaN_orderOf (n := 6) (k := 3) (by omega) (by omega)
      obtain ⟨σ₄, hσ₄⟩ := exists_sigmaN_orderOf (n := 6) (k := 4) (by omega) (by omega)
      obtain ⟨σ₅, hσ₅⟩ := exists_sigmaN_orderOf (n := 6) (k := 5) (by omega) (by omega)
      have h3 : 3 ∣ garlingExponent (SigmaN 6) := by have hd := (helem σ₃).2.2; rwa [hσ₃] at hd
      have h4 : 4 ∣ garlingExponent (SigmaN 6) := by have hd := (helem σ₄).2.2; rwa [hσ₄] at hd
      have h5 : 5 ∣ garlingExponent (SigmaN 6) := by have hd := (helem σ₅).2.2; rwa [hσ₅] at hd
      exact Nat.lcm_dvd (Nat.lcm_dvd h3 h4) h5
  have hS6_card : Nat.card (SigmaN 6) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hS6_setOrder : setOrder (SigmaN 6) = 720 := by
    rw [setOrder_sigmaN 6]
    rfl
  exact ⟨hS3_set, hS3_exp, hS6_set, hS6_exp, hS6_card, hS6_setOrder⟩

/-- **Corollary** [to **Theorem 12.2**] (§12.3, printed p. 104 / PDF p. 112):
*"Suppose that `G` is a finite abelian group. There exists `g` in `G` such that `o(g) = e(G)`."*
Proved directly from `theorem_12_2` following Garling's proof on p. 104. -/
theorem corollary_to_theorem_12_2 (G : Type u) [CommGroup G] [Finite G] :
    ∃ g : G, garlingElemOrder g = garlingExponent G := by
  classical
  obtain ⟨s, d, hd_gt1, hd_dvd, ⟨eA⟩, _, _, _, _⟩ := theorem_12_2 (Additive G)
  obtain ⟨_, _, hmin, _, _, _, _, helem⟩ := garlingExponent_and_elemOrder_properties G
  rcases s with _ | u
  · have hsubG : Subsingleton G :=
      ⟨fun x y => Additive.ofMul.injective (eA.injective (funext fun j => j.elim0))⟩
    refine ⟨1, ?_⟩
    have hexp1 : garlingExponent G ≤ 1 :=
      hmin 1 Nat.zero_lt_one (fun g => by rw [hsubG.elim g 1, one_pow])
    have hexp_pos := (garlingExponent_and_elemOrder_properties G).1
    have hord1 : garlingElemOrder (1 : G) = 1 := by simp [garlingElemOrder]
    omega
  · let last : Fin (u + 1) := Fin.last u
    let ds := d last
    have hds_pos : 0 < ds := lt_trans Nat.zero_lt_one (hd_gt1 last)
    have hd_dvd_ds : ∀ j : Fin (u + 1), d j ∣ ds := by
      intro j
      rcases eq_or_lt_of_le (Fin.le_last j) with rfl | hlt
      · exact dvd_refl ds
      · exact hd_dvd j last hlt
    have hall_pow : ∀ g : G, g ^ ds = 1 := by
      intro g
      have hsmul0 : ds • eA (Additive.ofMul g) = 0 := by
        ext j
        rw [Pi.smul_apply, Pi.zero_apply]
        rcases hd_dvd_ds j with ⟨q, hq⟩
        induction eA (Additive.ofMul g) j using Quotient.inductionOn with | h z =>
        change ds • (QuotientAddGroup.mk z : Zn (d j)) = 0
        rw [zn_nsmul_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
        exact ⟨(q : ℤ) * z, by simp [hq]; ring⟩
      have hA0 : ds • Additive.ofMul g = 0 :=
        eA.injective ((map_nsmul eA ds _).trans (hsmul0.trans (map_zero eA).symm))
      exact Additive.ofMul.injective hA0
    have hexp_le : garlingExponent G ≤ ds := hmin ds hds_pos hall_pow
    let y : (j : Fin (u + 1)) → Zn (d j) := Pi.single last (QuotientAddGroup.mk 1)
    let h : G := Additive.toMul (eA.symm y)
    have hh_pow_iff : ∀ k : ℕ, h ^ k = 1 ↔ ds ∣ k := by
      intro k
      have hk1 : h ^ k = 1 ↔ k • y = 0 := by
        constructor
        · intro hk
          have hA : k • eA.symm y = 0 := hk
          have hy := congrArg eA hA
          rwa [map_nsmul eA, eA.apply_symm_apply, map_zero eA] at hy
        · intro hk
          change k • eA.symm y = 0
          rw [← map_nsmul eA.symm, hk, map_zero eA.symm]
      rw [hk1]
      constructor
      · intro hy0
        have hlast := congrFun hy0 last
        simp only [y, Pi.smul_apply, Pi.zero_apply, Pi.single_eq_same] at hlast
        rw [zn_nsmul_mk, mul_one, QuotientAddGroup.eq_zero_iff,
          AddSubgroup.mem_zmultiples_iff] at hlast
        rcases hlast with ⟨q, hq⟩
        rw [zsmul_eq_mul, mul_comm] at hq
        exact Int.ofNat_dvd.mp ⟨q, hq.symm⟩
      · rintro ⟨q, rfl⟩
        ext j
        by_cases hj : j = last
        · subst j
          simp only [y, Pi.smul_apply, Pi.zero_apply, Pi.single_eq_same]
          rw [zn_nsmul_mk, mul_one, QuotientAddGroup.eq_zero_iff,
            AddSubgroup.mem_zmultiples_iff]
          exact ⟨q, by simp; ring⟩
        · simp [y, Pi.single_eq_of_ne hj]
    have hh_ord : garlingElemOrder h = ds := by
      rw [garlingElemOrder]
      refine orderOf_eq_of_pow_eq_one_and_lt_ne_one hds_pos
        ((hh_pow_iff ds).mpr (dvd_refl ds)) ?_
      intro m hm_pos hmlt _ hm1
      have hdvd_m : ds ∣ m := (hh_pow_iff m).mp hm1
      exact not_lt_of_ge (Nat.le_of_dvd hm_pos hdvd_m) hmlt
    have hle_exp := (helem h).2.1
    exact ⟨h, le_antisymm hle_exp (hh_ord ▸ hexp_le)⟩

/-- **Exercise 12.5** (§12.3, printed p. 104 / PDF p. 112):
*"Suppose that `a` and `b` are positive integers with highest common factor `d`. Show that
`ℤ_a × ℤ_b ≅ ℤ_d × ℤ_{ab/d}`."* -/
theorem exercise_12_5 {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : d = Nat.gcd a b) :
    Nonempty ((Zn a × Zn b) ≃+ (Zn d × Zn ((a * b) / d))) ∧
    Nonempty ((ZMod a × ZMod b) ≃+ (ZMod d × ZMod ((a * b) / d))) := by
  subst hd
  let eZn := znProdAddEquivGcdLcm ha hb
  let eZM :=
    (((znAddEquivZMod a).symm.prodCongr (znAddEquivZMod b).symm).trans eZn).trans
      ((znAddEquivZMod (Nat.gcd a b)).prodCongr (znAddEquivZMod ((a * b) / Nat.gcd a b)))
  exact ⟨⟨eZn⟩, ⟨eZM⟩⟩

/-- Companion to **Exercise 12.5** phrased directly with Garling's §3.6 `IsGarlingHCF` predicate on
`ℤ` (`IsGarlingHCF {(a : ℤ), (b : ℤ)} (d : ℤ)` for positive `a, b, d : ℕ`). -/
theorem exercise_12_5_garling_hcf {a b d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hhcf : IsGarlingHCF ({(a : ℤ), (b : ℤ)} : Set ℤ) (d : ℤ)) :
    d = Nat.gcd a b ∧ Nonempty ((Zn a × Zn b) ≃+ (Zn d × Zn ((a * b) / d))) := by
  have hd_eq : d = Nat.gcd a b := by
    apply Nat.dvd_antisymm
    · refine Nat.dvd_gcd ?_ ?_
      · exact Int.ofNat_dvd.mp (hhcf.1 (a : ℤ) (by simp))
      · exact Int.ofNat_dvd.mp (hhcf.1 (b : ℤ) (by simp))
    · refine Int.ofNat_dvd.mp (hhcf.2 (Nat.gcd a b : ℤ) ?_)
      intro x hx
      rcases hx with rfl | rfl
      · exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left a b)
      · exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_right a b)
  exact ⟨hd_eq, (exercise_12_5 ha hb hd_eq).1⟩

/-- **Exercise 12.6** (§12.3, printed p. 104 / PDF p. 112):
*"Show that a finite abelian group is isomorphic to a product of cyclic groups of prime power
order."* (Proved in both multiplicative `CommGroup` and additive `AddCommGroup` forms, with empty
index type `Fin 0` at `|G| = 1` so every factor has strict prime-power order `IsPrimePow`.) -/
private noncomputable def directSumDropZeroEquiv (ι : Type*) [DecidableEq ι] (p₀ e₀ : ι → ℕ) :
    DirectSum ι (fun i => ZMod (p₀ i ^ e₀ i)) ≃+
      DirectSum {i : ι // e₀ i ≠ 0} (fun j => ZMod (p₀ j.1 ^ e₀ j.1)) where
  toFun := DirectSum.toAddMonoid fun i =>
    if hi : e₀ i = 0 then 0
    else DirectSum.of (fun j : {i : ι // e₀ i ≠ 0} => ZMod (p₀ j.1 ^ e₀ j.1)) ⟨i, hi⟩
  invFun := DirectSum.toAddMonoid fun j =>
    DirectSum.of (fun i : ι => ZMod (p₀ i ^ e₀ i)) j.1
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      simp only [DirectSum.toAddMonoid_of]
      split_ifs with hi
      · have hsub : Subsingleton (ZMod (p₀ i ^ e₀ i)) :=
          ZMod.subsingleton_iff.mpr (by rw [hi, pow_zero])
        simp [hsub.elim a 0]
      · simp [DirectSum.toAddMonoid_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv y := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j a => simp [DirectSum.toAddMonoid_of, j.2]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add _

theorem exercise_12_6 (G : Type u) [CommGroup G] [Finite G] :
    ∃ (r : ℕ) (p k : Fin r → ℕ) (C : Fin r → Type),
      (∃ inst : ∀ i, CommGroup (C i),
        (∀ i, letI := inst i; IsCyclic (C i)) ∧
        (∀ i, Finite (C i)) ∧
        (∀ i, Nat.Prime (p i) ∧ 0 < k i ∧ IsPrimePow (p i ^ k i) ∧
          Nat.card (C i) = p i ^ k i) ∧
        Nonempty (G ≃* ((i : Fin r) → C i))) := by
  classical
  obtain ⟨ι, hι, p₀, hp₀, e₀, ⟨eDS⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite (Additive G)
  let _ : Fintype ι := hι
  let J := {i : ι // e₀ i ≠ 0}
  let r := Fintype.card J
  let eqvFin : Fin r ≃ J := (Fintype.equivFin J).symm
  let p : Fin r → ℕ := fun j => p₀ (eqvFin j).1
  let k : Fin r → ℕ := fun j => e₀ (eqvFin j).1
  let C : Fin r → Type := fun j => Multiplicative (Zn (p j ^ k j))
  let eAdd : Additive G ≃+ ((j : Fin r) → Zn (p j ^ k j)) :=
    (((eDS.trans (directSumDropZeroEquiv ι p₀ e₀)).trans (DirectSum.addEquivProd _)).trans
      (reindexPiAddEquiv eqvFin (fun j : J => ZMod (p₀ j.1 ^ e₀ j.1)))).trans
      (AddEquiv.piCongrRight fun j => (znAddEquivZMod (p j ^ k j)).symm)
  let eMul : G ≃* ((j : Fin r) → C j) :=
    MulEquiv.toAdditive.symm (eAdd.trans (MulEquiv.piMultiplicative _).toAdditiveRight)
  refine ⟨r, p, k, C, inferInstance, ?_, ?_, ?_, ⟨eMul⟩⟩
  · intro j
    refine ⟨⟨Multiplicative.ofAdd (QuotientAddGroup.mk 1 : Zn (p j ^ k j)), fun x => ?_⟩⟩
    induction hx : Multiplicative.toAdd x using Quotient.inductionOn with | h z =>
    refine ⟨z, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hx]
    exact (zn_zsmul_mk (p j ^ k j) z 1).trans (congrArg QuotientAddGroup.mk (mul_one z))
  · intro j
    have hprime : Nat.Prime (p j) := hp₀ (eqvFin j).1
    have _ : NeZero (p j ^ k j) := ⟨pow_ne_zero (k j) hprime.ne_zero⟩
    exact Finite.of_equiv (ZMod (p j ^ k j))
      ((znAddEquivZMod (p j ^ k j)).symm.toEquiv.trans Multiplicative.ofAdd)
  · intro j
    have hprime : Nat.Prime (p j) := hp₀ (eqvFin j).1
    have hk_ne0 : k j ≠ 0 := (eqvFin j).2
    have hk_pos : 0 < k j := Nat.pos_of_ne_zero hk_ne0
    have hppow : IsPrimePow (p j ^ k j) := hprime.prime.isPrimePow.pow hk_ne0
    have _ : NeZero (p j ^ k j) := ⟨pow_ne_zero (k j) hprime.ne_zero⟩
    have hcard : Nat.card (C j) = p j ^ k j := by
      dsimp [C]
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr (znAddEquivZMod _).toEquiv,
        Nat.card_zmod]
    exact ⟨hprime, hk_pos, hppow, hcard⟩

/-- Additive companion to **Exercise 12.6** (§12.3, p. 104): every finite additive abelian group `G`
is isomorphic to `∏_{j : Fin r} ℤ_{p_j^{k_j}}` for primes `p_j` and positive exponents `k_j`. -/
theorem exercise_12_6_add (G : Type u) [AddCommGroup G] [Finite G] :
    ∃ (r : ℕ) (p k : Fin r → ℕ),
      (∀ j, Nat.Prime (p j) ∧ 0 < k j ∧ IsPrimePow (p j ^ k j)) ∧
      Nonempty (G ≃+ ((j : Fin r) → Zn (p j ^ k j))) := by
  classical
  obtain ⟨ι, hι, p₀, hp₀, e₀, ⟨eDS⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  let _ : Fintype ι := hι
  let J := {i : ι // e₀ i ≠ 0}
  let r := Fintype.card J
  let eqvFin : Fin r ≃ J := (Fintype.equivFin J).symm
  let p : Fin r → ℕ := fun j => p₀ (eqvFin j).1
  let k : Fin r → ℕ := fun j => e₀ (eqvFin j).1
  let eAdd : G ≃+ ((j : Fin r) → Zn (p j ^ k j)) :=
    (((eDS.trans (directSumDropZeroEquiv ι p₀ e₀)).trans (DirectSum.addEquivProd _)).trans
      (reindexPiAddEquiv eqvFin (fun j : J => ZMod (p₀ j.1 ^ e₀ j.1)))).trans
      (AddEquiv.piCongrRight fun j => (znAddEquivZMod (p j ^ k j)).symm)
  refine ⟨r, p, k, fun j => ?_, ⟨eAdd⟩⟩
  have hprime : Nat.Prime (p j) := hp₀ (eqvFin j).1
  have hk_ne0 : k j ≠ 0 := (eqvFin j).2
  exact ⟨hprime, Nat.pos_of_ne_zero hk_ne0, hprime.prime.isPrimePow.pow hk_ne0⟩

/-- The torsion subgroup `T = {g ∈ G : g has finite order}` of a commutative group `G`
(`Exercise 12.7`, §12.3, printed p. 105 / PDF p. 113). -/
def garlingTorsionSubgroup (G : Type u) [CommGroup G] : Subgroup G where
  carrier := {g : G | IsOfFinOrder g}
  one_mem' := isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  mul_mem' {a b} ha hb := by
    rcases isOfFinOrder_iff_pow_eq_one.mp ha with ⟨m, hm_pos, hm⟩
    rcases isOfFinOrder_iff_pow_eq_one.mp hb with ⟨n, hn_pos, hn⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, Nat.mul_pos hm_pos hn_pos, ?_⟩
    rw [mul_pow, pow_mul, hm, one_pow, mul_comm m n, pow_mul, hn, one_pow, one_mul]
  inv_mem' {a} ha := by
    rcases isOfFinOrder_iff_pow_eq_one.mp ha with ⟨m, hm_pos, hm⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm_pos, by rw [inv_pow, hm, inv_one]⟩

/-- Additive torsion subgroup `T = {g ∈ G : g has finite additive order}` of an additive abelian
group `(G, +)` (`Exercises 12.7`–`12.9`, §12.3, printed p. 105 / PDF p. 113). -/
def garlingAddTorsionSubgroup (G : Type u) [AddCommGroup G] : AddSubgroup G where
  carrier := {g : G | IsOfFinAddOrder g}
  zero_mem' := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, Nat.zero_lt_one, smul_zero 1⟩
  add_mem' {a b} ha hb := by
    rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp ha with ⟨m, hm_pos, hm⟩
    rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hb with ⟨n, hn_pos, hn⟩
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m * n, Nat.mul_pos hm_pos hn_pos, ?_⟩
    rw [nsmul_add, mul_nsmul, hm, smul_zero, zero_add, mul_comm m n, mul_nsmul, hn, smul_zero]
  neg_mem' {a} ha := by
    rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp ha with ⟨m, hm_pos, hm⟩
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm_pos, by rw [smul_neg, hm, neg_zero]⟩

/-- **Exercise 12.7** (§12.3, printed p. 105 / PDF p. 113):
*"Suppose that `G` is an abelian group. Show that the set `T` of elements of finite order is a
subgroup of `G` and that every element of `G/T`, except the identity, is of infinite order."* -/
theorem exercise_12_7 (G : Type u) [CommGroup G] :
    let T := garlingTorsionSubgroup G
    (T : Set G) = {g : G | IsOfFinOrder g} ∧
    T.Normal ∧
    (∀ q : G ⧸ T, q ≠ 1 → ¬ IsOfFinOrder q ∧ setOrder (Subgroup.zpowers q) = ⊤) := by
  intro T
  refine ⟨rfl, inferInstance, fun q hq1 => ?_⟩
  have hnotFin : ¬ IsOfFinOrder q := by
    intro hfin
    induction q using Quotient.inductionOn with | h g =>
    rcases isOfFinOrder_iff_pow_eq_one.mp hfin with ⟨k, hk_pos, hqk⟩
    change (QuotientGroup.mk g : G ⧸ T) ^ k = 1 at hqk
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hqk
    rcases isOfFinOrder_iff_pow_eq_one.mp hqk with ⟨m, hm_pos, hgkm⟩
    rw [← pow_mul] at hgkm
    have hgT : g ∈ T := isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk_pos hm_pos, hgkm⟩
    exact hq1 ((QuotientGroup.eq_one_iff g).mpr hgT)
  have hsetInf : setOrder (Subgroup.zpowers q) = ⊤ := by
    rw [setOrder, ENat.card_eq_top]
    refine Infinite.of_injective (fun n : ℕ => (⟨q ^ n, Subgroup.npow_mem_zpowers q n⟩ : Subgroup.zpowers q)) ?_
    intro a b hab
    have hpow : q ^ a = q ^ b := congrArg Subtype.val hab
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exfalso
      have hdiff : q ^ (b - a) = 1 := by
        have h1 : q ^ a * q ^ (b - a) = q ^ a * 1 := by
          rw [← pow_add, Nat.add_sub_of_le (le_of_lt hlt), ← hpow, mul_one]
        exact mul_left_cancel h1
      exact hnotFin (isOfFinOrder_iff_pow_eq_one.mpr ⟨b - a, by omega, hdiff⟩)
    · rfl
    · exfalso
      have hdiff : q ^ (a - b) = 1 := by
        have h1 : q ^ b * q ^ (a - b) = q ^ b * 1 := by
          rw [← pow_add, Nat.add_sub_of_le (le_of_lt hgt), hpow, mul_one]
        exact mul_left_cancel h1
      exact hnotFin (isOfFinOrder_iff_pow_eq_one.mpr ⟨a - b, by omega, hdiff⟩)
  exact ⟨hnotFin, hsetInf⟩

/-- Additive companion to **Exercise 12.7** (§12.3, p. 105). -/
theorem exercise_12_7_add (G : Type u) [AddCommGroup G] :
    let T := garlingAddTorsionSubgroup G
    (T : Set G) = {g : G | IsOfFinAddOrder g} ∧
    (∀ q : G ⧸ T, q ≠ 0 → ¬ IsOfFinAddOrder q ∧ setOrder (AddSubgroup.zmultiples q) = ⊤) := by
  intro T
  refine ⟨rfl, fun q hq0 => ?_⟩
  have hnotFin : ¬ IsOfFinAddOrder q := by
    intro hfin
    induction q using Quotient.inductionOn with | h g =>
    rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin with ⟨k, hk_pos, hqk⟩
    change k • (QuotientAddGroup.mk g : G ⧸ T) = 0 at hqk
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hqk
    rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hqk with ⟨m, hm_pos, hgkm⟩
    rw [← mul_nsmul] at hgkm
    have hgT : g ∈ T :=
      isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k * m, Nat.mul_pos hk_pos hm_pos, hgkm⟩
    exact hq0 ((QuotientAddGroup.eq_zero_iff g).mpr hgT)
  have hsetInf : setOrder (AddSubgroup.zmultiples q) = ⊤ := by
    rw [setOrder, ENat.card_eq_top]
    refine Infinite.of_injective
      (fun n : ℕ => (⟨(n : ℤ) • q, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
        AddSubgroup.zmultiples q)) ?_
    intro a b hab
    have hsmul : (a : ℤ) • q = (b : ℤ) • q := congrArg Subtype.val hab
    simp only [natCast_zsmul] at hsmul
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exfalso
      have hdiff : (b - a) • q = 0 := by
        have h1 : a • q + (b - a) • q = a • q + 0 := by
          rw [← add_nsmul, Nat.add_sub_of_le (le_of_lt hlt), ← hsmul, add_zero]
        exact add_left_cancel h1
      exact hnotFin (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨b - a, by omega, hdiff⟩)
    · rfl
    · exfalso
      have hdiff : (a - b) • q = 0 := by
        have h1 : b • q + (a - b) • q = b • q + 0 := by
          rw [← add_nsmul, Nat.add_sub_of_le (le_of_lt hgt), hsmul, add_zero]
        exact add_left_cancel h1
      exact hnotFin (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨a - b, by omega, hdiff⟩)
  exact ⟨hnotFin, hsetInf⟩

/-- Explicit trivial-group (`|G| = 1`) counterexample to **Exercise 12.8** under Garling's §1.1
(p. 7) non-empty generating-set definition `IsGarlingAddGeneratedBy` (and under naive `ℕ`
subtraction `s - 1` on `IsAddGeneratedBy`):
for `G = PUnit` (`|G| = 1`, finitely generated and vacuously torsion-free on `x ≠ 0`),
(1) under `IsGarlingAddGeneratedBy`, the unique `s` such that `G` is generated by `s` elements
but not by `s - 1` elements is `s = 1`, yet `G` is NOT isomorphic to `ℤ^1`; and
(2) under `IsAddGeneratedBy` with `ℕ` subtraction `s - 1`, NO `s : ℕ` satisfies
`IsAddGeneratedBy PUnit s ∧ ¬ IsAddGeneratedBy PUnit (s - 1)`. -/
theorem exercise_12_8_trivial_counterexample :
    (∀ x : Unit, x ≠ 0 → ¬ IsOfFinAddOrder x) ∧
    (∀ s : ℕ, (IsGarlingAddGeneratedBy Unit s ∧ ¬ IsGarlingAddGeneratedBy Unit (s - 1)) ↔ s = 1) ∧
    IsEmpty (Unit ≃+ (Fin 1 → ℤ)) ∧
    (¬ ∃ s : ℕ, IsAddGeneratedBy Unit s ∧ ¬ IsAddGeneratedBy Unit (s - 1)) := by
  have htf : ∀ x : Unit, x ≠ 0 → ¬ IsOfFinAddOrder x :=
    fun x hx0 => (hx0 (Subsingleton.elim x 0)).elim
  have hgen_all : ∀ s : ℕ, IsAddGeneratedBy Unit s := fun s => by
    refine ⟨fun _ => 0, ?_⟩
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact AddSubgroup.zero_mem _
  have hgar : ∀ s : ℕ,
      (IsGarlingAddGeneratedBy Unit s ∧ ¬ IsGarlingAddGeneratedBy Unit (s - 1)) ↔ s = 1 := by
    intro s
    rcases s with _ | _ | u
    · simp [not_isGarlingAddGeneratedBy_zero]
    · refine ⟨fun _ => rfl, fun _ => ⟨?_, not_isGarlingAddGeneratedBy_zero Unit⟩⟩
      exact (isGarlingAddGeneratedBy_iff_of_pos Nat.zero_lt_one).mpr (hgen_all 1)
    · refine ⟨fun ⟨_, hnot⟩ => (hnot ?_).elim, fun h => by omega⟩
      exact (isGarlingAddGeneratedBy_iff_of_pos (by omega)).mpr (hgen_all (u + 1))
  have hemp : IsEmpty (Unit ≃+ (Fin 1 → ℤ)) := ⟨fun e => by
    have h := e.symm.injective (Subsingleton.elim (e.symm (fun _ => 0)) (e.symm (fun _ => 1)))
    have h01 := congrFun h 0
    omega⟩
  have hno_nat : ¬ ∃ s : ℕ, IsAddGeneratedBy Unit s ∧ ¬ IsAddGeneratedBy Unit (s - 1) := by
    rintro ⟨s, _, hnot⟩
    exact hnot (hgen_all (s - 1))
  exact ⟨htf, hgar, hemp, hno_nat⟩

/-- **Exercise 12.8** (§12.3, printed p. 105 / PDF p. 113; see `QUEUE.md` on trivial-group `|G| = 1`
edge case vs. §1.1 p. 7's non-empty generating-set convention):
*"Suppose that `G` is a finitely generated abelian group every element of which, except the
identity, has infinite order. Show that `G ≅ ℤ^s`, where `s` is defined by the property that `G`
is generated by `s` elements, but is not generated by `s - 1` elements."*

Unconditional version over all finitely generated torsion-free abelian groups `G` (`|G| ≥ 1`,
characterizing `s` via `∀ t < s` and integer-typed `(s : ℤ) - 1`), followed by
`exercise_12_8_nontrivial` for `[Nontrivial G]` with literal `ℕ` subtraction `s - 1`. -/
theorem exercise_12_8 (G : Type u) [AddCommGroup G] [AddGroup.FG G]
    (htf : ∀ x : G, x ≠ 0 → ¬ IsOfFinAddOrder x) :
    ∃! s : ℕ,
      IsAddGeneratedBy G s ∧
      (∀ t < s, ¬ IsAddGeneratedBy G t) ∧
      (¬ ∃ t : ℕ, (t : ℤ) = (s : ℤ) - 1 ∧ IsAddGeneratedBy G t) ∧
      Nonempty (G ≃+ (Fin s → ℤ)) := by
  classical
  obtain ⟨s, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let _ : Fintype ι := fι
  let T₀ := DirectSum ι (fun i => ZMod (p i ^ e i))
  have hT₀_fin : Finite T₀ := by
    have _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero (e i) (hp i).ne_zero⟩
    exact Finite.of_equiv ((i : ι) → ZMod (p i ^ e i)) (DirectSum.addEquivProd _).symm.toEquiv
  have hT₀_sub : Subsingleton T₀ := by
    refine ⟨fun a b => ?_⟩
    have ha0 : ∀ c : T₀, c = 0 := by
      intro c
      by_contra hc0
      let g : G := f.symm (0, c)
      have hg0 : g ≠ 0 := fun h0 => hc0 (by
        have h1 := congrArg (Prod.snd ∘ f) h0
        simpa [g] using h1)
      have hc_fin : IsOfFinAddOrder c := isOfFinAddOrder_of_finite c
      rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hc_fin with ⟨k, hk_pos, hkc⟩
      have hg_fin : IsOfFinAddOrder g := by
        refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk_pos, ?_⟩
        dsimp [g]
        rw [← map_nsmul f.symm]
        have hpair : k • ((0 : Fin s →₀ ℤ), c) = 0 := Prod.ext (smul_zero k) hkc
        rw [hpair, map_zero f.symm]
      exact htf g hg0 hg_fin
    rw [ha0 a, ha0 b]
  have eFree : G ≃+ (Fin s → ℤ) :=
    (f.trans
      { toFun := Prod.fst
        invFun := fun x => (x, 0)
        left_inv := fun ⟨x, y⟩ => Prod.ext rfl (hT₀_sub.elim 0 y)
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }).trans Finsupp.addEquivFunOnFinite
  have hgen_s : IsAddGeneratedBy G s := by
    rw [isAddGeneratedBy_congr eFree s]
    refine isAddGeneratedBy_pi_of_zmultiples (fun _ => ℤ) (fun _ => 1) fun _ => ?_
    rw [eq_top_iff]
    intro z _
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, by simp⟩
  have hnot_lt : ∀ t < s, ¬ IsAddGeneratedBy G t := by
    intro t hts
    let π : (Fin s → ℤ) →+ (Fin s → ZMod 2) :=
      { toFun := fun v j => (v j : ZMod 2)
        map_zero' := by ext j; simp
        map_add' := fun u v => by ext j; simp }
    have hπ_surj : Function.Surjective π := by
      intro w
      refine ⟨fun j => (w j).val, ?_⟩
      ext j
      change (((w j).val : ℤ) : ZMod 2) = w j
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact not_isAddGeneratedBy_of_surjective_zmod_pow Nat.prime_two hts
      (π.comp eFree.toAddMonoidHom) (hπ_surj.comp eFree.surjective)
  have hnot_int_pred : ¬ ∃ t : ℕ, (t : ℤ) = (s : ℤ) - 1 ∧ IsAddGeneratedBy G t := by
    rintro ⟨t, _, ht_gen⟩
    exact hnot_lt t (by omega) ht_gen
  refine ⟨s, ⟨hgen_s, hnot_lt, hnot_int_pred, ⟨eFree⟩⟩, ?_⟩
  rintro s' ⟨hgen', hnot', _, _⟩
  rcases lt_trichotomy s' s with hlt | rfl | hgt
  · exact (hnot_lt s' hlt hgen').elim
  · rfl
  · exact (hnot' s hgt hgen_s).elim

/-- Nontrivial companion to **Exercise 12.8** (§12.3, p. 105): when `[Nontrivial G]`, `0 < s` and
both `IsAddGeneratedBy` and §1.1's `IsGarlingAddGeneratedBy` characterize `s` literally with `ℕ`
subtraction `s - 1`. -/
theorem exercise_12_8_nontrivial (G : Type u) [AddCommGroup G] [AddGroup.FG G] [Nontrivial G]
    (htf : ∀ x : G, x ≠ 0 → ¬ IsOfFinAddOrder x) :
    ∃! s : ℕ,
      0 < s ∧
      IsAddGeneratedBy G s ∧
      ¬ IsAddGeneratedBy G (s - 1) ∧
      IsGarlingAddGeneratedBy G s ∧
      ¬ IsGarlingAddGeneratedBy G (s - 1) ∧
      Nonempty (G ≃+ (Fin s → ℤ)) := by
  obtain ⟨s, ⟨hgen, hnot_lt, _, ⟨eFree⟩⟩, huniq⟩ := exercise_12_8 G htf
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exfalso
      obtain ⟨x, y, hxy⟩ := exists_pair_ne G
      exact hxy (eFree.injective (funext fun j => j.elim0))
    · exact hpos
  have hgar_s : IsGarlingAddGeneratedBy G s :=
    (isGarlingAddGeneratedBy_iff_of_pos hs_pos).mpr hgen
  have hnot_gar_pred : ¬ IsGarlingAddGeneratedBy G (s - 1) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs_pos) with heq | hgt1
    · have hs1 : s = 1 := heq.symm
      rw [hs1, Nat.sub_self]
      exact not_isGarlingAddGeneratedBy_zero G
    · exact mt (isGarlingAddGeneratedBy_iff_of_pos (by omega)).mp (hnot_lt (s - 1) (by omega))
  refine ⟨s, ⟨hs_pos, hgen, hnot_lt (s - 1) (by omega), hgar_s, hnot_gar_pred, ⟨eFree⟩⟩, ?_⟩
  rintro s' ⟨_, hgen', hnot_pred', _, _, _⟩
  rcases lt_trichotomy s' s with hlt | rfl | hgt
  · exact (hnot_lt s' hlt hgen').elim
  · rfl
  · have hle : s ≤ s' - 1 := by omega
    have hgen_pred' : IsAddGeneratedBy G (s' - 1) := by
      rcases hgen with ⟨g, hg⟩
      let g' : Fin (s' - 1) → G := fun i =>
        if h : (i : ℕ) < s then g ⟨i, h⟩ else 0
      refine ⟨g', ?_⟩
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ AddSubgroup.closure (Set.range g) := hg ▸ AddSubgroup.mem_top x
      refine AddSubgroup.closure_mono ?_ hx
      rintro _ ⟨j, rfl⟩
      refine ⟨⟨j, lt_of_lt_of_le j.2 hle⟩, ?_⟩
      simp [g', j.2]
    exact (hnot_pred' hgen_pred').elim

/-- **Exercise 12.9** (§12.3, printed p. 105 / PDF p. 113):
*"Suppose that `G` is a finitely generated abelian group. Show that `G ≅ ℤ^s × T`, where `T` is a
finite group."*
Proved unconditionally for all finitely generated abelian groups `G` (`|G| ≥ 1`), both with `T` in
`G`'s universe `Type u` (canonically realized as `garlingAddTorsionSubgroup G`) and in
multiplicative `CommGroup` form below. -/
theorem exercise_12_9 (G : Type u) [AddCommGroup G] [AddGroup.FG G] :
    Finite (garlingAddTorsionSubgroup G) ∧
    (∃ s : ℕ, Nonempty (G ≃+ (Fin s → ℤ) × garlingAddTorsionSubgroup G)) ∧
    (∃ (s : ℕ) (T : Type u) (_ : AddCommGroup T),
      Finite T ∧ Nonempty (G ≃+ (Fin s → ℤ) × T)) := by
  classical
  obtain ⟨s, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let _ : Fintype ι := fι
  let T₀ := DirectSum ι (fun i => ZMod (p i ^ e i))
  have _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero (e i) (hp i).ne_zero⟩
  have hT₀_fin : Finite T₀ :=
    Finite.of_equiv ((i : ι) → ZMod (p i ^ e i)) (DirectSum.addEquivProd _).symm.toEquiv
  let eProd : G ≃+ (Fin s → ℤ) × T₀ :=
    f.trans (Finsupp.addEquivFunOnFinite.prodCongr (AddEquiv.refl T₀))
  have hmemT_iff : ∀ g : G, g ∈ garlingAddTorsionSubgroup G ↔ (eProd g).1 = 0 := by
    intro g
    constructor
    · intro hg
      rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hg with ⟨k, hk_pos, hkg⟩
      have hk_map : k • eProd g = 0 := by rw [← map_nsmul eProd, hkg, map_zero eProd]
      have hfst : k • (eProd g).1 = 0 := congrArg Prod.fst hk_map
      ext j
      have hj : k • ((eProd g).1 j) = 0 := congrFun hfst j
      rw [nsmul_eq_mul] at hj
      rcases mul_eq_zero.mp hj with hk0 | hv0
      · exact (Nat.ne_of_gt hk_pos (Int.natCast_eq_zero.mp hk0)).elim
      · exact hv0
    · intro hfst0
      have hsnd_fin : IsOfFinAddOrder (eProd g).2 := isOfFinAddOrder_of_finite (eProd g).2
      rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp hsnd_fin with ⟨k, hk_pos, hksnd⟩
      refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk_pos, ?_⟩
      apply eProd.injective
      rw [map_nsmul eProd, map_zero eProd]
      exact Prod.ext (by change k • (eProd g).1 = 0; rw [hfst0, smul_zero]) hksnd
  let eTor : garlingAddTorsionSubgroup G ≃+ T₀ :=
    { toFun := fun x => (eProd x.1).2
      invFun := fun t => ⟨eProd.symm (0, t), (hmemT_iff _).mpr (by simp)⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply eProd.injective
        rw [eProd.apply_symm_apply]
        exact Prod.ext ((hmemT_iff x.1).mp x.2).symm rfl
      right_inv := fun t => by simp
      map_add' := fun x y => by simp }
  have hT_fin : Finite (garlingAddTorsionSubgroup G) := Finite.of_equiv T₀ eTor.symm.toEquiv
  let eCan : G ≃+ (Fin s → ℤ) × garlingAddTorsionSubgroup G :=
    eProd.trans ((AddEquiv.refl _).prodCongr eTor.symm)
  exact ⟨hT_fin, ⟨s, ⟨eCan⟩⟩, ⟨s, garlingAddTorsionSubgroup G, inferInstance, hT_fin, ⟨eCan⟩⟩⟩

/-- Multiplicative companion to **Exercise 12.9** (§12.3, p. 105). -/
theorem exercise_12_9_mul (G : Type u) [CommGroup G] [Group.FG G] :
    ∃ (s : ℕ) (T : Type u) (_ : CommGroup T),
      Finite T ∧ Nonempty (G ≃* (Fin s → Multiplicative ℤ) × T) := by
  have _ : AddGroup.FG (Additive G) := inferInstance
  obtain ⟨_, ⟨s, ⟨eAdd⟩⟩, _⟩ := exercise_12_9 (Additive G)
  let T := Multiplicative (garlingAddTorsionSubgroup (Additive G))
  have _ : Finite (garlingAddTorsionSubgroup (Additive G)) := (exercise_12_9 (Additive G)).1
  have hT_fin : Finite T := Finite.of_equiv _ Multiplicative.ofAdd
  let eMul : G ≃* (Fin s → Multiplicative ℤ) × T :=
    MulEquiv.toAdditive.symm
      ((eAdd.trans ((MulEquiv.piMultiplicative _).toAdditiveRight.prodCongr
        (AddEquiv.additiveMultiplicative _).symm)).trans
        (AddEquiv.prodAdditive _ _).symm)
  exact ⟨s, T, inferInstance, hT_fin, ⟨eMul⟩⟩

/-! ## §12.4 The multiplicative group of a finite field (printed p. 105, PDF p. 113) -/

/-- **Theorem 12.3** (§12.4, printed p. 105 / PDF p. 113):
*"Suppose that `K` is a field, with multiplicative group `K*` of non-zero elements. If `G` is a
finite subgroup of `K*`, then `G` is cyclic."*

Proved directly from `garlingExponent_and_elemOrder_properties` (`e(G) ≤ |G|`), polynomial root
counting (`|G| ≤ e(G)` on `x^{e(G)} - 1`), and `corollary_to_theorem_12_2` (`∃ g ∈ G, o(g) = e(G)`),
matching Garling's 4-line proof on p. 105. -/
theorem theorem_12_3 (K : Type u) [Field K] (G : Subgroup Kˣ) [Finite G] :
    IsCyclic G ∧ ∃ g : G, Subgroup.zpowers g = ⊤ ∧ orderOf g = Nat.card G := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨hlam_pos, hpow_lam, _, _, _, hlam_le_card, _, _⟩ :=
    garlingExponent_and_elemOrder_properties G
  let lam := garlingExponent G
  let f : K[X] := Polynomial.X ^ lam - Polynomial.C 1
  have hf_ne0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hlam_pos 1
  have hf_deg : f.natDegree = lam := Polynomial.natDegree_X_pow_sub_C
  have hroot_mem : ∀ g : G, ((g.1 : Kˣ) : K) ∈ f.roots.toFinset := by
    intro g
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne0, Polynomial.IsRoot.def]
    dsimp [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have hg1 : ((g ^ lam : G).1 : Kˣ) = 1 := congrArg Subtype.val (hpow_lam g)
    have hval : ((g.1 : Kˣ) : K) ^ lam = 1 := by
      simpa using congrArg (Units.val : Kˣ → K) hg1
    rw [hval, sub_self]
  let emb : G → f.roots.toFinset := fun g => ⟨((g.1 : Kˣ) : K), hroot_mem g⟩
  have hemb_inj : Function.Injective emb := by
    intro g₁ g₂ h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  have hcard_le_lam : Nat.card G ≤ lam := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card G ≤ Fintype.card f.roots.toFinset :=
          Fintype.card_le_of_injective emb hemb_inj
      _ = f.roots.toFinset.card := Fintype.card_coe _
      _ ≤ f.roots.card := Multiset.toFinset_card_le f.roots
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = lam := hf_deg
  have hlam_eq : lam = Nat.card G := le_antisymm hlam_le_card hcard_le_lam
  obtain ⟨g, hg_ord⟩ := corollary_to_theorem_12_2 G
  have hord_card : orderOf g = Nat.card G := hg_ord.trans hlam_eq
  have hcard_zpow : Nat.card (Subgroup.zpowers g) = Nat.card G :=
    (Nat.card_zpowers g).trans hord_card
  have htop : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ hcard_zpow
  have hcyc : IsCyclic G := ⟨⟨g, fun x => Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top x)⟩⟩
  exact ⟨hcyc, g, htop, hord_card⟩

/-- **Corollary 1** [to **Theorem 12.3**] (§12.4, printed p. 105 / PDF p. 113):
*"If `K` is a finite field, `K*` is cyclic."* -/
theorem corollary_1_to_theorem_12_3 (K : Type u) [Field K] [Finite K] :
    IsCyclic Kˣ ∧
    Nat.card Kˣ = Nat.card K - 1 ∧
    ∃ u : Kˣ, Subgroup.zpowers u = ⊤ ∧ orderOf u = Nat.card K - 1 := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨_, g, hg_top, hg_ord⟩ := theorem_12_3 K (⊤ : Subgroup Kˣ)
  let eTop : (⊤ : Subgroup Kˣ) ≃* Kˣ := Subgroup.topEquiv
  let u : Kˣ := eTop g
  have hsurj : Function.Surjective (u ^ · : ℤ → Kˣ) := by
    intro x
    have hx : eTop.symm x ∈ Subgroup.zpowers g := hg_top ▸ Subgroup.mem_top _
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc u ^ k = eTop (g ^ k) := (map_zpow eTop g k).symm
      _ = eTop (eTop.symm x) := by rw [hk]
      _ = x := eTop.apply_symm_apply x
  have hu_top : Subgroup.zpowers u = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_zpowers_iff.mpr (hsurj x)
  have hcard_units : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hu_ord : orderOf u = Nat.card K - 1 := by
    calc orderOf u = orderOf (eTop.toMonoidHom g) := rfl
      _ = orderOf g := orderOf_injective eTop.toMonoidHom eTop.injective g
      _ = Nat.card (⊤ : Subgroup Kˣ) := hg_ord
      _ = Nat.card Kˣ := Nat.card_congr eTop.toEquiv
      _ = Nat.card K - 1 := hcard_units
  exact ⟨⟨⟨u, hsurj⟩⟩, hcard_units, u, hu_top, hu_ord⟩

/-- **Corollary 2** [to **Theorem 12.3**] (§12.4, printed p. 105 / PDF p. 113):
*"If `L : K` is an extension, and `L` is a finite field, then `L : K` is simple."*

Proved directly by Garling's 1-line proof on p. 105 (*"Let `α` generate the multiplicative group
`L*`. Then `L = K(α)`"*). -/
theorem corollary_2_to_theorem_12_3 (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Finite L] :
    IsSimpleExtension K L := by
  obtain ⟨_, _, u, hu_top, _⟩ := corollary_1_to_theorem_12_3 L
  refine ⟨(u : L), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact (IntermediateField.adjoin K {(u : L)}).zero_mem
  · have hmem : Units.mk0 x hx ∈ Subgroup.zpowers u := hu_top ▸ Subgroup.mem_top _
    rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨k, hk⟩
    have hx_eq : x = (u : L) ^ k := by
      simpa using (congrArg (Units.val : Lˣ → L) hk).symm
    rw [hx_eq]
    exact zpow_mem (IntermediateField.mem_adjoin_simple_self K (u : L)) k

/-- Subfield companion to **Corollary 2** [to **Theorem 12.3**] (§12.4, p. 105). -/
theorem corollary_2_to_theorem_12_3_subfield {L : Type u} [Field L] [Finite L] (K : Subfield L) :
    IsSimpleExtension K L :=
  corollary_2_to_theorem_12_3 K L

/-- Extension-triple companion to **Corollary 2** [to **Theorem 12.3**] (§12.4, p. 105). -/
theorem corollary_2_to_theorem_12_3_triple {K : Type u} {L : Type v} [Field K] [Field L]
    [Finite L] (ext : FieldExtensionTriple K L) :
    @IsSimpleExtension K L _ _ ext.hom.toAlgebra := by
  let _ : Algebra K L := ext.hom.toAlgebra
  exact corollary_2_to_theorem_12_3 K L

/-! ## §12.5 The automorphism group of a finite field (printed pp. 105–106, PDF pp. 113–114) -/

/-- Garling's *Frobenius automorphism* `φ : K ≃+* K` (`φ(α) = α^p`, where `p = char K`) on a finite
field `K` (§12.5, printed p. 105 / PDF p. 113, obtained from §10.5's `garlingFrobenius` and
`corollary_to_theorem_10_7`). -/
noncomputable def garlingFrobeniusAut (K : Type u) [Field K] [Finite K] : GarlingAut K :=
  let hp := (finite_field_char_and_prime_power K).2.1
  let halg : IsAlgebraicExtension (primeSubfield K) K :=
    (isAlgebraicExtension_iff (primeSubfield K) K).mpr inferInstance
  let hbij := corollary_to_theorem_10_7 (K := K) rfl hp.ne_zero halg
  RingEquiv.ofBijective (garlingFrobenius K rfl hp.ne_zero) ⟨hbij.1, hbij.2⟩

@[simp]
theorem garlingFrobeniusAut_apply (K : Type u) [Field K] [Finite K] (α : K) :
    garlingFrobeniusAut K α = α ^ ringChar K := rfl

theorem garlingFrobeniusAut_pow_apply (K : Type u) [Field K] [Finite K] (d : ℕ) (α : K) :
    ((garlingFrobeniusAut K ^ d) α) = α ^ (ringChar K ^ d) := by
  induction d generalizing α with
  | zero => simp
  | succ k ih =>
    change ((garlingFrobeniusAut K ^ k) * garlingFrobeniusAut K) α = α ^ (ringChar K ^ (k + 1))
    change (garlingFrobeniusAut K ^ k) (garlingFrobeniusAut K α) = α ^ (ringChar K ^ (k + 1))
    rw [garlingFrobeniusAut_apply, ih, ← pow_mul, ← pow_succ']

/-- Helper: every ring automorphism `σ : GarlingAut K` of any field `K` fixes `primeSubfield K`. -/
private theorem garlingAut_fixes_primeSubfield {K : Type u} [Field K] (σ : GarlingAut K) :
    ∀ x ∈ primeSubfield K, σ x = x := by
  let F : Subfield K :=
    { carrier := {x : K | σ x = x}
      mul_mem' := fun {a b} ha hb => by change σ (a * b) = a * b; rw [map_mul, ha, hb]
      one_mem' := map_one σ
      add_mem' := fun {a b} ha hb => by change σ (a + b) = a + b; rw [map_add, ha, hb]
      zero_mem' := map_zero σ
      neg_mem' := fun {a} ha => by change σ (-a) = -a; rw [map_neg, ha]
      inv_mem' := fun {a} ha => by change σ a⁻¹ = a⁻¹; rw [map_inv₀, ha] }
  have hle : primeSubfield K ≤ F := by
    rw [primeSubfield_eq_bot]
    exact bot_le
  exact fun x hx => hle hx

/-- **Theorem 12.4** (§12.5, printed p. 105 / PDF p. 113; see `QUEUE.md` on implicit `Nat.Prime p`):
*"Suppose that `K` is a finite field with `p^n` elements. Then the group of all automorphisms of `K`
is cyclic of order `n`, and is generated by the Frobenius automorphism `φ`."*

Proved under `hp : Nat.Prime p` (automatically deducing `0 < n`, `Finite K`, and `ringChar K = p`),
following Garling's exact proof on p. 105 via `Corollary 1` to `Theorem 12.1`, `Theorem 10.4`, and
root-counting on `x^{p^d} - x`. -/
theorem theorem_12_4 {K : Type u} [Field K] {p n : ℕ}
    (hp : Nat.Prime p) (hcard : Nat.card K = p ^ n) :
    ∃ hfin : Finite K,
      let φ : GarlingAut K := @garlingFrobeniusAut K _ hfin
      0 < n ∧
      ringChar K = p ∧
      IsCyclic (GarlingAut K) ∧
      Nat.card (GarlingAut K) = n ∧
      setOrder (GarlingAut K) = (n : ℕ) ∧
      orderOf φ = n ∧
      Subgroup.zpowers φ = ⊤ := by
  classical
  obtain ⟨hn_pos, hfinK, hcharK, hdegK, _, _⟩ :=
    finite_field_isSplittingField_primeSubfield hp hcard
  let _ : Finite K := hfinK
  let _ : Fintype K := Fintype.ofFinite K
  let φ : GarlingAut K := garlingFrobeniusAut K
  have hgal : IsGarlingGaloisExtension (primeSubfield K) K := corollary_1_to_theorem_12_1 K
  have hfin_ext : IsFiniteExtension (primeSubfield K) K := hgal.1
  let A := {τ : K →+* K | IsFieldAutomorphism τ ∧ FixesBaseField (primeSubfield K) τ}
  let eqvAut : GarlingAut K ≃ A :=
    { toFun := fun σ =>
        ⟨σ.toRingHom, ⟨σ.injective, σ.surjective⟩, fun k => garlingAut_fixes_primeSubfield σ k.1 k.2⟩
      invFun := fun τ => RingEquiv.ofBijective τ.1 ⟨τ.2.1.1, τ.2.1.2⟩
      left_inv := fun σ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl }
  have h104 := (theorem_10_4 hfin_ext).1 hgal
  have hcardAut : Nat.card (GarlingAut K) = n :=
    (Nat.card_congr eqvAut).trans (h104.2.trans hdegK)
  have hfinAut : Finite (GarlingAut K) :=
    Nat.finite_of_card_ne_zero (hcardAut.symm ▸ hn_pos.ne')
  have hsetAut : setOrder (GarlingAut K) = (n : ℕ) :=
    setOrder_eq_natCast_iff.mpr ⟨hfinAut, hcardAut⟩
  let d := orderOf φ
  have hd_dvd_n : d ∣ n := hcardAut ▸ orderOf_dvd_natCard φ
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_n hn_pos
  have hd_le_n : d ≤ n := Nat.le_of_dvd hn_pos hd_dvd_n
  have hpow_pd : ∀ α : K, α ^ (p ^ d) = α := by
    intro α
    have h1 : (φ ^ d) α = α := by rw [pow_orderOf_eq_one]; rfl
    have h2 : (φ ^ d) α = α ^ (p ^ d) := by
      dsimp [φ]
      rw [garlingFrobeniusAut_pow_apply, hcharK]
    exact h2.symm.trans h1
  have hpd_gt1 : 1 < p ^ d := one_lt_pow₀ hp.one_lt hd_pos.ne'
  let g : K[X] := Polynomial.X ^ (p ^ d) - Polynomial.X
  obtain ⟨hg_mon, hg_deg⟩ := monic_and_natDegree_X_pow_sub_X K hpd_gt1
  have hmem_roots : ∀ α : K, α ∈ g.roots.toFinset := by
    intro α
    classical
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg_mon.ne_zero, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hpow_pd α, sub_self]
  have hpn_le_pd : p ^ n ≤ p ^ d := by
    classical
    calc p ^ n = Fintype.card K := (Nat.card_eq_fintype_card.symm.trans hcard).symm
      _ ≤ Fintype.card g.roots.toFinset :=
          Fintype.card_le_of_injective (fun α => ⟨α, hmem_roots α⟩)
            (fun _ _ h => congrArg Subtype.val h)
      _ = g.roots.toFinset.card := Fintype.card_coe _
      _ ≤ g.roots.card := Multiset.toFinset_card_le g.roots
      _ ≤ g.natDegree := Polynomial.card_roots' g
      _ = p ^ d := hg_deg
  have hn_le_d : n ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpn_le_pd
  have hd_eq_n : d = n := le_antisymm hd_le_n hn_le_d
  have hcard_zpow : Nat.card (Subgroup.zpowers φ) = Nat.card (GarlingAut K) :=
    (Nat.card_zpowers φ).trans (hd_eq_n.trans hcardAut.symm)
  have hzpow_top : Subgroup.zpowers φ = ⊤ := Subgroup.eq_top_of_card_eq _ hcard_zpow
  have hcyc : IsCyclic (GarlingAut K) :=
    ⟨⟨φ, fun σ => Subgroup.mem_zpowers_iff.mp (hzpow_top ▸ Subgroup.mem_top σ)⟩⟩
  exact ⟨hfinK, hn_pos, hcharK, hcyc, hcardAut, hsetAut, hd_eq_n, hzpow_top⟩

/-- Explicit composite-`p` counterexample to **Theorem 12.4** if `Nat.Prime p` is omitted
(§12.5, p. 105): at `p = 4, n = 1`, there exists a finite field `K` (`𝔽_4`) with `4^1 = 4`
elements whose automorphism group `GarlingAut K` has order `2 ≠ 1 = n`. -/
theorem theorem_12_4_nonprime_counterexample :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 4 ^ 1 ∧
      setOrder K = (4 ^ 1 : ℕ) ∧
      Nat.card (GarlingAut K) = 2 ∧
      Nat.card (GarlingAut K) ≠ 1 := by
  obtain ⟨⟨K, instFK, hsetK, hcardK, _⟩, _⟩ :=
    theorem_12_1.{0, 0} Nat.prime_two (by decide : 0 < 2)
  let _ : Field K := instFK
  obtain ⟨hfinK, _, _, _, hcardAut, _, _, _⟩ := theorem_12_4 Nat.prime_two hcardK
  refine ⟨K, instFK, hfinK, ?_, ?_, hcardAut, by omega⟩
  · simpa using hcardK
  · simpa using hsetK

/-- **Corollary** [to **Theorem 12.4**] (§12.5, printed p. 105 / PDF p. 113; proof pp. 105–106 /
PDF pp. 113–114):
*"Suppose that `L : K` is an extension and that `L` is finite. Then `Γ(L:K)` is cyclic of order
`[L:K]`."* -/
theorem corollary_to_theorem_12_4 (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [Finite L] :
    IsCyclic (GarlingGaloisGroup K L) ∧
    Nat.card (GarlingGaloisGroup K L) = Module.finrank K L ∧
    setOrder (GarlingGaloisGroup K L) = extDegree K L := by
  obtain ⟨_, hp_prime, _, _, _, _, _, hcardL, _⟩ := finite_field_char_and_prime_power L
  obtain ⟨_, hnL_pos, _, hcycAutL, hcardAutL, _, _, _⟩ := theorem_12_4 hp_prime hcardL
  have _ : IsCyclic (GarlingAut L) := hcycAutL
  have _ : Finite (GarlingAut L) := Nat.finite_of_card_ne_zero (hcardAutL.symm ▸ hnL_pos.ne')
  have hcycSub : IsCyclic (garlingGaloisSubgroup K L) := Subgroup.isCyclic _
  obtain ⟨g, hg⟩ := exists_zpow_surjective (garlingGaloisSubgroup K L)
  let eGal := (garlingGaloisGroupMulEquiv K L).symm
  have hcycGal : IsCyclic (GarlingGaloisGroup K L) := by
    refine ⟨⟨eGal g, fun σ => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg (eGal.symm σ)
    dsimp at hk
    refine ⟨k, ?_⟩
    calc (eGal g) ^ k = eGal (g ^ k) := (map_zpow eGal g k).symm
      _ = eGal (eGal.symm σ) := by rw [hk]
      _ = σ := eGal.apply_symm_apply σ
  have hgalKL : IsGarlingGaloisExtension K L := corollary_2_to_theorem_12_1 K L
  have hcardGal : Nat.card (GarlingGaloisGroup K L) = Module.finrank K L :=
    (theorem_10_4_algEquiv hgalKL.1).1 hgalKL
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hgalKL.1
  have hfinGal : Finite (GarlingGaloisGroup K L) :=
    Finite.of_equiv (garlingGaloisSubgroup K L) eGal.toEquiv
  have hsetGal : setOrder (GarlingGaloisGroup K L) = extDegree K L := by
    rw [extDegree_eq_finrank K L]
    exact setOrder_eq_natCast_iff.mpr ⟨hfinGal, hcardGal⟩
  exact ⟨hcycGal, hcardGal, hsetGal⟩

/-- Subfield companion to **Corollary** [to **Theorem 12.4**] (§12.5, p. 105), stated directly on
`garlingGamma K ≤ GarlingAut L`. -/
theorem corollary_to_theorem_12_4_subfield {L : Type u} [Field L] [Finite L] (K : Subfield L) :
    IsCyclic (garlingGamma K) ∧
    Nat.card (garlingGamma K) = Module.finrank K L ∧
    setOrder (garlingGamma K) = extDegree K L := by
  obtain ⟨hcyc, hcard, hset⟩ := corollary_to_theorem_12_4 K L
  let e := garlingGaloisGroupSubfieldMulEquiv K
  obtain ⟨g, hg⟩ := @exists_zpow_surjective _ _ hcyc
  have hcycG : IsCyclic (garlingGamma K) := ⟨⟨e g, fun τ => by
    obtain ⟨k, hk⟩ := hg (e.symm τ)
    exact ⟨k, ((map_zpow e g k).symm.trans (congrArg e hk)).trans (e.apply_symm_apply τ)⟩⟩⟩
  exact ⟨hcycG,
    (Nat.card_congr e.symm.toEquiv).trans hcard,
    (ENat.card_congr e.symm.toEquiv).trans hset⟩

/-- **Exercise 12.10** (§12.5, printed p. 106 / PDF p. 114; see `QUEUE.md` on proof-method prompt
and inherited `Nat.Prime p`):
*"Use Theorem 12.4 to give another solution to Exercise 12.3."*

Proved **genuinely** from `theorem_12_4` (`GarlingAut L = ⟨φ⟩` cyclic of order `n`),
`corollary_to_theorem_12_4_subfield` (`|Γ(L:F)| = [L:F]`), and `theorem_11_8` (the Fundamental
Theorem of Galois Theory over `primeSubfield L`, identifying subfields of `L` of order `p^d` with
subgroups of `⟨φ⟩` of order `n/d`, namely the unique subgroup `⟨φ^d⟩`), **without** invoking
`exercise_12_3`. -/
theorem exercise_12_10 {L : Type u} [Field L] {p n : ℕ}
    (hp : Nat.Prime p) (hL : Nat.card L = p ^ n) :
    (∀ (K : Type v) [Field K] [Algebra K L],
      ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ Nat.card K = p ^ d ∧ setOrder K = (p ^ d : ℕ)) ∧
    (∀ {d : ℕ}, d ∣ n →
      ∃ hfin : Finite L,
        let φ : GarlingAut L := @garlingFrobeniusAut L _ hfin
        let Hd : Subgroup (GarlingAut L) := Subgroup.zpowers (φ ^ d)
        let Fd : Subfield L := garlingPhi (Hd : Set (GarlingAut L))
        (Polynomial.X ^ (p ^ d) - Polynomial.X : (ZMod p)[X]) ∣
          (Polynomial.X ^ (p ^ n) - Polynomial.X : (ZMod p)[X]) ∧
        (Polynomial.X ^ (p ^ d) - Polynomial.X : L[X]) ∣
          (Polynomial.X ^ (p ^ n) - Polynomial.X : L[X]) ∧
        Nat.card Hd = n / d ∧
        (∀ H : Subgroup (GarlingAut L), Nat.card H = n / d ↔ H = Hd) ∧
        Nat.card Fd = p ^ d ∧
        (∀ F : Subfield L, Nat.card F = p ^ d ↔ F = Fd) ∧
        (∃! F : Subfield L, Nat.card F = p ^ d) ∧
        (∃! F : Subfield L, setOrder F = (p ^ d : ℕ))) := by
  obtain ⟨hfinL, hn_pos, hcharL, _, hcardAut, _, hord_φ, hzpow_φ⟩ := theorem_12_4 hp hL
  let _ : Finite L := hfinL
  let _ : Fintype L := Fintype.ofFinite L
  have _ : Finite (GarlingAut L) := Nat.finite_of_card_ne_zero (hcardAut.symm ▸ hn_pos.ne')
  let P : Subfield L := primeSubfield L
  have hfinPL : IsFiniteExtension P L := (corollary_1_to_theorem_12_1 L).1
  have _ : Module.Finite P L := (isFiniteExtension_iff_moduleFinite P L).mp hfinPL
  have hGP_top : garlingGamma P = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true, mem_garlingGamma_iff]
    exact garlingAut_fixes_primeSubfield σ
  have hdegPL : Module.finrank P L = n := by
    obtain ⟨_, hcardG, _⟩ := corollary_to_theorem_12_4_subfield P
    calc Module.finrank P L = Nat.card (garlingGamma P) := hcardG.symm
      _ = Nat.card (⊤ : Subgroup (GarlingAut L)) := by rw [hGP_top]
      _ = Nat.card (GarlingAut L) := Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = n := hcardAut
  have hcardP : Nat.card P = p := by
    obtain ⟨_, ⟨ePZ⟩⟩ := (theorem_3_17 L).2 (hcharL.symm ▸ hp.ne_zero)
    rw [Nat.card_congr ePZ.toEquiv, hcharL, Nat.card_zmod]
  -- Helper computing `|F| = p^{[F : P]}` and `[F : P] * [L : F] = n` for any `F : Subfield L`.
  have subfield_card_and_tower : ∀ F : Subfield L,
      ∃ (dF qF : ℕ), 0 < dF ∧ 0 < qF ∧ dF * qF = n ∧
        Nat.card F = p ^ dF ∧ Nat.card (garlingGamma F) = qF := by
    intro F
    have hP_le_F : P ≤ F := by dsimp [P]; rw [primeSubfield_eq_bot]; exact bot_le
    let iPF : P →+* F := Subfield.inclusion hP_le_F
    let _ : Algebra P F := iPF.toAlgebra
    have _ : IsScalarTower P F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have _ : Module.Finite P F := Module.Finite.left P F L
    have _ : Module.Finite F L := Module.Finite.right P F L
    let dF := Module.finrank P F
    let qF := Module.finrank F L
    have hdF_pos : 0 < dF := Module.finrank_pos
    have hqF_pos : 0 < qF := Module.finrank_pos
    have hmul : dF * qF = n := (Module.finrank_mul_finrank P F L).trans hdegPL
    let bPF := Module.finBasis P F
    have hcardF : Nat.card F = p ^ dF := by
      rw [Nat.card_congr bPF.equivFun.toEquiv, Nat.card_fun, hcardP, Nat.card_fin]
    have hcardGF : Nat.card (garlingGamma F) = qF := (corollary_to_theorem_12_4_subfield F).2.1
    exact ⟨dF, qF, hdF_pos, hqF_pos, hmul, hcardF, hcardGF⟩
  refine ⟨?_, ?_⟩
  · intro K _ _
    let F : Subfield L := (algebraMap K L).fieldRange
    let eKF : K ≃+* F := RingEquiv.ofBijective (algebraMap K L).rangeRestrict
      ⟨fun x y h => (algebraMap K L).injective (congrArg Subtype.val h),
       fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
    obtain ⟨dF, qF, hdF_pos, _, hmul, hcardF, _⟩ := subfield_card_and_tower F
    have hcardK : Nat.card K = p ^ dF := (Nat.card_congr eKF.toEquiv).trans hcardF
    have hfinK : Finite K := Finite.of_equiv F eKF.symm.toEquiv
    exact ⟨dF, hdF_pos, ⟨qF, hmul.symm⟩, hcardK, setOrder_eq_natCast_iff.mpr ⟨hfinK, hcardK⟩⟩
  · intro d hdn
    refine ⟨hfinL, ?_⟩
    let φ : GarlingAut L := garlingFrobeniusAut L
    let Hd : Subgroup (GarlingAut L) := Subgroup.zpowers (φ ^ d)
    let Fd : Subfield L := garlingPhi (Hd : Set (GarlingAut L))
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn_pos
    have hq_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn_pos hdn) hd_pos
    have hdq_eq : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hcard_Hd : Nat.card Hd = n / d := by
      rw [Nat.card_zpowers, orderOf_pow' φ hd_pos.ne', hord_φ, Nat.gcd_eq_right hdn]
    -- Unique subgroup of cyclic `⟨φ⟩` of order `n / d`:
    have huniq_Hd : ∀ H : Subgroup (GarlingAut L), Nat.card H = n / d ↔ H = Hd := by
      intro H
      constructor
      · intro hcardH
        have hle : H ≤ Hd := by
          intro σ hσ
          have hσ_mem : σ ∈ Subgroup.zpowers φ := hzpow_φ ▸ Subgroup.mem_top σ
          rcases Subgroup.mem_zpowers_iff.mp hσ_mem with ⟨k, rfl⟩
          have hmod_nn : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k (by omega)
          let r : ℕ := (k % (n : ℤ)).toNat
          have hr_cast : (r : ℤ) = k % (n : ℤ) := Int.toNat_of_nonneg hmod_nn
          have hφ_n1 : φ ^ (n : ℤ) = 1 := by rw [zpow_natCast, ← hord_φ, pow_orderOf_eq_one]
          have hφk_eq : φ ^ k = φ ^ r := by
            conv_lhs => rw [show k = (n : ℤ) * (k / (n : ℤ)) + k % (n : ℤ) by
              linarith [Int.ediv_mul_add_emod k (n : ℤ)]]
            rw [zpow_add, zpow_mul, hφ_n1, one_zpow, one_mul, ← hr_cast, zpow_natCast]
          have hpow_H1 : (⟨φ ^ k, hσ⟩ : H) ^ (n / d) = 1 := by
            let _ : Fintype H := Fintype.ofFinite H
            rw [← hcardH, Nat.card_eq_fintype_card]
            exact pow_card_eq_one
          have hφ_pow1 : (φ ^ r) ^ (n / d) = 1 := by
            rw [← hφk_eq]
            exact congrArg Subtype.val hpow_H1
          rw [← pow_mul] at hφ_pow1
          have hn_dvd : n ∣ r * (n / d) := by
            have hdiv := orderOf_dvd_of_pow_eq_one hφ_pow1
            rwa [hord_φ] at hdiv
          have hd_dvd_r : d ∣ r := by
            rcases hn_dvd with ⟨m, hm⟩
            refine ⟨m, ?_⟩
            have h1 : (r * (n / d)) = (d * m) * (n / d) := by
              calc r * (n / d) = n * m := hm
                _ = (d * (n / d)) * m := by rw [hdq_eq]
                _ = (d * m) * (n / d) := by ring
            exact Nat.eq_of_mul_eq_mul_right hq_pos h1
          rcases hd_dvd_r with ⟨t, hr_eq⟩
          rw [hφk_eq, hr_eq, pow_mul]
          exact Subgroup.npow_mem_zpowers (φ ^ d) t
        have hncard_le : (Hd : Set (GarlingAut L)).ncard ≤ (H : Set (GarlingAut L)).ncard := by
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
          change Nat.card Hd ≤ Nat.card H
          omega
        exact SetLike.ext' (Set.eq_of_subset_of_ncard_le hle hncard_le (Set.toFinite _))
      · rintro rfl
        exact hcard_Hd
    -- Apply FTGT (`theorem_11_8`) over `P = primeSubfield L`:
    obtain ⟨⟨hFTG_left, hFTG_right, _, _⟩, _, _⟩ := theorem_11_8 P hfinPL
    have hgamma_Fd : garlingGamma Fd = Hd := by
      have h1 := congrArg Subtype.val (hFTG_left ⟨Hd, hGP_top ▸ le_top⟩)
      exact h1
    obtain ⟨dFd, qFd, _, _, hmul_Fd, hcard_Fd0, hcardG_Fd⟩ := subfield_card_and_tower Fd
    have hqFd_eq : qFd = n / d := hcardG_Fd.symm.trans (hgamma_Fd ▸ hcard_Hd)
    have hdFd_eq : dFd = d := by
      apply Nat.eq_of_mul_eq_mul_right hq_pos
      calc dFd * (n / d) = dFd * qFd := by rw [hqFd_eq]
        _ = n := hmul_Fd
        _ = d * (n / d) := hdq_eq.symm
    have hcard_Fd : Nat.card Fd = p ^ d := hdFd_eq ▸ hcard_Fd0
    -- Uniqueness of `Fd` via FTGT (`hFTG_right`) + `huniq_Hd`:
    have hK₀_le : ∀ F : Subfield L, garlingPhi (garlingGamma P : Set (GarlingAut L)) ≤ F := by
      intro F
      have hgalP : IsGarlingGaloisExtension P L := corollary_1_to_theorem_12_1 L
      have hP_eq_K₀ : P = garlingPhi (garlingGamma P : Set (GarlingAut L)) :=
        (theorem_11_4 P hfinPL).1 hgalP |>.2.2
      rw [← hP_eq_K₀]
      dsimp [P]
      rw [primeSubfield_eq_bot]
      exact bot_le
    have huniq_Fd : ∀ F : Subfield L, Nat.card F = p ^ d ↔ F = Fd := by
      intro F
      constructor
      · intro hF_card
        obtain ⟨dF, qF, _, _, hmulF, hcardF0, hcardGF⟩ := subfield_card_and_tower F
        have hdF_eq : dF = d :=
          Nat.pow_right_injective hp.two_le (hcardF0.symm.trans hF_card)
        have hqF_eq : qF = n / d := by
          apply Nat.eq_of_mul_eq_mul_left hd_pos
          calc d * qF = dF * qF := by rw [hdF_eq]
            _ = n := hmulF
            _ = d * (n / d) := hdq_eq.symm
        have hGF_eq_Hd : garlingGamma F = Hd :=
          (huniq_Hd (garlingGamma F)).mp (hcardGF.trans hqF_eq)
        have hF_recover := congrArg Subtype.val (hFTG_right ⟨F, hK₀_le F⟩)
        change garlingPhi (garlingGamma F : Set (GarlingAut L)) = F at hF_recover
        rw [hGF_eq_Hd] at hF_recover
        exact hF_recover.symm
      · rintro rfl
        exact hcard_Fd
    have hex_nat : ∃! F : Subfield L, Nat.card F = p ^ d :=
      ⟨Fd, hcard_Fd, fun F hF => (huniq_Fd F).mp hF⟩
    have hset_iff : ∀ F : Subfield L, setOrder F = (p ^ d : ℕ) ↔ Nat.card F = p ^ d :=
      fun F => setOrder_eq_natCast_iff.trans (and_iff_right inferInstance)
    have hex_set : ∃! F : Subfield L, setOrder F = (p ^ d : ℕ) :=
      ⟨Fd, (hset_iff Fd).mpr hcard_Fd, fun F hF => (huniq_Fd F).mp ((hset_iff F).mp hF)⟩
    exact ⟨poly_X_pow_sub_X_dvd hp.pos hdn, poly_X_pow_sub_X_dvd hp.pos hdn,
      hcard_Hd, huniq_Hd, hcard_Fd, huniq_Fd, hex_nat, hex_set⟩

/-- **Exercise 12.11** (§12.5, printed p. 106 / PDF p. 114):
*"Suppose that `p` and `q` are primes and that `p < q`. Show that if `p` does not divide `q - 1`
then there is an extension `L : ℤ_q` which is a splitting field extension for each of the
polynomials `x^p - a` (`a` a non-zero element of `ℤ_q`)."* -/
theorem exercise_12_11 {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (_hpq : p < q) (hndvd : ¬ (p ∣ q - 1)) :
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod q) L),
      ∀ a : ZMod q, a ≠ 0 →
        IsGarlingSplittingFieldExtension (ZMod q) L (Polynomial.X ^ p - Polynomial.C a) := by
  classical
  have _ : Fact (Nat.Prime q) := ⟨hq⟩
  -- Step 1: `u ↦ u^p` is an injective, hence surjective, endomorphism of `(ZMod q)ˣ`.
  let powP : (ZMod q)ˣ →* (ZMod q)ˣ :=
    { toFun := fun u => u ^ p
      map_one' := one_pow p
      map_mul' := fun u v => mul_pow u v p }
  have hcard_units : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have hpowP_inj : Function.Injective powP := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hdvd_p : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hu
    rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | heq_p
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hdvd_card : orderOf u ∣ Fintype.card (ZMod q)ˣ := orderOf_dvd_card
      rw [heq_p, hcard_units] at hdvd_card
      exact hndvd hdvd_card
  have hpowP_surj : Function.Surjective powP := Finite.surjective_of_injective hpowP_inj
  -- Step 2: Take `L : ZMod q` to be a splitting field of `f₁ = X^p - 1` over `ZMod q`.
  let f₁ : (ZMod q)[X] := Polynomial.X ^ p - Polynomial.C 1
  obtain ⟨L, instFL, instAZL, hsf₁, _⟩ := theorem_7_3_natDegree f₁
  let _ : Field L := instFL
  let _ : Algebra (ZMod q) L := instAZL
  let ι := algebraMap (ZMod q) L
  obtain ⟨hsp₁, hadj₁⟩ := (isGarlingSplittingFieldExtension_iff (ZMod q) L f₁).mp hsf₁
  obtain ⟨n₁, c₁, ζ, hexp₁⟩ := hsf₁.1
  have hf₁_mon : f₁.Monic := Polynomial.monic_X_pow_sub_C 1 hp.ne_zero
  have hf₁_deg : f₁.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  have hc₁_eq1 : ι c₁ = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hexp₁
    have hprod_mon : (∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ζ i))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    rw [(hf₁_mon.map ι).leadingCoeff, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hprod_mon.leadingCoeff, mul_one] at hlc
    exact hlc.symm
  have hn₁_eq_p : n₁ = p := by
    have hd := congrArg Polynomial.natDegree hexp₁
    have hprod_deg : (∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ζ i))).natDegree = n₁ := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun i _ => Polynomial.natDegree_X_sub_C _),
        Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
    rw [hf₁_mon.natDegree_map, hf₁_deg, hc₁_eq1, map_one, one_mul, hprod_deg] at hd
    exact hd.symm
  have hexp₁_monic : f₁.map ι = ∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ζ i)) := by
    rw [hexp₁, hc₁_eq1, map_one, one_mul]
  refine ⟨L, instFL, instAZL, fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := hpowP_surj (Units.mk0 a ha)
  let b : ZMod q := (u : ZMod q)
  have hb0 : b ≠ 0 := u.ne_zero
  have hbp : b ^ p = a := by simpa [powP, b] using congrArg (Units.val : (ZMod q)ˣ → ZMod q) hu
  have hιb0 : ι b ≠ 0 := fun h0 => hb0 (ι.injective (h0.trans (map_zero ι).symm))
  let fa : (ZMod q)[X] := Polynomial.X ^ p - Polynomial.C a
  have hfa_mon : fa.Monic := Polynomial.monic_X_pow_sub_C a hp.ne_zero
  -- Step 3: Scale `X^p - 1 = ∏_i (X - ζ_i)` by `ι b` via `comp (C (ι b)⁻¹ * X)` to factor `X^p - C (ι a)`.
  have hfa_prod : fa.map ι = ∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ι b * ζ i)) := by
    let S : L[X] := Polynomial.C (ι b)⁻¹ * Polynomial.X
    have hcomp := congrArg (fun P : L[X] => Polynomial.C ((ι b) ^ p) * P.comp S) hexp₁_monic
    have hlhs : Polynomial.C ((ι b) ^ p) * (f₁.map ι).comp S = fa.map ι := by
      have hmap₁ : f₁.map ι = Polynomial.X ^ p - 1 := by simp [f₁, ι]
      have hmapa : fa.map ι = Polynomial.X ^ p - Polynomial.C (ι a) := by simp [fa, ι]
      have hab_inv : ι a * (ι b)⁻¹ ^ p = 1 := by
        rw [← hbp, map_pow, ← mul_pow, mul_inv_cancel₀ hιb0, one_pow]
      rw [hmap₁, hmapa]
      simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.one_comp,
        S, mul_pow, ← Polynomial.C_pow, mul_sub, mul_one, ← mul_assoc, ← map_mul,
        ← map_pow ι b p, hbp]
      rw [hab_inv, map_one, one_mul]
    have hrhs : Polynomial.C ((ι b) ^ p) *
        (∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ζ i))).comp S =
          ∏ i : Fin n₁, (Polynomial.X - Polynomial.C (ι b * ζ i)) := by
      rw [Polynomial.prod_comp]
      have hpow_prod : Polynomial.C ((ι b) ^ p) = ∏ _i : Fin n₁, Polynomial.C (ι b) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hn₁_eq_p, Polynomial.C_pow]
      rw [hpow_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, S, mul_sub,
        ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hιb0, map_one, one_mul]
    exact hlhs.symm.trans (hcomp.trans hrhs)
  rw [isGarlingSplittingFieldExtension_iff]
  refine ⟨?_, ?_⟩
  · rw [hfa_prod]
    exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  · apply le_antisymm le_top
    rw [← hadj₁]
    refine Algebra.adjoin_le ?_
    intro x hx
    have hx_pow : x ^ p = 1 := by
      rw [Polynomial.mem_rootSet_of_ne hf₁_mon.ne_zero] at hx
      have h1 : x ^ p - 1 = 0 := by simpa [f₁] using hx
      linear_combination h1
    have hbx_root : ι b * x ∈ fa.rootSet L := by
      rw [Polynomial.mem_rootSet_of_ne hfa_mon.ne_zero]
      have hmap_eval : Polynomial.aeval (ι b * x) fa = (ι b * x) ^ p - ι a := by simp [fa, ι]
      rw [hmap_eval, mul_pow, hx_pow, mul_one, ← map_pow, hbp, sub_self]
    have hbx_in : ι b * x ∈ Algebra.adjoin (ZMod q) (fa.rootSet L) :=
      Algebra.subset_adjoin hbx_root
    have hsmul := Subalgebra.smul_mem (Algebra.adjoin (ZMod q) (fa.rootSet L)) hbx_in b⁻¹
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hb0, map_one, one_mul] at hsmul
    exact hsmul

end Garling.Chapter12
