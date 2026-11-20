import Garling.Chapter01
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter07
import Garling.Chapter09
import Garling.Chapter10
import Garling.Chapter11
import Garling.Chapter12
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Chapter 15: Roots of unity

Formalization of Chapter 15 (*Roots of unity*, printed pp. 118–122 / PDF pp. 126–130) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
2-paragraph unnumbered chapter preamble, all three sections (`§15.1`–`§15.3`), all 5 main-text
theorem/lemma/corollary items (`Theorem 15.1`, `Lemma 15.2` — the sole numbered `Lemma` in the book —
`Theorem 15.3`, `Theorem 15.4`, and the unnumbered `Corollary` [to `Theorem 15.4`]), all 10 numbered
exercises (`Exercise 15.1`–`Exercise 15.10`), and all unnumbered prose definitions, derivations, and
worked examples in exact source order.

Note: Chapter 15 imports only `Garling.Chapter01`, `Chapter03`, `Chapter04`, `Chapter05`,
`Chapter07`, `Chapter09`, `Chapter10`, `Chapter11`, and `Chapter12` (zero Chapter 8 algebraic-closure
material and zero later chapters).
-/

namespace Garling.Chapter15

open Garling.Chapter01 Garling.Chapter03 Garling.Chapter04 Garling.Chapter05
open Garling.Chapter07 Garling.Chapter09 Garling.Chapter10 Garling.Chapter11 Garling.Chapter12
open scoped BigOperators Polynomial IntermediateField

universe u v w

/-! ## Chapter 15 Preamble (printed p. 118, PDF p. 126) -/

/-- Helper: in characteristic `p > 0`, `(X ^ q - 1) ^ (p ^ r) = X ^ (p ^ r * q) - 1` in `K[X]`. -/
private theorem X_pow_sub_one_pow_char_pow {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : 0 < p) (r q : ℕ) :
    (Polynomial.X ^ q - 1 : K[X]) ^ (p ^ r) = Polynomial.X ^ (p ^ r * q) - 1 := by
  have hp_prime : Nat.Prime p :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right (by omega) |> (hchar ▸ ·)
  have _ : Fact p.Prime := ⟨hp_prime⟩
  have _ : CharP K p := hchar ▸ inferInstance
  induction r with
  | zero =>
    rw [pow_zero, pow_one, one_mul]
  | succ r ih =>
    rw [pow_succ, pow_mul, ih, sub_pow_char, one_pow, ← pow_mul]
    congr 2
    ring

/-- Helper: for `n ≠ 0` over a field `F`, `(g ^ n).Splits ↔ g.Splits`. -/
private theorem splits_pow_iff_of_ne_zero {F : Type*} [Field F] {g : F[X]} {n : ℕ} (hn : n ≠ 0) :
    (g ^ n).Splits ↔ g.Splits := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [zero_pow hn]
  · refine ⟨fun h => h.of_dvd (pow_ne_zero n hg0) (dvd_pow_self g hn), fun h => h.pow n⟩

/-- Helper: in characteristic `p > 0` with `m = p ^ r * q`, `X ^ q - 1` splits over an extension `M`
iff `X ^ m - 1` splits over `M`. -/
private theorem garlingSplitsOver_char_pow_iff {K : Type*} (M : Type*) [Field K] [Field M]
    [Algebra K M] {p m r q : ℕ} (hchar : ringChar K = p) (hp0 : 0 < p) (hm : m = p ^ r * q) :
    GarlingSplitsOver K M (Polynomial.X ^ q - 1) ↔
    GarlingSplitsOver K M (Polynomial.X ^ m - 1) := by
  have hpoly : (Polynomial.X ^ m - 1 : K[X]) = (Polynomial.X ^ q - 1 : K[X]) ^ (p ^ r) := by
    rw [hm, X_pow_sub_one_pow_char_pow hchar hp0 r q]
  have hpow_ne0 : p ^ r ≠ 0 := pow_ne_zero r (by omega)
  rw [garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits, hpoly, Polynomial.map_pow,
    splits_pow_iff_of_ne_zero hpow_ne0]

/-- Unnumbered chapter-preamble prime-power characteristic reduction (printed p. 118 / PDF p. 126):
*"Suppose that `char K = p > 0` and that `m = p^r q`, where `p` does not divide `q`. Then in `K[x]`,
`x^m - 1 = (x^q - 1)^{p^r}`; thus a splitting field extension for `x^q - 1` is a splitting field
extension for `x^m - 1`: we need only consider the polynomial `x^q - 1`."*

Note: both the polynomial identity and the splitting-field equivalence hold for all `r, q : ℕ`
(with or without `¬ p ∣ q`); when `¬ p ∣ q`, the reduced exponent `q` additionally satisfies
Chapter 15's standing separability condition `¬ (ringChar K ∣ q)`. -/
theorem preamble_char_prime_pow_reduction {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {p m r q : ℕ}
    (hchar : ringChar K = p) (hp0 : 0 < p) (hm : m = p ^ r * q) :
    (Polynomial.X ^ m - 1 : K[X]) = (Polynomial.X ^ q - 1 : K[X]) ^ (p ^ r) ∧
    (∀ M : Type w, ∀ [Field M] [Algebra K M],
      GarlingSplitsOver K M (Polynomial.X ^ q - 1) ↔
      GarlingSplitsOver K M (Polynomial.X ^ m - 1)) ∧
    (IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - 1) ↔
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) ∧
    (¬ p ∣ q → ¬ (ringChar K ∣ q)) := by
  have hpoly : (Polynomial.X ^ m - 1 : K[X]) = (Polynomial.X ^ q - 1 : K[X]) ^ (p ^ r) := by
    rw [hm, X_pow_sub_one_pow_char_pow hchar hp0 r q]
  refine ⟨hpoly, fun M _ _ => garlingSplitsOver_char_pow_iff M hchar hp0 hm, ?_,
    fun hpq => hchar.symm ▸ hpq⟩
  unfold IsGarlingSplittingFieldExtension
  constructor
  · rintro ⟨hL, hmin⟩
    exact ⟨(garlingSplitsOver_char_pow_iff L hchar hp0 hm).mp hL,
      fun M hM hMs => hmin M hM ((garlingSplitsOver_char_pow_iff M hchar hp0 hm).mpr hMs)⟩
  · rintro ⟨hL, hmin⟩
    exact ⟨(garlingSplitsOver_char_pow_iff L hchar hp0 hm).mpr hL,
      fun M hM hMs => hmin M hM ((garlingSplitsOver_char_pow_iff M hchar hp0 hm).mp hMs)⟩

/-- Helper extracting `1 ≤ m` and `(m : K) ≠ 0` (`NeZero (m : K)`) from Chapter 15's standing
assumption `¬ (ringChar K ∣ m)` (printed p. 118 / PDF p. 126). Note that at `m = 0`, `ringChar K ∣ 0`
always holds (including `0 ∣ 0` when `ringChar K = 0`), so `¬ (ringChar K ∣ m)` automatically forces
`1 ≤ m`. -/
theorem pos_and_natCast_ne_zero_of_not_ringChar_dvd {K : Type*} [Field K] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m)) :
    1 ≤ m ∧ (m : K) ≠ 0 := by
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    have hz : m = 0 := by omega
    exact hchar (hz ▸ dvd_zero (ringChar K))
  have hm_ne0 : (m : K) ≠ 0 := fun h0 => hchar ((ringChar.spec K m).mp h0)
  exact ⟨hm_pos, hm_ne0⟩

/-- Unnumbered chapter-preamble derivative and distinct-roots deduction under Chapter 15's standing
hypothesis `¬ (ringChar K ∣ m)` (printed p. 118 / PDF p. 126):
*"For this reason, **in this chapter we shall suppose that `char K` does not divide `m`**. In this
case, `D(x^m - 1) = m x^{m - 1} ≠ 0`, and so `x^m - 1` has `m` distinct roots in a splitting field."* -/
theorem preamble_deriv_X_pow_sub_one_ne_zero {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m)) :
    1 ≤ m ∧
    garlingDeriv (Polynomial.X ^ m - 1 : K[X]) = Polynomial.C (m : K) * Polynomial.X ^ (m - 1) ∧
    garlingDeriv (Polynomial.X ^ m - 1 : K[X]) ≠ 0 ∧
    (Polynomial.X ^ m - 1 : K[X]).Separable ∧
    IsGarlingSeparablePoly (Polynomial.X ^ m - 1 : K[X]) ∧
    (IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1) →
      (garlingRootSet K L (Polynomial.X ^ m - 1)).ncard = m ∧
      IsGarlingGaloisExtension K L) := by
  obtain ⟨hm_pos, hm_ne0⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have hderiv :
      garlingDeriv (Polynomial.X ^ m - 1 : K[X]) =
        Polynomial.C (m : K) * Polynomial.X ^ (m - 1) := by
    rw [garlingDeriv_eq_derivative, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero]
  have hderiv_ne0 : garlingDeriv (Polynomial.X ^ m - 1 : K[X]) ≠ 0 := by
    rw [hderiv]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hm_ne0) (pow_ne_zero _ Polynomial.X_ne_zero)
  have hsep : (Polynomial.X ^ m - 1 : K[X]).Separable := by
    simpa using Polynomial.separable_X_pow_sub_C (1 : K) hm_ne0 one_ne_zero
  have hgsep : IsGarlingSeparablePoly (Polynomial.X ^ m - 1 : K[X]) :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly _).mp hsep).2.2
  refine ⟨hm_pos, hderiv, hderiv_ne0, hsep, hgsep, fun hsf => ?_⟩
  have hdeg : (Polynomial.X ^ m - 1 : K[X]).natDegree = m := by
    simpa using (Polynomial.natDegree_X_pow_sub_C (R := K) (n := m) (r := 1))
  have hncard : (garlingRootSet K L (Polynomial.X ^ m - 1)).ncard = m := by
    rw [ncard_garlingRootSet_eq_natDegree_of_separable hsep hsf, hdeg]
  have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨Polynomial.X ^ m - 1, hsf⟩
  have hsep_ext : IsGarlingSeparableExtension K L := corollary_3_to_theorem_10_3 hgsep hsf
  exact ⟨hncard, ⟨hfin, hnorm, hsep_ext⟩⟩

/-! ## §15.1 Cyclotomic polynomials (printed pp. 118–120, PDF pp. 126–128) -/

/-- The multiplicative subgroup `R ≤ Lˣ` of `m`th roots of unity in a field `L`
(§15.1, printed p. 118 / PDF p. 126: *"The set `R` of roots in `L` clearly forms a group under
multiplication"*). -/
def garlingRootsOfUnitySubgroup (L : Type*) [Field L] (m : ℕ) : Subgroup Lˣ where
  carrier := {u : Lˣ | (u : L) ^ m = 1}
  mul_mem' {a b} ha hb := by
    change ((a * b : Lˣ) : L) ^ m = 1
    rw [Units.val_mul, mul_pow, ha, hb, mul_one]
  one_mem' := by
    change ((1 : Lˣ) : L) ^ m = 1
    rw [Units.val_one, one_pow]
  inv_mem' {a} ha := by
    change ((a⁻¹ : Lˣ) : L) ^ m = 1
    rw [Units.val_inv_eq_inv_val, inv_pow, ha, inv_one]

@[simp]
theorem mem_garlingRootsOfUnitySubgroup_iff {L : Type*} [Field L] {m : ℕ} {u : Lˣ} :
    u ∈ garlingRootsOfUnitySubgroup L m ↔ (u : L) ^ m = 1 :=
  Iff.rfl

/-- §15.1 prose deduction from `Theorem 12.3` (printed p. 118 / PDF p. 126):
*"Suppose that `L : K` is a splitting field extension for `x^m - 1` over `K`. As `x^m - 1` has `m`
distinct roots, `L : K` is a Galois extension. The set `R` of roots in `L` clearly forms a group
under multiplication, and so, by Theorem 12.3, `R` is a cyclic group of order `m`."* -/
theorem section_15_1_roots_group_cyclic {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) :
    let R := garlingRootsOfUnitySubgroup L m
    IsGarlingGaloisExtension K L ∧
    Finite R ∧
    IsCyclic R ∧
    Nat.card R = m ∧
    setOrder R = (m : ℕ) ∧
    ∃ g : R, Subgroup.zpowers g = ⊤ ∧ orderOf g = m := by
  intro R
  obtain ⟨hm_pos, _, _, _, _, hsplit_props⟩ := preamble_deriv_X_pow_sub_one_ne_zero (L := L) hchar
  obtain ⟨hncard, hgal⟩ := hsplit_props hsf
  have hf_ne0 : (Polynomial.X ^ m - 1 : K[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < m) (1 : K)
  have hroot_iff : ∀ x : L, x ∈ garlingRootSet K L (Polynomial.X ^ m - 1) ↔ x ^ m = 1 := by
    intro x
    rw [mem_garlingRootSet_iff]
    simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, sub_eq_zero]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf_ne0, h⟩⟩
  let e : R ≃ garlingRootSet K L (Polynomial.X ^ m - 1) :=
    { toFun := fun u => ⟨(u.1 : L), (hroot_iff (u.1 : L)).mpr u.2⟩
      invFun := fun x =>
        have hx1 : x.1 ^ m = 1 := (hroot_iff x.1).mp x.2
        have hx0 : x.1 ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by omega : m ≠ 0)] at hx1
          exact zero_ne_one hx1
        ⟨Units.mk0 x.1 hx0, by
          rw [mem_garlingRootsOfUnitySubgroup_iff, Units.val_mk0]
          exact hx1⟩
      left_inv := fun u => by ext; rfl
      right_inv := fun x => by ext; rfl }
  have hfin_roots : (garlingRootSet K L (Polynomial.X ^ m - 1)).Finite := by
    rw [garlingRootSet_eq_rootSet K L _ hf_ne0]
    exact Finite.of_fintype _
  have _ : Finite (garlingRootSet K L (Polynomial.X ^ m - 1)) := hfin_roots
  have hfinR : Finite R := Finite.of_equiv _ e.symm
  have _ : Finite R := hfinR
  have hcardR : Nat.card R = m := by
    calc Nat.card R = Nat.card (garlingRootSet K L (Polynomial.X ^ m - 1)) := Nat.card_congr e
      _ = (garlingRootSet K L (Polynomial.X ^ m - 1)).ncard := (Set.ncard_def _).symm
      _ = m := hncard
  obtain ⟨hcyc, g, hg_top, hg_ord⟩ := theorem_12_3 L R
  have hsetOrder : setOrder R = (m : ℕ) := by
    let _ : Fintype R := Fintype.ofFinite R
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcardR]
  exact ⟨hgal, hfinR, hcyc, hcardR, hsetOrder, g, hg_top, hg_ord.trans hcardR⟩

/-- Garling's first inline prose characterization of a *primitive `m`th root of unity* via
generating `R` (§15.1, printed p. 118 / PDF p. 126: *"An element `ε` of `R` is called a **primitive
`m`th root of unity** if `ε` generates `R`."*). -/
def GeneratesGarlingRootsOfUnity (L : Type*) [Field L] (m : ℕ) (ε : L) : Prop :=
  ∃ u : garlingRootsOfUnitySubgroup L m, (u.1 : L) = ε ∧ Subgroup.zpowers u = ⊤

/-- Garling's explicit order characterization of a *primitive `m`th root of unity* (§15.1, printed
p. 118 / PDF p. 126, with printed spelling slip `ony` for `only`:
*"Thus an element `ε` of `L` is a primitive `m`th root of unity if and ony [sic] if `ε^m = 1` and
`ε^j ≠ 1` for `1 ≤ j < m`."*). -/
def IsGarlingPrimitiveRoot {R : Type*} [CommMonoid R] (m : ℕ) (ε : R) : Prop :=
  1 ≤ m ∧ ε ^ m = 1 ∧ ∀ j : ℕ, 1 ≤ j → j < m → ε ^ j ≠ 1

/-- Exact bridge between `IsGarlingPrimitiveRoot m ε` and Mathlib's `IsPrimitiveRoot ε m` for all
positive integers `1 ≤ m`. -/
theorem isGarlingPrimitiveRoot_iff_isPrimitiveRoot {R : Type*} [CommMonoid R] {m : ℕ} (hm : 1 ≤ m)
    (ε : R) :
    IsGarlingPrimitiveRoot m ε ↔ IsPrimitiveRoot ε m := by
  constructor
  · rintro ⟨_, hpow, hmin⟩
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hpow, fun l hl => ?_⟩
    by_cases hl0 : l = 0
    · rw [hl0]
      exact dvd_zero m
    · have hmod : ε ^ (l % m) = 1 := by
        have hdiv := Nat.div_add_mod l m
        have h1 : ε ^ l = (ε ^ m) ^ (l / m) * ε ^ (l % m) := by
          rw [← pow_mul, ← pow_add, hdiv]
        rw [hl, hpow, one_pow, one_mul] at h1
        exact h1.symm
      by_cases hrem0 : l % m = 0
      · exact Nat.dvd_of_mod_eq_zero hrem0
      · exfalso
        exact hmin (l % m) (by omega) (Nat.mod_lt l (by omega)) hmod
  · intro hprim
    refine ⟨hm, hprim.pow_eq_one, fun j hj1 hjlt hj => ?_⟩
    have hdvd : m ∣ j := hprim.dvd_of_pow_eq_one j hj
    have hle : m ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega

/-- Equivalence of p. 118's two characterizations of *primitive `m`th root of unity* inside any
splitting field extension `L : K` for `x^m - 1` under `¬ (ringChar K ∣ m)`: `ε` generates `R` if
and only if `ε^m = 1` and `ε^j ≠ 1` for `1 ≤ j < m`. -/
theorem generatesGarlingRootsOfUnity_iff_isGarlingPrimitiveRoot {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) (ε : L) :
    GeneratesGarlingRootsOfUnity L m ε ↔ IsGarlingPrimitiveRoot m ε := by
  obtain ⟨hm_pos, _⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  obtain ⟨_, hfinR, _, hcardR, _, _⟩ := section_15_1_roots_group_cyclic hchar hsf
  let _ : Finite (garlingRootsOfUnitySubgroup L m) := hfinR
  let _ : Fintype (garlingRootsOfUnitySubgroup L m) := Fintype.ofFinite _
  rw [isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos]
  constructor
  · rintro ⟨u, rfl, hutop⟩
    have hord_u : orderOf u = m := by
      rw [← Nat.card_zpowers u, hutop, Subgroup.card_top, hcardR]
    have hord_val : orderOf ((u.1 : Lˣ) : L) = m := by
      have hinj1 : Function.Injective
          (Subgroup.subtype (garlingRootsOfUnitySubgroup L m)) := Subtype.val_injective
      have h1 : orderOf (u.1 : Lˣ) = orderOf u := orderOf_injective _ hinj1 u
      have h2 : orderOf ((u.1 : Lˣ) : L) = orderOf (u.1 : Lˣ) := orderOf_units
      exact h2.trans (h1.trans hord_u)
    exact hord_val ▸ IsPrimitiveRoot.orderOf ((u.1 : Lˣ) : L)
  · intro hprim
    have hpow : ε ^ m = 1 := hprim.pow_eq_one
    have hε0 : ε ≠ 0 := hprim.ne_zero (by omega)
    let u : garlingRootsOfUnitySubgroup L m := ⟨Units.mk0 ε hε0, by simp [hpow]⟩
    have hord_u : orderOf u = m := by
      have hinj1 : Function.Injective
          (Subgroup.subtype (garlingRootsOfUnitySubgroup L m)) := Subtype.val_injective
      have h1 : orderOf (u.1 : Lˣ) = orderOf u := orderOf_injective _ hinj1 u
      have h2 : orderOf ((u.1 : Lˣ) : L) = orderOf (u.1 : Lˣ) := orderOf_units
      have h3 : orderOf ((u.1 : Lˣ) : L) = m := hprim.eq_orderOf.symm
      omega
    have hcard_zpow : Nat.card (Subgroup.zpowers u) = Nat.card (garlingRootsOfUnitySubgroup L m) := by
      rw [Nat.card_zpowers, hord_u, hcardR]
    exact ⟨u, rfl, Subgroup.eq_top_of_card_eq _ hcard_zpow⟩

/-- §15.1 prose examples of primitive roots of unity in `ℂ` (printed p. 118 / PDF p. 126):
*"For example, in `ℂ`, `i` and `-i` are the primitive fourth roots of unity: `-1` is the only
primitive second root of unity and `1` is the only first root of unity."* -/
theorem section_15_1_complex_prim_roots_examples :
    Complex.I ≠ -Complex.I ∧
    {z : ℂ | IsGarlingPrimitiveRoot 4 z} = {Complex.I, -Complex.I} ∧
    {z : ℂ | IsGarlingPrimitiveRoot 2 z} = {-1} ∧
    {z : ℂ | IsGarlingPrimitiveRoot 1 z} = {1} := by
  have hI_ne : Complex.I ≠ -Complex.I := by
    intro h
    have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h20 | hI0
    · norm_num at h20
    · exact Complex.I_ne_zero hI0
  refine ⟨hI_ne, ?_, ?_, ?_⟩
  · ext z
    change IsGarlingPrimitiveRoot 4 z ↔ z = Complex.I ∨ z = -Complex.I
    constructor
    · rintro ⟨_, hz4, hzmin⟩
      have hz2_ne1 : z ^ 2 ≠ 1 := hzmin 2 (by omega) (by omega)
      have hfac : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination hz4
      have hz2_add : z ^ 2 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hz2_ne1)
      have hfac2 : (z - Complex.I) * (z + Complex.I) = 0 := by
        calc (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
          _ = z ^ 2 + 1 := by simp [Complex.I_sq]
          _ = 0 := hz2_add
      rcases mul_eq_zero.mp hfac2 with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
    · rintro (rfl | rfl)
      · refine ⟨by omega, ?_, fun j hj1 hj4 => ?_⟩
        · calc Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
            _ = 1 := by norm_num [Complex.I_sq]
        · interval_cases j
          · intro h1
            have := congrArg Complex.im (by simpa using h1 : Complex.I = 1)
            norm_num at this
          · norm_num [Complex.I_sq]
          · intro h3
            have hcube : Complex.I ^ 3 = -Complex.I := by
              calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
                _ = -Complex.I := by simp [Complex.I_sq]
            rw [hcube] at h3
            have := congrArg Complex.im h3
            norm_num at this
      · refine ⟨by omega, ?_, fun j hj1 hj4 => ?_⟩
        · calc (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
            _ = 1 := by norm_num [Complex.I_sq]
        · interval_cases j
          · intro h1
            have := congrArg Complex.im (by simpa using h1 : -Complex.I = 1)
            norm_num at this
          · intro h2
            have hsq : (-Complex.I) ^ 2 = -1 := by
              calc (-Complex.I) ^ 2 = Complex.I ^ 2 := by ring
                _ = -1 := Complex.I_sq
            rw [hsq] at h2
            norm_num at h2
          · intro h3
            have hcube : (-Complex.I) ^ 3 = Complex.I := by
              calc (-Complex.I) ^ 3 = -(Complex.I ^ 2 * Complex.I) := by ring
                _ = Complex.I := by simp [Complex.I_sq]
            rw [hcube] at h3
            have := congrArg Complex.im h3
            norm_num at this
  · ext z
    change IsGarlingPrimitiveRoot 2 z ↔ z = -1
    constructor
    · rintro ⟨_, hz2, hzmin⟩
      have hz1 : z ≠ 1 := by simpa using hzmin 1 (by omega) (by omega)
      have hfac : (z - 1) * (z + 1) = 0 := by linear_combination hz2
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hz1))
    · rintro rfl
      refine ⟨by omega, by norm_num, fun j hj1 hj2 => ?_⟩
      interval_cases j
      norm_num
  · ext z
    change IsGarlingPrimitiveRoot 1 z ↔ z = 1
    constructor
    · rintro ⟨_, hz1, _⟩
      simpa using hz1
    · rintro rfl
      exact ⟨by omega, one_pow 1, fun j hj1 hjlt => by omega⟩

/-- §15.1 prose observation (printed p. 118 / PDF p. 126; OCR warning: `garling1986_pages.txt` l. 4427
corrupts `L = K(ε)` to `L = K(s)`):
*"Notice that if `ε` is a primitive `m`th root of unity then `L = K(ε)`."* -/
theorem section_15_1_simple_extension_of_prim_root {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (_hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1))
    {ε : L} (hε : IsGarlingPrimitiveRoot m ε) :
    IntermediateField.adjoin K ({ε} : Set L) = ⊤ ∧
    garlingFieldGenSubfield K ({ε} : Set L) = ⊤ ∧
    IsSimpleExtension K L := by
  have hm_pos : 1 ≤ m := hε.1
  have hprim : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
  let M : IntermediateField K L := IntermediateField.adjoin K ({ε} : Set L)
  have hε_mem : ε ∈ M := IntermediateField.mem_adjoin_simple_self K ε
  let εM : M := ⟨ε, hε_mem⟩
  have hprimM : IsPrimitiveRoot εM m := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hprim
  have hsplitsM : GarlingSplitsOver K M (Polynomial.X ^ m - 1) := by
    rw [garlingSplitsOver_iff_splits]
    simpa using Polynomial.X_pow_sub_one_splits hprimM
  have hM_top : M = ⊤ := by
    by_contra hne
    exact hsf.2 M hne hsplitsM
  have hsub_top : garlingFieldGenSubfield K ({ε} : Set L) = ⊤ := by
    rw [garlingFieldGenSubfield_eq_adjoin]
    change M.toSubfield = ⊤
    rw [hM_top]
    rfl
  exact ⟨hM_top, hsub_top, ⟨ε, hM_top⟩⟩

/-- Finite set of primitive `m`th roots of unity in a commutative domain `R` (`primitiveRoots m R`). -/
noncomputable def garlingPrimRootsFinset (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) :
    Finset R :=
  primitiveRoots m R

theorem mem_garlingPrimRootsFinset_iff {R : Type*} [CommRing R] [IsDomain R] {m : ℕ} (hm : 1 ≤ m)
    (ε : R) :
    ε ∈ garlingPrimRootsFinset R m ↔ IsGarlingPrimitiveRoot m ε := by
  rw [garlingPrimRootsFinset, mem_primitiveRoots (by omega : 0 < m),
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm ε).symm]

/-- Garling's literal §15.1 root-product definition of the *`m`th cyclotomic polynomial `Φ_m`*
(printed p. 118 / PDF p. 126; OCR warning: `garling1986_pages.txt` completely deletes the displayed
equation `Φ_m = ∏_ε (x - ε)` between ll. 4428 and 4429):
*"We now define the **`m`th cyclotomic polynomial `Φ_m`** to be `Φ_m = ∏_ε (x - ε)` where the product
is taken over all **primitive** `m`th roots of unity."* -/
noncomputable def garlingCyclotomicPoly (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) : R[X] :=
  ∏ ε ∈ garlingPrimRootsFinset R m, (Polynomial.X - Polynomial.C ε)

theorem garlingCyclotomicPoly_eq_cyclotomic' (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) :
    garlingCyclotomicPoly R m = Polynomial.cyclotomic' m R :=
  rfl

theorem garlingCyclotomicPoly_monic (R : Type*) [CommRing R] [IsDomain R] (m : ℕ) :
    (garlingCyclotomicPoly R m).Monic :=
  Polynomial.cyclotomic'.monic m R

/-- Helper extracting existence of a primitive `m`th root of unity in `L` whenever `L : K` is a
splitting field extension for `x^m - 1` under `¬ (ringChar K ∣ m)`. -/
theorem exists_isGarlingPrimitiveRoot_of_splittingField {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) :
    ∃ ε : L, IsGarlingPrimitiveRoot m ε := by
  obtain ⟨_, _, _, _, _, g, hg_top, _⟩ := section_15_1_roots_group_cyclic hchar hsf
  exact ⟨(g.1 : L),
    (generatesGarlingRootsOfUnity_iff_isGarlingPrimitiveRoot hchar hsf (g.1 : L)).mp
      ⟨g, rfl, hg_top⟩⟩

/-- §15.1 divisor-product identity (printed p. 119 / PDF p. 127):
*"An element `α` in `L` is a root of `x^m - 1` if and only if it is a primitive `d`th root of unity
for some `d` which divides `m`: thus `x^m - 1 = ∏_{d ∣ m} Φ_d`."* -/
theorem section_15_1_X_pow_sub_one_eq_prod_cyclotomic {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) :
    (∀ α : L, α ^ m = 1 ↔ ∃! d : ℕ, d ∣ m ∧ IsGarlingPrimitiveRoot d α) ∧
    (Polynomial.X ^ m - 1 : L[X]) = ∏ d ∈ m.divisors, garlingCyclotomicPoly L d := by
  obtain ⟨hm_pos, _⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  obtain ⟨ε, hε⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf
  have hprim : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
  refine ⟨fun α => ?_, ?_⟩
  · constructor
    · intro hα
      have hfin : IsOfFinOrder α := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, by omega, hα⟩
      let d := orderOf α
      have hd_pos : 1 ≤ d := hfin.orderOf_pos
      have hd_dvd : d ∣ m := orderOf_dvd_of_pow_eq_one hα
      have hd_prim : IsGarlingPrimitiveRoot d α :=
        (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hd_pos α).mpr (IsPrimitiveRoot.orderOf α)
      refine ⟨d, ⟨hd_dvd, hd_prim⟩, fun d' ⟨_, hd'_prim⟩ => ?_⟩
      have hd'_pos : 1 ≤ d' := hd'_prim.1
      have hd'_ip : IsPrimitiveRoot α d' :=
        (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hd'_pos α).mp hd'_prim
      exact hd'_ip.eq_orderOf
    · rintro ⟨d, ⟨hd_dvd, hd_prim⟩, _⟩
      rcases hd_dvd with ⟨k, rfl⟩
      rw [pow_mul, hd_prim.2.1, one_pow]
  · symm
    simpa [garlingCyclotomicPoly_eq_cyclotomic'] using
      Polynomial.prod_cyclotomic'_eq_X_pow_sub_one (by omega : 0 < m) hprim

/-- §15.1 prose examples of cyclotomic polynomials in `ℂ[x]` (printed p. 119 / PDF p. 127):
`Φ_1 = x - 1`, `Φ_2 = x + 1`, `Φ_3 = (x - ω)(x - ω^2) = x^2 + x + 1`,
`Φ_4 = (x - i)(x + i) = x^2 + 1`, and `x^4 - 1 = (x - 1)(x + 1)(x^2 + 1) = Φ_1 Φ_2 Φ_4`. -/
theorem section_15_1_complex_cyclotomic_examples :
    garlingCyclotomicPoly ℂ 1 = Polynomial.X - 1 ∧
    garlingCyclotomicPoly ℂ 2 = Polynomial.X + 1 ∧
    garlingCyclotomicPoly ℂ 3 =
      (Polynomial.X - Polynomial.C omegaCubeRoot) *
        (Polynomial.X - Polynomial.C (omegaCubeRoot ^ 2)) ∧
    garlingCyclotomicPoly ℂ 3 = Polynomial.X ^ 2 + Polynomial.X + 1 ∧
    garlingCyclotomicPoly ℂ 4 =
      (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I) ∧
    garlingCyclotomicPoly ℂ 4 = Polynomial.X ^ 2 + 1 ∧
    (Polynomial.X ^ 4 - 1 : ℂ[X]) =
      (Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + 1) ∧
    (Polynomial.X ^ 4 - 1 : ℂ[X]) =
      garlingCyclotomicPoly ℂ 1 * garlingCyclotomicPoly ℂ 2 * garlingCyclotomicPoly ℂ 4 := by
  have h1 : garlingCyclotomicPoly ℂ 1 = Polynomial.cyclotomic 1 ℂ :=
    (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp 1 one_ne_zero)).symm
  have h2 : garlingCyclotomicPoly ℂ 2 = Polynomial.cyclotomic 2 ℂ :=
    (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp 2 (by omega))).symm
  have h3 : garlingCyclotomicPoly ℂ 3 = Polynomial.cyclotomic 3 ℂ :=
    (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp 3 (by omega))).symm
  have h4 : garlingCyclotomicPoly ℂ 4 = Polynomial.cyclotomic 4 ℂ :=
    (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp 4 (by omega))).symm
  have hphi1 : garlingCyclotomicPoly ℂ 1 = Polynomial.X - 1 := by
    rw [h1, Polynomial.cyclotomic_one]
  have hphi2 : garlingCyclotomicPoly ℂ 2 = Polynomial.X + 1 := by
    rw [h2, Polynomial.cyclotomic_two]
  have hphi3 : garlingCyclotomicPoly ℂ 3 = Polynomial.X ^ 2 + Polynomial.X + 1 := by
    rw [h3, Polynomial.cyclotomic_three]
  have hphi4 : garlingCyclotomicPoly ℂ 4 = Polynomial.X ^ 2 + 1 := by
    rw [h4]
    have h4_eq : Polynomial.cyclotomic (2 ^ (1 + 1)) ℂ =
        ∑ i ∈ Finset.range 2, (Polynomial.X ^ (2 ^ 1) : ℂ[X]) ^ i :=
      Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two
    simpa [Finset.sum_range_succ, add_comm] using h4_eq
  obtain ⟨homega_quad, homega3, _⟩ := omegaCubeRoot_props
  have hphi3_fac :
      (Polynomial.X - Polynomial.C omegaCubeRoot) *
        (Polynomial.X - Polynomial.C (omegaCubeRoot ^ 2)) =
        Polynomial.X ^ 2 + Polynomial.X + 1 := by
    have hsum : omegaCubeRoot + omegaCubeRoot ^ 2 = -1 := by linear_combination homega_quad
    have hprod : omegaCubeRoot * omegaCubeRoot ^ 2 = 1 := by
      calc omegaCubeRoot * omegaCubeRoot ^ 2 = omegaCubeRoot ^ 3 := by ring
        _ = 1 := homega3
    calc (Polynomial.X - Polynomial.C omegaCubeRoot) *
          (Polynomial.X - Polynomial.C (omegaCubeRoot ^ 2))
        = Polynomial.X ^ 2 - Polynomial.C (omegaCubeRoot + omegaCubeRoot ^ 2) * Polynomial.X +
            Polynomial.C (omegaCubeRoot * omegaCubeRoot ^ 2) := by
          simp only [map_add, map_mul]
          ring
      _ = Polynomial.X ^ 2 + Polynomial.X + 1 := by
          rw [hsum, hprod, map_neg, map_one]
          ring
  have hphi4_fac :
      (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I) =
        Polynomial.X ^ 2 + 1 := by
    calc (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X + Polynomial.C Complex.I)
        = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2) := by
          rw [pow_two (Complex.I : ℂ), map_mul]
          ring
      _ = Polynomial.X ^ 2 + 1 := by simp [Complex.I_sq]
  have hx4 : (Polynomial.X ^ 4 - 1 : ℂ[X]) =
      (Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + 1) := by ring
  refine ⟨hphi1, hphi2, hphi3.trans hphi3_fac.symm, hphi3, hphi4.trans hphi4_fac.symm, hphi4,
    hx4, ?_⟩
  rw [hphi1, hphi2, hphi4, hx4]

/-- Private polynomial long-division descent helper implementing Garling's coefficient induction in
`Lemma 15.2` (printed p. 119 / PDF p. 127) ahead of `Theorem 15.1` so `theorem_15_1` and `lemma_15_2`
appear in exact printed source order. -/
private theorem coeff_mem_subring_of_mul_leadingCoeff_unit {B : Type*} [CommRing B]
    (A : Subring B) {f q g : B[X]}
    (hfA : ∀ k, f.coeff k ∈ A) (hgA : ∀ k, g.coeff k ∈ A)
    {u : B} (huA : u ∈ A) (hug : u * g.leadingCoeff = 1)
    (hfqg : f = q * g) :
    ∀ j : ℕ, q.coeff j ∈ A := by
  by_cases hq0 : q = 0
  · subst hq0
    intro j
    rw [Polynomial.coeff_zero]
    exact A.zero_mem
  · let m := q.natDegree
    let n := g.natDegree
    suffices hdesc : ∀ d : ℕ, ∀ j : ℕ, m - d ≤ j → q.coeff j ∈ A by
      intro j
      exact hdesc m j (by simp)
    intro d
    induction d with
    | zero =>
      intro j hj
      by_cases hgt : m < j
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
        exact A.zero_mem
      · have hjm : j = m := by omega
        subst hjm
        have htop : f.coeff (m + n) = q.coeff m * g.leadingCoeff := by
          rw [hfqg, Polynomial.coeff_mul]
          have hmem : (m, n) ∈ Finset.antidiagonal (m + n) := Finset.mem_antidiagonal.mpr rfl
          rw [← Finset.add_sum_erase _ _ hmem]
          have hrest : ∑ x ∈ (Finset.antidiagonal (m + n)).erase (m, n),
              q.coeff x.1 * g.coeff x.2 = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            rcases Finset.mem_erase.mp hx with ⟨hne, hsum⟩
            rw [Finset.mem_antidiagonal] at hsum
            by_cases hx1 : m < x.1
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx1, zero_mul]
            · have hx2 : n < x.2 := by
                by_contra hle
                apply hne
                ext <;> omega
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx2, mul_zero]
          rw [hrest, add_zero]
          rfl
        have hqm : q.coeff m = f.coeff (m + n) * u := by
          calc q.coeff m = q.coeff m * (u * g.leadingCoeff) := by rw [hug, mul_one]
            _ = (q.coeff m * g.leadingCoeff) * u := by ring
            _ = f.coeff (m + n) * u := by rw [← htop]
        rw [hqm]
        exact A.mul_mem (hfA (m + n)) huA
    | succ d ih =>
      intro j hj
      by_cases hjprev : m - d ≤ j
      · exact ih j hjprev
      · have hjeq : j = m - (d + 1) := by omega
        have hlt_m : j < m := by omega
        have hcoeff : f.coeff (j + n) = q.coeff j * g.leadingCoeff +
            ∑ x ∈ (Finset.antidiagonal (j + n)).erase (j, n), q.coeff x.1 * g.coeff x.2 := by
          rw [hfqg, Polynomial.coeff_mul]
          have hmem : (j, n) ∈ Finset.antidiagonal (j + n) := Finset.mem_antidiagonal.mpr rfl
          rw [← Finset.add_sum_erase _ _ hmem]
          rfl
        have hsum_mem :
            (∑ x ∈ (Finset.antidiagonal (j + n)).erase (j, n), q.coeff x.1 * g.coeff x.2) ∈ A := by
          refine A.sum_mem fun x hx => ?_
          rcases Finset.mem_erase.mp hx with ⟨hne, hsum⟩
          rw [Finset.mem_antidiagonal] at hsum
          by_cases hx2 : n < x.2
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx2, mul_zero]
            exact A.zero_mem
          · have hx1 : j < x.1 := by
              by_contra hle
              apply hne
              ext <;> omega
            exact A.mul_mem (ih x.1 (by omega)) (hgA x.2)
        have hprod_mem : q.coeff j * g.leadingCoeff ∈ A := by
          have hsub : q.coeff j * g.leadingCoeff = f.coeff (j + n) -
              ∑ x ∈ (Finset.antidiagonal (j + n)).erase (j, n), q.coeff x.1 * g.coeff x.2 := by
            rw [hcoeff, add_sub_cancel_right]
          rw [hsub]
          exact A.sub_mem (hfA (j + n)) hsum_mem
        have hqj : q.coeff j = (q.coeff j * g.leadingCoeff) * u := by
          calc q.coeff j = q.coeff j * (u * g.leadingCoeff) := by rw [hug, mul_one]
            _ = (q.coeff j * g.leadingCoeff) * u := by ring
        rw [hqj]
        exact A.mul_mem hprod_mem huA

/-- Helper reconstructing `q₀ : R[X]` with `q₀.map φ = q` when every coefficient of `q : S[X]` lies
in `φ.range`. -/
private theorem exists_poly_map_eq_of_coeff_mem_range {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (q : S[X]) (hcoeff : ∀ j : ℕ, q.coeff j ∈ φ.range) :
    ∃ q₀ : R[X], q₀.map φ = q := by
  choose c hc using hcoeff
  refine ⟨∑ j ∈ q.support, Polynomial.monomial j (c j), ?_⟩
  ext j
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hj : j ∈ q.support
  · rw [Finset.sum_eq_single j
      (fun b _ hbj => if_neg hbj)
      (fun h => absurd hj h),
      if_pos rfl]
    exact hc j
  · rw [Finset.sum_eq_zero (fun b hb =>
      if_neg (fun hbj : b = j => hj (hbj ▸ hb))),
      Polynomial.notMem_support_iff.mp hj, map_zero]

/-- **Theorem 15.1** (§15.1, printed p. 119 / PDF p. 127; OCR warning: `garling1986_pages.txt` l. 4444
corrupts `If K_0 = ℚ` to `If K 0 =0`):
*"`Φ_m ∈ K_0[x]`, where `K_0` is the prime subfield of `K`. If `K_0 = ℚ` then `Φ_m ∈ ℤ[x]`."*

Proved directly following Garling's printed inductive argument on p. 119 via `x^m - 1 = ∏_{d ∣ m} Φ_d`
and long-division coefficient descent (`Lemma 15.2 (i)` onto `K_0` and `Lemma 15.2 (ii)` onto `ℤ`),
under p. 118's chapter-wide standing assumption `¬ (ringChar K ∣ m)`. Also identifies the descended
polynomial with `Polynomial.cyclotomic m`. -/
theorem theorem_15_1 {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) :
    (∃ P₀ : (primeSubfield K)[X],
      P₀.map ((algebraMap K L).comp (primeSubfield K).subtype) = garlingCyclotomicPoly L m) ∧
    (∀ j : ℕ, ∃ c ∈ primeSubfield K,
      (garlingCyclotomicPoly L m).coeff j = algebraMap K L c) ∧
    ((Nonempty (primeSubfield K ≃+* ℚ) ∨ ringChar K = 0) →
      ∃ P_int : ℤ[X], P_int.map (Int.castRingHom L) = garlingCyclotomicPoly L m ∧
        ∀ j : ℕ, (garlingCyclotomicPoly L m).coeff j ∈ Set.range (Int.cast : ℤ → L)) ∧
    garlingCyclotomicPoly L m = (Polynomial.cyclotomic m K).map (algebraMap K L) := by
  obtain ⟨hm_pos, _⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  obtain ⟨ε, hε⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf
  have hprim : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
  have hall_div_int : ∀ k : ℕ, k ≤ m → k ∣ m →
      ∀ j : ℕ, (garlingCyclotomicPoly L k).coeff j ∈ (⊥ : Subring L) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro _ hkdvd
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hkdvd (by omega)
      obtain ⟨c, hc⟩ := hkdvd
      have hkdvd' : k ∣ m := ⟨c, hc⟩
      have hprim_k : IsPrimitiveRoot (ε ^ c) k := by
        refine hprim.pow (by omega) ?_
        rw [mul_comm]
        exact hc
      have hprod_k :
          ∏ d ∈ k.divisors, garlingCyclotomicPoly L d = (Polynomial.X ^ k - 1 : L[X]) := by
        simpa [garlingCyclotomicPoly_eq_cyclotomic'] using
          Polynomial.prod_cyclotomic'_eq_X_pow_sub_one hk_pos hprim_k
      rw [← Nat.cons_self_properDivisors hk_pos.ne', Finset.prod_cons] at hprod_k
      let g : L[X] := ∏ d ∈ k.properDivisors, garlingCyclotomicPoly L d
      have hg_monic : g.Monic :=
        Polynomial.monic_prod_of_monic _ _ fun d _ => garlingCyclotomicPoly_monic L d
      have hg_bot : ∀ j : ℕ, g.coeff j ∈ (⊥ : Subring L) := by
        suffices hprod_mem : ∀ s : Finset ℕ, s ⊆ k.properDivisors →
            ∀ j : ℕ, (∏ d ∈ s, garlingCyclotomicPoly L d).coeff j ∈ (⊥ : Subring L) from
          hprod_mem k.properDivisors Finset.Subset.rfl
        intro s hs
        induction s using Finset.cons_induction with
        | empty =>
          intro j
          rw [Finset.prod_empty, Polynomial.coeff_one]
          split_ifs
          · exact (⊥ : Subring L).one_mem
          · exact (⊥ : Subring L).zero_mem
        | cons d s hd ihs =>
          intro j
          rw [Finset.prod_cons, Polynomial.coeff_mul]
          have hd_prop : d ∈ k.properDivisors := hs (Finset.mem_cons_self d s)
          rcases Nat.mem_properDivisors.mp hd_prop with ⟨hddvd, hdlt⟩
          have hdm : d ∣ m := dvd_trans hddvd hkdvd'
          have hd_coeff := ih d hdlt (by omega) hdm
          have hs_coeff := ihs (Finset.Subset.trans (Finset.subset_cons _) hs)
          exact (⊥ : Subring L).sum_mem fun x _ =>
            (⊥ : Subring L).mul_mem (hd_coeff x.1) (hs_coeff x.2)
      have hf_bot : ∀ j : ℕ, (Polynomial.X ^ k - 1 : L[X]).coeff j ∈ (⊥ : Subring L) := by
        intro j
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
        refine (⊥ : Subring L).sub_mem ?_ ?_
        · split_ifs
          · exact (⊥ : Subring L).one_mem
          · exact (⊥ : Subring L).zero_mem
        · split_ifs
          · exact (⊥ : Subring L).one_mem
          · exact (⊥ : Subring L).zero_mem
      exact coeff_mem_subring_of_mul_leadingCoeff_unit (⊥ : Subring L) hf_bot hg_bot
        (⊥ : Subring L).one_mem (by rw [hg_monic.leadingCoeff, mul_one]) hprod_k.symm
  have hm_bot : ∀ j : ℕ, (garlingCyclotomicPoly L m).coeff j ∈ (⊥ : Subring L) :=
    hall_div_int m le_rfl dvd_rfl
  have hm_range : ∀ j : ℕ, (garlingCyclotomicPoly L m).coeff j ∈ (Int.castRingHom L).range := by
    intro j
    rcases Subring.mem_bot.mp (hm_bot j) with ⟨z, hz⟩
    exact ⟨z, hz⟩
  obtain ⟨P_int, hP_int⟩ := exists_poly_map_eq_of_coeff_mem_range (Int.castRingHom L) _ hm_range
  let ιK₀ : primeSubfield K →+* L := (algebraMap K L).comp (primeSubfield K).subtype
  let P₀ : (primeSubfield K)[X] := P_int.map (Int.castRingHom (primeSubfield K))
  have hP₀ : P₀.map ιK₀ = garlingCyclotomicPoly L m := by
    rw [Polynomial.map_map]
    have hhom : ιK₀.comp (Int.castRingHom (primeSubfield K)) = Int.castRingHom L :=
      Subsingleton.elim _ _
    rw [hhom, hP_int]
  have hK₀_coeffs : ∀ j : ℕ, ∃ c ∈ primeSubfield K,
      (garlingCyclotomicPoly L m).coeff j = algebraMap K L c := by
    intro j
    refine ⟨(P₀.coeff j).1, (P₀.coeff j).2, ?_⟩
    rw [← hP₀, Polynomial.coeff_map]
    rfl
  have hcyc_eq : garlingCyclotomicPoly L m = (Polynomial.cyclotomic m K).map (algebraMap K L) := by
    rw [Polynomial.map_cyclotomic, garlingCyclotomicPoly_eq_cyclotomic',
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.cyclotomic']
  refine ⟨⟨P₀, hP₀⟩, hK₀_coeffs, fun _ => ⟨P_int, hP_int, fun j => ?_⟩, hcyc_eq⟩
  exact ⟨P_int.coeff j, by rw [← hP_int, Polynomial.coeff_map]; rfl⟩

/-- Unconditional companion to `Theorem 15.1` on `Polynomial.cyclotomic m K` across **all** `m : ℕ`
(including `m = 0`, where `cyclotomic 0 K = 1`) and **all** fields `K`. -/
theorem theorem_15_1_cyclotomic (K : Type u) [Field K] (m : ℕ) :
    (∃ P₀ : (primeSubfield K)[X],
      P₀.map (primeSubfield K).subtype = Polynomial.cyclotomic m K) ∧
    (∃ P_int : ℤ[X], P_int.map (Int.castRingHom K) = Polynomial.cyclotomic m K) := by
  refine ⟨⟨Polynomial.cyclotomic m (primeSubfield K), Polynomial.map_cyclotomic m _⟩,
    ⟨Polynomial.cyclotomic m ℤ, Polynomial.map_cyclotomic_int m K⟩⟩

/-- **Lemma 15.2** (§15.1, printed p. 119 / PDF p. 127 — the **sole** numbered `Lemma` in Garling
1986):
*"(i) If `L : K` is an extension, if `q ∈ L[x]` and if there exist non-zero `f` and `g` in `K[x]`
such that `f = q g`, then `q ∈ K[x]`.*
*(ii) Suppose that `K` is the field of fractions of an integral domain `R`, that `q ∈ K[x]` and
that there exist monic `f` and `g` in `R[x]` such that `f = q g`. Then `q ∈ R[x]`."*

Proved directly via Garling's downward coefficient induction (`coeff_mem_subring_of_mul_leadingCoeff_unit`). -/
theorem lemma_15_2 :
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
      (q : L[X]) (f g : K[X]),
      f ≠ 0 → g ≠ 0 →
      f.map (algebraMap K L) = q * g.map (algebraMap K L) →
      ∃ q₀ : K[X], q₀.map (algebraMap K L) = q ∧ f = q₀ * g) ∧
    (∀ {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
      [IsFractionRing R K] (q : K[X]) (f g : R[X]),
      f.Monic → g.Monic →
      f.map (algebraMap R K) = q * g.map (algebraMap R K) →
      ∃ q₀ : R[X], q₀.Monic ∧ q₀.map (algebraMap R K) = q ∧ f = q₀ * g) := by
  refine ⟨?_, ?_⟩
  · intro K L _ _ _ q f g _ hg0 hfqg
    let A : Subring L := (algebraMap K L).range
    have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
    have hfA : ∀ k, (f.map (algebraMap K L)).coeff k ∈ A := fun k => by
      rw [Polynomial.coeff_map]
      exact ⟨f.coeff k, rfl⟩
    have hgA : ∀ k, (g.map (algebraMap K L)).coeff k ∈ A := fun k => by
      rw [Polynomial.coeff_map]
      exact ⟨g.coeff k, rfl⟩
    have hglc_ne0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    let u : L := algebraMap K L (g.leadingCoeff)⁻¹
    have huA : u ∈ A := ⟨(g.leadingCoeff)⁻¹, rfl⟩
    have hug : u * (g.map (algebraMap K L)).leadingCoeff = 1 := by
      rw [Polynomial.leadingCoeff_map_of_injective hinj, ← map_mul, inv_mul_cancel₀ hglc_ne0,
        map_one]
    have hqA := coeff_mem_subring_of_mul_leadingCoeff_unit A hfA hgA huA hug hfqg
    obtain ⟨q₀, hq₀_map⟩ := exists_poly_map_eq_of_coeff_mem_range (algebraMap K L) q hqA
    have hfq₀g : f = q₀ * g := by
      apply Polynomial.map_injective (algebraMap K L) hinj
      rw [Polynomial.map_mul, hq₀_map, hfqg]
    exact ⟨q₀, hq₀_map, hfq₀g⟩
  · intro R K _ _ _ _ _ q f g hf_mon hg_mon hfqg
    let A : Subring K := (algebraMap R K).range
    have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
    have hfA : ∀ k, (f.map (algebraMap R K)).coeff k ∈ A := fun k => by
      rw [Polynomial.coeff_map]
      exact ⟨f.coeff k, rfl⟩
    have hgA : ∀ k, (g.map (algebraMap R K)).coeff k ∈ A := fun k => by
      rw [Polynomial.coeff_map]
      exact ⟨g.coeff k, rfl⟩
    have hug : (1 : K) * (g.map (algebraMap R K)).leadingCoeff = 1 := by
      rw [one_mul, (hg_mon.map (algebraMap R K)).leadingCoeff]
    have hqA := coeff_mem_subring_of_mul_leadingCoeff_unit A hfA hgA A.one_mem hug hfqg
    obtain ⟨q₀, hq₀_map⟩ := exists_poly_map_eq_of_coeff_mem_range (algebraMap R K) q hqA
    have hfq₀g : f = q₀ * g := by
      apply Polynomial.map_injective (algebraMap R K) hinj
      rw [Polynomial.map_mul, hq₀_map, hfqg]
    have hq₀_mon : q₀.Monic := by
      have hlc := congrArg Polynomial.leadingCoeff hfq₀g
      rw [hf_mon.leadingCoeff, Polynomial.leadingCoeff_mul_monic hg_mon] at hlc
      exact hlc.symm
    exact ⟨q₀, hq₀_mon, hq₀_map, hfq₀g⟩

/-- Subfield and `FractionRing R` / `IsGarlingIntegralDomain R` companion to `Lemma 15.2`. -/
theorem lemma_15_2_subfield {L : Type u} [Field L] (F : Subfield L) (q f g : L[X])
    (hfF : ∀ k, f.coeff k ∈ F) (hgF : ∀ k, g.coeff k ∈ F) (hg0 : g ≠ 0) (hfqg : f = q * g) :
    ∀ k, q.coeff k ∈ F := by
  have hglc_mem : g.leadingCoeff ∈ F := hgF g.natDegree
  have hglc_ne0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  exact coeff_mem_subring_of_mul_leadingCoeff_unit F.toSubring hfF hgF (F.inv_mem hglc_mem)
    (inv_mul_cancel₀ hglc_ne0) hfqg

/-- **Exercise 15.1** (§15.1, printed p. 119 / PDF p. 127; OCR warning: `garling1986_pages.txt` l. 4464
mangles `m ∏_{p ∣ m} ((p - 1)/p)` to `mOplm((p-1)/p)`):
*"Show that the degree of `Φ_m` is `m ∏_{p ∣ m} ((p - 1)/p)`, where the product is taken over all
primes `p` which divide `m`."*

Proved both for Garling's §15.1 root-product `garlingCyclotomicPoly L m` (using Chapter 3's
`garlingDegree`) under `¬ (ringChar K ∣ m)` and unconditionally for `Polynomial.cyclotomic m R`
across all `[Ring R] [Nontrivial R]` and all `m : ℕ`. -/
theorem exercise_15_1 :
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {m : ℕ},
      ¬ (ringChar K ∣ m) →
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1) →
      ((garlingDegree (garlingCyclotomicPoly L m)
          (garlingCyclotomicPoly_monic L m).ne_zero : ℕ) : ℚ) =
        (m : ℚ) * ∏ p ∈ m.primeFactors, (((p : ℚ) - 1) / (p : ℚ))) ∧
    (∀ (R : Type u) [Ring R] [Nontrivial R] (m : ℕ),
      ((garlingDegree (Polynomial.cyclotomic m R)
          (Polynomial.cyclotomic_ne_zero m R) : ℕ) : ℚ) =
        (m : ℚ) * ∏ p ∈ m.primeFactors, (((p : ℚ) - 1) / (p : ℚ)) ∧
      ((Polynomial.cyclotomic m R).natDegree : ℚ) =
        (m : ℚ) * ∏ p ∈ m.primeFactors, (((p : ℚ) - 1) / (p : ℚ))) := by
  have htot_rat : ∀ m : ℕ,
      (Nat.totient m : ℚ) = (m : ℚ) * ∏ p ∈ m.primeFactors, (((p : ℚ) - 1) / (p : ℚ)) := by
    intro m
    rw [Nat.totient_eq_mul_prod_factors m]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pos : 0 < p := Nat.pos_of_mem_primeFactors hp
    have hp_ne0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
    field_simp [hp_ne0]
  refine ⟨?_, ?_⟩
  · intro K L _ _ _ m hchar hsf
    obtain ⟨_, _, _, hcyc_eq⟩ := theorem_15_1 hchar hsf
    have hdeg : garlingDegree (garlingCyclotomicPoly L m)
        (garlingCyclotomicPoly_monic L m).ne_zero = Nat.totient m := by
      change (garlingCyclotomicPoly L m).natDegree = Nat.totient m
      rw [hcyc_eq, Polynomial.map_cyclotomic, Polynomial.natDegree_cyclotomic]
    rw [hdeg, htot_rat m]
  · intro R _ _ m
    have hdeg : (Polynomial.cyclotomic m R).natDegree = Nat.totient m :=
      Polynomial.natDegree_cyclotomic m R
    exact ⟨by change ((Polynomial.cyclotomic m R).natDegree : ℚ) = _; rw [hdeg, htot_rat m],
      by rw [hdeg, htot_rat m]⟩

/-- Counterexample to the literal `n = 1` case of **Exercise 15.2** (`QUEUE.md` fidelity hold;
§15.1, printed p. 120 / PDF p. 128): `n = 1` is odd, yet `Φ_{2·1}(x) = Φ_2(x) = x + 1` whereas
`Φ_1(-x) = -x - 1 = -Φ_2(x)`, which are distinct over `ℤ`, `ℚ`, and every field `K` satisfying
Chapter 15's standing hypothesis `¬ (ringChar K ∣ 2 * 1)` (`char K ≠ 2`). -/
theorem exercise_15_2_n1_counterexample :
    Odd (1 : ℕ) ∧
    Polynomial.cyclotomic (2 * 1) ℤ = Polynomial.X + 1 ∧
    (Polynomial.cyclotomic 1 ℤ).comp (-Polynomial.X) = -Polynomial.X - 1 ∧
    Polynomial.cyclotomic (2 * 1) ℤ ≠ (Polynomial.cyclotomic 1 ℤ).comp (-Polynomial.X) ∧
    Polynomial.cyclotomic (2 * 1) ℚ ≠ (Polynomial.cyclotomic 1 ℚ).comp (-Polynomial.X) ∧
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
      ¬ (ringChar K ∣ 2 * 1) →
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ (2 * 1) - 1) →
      garlingCyclotomicPoly L (2 * 1) ≠ (garlingCyclotomicPoly L 1).comp (-Polynomial.X)) := by
  have h2z : Polynomial.cyclotomic (2 * 1) ℤ = Polynomial.X + 1 := by simp
  have h1z : (Polynomial.cyclotomic 1 ℤ).comp (-Polynomial.X) = -Polynomial.X - 1 := by simp
  have hnez : Polynomial.cyclotomic (2 * 1) ℤ ≠ (Polynomial.cyclotomic 1 ℤ).comp (-Polynomial.X) := by
    rw [h2z, h1z]
    intro h
    have hc0 := congrArg (fun P : ℤ[X] => P.coeff 0) h
    norm_num at hc0
  have hneq : Polynomial.cyclotomic (2 * 1) ℚ ≠ (Polynomial.cyclotomic 1 ℚ).comp (-Polynomial.X) := by
    simp only [mul_one, Polynomial.cyclotomic_two, Polynomial.cyclotomic_one, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.one_comp]
    intro h
    have hc0 := congrArg (fun P : ℚ[X] => P.coeff 0) h
    norm_num at hc0
  refine ⟨odd_one, h2z, h1z, hnez, hneq, ?_⟩
  intro K L _ _ _ hchar hsf hEq
  obtain ⟨_, h2ne0⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have h2K_ne0 : (2 : K) ≠ 0 := by simpa using h2ne0
  have h2Lne0 : (2 : L) ≠ 0 := by
    intro h2L
    apply h2K_ne0
    apply (algebraMap K L).injective
    rw [map_ofNat, h2L, map_zero]
  obtain ⟨_, _, _, hcyc2⟩ := theorem_15_1 hchar hsf
  have hcyc1 : garlingCyclotomicPoly L 1 = Polynomial.X - 1 := by
    rw [garlingCyclotomicPoly_eq_cyclotomic', Polynomial.cyclotomic'_one]
  rw [hcyc2, Polynomial.map_cyclotomic, show 2 * 1 = 2 from rfl, Polynomial.cyclotomic_two,
    hcyc1, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp] at hEq
  have hc0 := congrArg (fun P : L[X] => P.coeff 0) hEq
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
    Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_add, neg_zero, zero_sub] at hc0
  exact h2Lne0 (by linear_combination hc0)

/-- General odd-`n` relation (`n ≥ 1`): for every odd `n`, `Φ_n(-x) = (-1)^{φ(n)} Φ_{2n}(x)` in
`R[x]` (proved via the bijection `ε ↦ -ε` between primitive `n`th and primitive `2n`th roots of
unity in `ℂ`). -/
theorem exercise_15_2_general_odd (R : Type u) [CommRing R] {n : ℕ} (hn : Odd n) :
    (Polynomial.cyclotomic n R).comp (-Polynomial.X) =
      (-1 : R[X]) ^ Nat.totient n * Polynomial.cyclotomic (2 * n) R := by
  have hn_pos : 0 < n := hn.pos
  have h2n_pos : 0 < 2 * n := by omega
  suffices hZ : (Polynomial.cyclotomic n ℤ).comp (-Polynomial.X) =
      (-1 : ℤ[X]) ^ Nat.totient n * Polynomial.cyclotomic (2 * n) ℤ by
    have hmap := congrArg (Polynomial.map (Int.castRingHom R)) hZ
    simpa [Polynomial.map_comp, Polynomial.map_cyclotomic_int] using hmap
  apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  simp only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_cyclotomic_int]
  have hprim_n : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  have hprim_2n : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ))) (2 * n) :=
    Complex.isPrimitiveRoot_exp (2 * n) h2n_pos.ne'
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim_n,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim_2n, Polynomial.prod_comp]
  have hneg_prim : ∀ ζ : ℂ, IsPrimitiveRoot ζ n ↔ IsPrimitiveRoot (-ζ) (2 * n) := by
    intro ζ
    have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
    constructor
    · intro hζ
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨?_, fun l hl => ?_⟩
      · rw [pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      · have hζ2l : ζ ^ (2 * l) = 1 := by
          calc ζ ^ (2 * l) = (ζ ^ 2) ^ l := pow_mul ζ 2 l
            _ = ((-ζ) ^ 2) ^ l := by rw [neg_sq]
            _ = ((-ζ) ^ l) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
            _ = 1 := by rw [hl, one_pow]
        have hndvd2l : n ∣ 2 * l := hζ.dvd_of_pow_eq_one (2 * l) hζ2l
        have hndvdl : n ∣ l := hcop.symm.dvd_of_dvd_mul_left hndvd2l
        rcases hndvdl with ⟨k, rfl⟩
        have hnegk : (-1 : ℂ) ^ k = 1 := by
          calc (-1 : ℂ) ^ k = (-(ζ ^ n)) ^ k := by rw [hζ.pow_eq_one]
            _ = ((-ζ) ^ n) ^ k := by rw [hn.neg_pow]
            _ = (-ζ) ^ (n * k) := (pow_mul (-ζ) n k).symm
            _ = 1 := hl
        have h2dvdk : 2 ∣ k := by
          by_contra hk2
          have hoddk : Odd k := Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr hk2)
          rw [hoddk.neg_one_pow] at hnegk
          norm_num at hnegk
        rcases h2dvdk with ⟨t, rfl⟩
        exact ⟨t, by ring⟩
    · intro hnegζ
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨?_, fun l hl => ?_⟩
      · have h2n : (-ζ) ^ (2 * n) = 1 := hnegζ.pow_eq_one
        have hn_ne1 : (-ζ) ^ n ≠ 1 := by
          intro h1
          have hdvd : 2 * n ∣ n := hnegζ.dvd_of_pow_eq_one n h1
          have hle : 2 * n ≤ n := Nat.le_of_dvd hn_pos hdvd
          omega
        have hsq1 : ((-ζ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, h2n]
        have hneg1_pow : (-ζ) ^ n = -1 := by
          have hfac : ((-ζ) ^ n - 1) * ((-ζ) ^ n + 1) = 0 := by linear_combination hsq1
          exact eq_neg_of_add_eq_zero_left
            ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hn_ne1))
        rw [hn.neg_pow] at hneg1_pow
        exact neg_inj.mp hneg1_pow
      · have h2l : (-ζ) ^ (2 * l) = 1 := by
          calc (-ζ) ^ (2 * l) = ((-ζ) ^ 2) ^ l := pow_mul (-ζ) 2 l
            _ = (ζ ^ 2) ^ l := by rw [neg_sq]
            _ = (ζ ^ l) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
            _ = 1 := by rw [hl, one_pow]
        have hdvd : 2 * n ∣ 2 * l := hnegζ.dvd_of_pow_eq_one (2 * l) h2l
        exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hdvd
  have himg : (primitiveRoots n ℂ).image Neg.neg = primitiveRoots (2 * n) ℂ := by
    ext w
    simp only [Finset.mem_image, mem_primitiveRoots hn_pos, mem_primitiveRoots h2n_pos]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact (hneg_prim ζ).mp hζ
    · intro hw
      refine ⟨-w, ?_, neg_neg w⟩
      exact (hneg_prim (-w)).mpr (by simpa using hw)
  rw [← himg, Finset.prod_image (fun a _ b _ hab => neg_inj.mp hab)]
  have hcard : (primitiveRoots n ℂ).card = Nat.totient n := hprim_n.card_primitiveRoots
  rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ζ _ => ?_
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_neg]
  ring

/-- Universal `CommRing` form of **Exercise 15.2** for odd `n ≥ 3`. -/
theorem exercise_15_2_cyclotomic (R : Type u) [CommRing R] {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    Polynomial.cyclotomic (2 * n) R = (Polynomial.cyclotomic n R).comp (-Polynomial.X) := by
  have heven : Even (Nat.totient n) := Nat.totient_even (by omega : 2 < n)
  rw [exercise_15_2_general_odd R hn, heven.neg_one_pow, one_mul]

/-- **Exercise 15.2** (`QUEUE.md` fidelity hold — repaired `3 ≤ n` theorem; §15.1, printed p. 120 /
PDF p. 128):
*"Show that if `n` is odd then `Φ_{2n}(x) = Φ_n(-x)`."*

Holds for every odd integer `n ≥ 3` (`Odd n` and `3 ≤ n`), both for `Polynomial.cyclotomic` over any
commutative ring `R` and for Garling's §15.1 root-product `garlingCyclotomicPoly` over any splitting
field extension `L : K` satisfying `¬ (ringChar K ∣ 2 * n)`. -/
theorem exercise_15_2 :
    (∀ (R : Type u) [CommRing R] {n : ℕ}, Odd n → 3 ≤ n →
      Polynomial.cyclotomic (2 * n) R = (Polynomial.cyclotomic n R).comp (-Polynomial.X)) ∧
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {n : ℕ},
      Odd n → 3 ≤ n →
      ¬ (ringChar K ∣ 2 * n) →
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ (2 * n) - 1) →
      garlingCyclotomicPoly L (2 * n) =
        (garlingCyclotomicPoly L n).comp (-Polynomial.X)) := by
  refine ⟨fun R _ _ hn h3 => exercise_15_2_cyclotomic R hn h3, ?_⟩
  intro K L _ _ _ n hn h3 hchar hsf
  obtain ⟨ε, hε⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf
  have hprim2n : IsPrimitiveRoot ε (2 * n) :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot (by omega) ε).mp hε
  have hprimn : IsPrimitiveRoot (ε ^ 2) n :=
    IsPrimitiveRoot.pow (by omega : 0 < 2 * n) hprim2n rfl
  have hcyc2n : garlingCyclotomicPoly L (2 * n) = Polynomial.cyclotomic (2 * n) L := by
    rw [garlingCyclotomicPoly_eq_cyclotomic',
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim2n, Polynomial.cyclotomic']
  have hcycn : garlingCyclotomicPoly L n = Polynomial.cyclotomic n L := by
    rw [garlingCyclotomicPoly_eq_cyclotomic',
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprimn, Polynomial.cyclotomic']
  rw [hcyc2n, hcycn, exercise_15_2_cyclotomic L hn h3]

/-- Exact characterization companion to **Exercise 15.2**: over any commutative ring `R` with
`(2 : R) ≠ 0`, for any odd `n`, `Φ_{2n}(x) = Φ_n(-x)` holds if and only if `3 ≤ n`. -/
theorem exercise_15_2_iff {R : Type u} [CommRing R] (h2 : (2 : R) ≠ 0) {n : ℕ} (hn : Odd n) :
    Polynomial.cyclotomic (2 * n) R = (Polynomial.cyclotomic n R).comp (-Polynomial.X) ↔
      3 ≤ n := by
  constructor
  · intro hEq
    by_contra hlt
    have hn1 : n = 1 := by
      rcases hn with ⟨k, rfl⟩
      omega
    subst hn1
    simp only [mul_one, Polynomial.cyclotomic_two, Polynomial.cyclotomic_one, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.one_comp] at hEq
    have hc0 := congrArg (fun P : R[X] => P.coeff 0) hEq
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg,
      Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_add, neg_zero, zero_sub] at hc0
    exact h2 (by linear_combination hc0)
  · exact exercise_15_2_cyclotomic R hn

/-- Counterexample to the `n = 0` boundary case of **Exercise 15.3** (`QUEUE.md` fidelity hold;
§15.1, printed p. 120 / PDF p. 128): at `n = 0`, `Φ_{p^0}(x) = Φ_1(x) = x - 1`, whereas under `ℕ`
truncated subtraction `0 - 1 = 0` the right-hand sum `∑_{j=0}^{p-1} x^{j p^{n-1}}` evaluates to
`1 + x + … + x^{p-1} = Φ_p(x) ≠ x - 1`. -/
theorem exercise_15_3_n0_counterexample {p : ℕ} (hp : Nat.Prime p) :
    Polynomial.cyclotomic (p ^ 0) ℤ = Polynomial.X - 1 ∧
    (∑ j ∈ Finset.range p, (Polynomial.X : ℤ[X]) ^ (j * p ^ (0 - 1))) =
      Polynomial.cyclotomic p ℤ ∧
    Polynomial.cyclotomic (p ^ 0) ℤ ≠
      ∑ j ∈ Finset.range p, (Polynomial.X : ℤ[X]) ^ (j * p ^ (0 - 1)) := by
  have _ : Fact p.Prime := ⟨hp⟩
  have hlhs : Polynomial.cyclotomic (p ^ 0) ℤ = Polynomial.X - 1 := by simp
  have hrhs : (∑ j ∈ Finset.range p, (Polynomial.X : ℤ[X]) ^ (j * p ^ (0 - 1))) =
      Polynomial.cyclotomic p ℤ := by
    rw [Polynomial.cyclotomic_prime]
    simp
  refine ⟨hlhs, hrhs, ?_⟩
  rw [hlhs]
  intro hEq
  have hev := congrArg (Polynomial.eval 1) hEq
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, sub_self,
    Polynomial.eval_finsetSum, Polynomial.eval_pow, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at hev
  exact (Nat.cast_ne_zero.mpr hp.ne_zero) hev.symm

/-- Universal `CommRing` form of **Exercise 15.3** for prime `p` and `1 ≤ n`. -/
theorem exercise_15_3_cyclotomic (R : Type u) [CommRing R] {p n : ℕ} (hp : Nat.Prime p)
    (hn : 1 ≤ n) :
    Polynomial.cyclotomic (p ^ n) R =
      ∑ j ∈ Finset.range p, (Polynomial.X : R[X]) ^ (j * p ^ (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 k, Nat.add_sub_cancel, Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]

/-- **Exercise 15.3** (`QUEUE.md` fidelity hold — `1 ≤ n` theorem; §15.1, printed p. 120 /
PDF p. 128; OCR warning: `garling1986_pages.txt` l. 4471 mangles `(p - 1)` to `<p-l)`):
*"Show that if `p` is a prime then `Φ_{p^n}(x) = 1 + x^{p^{n-1}} + x^{2p^{n-1}} + … + x^{(p-1)p^{n-1}}`."*

Proved for every prime `p` and every `1 ≤ n`, both over arbitrary commutative rings `R` via
`Polynomial.cyclotomic` and for Garling's §15.1 root-product `garlingCyclotomicPoly` over any
splitting field `L : K` with `¬ (ringChar K ∣ p ^ n)`. -/
theorem exercise_15_3 :
    (∀ (R : Type u) [CommRing R] {p n : ℕ}, Nat.Prime p → 1 ≤ n →
      Polynomial.cyclotomic (p ^ n) R =
        ∑ j ∈ Finset.range p, (Polynomial.X : R[X]) ^ (j * p ^ (n - 1))) ∧
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {p n : ℕ},
      Nat.Prime p → 1 ≤ n →
      ∀ (hchar : ¬ (ringChar K ∣ p ^ n))
        (_hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ (p ^ n) - 1)),
        garlingCyclotomicPoly L (p ^ n) =
          ∑ j ∈ Finset.range p, (Polynomial.X : L[X]) ^ (j * p ^ (n - 1))) := by
  refine ⟨fun R _ _ _ hp hn => exercise_15_3_cyclotomic R hp hn, ?_⟩
  intro K L _ _ _ p n hp hn hchar hsf
  obtain ⟨_, _, _, hcyc_eq⟩ := theorem_15_1 hchar hsf
  rw [hcyc_eq, Polynomial.map_cyclotomic, exercise_15_3_cyclotomic L hp hn]

/-- Exact characterization companion to **Exercise 15.3**: for any prime `p` and `n : ℕ`,
`cyclotomic (p ^ n) ℤ = ∑_{j < p} X^{j p^{n - 1}}` holds if and only if `1 ≤ n`. -/
theorem exercise_15_3_iff {p n : ℕ} (hp : Nat.Prime p) :
    Polynomial.cyclotomic (p ^ n) ℤ =
      ∑ j ∈ Finset.range p, (Polynomial.X : ℤ[X]) ^ (j * p ^ (n - 1)) ↔ 1 ≤ n := by
  rcases n with _ | n
  · exact ⟨fun h => absurd h (exercise_15_3_n0_counterexample hp).2.2, fun h => by omega⟩
  · exact ⟨fun _ => by omega, fun h => exercise_15_3_cyclotomic ℤ hp h⟩

/-! ## §15.2 Irreducibility (printed pp. 120–121, PDF pp. 128–129) -/

/-- Helper: a degree-`2` polynomial over a field `F` is irreducible iff it has no root in `F`. -/
private theorem irreducible_of_natDegree_two_of_no_roots {F : Type*} [Field F] {f : F[X]}
    (hd : f.natDegree = 2) (hnr : ∀ x : F, f.eval x ≠ 0) :
    Irreducible f := by
  have hf_nu : ¬ IsUnit f := Polynomial.not_isUnit_of_natDegree_pos f (by omega)
  refine irreducible_iff.mpr ⟨hf_nu, fun a b hfab => ?_⟩
  by_contra hboth
  push_neg at hboth
  rcases hboth with ⟨ha_nu, hb_nu⟩
  have ha0 : a ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hfab
    rw [hfab, Polynomial.natDegree_zero] at hd
    omega
  have hb0 : b ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hfab
    rw [hfab, Polynomial.natDegree_zero] at hd
    omega
  have ha_pos : 1 ≤ a.natDegree := by
    by_contra h0
    have hz : a.natDegree = 0 := by omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hz
    have hc0 : c ≠ 0 := fun hcz => ha0 (by rw [← hc, hcz, map_zero])
    exact ha_nu (hc ▸ (IsUnit.mk0 c hc0).map Polynomial.C)
  have hb_pos : 1 ≤ b.natDegree := by
    by_contra h0
    have hz : b.natDegree = 0 := by omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hz
    have hc0 : c ≠ 0 := fun hcz => hb0 (by rw [← hc, hcz, map_zero])
    exact hb_nu (hc ▸ (IsUnit.mk0 c hc0).map Polynomial.C)
  have hsum : 2 = a.natDegree + b.natDegree := by
    rw [← hd, hfab, Polynomial.natDegree_mul ha0 hb0]
  have ha1 : a.natDegree = 1 := by omega
  have ha_eq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one ha1.le
  have hc1_ne0 : a.coeff 1 ≠ 0 := by
    rw [← ha1]
    exact Polynomial.leadingCoeff_ne_zero.mpr ha0
  let r : F := -a.coeff 0 / a.coeff 1
  have ha_root : a.eval r = 0 := by
    rw [ha_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_C]
    field_simp [hc1_ne0]
    ring_nf
  have hf_root : f.eval r = 0 := by
    rw [hfab, Polynomial.eval_mul, ha_root, zero_mul]
  exact hnr r hf_root

/-- §15.2 prose worked example on `Φ_3 = x^2 + x + 1` over `ℤ_5` vs. `ℤ_7`
(printed p. 120 / PDF p. 128; OCR warning: `garling1986_pages.txt` l. 4477 strips the overbars on
`2̄` and `4̄`):
*"for example, `Φ_3 = x^2 + x + 1` is irreducible over `ℤ_5`, while over `ℤ_7`,
`x^2 + x + 1 = (x - 2̄)(x - 4̄)`."* -/
theorem section_15_2_phi3_zmod5_zmod7 :
    Polynomial.cyclotomic 3 (ZMod 5) = Polynomial.X ^ 2 + Polynomial.X + 1 ∧
    Irreducible (Polynomial.cyclotomic 3 (ZMod 5)) ∧
    IsGarlingIrreducible (Polynomial.cyclotomic 3 (ZMod 5)) ∧
    Polynomial.cyclotomic 3 (ZMod 7) = Polynomial.X ^ 2 + Polynomial.X + 1 ∧
    Polynomial.cyclotomic 3 (ZMod 7) =
      (Polynomial.X - Polynomial.C (2 : ZMod 7)) *
        (Polynomial.X - Polynomial.C (4 : ZMod 7)) ∧
    ¬ Irreducible (Polynomial.cyclotomic 3 (ZMod 7)) := by
  have h3_5 : Polynomial.cyclotomic 3 (ZMod 5) = Polynomial.X ^ 2 + Polynomial.X + 1 :=
    Polynomial.cyclotomic_three (ZMod 5)
  have h3_7 : Polynomial.cyclotomic 3 (ZMod 7) = Polynomial.X ^ 2 + Polynomial.X + 1 :=
    Polynomial.cyclotomic_three (ZMod 7)
  have hdeg5 : (Polynomial.cyclotomic 3 (ZMod 5)).natDegree = 2 := by
    rw [Polynomial.natDegree_cyclotomic]
    norm_num
  have hnr5 : ∀ x : ZMod 5, (Polynomial.cyclotomic 3 (ZMod 5)).eval x ≠ 0 := by
    rw [h3_5]
    intro x
    fin_cases x <;> decide
  have hirr5 : Irreducible (Polynomial.cyclotomic 3 (ZMod 5)) :=
    irreducible_of_natDegree_two_of_no_roots hdeg5 hnr5
  have hgirr5 : IsGarlingIrreducible (Polynomial.cyclotomic 3 (ZMod 5)) :=
    (isGarlingIrreducible_iff _).mpr hirr5
  have hfac7 : (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 7)[X]) =
      (Polynomial.X - Polynomial.C (2 : ZMod 7)) *
        (Polynomial.X - Polynomial.C (4 : ZMod 7)) := by
    have hsum7 : (2 : ZMod 7) + 4 = -1 := by
      apply ZMod.val_injective
      rfl
    have hmul7 : (2 : ZMod 7) * 4 = 1 := by
      apply ZMod.val_injective
      rfl
    calc (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 7)[X])
        = Polynomial.X ^ 2 - Polynomial.C ((2 : ZMod 7) + 4) * Polynomial.X +
            Polynomial.C ((2 : ZMod 7) * 4) := by
          rw [hsum7, hmul7, map_neg, map_one]
          ring
      _ = (Polynomial.X - Polynomial.C (2 : ZMod 7)) *
            (Polynomial.X - Polynomial.C (4 : ZMod 7)) := by
          simp only [map_add, map_mul]
          ring
  have hred7 : ¬ Irreducible (Polynomial.cyclotomic 3 (ZMod 7)) := by
    rw [h3_7, hfac7]
    intro hirr
    have hnu2 : ¬ IsUnit (Polynomial.X - Polynomial.C (2 : ZMod 7)) :=
      Polynomial.not_isUnit_of_natDegree_pos _ (by simp)
    have hnu4 : ¬ IsUnit (Polynomial.X - Polynomial.C (4 : ZMod 7)) :=
      Polynomial.not_isUnit_of_natDegree_pos _ (by simp)
    exact (hirr.isUnit_or_isUnit rfl).elim hnu2 hnu4
  exact ⟨h3_5, hirr5, hgirr5, h3_7, h3_7.trans hfac7, hred7⟩

/-- Key mod-`p` reduction sublemma inside Garling's proof of **Theorem 15.3** (§15.2, printed p. 120 /
PDF p. 128):
*"We shall first show that, if `ε` is a root of `f` in `L` and `p` is a prime which does not divide
`m`, then `ε^p` is a root of `f`."*

Follows Garling's exact printed steps: sets `k(x) = g(x^p) ∈ ℤ[x]`, applies `Lemma 15.2 (ii)` to
obtain `k = f h` in `ℤ[x]`, reduces modulo `p` to get `f̄ h̄ = k̄ = (ḡ)^p` in `ℤ_p[x]`, picks an
irreducible factor `q̄` of `f̄`, and derives `q̄^2 ∣ f̄ ḡ = Φ̄_m ∣ x^m - 1`, contradicting
separability of `x^m - 1` over `ℤ_p` when `p ∤ m`. -/
theorem theorem_15_3_root_pow_prime {L : Type u} [Field L] [Algebra ℚ L]
    {m : ℕ} (hm : 1 ≤ m) {f g : ℤ[X]}
    (hf_mon : f.Monic) (hg_mon : g.Monic)
    (hf_irr : Irreducible (f.map (algebraMap ℤ ℚ)))
    (hfg : Polynomial.cyclotomic m ℤ = f * g)
    {ε : L} (hε_prim : IsPrimitiveRoot ε m)
    (hε_f : Polynomial.aeval ε f = 0)
    {p : ℕ} (hp : Nat.Prime p) (hpm : ¬ p ∣ m) :
    Polynomial.aeval (ε ^ p) f = 0 := by
  by_contra hnot
  have hεp_prim : IsPrimitiveRoot (ε ^ p) m := hε_prim.pow_of_prime hp hpm
  have hεp_cyc : Polynomial.aeval (ε ^ p) (Polynomial.cyclotomic m ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      show algebraMap ℤ L = Int.castRingHom L from Subsingleton.elim _ _,
      Polynomial.map_cyclotomic_int, ← Polynomial.IsRoot.def]
    exact hεp_prim.isRoot_cyclotomic (by omega)
  have hεp_g : Polynomial.aeval (ε ^ p) g = 0 := by
    rw [hfg, map_mul] at hεp_cyc
    exact (mul_eq_zero.mp hεp_cyc).resolve_left hnot
  let k : ℤ[X] := Polynomial.expand ℤ p g
  have hk_mon : k.Monic := hg_mon.expand hp.pos
  have hk_ε : Polynomial.aeval ε k = 0 := by
    dsimp [k]
    rw [Polynomial.expand_aeval, hεp_g]
  have hfQ_mon : (f.map (algebraMap ℤ ℚ)).Monic := hf_mon.map (algebraMap ℤ ℚ)
  have hfQ_ε : Polynomial.aeval ε (f.map (algebraMap ℤ ℚ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hε_f
  have hkQ_ε : Polynomial.aeval ε (k.map (algebraMap ℤ ℚ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hk_ε
  have hfQ_min : f.map (algebraMap ℤ ℚ) = minpoly ℚ ε :=
    (minpoly.eq_of_irreducible_of_monic hf_irr hfQ_ε hfQ_mon).symm
  have hdvdQ : f.map (algebraMap ℤ ℚ) ∣ k.map (algebraMap ℤ ℚ) := by
    rw [hfQ_min]
    exact minpoly.dvd ℚ ε hkQ_ε
  rcases hdvdQ with ⟨qQ, hkqQ⟩
  rw [mul_comm] at hkqQ
  -- Apply Lemma 15.2 (ii) to descend `qQ ∈ ℚ[X]` to `h ∈ ℤ[X]`!
  obtain ⟨h, _, _, hkhf⟩ := lemma_15_2.2 qQ k f hk_mon hf_mon hkqQ
  have hkfh : k = f * h := by rw [hkhf, mul_comm]
  -- Reduce modulo `p` (`ℤ[x] → (ZMod p)[x]`):
  have _ : Fact p.Prime := ⟨hp⟩
  let π : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let fbar : (ZMod p)[X] := f.map π
  let gbar : (ZMod p)[X] := g.map π
  let hbar : (ZMod p)[X] := h.map π
  let kbar : (ZMod p)[X] := k.map π
  have hfbar_mon : fbar.Monic := hf_mon.map π
  have hfh_eq_k : fbar * hbar = kbar := by
    dsimp [fbar, hbar, kbar]
    rw [← Polynomial.map_mul, hkfh]
  have hkbar_eq_pow : kbar = gbar ^ p := by
    dsimp [kbar, gbar, k]
    rw [Polynomial.map_expand, ZMod.expand_card]
  have hf_deg_pos : 1 ≤ f.natDegree := by
    have hfQ_pos : 0 < (f.map (algebraMap ℤ ℚ)).natDegree := hf_irr.natDegree_pos
    have hmap_deg : (f.map (algebraMap ℤ ℚ)).natDegree = f.natDegree :=
      hf_mon.natDegree_map (algebraMap ℤ ℚ)
    omega
  have hfbar_deg_pos : 1 ≤ fbar.natDegree := by
    rw [hf_mon.natDegree_map π]
    exact hf_deg_pos
  have hfbar_nu : ¬ IsUnit fbar :=
    Polynomial.not_isUnit_of_natDegree_pos fbar (by omega)
  obtain ⟨qbar, hqbar_irr, hqbar_dvd_f⟩ :=
    WfDvdMonoid.exists_irreducible_factor hfbar_nu hfbar_mon.ne_zero
  have hqbar_dvd_gp : qbar ∣ gbar ^ p := by
    rw [← hkbar_eq_pow, ← hfh_eq_k]
    exact dvd_mul_of_dvd_left hqbar_dvd_f hbar
  have hqbar_dvd_g : qbar ∣ gbar := hqbar_irr.prime.dvd_of_dvd_pow hqbar_dvd_gp
  have hsq_dvd_fg : qbar ^ 2 ∣ fbar * gbar := by
    rw [sq]
    exact mul_dvd_mul hqbar_dvd_f hqbar_dvd_g
  have hfg_dvd_xm1 : fbar * gbar ∣ (Polynomial.X ^ m - 1 : (ZMod p)[X]) := by
    have hcyc_zp : fbar * gbar = Polynomial.cyclotomic m (ZMod p) := by
      dsimp [fbar, gbar]
      rw [← Polynomial.map_mul, ← hfg, Polynomial.map_cyclotomic_int]
    rw [hcyc_zp]
    exact Polynomial.cyclotomic.dvd_X_pow_sub_one m (ZMod p)
  have hsq_dvd_xm1 : qbar ^ 2 ∣ (Polynomial.X ^ m - 1 : (ZMod p)[X]) :=
    dvd_trans hsq_dvd_fg hfg_dvd_xm1
  have hm_zp : (m : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff m p).not.mpr hpm
  have hsep_zp : (Polynomial.X ^ m - 1 : (ZMod p)[X]).Separable := by
    simpa using Polynomial.separable_X_pow_sub_C (1 : ZMod p) hm_zp one_ne_zero
  have hunit_qbar : IsUnit qbar := by
    refine hsep_zp.squarefree qbar ?_
    rwa [← sq]
  exact hqbar_irr.not_isUnit hunit_qbar

/-- **Theorem 15.3** (§15.2, printed p. 120 / PDF p. 128; OCR warning: `garling1986_pages.txt`
ll. 4482, 4486, 4491 corrupts `ℚ` to `01` three times):
*"For each `m`, `Φ_m` is irreducible over `ℚ`."*

Proved directly from Garling's p. 120 mod-`p` + `Lemma 15.2` argument (`theorem_15_3_root_pow_prime`)
for every `1 ≤ m` (equivalently `¬ (ringChar ℚ ∣ m)` under p. 118's chapter-wide standing assumption),
without invoking `Polynomial.cyclotomic.irreducible_rat`. Establishes irreducibility both in `ℚ[x]`
and in `ℤ[x]`, in both Mathlib's `Irreducible` and Chapter 3's `IsGarlingIrreducible` forms. -/
theorem theorem_15_3 {m : ℕ} (hm : 1 ≤ m) :
    Irreducible (Polynomial.cyclotomic m ℚ) ∧
    IsGarlingIrreducible (Polynomial.cyclotomic m ℚ) ∧
    Irreducible (Polynomial.cyclotomic m ℤ) ∧
    IsGarlingIrreducible (Polynomial.cyclotomic m ℤ) := by
  classical
  have _ : NeZero m := ⟨by omega⟩
  let L := (Polynomial.X ^ m - 1 : ℚ[X]).SplittingField
  have hcharQ : ¬ (ringChar ℚ ∣ m) := by
    rw [ringChar.eq_zero]
    intro h0
    have := zero_dvd_iff.mp h0
    omega
  have hsf : IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ m - 1) :=
    (isGarlingSplittingFieldExtension_iff ℚ L _).mpr inferInstance
  obtain ⟨η, hη_gar⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hcharQ hsf
  have hη : IsPrimitiveRoot η m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm η).mp hη_gar
  have hη_int : IsIntegral ℤ η := hη.isIntegral (by omega)
  let f : ℤ[X] := minpoly ℤ η
  have hf_mon : f.Monic := minpoly.monic hη_int
  have hfQ_eq : f.map (algebraMap ℤ ℚ) = minpoly ℚ η := by
    symm
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hη_int
  have hf_irr : Irreducible (f.map (algebraMap ℤ ℚ)) := by
    rw [hfQ_eq]
    exact minpoly.irreducible (IsIntegral.tower_top (R := ℤ) (A := ℚ) hη_int)
  have hf_dvd_cyc : f ∣ Polynomial.cyclotomic m ℤ :=
    hη.minpoly_dvd_cyclotomic (by omega)
  rcases hf_dvd_cyc with ⟨g, hfg⟩
  have hg_mon : g.Monic := by
    have hlc : (Polynomial.cyclotomic m ℤ).leadingCoeff = (f * g).leadingCoeff :=
      congrArg Polynomial.leadingCoeff hfg
    rw [(Polynomial.cyclotomic.monic m ℤ).leadingCoeff] at hlc
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfg
      exact Polynomial.cyclotomic_ne_zero m ℤ hfg
    have hcoeff : (f * g).coeff (f.natDegree + g.natDegree) = f.leadingCoeff * g.leadingCoeff :=
      Polynomial.coeff_mul_degree_add_degree f g
    have hglc_ne0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hmul_ne0 : f.leadingCoeff * g.leadingCoeff ≠ 0 := by
      rw [hf_mon.leadingCoeff, one_mul]
      exact hglc_ne0
    have hdeg_fg : (f * g).natDegree = f.natDegree + g.natDegree :=
      Polynomial.natDegree_mul' hmul_ne0
    change g.leadingCoeff = 1
    calc g.leadingCoeff = f.leadingCoeff * g.leadingCoeff := by rw [hf_mon.leadingCoeff, one_mul]
      _ = (f * g).coeff (f.natDegree + g.natDegree) := hcoeff.symm
      _ = (f * g).leadingCoeff := by rw [← hdeg_fg]; rfl
      _ = 1 := hlc.symm
  -- Strong induction on `r ≥ 1` coprime to `m`: `ε ^ r` is a root of `f` for every primitive root `ε` of `f`.
  have hpow_coprime : ∀ r : ℕ, 1 ≤ r → Nat.Coprime r m →
      ∀ ε : L, IsPrimitiveRoot ε m → Polynomial.aeval ε f = 0 → Polynomial.aeval (ε ^ r) f = 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ihr =>
      intro hr1 hcop ε hεp hεf
      by_cases hr_eq1 : r = 1
      · subst hr_eq1
        simpa using hεf
      · have hr_gt1 : 1 < r := by omega
        let p := r.minFac
        have hp : Nat.Prime p := Nat.minFac_prime (by omega)
        have hpr : p ∣ r := Nat.minFac_dvd r
        have hpm : ¬ p ∣ m := by
          intro hpm_dvd
          have hdvd_gcd : p ∣ Nat.gcd r m := Nat.dvd_gcd hpr hpm_dvd
          rw [hcop.gcd_eq_one] at hdvd_gcd
          exact hp.not_dvd_one hdvd_gcd
        rcases hpr with ⟨q, hprod⟩
        have hq_pos : 1 ≤ q := by
          by_contra hq0
          have : q = 0 := by omega
          rw [this, mul_zero] at hprod
          omega
        have hq_lt : q < r := by
          have hp2 : 2 ≤ p := hp.two_le
          nlinarith
        have hcop_q : Nat.Coprime q m :=
          (Nat.coprime_mul_iff_left.mp (hprod ▸ hcop)).2
        have hεp_f : Polynomial.aeval (ε ^ p) f = 0 :=
          theorem_15_3_root_pow_prime hm hf_mon hg_mon hf_irr hfg hεp hεf hp hpm
        have hεp_prim : IsPrimitiveRoot (ε ^ p) m := hεp.pow_of_prime hp hpm
        have hrec := ihr q hq_lt hq_pos hcop_q (ε ^ p) hεp_prim hεp_f
        rwa [← pow_mul, ← hprod] at hrec
  -- Every primitive `m`th root of unity in `L` is therefore a root of `f`:
  have hall_prim : primitiveRoots m L ⊆
      (f.map (algebraMap ℤ L)).roots.toFinset := by
    intro θ hθ
    rw [mem_primitiveRoots (by omega : 0 < m)] at hθ
    obtain ⟨r, hr_lt, rfl⟩ := hη.eq_pow_of_pow_eq_one hθ.pow_eq_one
    have hcop : Nat.Coprime r m :=
      (hη.pow_iff_coprime (by omega : 0 < m) r).mp hθ
    have hroot : Polynomial.aeval (η ^ r) f = 0 := by
      by_cases hr0 : r = 0
      · subst hr0
        rw [Nat.coprime_zero_left] at hcop
        subst hcop
        rw [pow_zero]
        have h1 : η = 1 := by simpa using hη.pow_eq_one
        rw [← h1]
        exact minpoly.aeval ℤ η
      · exact hpow_coprime r (by omega) hcop η hη (minpoly.aeval ℤ η)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hf_mon.map _).ne_zero,
      Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact hroot
  have hcard_le : Nat.totient m ≤ f.natDegree := by
    have h1 : (primitiveRoots m L).card = Nat.totient m := hη.card_primitiveRoots
    have h2 : (primitiveRoots m L).card ≤ (f.map (algebraMap ℤ L)).roots.toFinset.card :=
      Finset.card_le_card hall_prim
    have h3 : (f.map (algebraMap ℤ L)).roots.toFinset.card ≤ (f.map (algebraMap ℤ L)).roots.card :=
      Multiset.toFinset_card_le _
    have h4 : (f.map (algebraMap ℤ L)).roots.card ≤ (f.map (algebraMap ℤ L)).natDegree :=
      Polynomial.card_roots' _
    rw [hf_mon.natDegree_map] at h4
    omega
  have hdeg_sum : Nat.totient m = f.natDegree + g.natDegree := by
    have hd := congrArg Polynomial.natDegree hfg
    rw [Polynomial.natDegree_cyclotomic m ℤ, hf_mon.natDegree_mul hg_mon] at hd
    exact hd
  have hg_deg0 : g.natDegree = 0 := by omega
  have hg_one : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg_mon hg_deg0
  have hcyc_eq_f : Polynomial.cyclotomic m ℤ = f := by rw [hfg, hg_one, mul_one]
  have hcycQ_eq : Polynomial.cyclotomic m ℚ = f.map (algebraMap ℤ ℚ) := by
    rw [← Polynomial.map_cyclotomic_int m ℚ, hcyc_eq_f]
    rfl
  have hirrQ : Irreducible (Polynomial.cyclotomic m ℚ) := hcycQ_eq ▸ hf_irr
  have hgirrQ : IsGarlingIrreducible (Polynomial.cyclotomic m ℚ) :=
    (isGarlingIrreducible_iff _).mpr hirrQ
  have hirrZ : Irreducible (Polynomial.cyclotomic m ℤ) := by
    have hprimZ : (Polynomial.cyclotomic m ℤ).IsPrimitive :=
      Polynomial.cyclotomic.isPrimitive m ℤ
    exact (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprimZ).mpr
      (by simpa [Polynomial.map_cyclotomic_int] using hirrQ)
  have hgirrZ : IsGarlingIrreducible (Polynomial.cyclotomic m ℤ) :=
    (isGarlingIrreducible_iff _).mpr hirrZ
  exact ⟨hirrQ, hgirrQ, hirrZ, hgirrZ⟩

/-- Non-counted boundary remark on `m = 0`: Mathlib totalizes `Polynomial.cyclotomic 0 ℚ = 1`, which
is a unit (not irreducible), whereas Garling's p. 118 chapter-wide convention `¬ (ringChar K ∣ m)` at
`K = ℚ` (`ringChar ℚ = 0`) is literally `m ≠ 0` (`1 ≤ m`). -/
theorem cyclotomic_zero_not_irreducible_remark :
    Polynomial.cyclotomic 0 ℚ = 1 ∧
    IsUnit (Polynomial.cyclotomic 0 ℚ) ∧
    ¬ Irreducible (Polynomial.cyclotomic 0 ℚ) ∧
    (∀ m : ℕ, Irreducible (Polynomial.cyclotomic m ℚ) ↔ 1 ≤ m) := by
  refine ⟨Polynomial.cyclotomic_zero ℚ, by simp, ?_, fun m => ?_⟩
  · rw [Polynomial.cyclotomic_zero]
    exact not_irreducible_one
  · rcases m with _ | m
    · simp [not_irreducible_one]
    · exact ⟨fun _ => by omega, fun hm => (theorem_15_3 hm).1⟩

/-- **Exercise 15.4** (`QUEUE.md` fidelity hold — open-ended minimal-polynomial and Galois-group
identification prompt; §15.2, printed p. 121 / PDF p. 129; OCR warning: `garling1986_pages.txt`
ll. 4511–4513 mangles `[ℚ(ε):ℚ(η)] = 2` and `Γ[ℚ(ε):ℚ(η)]`):
*"Suppose that `ε` is a primitive `m`th root of unity over `ℚ`, where `m > 2`. Let `η = ε + ε⁻¹`.
Show that `[ℚ(ε) : ℚ(η)] = 2`, find the minimal polynomial for `ε` over `ℚ(η)` and identify the
Galois group `Γ[ℚ(ε) : ℚ(η)]`."*

Proved universally for any extension `L : ℚ`, any `m > 2`, and any primitive `m`th root of unity
`ε ∈ L`: sets `E = ℚ(ε)` (`ε₀ ∈ E`), `η₀ = ε₀ + ε₀⁻¹ ∈ E`, and `M = ℚ(η₀) ⊆ E` (canonically
isomorphic to `ℚ(η) ⊆ L`), and proves:
1. `[E : M] = 2` (both `Module.finrank M E = 2` and `extDegree M E = 2`, with `[E : ℚ] = φ(m)` and
   `[ℚ(η) : ℚ] = φ(m) / 2`);
2. `minpoly M ε₀ = X ^ 2 - C η_M * X + 1` (irreducible in `M[X]`);
3. `E : M` is a Galois extension whose Galois group `Γ[ℚ(ε) : ℚ(η)] = GarlingGaloisGroup M E` is
   cyclic of order `2` (`≃* Multiplicative (ZMod 2)`), consisting of `{1, τ}` where `τ ≠ 1` is the
   unique automorphism sending `ε₀ ↦ ε₀⁻¹`. -/
theorem exercise_15_4 {L : Type u} [Field L] [Algebra ℚ L] {m : ℕ} (hm : 2 < m)
    {ε : L} (hε : IsGarlingPrimitiveRoot m ε) :
    let E : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ε} : Set L)
    let ε₀ : E := ⟨ε, IntermediateField.mem_adjoin_simple_self ℚ ε⟩
    let η : L := ε + ε⁻¹
    let F : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({η} : Set L)
    let η₀ : E := ε₀ + ε₀⁻¹
    let M : IntermediateField ℚ E := IntermediateField.adjoin ℚ ({η₀} : Set E)
    let ηM : M := ⟨η₀, IntermediateField.mem_adjoin_simple_self ℚ η₀⟩
    Nonempty (M ≃ₐ[ℚ] F) ∧
    Module.finrank M E = 2 ∧
    extDegree M E = 2 ∧
    Module.finrank ℚ E = Nat.totient m ∧
    Module.finrank ℚ F = Nat.totient m / 2 ∧
    minpoly M ε₀ = Polynomial.X ^ 2 - Polynomial.C ηM * Polynomial.X + 1 ∧
    Irreducible (Polynomial.X ^ 2 - Polynomial.C ηM * Polynomial.X + 1 : M[X]) ∧
    IsGarlingGaloisExtension M E ∧
    IsCyclic (GarlingGaloisGroup M E) ∧
    Nat.card (GarlingGaloisGroup M E) = 2 ∧
    setOrder (GarlingGaloisGroup M E) = 2 ∧
    Nonempty (GarlingGaloisGroup M E ≃* Multiplicative (ZMod 2)) ∧
    ∃ τ : GarlingGaloisGroup M E,
      τ ≠ 1 ∧ τ ^ 2 = 1 ∧ τ ε₀ = ε₀⁻¹ ∧
      (Set.univ : Set (GarlingGaloisGroup M E)) = {1, τ} := by
  intro E ε₀ η F η₀ M ηM
  classical
  have _ : CharZero L := ⟨fun a b h =>
    Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using h))⟩
  have _ : CharZero E := ⟨fun a b h =>
    Nat.cast_injective (R := ℚ) ((algebraMap ℚ E).injective (by simpa using h))⟩
  have hm_pos : 1 ≤ m := by omega
  have hprimL : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
  have hprimE : IsPrimitiveRoot ε₀ m := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hprimL
  -- Equivalence `M ≃ₐ[ℚ] F` inside `L`:
  have hMF_range : (E.val.comp M.val).fieldRange = F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (y : E).1 ∈ F
      have hy : (y : E) ∈ M := y.2
      let F_sub_E : IntermediateField ℚ E := F.comap E.val
      have hη₀_mem : η₀ ∈ F_sub_E := by
        change η ∈ F
        exact IntermediateField.mem_adjoin_simple_self ℚ η
      have hle : M ≤ F_sub_E := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hη₀_mem)
      exact hle hy
    · intro hx
      have hηE : η ∈ E := E.add_mem ε₀.2 (E.inv_mem ε₀.2)
      have hFE : F ≤ E := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hηE)
      let xE : E := ⟨x, hFE hx⟩
      have hxM : xE ∈ M := by
        let M_map : IntermediateField ℚ L := M.map E.val
        have hη_in_Mmap : η ∈ M_map := ⟨η₀, ηM.2, rfl⟩
        have hF_le : F ≤ M_map :=
          IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hη_in_Mmap)
        rcases hF_le hx with ⟨z, hzM, hzx⟩
        have hz_eq : z = xE := Subtype.ext hzx
        exact hz_eq ▸ hzM
      exact ⟨⟨xE, hxM⟩, rfl⟩
  let isoMF : M ≃ₐ[ℚ] F :=
    (AlgEquiv.ofInjective (E.val.comp M.val) (RingHom.injective _)).trans
      (IntermediateField.equivOfEq hMF_range)
  -- Degree `[E : ℚ] = φ(m)`:
  have hminQ_ε₀ : minpoly ℚ ε₀ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hprimE (by omega : 0 < m)).symm
  have hintQ_ε₀ : IsIntegral ℚ ε₀ :=
    IsIntegral.tower_top (R := ℤ) (A := ℚ) (hprimE.isIntegral (by omega))
  have hE_top : ℚ⟮ε₀⟯ = (⊤ : IntermediateField ℚ E) := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    have hxE : x.1 ∈ E := x.2
    let S : IntermediateField ℚ L := ℚ⟮ε₀⟯.map E.val
    have hεS : ε ∈ S := ⟨ε₀, IntermediateField.mem_adjoin_simple_self ℚ ε₀, rfl⟩
    have hES : E ≤ S := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hεS)
    rcases hES hxE with ⟨y, hy, hyx⟩
    have hyeq : y = x := Subtype.ext hyx
    exact hyeq ▸ hy
  let pbE : PowerBasis ℚ E :=
    (IntermediateField.adjoin.powerBasis hintQ_ε₀).map
      ((IntermediateField.equivOfEq hE_top).trans IntermediateField.topEquiv)
  have hpbE_gen : pbE.gen = ε₀ := by
    simp [pbE, IntermediateField.adjoin.powerBasis_gen]
  have hfinrankQE : Module.finrank ℚ E = Nat.totient m := by
    rw [pbE.finrank, pbE.dim_eq_natDegree_minpoly, hpbE_gen, hminQ_ε₀,
      Polynomial.natDegree_cyclotomic]
  -- Construct the `ℚ`-automorphism `τ₀ : E ≃ₐ[ℚ] E` sending `ε₀ ↦ ε₀⁻¹`:
  have hprimE_inv : IsPrimitiveRoot ε₀⁻¹ m := hprimE.inv
  have hminQ_inv : minpoly ℚ ε₀⁻¹ = minpoly ℚ ε₀ := by
    rw [hminQ_ε₀]
    exact (Polynomial.cyclotomic_eq_minpoly_rat hprimE_inv (by omega : 0 < m)).symm
  have hintQ_inv : IsIntegral ℚ ε₀⁻¹ :=
    IsIntegral.tower_top (A := ℤ) (hprimE_inv.isIntegral (by omega))
  have hE_top_inv : ℚ⟮ε₀⁻¹⟯ = (⊤ : IntermediateField ℚ E) := by
    rw [IntermediateField.adjoin_inv]
    exact hE_top
  let pbE_inv : PowerBasis ℚ E :=
    (IntermediateField.adjoin.powerBasis hintQ_inv).map
      ((IntermediateField.equivOfEq hE_top_inv).trans IntermediateField.topEquiv)
  have hpbE_inv_gen : pbE_inv.gen = ε₀⁻¹ := by
    simp [pbE_inv, IntermediateField.adjoin.powerBasis_gen]
  let τ₀ : E ≃ₐ[ℚ] E := pbE.equivOfMinpoly pbE_inv (by rw [hpbE_gen, hpbE_inv_gen, hminQ_inv])
  have hτ₀_gen : τ₀ ε₀ = ε₀⁻¹ := by
    have h := pbE.equivOfMinpoly_gen pbE_inv (by rw [hpbE_gen, hpbE_inv_gen, hminQ_inv])
    rwa [hpbE_gen, hpbE_inv_gen] at h
  have hτ₀_η₀ : τ₀ η₀ = η₀ := by
    dsimp [η₀]
    rw [map_add, map_inv₀, hτ₀_gen, inv_inv, add_comm]
  have hτ₀_fix_M : ∀ y : M, τ₀ y.1 = y.1 := by
    let Fix : IntermediateField ℚ E :=
      { carrier := {x : E | τ₀ x = x}
        add_mem' := fun {a b} ha hb => by change τ₀ (a + b) = a + b; rw [map_add, ha, hb]
        zero_mem' := map_zero τ₀
        neg_mem' := fun {a} ha => by change τ₀ (-a) = -a; rw [map_neg, ha]
        mul_mem' := fun {a b} ha hb => by change τ₀ (a * b) = a * b; rw [map_mul, ha, hb]
        one_mem' := map_one τ₀
        inv_mem' := fun {a} ha => by change τ₀ a⁻¹ = a⁻¹; rw [map_inv₀, ha]
        algebraMap_mem' := fun q => τ₀.commutes q }
    have hle : M ≤ Fix :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hτ₀_η₀)
    exact fun y => hle y.2
  let τ : GarlingGaloisGroup M E :=
    { τ₀ with commutes' := fun y => hτ₀_fix_M y }
  have hτ_ε₀ : τ ε₀ = ε₀⁻¹ := hτ₀_gen
  have hε₀_ne0 : ε₀ ≠ 0 := hprimE.ne_zero (by omega)
  have hε₀_ne_inv : ε₀ ≠ ε₀⁻¹ := by
    intro hEq
    have hsq : ε₀ ^ 2 = 1 := by
      calc ε₀ ^ 2 = ε₀ * ε₀ := sq ε₀
        _ = ε₀ * ε₀⁻¹ := by nth_rw 2 [hEq]
        _ = 1 := mul_inv_cancel₀ hε₀_ne0
    have hgarE : IsGarlingPrimitiveRoot m ε₀ :=
      (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε₀).mpr hprimE
    exact hgarE.2.2 2 (by omega) hm hsq
  have hτ_ne1 : τ ≠ 1 := by
    intro h1
    have := AlgEquiv.congr_fun h1 ε₀
    rw [hτ_ε₀, AlgEquiv.one_apply] at this
    exact hε₀_ne_inv this.symm
  have hτ_sq : τ ^ 2 = 1 := by
    rw [sq]
    apply AlgEquiv.coe_algHom_injective
    apply AlgHom.coe_ringHom_injective
    have hext : ∀ x : E, (τ * τ) x = x := by
      let Fix2 : IntermediateField ℚ E :=
        { carrier := {x : E | (τ * τ) x = x}
          add_mem' := fun {a b} ha hb => by change (τ * τ) (a + b) = a + b; rw [map_add, ha, hb]
          zero_mem' := map_zero (τ * τ)
          neg_mem' := fun {a} ha => by change (τ * τ) (-a) = -a; rw [map_neg, ha]
          mul_mem' := fun {a b} ha hb => by change (τ * τ) (a * b) = a * b; rw [map_mul, ha, hb]
          one_mem' := map_one (τ * τ)
          inv_mem' := fun {a} ha => by change (τ * τ) a⁻¹ = a⁻¹; rw [map_inv₀, ha]
          algebraMap_mem' := fun q => by
            change τ (τ (algebraMap ℚ E q)) = algebraMap ℚ E q
            have hq : algebraMap ℚ E q = algebraMap M E (algebraMap ℚ M q) :=
              IsScalarTower.algebraMap_apply ℚ M E q
            rw [hq, τ.commutes, τ.commutes] }
      have hε₀_fix2 : ε₀ ∈ Fix2 := by
        change τ (τ ε₀) = ε₀
        rw [hτ_ε₀, map_inv₀, hτ_ε₀, inv_inv]
      have htop_le : (⊤ : IntermediateField ℚ E) ≤ Fix2 := by
        rw [← hE_top]
        exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hε₀_fix2)
      exact fun x => htop_le IntermediateField.mem_top
    ext x
    exact hext x
  -- Quadratic polynomial `P = X^2 - ηM * X + 1 ∈ M[X]`:
  let P : M[X] := Polynomial.X ^ 2 - Polynomial.C ηM * Polynomial.X + 1
  have hP_deg_and_mon : P.Monic ∧ P.natDegree = 2 := by
    have hcoeff2 : P.coeff 2 = 1 := by
      dsimp [P]
      simp [Polynomial.coeff_one]
    have hdeg_le : P.natDegree ≤ 2 := by
      dsimp [P]
      compute_degree!
    have hdeg_ge : 2 ≤ P.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff2]; exact one_ne_zero)
    have hdeg : P.natDegree = 2 := le_antisymm hdeg_le hdeg_ge
    exact ⟨by rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcoeff2], hdeg⟩
  obtain ⟨hP_mon, hP_deg⟩ := hP_deg_and_mon
  have hP_aeval : Polynomial.aeval ε₀ P = 0 := by
    dsimp [P]
    simp only [map_add, map_sub, map_pow, map_mul, map_one, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have hηM_coe : algebraMap M E ηM = ε₀ + ε₀⁻¹ := rfl
    rw [hηM_coe, add_mul, inv_mul_cancel₀ hε₀_ne0]
    ring
  have hintM_ε₀ : IsIntegral M ε₀ := ⟨P, hP_mon, hP_aeval⟩
  have hME_adjoin : IntermediateField.adjoin M ({ε₀} : Set E) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let S : IntermediateField ℚ E :=
      (IntermediateField.adjoin M ({ε₀} : Set E)).restrictScalars ℚ
    have hεS : ε₀ ∈ S := IntermediateField.mem_adjoin_simple_self M ε₀
    have htopS : (⊤ : IntermediateField ℚ E) ≤ S := by
      rw [← hE_top]
      exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hεS)
    exact htopS IntermediateField.mem_top
  let pbME : PowerBasis M E :=
    (IntermediateField.adjoin.powerBasis hintM_ε₀).map
      ((IntermediateField.equivOfEq hME_adjoin).trans IntermediateField.topEquiv)
  have hpbME_gen : pbME.gen = ε₀ := by
    simp [pbME, IntermediateField.adjoin.powerBasis_gen]
  have hminM_dvd_P : minpoly M ε₀ ∣ P := minpoly.dvd M ε₀ hP_aeval
  have hdeg_min_le_2 : (minpoly M ε₀).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hminM_dvd_P hP_mon.ne_zero
    omega
  have hfin_QE : FiniteDimensional ℚ E := pbE.finite
  have hfin_ME : FiniteDimensional M E := pbME.finite
  have hfinrank_le_2 : Module.finrank M E ≤ 2 := by
    rw [pbME.finrank, pbME.dim_eq_natDegree_minpoly, hpbME_gen]
    exact hdeg_min_le_2
  -- Also `2 ≤ Nat.card (GarlingGaloisGroup M E) ≤ Module.finrank M E`:
  have hcard_gal_le : Nat.card (GarlingGaloisGroup M E) ≤ Module.finrank M E := by
    let _ : Fintype (GarlingGaloisGroup M E) := AlgEquiv.fintype M E
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le_finrank M E
  have hcard_gal_ge_2 : 2 ≤ Nat.card (GarlingGaloisGroup M E) := by
    let _ : Fintype (GarlingGaloisGroup M E) := AlgEquiv.fintype M E
    rw [Nat.card_eq_fintype_card]
    have hcard_pair : ({1, τ} : Finset (GarlingGaloisGroup M E)).card = 2 :=
      Finset.card_pair hτ_ne1.symm
    calc 2 = ({1, τ} : Finset (GarlingGaloisGroup M E)).card := hcard_pair.symm
      _ ≤ (Finset.univ : Finset (GarlingGaloisGroup M E)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (GarlingGaloisGroup M E) := rfl
  have hfinrankME : Module.finrank M E = 2 := by omega
  have hcard_gal : Nat.card (GarlingGaloisGroup M E) = 2 := by omega
  have hextME : extDegree M E = 2 := by
    rw [extDegree_eq_finrank, hfinrankME]
    rfl
  have hdeg_min_eq_2 : (minpoly M ε₀).natDegree = 2 := by
    have h := hfinrankME
    rw [pbME.finrank, pbME.dim_eq_natDegree_minpoly, hpbME_gen] at h
    exact h
  have hminM_eq_P : minpoly M ε₀ = P :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP_mon (minpoly.monic hintM_ε₀)
      hminM_dvd_P (by omega)
  have hP_irr : Irreducible P := hminM_eq_P ▸ minpoly.irreducible hintM_ε₀
  -- Tower law `finrank ℚ E = finrank ℚ M * finrank M E` gives `finrank ℚ F = φ(m) / 2`:
  have hfin_QM : FiniteDimensional ℚ M := FiniteDimensional.left ℚ M E
  have htower : Module.finrank ℚ M * Module.finrank M E = Module.finrank ℚ E :=
    Module.finrank_mul_finrank ℚ M E
  have hfinrankQM : Module.finrank ℚ M = Nat.totient m / 2 := by
    rw [hfinrankME, hfinrankQE] at htower
    omega
  have hfinrankQF : Module.finrank ℚ F = Nat.totient m / 2 := by
    rw [← LinearEquiv.finrank_eq isoMF.toLinearEquiv, hfinrankQM]
  -- Galoisness and Galois group identification:
  have hgalME : IsGarlingGaloisExtension M E := by
    have hfin_ext : IsFiniteExtension M E := (isFiniteExtension_iff_moduleFinite M E).mpr hfin_ME
    by_contra hng
    have hlt := (theorem_10_4_algEquiv (K := M) (L := E) hfin_ext).2 hng
    change Nat.card (GarlingGaloisGroup M E) < Module.finrank M E at hlt
    omega
  have hcyc_gal : IsCyclic (GarlingGaloisGroup M E) := by
    apply isCyclic_of_prime_card (p := 2)
    exact hcard_gal
  have hsetOrder_gal : setOrder (GarlingGaloisGroup M E) = 2 := by
    let _ : Fintype (GarlingGaloisGroup M E) := AlgEquiv.fintype M E
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard_gal]
    rfl
  have huniv_eq : (Set.univ : Set (GarlingGaloisGroup M E)) = {1, τ} := by
    let _ : Fintype (GarlingGaloisGroup M E) := AlgEquiv.fintype M E
    have hcard_u : (Finset.univ : Finset (GarlingGaloisGroup M E)).card = 2 := by
      rw [← Fintype.card, ← Nat.card_eq_fintype_card, hcard_gal]
    have hcard_p : ({1, τ} : Finset (GarlingGaloisGroup M E)).card = 2 :=
      Finset.card_pair hτ_ne1.symm
    have hfeq : ({1, τ} : Finset (GarlingGaloisGroup M E)) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by omega)
    ext σ
    simpa using (Finset.ext_iff.mp hfeq.symm σ)
  have hiso_zmod2 : Nonempty (GarlingGaloisGroup M E ≃* Multiplicative (ZMod 2)) := by
    have hord_τ : orderOf τ = 2 := by
      refine orderOf_eq_prime hτ_sq hτ_ne1
    let φ : Multiplicative (ZMod 2) →* GarlingGaloisGroup M E :=
      { toFun := fun x => τ ^ (Multiplicative.toAdd x).val
        map_one' := by simp
        map_mul' := fun x y => by
          change τ ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).val =
            τ ^ (Multiplicative.toAdd x).val * τ ^ (Multiplicative.toAdd y).val
          rw [← pow_add]
          have hmod : ((Multiplicative.toAdd x + Multiplicative.toAdd y).val) =
              ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 2 :=
            ZMod.val_add _ _
          rw [hmod, ← pow_mod_orderOf, hord_τ] }
    have hsurj : Function.Surjective φ := by
      intro σ
      have hmem : σ ∈ ({1, τ} : Set (GarlingGaloisGroup M E)) := huniv_eq ▸ Set.mem_univ σ
      rcases hmem with rfl | rfl
      · exact ⟨1, map_one φ⟩
      · refine ⟨Multiplicative.ofAdd (1 : ZMod 2), ?_⟩
        change τ ^ (1 : ZMod 2).val = τ
        have hval1 : (1 : ZMod 2).val = 1 := rfl
        rw [hval1, pow_one]
    have hinj : Function.Injective φ := by
      let _ : Fintype (GarlingGaloisGroup M E) := AlgEquiv.fintype M E
      have hcard1 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Fintype.card_multiplicative, ZMod.card]
      have hcard2 : Fintype.card (GarlingGaloisGroup M E) = 2 := by
        rw [← Nat.card_eq_fintype_card, hcard_gal]
      exact (Fintype.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcard1.trans hcard2.symm⟩ |>.1
    exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩
  exact ⟨⟨isoMF⟩, hfinrankME, hextME, hfinrankQE, hfinrankQF, hminM_eq_P, hP_irr, hgalME,
    hcyc_gal, hcard_gal, hsetOrder_gal, hiso_zmod2, τ, hτ_ne1, hτ_sq, hτ_ε₀, huniv_eq⟩

/-! ## §15.3 The Galois group of a cyclotomic polynomial (printed pp. 121–122, PDF pp. 129–130) -/

/-- Garling's notation `U_m` for the *multiplicative* group of units in the ring `ℤ_m`
(§15.3, printed p. 121 / PDF p. 129: *"Thus `(n̄_1, …, n̄_k)` [sic] is the **multiplicative** group
`U_m` of units in the ring `ℤ_m`."*). -/
abbrev GarlingUnitsZMod (m : ℕ) : Type :=
  (ZMod m)ˣ

/-- §15.3 Bézout characterization of `U_m`, isomorphism with `(ℤ ⧸ (m))ˣ`, and primitive-root
power enumeration `ε^{n_1}, …, ε^{n_k}` (printed p. 121 / PDF p. 129; OCR warning:
`garling1986_pages.txt` l. 4518 completely deletes the displayed list `ε^{n_1}, ε^{n_2}, …, ε^{n_k}`). -/
theorem section_15_3_units_zmod_coprime {m : ℕ} (hm : 1 ≤ m) :
    Nonempty ((ℤ ⧸ Ideal.span {(m : ℤ)})ˣ ≃* GarlingUnitsZMod m) ∧
    Nat.card (GarlingUnitsZMod m) = Nat.totient m ∧
    (∀ n : ℕ, IsUnit (n : ZMod m) ↔ Nat.Coprime n m) ∧
    (∀ n : ℕ, Nat.Coprime n m ↔ ∃ a b : ℤ, a * (n : ℤ) + b * (m : ℤ) = 1) ∧
    (∀ {L : Type u} [Field L] {ε : L}, IsGarlingPrimitiveRoot m ε →
      garlingPrimRootsFinset L m =
        ((Finset.range m).filter (fun n => Nat.Coprime n m)).image (fun n => ε ^ n)) := by
  classical
  have _ : NeZero m := ⟨by omega⟩
  have hcard : Nat.card (GarlingUnitsZMod m) = Nat.totient m := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hbezout : ∀ n : ℕ, Nat.Coprime n m ↔ ∃ a b : ℤ, a * (n : ℤ) + b * (m : ℤ) = 1 := by
    intro n
    constructor
    · intro hcop
      refine ⟨Nat.gcdA n m, Nat.gcdB n m, ?_⟩
      have h := Nat.gcd_eq_gcd_ab n m
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      linarith
    · rintro ⟨a, b, hab⟩
      refine Nat.coprime_of_dvd' fun p hp hpn hpm => ?_
      have hpz_n : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hpn
      have hpz_m : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
      have hpz_1 : (p : ℤ) ∣ 1 := by
        rw [← hab]
        exact dvd_add (dvd_mul_of_dvd_right hpz_n a) (dvd_mul_of_dvd_right hpz_m b)
      have hp1 : p ∣ 1 := Int.natCast_dvd_natCast.mp hpz_1
      exact absurd (Nat.dvd_one.mp hp1) hp.ne_one
  refine ⟨⟨Units.mapEquiv (Int.quotientSpanNatEquivZMod m).toMulEquiv⟩, hcard,
    fun n => ZMod.isUnit_iff_coprime n m, hbezout, ?_⟩
  intro L _ ε hε
  have hprim : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm ε).mp hε
  ext θ
  simp only [garlingPrimRootsFinset, mem_primitiveRoots (by omega : 0 < m), Finset.mem_image,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hθ
    obtain ⟨r, hr_lt, rfl⟩ := hprim.eq_pow_of_pow_eq_one hθ.pow_eq_one
    exact ⟨r, ⟨hr_lt, (hprim.pow_iff_coprime (by omega : 0 < m) r).mp hθ⟩, rfl⟩
  · rintro ⟨r, ⟨_, hcop⟩, rfl⟩
    exact hprim.pow_of_coprime r hcop

/-- Helper: under `¬ (ringChar K ∣ m)`, `Φ_m` splits over an extension `M : K` iff `x^m - 1` splits
over `M`. -/
private theorem garlingSplitsOver_cyclotomic_iff_X_pow_sub_one {K : Type*} (M : Type*)
    [Field K] [Field M] [Algebra K M] {m : ℕ} (hchar : ¬ (ringChar K ∣ m)) :
    GarlingSplitsOver K M (Polynomial.cyclotomic m K) ↔
    GarlingSplitsOver K M (Polynomial.X ^ m - 1) := by
  obtain ⟨hm_pos, hmK_ne0⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have hmM_ne0 : (m : M) ≠ 0 := fun h0 =>
    hmK_ne0 ((algebraMap K M).injective (by rw [map_natCast, h0, map_zero]))
  have _ : NeZero (m : M) := ⟨hmM_ne0⟩
  rw [garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits, Polynomial.map_cyclotomic]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  constructor
  · intro hs
    have hdeg_pos : 0 < (Polynomial.cyclotomic m M).degree :=
      Polynomial.degree_cyclotomic_pos m M (by omega)
    obtain ⟨ε, hε_root⟩ := Polynomial.Splits.exists_eval_eq_zero hs (ne_of_gt hdeg_pos)
    have hprim : IsPrimitiveRoot ε m :=
      Polynomial.isRoot_cyclotomic_iff.mp hε_root
    simpa using Polynomial.X_pow_sub_one_splits hprim
  · intro hs
    have hxm1_ne0 : (Polynomial.X ^ m - 1 : M[X]) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < m) (1 : M)
    exact hs.of_dvd hxm1_ne0 (Polynomial.cyclotomic.dvd_X_pow_sub_one m M)

/-- §15.3 opening equivalence of splitting fields for `Φ_m` and `x^m - 1` and simplicity `L = K(ε)`
(printed p. 121 / PDF p. 129):
*"Suppose that `L : K` is a splitting field extension for the cyclotomic polynomial `Φ_m` over `K`.
If `ε` is a primitive `m`th root of unity then, as we have seen, `L = K(ε)`."* -/
theorem section_15_3_splittingField_cyclotomic_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m)) :
    (IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K) ↔
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1)) ∧
    (IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K) →
      ∀ {ε : L}, IsGarlingPrimitiveRoot m ε →
        IntermediateField.adjoin K ({ε} : Set L) = ⊤ ∧ IsSimpleExtension K L) := by
  have hsf_iff :
      IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K) ↔
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ m - 1) := by
    unfold IsGarlingSplittingFieldExtension
    constructor
    · rintro ⟨hL, hmin⟩
      exact ⟨(garlingSplitsOver_cyclotomic_iff_X_pow_sub_one L hchar).mp hL,
        fun M hM hMs => hmin M hM
          ((garlingSplitsOver_cyclotomic_iff_X_pow_sub_one M hchar).mpr hMs)⟩
    · rintro ⟨hL, hmin⟩
      exact ⟨(garlingSplitsOver_cyclotomic_iff_X_pow_sub_one L hchar).mpr hL,
        fun M hM hMs => hmin M hM
          ((garlingSplitsOver_cyclotomic_iff_X_pow_sub_one M hchar).mp hMs)⟩
  refine ⟨hsf_iff, fun hsf ε hε => ?_⟩
  obtain ⟨hadj, _, hsimp⟩ :=
    section_15_1_simple_extension_of_prim_root hchar (hsf_iff.mp hsf) hε
  exact ⟨hadj, hsimp⟩

/-- Garling's explicit §15.3 Galois-group homomorphism `σ ↦ n̄_{j(σ)} : Γ_K(Φ_m) →* U_m`
(printed p. 121 / PDF p. 129: *"and so the mapping `σ → n̄_{j(σ)}` is a homomorphism of `Γ_K(Φ_m)`
into `U_m`"*), sending each `K`-automorphism `σ` of `L` to the unique unit `u ∈ (ZMod m)ˣ` such that
`σ(ε) = ε^u` for every primitive `m`th root of unity `ε ∈ L`. -/
noncomputable def garlingCyclotomicGalHom {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K)) :
    GarlingPolyGaloisGroup K L (Polynomial.cyclotomic m K) →* GarlingUnitsZMod m :=
  let hm_pos : 1 ≤ m := (pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar).1
  let _ : NeZero m := ⟨by omega⟩
  let hsf_xm1 := (section_15_3_splittingField_cyclotomic_iff hchar).1.mp hsf
  let hex := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf_xm1
  let hprim₀ : IsPrimitiveRoot (Classical.choose hex) m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos _).mp (Classical.choose_spec hex)
  hprim₀.autToPow K

/-- Universal action and injectivity specification of `garlingCyclotomicGalHom` (§15.3, printed
p. 121 / PDF p. 129): `garlingCyclotomicGalHom` is independent of the chosen primitive `m`th root of
unity (`σ(ε) = ε^{n_{j(σ)}}` for **every** primitive `m`th root of unity `ε ∈ L`) and is injective. -/
theorem garlingCyclotomicGalHom_spec_and_injective {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K)) :
    (∀ (ε : L), IsGarlingPrimitiveRoot m ε →
      ∀ σ : GarlingPolyGaloisGroup K L (Polynomial.cyclotomic m K),
        σ ε = ε ^ ((garlingCyclotomicGalHom hchar hsf σ : ZMod m).val)) ∧
    Function.Injective (garlingCyclotomicGalHom hchar hsf) := by
  obtain ⟨hm_pos, _⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  let _ : NeZero m := ⟨by omega⟩
  let hsf_xm1 := (section_15_3_splittingField_cyclotomic_iff hchar).1.mp hsf
  let hex := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf_xm1
  let ε₀ : L := Classical.choose hex
  have hgar₀ : IsGarlingPrimitiveRoot m ε₀ := Classical.choose_spec hex
  have hprim₀ : IsPrimitiveRoot ε₀ m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε₀).mp hgar₀
  have hspec₀ : ∀ σ : GarlingPolyGaloisGroup K L (Polynomial.cyclotomic m K),
      σ ε₀ = ε₀ ^ ((garlingCyclotomicGalHom hchar hsf σ : ZMod m).val) := by
    intro σ
    exact (hprim₀.autToPow_spec K σ).symm
  have hspec_all : ∀ (ε : L), IsGarlingPrimitiveRoot m ε →
      ∀ σ : GarlingPolyGaloisGroup K L (Polynomial.cyclotomic m K),
        σ ε = ε ^ ((garlingCyclotomicGalHom hchar hsf σ : ZMod m).val) := by
    intro ε hε σ
    have hprim : IsPrimitiveRoot ε m :=
      (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
    obtain ⟨r, _, rfl⟩ := hprim₀.eq_pow_of_pow_eq_one hprim.pow_eq_one
    rw [map_pow, hspec₀ σ, pow_right_comm]
  refine ⟨hspec_all, ?_⟩
  intro σ τ hEq
  have hε_eq : σ ε₀ = τ ε₀ := by
    rw [hspec₀ σ, hspec₀ τ, hEq]
  obtain ⟨hadj, _, _⟩ := section_15_1_simple_extension_of_prim_root hchar hsf_xm1 hgar₀
  let EqField : IntermediateField K L :=
    { carrier := {x : L | σ x = τ x}
      add_mem' := fun {a b} ha hb => by change σ (a + b) = τ (a + b); rw [map_add, map_add, ha, hb]
      zero_mem' := by change σ 0 = τ 0; rw [map_zero, map_zero]
      neg_mem' := fun {a} ha => by change σ (-a) = τ (-a); rw [map_neg, map_neg, ha]
      mul_mem' := fun {a b} ha hb => by change σ (a * b) = τ (a * b); rw [map_mul, map_mul, ha, hb]
      one_mem' := by change σ 1 = τ 1; rw [map_one, map_one]
      inv_mem' := fun {a} ha => by change σ a⁻¹ = τ a⁻¹; rw [map_inv₀, map_inv₀, ha]
      algebraMap_mem' := fun k => by change σ (algebraMap K L k) = τ (algebraMap K L k); simp }
  have htop : (⊤ : IntermediateField K L) ≤ EqField := by
    rw [← hadj]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hε_eq)
  ext x
  exact htop IntermediateField.mem_top

/-- **Theorem 15.4** (§15.3, printed p. 121 / PDF p. 129; proved in the preceding prose on p. 121):
*"If `Φ_m` is the `m`th cyclotomic polynomial over `K`, `Γ_K(Φ_m)` is an abelian group which is
isomorphic to a subgroup of `U_m`, the multiplicative group of units of the ring `ℤ_m`. `Φ_m` is
irreducible over `K` if and only if `Γ_K(Φ_m)` is isomorphic to `U_m`."* -/
theorem theorem_15_4 {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m : ℕ}
    (hchar : ¬ (ringChar K ∣ m))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic m K)) :
    let G := GarlingPolyGaloisGroup K L (Polynomial.cyclotomic m K)
    (∀ σ τ : G, σ * τ = τ * σ) ∧
    (∃ H : Subgroup (GarlingUnitsZMod m), Nonempty (G ≃* H)) ∧
    (Irreducible (Polynomial.cyclotomic m K) ↔
      Nonempty (G ≃* GarlingUnitsZMod m)) ∧
    (IsGarlingIrreducible (Polynomial.cyclotomic m K) ↔
      Nonempty (G ≃* GarlingUnitsZMod m)) ∧
    (Irreducible (Polynomial.cyclotomic m K) ↔
      Function.Surjective (garlingCyclotomicGalHom hchar hsf)) := by
  intro G
  classical
  obtain ⟨hm_pos, hmK_ne0⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  let _ : NeZero m := ⟨by omega⟩
  obtain ⟨_, hinj⟩ := garlingCyclotomicGalHom_spec_and_injective hchar hsf
  let φ := garlingCyclotomicGalHom hchar hsf
  -- 1. `Γ_K(Φ_m)` is abelian:
  have hab : ∀ σ τ : G, σ * τ = τ * σ := by
    intro σ τ
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  -- 2. `Γ_K(Φ_m)` is isomorphic to the subgroup `φ.range ≤ U_m`:
  have hsub : ∃ H : Subgroup (GarlingUnitsZMod m), Nonempty (G ≃* H) := by
    refine ⟨φ.range, ⟨MulEquiv.ofBijective φ.rangeRestrict ⟨?_, φ.rangeRestrict_surjective⟩⟩⟩
    intro σ τ h
    exact hinj (congrArg Subtype.val h)
  -- 3. `Φ_m` is irreducible over `K` iff `φ` is surjective iff `Γ_K(Φ_m) ≃* U_m`:
  let hsf_xm1 := (section_15_3_splittingField_cyclotomic_iff hchar).1.mp hsf
  obtain ⟨hgalKL, _, _, _, _, _⟩ := section_15_1_roots_group_cyclic hchar hsf_xm1
  obtain ⟨ε, hε_gar⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hchar hsf_xm1
  have hε_prim : IsPrimitiveRoot ε m :=
    (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε_gar
  obtain ⟨hadj, _, _⟩ := section_15_1_simple_extension_of_prim_root hchar hsf_xm1 hε_gar
  have hε_cyc : Polynomial.aeval ε (Polynomial.cyclotomic m K) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hε_prim.isRoot_cyclotomic (by omega)
  have hint_ε : IsIntegral K ε :=
    ⟨Polynomial.cyclotomic m K, Polynomial.cyclotomic.monic m K, hε_cyc⟩
  have hmin_dvd : minpoly K ε ∣ Polynomial.cyclotomic m K := minpoly.dvd K ε hε_cyc
  let pbKL : PowerBasis K L :=
    (IntermediateField.adjoin.powerBasis hint_ε).map
      ((IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv)
  have hpbKL_gen : pbKL.gen = ε := by
    simp [pbKL, IntermediateField.adjoin.powerBasis_gen]
  have hfinrankKL : Module.finrank K L = (minpoly K ε).natDegree := by
    rw [pbKL.finrank, pbKL.dim_eq_natDegree_minpoly, hpbKL_gen]
  have hcardG : Nat.card G = Module.finrank K L :=
    (theorem_10_4_algEquiv (K := K) (L := L) hgalKL.1).1 hgalKL
  have hcardUm : Nat.card (GarlingUnitsZMod m) = Nat.totient m := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  let _ : Fintype G := AlgEquiv.fintype K L
  have hirr_imp_surj : Irreducible (Polynomial.cyclotomic m K) → Function.Surjective φ := by
    intro hirr
    have hmin_eq : minpoly K ε = Polynomial.cyclotomic m K :=
      (minpoly.eq_of_irreducible_of_monic hirr hε_cyc (Polynomial.cyclotomic.monic m K)).symm
    have hcard_eq : Fintype.card G = Fintype.card (GarlingUnitsZMod m) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardG, hfinrankKL, hmin_eq,
        Polynomial.natDegree_cyclotomic, hcardUm]
    exact ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_eq⟩).2
  have hsurj_imp_iso : Function.Surjective φ → Nonempty (G ≃* GarlingUnitsZMod m) :=
    fun hsurj => ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩
  have hiso_imp_irr : Nonempty (G ≃* GarlingUnitsZMod m) →
      Irreducible (Polynomial.cyclotomic m K) := by
    rintro ⟨e⟩
    have hcard_eq : Nat.card G = Nat.card (GarlingUnitsZMod m) := Nat.card_congr e.toEquiv
    have hdeg_eq : (minpoly K ε).natDegree = (Polynomial.cyclotomic m K).natDegree := by
      rw [← hfinrankKL, ← hcardG, hcard_eq, hcardUm, Polynomial.natDegree_cyclotomic]
    have hpoly_eq : Polynomial.cyclotomic m K = minpoly K ε :=
      (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Polynomial.cyclotomic.monic m K)
        (minpoly.monic hint_ε) hmin_dvd hdeg_eq.ge).symm
    rw [hpoly_eq]
    exact minpoly.irreducible hint_ε
  have hirr_iff_iso : Irreducible (Polynomial.cyclotomic m K) ↔
      Nonempty (G ≃* GarlingUnitsZMod m) :=
    ⟨fun h => hsurj_imp_iso (hirr_imp_surj h), hiso_imp_irr⟩
  have hirr_iff_surj : Irreducible (Polynomial.cyclotomic m K) ↔ Function.Surjective φ :=
    ⟨hirr_imp_surj, fun hs => hiso_imp_irr (hsurj_imp_iso hs)⟩
  exact ⟨hab, hsub, hirr_iff_iso, (isGarlingIrreducible_iff _).trans hirr_iff_iso, hirr_iff_surj⟩

/-- Helper constructing an explicit Klein four-group isomorphism
`G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)` for any commutative group `G` of cardinality
`4` containing two distinct non-trivial involutions `a, b`. -/
private noncomputable def kleinFourMulEquiv {G : Type*} [CommGroup G] [Fintype G]
    (hcard : Fintype.card G = 4) {a b : G}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := by
  classical
  have hpow2 : ∀ {g : G}, g ^ 2 = 1 → ∀ n : ℕ, g ^ (n % 2) = g ^ n := by
    intro g hg2 n
    conv_rhs => rw [← Nat.div_add_mod n 2]
    rw [pow_add, pow_mul, hg2, one_pow, one_mul]
  let φ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* G :=
    { toFun := fun p => a ^ (Multiplicative.toAdd p.1).val * b ^ (Multiplicative.toAdd p.2).val
      map_one' := by simp
      map_mul' := fun p q => by
        change a ^ (Multiplicative.toAdd p.1 + Multiplicative.toAdd q.1).val *
            b ^ (Multiplicative.toAdd p.2 + Multiplicative.toAdd q.2).val =
          (a ^ (Multiplicative.toAdd p.1).val * b ^ (Multiplicative.toAdd p.2).val) *
            (a ^ (Multiplicative.toAdd q.1).val * b ^ (Multiplicative.toAdd q.2).val)
        rw [ZMod.val_add, ZMod.val_add, hpow2 ha2, hpow2 hb2, pow_add, pow_add]
        ac_rfl }
  have hab_ne1 : a * b ≠ 1 := by
    intro h1
    apply hab
    calc a = a * (b * b) := by rw [← sq, hb2, mul_one]
      _ = (a * b) * b := by ac_rfl
      _ = b := by rw [h1, one_mul]
  have hinj : Function.Injective φ := by
    intro p q hpq
    rcases p with ⟨x1, y1⟩
    rcases q with ⟨x2, y2⟩
    revert hpq
    -- Case-split on `Multiplicative.toAdd` in `ZMod 2`:
    obtain ⟨u1, rfl⟩ := Multiplicative.ofAdd.surjective x1
    obtain ⟨v1, rfl⟩ := Multiplicative.ofAdd.surjective y1
    obtain ⟨u2, rfl⟩ := Multiplicative.ofAdd.surjective x2
    obtain ⟨v2, rfl⟩ := Multiplicative.ofAdd.surjective y2
    fin_cases u1 <;> fin_cases v1 <;> fin_cases u2 <;> fin_cases v2 <;>
      intro hpq
    all_goals
      try rfl
      dsimp [φ] at hpq
      change a ^ (_ : ℕ) * b ^ (_ : ℕ) = a ^ (_ : ℕ) * b ^ (_ : ℕ) at hpq
      simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one] at hpq
    · exact absurd hpq hb1.symm
    · exact absurd hpq ha1.symm
    · exact absurd hpq hab_ne1.symm
    · exact absurd hpq hb1
    · exact absurd hpq hab.symm
    · exact absurd (mul_right_cancel (by rw [hpq, one_mul])) ha1.symm
    · exact absurd hpq ha1
    · exact absurd hpq hab
    · exact absurd (mul_left_cancel (by rw [← hpq, mul_one])) hb1
    · exact absurd hpq hab_ne1
    · exact absurd (mul_right_cancel (by rw [← hpq, one_mul])) ha1
    · exact absurd (mul_left_cancel (by rw [hpq, mul_one])) hb1.symm
  have hcard_dom : Fintype.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
    rw [Fintype.card_prod, Fintype.card_multiplicative, Fintype.card_multiplicative, ZMod.card]
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_dom.trans hcard.symm⟩
  exact (MulEquiv.ofBijective φ hbij).symm

/-- Helper constructing `G ≃* Multiplicative (ZMod n)` for a finite group `G` of cardinality `n ≥ 1`
generated by an element `g` of order `n`. -/
private noncomputable def cyclicMulEquivOfOrderOf {G : Type*} [Group G] [Fintype G] {n : ℕ}
    [NeZero n] (hcard : Fintype.card G = n) {g : G} (hord : orderOf g = n) :
    G ≃* Multiplicative (ZMod n) := by
  let φ : Multiplicative (ZMod n) →* G :=
    { toFun := fun x => g ^ (Multiplicative.toAdd x).val
      map_one' := by simp
      map_mul' := fun x y => by
        change g ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).val =
          g ^ (Multiplicative.toAdd x).val * g ^ (Multiplicative.toAdd y).val
        rw [ZMod.val_add, ← pow_mod_orderOf, hord, pow_add] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective x
    obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective y
    dsimp [φ] at hxy
    have hmod : u.val ≡ v.val [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hxy
    rw [hord] at hmod
    have huv : u.val = v.val := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt u.val_lt, Nat.mod_eq_of_lt v.val_lt] at hmod
      exact hmod
    exact congrArg Multiplicative.ofAdd (ZMod.val_injective n huv)
  have hcard_dom : Fintype.card (Multiplicative (ZMod n)) = n := by
    rw [Fintype.card_multiplicative, ZMod.card]
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_dom.trans hcard.symm⟩
  exact (MulEquiv.ofBijective φ hbij).symm

/-- §15.3 prose worked example on `U_{12} = {1̄, 5̄, 7̄, 11̄} ≅ ℤ_2 × ℤ_2` (printed p. 121 /
PDF p. 129; OCR warning: `garling1986_pages.txt` ll. 4545–4546 corrupts `5̄` to `3` twice, writing
`U12 = {1, 3, 7, 11}` and `12 = 32 = 112 = 1`, even though `3̄` is not a unit in `ℤ_{12}`!). -/
theorem section_15_3_u12_example :
    (Finset.univ.image (Units.val : GarlingUnitsZMod 12 → ZMod 12)) = {1, 5, 7, 11} ∧
    ¬ IsUnit (3 : ZMod 12) ∧
    (1 : ZMod 12) ^ 2 = 1 ∧
    (5 : ZMod 12) ^ 2 = 1 ∧
    (7 : ZMod 12) ^ 2 = 1 ∧
    (11 : ZMod 12) ^ 2 = 1 ∧
    Nonempty (GarlingUnitsZMod 12 ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    ¬ IsCyclic (GarlingUnitsZMod 12) := by
  have himg : (Finset.univ.image (Units.val : GarlingUnitsZMod 12 → ZMod 12)) = {1, 5, 7, 11} := by
    decide
  have hnot3 : ¬ IsUnit (3 : ZMod 12) := by
    rw [show (3 : ZMod 12) = ((3 : ℕ) : ZMod 12) from rfl, ZMod.isUnit_iff_coprime]
    decide
  let u5 : GarlingUnitsZMod 12 := ZMod.unitOfCoprime 5 (by decide)
  let u7 : GarlingUnitsZMod 12 := ZMod.unitOfCoprime 7 (by decide)
  have hcard12 : Fintype.card (GarlingUnitsZMod 12) = 4 := by
    rw [ZMod.card_units_eq_totient]
    decide
  have hiso : Nonempty (GarlingUnitsZMod 12 ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    ⟨kleinFourMulEquiv hcard12 (a := u5) (b := u7)
      (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have hnot_cyc : ¬ IsCyclic (GarlingUnitsZMod 12) := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hg2 : g ^ 2 = 1 := by
      revert g
      decide
    have hord_le : orderOf g ≤ 2 := orderOf_le_of_pow_eq_one (by omega) hg2
    have hcard_zpow : Nat.card (Subgroup.zpowers g) = 4 := by
      have htop : Subgroup.zpowers g = ⊤ :=
        eq_top_iff.mpr fun x _ => Subgroup.mem_zpowers_iff.mpr (hg x)
      rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, hcard12]
    rw [Nat.card_zpowers] at hcard_zpow
    omega
  exact ⟨himg, hnot3, by decide, by decide, by decide, by decide, hiso, hnot_cyc⟩

/-- **Corollary** [to **Theorem 15.4**] (§15.3, printed p. 122 / PDF p. 130):
*"If `p` is a prime then either `Φ_p` splits over `K` or `Γ_K(Φ_p)` is cyclic."*

Proved unconditionally across **all** fields `K` (of any characteristic, including `ringChar K = p`,
where `Φ_p(x) = (x - 1)^{p - 1}` splits over `K` and `Γ_K(Φ_p)` is trivial) and **all** primes `p`:
establishes the printed inclusive disjunction, the strengthened disjunction
`Splits ∨ (Nontrivial ∧ IsCyclic)`, and unconditional cyclicity `IsCyclic (Γ_K(Φ_p))` in every case. -/
theorem corollary_to_theorem_15_4 {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {p : ℕ} (hp : Nat.Prime p)
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic p K)) :
    let G := GarlingPolyGaloisGroup K L (Polynomial.cyclotomic p K)
    (GarlingSplitsOver K K (Polynomial.cyclotomic p K) ∨ IsCyclic G) ∧
    (GarlingSplitsOver K K (Polynomial.cyclotomic p K) ∨ (Nontrivial G ∧ IsCyclic G)) ∧
    IsCyclic G := by
  intro G
  classical
  have _ : Fact p.Prime := ⟨hp⟩
  by_cases hchar : ringChar K ∣ p
  · -- When `ringChar K ∣ p`, `ringChar K = p` and `Φ_p(x) = (x - 1)^{p - 1}` splits over `K`:
    have hr_ne0 : ringChar K ≠ 0 := by
      intro h0
      rw [h0] at hchar
      exact hp.ne_zero (zero_dvd_iff.mp hchar)
    have hr_prime : Nat.Prime (ringChar K) :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hr_ne0
    have hchar_eq : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp).mp hchar
    have _ : CharP K p := hchar_eq ▸ inferInstance
    have hpoly_eq : Polynomial.cyclotomic p K = (Polynomial.X - 1 : K[X]) ^ (p - 1) := by
      apply mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : K))
      have h1 : Polynomial.cyclotomic p K * (Polynomial.X - 1) = Polynomial.X ^ p - 1 :=
        Polynomial.cyclotomic_prime_mul_X_sub_one K p
      have h2 : (Polynomial.X - 1 : K[X]) ^ (p - 1) * (Polynomial.X - 1) =
          (Polynomial.X - 1 : K[X]) ^ p := by
        rw [← pow_succ, Nat.sub_add_cancel hp.pos]
      have h3 : (Polynomial.X - 1 : K[X]) ^ p = Polynomial.X ^ p - 1 := by
        rw [sub_pow_char, one_pow]
      simp only [Polynomial.C_1]
      rw [h1, h2, h3]
    have hsplitsK : GarlingSplitsOver K K (Polynomial.cyclotomic p K) := by
      rw [garlingSplitsOver_iff_splits, Polynomial.map_id, hpoly_eq]
      exact (Polynomial.Splits.X_sub_C (1 : K)).pow (p - 1)
    have hsplits_bot :
        GarlingSplitsOver K (⊥ : IntermediateField K L) (Polynomial.cyclotomic p K) := by
      rw [garlingSplitsOver_iff_splits]
      have hmap : (Polynomial.cyclotomic p K).map (algebraMap K (⊥ : IntermediateField K L)) =
          (Polynomial.X - 1) ^ (p - 1) := by
        rw [hpoly_eq, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
      rw [hmap]
      exact (Polynomial.Splits.X_sub_C (1 : (⊥ : IntermediateField K L))).pow (p - 1)
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ := by
      by_contra hne
      exact hsf.2 ⊥ hne hsplits_bot
    have hsubG : Subsingleton G := by
      refine ⟨fun σ τ => ?_⟩
      ext x
      have hx : x ∈ (⊥ : IntermediateField K L) := hbot_top ▸ IntermediateField.mem_top
      rcases IntermediateField.mem_bot.mp hx with ⟨k, rfl⟩
      simp
    have hcycG : IsCyclic G := isCyclic_of_subsingleton
    exact ⟨Or.inl hsplitsK, Or.inl hsplitsK, hcycG⟩
  · -- Standing Chapter 15 case `¬ (ringChar K ∣ p)`: `G` embeds into `U_p = (ZMod p)ˣ`, which is cyclic by `Theorem 12.3`!
    obtain ⟨_, ⟨H, ⟨eGH⟩⟩, _, _, _⟩ := theorem_15_4 hchar hsf
    obtain ⟨hcyc_Up, _, _⟩ := corollary_1_to_theorem_12_3 (ZMod p)
    have _ : IsCyclic (GarlingUnitsZMod p) := hcyc_Up
    have hcyc_H : IsCyclic H := Subgroup.isCyclic H
    have hcycG : IsCyclic G := isCyclic_of_surjective eGH.symm eGH.symm.surjective
    refine ⟨Or.inr hcycG, ?_, hcycG⟩
    by_cases hsp : GarlingSplitsOver K K (Polynomial.cyclotomic p K)
    · exact Or.inl hsp
    · right
      refine ⟨?_, hcycG⟩
      -- Since `Φ_p` does not split over `K`, `⊥ ≠ ⊤` in `IntermediateField K L`, so `1 < [L : K] = |G|`:
      have hsf_xm1 := (section_15_3_splittingField_cyclotomic_iff hchar).1.mp hsf
      obtain ⟨hgalKL, _, _, _, _, _⟩ := section_15_1_roots_group_cyclic hchar hsf_xm1
      have hcardG : Nat.card G = Module.finrank K L :=
        (theorem_10_4_algEquiv (K := K) (L := L) hgalKL.1).1 hgalKL
      have hbot_ne_top : (⊥ : IntermediateField K L) ≠ ⊤ := by
        intro hbt
        apply hsp
        rw [garlingSplitsOver_iff_splits, Polynomial.map_id]
        have hsL : ((Polynomial.cyclotomic p K).map (algebraMap K L)).Splits :=
          (garlingSplitsOver_iff_splits K L _).mp hsf.1
        have hsurj : Function.Surjective (algebraMap K L) := by
          intro y
          have hy : y ∈ (⊥ : IntermediateField K L) := hbt ▸ IntermediateField.mem_top
          exact IntermediateField.mem_bot.mp hy
        let isoKL : K ≃+* L := RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, hsurj⟩
        have hmap_symm := hsL.map isoKL.symm.toRingHom
        have hcomp : isoKL.symm.toRingHom.comp (algebraMap K L) = RingHom.id K := by
          ext x
          exact isoKL.symm_apply_apply x
        rwa [Polynomial.map_map, hcomp, Polynomial.map_id] at hmap_symm
      have _ : FiniteDimensional K L := (isFiniteExtension_iff_moduleFinite K L).mp hgalKL.1
      have hfinrank_gt1 : 1 < Module.finrank K L := by
        by_contra hle1
        have hpos : 0 < Module.finrank K L := Module.finrank_pos
        have heq1 : Module.finrank K L = 1 := by omega
        exact hbot_ne_top (IntermediateField.bot_eq_top_of_finrank_eq_one heq1)
      let _ : Fintype G := AlgEquiv.fintype K L
      exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

/-- **Exercise 15.5** (`QUEUE.md` fidelity hold — *"Find the Galois groups..."* identification
prompt; §15.3, printed p. 122 / PDF p. 130):
*"Find the Galois groups of `x^4 + 1` and `x^5 + 1` over `ℚ`."*

Proved universally across **all** splitting field extensions `L : ℚ`:
1. `x^4 + 1 = Φ_8(x)` is irreducible over `ℚ`, and `Γ_ℚ(x^4 + 1) ≃* U_8 ≃* ℤ_2 × ℤ_2 ≃* viergruppe`
   (abelian, non-cyclic of order `4`);
2. `x^5 + 1 = (x + 1) Φ_{10}(x)` (`Φ_{10}(x) = x^4 - x^3 + x^2 - x + 1` irreducible over `ℚ`) has
   the same splitting fields over `ℚ` as `Φ_{10}`, and `Γ_ℚ(x^5 + 1) ≃* U_{10} ≃* ℤ_4`
   (cyclic of order `4`). -/
theorem exercise_15_5 :
    ((Polynomial.X ^ 4 + 1 : ℚ[X]) = Polynomial.cyclotomic 8 ℚ ∧
      Irreducible (Polynomial.X ^ 4 + 1 : ℚ[X]) ∧
      ∀ {L : Type u} [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 + 1) →
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1)) = 4 ∧
        ¬ IsCyclic (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1)) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1) ≃* GarlingUnitsZMod 8) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1) ≃*
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1) ≃* viergruppe)) ∧
    ((Polynomial.X ^ 5 + 1 : ℚ[X]) =
        (Polynomial.X + 1) * Polynomial.cyclotomic 10 ℚ ∧
      Polynomial.cyclotomic 10 ℚ =
        Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X ^ 2 - Polynomial.X + 1 ∧
      Irreducible (Polynomial.cyclotomic 10 ℚ) ∧
      (∀ {L : Type u} [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 5 + 1) ↔
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic 10 ℚ)) ∧
      ∀ {L : Type u} [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 5 + 1) →
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1)) = 4 ∧
        IsCyclic (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1)) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1) ≃* GarlingUnitsZMod 10) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1) ≃*
          Multiplicative (ZMod 4))) := by
  -- Part 1: `x^4 + 1 = Φ_8(x)` over `ℚ`
  have hphi8 : (Polynomial.X ^ 4 + 1 : ℚ[X]) = Polynomial.cyclotomic 8 ℚ := by
    have h := exercise_15_3_cyclotomic ℚ Nat.prime_two (n := 3) (by omega)
    simpa [Finset.sum_range_succ, add_comm] using h.symm
  have hirr8 : Irreducible (Polynomial.X ^ 4 + 1 : ℚ[X]) := by
    rw [hphi8]
    exact (theorem_15_3 (m := 8) (by omega)).1
  have hcharQ8 : ¬ (ringChar ℚ ∣ 8) := by
    rw [ringChar.eq_zero]
    decide
  let u8_3 : GarlingUnitsZMod 8 := ZMod.unitOfCoprime 3 (by decide)
  let u8_5 : GarlingUnitsZMod 8 := ZMod.unitOfCoprime 5 (by decide)
  have hcard_u8 : Fintype.card (GarlingUnitsZMod 8) = 4 := by
    rw [ZMod.card_units_eq_totient]
    decide
  let iso_u8_v4 : GarlingUnitsZMod 8 ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    kleinFourMulEquiv hcard_u8 (a := u8_3) (b := u8_5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Also `viergruppe ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`:
  have hcard_vier : Fintype.card viergruppe = 4 := by decide
  let v_a : viergruppe := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩
  let v_b : viergruppe := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩
  have hcomm_vier : ∀ x y : viergruppe, x * y = y * x := by decide
  let _ : CommGroup viergruppe :=
    { inferInstanceAs (Group viergruppe) with mul_comm := hcomm_vier }
  let iso_vier_v4 : viergruppe ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    kleinFourMulEquiv hcard_vier (a := v_a) (b := v_b)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Part 2: `x^5 + 1 = (x + 1) Φ_{10}(x)` over `ℚ`
  have hphi10 : Polynomial.cyclotomic 10 ℚ =
      Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X ^ 2 - Polynomial.X + 1 := by
    have h2n := exercise_15_2_cyclotomic ℚ (n := 5) (by decide) (by omega)
    have hp5 : Polynomial.cyclotomic 5 ℚ = ∑ i ∈ Finset.range 5, (Polynomial.X : ℚ[X]) ^ i := by
      have _ : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact Polynomial.cyclotomic_prime ℚ 5
    rw [show (10 : ℕ) = 2 * 5 from rfl, h2n, hp5]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Polynomial.add_comp,
      Polynomial.pow_comp, Polynomial.X_comp]
    ring
  have hx5_fac : (Polynomial.X ^ 5 + 1 : ℚ[X]) =
      (Polynomial.X + 1) * Polynomial.cyclotomic 10 ℚ := by
    rw [hphi10]
    ring
  have hirr10 : Irreducible (Polynomial.cyclotomic 10 ℚ) :=
    (theorem_15_3 (m := 10) (by omega)).1
  have hsplits_x5_iff : ∀ (M : Type u) [Field M] [Algebra ℚ M],
      GarlingSplitsOver ℚ M (Polynomial.X ^ 5 + 1) ↔
      GarlingSplitsOver ℚ M (Polynomial.cyclotomic 10 ℚ) := by
    intro M _ _
    rw [garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits, hx5_fac, Polynomial.map_mul]
    have hlin : ((Polynomial.X + 1 : ℚ[X]).map (algebraMap ℚ M)).Splits := by
      simpa using Polynomial.Splits.X_add_C (1 : M)
    have hlin_ne0 : ((Polynomial.X + 1 : ℚ[X]).map (algebraMap ℚ M)) ≠ 0 := by
      simpa using Polynomial.X_add_C_ne_zero (1 : M)
    constructor
    · intro hmul
      have hne0 : ((Polynomial.X + 1 : ℚ[X]).map (algebraMap ℚ M) *
          (Polynomial.cyclotomic 10 ℚ).map (algebraMap ℚ M)) ≠ 0 :=
        mul_ne_zero hlin_ne0 (Polynomial.cyclotomic.monic 10 M |> fun hm => by
          rw [Polynomial.map_cyclotomic]; exact hm.ne_zero)
      exact hmul.of_dvd hne0 (dvd_mul_left _ _)
    · exact fun h10 => hlin.mul h10
  have hsf_x5_iff : ∀ {L : Type u} [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 5 + 1) ↔
      IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic 10 ℚ) := by
    intro L _ _
    unfold IsGarlingSplittingFieldExtension
    constructor
    · rintro ⟨hL, hmin⟩
      exact ⟨(hsplits_x5_iff L).mp hL, fun M hM hMs => hmin M hM ((hsplits_x5_iff M).mpr hMs)⟩
    · rintro ⟨hL, hmin⟩
      exact ⟨(hsplits_x5_iff L).mpr hL, fun M hM hMs => hmin M hM ((hsplits_x5_iff M).mp hMs)⟩
  have hcharQ10 : ¬ (ringChar ℚ ∣ 10) := by
    rw [ringChar.eq_zero]
    decide
  let u10_3 : GarlingUnitsZMod 10 := ZMod.unitOfCoprime 3 (by decide)
  have hcard_u10 : Fintype.card (GarlingUnitsZMod 10) = 4 := by
    rw [ZMod.card_units_eq_totient]
    decide
  have hord_u10_3 : orderOf u10_3 = 4 := by
    have h4 : u10_3 ^ 4 = 1 := by decide
    have h2 : u10_3 ^ 2 ≠ 1 := by decide
    have hdvd : orderOf u10_3 ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hle : orderOf u10_3 ≤ 4 := Nat.le_of_dvd (by omega) hdvd
    have hpos : 0 < orderOf u10_3 := isOfFinOrder_of_finite u10_3 |>.orderOf_pos
    by_contra hne4
    interval_cases orderOf u10_3
    · have h1 : u10_3 = 1 := by simpa using pow_orderOf_eq_one u10_3
      exact h2 (by rw [h1, one_pow])
    · exact h2 (pow_orderOf_eq_one u10_3)
    · norm_num at hdvd
  let iso_u10_z4 : GarlingUnitsZMod 10 ≃* Multiplicative (ZMod 4) :=
    cyclicMulEquivOfOrderOf hcard_u10 hord_u10_3
  refine ⟨⟨hphi8, hirr8, ?_⟩, ⟨hx5_fac, hphi10, hirr10, hsf_x5_iff, ?_⟩⟩
  · intro L _ _ hsf8
    have hsf_cyc8 : IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic 8 ℚ) :=
      hphi8 ▸ hsf8
    obtain ⟨_, _, hirr_iff, _, _⟩ := theorem_15_4 hcharQ8 hsf_cyc8
    obtain ⟨eG8⟩ := hirr_iff.mp (hphi8 ▸ hirr8)
    have hcardG : Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1)) = 4 := by
      calc Nat.card (L ≃ₐ[ℚ] L) = Nat.card (GarlingUnitsZMod 8) := Nat.card_congr eG8.toEquiv
        _ = Fintype.card (GarlingUnitsZMod 8) := Nat.card_eq_fintype_card
        _ = 4 := hcard_u8
    have hnot_cycG : ¬ IsCyclic (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1)) := by
      intro hc
      exact ZMod.not_isCyclic_units_eight (isCyclic_of_surjective eG8 eG8.surjective)
    exact ⟨hcardG, hnot_cycG, ⟨eG8⟩, ⟨eG8.trans iso_u8_v4⟩,
      ⟨(eG8.trans iso_u8_v4).trans iso_vier_v4.symm⟩⟩
  · intro L _ _ hsf5
    have hsf_cyc10 : IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic 10 ℚ) :=
      hsf_x5_iff.mp hsf5
    obtain ⟨_, _, hirr_iff, _, _⟩ := theorem_15_4 hcharQ10 hsf_cyc10
    obtain ⟨eG10⟩ := hirr_iff.mp hirr10
    let eZ4 := eG10.trans iso_u10_z4
    have hcardG : Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1)) = 4 := by
      calc Nat.card (L ≃ₐ[ℚ] L) = Nat.card (GarlingUnitsZMod 10) := Nat.card_congr eG10.toEquiv
        _ = Fintype.card (GarlingUnitsZMod 10) := Nat.card_eq_fintype_card
        _ = 4 := hcard_u10
    have hcyc_u10 : IsCyclic (GarlingUnitsZMod 10) := by
      rw [isCyclic_iff_exists_orderOf_eq_natCard]
      refine ⟨u10_3, ?_⟩
      rw [hord_u10_3, Nat.card_eq_fintype_card, hcard_u10]
    have hcycG : IsCyclic (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 5 + 1)) :=
      isCyclic_of_surjective eG10.symm eG10.symm.surjective
    exact ⟨hcardG, hcycG, ⟨eG10⟩, ⟨eZ4⟩⟩

/-- **Exercise 15.6** (`QUEUE.md` fidelity hold — open-ended *"When is…?"* characterization prompts;
§15.3, printed p. 122 / PDF p. 130; OCR warning: `garling1986_pages.txt` l. 4557 drops the overbar
on `p̄`):
*"Suppose that `p` is a prime which does not divide `m`, and let `ε` be a primitive `m`th root of
unity over `ℤ_p`. Show that `[ℤ_p(ε) : ℤ_p] = k`, where `k` is the order of `p̄` in the
multiplicative group `U_m` of units in `ℤ_m`. Show that `Φ_m` is irreducible over `ℤ_p` if and only
if `U_m` is a cyclic group generated by `p̄`. When is `Φ_4` irreducible over `ℤ_p`? When is `Φ_8`
irreducible over `ℤ_p`?"*

Proves all four parts across arbitrary primes `p` (with `Φ_4` and `Φ_8` proved across **all** primes
`p`, including `p = 2`):
1. `[ℤ_p(ε) : ℤ_p] = orderOf p̄` (both `Module.finrank` and `extDegree`);
2. `Irreducible (Φ_m over ℤ_p) ↔ Subgroup.zpowers p̄ = ⊤ ↔ IsCyclic U_m ∧ Subgroup.zpowers p̄ = ⊤`;
3. `Irreducible (Φ_4 over ℤ_p) ↔ p % 4 = 3`;
4. `¬ Irreducible (Φ_8 over ℤ_p)` for every prime `p`. -/
theorem exercise_15_6 :
    (∀ {p m : ℕ} (hp : Nat.Prime p) (hpm : ¬ p ∣ m),
      haveI : Fact p.Prime := ⟨hp⟩
      let pbar : GarlingUnitsZMod m := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpm)
      let k : ℕ := orderOf pbar
      (∀ {L : Type u} [Field L] [Algebra (ZMod p) L] {ε : L},
        IsGarlingPrimitiveRoot m ε →
        Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = k ∧
        extDegree (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = (k : ℕ)) ∧
      (Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔ Subgroup.zpowers pbar = ⊤) ∧
      (Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔
        IsCyclic (GarlingUnitsZMod m) ∧ Subgroup.zpowers pbar = ⊤)) ∧
    (∀ {p : ℕ} (hp : Nat.Prime p),
      haveI : Fact p.Prime := ⟨hp⟩
      Irreducible (Polynomial.cyclotomic 4 (ZMod p)) ↔ p % 4 = 3) ∧
    (∀ {p : ℕ} (hp : Nat.Prime p),
      haveI : Fact p.Prime := ⟨hp⟩
      ¬ Irreducible (Polynomial.cyclotomic 8 (ZMod p))) := by
  have hpart12 : ∀ {p m : ℕ} (hp : Nat.Prime p) (hpm : ¬ p ∣ m),
      haveI : Fact p.Prime := ⟨hp⟩
      let pbar : GarlingUnitsZMod m := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpm)
      let k : ℕ := orderOf pbar
      (∀ {L : Type u} [Field L] [Algebra (ZMod p) L] {ε : L},
        IsGarlingPrimitiveRoot m ε →
        Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = k ∧
        extDegree (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = (k : ℕ)) ∧
      (Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔ Subgroup.zpowers pbar = ⊤) ∧
      (Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔
        IsCyclic (GarlingUnitsZMod m) ∧ Subgroup.zpowers pbar = ⊤) := by
    intro p m hp hpm
    have _ : Fact p.Prime := ⟨hp⟩
    have hm_pos : 1 ≤ m := by
      by_contra h0
      have hz : m = 0 := by omega
      exact hpm (hz ▸ dvd_zero p)
    have _ : NeZero m := ⟨by omega⟩
    have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    let pbar : GarlingUnitsZMod m := ZMod.unitOfCoprime p hcop
    let k : ℕ := orderOf pbar
    have hunit_eq : ZMod.unitOfCoprime (p ^ 1) (hcop.pow_left 1) = pbar := by
      ext
      simp [pbar]
    have hcard_zp : Fintype.card (ZMod p) = p ^ 1 := by simp [ZMod.card]
    have hdeg_part : ∀ {L : Type u} [Field L] [Algebra (ZMod p) L] {ε : L},
        IsGarlingPrimitiveRoot m ε →
        Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = k ∧
        extDegree (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = (k : ℕ) := by
      intro L _ _ ε hε
      have hprim : IsPrimitiveRoot ε m :=
        (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
      have hm_zp_ne0 : (m : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff m p).not.mpr hpm
      have hm_L_ne0 : (m : L) ≠ 0 := fun h0 =>
        hm_zp_ne0 ((algebraMap (ZMod p) L).injective (by rw [map_natCast, h0, map_zero]))
      have _ : NeZero (m : L) := ⟨hm_L_ne0⟩
      have hroot_cyc : Polynomial.aeval ε (Polynomial.cyclotomic m (ZMod p)) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
          ← Polynomial.IsRoot.def]
        exact hprim.isRoot_cyclotomic (by omega)
      have hint : IsIntegral (ZMod p) ε :=
        ⟨Polynomial.cyclotomic m (ZMod p), Polynomial.cyclotomic.monic m (ZMod p), hroot_cyc⟩
      have hdvd : minpoly (ZMod p) ε ∣ Polynomial.cyclotomic m (ZMod p) :=
        minpoly.dvd (ZMod p) ε hroot_cyc
      have hdeg_min : (minpoly (ZMod p) ε).natDegree = k := by
        have h := Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible hcard_zp hcop hdvd
          (minpoly.irreducible hint)
        rwa [hunit_eq] at h
      have hfinrank :
          Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = k := by
        rw [IntermediateField.adjoin.finrank hint, hdeg_min]
      have hext :
          extDegree (ZMod p) (IntermediateField.adjoin (ZMod p) ({ε} : Set L)) = (k : ℕ) := by
        rw [extDegree_eq_finrank, hfinrank]
      exact ⟨hfinrank, hext⟩
    have hirr_iff_zpow :
        Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔ Subgroup.zpowers pbar = ⊤ := by
      constructor
      · intro hirr
        let L := (Polynomial.X ^ m - 1 : (ZMod p)[X]).SplittingField
        have hchar_zp : ¬ (ringChar (ZMod p) ∣ m) := by
          rw [ZMod.ringChar_zmod_n p]
          exact hpm
        have hsf : IsGarlingSplittingFieldExtension (ZMod p) L (Polynomial.X ^ m - 1) :=
          (isGarlingSplittingFieldExtension_iff (ZMod p) L _).mpr inferInstance
        obtain ⟨ε, hε⟩ := exists_isGarlingPrimitiveRoot_of_splittingField hchar_zp hsf
        have hprim : IsPrimitiveRoot ε m :=
          (isGarlingPrimitiveRoot_iff_isPrimitiveRoot hm_pos ε).mp hε
        have hroot_cyc : Polynomial.aeval ε (Polynomial.cyclotomic m (ZMod p)) = 0 := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
            ← Polynomial.IsRoot.def]
          exact hprim.isRoot_cyclotomic (by omega)
        have hmin_eq : minpoly (ZMod p) ε = Polynomial.cyclotomic m (ZMod p) :=
          (minpoly.eq_of_irreducible_of_monic hirr hroot_cyc
            (Polynomial.cyclotomic.monic m (ZMod p))).symm
        have hint : IsIntegral (ZMod p) ε :=
          ⟨Polynomial.cyclotomic m (ZMod p), Polynomial.cyclotomic.monic m (ZMod p), hroot_cyc⟩
        have hk_eq : k = Nat.totient m := by
          have h := Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible hcard_zp hcop
            (dvd_refl _) hirr
          rw [hunit_eq, Polynomial.natDegree_cyclotomic] at h
          exact h.symm
        have hcard_zpow : Nat.card (Subgroup.zpowers pbar) = Nat.card (GarlingUnitsZMod m) := by
          rw [Nat.card_zpowers, show orderOf pbar = k from rfl, hk_eq, Nat.card_eq_fintype_card,
            ZMod.card_units_eq_totient]
        exact Subgroup.eq_top_of_card_eq _ hcard_zpow
      · intro htop
        have hk_eq : orderOf pbar = (Polynomial.cyclotomic m (ZMod p)).natDegree := by
          rw [← Nat.card_zpowers pbar, htop, Subgroup.card_top, Nat.card_eq_fintype_card,
            ZMod.card_units_eq_totient, Polynomial.natDegree_cyclotomic]
        exact ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hpm dvd_rfl hk_eq.symm
    have hirr_iff_cyc :
        Irreducible (Polynomial.cyclotomic m (ZMod p)) ↔
          IsCyclic (GarlingUnitsZMod m) ∧ Subgroup.zpowers pbar = ⊤ := by
      rw [hirr_iff_zpow]
      exact ⟨fun htop => ⟨⟨⟨pbar, fun u => Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top u)⟩⟩,
        htop⟩, fun ⟨_, htop⟩ => htop⟩
    exact ⟨hdeg_part, hirr_iff_zpow, hirr_iff_cyc⟩
  refine ⟨hpart12, ?_, ?_⟩
  · -- When is `Φ_4` irreducible over `ℤ_p`? Iff `p % 4 = 3`:
    intro p hp
    have _ : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst hp2
      have hmod : ¬ (2 % 4 = 3) := by decide
      refine iff_of_false ?_ hmod
      have hphi4_2 : Polynomial.cyclotomic 4 (ZMod 2) = (Polynomial.X + 1) ^ 2 := by
        have h := exercise_15_3_cyclotomic (ZMod 2) Nat.prime_two (n := 2) (by omega)
        have hchar2 : (Polynomial.X + 1 : (ZMod 2)[X]) ^ 2 = Polynomial.X ^ 2 + 1 := by
          rw [add_pow_char, one_pow]
        rw [hchar2]
        simpa [Finset.sum_range_succ, add_comm] using h
      rw [hphi4_2, sq]
      intro hirr
      have hnu : ¬ IsUnit (Polynomial.X + 1 : (ZMod 2)[X]) :=
        Polynomial.not_isUnit_of_natDegree_pos _ (by simp)
      exact (hirr.isUnit_or_isUnit rfl).elim hnu hnu
    · have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
      have hp_not_dvd4 : ¬ p ∣ 4 := by
        intro hdvd
        have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd)
        have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hp_dvd2
        have hp_ge2 : 2 ≤ p := hp.two_le
        omega
      obtain ⟨_, hirr_iff, _⟩ := hpart12 (m := 4) hp hp_not_dvd4
      rw [hirr_iff]
      let pbar4 : GarlingUnitsZMod 4 := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hp_not_dvd4)
      have hmod_cases : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hmod_cases with hm1 | hm3
      · refine iff_of_false ?_ (by omega)
        have hp1 : pbar4 = 1 := by
          apply Units.ext
          change (p : ZMod 4) = 1
          rw [← ZMod.natCast_mod p 4, hm1, Nat.cast_one]
        rw [hp1, Subgroup.zpowers_one_eq_bot]
        intro hbot_top
        have hcard1 : Nat.card (⊥ : Subgroup (GarlingUnitsZMod 4)) = 1 := by simp
        have hcard2 : Nat.card (⊤ : Subgroup (GarlingUnitsZMod 4)) = 2 := by
          rw [Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
          decide
        rw [hbot_top] at hcard1
        omega
      · refine iff_of_true ?_ hm3
        have hp_ne1 : pbar4 ≠ 1 := by
          intro h1
          have hval : (p : ZMod 4) = 1 := congrArg Units.val h1
          rw [← ZMod.natCast_mod p 4, hm3] at hval
          revert hval
          decide
        have hp_sq : pbar4 ^ 2 = 1 := by
          revert pbar4
          decide
        have hord2 : orderOf pbar4 = 2 := orderOf_eq_prime hp_sq hp_ne1
        have hcard_eq : Nat.card (Subgroup.zpowers pbar4) = Nat.card (GarlingUnitsZMod 4) := by
          rw [Nat.card_zpowers, hord2, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
          decide
        exact Subgroup.eq_top_of_card_eq _ hcard_eq
  · -- When is `Φ_8` irreducible over `ℤ_p`? Never (`¬ Irreducible` for every prime `p`):
    intro p hp
    have _ : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst hp2
      have hphi8_2 : Polynomial.cyclotomic 8 (ZMod 2) =
          (Polynomial.X ^ 2 + 1) * (Polynomial.X ^ 2 + 1) := by
        have h := exercise_15_3_cyclotomic (ZMod 2) Nat.prime_two (n := 3) (by omega)
        have hsq : (Polynomial.X ^ 2 + 1 : (ZMod 2)[X]) ^ 2 = Polynomial.X ^ 4 + 1 := by
          rw [add_pow_char, ← pow_mul, one_pow]
        rw [← sq, hsq]
        simpa [Finset.sum_range_succ, add_comm] using h
      rw [hphi8_2]
      intro hirr
      have hdeg2 : (Polynomial.X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
      have hnu : ¬ IsUnit (Polynomial.X ^ 2 + 1 : (ZMod 2)[X]) :=
        Polynomial.not_isUnit_of_natDegree_pos _ (by omega)
      exact (hirr.isUnit_or_isUnit rfl).elim hnu hnu
    · have hp_not_dvd8 : ¬ p ∣ 8 := by
        intro hdvd
        have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using hdvd)
        have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hp_dvd2
        have hp_ge2 : 2 ≤ p := hp.two_le
        omega
      obtain ⟨_, _, hirr_iff_cyc⟩ := hpart12 (m := 8) hp hp_not_dvd8
      intro hirr
      exact ZMod.not_isCyclic_units_eight (hirr_iff_cyc.mp hirr).1

/-- Counterexamples to the omitted `1 ≤ t` setup hypothesis and omitted `1 ≤ u` hypothesis in part
`(iii)` of **Exercise 15.7** (`QUEUE.md` fidelity hold; §15.3, printed p. 122 / PDF p. 130):
1. At `t = 0` (`m = q^0 = 1`), `|U_1| = 1 ≠ (q - 1) q^{0 - 1}` and `U_1` contains no element of
   order `q - 1 ≥ 2`;
2. At `u = 0` in `(iii)`, for **every** prime `q` and **every** integer `a` with `q ∤ a`, there
   exists **no** integer `b` such that `(1 + a q^0)^q = 1 + b q^{0 + 1}` (in particular at
   `q = 3, u = 0, a = 2`, `(1 + 2 · 3^0)^3 = 27 ≠ 1 + 3 b` for all `b : ℤ`). -/
theorem exercise_15_7_counterexamples :
    (∀ {q : ℕ}, Nat.Prime q → Odd q →
      Nat.card (GarlingUnitsZMod (q ^ 0)) = 1 ∧
      Nat.card (GarlingUnitsZMod (q ^ 0)) ≠ (q - 1) * q ^ (0 - 1) ∧
      ¬ ∃ x : GarlingUnitsZMod (q ^ 0), orderOf x = q - 1) ∧
    (∀ {q : ℕ}, Nat.Prime q → ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
      ¬ ∃ b : ℤ, (1 + a * (q : ℤ) ^ 0) ^ q = 1 + b * (q : ℤ) ^ (0 + 1)) ∧
    ((1 + (2 : ℤ) * (3 : ℤ) ^ 0) ^ 3 = 27 ∧
      ∀ b : ℤ, (1 + (2 : ℤ) * (3 : ℤ) ^ 0) ^ 3 ≠ 1 + b * (3 : ℤ) ^ (0 + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hodd
    have hq3 : 3 ≤ q := by
      have hp2 := hq.two_le
      rcases hodd with ⟨k, rfl⟩
      omega
    have hcard1 : Nat.card (GarlingUnitsZMod (q ^ 0)) = 1 := by
      rw [pow_zero, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      rfl
    have hneq : (1 : ℕ) ≠ (q - 1) * q ^ (0 - 1) := by
      simp only [Nat.sub_zero, pow_zero, mul_one]
      omega
    have hno_ord : ¬ ∃ x : GarlingUnitsZMod (q ^ 0), orderOf x = q - 1 := by
      rintro ⟨x, hx⟩
      rw [pow_zero] at x
      have hx1 : x = 1 := Subsingleton.elim x 1
      rw [hx1, orderOf_one] at hx
      omega
    exact ⟨hcard1, hcard1 ▸ hneq, hno_ord⟩
  · intro q hq a hqa ⟨b, hb⟩
    have _ : Fact q.Prime := ⟨hq⟩
    simp only [pow_zero, mul_one, zero_add, pow_one] at hb
    -- Map `(1 + a)^q = 1 + b * q` to `ZMod q` and apply Fermat's Little Theorem `x^q = x`:
    have hmod : ((1 + a : ℤ) : ZMod q) ^ q = ((1 + b * (q : ℤ) : ℤ) : ZMod q) := by
      rw [← Int.cast_pow, hb]
    rw [ZMod.pow_card] at hmod
    simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, add_zero] at hmod
    have ha0 : (a : ZMod q) = 0 := add_left_cancel (hmod.trans (add_zero 1).symm)
    exact hqa ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp ha0)
  · refine ⟨by norm_num, fun b hb => ?_⟩
    omega

/-- **Exercise 15.7** (`QUEUE.md` fidelity hold — repaired `1 ≤ t`, `1 ≤ u` theorem; §15.3, printed
p. 122 / PDF p. 130):
*"Suppose that `m = q^t`, where `q` is an odd prime.*
*(i) Show that `|U_m| = (q - 1) q^{t - 1}`.*
*(ii) Use the fact that `U_q` is cyclic of order `q - 1` to show that there is an element of order
`q - 1` in `U_m`.*
*(iii) Show that if `q` does not divide `a` then `(1 + a q^u)^q = 1 + b q^{u + 1}`, where `q` does
not divide `b`.*
*(iv) Show that `1 + q` has order `q^{t - 1}` in `U_m`.*
*(v) Combine (ii) and (iv) to show that `U_m` is cyclic."* -/
theorem exercise_15_7 {q t m : ℕ} (hq : Nat.Prime q) (hq_odd : Odd q) (ht : 1 ≤ t)
    (hm : m = q ^ t) :
    let _ : NeZero m := ⟨by rw [hm]; exact pow_ne_zero t hq.ne_zero⟩
    let u1q : GarlingUnitsZMod m :=
      ZMod.unitOfCoprime (1 + q) (by
        rw [hm]
        exact (Nat.coprime_add_self_left.mpr Nat.coprime_one_left).pow_right t)
    -- (i) `|U_m| = (q - 1) q^{t - 1}`
    (Nat.card (GarlingUnitsZMod m) = (q - 1) * q ^ (t - 1) ∧
      setOrder (GarlingUnitsZMod m) = ((q - 1) * q ^ (t - 1) : ℕ)) ∧
    -- (ii) `∃ g ∈ U_m` of order `q - 1` lifted from `U_q`
    (IsCyclic (GarlingUnitsZMod q) ∧
      Nat.card (GarlingUnitsZMod q) = q - 1 ∧
      ∃ g : GarlingUnitsZMod m, orderOf g = q - 1) ∧
    -- (iii) `(1 + a q^u)^q = 1 + b q^{u + 1}` with `q ∤ b` for all `u ≥ 1` and `q ∤ a`
    (∀ {u : ℕ}, 1 ≤ u → ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
      ∃ b : ℤ, (1 + a * (q : ℤ) ^ u) ^ q = 1 + b * (q : ℤ) ^ (u + 1) ∧ ¬ ((q : ℤ) ∣ b)) ∧
    -- (iv) `1 + q` has order `q^{t - 1}` in `U_m`
    ((u1q : ZMod m) = 1 + (q : ZMod m) ∧ orderOf u1q = q ^ (t - 1)) ∧
    -- (v) Combining `(ii)` and `(iv)`, `U_m` is cyclic (generated by `g * (1 + q)`)
    (IsCyclic (GarlingUnitsZMod m) ∧
      ∃ g : GarlingUnitsZMod m,
        orderOf g = q - 1 ∧
        orderOf (g * u1q) = (q - 1) * q ^ (t - 1) ∧
        Subgroup.zpowers (g * u1q) = ⊤) := by
  subst hm
  have _ : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hq_odd with ⟨k, rfl⟩
    omega
  have hq_ne2 : q ≠ 2 := by omega
  have _ : NeZero (q ^ t) := ⟨pow_ne_zero t hq.ne_zero⟩
  let u1q : GarlingUnitsZMod (q ^ t) :=
    ZMod.unitOfCoprime (1 + q)
      ((Nat.coprime_add_self_left.mpr Nat.coprime_one_left).pow_right t)
  -- (i) Cardinality of `U_{q^t}`:
  have hcard : Nat.card (GarlingUnitsZMod (q ^ t)) = (q - 1) * q ^ (t - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hq (by omega : 0 < t), mul_comm]
  have hsetOrder : setOrder (GarlingUnitsZMod (q ^ t)) = ((q - 1) * q ^ (t - 1) : ℕ) := by
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  -- (ii) Lift generator of `U_q` to `U_{q^t}` and raise to power `orderOf b / (q - 1)`:
  obtain ⟨hcyc_Uq, hcard_Uq_raw, c, _, hc_ord_raw⟩ := corollary_1_to_theorem_12_3 (ZMod q)
  have hcard_Uq : Nat.card (GarlingUnitsZMod q) = q - 1 := by
    rw [hcard_Uq_raw, Nat.card_zmod]
  have hc_ord : orderOf c = q - 1 := by
    rw [hc_ord_raw, Nat.card_zmod]
  have hdvd_qt : q ∣ q ^ t := dvd_pow_self q (by omega : t ≠ 0)
  obtain ⟨b, hb_map⟩ := ZMod.unitsMap_surjective hdvd_qt c
  have hq1_dvd_ordb : q - 1 ∣ orderOf b := by
    rw [← hc_ord, ← hb_map]
    exact orderOf_map_dvd (ZMod.unitsMap hdvd_qt) b
  let g : GarlingUnitsZMod (q ^ t) := b ^ (orderOf b / (q - 1))
  have hg_ord : orderOf g = q - 1 :=
    orderOf_pow_orderOf_div (isOfFinOrder_of_finite b).orderOf_pos.ne' hq1_dvd_ordb
  -- (iii) Binomial expansion `(1 + a q^u)^q = 1 + b q^{u + 1}` with `q ∤ b` for `1 ≤ u`:
  have hpart_iii : ∀ {u : ℕ}, 1 ≤ u → ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
      ∃ b : ℤ, (1 + a * (q : ℤ) ^ u) ^ q = 1 + b * (q : ℤ) ^ (u + 1) ∧ ¬ ((q : ℤ) ∣ b) := by
    intro u hu a hqa
    have hvu : (q : ℤ) ∣ (q : ℤ) ^ u := dvd_pow_self (q : ℤ) (by omega)
    have hpuv : (q : ℤ) * (q : ℤ) ^ u * (q : ℤ) ∣ ((q : ℤ) ^ u) ^ q := by
      have hlhs : (q : ℤ) * (q : ℤ) ^ u * (q : ℤ) = (q : ℤ) ^ (u + 2) := by ring
      have hrhs : ((q : ℤ) ^ u) ^ q = (q : ℤ) ^ (u * q) := (pow_mul (q : ℤ) u q).symm
      rw [hlhs, hrhs]
      exact pow_dvd_pow (q : ℤ) (by nlinarith : u + 2 ≤ u * q)
    obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_eq hq hvu hpuv a
    refine ⟨a + (q : ℤ) * y, ?_, ?_⟩
    · calc (1 + a * (q : ℤ) ^ u) ^ q = (1 + (q : ℤ) ^ u * a) ^ q := by ring
        _ = 1 + (q : ℤ) * (q : ℤ) ^ u * (a + (q : ℤ) * y) := hy
        _ = 1 + (a + (q : ℤ) * y) * (q : ℤ) ^ (u + 1) := by ring
    · intro hqb
      exact hqa ((dvd_add_left (dvd_mul_right (q : ℤ) y)).mp hqb)
  -- (iv) Order of `1 + q` in `U_{q^t}` is `q^{t - 1}` (iterating `(iii)`):
  have hu1q_coe : (u1q : ZMod (q ^ t)) = 1 + (q : ZMod (q ^ t)) := by
    simp [u1q]
  have hu1q_ord : orderOf u1q = q ^ (t - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [add_comm 1 k, Nat.add_sub_cancel]
    have hord_val : orderOf (u1q : ZMod (q ^ (k + 1))) = orderOf u1q := orderOf_units
    rw [← hord_val, hu1q_coe]
    exact ZMod.orderOf_one_add_prime hq hq_ne2 k
  -- (v) Combine `(ii)` and `(iv)`:
  have hcop_orders : Nat.Coprime (orderOf g) (orderOf u1q) := by
    rw [hg_ord, hu1q_ord]
    refine Nat.Coprime.pow_right (t - 1) ?_
    rw [Nat.coprime_self_sub_left hq.pos]
    exact Nat.coprime_one_right q
  have hprod_ord : orderOf (g * u1q) = (q - 1) * q ^ (t - 1) := by
    rw [(Commute.all g u1q).orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders, hg_ord, hu1q_ord]
  have hcard_zpow :
      Nat.card (Subgroup.zpowers (g * u1q)) = Nat.card (GarlingUnitsZMod (q ^ t)) := by
    rw [Nat.card_zpowers, hprod_ord, hcard]
  have hzpow_top : Subgroup.zpowers (g * u1q) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hcard_zpow
  have hcyc_Uqt : IsCyclic (GarlingUnitsZMod (q ^ t)) :=
    ⟨⟨g * u1q, fun x => Subgroup.mem_zpowers_iff.mp (hzpow_top ▸ Subgroup.mem_top x)⟩⟩
  exact ⟨⟨hcard, hsetOrder⟩, ⟨hcyc_Uq, hcard_Uq, g, hg_ord⟩, hpart_iii,
    ⟨hu1q_coe, hu1q_ord⟩, ⟨hcyc_Uqt, g, hg_ord, hprod_ord, hzpow_top⟩⟩

/-- Counterexamples to the literal printed wording *"distinct prime powers"* in **Exercise 15.8**
(`QUEUE.md` fidelity hold; §15.3, printed p. 122 / PDF p. 130):
1. `m_1 = 2` and `m_2 = 4` are distinct prime powers (`IsPrimePow 2 ∧ IsPrimePow 4 ∧ 2 ≠ 4`) with
   product `m = 8`, yet `|U_8| = 4 ≠ 2 = |U_2 × U_4|`, so `U_8 ≇ U_2 × U_4`;
2. `m_1 = 3` and `m_2 = 9` are distinct prime powers (`IsPrimePow 3 ∧ IsPrimePow 9 ∧ 3 ≠ 9`) with
   product `m = 27`, yet `|U_{27}| = 18 ≠ 12 = |U_3 × U_9|`, so `U_{27} ≇ U_3 × U_9`. -/
theorem exercise_15_8_same_prime_counterexamples :
    (IsPrimePow (2 : ℕ) ∧ IsPrimePow (4 : ℕ) ∧ (2 : ℕ) ≠ 4 ∧
      Nat.card (GarlingUnitsZMod (2 * 4)) = 4 ∧
      Nat.card (GarlingUnitsZMod 2 × GarlingUnitsZMod 4) = 2 ∧
      IsEmpty (GarlingUnitsZMod (2 * 4) ≃* GarlingUnitsZMod 2 × GarlingUnitsZMod 4)) ∧
    (IsPrimePow (3 : ℕ) ∧ IsPrimePow (9 : ℕ) ∧ (3 : ℕ) ≠ 9 ∧
      Nat.card (GarlingUnitsZMod (3 * 9)) = 18 ∧
      Nat.card (GarlingUnitsZMod 3 × GarlingUnitsZMod 9) = 12 ∧
      IsEmpty (GarlingUnitsZMod (3 * 9) ≃* GarlingUnitsZMod 3 × GarlingUnitsZMod 9)) := by
  have hpp2 : IsPrimePow (2 : ℕ) := Nat.prime_two.isPrimePow
  have hpp4 : IsPrimePow (4 : ℕ) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]
    exact Nat.prime_two.isPrimePow.pow (by omega)
  have hpp3 : IsPrimePow (3 : ℕ) := Nat.prime_three.isPrimePow
  have hpp9 : IsPrimePow (9 : ℕ) := by
    rw [show (9 : ℕ) = 3 ^ 2 from rfl]
    exact Nat.prime_three.isPrimePow.pow (by omega)
  have hc8 : Nat.card (GarlingUnitsZMod (2 * 4)) = 4 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hc24 : Nat.card (GarlingUnitsZMod 2 × GarlingUnitsZMod 4) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card_units_eq_totient,
      ZMod.card_units_eq_totient]
    decide
  have hc27 : Nat.card (GarlingUnitsZMod (3 * 9)) = 18 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have hc39 : Nat.card (GarlingUnitsZMod 3 × GarlingUnitsZMod 9) = 12 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card_units_eq_totient,
      ZMod.card_units_eq_totient]
    decide
  refine ⟨⟨hpp2, hpp4, by omega, hc8, hc24, ⟨fun e => ?_⟩⟩,
    ⟨hpp3, hpp9, by omega, hc27, hc39, ⟨fun e => ?_⟩⟩⟩
  · have h := Nat.card_congr e.toEquiv
    omega
  · have h := Nat.card_congr e.toEquiv
    omega

/-- Explicit finite-product Chinese Remainder unit isomorphism
`U_{m_1 ⋯ m_r} ≃* U_{m_1} × ⋯ × U_{m_r}` for any pairwise relatively prime tuple `μ : Fin r → ℕ`
(**Exercise 15.8**, §15.3, printed p. 122 / PDF p. 130). -/
noncomputable def garlingUnitsZModProdEquiv :
    ∀ {r : ℕ} (μ : Fin r → ℕ),
      Pairwise (fun i j => Nat.Coprime (μ i) (μ j)) →
      GarlingUnitsZMod (∏ i : Fin r, μ i) ≃* (∀ i : Fin r, GarlingUnitsZMod (μ i))
  | 0, μ, _ =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => 1
      left_inv := fun u => Subsingleton.elim 1 u
      right_inv := fun f => funext fun i => Fin.elim0 i
      map_mul' := fun _ _ => funext fun i => Fin.elim0 i }
  | r + 1, μ, hcop =>
    let μ_tail : Fin r → ℕ := fun j => μ j.succ
    have hcop_tail : Pairwise (fun j₁ j₂ => Nat.Coprime (μ_tail j₁) (μ_tail j₂)) :=
      fun _ _ hne => hcop (Fin.succ_injective _ |>.ne hne)
    have hcop_head : Nat.Coprime (μ 0) (∏ j : Fin r, μ_tail j) :=
      Nat.coprime_prod_right_iff.mpr fun j _ => hcop (Fin.succ_ne_zero j).symm
    let e_split : GarlingUnitsZMod (∏ i : Fin (r + 1), μ i) ≃*
        GarlingUnitsZMod (μ 0) × GarlingUnitsZMod (∏ j : Fin r, μ_tail j) :=
      ({ toFun := fun u => Equiv.cast (congrArg GarlingUnitsZMod (Fin.prod_univ_succ μ)) u
         invFun := fun u => Equiv.cast (congrArg GarlingUnitsZMod (Fin.prod_univ_succ μ)).symm u
         left_inv := fun _ => by simp
         right_inv := fun _ => by simp
         map_mul' := fun a b => by
           cases Fin.prod_univ_succ μ
           rfl } : GarlingUnitsZMod (∏ i : Fin (r + 1), μ i) ≃*
             GarlingUnitsZMod (μ 0 * ∏ j : Fin r, μ_tail j)).trans
        ((Units.mapEquiv (ZMod.chineseRemainder hcop_head).toMulEquiv).trans MulEquiv.prodUnits)
    let e_ih := garlingUnitsZModProdEquiv μ_tail hcop_tail
    let e_cons : (GarlingUnitsZMod (μ 0) × ∀ j : Fin r, GarlingUnitsZMod (μ_tail j)) ≃*
        (∀ i : Fin (r + 1), GarlingUnitsZMod (μ i)) :=
      { toFun := fun p => Fin.cases p.1 p.2
        invFun := fun f => (f 0, fun j => f j.succ)
        left_inv := fun p => by
          ext
          · rfl
          · rfl
        right_inv := fun f => by
          ext i
          refine Fin.cases rfl (fun _ => rfl) i
        map_mul' := fun p q => by
          ext i
          refine Fin.cases rfl (fun _ => rfl) i }
    e_split.trans ((MulEquiv.prodCongr (MulEquiv.refl _) e_ih).trans e_cons)

/-- Helper: super-multiplicativity of `Nat.totient` over any finite product `∏ i ∈ s, f i`. -/
private theorem prod_totient_le_totient_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, Nat.totient (f i)) ≤ Nat.totient (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    exact le_trans (Nat.mul_le_mul_left _ ih) (Nat.totient_super_multiplicative _ _)

/-- **Exercise 15.8** (`QUEUE.md` fidelity hold — repaired powers-of-distinct-primes / pairwise
coprime theorem + exact `iff` for prime powers; §15.3, printed p. 122 / PDF p. 130; OCR warning:
`garling1986_pages.txt` ll. 4570–4572 corrupts `m = m_1 … m_r` and `U_m ≅ U_{m_1} × … × U_{m_r}`):
*"Suppose that `m = m_1 … m_r`, where `m_1, …, m_r` are [powers of distinct primes / pairwise
relatively prime]. Show that `U_m ≅ U_{m_1} × … × U_{m_r}`."* -/
theorem exercise_15_8 :
    (∀ {r : ℕ} (μ : Fin r → ℕ),
      Pairwise (fun i j => Nat.Coprime (μ i) (μ j)) →
      Nonempty (GarlingUnitsZMod (∏ i : Fin r, μ i) ≃*
        (∀ i : Fin r, GarlingUnitsZMod (μ i)))) ∧
    (∀ {r : ℕ} (p e : Fin r → ℕ),
      (∀ i, Nat.Prime (p i)) → Function.Injective p →
      Nonempty (GarlingUnitsZMod (∏ i : Fin r, p i ^ e i) ≃*
        (∀ i : Fin r, GarlingUnitsZMod (p i ^ e i)))) ∧
    (∀ {r : ℕ} (μ : Fin r → ℕ),
      (∀ i, IsPrimePow (μ i)) →
      (Nonempty (GarlingUnitsZMod (∏ i : Fin r, μ i) ≃*
        (∀ i : Fin r, GarlingUnitsZMod (μ i))) ↔
        Pairwise (fun i j => Nat.Coprime (μ i) (μ j)))) := by
  refine ⟨fun μ hcop => ⟨garlingUnitsZModProdEquiv μ hcop⟩, ?_, ?_⟩
  · intro r p e hp hinj
    refine ⟨garlingUnitsZModProdEquiv (fun i => p i ^ e i) ?_⟩
    intro i j hij
    have hp_ne : p i ≠ p j := hinj.ne hij
    have hcop_p : Nat.Coprime (p i) (p j) :=
      (Nat.coprime_primes (hp i) (hp j)).mpr hp_ne
    exact (hcop_p.pow_left (e i)).pow_right (e j)
  · intro r μ hpp
    constructor
    · rintro ⟨e⟩
      have hpos : ∀ i, 0 < μ i := fun i => (hpp i).pos
      have hprod_pos : 0 < ∏ i : Fin r, μ i :=
        Finset.prod_pos fun i _ => hpos i
      have _ : NeZero (∏ i : Fin r, μ i) := ⟨hprod_pos.ne'⟩
      have _ : ∀ i, NeZero (μ i) := fun i => ⟨(hpos i).ne'⟩
      have hcard_eq : Nat.totient (∏ i : Fin r, μ i) = ∏ i : Fin r, Nat.totient (μ i) := by
        have h := Nat.card_congr e.toEquiv
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.card_eq_fintype_card,
          Fintype.card_pi] at h
        simpa [ZMod.card_units_eq_totient] using h
      intro i j hij
      by_contra hnot_cop
      rcases (isPrimePow_nat_iff.mp (hpp i)) with ⟨pi, ai, hpi, hai, hμi⟩
      rcases (isPrimePow_nat_iff.mp (hpp j)) with ⟨pj, aj, hpj, haj, hμj⟩
      have hpeq : pi = pj := by
        by_contra hpne
        apply hnot_cop
        rw [← hμi, ← hμj]
        exact (((Nat.coprime_primes hpi hpj).mpr hpne).pow_left ai).pow_right aj
      subst hpeq
      -- Strict inequality `φ(pi^ai) * φ(pi^aj) < φ(pi^ai * pi^aj)`:
      have hstrict :
          Nat.totient (μ i) * Nat.totient (μ j) < Nat.totient (μ i * μ j) := by
        rw [← hμi, ← hμj, ← pow_add, Nat.totient_prime_pow hpi hai,
          Nat.totient_prime_pow hpi haj, Nat.totient_prime_pow hpi (by omega : 0 < ai + aj)]
        have hp2 : 2 ≤ pi := hpi.two_le
        have hexp : ai - 1 + (aj - 1) + 1 = ai + aj - 1 := by omega
        have hpow_split : pi ^ (ai + aj - 1) = pi ^ (ai - 1) * pi ^ (aj - 1) * pi := by
          rw [← pow_add, ← pow_succ, hexp]
        have hpos_pows : 0 < pi ^ (ai - 1) * pi ^ (aj - 1) :=
          Nat.mul_pos (pow_pos hpi.pos _) (pow_pos hpi.pos _)
        have hpos_sub : 0 < pi - 1 := by omega
        -- `(A * (pi - 1)) * (B * (pi - 1)) = A * B * (pi - 1) * (pi - 1) < A * B * pi * (pi - 1)`!
        calc (pi ^ (ai - 1) * (pi - 1)) * (pi ^ (aj - 1) * (pi - 1))
            = (pi ^ (ai - 1) * pi ^ (aj - 1)) * (pi - 1) * (pi - 1) := by ring
          _ < (pi ^ (ai - 1) * pi ^ (aj - 1)) * pi * (pi - 1) := by
              have hlt1 : (pi - 1) < pi := by omega
              have hlt2 : (pi ^ (ai - 1) * pi ^ (aj - 1)) * (pi - 1) <
                  (pi ^ (ai - 1) * pi ^ (aj - 1)) * pi :=
                Nat.mul_lt_mul_of_pos_left hlt1 hpos_pows
              exact Nat.mul_lt_mul_of_pos_right hlt2 hpos_sub
          _ = pi ^ (ai + aj - 1) * (pi - 1) := by rw [← hpow_split]
      -- Combine with `prod_totient_le_totient_prod` on the remaining indices `S = (univ.erase i).erase j`:
      let S : Finset (Fin r) := (Finset.univ.erase i).erase j
      have hj_mem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
      have hprod_split :
          (∏ k : Fin r, μ k) = (μ i * μ j) * ∏ k ∈ S, μ k := by
        rw [← Finset.mul_prod_erase Finset.univ μ (Finset.mem_univ i),
          ← Finset.mul_prod_erase (Finset.univ.erase i) μ hj_mem, mul_assoc]
      have htot_split :
          (∏ k : Fin r, Nat.totient (μ k)) =
            (Nat.totient (μ i) * Nat.totient (μ j)) * ∏ k ∈ S, Nat.totient (μ k) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun k => Nat.totient (μ k)) (Finset.mem_univ i),
          ← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => Nat.totient (μ k)) hj_mem,
          mul_assoc]
      have hS_tot_pos : 0 < ∏ k ∈ S, Nat.totient (μ k) :=
        Finset.prod_pos fun k _ => Nat.totient_pos.mpr (hpos k)
      have hle1 : ∏ k ∈ S, Nat.totient (μ k) ≤ Nat.totient (∏ k ∈ S, μ k) :=
        prod_totient_le_totient_prod S μ
      have hlt_chain :
          (∏ k : Fin r, Nat.totient (μ k)) < Nat.totient (∏ k : Fin r, μ k) := by
        rw [htot_split, hprod_split]
        calc (Nat.totient (μ i) * Nat.totient (μ j)) * ∏ k ∈ S, Nat.totient (μ k)
            < Nat.totient (μ i * μ j) * ∏ k ∈ S, Nat.totient (μ k) :=
              Nat.mul_lt_mul_of_pos_right hstrict hS_tot_pos
          _ ≤ Nat.totient (μ i * μ j) * Nat.totient (∏ k ∈ S, μ k) :=
              Nat.mul_le_mul_left _ hle1
          _ ≤ Nat.totient ((μ i * μ j) * ∏ k ∈ S, μ k) :=
              Nat.totient_super_multiplicative _ _
      omega
    · exact fun hcop => ⟨garlingUnitsZModProdEquiv μ hcop⟩

/-- Counterexamples to the boundary cases of **Exercise 15.9** (`QUEUE.md` fidelity hold; §15.3,
printed p. 122 / PDF p. 130):
1. Under the standard positive-exponent convention `1 ≤ t` (matching `15.7` and `15.8`), `m = 2`
   (where `ℤ_2` is a field with `1 ≠ 0` and `U_2 = {1̄}` is cyclic of order `1`) and `m = 1` both
   satisfy `IsCyclic (U_m)` while lying outside `{4} ∪ {q^t : 1 ≤ t} ∪ {2 q^t : 1 ≤ t}`;
2. At `m = 0` in Mathlib (`ZMod 0 = ℤ`), `(ZMod 0)ˣ = {1, -1}` is cyclic of order `2` while `0` lies
   outside `{4} ∪ {q^t : t ∈ ℕ} ∪ {2 q^t : t ∈ ℕ}` even when `t = 0` is permitted. -/
theorem exercise_15_9_counterexamples :
    (Nontrivial (ZMod 2) ∧
      IsCyclic (GarlingUnitsZMod 2) ∧
      ¬ ((2 : ℕ) = 4 ∨ ∃ q t : ℕ, q.Prime ∧ Odd q ∧ 1 ≤ t ∧
          (2 = q ^ t ∨ 2 = 2 * q ^ t))) ∧
    (IsCyclic (GarlingUnitsZMod 1) ∧
      ¬ ((1 : ℕ) = 4 ∨ ∃ q t : ℕ, q.Prime ∧ Odd q ∧ 1 ≤ t ∧
          (1 = q ^ t ∨ 1 = 2 * q ^ t))) ∧
    (IsCyclic (GarlingUnitsZMod 0) ∧
      ¬ ((0 : ℕ) = 4 ∨ ∃ q t : ℕ, q.Prime ∧ Odd q ∧
          (0 = q ^ t ∨ 0 = 2 * q ^ t))) := by
  refine ⟨⟨inferInstance, ZMod.isCyclic_units_two, ?_⟩,
    ⟨ZMod.isCyclic_units_one, ?_⟩,
    ⟨ZMod.isCyclic_units_zero, ?_⟩⟩
  · rintro (h4 | ⟨q, t, hqp, hqo, ht, h2 | h2⟩)
    · omega
    · have hq3 : 3 ≤ q := by rcases hqo with ⟨k, rfl⟩; have := hqp.two_le; omega
      have hge : 3 ≤ q ^ t := le_trans hq3 (Nat.le_self_pow (by omega) q)
      omega
    · have hq3 : 3 ≤ q := by rcases hqo with ⟨k, rfl⟩; have := hqp.two_le; omega
      have hge : 3 ≤ q ^ t := le_trans hq3 (Nat.le_self_pow (by omega) q)
      omega
  · rintro (h4 | ⟨q, t, hqp, hqo, ht, h1 | h1⟩)
    · omega
    · have hq3 : 3 ≤ q := by rcases hqo with ⟨k, rfl⟩; have := hqp.two_le; omega
      have hge : 3 ≤ q ^ t := le_trans hq3 (Nat.le_self_pow (by omega) q)
      omega
    · omega
  · rintro (h4 | ⟨q, t, hqp, _, h0 | h0⟩)
    · omega
    · exact pow_ne_zero t hqp.ne_zero h0.symm
    · exact mul_ne_zero two_ne_zero (pow_ne_zero t hqp.ne_zero) h0.symm

/-- **Exercise 15.9** (`QUEUE.md` fidelity hold — repaired `m ∈ {1, 2}` / `3 ≤ m` / `t ≥ 0`
characterizations; §15.3, printed p. 122 / PDF p. 130):
*"Show that `U_m` is cyclic if and only if `m = q^t` or `2 q^t` (where `q` is an odd prime) or `4`."*

Proves all three exact domain characterizations for `1 ≤ m`:
1. With `1 ≤ t` across all `1 ≤ m`: `IsCyclic U_m ↔ m ∈ {1, 2, 4} ∪ {q^t, 2 q^t : q odd prime, 1 ≤ t}`;
2. With `1 ≤ t` across `3 ≤ m`: the literal printed set `{4, q^t, 2 q^t}`;
3. Allowing `t : ℕ` (`t ≥ 0`) across all `1 ≤ m`: the literal printed formula `{4, q^t, 2 q^t}`
   (since `3^0 = 1` and `2 · 3^0 = 2`). -/
theorem exercise_15_9 :
    (∀ {m : ℕ}, 1 ≤ m →
      (IsCyclic (GarlingUnitsZMod m) ↔
        m = 1 ∨ m = 2 ∨ m = 4 ∨
          ∃ q t : ℕ, q.Prime ∧ Odd q ∧ 1 ≤ t ∧ (m = q ^ t ∨ m = 2 * q ^ t))) ∧
    (∀ {m : ℕ}, 3 ≤ m →
      (IsCyclic (GarlingUnitsZMod m) ↔
        m = 4 ∨ ∃ q t : ℕ, q.Prime ∧ Odd q ∧ 1 ≤ t ∧ (m = q ^ t ∨ m = 2 * q ^ t))) ∧
    (∀ {m : ℕ}, 1 ≤ m →
      (IsCyclic (GarlingUnitsZMod m) ↔
        m = 4 ∨ ∃ q t : ℕ, q.Prime ∧ Odd q ∧ (m = q ^ t ∨ m = 2 * q ^ t))) := by
  have h1 : ∀ {m : ℕ}, 1 ≤ m →
      (IsCyclic (GarlingUnitsZMod m) ↔
        m = 1 ∨ m = 2 ∨ m = 4 ∨
          ∃ q t : ℕ, q.Prime ∧ Odd q ∧ 1 ≤ t ∧ (m = q ^ t ∨ m = 2 * q ^ t)) := by
    intro m hm
    rw [ZMod.isCyclic_units_iff m]
    have hm0 : m ≠ 0 := by omega
    simp [hm0]
  refine ⟨h1, ?_, ?_⟩
  · intro m hm3
    rw [h1 (by omega : 1 ≤ m)]
    have hm1 : m ≠ 1 := by omega
    have hm2 : m ≠ 2 := by omega
    simp [hm1, hm2]
  · intro m hm1
    rw [h1 hm1]
    constructor
    · rintro (rfl | rfl | rfl | ⟨q, t, hqp, hqo, _, hqt⟩)
      · exact Or.inr ⟨3, 0, Nat.prime_three, by decide, Or.inl rfl⟩
      · exact Or.inr ⟨3, 0, Nat.prime_three, by decide, Or.inr rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨q, t, hqp, hqo, hqt⟩
    · rintro (rfl | ⟨q, t, hqp, hqo, hqt⟩)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases t with _ | t
        · rcases hqt with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨q, t + 1, hqp, hqo, by omega, hqt⟩))

/-- **Exercise 15.10** (§15.3, printed p. 122 / PDF p. 130):
*"Is `Φ_{18}` irreducible over (a) `ℤ_{23}`, (b) `ℤ_{43}`, (c) `ℤ_{73}`?"*

Proved directly via `Exercise 15.6` (`|U_{18}| = φ(18) = 6`, `Φ_{18}(x) = x^6 - x^3 + 1`):
- **(a) `ℤ_{23}` — YES:** `23̄ = 5̄ ∈ U_{18}` has order `6 = |U_{18}|` (`Subgroup.zpowers = ⊤`), so
  `Φ_{18}` **is irreducible** over `ℤ_{23}`;
- **(b) `ℤ_{43}` — NO:** `43̄ = 7̄ ∈ U_{18}` has order `3 ≠ 6`, so `Φ_{18}` **is not irreducible**
  over `ℤ_{43}` (every irreducible factor has degree `3`);
- **(c) `ℤ_{73}` — NO:** `73̄ = 1̄ ∈ U_{18}` has order `1 ≠ 6`, so `Φ_{18}` **splits into linear
  factors** and **is not irreducible** over `ℤ_{73}`. -/
theorem exercise_15_10 :
    (∀ R : Type u, ∀ [CommRing R],
      Polynomial.cyclotomic 18 R = Polynomial.X ^ 6 - Polynomial.X ^ 3 + 1) ∧
    -- (a) Over `ℤ_{23}`: irreducible (YES)
    (orderOf (ZMod.unitOfCoprime 23 (by decide) : GarlingUnitsZMod 18) = 6 ∧
      Irreducible (Polynomial.cyclotomic 18 (ZMod 23)) ∧
      IsGarlingIrreducible (Polynomial.cyclotomic 18 (ZMod 23))) ∧
    -- (b) Over `ℤ_{43}`: reducible into cubics (NO)
    (orderOf (ZMod.unitOfCoprime 43 (by decide) : GarlingUnitsZMod 18) = 3 ∧
      ¬ Irreducible (Polynomial.cyclotomic 18 (ZMod 43)) ∧
      ¬ IsGarlingIrreducible (Polynomial.cyclotomic 18 (ZMod 43))) ∧
    -- (c) Over `ℤ_{73}`: splits completely into linear factors, reducible (NO)
    (orderOf (ZMod.unitOfCoprime 73 (by decide) : GarlingUnitsZMod 18) = 1 ∧
      GarlingSplitsOver (ZMod 73) (ZMod 73) (Polynomial.cyclotomic 18 (ZMod 73)) ∧
      ¬ Irreducible (Polynomial.cyclotomic 18 (ZMod 73)) ∧
      ¬ IsGarlingIrreducible (Polynomial.cyclotomic 18 (ZMod 73))) := by
  have hphi18 : ∀ (R : Type u) [CommRing R],
      Polynomial.cyclotomic 18 R = Polynomial.X ^ 6 - Polynomial.X ^ 3 + 1 := by
    intro R _
    have h2n := exercise_15_2_cyclotomic R (n := 9) (by decide) (by omega)
    have h9 := exercise_15_3_cyclotomic R Nat.prime_three (n := 2) (by omega)
    rw [show (18 : ℕ) = 2 * 9 from rfl, h2n, show (9 : ℕ) = 3 ^ 2 from rfl, h9]
    simp only [Nat.add_sub_cancel, pow_one, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp]
    ring
  have hp23 : Nat.Prime 23 := by decide
  have hp43 : Nat.Prime 43 := by decide
  have hp73 : Nat.Prime 73 := by decide
  have _ : Fact (Nat.Prime 23) := ⟨hp23⟩
  have _ : Fact (Nat.Prime 43) := ⟨hp43⟩
  have _ : Fact (Nat.Prime 73) := ⟨hp73⟩
  let u23 : GarlingUnitsZMod 18 := ZMod.unitOfCoprime 23 (by decide)
  let u43 : GarlingUnitsZMod 18 := ZMod.unitOfCoprime 43 (by decide)
  let u73 : GarlingUnitsZMod 18 := ZMod.unitOfCoprime 73 (by decide)
  have hcard18 : Nat.card (GarlingUnitsZMod 18) = 6 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  -- Order of `u23` is `6`:
  have hord23 : orderOf u23 = 6 := by
    have h6 : u23 ^ 6 = 1 := by decide
    have h2 : u23 ^ 2 ≠ 1 := by decide
    have h3 : u23 ^ 3 ≠ 1 := by decide
    have hdvd : orderOf u23 ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    have hle : orderOf u23 ≤ 6 := Nat.le_of_dvd (by omega) hdvd
    have hpos : 0 < orderOf u23 := (isOfFinOrder_of_finite u23).orderOf_pos
    by_contra hne6
    interval_cases orderOf u23
    · have h1 : u23 = 1 := by simpa using pow_orderOf_eq_one u23
      exact h2 (by rw [h1, one_pow])
    · exact h2 (pow_orderOf_eq_one u23)
    · exact h3 (pow_orderOf_eq_one u23)
    · norm_num at hdvd
    · norm_num at hdvd
  -- Order of `u43` is `3`:
  have hord43 : orderOf u43 = 3 :=
    orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) (by decide) (by decide)
  -- Order of `u73` is `1`:
  have hord73 : orderOf u73 = 1 := by
    have hu73_1 : u73 = 1 := by decide
    rw [hu73_1, orderOf_one]
  -- (a) Irreducibility over `ℤ_{23}`:
  have hirr23 : Irreducible (Polynomial.cyclotomic 18 (ZMod 23)) := by
    obtain ⟨_, hirr_iff, _⟩ := exercise_15_6.1 hp23 (m := 18) (by decide)
    rw [hirr_iff]
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hord23, hcard18]
  -- (b) Reducibility over `ℤ_{43}`:
  have hnot_irr43 : ¬ Irreducible (Polynomial.cyclotomic 18 (ZMod 43)) := by
    obtain ⟨_, hirr_iff, _⟩ := exercise_15_6.1 hp43 (m := 18) (by decide)
    rw [hirr_iff]
    intro htop
    have hc : Nat.card (Subgroup.zpowers u43) = 6 := by
      rw [htop, Subgroup.card_top, hcard18]
    rw [Nat.card_zpowers, hord43] at hc
    omega
  -- (c) Splitting and reducibility over `ℤ_{73}`:
  have hnot_irr73 : ¬ Irreducible (Polynomial.cyclotomic 18 (ZMod 73)) := by
    obtain ⟨_, hirr_iff, _⟩ := exercise_15_6.1 hp73 (m := 18) (by decide)
    rw [hirr_iff]
    intro htop
    have hc : Nat.card (Subgroup.zpowers u73) = 6 := by
      rw [htop, Subgroup.card_top, hcard18]
    rw [Nat.card_zpowers, hord73] at hc
    omega
  have hprim73 : IsPrimitiveRoot (-2 : ZMod 73) 18 := by
    rw [← isGarlingPrimitiveRoot_iff_isPrimitiveRoot (by omega : 1 ≤ 18)]
    refine ⟨by omega, by decide, fun j hj1 hj18 => ?_⟩
    interval_cases j <;> decide
  have hsplits73 : GarlingSplitsOver (ZMod 73) (ZMod 73) (Polynomial.cyclotomic 18 (ZMod 73)) := by
    rw [garlingSplitsOver_iff_splits, Polynomial.map_id]
    have hs_x18 : (Polynomial.X ^ 18 - 1 : (ZMod 73)[X]).Splits := by
      simpa using Polynomial.X_pow_sub_one_splits hprim73
    have hne0 : (Polynomial.X ^ 18 - 1 : (ZMod 73)[X]) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < 18) (1 : ZMod 73)
    exact hs_x18.of_dvd hne0 (Polynomial.cyclotomic.dvd_X_pow_sub_one 18 (ZMod 73))
  exact ⟨hphi18,
    ⟨hord23, hirr23, (isGarlingIrreducible_iff _).mpr hirr23⟩,
    ⟨hord43, hnot_irr43, mt (isGarlingIrreducible_iff _).mp hnot_irr43⟩,
    ⟨hord73, hsplits73, hnot_irr73, mt (isGarlingIrreducible_iff _).mp hnot_irr73⟩⟩

end Garling.Chapter15
