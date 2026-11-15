import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04

/-!
# Chapter 5: Tests for irreducibility

Formalization of Chapter 5 ("Tests for irreducibility", printed pp. 49–53 / PDF pp. 57–61) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986):

- **§5.1 Introduction** (printed pp. 49–51, PDF pp. 57–59):
  cubic worked example `x^3 - 3x - 1`, Kronecker's factorization algorithm (`Theorem 5.1`),
  and `Exercises 5.1`–`5.5`.
- **§5.2 Eisenstein's criterion** (printed pp. 51–52, PDF pp. 59–60):
  `Theorem 5.2 (Eisenstein's criterion)` over arbitrary integral domains, quintic worked example
  `x^5 - 4x + 2`, and `Exercises 5.6`–`5.10`.
- **§5.3 Other methods for establishing irreducibility** (printed pp. 52–53, PDF pp. 60–61):
  shifted quartic worked example `x^4 + 4x^3 + 10x^2 + 12x + 7`, reduction modulo `p`,
  `Theorem 5.3 (Localization principle)`, localization worked example `x^n + px + p^2`,
  and `Exercises 5.11`–`5.12`.
-/

namespace Garling.Chapter05

open scoped Polynomial
open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03 Garling.Chapter04

/-! ## §5.1 Introduction (printed pp. 49–51, PDF pp. 57–59) -/

/-- Helper: any monic polynomial `f ∈ ℤ[X]` is primitive (`IsGarlingPrimitive` and `IsPrimitive`). -/
theorem isPrimitive_of_monic_int {f : ℤ[X]} (hf : f.Monic) :
    IsGarlingPrimitive f ∧ f.IsPrimitive := by
  have hp : f.IsPrimitive := hf.isPrimitive
  exact ⟨(isGarlingPrimitive_iff f).mpr hp, hp⟩

/-- Helper: if `f ∈ ℤ[X]` is monic of degree `3` and has no integer root `r ∈ ℤ`, then `f` is
irreducible in `ℤ[X]` and its image in `ℚ[X]` is irreducible in `ℚ[X]`. -/
theorem irreducible_int_and_rat_of_monic_deg_three {f : ℤ[X]}
    (hmonic : f.Monic) (hdeg : f.natDegree = 3) (hno_root : ∀ r : ℤ, f.eval r ≠ 0) :
    Irreducible f ∧ Irreducible (f.map (algebraMap ℤ ℚ)) := by
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hprim : IsGarlingPrimitive f := (isPrimitive_of_monic_int hmonic).1
  have hirr_Z : Irreducible f := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hg0 : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
      have hg_deg_pos : 0 < g.natDegree := by
        by_contra hle
        have hd0 : g.natDegree = 0 := by omega
        have hgC : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
        have hdvd : Polynomial.C (g.coeff 0) ∣ f := ⟨h, by rw [← hgC, hgh]⟩
        have hu0 : IsUnit (g.coeff 0) := ((isGarlingPrimitive_iff f).mp hprim) (g.coeff 0) hdvd
        exact hgu (hgC ▸ hu0.map Polynomial.C)
      have hh_deg_pos : 0 < h.natDegree := by
        by_contra hle
        have hd0 : h.natDegree = 0 := by omega
        have hhC : h = Polynomial.C (h.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
        have hdvd : Polynomial.C (h.coeff 0) ∣ f := ⟨g, by rw [← hhC, mul_comm, hgh]⟩
        have hu0 : IsUnit (h.coeff 0) := ((isGarlingPrimitive_iff f).mp hprim) (h.coeff 0) hdvd
        exact hhu (hhC ▸ hu0.map Polynomial.C)
      have hsum : g.natDegree + h.natDegree = 3 := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      have hlead : g.leadingCoeff * h.leadingCoeff = 1 := by
        rw [← Polynomial.leadingCoeff_mul, ← hgh]
        exact hmonic.leadingCoeff
      have hlin_root : ∀ p : ℤ[X], p.natDegree = 1 → IsUnit p.leadingCoeff →
          ∃ r : ℤ, p.eval r = 0 := by
        intro p hp1 hpu
        have hp_eq : p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X := by
          ext k
          rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X]
          rcases k with _ | _ | k
          · rw [Polynomial.coeff_C_zero]
            simp
          · rw [Polynomial.coeff_C_succ]
            simp
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < k + 2 by omega),
              Polynomial.coeff_C_succ]
            simp
        have hp1_lead : p.coeff 1 = p.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hp1]
        have hu_pm : p.coeff 1 = 1 ∨ p.coeff 1 = -1 := by
          rw [hp1_lead]
          exact Int.isUnit_iff.mp hpu
        rcases hu_pm with h1 | hm1
        · refine ⟨-p.coeff 0, ?_⟩
          rw [hp_eq, h1]
          simp
        · refine ⟨p.coeff 0, ?_⟩
          rw [hp_eq, hm1]
          simp
      by_cases hg1 : g.natDegree = 1
      · have hgu_lead : IsUnit g.leadingCoeff :=
          ⟨⟨g.leadingCoeff, h.leadingCoeff, hlead, mul_comm g.leadingCoeff h.leadingCoeff ▸ hlead⟩, rfl⟩
        obtain ⟨r, hr⟩ := hlin_root g hg1 hgu_lead
        apply hno_root r
        rw [hgh, Polynomial.eval_mul, hr, zero_mul]
      · have hh1 : h.natDegree = 1 := by omega
        have hhu_lead : IsUnit h.leadingCoeff :=
          ⟨⟨h.leadingCoeff, g.leadingCoeff, mul_comm g.leadingCoeff h.leadingCoeff ▸ hlead, hlead⟩, rfl⟩
        obtain ⟨r, hr⟩ := hlin_root h hh1 hhu_lead
        apply hno_root r
        rw [hgh, Polynomial.eval_mul, hr, mul_zero]
  have hirr_Q : Irreducible (f.map (algebraMap ℤ ℚ)) := by
    rcases (corollary_gauss_lemma ℚ f).mp hirr_Z with ⟨a, _, hfC⟩ | ⟨_, hQ⟩
    · have hd0 : f.natDegree = 0 := by rw [hfC, Polynomial.natDegree_C]
      omega
    · exact hQ
  exact ⟨hirr_Z, hirr_Q⟩

/-- **Prose worked example** (§5.1, printed p. 49 / PDF p. 57, needed in Chapter 6):
For `f = x^3 - 3x - 1 ∈ ℤ[x]`, `f(1) = -3` and `f(-1) = 1`, and `f` is irreducible both in `ℤ[x]`
and in `ℚ[x]`. -/
theorem example_5_1_cubic_irreducible :
    let f : ℤ[X] := Polynomial.X ^ 3 - 3 * Polynomial.X - 1
    f.eval 1 = -3 ∧ f.eval (-1) = 1 ∧
      Irreducible f ∧
      Irreducible (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : ℚ[X]) := by
  intro f
  have hf_deg : f.natDegree = 3 := by
    dsimp [f]
    compute_degree!
  have hf_monic : f.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf_deg]
    dsimp [f]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
  have hno_root : ∀ r : ℤ, f.eval r ≠ 0 := by
    intro r hr
    dsimp [f] at hr
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one] at hr
    have hdvd : r ∣ (1 : ℤ) := ⟨r ^ 2 - 3, by linear_combination -hr⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with rfl | rfl <;> omega
  obtain ⟨hirrZ, hirrQ⟩ := irreducible_int_and_rat_of_monic_deg_three hf_monic hf_deg hno_root
  have hmap : f.map (algebraMap ℤ ℚ) = (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : ℚ[X]) := by
    dsimp [f]
    simp
  refine ⟨?_, ?_, hirrZ, hmap ▸ hirrQ⟩
  · dsimp [f]; norm_num
  · dsimp [f]; norm_num

/-! ### Theorem 5.1 & Exercises 5.1–5.3: Kronecker's algorithm and finite-field factorization -/

/-- **Theorem 5.1 — Zero counterexample to literal `"any element"`** (§5.1, p. 49):
In any integral domain `R` (in particular `ℤ[X]` and `K[X]`), `0` cannot be expressed as a product
of irreducible elements, even up to a unit factor. -/
theorem zero_not_prod_irreducibles {R : Type*} [CommRing R] [IsDomain R] :
    (¬ ∃ L : List R, (∀ p ∈ L, Irreducible p) ∧ L.prod = 0) ∧
    (¬ ∃ (u : R) (L : List R), IsUnit u ∧ (∀ p ∈ L, Irreducible p) ∧ u * L.prod = 0) := by
  have hprod_ne_zero : ∀ L : List R, (∀ p ∈ L, Irreducible p) → L.prod ≠ 0 := by
    intro L hL
    induction L with
    | nil => simp
    | cons p ps ih =>
      rw [List.prod_cons]
      exact mul_ne_zero (hL p List.mem_cons_self).ne_zero
        (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)))
  refine ⟨?_, ?_⟩
  · rintro ⟨L, hL, h0⟩
    exact hprod_ne_zero L hL h0
  · rintro ⟨u, L, hu, hL, h0⟩
    exact mul_ne_zero hu.ne_zero (hprod_ne_zero L hL) h0

/-- **Theorem 5.1 — Zero counterexample in `ℤ[X]`** (§5.1, p. 49). -/
theorem theorem_5_1_zero_counterexample :
    (¬ ∃ L : List ℤ[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = 0) ∧
    (¬ ∃ (u : ℤ[X]) (L : List ℤ[X]), IsUnit u ∧ (∀ p ∈ L, Irreducible p) ∧ u * L.prod = 0) :=
  zero_not_prod_irreducibles

/-- **Theorem 5.1 — Unit counterexamples to literal `"any element"`** (§5.1, p. 49):
In `ℤ[X]`, the unit `-1` cannot be expressed as a (possibly empty) product of irreducible factors,
and `1` cannot be expressed as a non-empty product of irreducible factors. -/
theorem theorem_5_1_unit_counterexample :
    IsUnit (-1 : ℤ[X]) ∧
    (¬ ∃ L : List ℤ[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = -1) ∧
    (¬ ∃ L : List ℤ[X], L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = 1) := by
  refine ⟨isUnit_one.neg, ?_, ?_⟩
  · rintro ⟨L, hL, hprod⟩
    cases L with
    | nil =>
      simp only [List.prod_nil] at hprod
      have hc := congrArg (fun p : ℤ[X] => p.coeff 0) hprod
      simp at hc
    | cons p ps =>
      rw [List.prod_cons] at hprod
      have hdvd : p ∣ (-1 : ℤ[X]) := ⟨ps.prod, hprod.symm⟩
      exact (hL p List.mem_cons_self).not_isUnit (isUnit_of_dvd_unit hdvd isUnit_one.neg)
  · rintro ⟨L, hne, hL, hprod⟩
    cases L with
    | nil => exact hne rfl
    | cons p ps =>
      rw [List.prod_cons] at hprod
      have hdvd : p ∣ (1 : ℤ[X]) := ⟨ps.prod, hprod.symm⟩
      exact (hL p List.mem_cons_self).not_isUnit (isUnit_of_dvd_one hdvd)

/-- Exact characterization of which elements `f ∈ R` in a UFD (such as `ℤ[X]` or `K[X]`) are
products of irreducible factors (§5.1, pp. 49–50). -/
theorem exists_prod_irreducibles_iff {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (f : R) :
    ((∃ L : List R, (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ f = 1 ∨ (f ≠ 0 ∧ ¬ IsUnit f)) ∧
    ((∃ L : List R, L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ (f ≠ 0 ∧ ¬ IsUnit f)) := by
  have hnonempty :
      (∃ L : List R, L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ (f ≠ 0 ∧ ¬ IsUnit f) := by
    constructor
    · rintro ⟨L, hne, hL, rfl⟩
      cases L with
      | nil => exact absurd rfl hne
      | cons p ps =>
        have hne0 : (p :: ps).prod ≠ 0 := by
          intro hz
          exact zero_not_prod_irreducibles.1 ⟨p :: ps, hL, hz⟩
        refine ⟨hne0, fun hu => ?_⟩
        rw [List.prod_cons] at hu
        exact (hL p List.mem_cons_self).not_isUnit (isUnit_of_mul_isUnit_left hu)
    · rintro ⟨hf0, hfu⟩
      have hacc : SatisfiesACCPI R :=
        ufd_satisfiesACCPI ((isGarlingUFD_iff_uniqueFactorizationMonoid R).mpr inferInstance)
      obtain ⟨m, hm, p, hp, hprod⟩ := theorem_3_4 hacc hf0 hfu
      refine ⟨List.ofFn p, ?_, ?_, ?_⟩
      · intro hnil
        have hlen := congrArg List.length hnil
        simp at hlen
        omega
      · intro q hq
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
        exact hp i
      · simpa [List.prod_ofFn] using hprod
  refine ⟨?_, hnonempty⟩
  constructor
  · rintro ⟨L, hL, rfl⟩
    cases L with
    | nil => exact Or.inl rfl
    | cons p ps =>
      exact Or.inr (hnonempty.mp ⟨p :: ps, List.cons_ne_nil p ps, hL, rfl⟩)
  · rintro (rfl | hnu)
    · exact ⟨[], by simp, rfl⟩
    · obtain ⟨L, _, hL, hprod⟩ := hnonempty.mpr hnu
      exact ⟨L, hL, hprod⟩

/-- **Theorem 5.1 — Exact characterization in `ℤ[X]`** (§5.1, p. 49). -/
theorem theorem_5_1_iff (f : ℤ[X]) :
    ((∃ L : List ℤ[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ f = 1 ∨ (f ≠ 0 ∧ ¬ IsUnit f)) ∧
    ((∃ L : List ℤ[X], L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ (f ≠ 0 ∧ ¬ IsUnit f)) :=
  exists_prod_irreducibles_iff f

/-! #### Computable Kronecker programme on dense integer coefficient lists (`List ℤ`) -/

/-- Decoding a dense coefficient list `[a_0, a_1, ..., a_n]` into `ℤ[X]` via Horner form. -/
noncomputable def coeffsToPoly : List ℤ → ℤ[X]
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * coeffsToPoly as

/-- Encoding a polynomial `f ∈ ℤ[X]` as its canonical trimmed coefficient list. -/
noncomputable def polyToCoeffs (f : ℤ[X]) : List ℤ :=
  if f = 0 then [] else (List.range (f.natDegree + 1)).map f.coeff

/-- Computable polynomial addition on `List ℤ`. -/
def coeffsAdd : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: coeffsAdd as bs

/-- Computable scalar multiplication on `List ℤ`. -/
def coeffsScale (c : ℤ) (as : List ℤ) : List ℤ :=
  as.map (c * ·)

/-- Computable polynomial multiplication on `List ℤ`. -/
def coeffsMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, bs => coeffsAdd (coeffsScale a bs) (0 :: coeffsMul as bs)

/-- Computable polynomial evaluation on `List ℤ`. -/
def coeffsEval : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: as, x => a + x * coeffsEval as x

/-- Computable removal of trailing zeros on `List ℤ`. -/
def coeffsTrim : List ℤ → List ℤ
  | [] => []
  | a :: as =>
    match coeffsTrim as with
    | [] => if a = 0 then [] else [a]
    | bs => a :: bs

theorem coeffsToPoly_add (as bs : List ℤ) :
    coeffsToPoly (coeffsAdd as bs) = coeffsToPoly as + coeffsToPoly bs := by
  induction as generalizing bs with
  | nil => simp [coeffsAdd, coeffsToPoly]
  | cons a as ih =>
    cases bs with
    | nil => simp [coeffsAdd, coeffsToPoly]
    | cons b bs =>
      simp only [coeffsAdd, coeffsToPoly, ih, map_add]
      ring

theorem coeffsToPoly_scale (c : ℤ) (as : List ℤ) :
    coeffsToPoly (coeffsScale c as) = Polynomial.C c * coeffsToPoly as := by
  induction as with
  | nil => simp [coeffsScale, coeffsToPoly]
  | cons a as ih =>
    rw [coeffsScale, List.map_cons, ← coeffsScale, coeffsToPoly, ih, coeffsToPoly]
    simp only [map_mul]
    ring

theorem coeffsToPoly_mul (as bs : List ℤ) :
    coeffsToPoly (coeffsMul as bs) = coeffsToPoly as * coeffsToPoly bs := by
  induction as with
  | nil => simp [coeffsMul, coeffsToPoly]
  | cons a as ih =>
    simp only [coeffsMul, coeffsToPoly_add, coeffsToPoly_scale, coeffsToPoly, map_zero, zero_add, ih]
    ring

theorem coeffsEval_eq (as : List ℤ) (x : ℤ) :
    coeffsEval as x = (coeffsToPoly as).eval x := by
  induction as with
  | nil => simp [coeffsEval, coeffsToPoly]
  | cons a as ih =>
    simp [coeffsEval, coeffsToPoly, ih]

theorem coeffsToPoly_trim (as : List ℤ) :
    coeffsToPoly (coeffsTrim as) = coeffsToPoly as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have hdef : coeffsTrim (a :: as) =
        match coeffsTrim as with
        | [] => if a = 0 then [] else [a]
        | bs => a :: bs := rfl
    rw [hdef]
    cases h : coeffsTrim as with
    | nil =>
      rw [h] at ih
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte]
        simp [coeffsToPoly, ← ih]
      · simp only [ha, ↓reduceIte]
        rw [coeffsToPoly, ih]
        rfl
    | cons b bs =>
      rw [h] at ih
      rw [coeffsToPoly, ih]
      rfl

theorem coeffsTrim_idem (as : List ℤ) :
    coeffsTrim (coeffsTrim as) = coeffsTrim as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have hdef : coeffsTrim (a :: as) =
        match coeffsTrim as with
        | [] => if a = 0 then [] else [a]
        | bs => a :: bs := rfl
    rw [hdef]
    cases h : coeffsTrim as with
    | nil =>
      by_cases ha : a = 0 <;> simp [ha, coeffsTrim]
    | cons b bs =>
      have ih' : coeffsTrim (b :: bs) = b :: bs := by rw [← h, ih]
      simp only []
      rw [coeffsTrim, ih']

private theorem C_add_X_mul_eq_zero_iff {R : Type*} [Semiring R] (a : R) (p : R[X]) :
    Polynomial.C a + Polynomial.X * p = 0 ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun q : R[X] => q.coeff 0) h
    simp at h0
    refine ⟨h0, ?_⟩
    ext k
    have hk := congrArg (fun q : R[X] => q.coeff (k + 1)) h
    simpa using hk
  · rintro ⟨rfl, rfl⟩
    simp

theorem coeffsTrim_eq_nil_iff (as : List ℤ) :
    coeffsTrim as = [] ↔ coeffsToPoly as = 0 := by
  induction as with
  | nil => simp [coeffsTrim, coeffsToPoly]
  | cons a as ih =>
    rw [coeffsToPoly, C_add_X_mul_eq_zero_iff, ← ih]
    simp only [coeffsTrim]
    cases h : coeffsTrim as with
    | nil =>
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs =>
      simp

theorem coeffsTrim_getLast_ne_zero {as : List ℤ} (hne : coeffsTrim as ≠ []) :
    (coeffsTrim as).getLast hne ≠ 0 := by
  induction as with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    revert hne
    change ∀ (hne : (match coeffsTrim as with
        | [] => if a = 0 then [] else [a]
        | bs => a :: bs) ≠ []),
      (match coeffsTrim as with
        | [] => if a = 0 then [] else [a]
        | bs => a :: bs).getLast hne ≠ 0
    cases h : coeffsTrim as with
    | nil =>
      by_cases ha : a = 0
      · simp [ha]
      · intro _
        simp [ha]
    | cons b bs =>
      intro _
      have hne_as : coeffsTrim as ≠ [] := by rw [h]; exact List.cons_ne_nil b bs
      have hlast := ih hne_as
      simpa [h] using hlast

theorem coeffsToPoly_coeff : ∀ (as : List ℤ) (k : ℕ),
    (coeffsToPoly as).coeff k = as.getD k 0
  | [], k => by simp [coeffsToPoly]
  | a :: as, 0 => by simp [coeffsToPoly]
  | a :: as, k + 1 => by
    rw [coeffsToPoly, Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add,
      Polynomial.coeff_X_mul, coeffsToPoly_coeff as k]
    rfl

theorem coeffsToPoly_natDegree_le (as : List ℤ) :
    (coeffsToPoly as).natDegree ≤ as.length - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeffsToPoly_coeff]
  cases as with
  | nil => simp
  | cons a as =>
    simp only [List.length_cons, Nat.add_sub_cancel] at hN
    exact List.getD_eq_default (a :: as) 0 (by simp; omega)

theorem coeffsTrim_length_eq_natDegree_succ {as : List ℤ} (hne : coeffsTrim as ≠ []) :
    (coeffsTrim as).length = (coeffsToPoly as).natDegree + 1 := by
  rw [← coeffsToPoly_trim as]
  have hlast : (coeffsTrim as).getLast hne ≠ 0 := coeffsTrim_getLast_ne_zero hne
  have hlen_pos : 0 < (coeffsTrim as).length := List.length_pos_of_ne_nil hne
  have hcoeff_top : (coeffsToPoly (coeffsTrim as)).coeff ((coeffsTrim as).length - 1) ≠ 0 := by
    rw [coeffsToPoly_coeff]
    have hget : (coeffsTrim as).getD ((coeffsTrim as).length - 1) 0 =
        (coeffsTrim as).getLast hne := by
      rw [List.getLast_eq_getElem hne, List.getD_eq_getElem _ _ (by omega)]
    rwa [hget]
  have hge : (coeffsTrim as).length - 1 ≤ (coeffsToPoly (coeffsTrim as)).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_top
  have hle : (coeffsToPoly (coeffsTrim as)).natDegree ≤ (coeffsTrim as).length - 1 :=
    coeffsToPoly_natDegree_le (coeffsTrim as)
  omega

theorem coeffsToPoly_polyToCoeffs (f : ℤ[X]) :
    coeffsToPoly (polyToCoeffs f) = f ∧ coeffsTrim (polyToCoeffs f) = polyToCoeffs f := by
  by_cases hf : f = 0
  · subst hf
    simp [polyToCoeffs, coeffsToPoly, coeffsTrim]
  · have hpoly : coeffsToPoly ((List.range (f.natDegree + 1)).map f.coeff) = f := by
      ext k
      rw [coeffsToPoly_coeff]
      by_cases hk : k < f.natDegree + 1
      · rw [List.getD_eq_getElem _ _ (by simp [hk])]
        simp
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
    have htrim_len : ∀ n : ℕ, ∀ g : ℤ[X], g.coeff n ≠ 0 →
        coeffsTrim ((List.range (n + 1)).map g.coeff) = (List.range (n + 1)).map g.coeff := by
      intro n g hgn
      have hne_nil : coeffsTrim ((List.range (n + 1)).map g.coeff) ≠ [] := by
        intro hnil
        have hz : coeffsToPoly ((List.range (n + 1)).map g.coeff) = 0 :=
          (coeffsTrim_eq_nil_iff _).mp hnil
        have hcn := congrArg (fun q : ℤ[X] => q.coeff n) hz
        rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ (by simp)] at hcn
        simp [hgn] at hcn
      have hdeg_eq : (coeffsToPoly ((List.range (n + 1)).map g.coeff)).natDegree = n := by
        apply le_antisymm
        · simpa using coeffsToPoly_natDegree_le ((List.range (n + 1)).map g.coeff)
        · apply Polynomial.le_natDegree_of_ne_zero
          rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ (by simp)]
          simpa using hgn
      have hlen_trim : (coeffsTrim ((List.range (n + 1)).map g.coeff)).length = n + 1 := by
        rw [coeffsTrim_length_eq_natDegree_succ hne_nil, hdeg_eq]
      apply List.ext_getElem
      · simp [hlen_trim]
      · intro i hi1 hi2
        have hc := congrArg (fun q : ℤ[X] => q.coeff i)
          (coeffsToPoly_trim ((List.range (n + 1)).map g.coeff))
        rw [coeffsToPoly_coeff, coeffsToPoly_coeff,
          List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hc
        exact hc
    refine ⟨by simpa [polyToCoeffs, hf] using hpoly, ?_⟩
    simpa [polyToCoeffs, hf] using htrim_len f.natDegree f (Polynomial.leadingCoeff_ne_zero.mpr hf)

theorem coeffsTrim_eq_polyToCoeffs (as : List ℤ) :
    coeffsTrim as = polyToCoeffs (coeffsToPoly as) := by
  by_cases hz : coeffsToPoly as = 0
  · rw [hz, (coeffsTrim_eq_nil_iff as).mpr hz]
    simp [polyToCoeffs]
  · have hne : coeffsTrim as ≠ [] := fun h => hz ((coeffsTrim_eq_nil_iff as).mp h)
    have hlen : (coeffsTrim as).length = (coeffsToPoly as).natDegree + 1 :=
      coeffsTrim_length_eq_natDegree_succ hne
    simp only [polyToCoeffs, hz, ↓reduceIte]
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi1 hi2
      have hc := congrArg (fun q : ℤ[X] => q.coeff i) (coeffsToPoly_trim as)
      rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi1] at hc
      simpa using hc

/-- Computable Horner bottom-up exact division helper on `List ℤ`. -/
def coeffsDivExactAux : ℕ → List ℤ → List ℤ → Option (List ℤ)
  | 0, _, _ => none
  | fuel + 1, a, b =>
    let a' := coeffsTrim a
    if a' = [] then some []
    else
      match b with
      | [] => none
      | b0 :: bs =>
        if b0 = 0 then
          match a' with
          | [] => some []
          | a0 :: as => if a0 = 0 then coeffsDivExactAux fuel as bs else none
        else
          match a' with
          | [] => some []
          | a0 :: _ =>
            if a0 % b0 = 0 then
              let q0 := a0 / b0
              let rem := (coeffsAdd a' (coeffsScale (-q0) b)).tail
              match coeffsDivExactAux fuel rem b with
              | some qs => some (q0 :: qs)
              | none => none
            else none

/-- Computable exact division in `ℤ[x]` represented by `List ℤ`: returns `some q` (trimmed) iff
`b ≠ 0` and `b * q = a` in `ℤ[X]`. -/
def coeffsDivExact? (a b : List ℤ) : Option (List ℤ) :=
  let a' := coeffsTrim a
  let b' := coeffsTrim b
  if b' = [] then none
  else
    match coeffsDivExactAux (a'.length + b'.length + 1) a' b' with
    | some q =>
      let q' := coeffsTrim q
      if coeffsTrim (coeffsMul b' q') == a' then some q' else none
    | none => none

theorem coeffsDivExact?_sound {a b q : List ℤ} (h : coeffsDivExact? a b = some q) :
    coeffsToPoly b ≠ 0 ∧ q = coeffsTrim q ∧
      coeffsToPoly a = coeffsToPoly b * coeffsToPoly q := by
  unfold coeffsDivExact? at h
  by_cases hb : coeffsTrim b = []
  · simp [hb] at h
  · simp only [hb, ↓reduceIte] at h
    cases haux : coeffsDivExactAux ((coeffsTrim a).length + (coeffsTrim b).length + 1)
        (coeffsTrim a) (coeffsTrim b) with
    | none => simp [haux] at h
    | some q0 =>
      simp only [haux] at h
      by_cases hmul : coeffsTrim (coeffsMul (coeffsTrim b) (coeffsTrim q0)) == coeffsTrim a
      · simp only [hmul, ↓reduceIte, Option.some.injEq] at h
        have hmul_eq : coeffsTrim (coeffsMul (coeffsTrim b) (coeffsTrim q0)) = coeffsTrim a :=
          beq_iff_eq.mp hmul
        refine ⟨fun hbz => hb ((coeffsTrim_eq_nil_iff b).mpr hbz), ?_, ?_⟩
        · rw [← h, coeffsTrim_idem]
        · have hp := congrArg coeffsToPoly hmul_eq
          simp only [coeffsToPoly_trim, coeffsToPoly_mul] at hp
          rw [← h, coeffsToPoly_trim, ← hp]
      · simp [hmul] at h

private theorem coeffsDivExactAux_complete_b0 {b0 : ℤ} (hb0 : b0 ≠ 0) (bs : List ℤ) :
    ∀ (q : List ℤ) (fuel : ℕ) (a : List ℤ),
      q = coeffsTrim q →
      q.length < fuel →
      coeffsToPoly a = coeffsToPoly (b0 :: bs) * coeffsToPoly q →
      coeffsDivExactAux fuel a (b0 :: bs) = some q := by
  intro q
  induction q with
  | nil =>
    intro fuel a _ hfuel ha
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [coeffsToPoly, mul_zero] at ha
      have htrim : coeffsTrim a = [] := (coeffsTrim_eq_nil_iff a).mpr ha
      simp [coeffsDivExactAux, htrim]
  | cons q0 qs ih =>
    intro fuel a hq_trim hfuel ha
    cases fuel with
    | zero => omega
    | succ f =>
      have hq_ne : coeffsToPoly (q0 :: qs) ≠ 0 := by
        intro hz
        have hnil := (coeffsTrim_eq_nil_iff (q0 :: qs)).mpr hz
        rw [← hq_trim] at hnil
        exact List.cons_ne_nil q0 qs hnil
      have hb_ne : coeffsToPoly (b0 :: bs) ≠ 0 := by
        intro hz
        have hc0 := congrArg (fun p : ℤ[X] => p.coeff 0) hz
        simp [coeffsToPoly, hb0] at hc0
      have ha_ne : coeffsToPoly a ≠ 0 := by
        rw [ha]
        exact mul_ne_zero hb_ne hq_ne
      have hatrim_ne : coeffsTrim a ≠ [] :=
        fun hnil => ha_ne ((coeffsTrim_eq_nil_iff a).mp hnil)
      cases hatrim : coeffsTrim a with
      | nil => exact absurd hatrim hatrim_ne
      | cons a0 as =>
        have ha_poly : coeffsToPoly (a0 :: as) = coeffsToPoly (b0 :: bs) * coeffsToPoly (q0 :: qs) := by
          rw [← hatrim, coeffsToPoly_trim, ha]
        have hc0 := congrArg (Polynomial.eval 0) ha_poly
        have ha0_eq : a0 = b0 * q0 := by simpa [coeffsToPoly] using hc0
        have hmod : a0 % b0 = 0 := by rw [ha0_eq, Int.mul_emod_right]
        have hdiv : a0 / b0 = q0 := by rw [ha0_eq, Int.mul_ediv_cancel_left q0 hb0]
        let rem := (coeffsAdd (a0 :: as) (coeffsScale (-q0) (b0 :: bs))).tail
        have hrem_poly : coeffsToPoly rem = coeffsToPoly (b0 :: bs) * coeffsToPoly qs := by
          let d := coeffsAdd (a0 :: as) (coeffsScale (-q0) (b0 :: bs))
          have hrem_eq : rem = d.tail := rfl
          have hd_poly : coeffsToPoly d =
              Polynomial.X * (coeffsToPoly (b0 :: bs) * coeffsToPoly qs) := by
            dsimp [d]
            rw [coeffsToPoly_add, coeffsToPoly_scale, ha_poly]
            simp only [coeffsToPoly, map_neg]
            ring
          cases hd : d with
          | nil =>
            rw [hd, coeffsToPoly] at hd_poly
            have hX_ne : (Polynomial.X : ℤ[X]) ≠ 0 := Polynomial.X_ne_zero
            have hrhs : coeffsToPoly (b0 :: bs) * coeffsToPoly qs = 0 :=
              (mul_eq_zero.mp hd_poly.symm).resolve_left hX_ne
            rw [hrem_eq, hd, List.tail_nil, coeffsToPoly, hrhs]
          | cons d0 ds =>
            rw [hd] at hd_poly
            have hd0_zero : d0 = 0 := by
              have h := congrArg (Polynomial.eval 0) hd_poly
              simpa [coeffsToPoly] using h
            have hX_eq : Polynomial.X * coeffsToPoly ds =
                Polynomial.X * (coeffsToPoly (b0 :: bs) * coeffsToPoly qs) := by
              simpa [coeffsToPoly, hd0_zero] using hd_poly
            have hds_eq : coeffsToPoly ds = coeffsToPoly (b0 :: bs) * coeffsToPoly qs :=
              mul_left_cancel₀ Polynomial.X_ne_zero hX_eq
            rw [hrem_eq, hd, List.tail_cons, hds_eq]
        have hqs_trim : qs = coeffsTrim qs := by
          simp only [coeffsTrim] at hq_trim
          cases h : coeffsTrim qs with
          | nil =>
            rw [h] at hq_trim
            by_cases hq0 : q0 = 0
            · simp [hq0] at hq_trim
            · simp [hq0] at hq_trim
              exact hq_trim
          | cons c cs =>
            rw [h] at hq_trim
            injection hq_trim
        have hqs_len : qs.length < f := by
          simp only [List.length_cons] at hfuel
          omega
        have hrec := ih f rem hqs_trim hqs_len hrem_poly
        simp [coeffsDivExactAux, hatrim, hb0, hmod, hdiv, rem, hrec]

theorem coeffsDivExact?_complete {a b : List ℤ} {q : ℤ[X]}
    (hb : coeffsToPoly b ≠ 0) (hmul : coeffsToPoly a = coeffsToPoly b * q) :
    coeffsDivExact? a b = some (polyToCoeffs q) := by
  have hbtrim_ne : coeffsTrim b ≠ [] := fun hnil => hb ((coeffsTrim_eq_nil_iff b).mp hnil)
  have hq_trim : polyToCoeffs q = coeffsTrim (polyToCoeffs q) :=
    (coeffsToPoly_polyToCoeffs q).2.symm
  have hq_poly : coeffsToPoly (polyToCoeffs q) = q := (coeffsToPoly_polyToCoeffs q).1
  have haux_peel : ∀ (bs : List ℤ),
      bs ≠ [] → bs = coeffsTrim bs →
      ∀ (as : List ℤ) (fuel : ℕ),
        as = coeffsTrim as →
        (polyToCoeffs q).length + bs.length ≤ fuel →
        coeffsToPoly as = coeffsToPoly bs * q →
        coeffsDivExactAux fuel as bs = some (polyToCoeffs q) := by
    intro bs
    induction bs with
    | nil => intro hne; exact absurd rfl hne
    | cons b0 bs ih =>
      intro _ hbs_trim as fuel has_trim hfuel has_eq
      by_cases hb0 : b0 = 0
      · subst hb0
        have hbs_ne : bs ≠ [] := by
          intro hnil
          rw [hnil] at hbs_trim
          simp [coeffsTrim] at hbs_trim
        have hbs_trim' : bs = coeffsTrim bs := by
          simp only [coeffsTrim] at hbs_trim
          cases h : coeffsTrim bs with
          | nil => rw [h] at hbs_trim; simp at hbs_trim
          | cons c cs => rw [h] at hbs_trim; injection hbs_trim
        cases fuel with
        | zero => simp at hfuel
        | succ f =>
          by_cases has_nil : as = []
          · subst has_nil
            simp only [coeffsToPoly, zero_eq_mul] at has_eq
            have hbs_pne : coeffsToPoly (0 :: bs) ≠ 0 := by
              intro hz
              exact List.cons_ne_nil 0 bs (hbs_trim.trans ((coeffsTrim_eq_nil_iff _).mpr hz))
            have hq0 : q = 0 := has_eq.resolve_left hbs_pne
            subst hq0
            simp [coeffsDivExactAux, coeffsTrim, polyToCoeffs]
          · cases as with
            | nil => exact absurd rfl has_nil
            | cons a0 as' =>
              have hc0 := congrArg (Polynomial.eval 0) has_eq
              have ha0 : a0 = 0 := by simpa [coeffsToPoly] using hc0
              subst ha0
              have has'_trim : as' = coeffsTrim as' := by
                simp only [coeffsTrim] at has_trim
                cases h : coeffsTrim as' with
                | nil => rw [h] at has_trim; simp at has_trim
                | cons c cs => rw [h] at has_trim; injection has_trim
              have has'_eq : coeffsToPoly as' = coeffsToPoly bs * q := by
                apply mul_left_cancel₀ Polynomial.X_ne_zero
                simpa [coeffsToPoly, mul_assoc] using has_eq
              have hrec := ih hbs_ne hbs_trim' as' f has'_trim (by simp at hfuel; omega) has'_eq
              have hatrim_self : coeffsTrim (0 :: as') = 0 :: as' := has_trim.symm
              simp [coeffsDivExactAux, hatrim_self, hrec]
      · apply coeffsDivExactAux_complete_b0 hb0 bs (polyToCoeffs q) fuel as hq_trim
        · simp at hfuel; omega
        · rwa [hq_poly]
  unfold coeffsDivExact?
  simp only [hbtrim_ne, ↓reduceIte]
  have hlen_le : (polyToCoeffs q).length ≤ (coeffsTrim a).length := by
    by_cases hq0 : q = 0
    · subst hq0; simp [polyToCoeffs]
    · have ha_ne : coeffsToPoly a ≠ 0 := by rw [hmul]; exact mul_ne_zero hb hq0
      have hatrim_ne : coeffsTrim a ≠ [] := fun hnil => ha_ne ((coeffsTrim_eq_nil_iff a).mp hnil)
      rw [coeffsTrim_length_eq_natDegree_succ hatrim_ne, hmul, Polynomial.natDegree_mul hb hq0]
      simp [polyToCoeffs, hq0]
  have haux := haux_peel (coeffsTrim b) hbtrim_ne (coeffsTrim_idem b).symm
    (coeffsTrim a) ((coeffsTrim a).length + (coeffsTrim b).length + 1)
    (coeffsTrim_idem a).symm (by omega)
    (by rw [coeffsToPoly_trim, coeffsToPoly_trim, hmul])
  rw [haux]
  simp only [← hq_trim]
  have hcheck : coeffsTrim (coeffsMul (coeffsTrim b) (polyToCoeffs q)) = coeffsTrim a := by
    rw [coeffsTrim_eq_polyToCoeffs (coeffsMul _ _), coeffsToPoly_mul,
      coeffsToPoly_trim b, hq_poly, ← hmul, ← coeffsTrim_eq_polyToCoeffs a]
  simp [hcheck]

/-! #### Computable integer divisors and scaled Lagrange interpolation -/

/-- Computable list of all integer divisors of a non-zero integer `c` (empty if `c = 0`),
ordered as `[d, -d]` for positive divisors `d ∣ |c|`. -/
def intDivisorsList (c : ℤ) : List ℤ :=
  let m := c.natAbs
  if m = 0 then []
  else
    ((List.range m).map fun i : ℕ => i + 1).flatMap fun d : ℕ =>
      if (d : ℤ) ∣ c then [(d : ℤ), -(d : ℤ)] else []

theorem mem_intDivisorsList_iff {c d : ℤ} (hc : c ≠ 0) :
    d ∈ intDivisorsList c ↔ d ∣ c := by
  unfold intDivisorsList
  have hm : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  simp only [hm, ↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, ⟨i, _, rfl⟩, hd⟩
    by_cases hkd : ((i + 1 : ℕ) : ℤ) ∣ c
    · simp only [hkd, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact hkd
      · exact neg_dvd.mpr hkd
    · simp only [hkd, ↓reduceIte, List.not_mem_nil] at hd
  · intro hd
    have hd0 : d ≠ 0 := fun hz => hc (zero_dvd_iff.mp (hz ▸ hd))
    have hd_abs_pos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    have hd_abs_le : d.natAbs ≤ c.natAbs := Int.natAbs_le_of_dvd_ne_zero hd hc
    refine ⟨d.natAbs, ⟨d.natAbs - 1, by omega, by omega⟩, ?_⟩
    have hkd : ((d.natAbs : ℤ)) ∣ c := Int.natAbs_dvd.mpr hd
    simp only [hkd, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
    exact Int.natAbs_eq d

theorem intDivisorsList_length_le (c : ℤ) :
    (intDivisorsList c).length ≤ 2 * c.natAbs := by
  unfold intDivisorsList
  by_cases hm : c.natAbs = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    have hbound : ∀ L : List ℕ,
        (L.flatMap fun d : ℕ => if (d : ℤ) ∣ c then [(d : ℤ), -(d : ℤ)] else []).length ≤
          2 * L.length := by
      intro L
      induction L with
      | nil => simp
      | cons d ds ih =>
        simp only [List.flatMap_cons, List.length_append]
        by_cases h : (d : ℤ) ∣ c <;>
          simp only [h, ↓reduceIte, List.length_cons, List.length_nil] <;> omega
    simpa using hbound ((List.range c.natAbs).map fun i : ℕ => i + 1)

/-- Computable product `∏_{k ∈ ks} (x - k)` in `List ℤ`. -/
def linearFactorProd : List ℕ → List ℤ
  | [] => [1]
  | k :: ks => coeffsMul [-(k : ℤ), 1] (linearFactorProd ks)

/-- Computable integer product `∏_{k ∈ ks} (j - k)`. -/
def denomProd (j : ℕ) : List ℕ → ℤ
  | [] => 1
  | k :: ks => ((j : ℤ) - (k : ℤ)) * denomProd j ks

theorem coeffsToPoly_linearFactorProd (ks : List ℕ) :
    coeffsToPoly (linearFactorProd ks) =
      (ks.map fun k : ℕ => Polynomial.X - Polynomial.C (k : ℤ)).prod := by
  induction ks with
  | nil => simp [linearFactorProd, coeffsToPoly]
  | cons k ks ih =>
    rw [linearFactorProd, coeffsToPoly_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [coeffsToPoly]
    ring

theorem eval_linearFactorProd_self (j : ℕ) (ks : List ℕ) :
    (coeffsToPoly (linearFactorProd ks)).eval (j : ℤ) = denomProd j ks := by
  induction ks with
  | nil => simp [linearFactorProd, denomProd, coeffsToPoly]
  | cons k ks ih =>
    rw [linearFactorProd, coeffsToPoly_mul, Polynomial.eval_mul, ih, denomProd]
    congr 1
    simp [coeffsToPoly]
    ring

theorem eval_linearFactorProd_of_mem {j : ℕ} {ks : List ℕ} (hmem : j ∈ ks) :
    (coeffsToPoly (linearFactorProd ks)).eval (j : ℤ) = 0 := by
  induction ks with
  | nil => cases hmem
  | cons k ks ih =>
    rw [linearFactorProd, coeffsToPoly_mul, Polynomial.eval_mul]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp [coeffsToPoly]
    · rw [ih hmem', mul_zero]

theorem denomProd_ne_zero {j : ℕ} {ks : List ℕ} (hnotmem : j ∉ ks) :
    denomProd j ks ≠ 0 := by
  induction ks with
  | nil => simp [denomProd]
  | cons k ks ih =>
    rw [denomProd]
    exact mul_ne_zero (fun hz => hnotmem (by simp; omega))
      (ih (fun hm => hnotmem (List.mem_cons_of_mem k hm)))

theorem natDegree_linearFactorProd_le (ks : List ℕ) :
    (coeffsToPoly (linearFactorProd ks)).natDegree ≤ ks.length := by
  rw [coeffsToPoly_linearFactorProd]
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    calc ((Polynomial.X - Polynomial.C (k : ℤ)) * _).natDegree
      _ ≤ (Polynomial.X - Polynomial.C (k : ℤ)).natDegree +
          ((ks.map fun m : ℕ => Polynomial.X - Polynomial.C (m : ℤ)).prod).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + ks.length := by
        have hlin : (Polynomial.X - Polynomial.C (k : ℤ)).natDegree ≤ 1 := by compute_degree
        omega
      _ = ks.length + 1 := Nat.add_comm 1 ks.length

/-- Computable scaled Lagrange interpolation on `0, ..., r`: given values `d : List ℤ` of length
`r + 1`, returns `some g` (trimmed, degree `≤ r`) if the unique `ℚ[X]` interpolant lies in `ℤ[X]`,
or `none` otherwise. -/
def lagrangeInterpCoeffs? (r : ℕ) (vals : List ℤ) : Option (List ℤ) :=
  let pts := List.range (r + 1)
  let denoms := pts.map fun j => denomProd j (pts.erase j)
  let M : ℤ := denoms.prod
  if M = 0 then none
  else
    let num : List ℤ :=
      (pts.map fun j =>
        let Mj : ℤ := ((pts.erase j).map fun i => denomProd i (pts.erase i)).prod
        coeffsScale (vals.getD j 0 * Mj) (linearFactorProd (pts.erase j))).foldr coeffsAdd []
    let numTrim := coeffsTrim num
    if numTrim.all (fun c => decide (M ∣ c)) then
      some (coeffsTrim (numTrim.map (· / M)))
    else none

theorem lagrangeInterpCoeffs?_eq_some_trim {r : ℕ} {vals g0 : List ℤ}
    (h : lagrangeInterpCoeffs? r vals = some g0) :
    g0 = coeffsTrim g0 := by
  dsimp only [lagrangeInterpCoeffs?] at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  rw [← h, coeffsTrim_idem]

/-- Garling's explicit rational Lagrange basis polynomial `g_j ∈ ℚ[X]` (§5.1, printed p. 50 /
PDF p. 58): `g_j = ∏_{0 ≤ k ≤ r, k ≠ j} ((x - k) / (j - k))`. -/
noncomputable def kroneckerBasisPoly (r j : ℕ) : ℚ[X] :=
  ∏ k ∈ (Finset.range (r + 1)).erase j,
    (Polynomial.X - Polynomial.C (k : ℚ)) * Polynomial.C (((j : ℚ) - (k : ℚ))⁻¹)

/-- Garling's explicit rational Lagrange interpolant `g = ∑_{j=0}^r d_j g_j ∈ ℚ[X]`
(§5.1, printed p. 50 / PDF p. 58). -/
noncomputable def kroneckerInterpPoly (r : ℕ) (d : ℕ → ℤ) : ℚ[X] :=
  ∑ j ∈ Finset.range (r + 1), Polynomial.C (d j : ℚ) * kroneckerBasisPoly r j

/-- Uniqueness and evaluation specification of Garling's Lagrange interpolant `kroneckerInterpPoly`
in `ℚ[X]` (§5.1, p. 50). -/
theorem kroneckerInterpPoly_spec (r : ℕ) (d : ℕ → ℤ) :
    (kroneckerInterpPoly r d).natDegree ≤ r ∧
    (∀ j ≤ r, (kroneckerInterpPoly r d).eval (j : ℚ) = (d j : ℚ)) ∧
    (∀ g : ℚ[X], g.natDegree ≤ r → (∀ j ≤ r, g.eval (j : ℚ) = (d j : ℚ)) →
      g = kroneckerInterpPoly r d) := by
  have hbasis_deg : ∀ j ≤ r, (kroneckerBasisPoly r j).natDegree ≤ r := by
    intro j hj
    unfold kroneckerBasisPoly
    have hcard : ((Finset.range (r + 1)).erase j).card = r := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
      omega
    calc (∏ k ∈ (Finset.range (r + 1)).erase j,
          (Polynomial.X - Polynomial.C (k : ℚ)) * Polynomial.C (((j : ℚ) - (k : ℚ))⁻¹)).natDegree
      _ ≤ ∑ k ∈ (Finset.range (r + 1)).erase j,
          ((Polynomial.X - Polynomial.C (k : ℚ)) * Polynomial.C (((j : ℚ) - (k : ℚ))⁻¹)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _k ∈ (Finset.range (r + 1)).erase j, 1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ((Polynomial.X - Polynomial.C (k : ℚ)) * Polynomial.C (((j : ℚ) - (k : ℚ))⁻¹)).natDegree
          _ ≤ (Polynomial.X - Polynomial.C (k : ℚ)).natDegree +
              (Polynomial.C (((j : ℚ) - (k : ℚ))⁻¹)).natDegree := Polynomial.natDegree_mul_le
          _ ≤ 1 + 0 := by
            have h1 : (Polynomial.X - Polynomial.C (k : ℚ)).natDegree ≤ 1 := by compute_degree
            rw [Polynomial.natDegree_C]
            omega
          _ = 1 := rfl
      _ = r := by simp [hcard]
  have hbasis_eval : ∀ j ≤ r, ∀ m ≤ r,
      (kroneckerBasisPoly r j).eval (m : ℚ) = if m = j then 1 else 0 := by
    intro j hj m hm
    unfold kroneckerBasisPoly
    rw [Polynomial.eval_prod]
    by_cases hmj : m = j
    · subst hmj
      simp only [↓reduceIte]
      refine Finset.prod_eq_one fun k hk => ?_
      have hkj : k ≠ m := (Finset.mem_erase.mp hk).1
      have hsub : (m : ℚ) - (k : ℚ) ≠ 0 := by
        exact_mod_cast (show (m : ℤ) - (k : ℤ) ≠ 0 by omega)
      simp [mul_inv_cancel₀ hsub]
    · simp only [hmj, ↓reduceIte]
      have hm_mem : m ∈ (Finset.range (r + 1)).erase j :=
        Finset.mem_erase.mpr ⟨hmj, Finset.mem_range.mpr (by omega)⟩
      refine Finset.prod_eq_zero hm_mem ?_
      simp
  have hdeg : (kroneckerInterpPoly r d).natDegree ≤ r := by
    unfold kroneckerInterpPoly
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (Polynomial.C (d j : ℚ) * kroneckerBasisPoly r j).natDegree
      _ ≤ (Polynomial.C (d j : ℚ)).natDegree + (kroneckerBasisPoly r j).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ r := by rw [Polynomial.natDegree_C, zero_add]; exact hbasis_deg j hj_le
  have heval : ∀ j ≤ r, (kroneckerInterpPoly r d).eval (j : ℚ) = (d j : ℚ) := by
    intro j hj
    unfold kroneckerInterpPoly
    rw [Polynomial.eval_finsetSum]
    have hterm : ∀ i ∈ Finset.range (r + 1),
        (Polynomial.C (d i : ℚ) * kroneckerBasisPoly r i).eval (j : ℚ) =
          if i = j then (d j : ℚ) else 0 := by
      intro i hi
      have hi_le : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Polynomial.eval_mul, Polynomial.eval_C, hbasis_eval i hi_le j hj]
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji]
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.mem_range.mpr (show j < r + 1 by omega)]
  refine ⟨hdeg, heval, fun g hg_deg hg_eval => ?_⟩
  by_contra hne
  have hdiff_ne : g - kroneckerInterpPoly r d ≠ 0 := sub_ne_zero.mpr hne
  have hdiff_deg : (g - kroneckerInterpPoly r d).natDegree ≤ r :=
    le_trans (Polynomial.natDegree_sub_le g _) (max_le hg_deg hdeg)
  let S : Finset ℚ := (Finset.range (r + 1)).image (fun j : ℕ => (j : ℚ))
  have hS_card : S.card = r + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hS_roots : ∀ x ∈ S, x ∈ (g - kroneckerInterpPoly r d).roots := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Polynomial.mem_roots hdiff_ne, Polynomial.IsRoot, Polynomial.eval_sub,
      hg_eval j hj_le, heval j hj_le, sub_self]
  have hcard_le : S.card ≤ (g - kroneckerInterpPoly r d).roots.card := by
    calc S.card = S.val.card := rfl
      _ ≤ (g - kroneckerInterpPoly r d).roots.card :=
        Multiset.card_le_card (Multiset.le_iff_subset S.nodup |>.mpr fun x hx => hS_roots x hx)
  have hroots_le : (g - kroneckerInterpPoly r d).roots.card ≤ (g - kroneckerInterpPoly r d).natDegree :=
    Polynomial.card_roots' _
  omega

/-- Completeness of computable `lagrangeInterpCoeffs?`: if `g ∈ ℤ[X]` has `g.natDegree ≤ r` and
`vals` has length `r + 1` with `vals[j] = g.eval j` for `0 ≤ j ≤ r`, then
`lagrangeInterpCoeffs? r vals = some (polyToCoeffs g)`. -/
theorem lagrangeInterpCoeffs?_complete (r : ℕ) (g : ℤ[X]) (hg_deg : g.natDegree ≤ r)
    (vals : List ℤ) (hvals_len : vals.length = r + 1)
    (hvals : ∀ j ≤ r, vals.getD j 0 = g.eval (j : ℤ)) :
    lagrangeInterpCoeffs? r vals = some (polyToCoeffs g) := by
  unfold lagrangeInterpCoeffs?
  let pts := List.range (r + 1)
  have hpts_nodup : pts.Nodup := List.nodup_range
  let den : ℕ → ℤ := fun j => denomProd j (pts.erase j)
  have hden_ne : ∀ j ∈ pts, den j ≠ 0 := by
    intro j _
    exact denomProd_ne_zero (hpts_nodup.not_mem_erase)
  let M : ℤ := (pts.map den).prod
  have hprod_ne0 : ∀ L : List ℤ, (∀ x ∈ L, x ≠ 0) → L.prod ≠ 0 := by
    intro L hL
    induction L with
    | nil => simp
    | cons x xs ih =>
      rw [List.prod_cons]
      exact mul_ne_zero (hL x List.mem_cons_self) (ih fun y hy => hL y (List.mem_cons_of_mem x hy))
  have hM_ne : M ≠ 0 := by
    apply hprod_ne0
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hden_ne j hj
  have hMj_mul : ∀ j ∈ pts,
      den j * ((pts.erase j).map den).prod = M := by
    intro j hj
    dsimp [M]
    have hperm : (j :: pts.erase j).Perm pts := (List.perm_cons_erase hj).symm
    have hmap_perm : ((j :: pts.erase j).map den).Perm (pts.map den) := hperm.map den
    simpa [List.map_cons, List.prod_cons] using hmap_perm.prod_eq
  let termList : ℕ → List ℤ := fun j =>
    coeffsScale (vals.getD j 0 * ((pts.erase j).map den).prod) (linearFactorProd (pts.erase j))
  let num : List ℤ := (pts.map termList).foldr coeffsAdd []
  have hfoldr_poly : ∀ L : List (List ℤ),
      coeffsToPoly (L.foldr coeffsAdd []) = (L.map coeffsToPoly).sum := by
    intro L
    induction L with
    | nil => simp [coeffsToPoly]
    | cons x xs ih => simp [coeffsToPoly_add, ih]
  have hnum_deg : (coeffsToPoly num).natDegree ≤ r := by
    dsimp [num]
    rw [hfoldr_poly]
    have hsum_le : ∀ L : List ℕ, (∀ j ∈ L, j ∈ pts) →
        (((L.map termList).map coeffsToPoly).sum).natDegree ≤ r := by
      intro L hL
      induction L with
      | nil => simp
      | cons j js ih =>
        simp only [List.map_cons, List.sum_cons]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (ih fun i hi => hL i (List.mem_cons_of_mem j hi)))
        dsimp [termList]
        rw [coeffsToPoly_scale]
        calc (Polynomial.C _ * coeffsToPoly (linearFactorProd (pts.erase j))).natDegree
          _ ≤ (Polynomial.C _).natDegree + (coeffsToPoly (linearFactorProd (pts.erase j))).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (pts.erase j).length := by
            rw [Polynomial.natDegree_C, zero_add]
            exact natDegree_linearFactorProd_le _
          _ = r := by
            have hj_mem : j ∈ pts := hL j List.mem_cons_self
            rw [List.length_erase_of_mem hj_mem]
            simp [pts]
    exact hsum_le pts (fun j hj => hj)
  have hnum_eval : ∀ k ≤ r, (coeffsToPoly num).eval (k : ℤ) = M * g.eval (k : ℤ) := by
    intro k hk
    have hk_pts : k ∈ pts := List.mem_range.mpr (by omega)
    have heval_foldr : ∀ L : List (List ℤ),
        (coeffsToPoly (L.foldr coeffsAdd [])).eval (k : ℤ) =
          ((L.map coeffsToPoly).map (Polynomial.eval (k : ℤ))).sum := by
      intro L
      induction L with
      | nil => simp [coeffsToPoly]
      | cons x xs ih => simp [coeffsToPoly_add, ih]
    dsimp [num]
    rw [heval_foldr]
    have hsplit : ∀ L : List ℕ, L.Nodup → k ∈ L → (∀ j ∈ L, j ∈ pts) →
        (((L.map termList).map coeffsToPoly).map (Polynomial.eval (k : ℤ))).sum =
          M * g.eval (k : ℤ) := by
      intro L hnd hkL hLpts
      induction L with
      | nil => cases hkL
      | cons j js ih =>
        rw [List.nodup_cons] at hnd
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hkL with rfl | hk_js
        · have hrest_zero : ∀ i ∈ js, (coeffsToPoly (termList i)).eval (k : ℤ) = 0 := by
            intro i hi
            have hik : k ≠ i := fun heq => hnd.1 (heq ▸ hi)
            have hk_erase : k ∈ pts.erase i :=
              (List.mem_erase_of_ne hik).mpr hk_pts
            dsimp [termList]
            rw [coeffsToPoly_scale, Polynomial.eval_mul, Polynomial.eval_C,
              eval_linearFactorProd_of_mem hk_erase, mul_zero]
          have hsum0 : (((js.map termList).map coeffsToPoly).map (Polynomial.eval (k : ℤ))).sum = 0 := by
            rw [List.map_map, List.map_map]
            apply List.sum_eq_zero
            intro v hv
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
            exact hrest_zero i hi
          rw [hsum0, add_zero]
          dsimp [termList]
          rw [coeffsToPoly_scale, Polynomial.eval_mul, Polynomial.eval_C,
            eval_linearFactorProd_self, hvals k hk]
          have hMk := hMj_mul k hk_pts
          dsimp [den] at hMk
          linear_combination g.eval (k : ℤ) * hMk
        · have hj_ne_k : k ≠ j := fun heq => hnd.1 (heq ▸ hk_js)
          have hk_erase : k ∈ pts.erase j := (List.mem_erase_of_ne hj_ne_k).mpr hk_pts
          have hhead0 : (coeffsToPoly (termList j)).eval (k : ℤ) = 0 := by
            dsimp [termList]
            rw [coeffsToPoly_scale, Polynomial.eval_mul, Polynomial.eval_C,
              eval_linearFactorProd_of_mem hk_erase, mul_zero]
          rw [hhead0, zero_add]
          exact ih hnd.2 hk_js (fun i hi => hLpts i (List.mem_cons_of_mem j hi))
    exact hsplit pts hpts_nodup hk_pts (fun j hj => hj)
  have hpoly_eq : coeffsToPoly num = Polynomial.C M * g := by
    by_contra hne
    have hdiff_ne : coeffsToPoly num - Polynomial.C M * g ≠ 0 := sub_ne_zero.mpr hne
    have hdiff_deg : (coeffsToPoly num - Polynomial.C M * g).natDegree ≤ r := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le hnum_deg ?_)
      calc (Polynomial.C M * g).natDegree
        _ ≤ (Polynomial.C M).natDegree + g.natDegree := Polynomial.natDegree_mul_le
        _ ≤ r := by rw [Polynomial.natDegree_C, zero_add]; exact hg_deg
    let S : Finset ℤ := (Finset.range (r + 1)).image (fun j : ℕ => (j : ℤ))
    have hS_card : S.card = r + 1 := by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    have hS_roots : ∀ x ∈ S, x ∈ (coeffsToPoly num - Polynomial.C M * g).roots := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Polynomial.mem_roots hdiff_ne, Polynomial.IsRoot, Polynomial.eval_sub,
        hnum_eval j hj_le, Polynomial.eval_mul, Polynomial.eval_C, sub_self]
    have hcard_le : S.card ≤ (coeffsToPoly num - Polynomial.C M * g).roots.card :=
      Multiset.card_le_card (Multiset.le_iff_subset S.nodup |>.mpr fun x hx => hS_roots x hx)
    have hroots_le := Polynomial.card_roots' (coeffsToPoly num - Polynomial.C M * g)
    omega
  let numTrim := coeffsTrim num
  have hnumTrim_poly : coeffsToPoly numTrim = Polynomial.C M * g := by
    rw [coeffsToPoly_trim, hpoly_eq]
  have hall_dvd : numTrim.all (fun c => decide (M ∣ c)) = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [decide_eq_true_eq]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hci := congrArg (fun p : ℤ[X] => p.coeff i) hnumTrim_poly
    rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi, Polynomial.coeff_C_mul] at hci
    exact ⟨g.coeff i, hci⟩
  have hmap_poly : coeffsToPoly (numTrim.map (· / M)) = g := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hM_ne)
    rw [← coeffsToPoly_scale, ← hnumTrim_poly]
    congr 1
    unfold coeffsScale
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.getElem_map, Function.comp_apply]
    have hci := congrArg (fun p : ℤ[X] => p.coeff i) hnumTrim_poly
    rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi2, Polynomial.coeff_C_mul] at hci
    rw [hci, Int.mul_ediv_cancel_left _ hM_ne]
  change (if M = 0 then none
    else if (numTrim.all fun c => decide (M ∣ c)) = true then
      some (coeffsTrim (numTrim.map (· / M)))
    else none) = some (polyToCoeffs g)
  simp only [hM_ne, hall_dvd, ↓reduceIte, Option.some.injEq]
  rw [coeffsTrim_eq_polyToCoeffs, hmap_poly]

/-- Cartesian product of a list of divisor lists (`∏_{j=0}^r D_j`), returning all value tuples. -/
def cartesianTuples : List (List ℤ) → List (List ℤ)
  | [] => [[]]
  | ds :: rest =>
    let tailTuples := cartesianTuples rest
    ds.flatMap fun d => tailTuples.map (d :: ·)

theorem mem_cartesianTuples_iff : ∀ (lists : List (List ℤ)) (t : List ℤ),
    t ∈ cartesianTuples lists ↔
      t.length = lists.length ∧ ∀ i (hi : i < lists.length), t.getD i 0 ∈ lists[i]
  | [], t => by
    simp only [cartesianTuples, List.mem_singleton, List.length_nil]
    constructor
    · rintro rfl; simp
    · intro ⟨hlen, _⟩; exact List.eq_nil_of_length_eq_zero hlen
  | ds :: rest, t => by
    simp only [cartesianTuples, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨d, hd, ts, hts, rfl⟩
      obtain ⟨hlen, hmem⟩ := (mem_cartesianTuples_iff rest ts).mp hts
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hd
      | succ j =>
        have hj : j < rest.length := by simp at hi; omega
        simpa using hmem j hj
    · rintro ⟨hlen, hmem⟩
      cases t with
      | nil => simp at hlen
      | cons d ts =>
        refine ⟨d, hmem 0 (by simp), ts, ?_, rfl⟩
        rw [mem_cartesianTuples_iff rest ts]
        refine ⟨by simp at hlen; omega, fun j hj => ?_⟩
        exact hmem (j + 1) (by simp; omega)

theorem cartesianTuples_length : ∀ (lists : List (List ℤ)),
    (cartesianTuples lists).length = (lists.map List.length).prod
  | [] => rfl
  | ds :: rest => by
    simp only [cartesianTuples, List.map_cons, List.prod_cons]
    have hflat : ∀ (xs : List ℤ) (ys : List (List ℤ)),
        (xs.flatMap fun d => ys.map (d :: ·)).length = xs.length * ys.length := by
      intro xs ys
      induction xs with
      | nil => simp
      | cons x xs' ih =>
        simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]
    rw [hflat, cartesianTuples_length rest]

/-- Computable natural-number GCD of all coefficients in a `List ℤ`. -/
def coeffsNatGcd : List ℤ → ℕ
  | [] => 0
  | a :: as => Nat.gcd a.natAbs (coeffsNatGcd as)

theorem coeffsNatGcd_dvd_all (as : List ℤ) :
    ∀ a ∈ as, (coeffsNatGcd as : ℤ) ∣ a := by
  induction as with
  | nil => intro _ h; cases h
  | cons a as ih =>
    intro x hx
    simp only [coeffsNatGcd]
    rcases List.mem_cons.mp hx with hxa | hmem
    · subst hxa
      exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left x.natAbs (coeffsNatGcd as))
    · exact dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right a.natAbs (coeffsNatGcd as))) (ih x hmem)

theorem dvd_coeffsNatGcd (as : List ℤ) (d : ℕ) (hd : ∀ a ∈ as, (d : ℤ) ∣ a) :
    d ∣ coeffsNatGcd as := by
  induction as with
  | nil => simp [coeffsNatGcd]
  | cons a as ih =>
    simp only [coeffsNatGcd]
    refine Nat.dvd_gcd ?_ (ih fun x hx => hd x (List.mem_cons_of_mem a hx))
    exact Int.ofNat_dvd_left.mp (hd a List.mem_cons_self)

theorem coeffsNatGcd_trim (as : List ℤ) :
    coeffsNatGcd (coeffsTrim as) = coeffsNatGcd as := by
  apply Nat.dvd_antisymm
  · apply dvd_coeffsNatGcd
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hci := congrArg (fun p : ℤ[X] => p.coeff i) (coeffsToPoly_trim as)
    rw [coeffsToPoly_coeff, coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi] at hci
    rw [← hci]
    by_cases hi' : i < (coeffsTrim as).length
    · rw [List.getD_eq_getElem _ _ hi']
      exact coeffsNatGcd_dvd_all (coeffsTrim as) _ (List.getElem_mem hi')
    · rw [List.getD_eq_default _ _ (by omega)]
      exact dvd_zero _
  · apply dvd_coeffsNatGcd
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hci := congrArg (fun p : ℤ[X] => p.coeff i) (coeffsToPoly_trim as).symm
    rw [coeffsToPoly_coeff, coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi] at hci
    rw [← hci]
    by_cases hi' : i < as.length
    · rw [List.getD_eq_getElem _ _ hi']
      exact coeffsNatGcd_dvd_all as _ (List.getElem_mem hi')
    · rw [List.getD_eq_default _ _ (by omega)]
      exact dvd_zero _

theorem coeffsNatGcd_eq_zero_iff (as : List ℤ) :
    coeffsNatGcd as = 0 ↔ coeffsToPoly as = 0 := by
  rw [← coeffsNatGcd_trim, ← coeffsTrim_eq_nil_iff]
  constructor
  · intro hg0
    by_contra hne
    have hlast := coeffsTrim_getLast_ne_zero hne
    have hdvd := coeffsNatGcd_dvd_all (coeffsTrim as) _ (List.getLast_mem hne)
    rw [hg0, Nat.cast_zero, zero_dvd_iff] at hdvd
    exact hlast hdvd
  · intro hnil
    simp [hnil, coeffsNatGcd]

theorem coeffsNatGcd_eq_one_iff_isPrimitive (as : List ℤ) :
    coeffsNatGcd as = 1 ↔ (coeffsToPoly as).IsPrimitive := by
  rw [← coeffsNatGcd_trim, ← coeffsToPoly_trim]
  constructor
  · intro hg1 r hr
    obtain ⟨q, hq⟩ := hr
    have hdvd_nat : r.natAbs ∣ coeffsNatGcd (coeffsTrim as) := by
      apply dvd_coeffsNatGcd
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hci := congrArg (fun p : ℤ[X] => p.coeff i) hq
      rw [coeffsToPoly_coeff, List.getD_eq_getElem _ _ hi, Polynomial.coeff_C_mul] at hci
      exact Int.natAbs_dvd.mpr ⟨q.coeff i, hci⟩
    rw [hg1, Nat.dvd_one] at hdvd_nat
    exact Int.isUnit_iff_natAbs_eq.mpr hdvd_nat
  · intro hprim
    have hdvd_poly : Polynomial.C (coeffsNatGcd (coeffsTrim as) : ℤ) ∣
        coeffsToPoly (coeffsTrim as) := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [coeffsToPoly_coeff]
      by_cases hi : i < (coeffsTrim as).length
      · rw [List.getD_eq_getElem _ _ hi]
        exact coeffsNatGcd_dvd_all (coeffsTrim as) _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact dvd_zero _
    have hu := hprim _ hdvd_poly
    have habs := Int.isUnit_iff_natAbs_eq.mp hu
    simpa using habs

/-- Fuel-based helper for natural-number prime factorization via `Nat.minFac`. -/
def natPrimeFactorListAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | _ + 1, 1 => []
  | fuel + 1, m =>
    let p := m.minFac
    p :: natPrimeFactorListAux fuel (m / p)

/-- Computable natural-number prime factorization via `Nat.minFac`. -/
def natPrimeFactorList (n : ℕ) : List ℕ :=
  natPrimeFactorListAux n n

theorem natPrimeFactorList_spec {n : ℕ} (hn0 : n ≠ 0) :
    (∀ p ∈ natPrimeFactorList n, Nat.Prime p) ∧ (natPrimeFactorList n).prod = n := by
  have haux : ∀ (fuel m : ℕ), m ≠ 0 → m ≤ fuel →
      (∀ p ∈ natPrimeFactorListAux fuel m, Nat.Prime p) ∧
      (natPrimeFactorListAux fuel m).prod = m := by
    intro fuel
    induction fuel with
    | zero =>
      intro m hm0 hle
      omega
    | succ f ih =>
      intro m hm0 hle
      match m with
      | 0 => exact absurd rfl hm0
      | 1 => simp [natPrimeFactorListAux]
      | k + 2 =>
        simp only [natPrimeFactorListAux]
        let p := (k + 2).minFac
        have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
        have hp_dvd : p ∣ k + 2 := Nat.minFac_dvd (k + 2)
        have hq_lt : (k + 2) / p < k + 2 := Nat.div_lt_self (by omega) hp_prime.one_lt
        have hq_ne : (k + 2) / p ≠ 0 := by
          intro hz
          have hmul := Nat.mul_div_cancel' hp_dvd
          rw [hz, mul_zero] at hmul
          omega
        obtain ⟨hprimes, hprod⟩ := ih ((k + 2) / p) hq_ne (by omega)
        refine ⟨?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hmem
          · exact hp_prime
          · exact hprimes q hmem
        · rw [List.prod_cons, hprod]
          exact Nat.mul_div_cancel' hp_dvd
  exact haux n n hn0 le_rfl

/-- Computable single Kronecker splitting step on a trimmed primitive polynomial `cs` of degree
`n ≥ 2` (`cs.length ≥ 3`): searches integer roots `0 ≤ j ≤ n / 2` first, then Lagrange interpolants
of degree `1 ≤ deg g ≤ n / 2` over divisor tuples of `(f(0), ..., f(r))`. Returns `some (g, q)`
with `1 ≤ deg g < n` and `1 ≤ deg q < n` if reducible, or `none` if irreducible. -/
def kroneckerFindProperFactor (cs : List ℤ) : Option (List ℤ × List ℤ) :=
  let cs' := coeffsTrim cs
  if cs'.length < 3 then none
  else
    let n := cs'.length - 1
    let r := n / 2
    let pts := List.range (r + 1)
    match pts.find? (fun j : ℕ => coeffsEval cs' (j : ℤ) == 0) with
    | some j =>
      let g := [-(j : ℤ), 1]
      match coeffsDivExact? cs' g with
      | some q => some (g, q)
      | none => none
    | none =>
      let divLists := pts.map (fun j : ℕ => intDivisorsList (coeffsEval cs' (j : ℤ)))
      let tuples := cartesianTuples divLists
      tuples.findSome? fun t =>
        match lagrangeInterpCoeffs? r t with
        | some g =>
          if 2 ≤ g.length ∧ g.length ≤ r + 1 then
            match coeffsDivExact? cs' g with
            | some q => some (g, q)
            | none => none
          else none
        | none => none

theorem kroneckerFindProperFactor_sound {cs g q : List ℤ}
    (h : kroneckerFindProperFactor cs = some (g, q)) :
    g = coeffsTrim g ∧ q = coeffsTrim q ∧
    2 ≤ g.length ∧ g.length < (coeffsTrim cs).length ∧
    2 ≤ q.length ∧ q.length < (coeffsTrim cs).length ∧
    coeffsToPoly cs = coeffsToPoly g * coeffsToPoly q := by
  unfold kroneckerFindProperFactor at h
  set cs' := coeffsTrim cs
  by_cases hlt : cs'.length < 3
  · simp [hlt] at h
  · simp only [hlt, ↓reduceIte] at h
    have hcs'_ne : cs' ≠ [] := by intro hnil; rw [hnil] at hlt; simp at hlt
    have hcs_pne : coeffsToPoly cs ≠ 0 :=
      fun hz => hcs'_ne ((coeffsTrim_eq_nil_iff cs).mpr hz)
    set n := cs'.length - 1
    set r := n / 2
    have hr_lt_n : r < n := by omega
    have hr_pos : 1 ≤ r := by omega
    cases hroot : (List.range (r + 1)).find? (fun j : ℕ => coeffsEval cs' (j : ℤ) == 0) with
    | some j =>
      rw [hroot] at h
      dsimp only [] at h
      cases hdiv : coeffsDivExact? cs' [-(j : ℤ), 1] with
      | none => simp [hdiv] at h
      | some q0 =>
        simp only [hdiv, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨_, hq_trim, hmul⟩ := coeffsDivExact?_sound hdiv
        rw [coeffsToPoly_trim] at hmul
        have hg_trim : [-(j : ℤ), 1] = coeffsTrim [-(j : ℤ), 1] := by simp [coeffsTrim]
        have hg_pne : coeffsToPoly [-(j : ℤ), 1] ≠ 0 := by
          intro hz
          have hnil := (coeffsTrim_eq_nil_iff [-(j : ℤ), 1]).mpr hz
          rw [← hg_trim] at hnil
          simp at hnil
        have hq_pne : coeffsToPoly q0 ≠ 0 := fun hz => hcs_pne (by rw [hmul, hz, mul_zero])
        have hq_ne : coeffsTrim q0 ≠ [] := fun hnil => hq_pne ((coeffsTrim_eq_nil_iff q0).mp hnil)
        have hdeg_g : (coeffsToPoly [-(j : ℤ), 1]).natDegree = 1 := by
          have hl := coeffsTrim_length_eq_natDegree_succ (hg_trim ▸ List.cons_ne_nil _ _)
          rw [← hg_trim] at hl
          simp at hl
          omega
        have hdeg_cs : (coeffsToPoly cs).natDegree = n := by
          have hl := coeffsTrim_length_eq_natDegree_succ hcs'_ne
          dsimp [cs', n]
          omega
        have hdeg_q : (coeffsToPoly q0).natDegree = n - 1 := by
          have hm := Polynomial.natDegree_mul hg_pne hq_pne
          rw [← hmul, hdeg_cs, hdeg_g] at hm
          omega
        have hq_len : q0.length = n := by
          have hl := coeffsTrim_length_eq_natDegree_succ hq_ne
          rw [← hq_trim, hdeg_q] at hl
          omega
        have hlin_len : [-(j : ℤ), 1].length = 2 := rfl
        refine ⟨hg_trim, hq_trim, by simp, by dsimp [n] at hr_lt_n; omega, by omega,
          by dsimp [n] at hq_len hr_lt_n; omega, hmul⟩
    | none =>
      rw [hroot] at h
      dsimp only [] at h
      obtain ⟨t, _, ht⟩ := List.exists_of_findSome?_eq_some h
      cases hlag : lagrangeInterpCoeffs? r t with
      | none => simp [hlag] at ht
      | some g0 =>
        simp only [hlag] at ht
        by_cases hglen : 2 ≤ g0.length ∧ g0.length ≤ r + 1
        · simp only [hglen, and_self, ↓reduceIte] at ht
          cases hdiv : coeffsDivExact? cs' g0 with
          | none => simp [hdiv] at ht
          | some q0 =>
            simp only [hdiv, Option.some.injEq, Prod.mk.injEq] at ht
            rcases ht with ⟨rfl, rfl⟩
            have hg_trim : g0 = coeffsTrim g0 := lagrangeInterpCoeffs?_eq_some_trim hlag
            obtain ⟨hg_pne, hq_trim, hmul⟩ := coeffsDivExact?_sound hdiv
            rw [coeffsToPoly_trim] at hmul
            have hq_pne : coeffsToPoly q0 ≠ 0 := fun hz => hcs_pne (by rw [hmul, hz, mul_zero])
            have hg_ne : coeffsTrim g0 ≠ [] := fun hnil => hg_pne ((coeffsTrim_eq_nil_iff g0).mp hnil)
            have hq_ne : coeffsTrim q0 ≠ [] := fun hnil => hq_pne ((coeffsTrim_eq_nil_iff q0).mp hnil)
            have hdeg_g : (coeffsToPoly g0).natDegree + 1 = g0.length := by
              have hl := coeffsTrim_length_eq_natDegree_succ hg_ne
              rw [← hg_trim] at hl
              exact hl.symm
            have hdeg_cs : (coeffsToPoly cs).natDegree = n := by
              have hl := coeffsTrim_length_eq_natDegree_succ hcs'_ne
              dsimp [cs', n]
              omega
            have hdeg_mul := Polynomial.natDegree_mul hg_pne hq_pne
            rw [← hmul, hdeg_cs] at hdeg_mul
            have hq_len : q0.length = (coeffsToPoly q0).natDegree + 1 := by
              have hl := coeffsTrim_length_eq_natDegree_succ hq_ne
              rwa [← hq_trim] at hl
            refine ⟨hg_trim, hq_trim, hglen.1, by dsimp [n] at hr_lt_n; omega, by omega,
              by dsimp [n] at hr_lt_n; omega, hmul⟩
        · simp [hglen] at ht

theorem kroneckerFindProperFactor_eq_none_irreducible {cs : List ℤ}
    (hprim : (coeffsToPoly cs).IsPrimitive)
    (hdeg_ge : 1 ≤ (coeffsToPoly cs).natDegree)
    (hnone : kroneckerFindProperFactor cs = none) :
    Irreducible (coeffsToPoly cs) := by
  set f := coeffsToPoly cs with hf_def
  have hf0 : f ≠ 0 := hprim.ne_zero
  have hf_not_unit : ¬ IsUnit f := by
    intro hu
    have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  refine ⟨hf_not_unit, fun a b hab => ?_⟩
  by_contra hboth
  push Not at hboth
  rcases hboth with ⟨hau, hbu⟩
  have ha0 : a ≠ 0 := fun hz => hf0 (by rw [hab, hz, zero_mul])
  have hb0 : b ≠ 0 := fun hz => hf0 (by rw [hab, hz, mul_zero])
  have ha_deg_pos : 1 ≤ a.natDegree := by
    by_contra hlt
    have hd0 : a.natDegree = 0 := by omega
    have haC : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hdvd : Polynomial.C (a.coeff 0) ∣ f := ⟨b, by rw [← haC, hab]⟩
    exact hau (haC ▸ (hprim (a.coeff 0) hdvd).map Polynomial.C)
  have hb_deg_pos : 1 ≤ b.natDegree := by
    by_contra hlt
    have hd0 : b.natDegree = 0 := by omega
    have hbC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hdvd : Polynomial.C (b.coeff 0) ∣ f := ⟨a, by rw [← hbC, mul_comm, hab]⟩
    exact hbu (hbC ▸ (hprim (b.coeff 0) hdvd).map Polynomial.C)
  have hsum : a.natDegree + b.natDegree = f.natDegree := by
    rw [← Polynomial.natDegree_mul ha0 hb0, ← hab]
  have hf_deg2 : 2 ≤ f.natDegree := by omega
  have hcs'_ne : coeffsTrim cs ≠ [] :=
    fun hnil => hf0 (by rw [hf_def]; exact (coeffsTrim_eq_nil_iff cs).mp hnil)
  have hcs'_len : (coeffsTrim cs).length = f.natDegree + 1 := by
    rw [hf_def]
    exact coeffsTrim_length_eq_natDegree_succ hcs'_ne
  obtain ⟨g, h, hgh, hg0, hg_deg_pos, hg_deg_le⟩ :
      ∃ g h : ℤ[X], f = g * h ∧ g ≠ 0 ∧ 1 ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree / 2 := by
    by_cases hal : a.natDegree ≤ f.natDegree / 2
    · exact ⟨a, b, hab, ha0, ha_deg_pos, hal⟩
    · exact ⟨b, a, hab.trans (mul_comm a b), hb0, hb_deg_pos, by omega⟩
  unfold kroneckerFindProperFactor at hnone
  have hnot_lt3 : ¬ (coeffsTrim cs).length < 3 := by omega
  have hn_eq : (coeffsTrim cs).length - 1 = f.natDegree := by omega
  simp only [hnot_lt3, ↓reduceIte, hn_eq] at hnone
  set r := f.natDegree / 2
  cases hroot : (List.range (r + 1)).find? (fun j : ℕ => coeffsEval (coeffsTrim cs) (j : ℤ) == 0) with
  | some j =>
    rw [hroot] at hnone
    dsimp only [] at hnone
    have hj_eval0 : f.eval (j : ℤ) = 0 := by
      have heq := List.find?_some hroot
      rw [beq_iff_eq, coeffsEval_eq, coeffsToPoly_trim, ← hf_def] at heq
      exact heq
    obtain ⟨q, hfq⟩ := Polynomial.dvd_iff_isRoot.mpr hj_eval0
    have hlin_eq : coeffsToPoly [-(j : ℤ), 1] = Polynomial.X - Polynomial.C (j : ℤ) := by
      simp [coeffsToPoly]; ring
    have hlin_ne : coeffsToPoly [-(j : ℤ), 1] ≠ 0 := by
      rw [hlin_eq]
      exact Polynomial.X_sub_C_ne_zero (j : ℤ)
    have hdiv := coeffsDivExact?_complete (a := coeffsTrim cs) (b := [-(j : ℤ), 1]) (q := q)
      hlin_ne (by rw [coeffsToPoly_trim, ← hf_def, hlin_eq]; exact hfq)
    simp [hdiv] at hnone
  | none =>
    rw [hroot] at hnone
    dsimp only [] at hnone
    have hno_root : ∀ j ≤ r, f.eval (j : ℤ) ≠ 0 := by
      intro j hj hz
      have hmem : j ∈ List.range (r + 1) := List.mem_range.mpr (by omega)
      have hsat : (coeffsEval (coeffsTrim cs) (j : ℤ) == 0) = true := by
        rw [beq_iff_eq, coeffsEval_eq, coeffsToPoly_trim, ← hf_def]
        exact hz
      exact List.find?_eq_none.mp hroot j hmem hsat
    let t : List ℤ := (List.range (r + 1)).map (fun j : ℕ => g.eval (j : ℤ))
    have ht_mem : t ∈ cartesianTuples
        ((List.range (r + 1)).map (fun j : ℕ => intDivisorsList (coeffsEval (coeffsTrim cs) (j : ℤ)))) := by
      rw [mem_cartesianTuples_iff]
      refine ⟨by simp [t], fun i hi => ?_⟩
      have hi_lt : i < r + 1 := by simpa using hi
      have ht_i : t.getD i 0 = g.eval (i : ℤ) := by
        rw [List.getD_eq_getElem _ _ (by simp [t]; omega)]
        simp [t]
      rw [ht_i]
      simp only [List.getElem_map, List.getElem_range]
      rw [coeffsEval_eq, coeffsToPoly_trim, ← hf_def, mem_intDivisorsList_iff (hno_root i (by omega))]
      exact ⟨h.eval (i : ℤ), by rw [hgh, Polynomial.eval_mul]⟩
    have hlag : lagrangeInterpCoeffs? r t = some (polyToCoeffs g) := by
      apply lagrangeInterpCoeffs?_complete r g hg_deg_le t (by simp [t])
      intro j hj
      rw [List.getD_eq_getElem _ _ (by simp [t]; omega)]
      simp [t]
    have hglen : 2 ≤ (polyToCoeffs g).length ∧ (polyToCoeffs g).length ≤ r + 1 := by
      simp only [polyToCoeffs, hg0, ↓reduceIte, List.length_map, List.length_range]
      exact ⟨by omega, Nat.add_le_add_right hg_deg_le 1⟩
    have hdiv : coeffsDivExact? (coeffsTrim cs) (polyToCoeffs g) = some (polyToCoeffs h) := by
      apply coeffsDivExact?_complete
      · rw [(coeffsToPoly_polyToCoeffs g).1]; exact hg0
      · rw [coeffsToPoly_trim, ← hf_def, (coeffsToPoly_polyToCoeffs g).1]; exact hgh
    have hnone_all := List.findSome?_eq_none_iff.mp hnone t ht_mem
    simp [hlag, hglen, hdiv] at hnone_all

/-- Computable recursive Kronecker factorization of a trimmed primitive polynomial `cs` of degree
at least `1` (`2 ≤ cs.length`), fueled by `cs.length`. -/
def kroneckerFactorPrimAux : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | fuel + 1, cs =>
    let cs' := coeffsTrim cs
    if cs'.length ≤ 2 then [cs']
    else
      match kroneckerFindProperFactor cs' with
      | none => [cs']
      | some (g, q) => kroneckerFactorPrimAux fuel g ++ kroneckerFactorPrimAux fuel q

theorem kroneckerFactorPrimAux_spec :
    ∀ (fuel : ℕ) (cs : List ℤ),
      2 ≤ (coeffsTrim cs).length →
      (coeffsTrim cs).length ≤ fuel →
      (coeffsToPoly cs).IsPrimitive →
      kroneckerFactorPrimAux fuel cs ≠ [] ∧
      (∀ p ∈ kroneckerFactorPrimAux fuel cs, Irreducible (coeffsToPoly p)) ∧
      ((kroneckerFactorPrimAux fuel cs).map coeffsToPoly).prod = coeffsToPoly cs := by
  intro fuel
  induction fuel with
  | zero =>
    intro cs hge2 hlen _
    omega
  | succ f ih =>
    intro cs hge2 hlen hprim
    unfold kroneckerFactorPrimAux
    set cs' := coeffsTrim cs
    have hcs'_poly : coeffsToPoly cs' = coeffsToPoly cs := coeffsToPoly_trim cs
    have hcs'_ne : cs' ≠ [] := by intro hnil; rw [hnil] at hge2; simp at hge2
    have hlen_deg : cs'.length = (coeffsToPoly cs).natDegree + 1 :=
      coeffsTrim_length_eq_natDegree_succ hcs'_ne
    by_cases hle2 : cs'.length ≤ 2
    · simp only [hle2, ↓reduceIte]
      have hd1 : (coeffsToPoly cs).natDegree = 1 := by omega
      have hirr_cs : Irreducible (coeffsToPoly cs) := by
        refine ⟨fun hu => ?_, fun a b hab => ?_⟩
        · have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
          omega
        · have ha0 : a ≠ 0 := fun hz => hprim.ne_zero (by rw [hab, hz, zero_mul])
          have hb0 : b ≠ 0 := fun hz => hprim.ne_zero (by rw [hab, hz, mul_zero])
          have hsum : a.natDegree + b.natDegree = 1 := by
            rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hd1]
          rcases (show a.natDegree = 0 ∨ b.natDegree = 0 by omega) with ha_d0 | hb_d0
          · left
            have haC := Polynomial.eq_C_of_natDegree_eq_zero ha_d0
            exact haC ▸ (hprim (a.coeff 0) ⟨b, by rw [← haC, hab]⟩).map Polynomial.C
          · right
            have hbC := Polynomial.eq_C_of_natDegree_eq_zero hb_d0
            exact hbC ▸ (hprim (b.coeff 0) ⟨a, by rw [← hbC, mul_comm, hab]⟩).map Polynomial.C
      refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
      · intro p hp
        rw [List.mem_singleton.mp hp, hcs'_poly]
        exact hirr_cs
      · simp [hcs'_poly]
    · simp only [hle2, ↓reduceIte]
      cases hfind : kroneckerFindProperFactor cs' with
      | none =>
        have hprim' : (coeffsToPoly cs').IsPrimitive := hcs'_poly.symm ▸ hprim
        have hdeg_ge' : 1 ≤ (coeffsToPoly cs').natDegree := by
          rw [hcs'_poly]; omega
        have hirr' := kroneckerFindProperFactor_eq_none_irreducible hprim' hdeg_ge' hfind
        refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
        · intro p hp
          rw [List.mem_singleton.mp hp]
          exact hirr'
        · simp [hcs'_poly]
      | some gq =>
        rcases gq with ⟨g, q⟩
        dsimp only []
        obtain ⟨hg_trim, hq_trim, hg_ge2, hg_lt, hq_ge2, hq_lt, hmul⟩ :=
          kroneckerFindProperFactor_sound hfind
        have hg_lt' : g.length < cs'.length := by dsimp [cs'] at hg_lt ⊢; rwa [coeffsTrim_idem] at hg_lt
        have hq_lt' : q.length < cs'.length := by dsimp [cs'] at hq_lt ⊢; rwa [coeffsTrim_idem] at hq_lt
        rw [hcs'_poly] at hmul
        have hg_prim : (coeffsToPoly g).IsPrimitive := by
          intro r hr
          exact hprim r (dvd_trans hr ⟨coeffsToPoly q, hmul⟩)
        have hq_prim : (coeffsToPoly q).IsPrimitive := by
          intro r hr
          exact hprim r (dvd_trans hr ⟨coeffsToPoly g, by rw [mul_comm, ← hmul]⟩)
        have hg_ge2' : 2 ≤ (coeffsTrim g).length := hg_trim ▸ hg_ge2
        have hq_ge2' : 2 ≤ (coeffsTrim q).length := hq_trim ▸ hq_ge2
        have hg_le_f : (coeffsTrim g).length ≤ f := by rw [← hg_trim]; omega
        have hq_le_f : (coeffsTrim q).length ≤ f := by rw [← hq_trim]; omega
        obtain ⟨hg_ne, hg_irr, hg_prod⟩ := ih g hg_ge2' hg_le_f hg_prim
        obtain ⟨_, hq_irr, hq_prod⟩ := ih q hq_ge2' hq_le_f hq_prim
        refine ⟨List.append_ne_nil_of_left_ne_nil hg_ne _, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hpg | hpq
          · exact hg_irr p hpg
          · exact hq_irr p hpq
        · rw [List.map_append, List.prod_append, hg_prod, hq_prod, ← hmul]

/-- **Exercise 5.1 — Computable Kronecker factorization programme** (§5.1, printed p. 50):
Total computable function `kroneckerProgramme : List ℤ → Option (ℤ × List (List ℤ))` implementing
the Kronecker factorization algorithm of Theorem 5.1 on dense integer coefficient lists:
- returns `none` iff the input polynomial is `0`;
- for any non-zero input `cs`, extracts integer content `c = gcd(cs) ≥ 1`, factors `c` into
  integer primes `[p]`, divides out `c` to obtain a primitive polynomial `primCs`, and factors
  `primCs` by Kronecker Lagrange-interpolation splitting, returning `some (u, factors)` where
  `u ∈ {1, -1}` (`u = 1` whenever a non-empty factor list is present so `u` is absorbed into the
  first factor!) and every `p ∈ factors` is irreducible in `ℤ[X]`. -/
def kroneckerProgramme (cs : List ℤ) : Option (ℤ × List (List ℤ)) :=
  let cs' := coeffsTrim cs
  if cs' = [] then none
  else
    let c := coeffsNatGcd cs'
    let contentFactors : List (List ℤ) := (natPrimeFactorList c).map (fun p : ℕ => [(p : ℤ)])
    let primCs := coeffsTrim (cs'.map (· / (c : ℤ)))
    if primCs.length ≤ 1 then
      let u := primCs.headD 1
      match contentFactors with
      | [] => some (u, [])
      | f0 :: fs => some (1, coeffsScale u f0 :: fs)
    else
      let polyFactors := kroneckerFactorPrimAux primCs.length primCs
      some (1, contentFactors ++ polyFactors)

private theorem int_irreducible_iff_natAbs_prime (a : ℤ) :
    Irreducible a ↔ Nat.Prime a.natAbs := by
  constructor
  · intro ha
    have ha0 : a ≠ 0 := ha.ne_zero
    have ha_nu : a.natAbs ≠ 1 := fun h1 => ha.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h1)
    have hge2 : 2 ≤ a.natAbs := by
      have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
      omega
    rw [Nat.prime_def_lt']
    refine ⟨hge2, fun m hm2 hmlt hmdvd => ?_⟩
    obtain ⟨k, hk⟩ := hmdvd
    have hk_ge2 : 2 ≤ k := by
      rcases k with _ | _ | k'
      · omega
      · omega
      · omega
    rcases Int.natAbs_eq a with hpos | hneg
    · have hprod : a = (m : ℤ) * (k : ℤ) := by
        rw [hpos, hk, Nat.cast_mul]
      rcases ha.isUnit_or_isUnit hprod with hum | huk
      · have hm1 : m = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp hum
        omega
      · have hk1 : k = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp huk
        omega
    · have hprod : a = (-(m : ℤ)) * (k : ℤ) := by
        rw [hneg, hk, Nat.cast_mul, neg_mul]
      rcases ha.isUnit_or_isUnit hprod with hum | huk
      · have hm1 : m = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp hum
        omega
      · have hk1 : k = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp huk
        omega
  · intro hp
    have hp_def := Nat.prime_def_lt'.mp hp
    refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
    · have h1 := Int.isUnit_iff_natAbs_eq.mp hu
      omega
    · have habs : a.natAbs = x.natAbs * y.natAbs := by rw [hxy, Int.natAbs_mul]
      by_cases hx1 : x.natAbs = 1
      · exact Or.inl (Int.isUnit_iff_natAbs_eq.mpr hx1)
      · by_cases hy1 : y.natAbs = 1
        · exact Or.inr (Int.isUnit_iff_natAbs_eq.mpr hy1)
        · exfalso
          have hx0 : x.natAbs ≠ 0 := by intro hz; rw [hz, zero_mul] at habs; omega
          have hy0 : y.natAbs ≠ 0 := by intro hz; rw [hz, mul_zero] at habs; omega
          have hx2 : 2 ≤ x.natAbs := by omega
          have hy2 : 2 ≤ y.natAbs := by omega
          have hx_lt : x.natAbs < a.natAbs := by nlinarith
          exact hp_def.2 x.natAbs hx2 hx_lt ⟨y.natAbs, habs⟩

private theorem irreducible_C_natPrime {p : ℕ} (hp : Nat.Prime p) :
    Irreducible (Polynomial.C (p : ℤ) : ℤ[X]) := by
  rw [corollary_gauss_lemma ℚ (Polynomial.C (p : ℤ))]
  exact Or.inl ⟨(p : ℤ), (int_irreducible_iff_natAbs_prime (p : ℤ)).mpr (by simpa using hp), rfl⟩

/-- **Exercise 5.1 — Full correctness specification of `kroneckerProgramme`** (§5.1, p. 50):
1. `kroneckerProgramme cs = none ↔ coeffsToPoly cs = 0`.
2. For every non-zero polynomial (`coeffsToPoly cs ≠ 0`), `kroneckerProgramme cs = some (u, L)` with
   `u = 1 ∨ u = -1`, every `q ∈ L` representing an irreducible polynomial in `ℤ[X]`, and
   `C u * (L.map coeffsToPoly).prod = coeffsToPoly cs`.
3. Whenever `coeffsToPoly cs` is also not a unit (`¬ IsUnit (coeffsToPoly cs)`), `u = 1` and
   `L ≠ []`, so `(L.map coeffsToPoly).prod = coeffsToPoly cs` expresses the polynomial directly as
   a non-empty product of irreducibles in `ℤ[X]`. -/
theorem exercise_5_1 (cs : List ℤ) :
    (kroneckerProgramme cs = none ↔ coeffsToPoly cs = 0) ∧
    (coeffsToPoly cs ≠ 0 →
      ∃ (u : ℤ) (L : List (List ℤ)),
        kroneckerProgramme cs = some (u, L) ∧
        (u = 1 ∨ u = -1) ∧
        (∀ q ∈ L, Irreducible (coeffsToPoly q)) ∧
        Polynomial.C u * (L.map coeffsToPoly).prod = coeffsToPoly cs ∧
        (¬ IsUnit (coeffsToPoly cs) →
          u = 1 ∧ L ≠ [] ∧ (L.map coeffsToPoly).prod = coeffsToPoly cs)) := by
  have hnone : kroneckerProgramme cs = none ↔ coeffsToPoly cs = 0 := by
    unfold kroneckerProgramme
    by_cases hnil : coeffsTrim cs = []
    · simp [hnil, (coeffsTrim_eq_nil_iff cs).mp hnil]
    · have hpne : coeffsToPoly cs ≠ 0 := fun hz => hnil ((coeffsTrim_eq_nil_iff cs).mpr hz)
      simp only [hnil, ↓reduceIte, hpne, iff_false]
      split_ifs with hle1
      · cases (natPrimeFactorList (coeffsNatGcd (coeffsTrim cs))).map (fun p : ℕ => [(p : ℤ)]) <;>
          simp
      · simp
  refine ⟨hnone, fun hf0 => ?_⟩
  have hnil : coeffsTrim cs ≠ [] := fun h => hf0 ((coeffsTrim_eq_nil_iff cs).mp h)
  unfold kroneckerProgramme
  simp only [hnil, ↓reduceIte]
  set cs' := coeffsTrim cs
  set c := coeffsNatGcd cs'
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    have hz : coeffsToPoly cs' = 0 := (coeffsNatGcd_eq_zero_iff cs').mp hc0
    rw [coeffsToPoly_trim] at hz
    exact hf0 hz
  obtain ⟨hc_primes, hc_prod⟩ := natPrimeFactorList_spec hc_ne0
  set contentFactors : List (List ℤ) := (natPrimeFactorList c).map (fun p : ℕ => [(p : ℤ)])
  have hcf_irr : ∀ q ∈ contentFactors, Irreducible (coeffsToPoly q) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simpa [coeffsToPoly] using irreducible_C_natPrime (hc_primes p hp)
  have hcf_prod : (contentFactors.map coeffsToPoly).prod = Polynomial.C (c : ℤ) := by
    dsimp [contentFactors]
    rw [List.map_map]
    have hmap_C : ∀ ps : List ℕ,
        (ps.map (coeffsToPoly ∘ fun p : ℕ => [(p : ℤ)])).prod = Polynomial.C (ps.prod : ℤ) := by
      intro ps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp [Function.comp_apply, coeffsToPoly, ih, Nat.cast_mul, map_mul]
    rw [hmap_C, hc_prod]
  set rawPrim := cs'.map (· / (c : ℤ))
  set primCs := coeffsTrim rawPrim
  have hcZ_ne0 : (c : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hc_ne0
  have hscale_prim : coeffsToPoly cs = Polynomial.C (c : ℤ) * coeffsToPoly primCs := by
    rw [coeffsToPoly_trim, ← coeffsToPoly_scale, ← coeffsToPoly_trim cs]
    congr 1
    dsimp [rawPrim, coeffsScale, cs']
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.getElem_map, Function.comp_apply]
    have hdvd : (c : ℤ) ∣ (coeffsTrim cs)[i] :=
      coeffsNatGcd_dvd_all (coeffsTrim cs) _ (List.getElem_mem hi1)
    exact (Int.mul_ediv_cancel' hdvd).symm
  have hprim_ne0 : coeffsToPoly primCs ≠ 0 :=
    fun hz => hf0 (by rw [hscale_prim, hz, mul_zero])
  have hprim_isPrim : (coeffsToPoly primCs).IsPrimitive := by
    intro r hr
    obtain ⟨q, hq⟩ := hr
    have hdvd_c : c * r.natAbs ∣ c := by
      apply dvd_coeffsNatGcd cs'
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hci := congrArg (fun p : ℤ[X] => p.coeff i)
        (by rw [hscale_prim, hq] : coeffsToPoly cs = Polynomial.C (c : ℤ) * (Polynomial.C r * q))
      rw [← coeffsToPoly_trim cs, coeffsToPoly_coeff] at hci
      have hi' : i < (coeffsTrim cs).length := hi
      rw [List.getD_eq_getElem _ _ hi', ← mul_assoc, ← Polynomial.C_mul,
        Polynomial.coeff_C_mul] at hci
      have habs_dvd : ((c * r.natAbs : ℕ) : ℤ) ∣ (c : ℤ) * r * q.coeff i := by
        rw [Nat.cast_mul]
        exact dvd_trans (mul_dvd_mul_left (c : ℤ) (Int.natAbs_dvd.mpr dvd_rfl))
          (dvd_mul_right ((c : ℤ) * r) (q.coeff i))
      exact hci ▸ habs_dvd
    have hr1 : r.natAbs = 1 := by
      obtain ⟨k, hk⟩ := hdvd_c
      have hpos : 0 < c := Nat.pos_of_ne_zero hc_ne0
      have hrk1 : r.natAbs * k = 1 := by nlinarith
      exact Nat.eq_one_of_mul_eq_one_right hrk1
    exact Int.isUnit_iff_natAbs_eq.mpr hr1
  have hprimCs_ne : primCs ≠ [] := by
    intro hz
    apply hprim_ne0
    rw [coeffsToPoly_trim]
    exact (coeffsTrim_eq_nil_iff rawPrim).mp hz
  by_cases hle1 : primCs.length ≤ 1
  · simp only [hle1, ↓reduceIte]
    have hprim_len1 : primCs.length = 1 := by
      have hpos := List.length_pos_of_ne_nil hprimCs_ne
      omega
    obtain ⟨u, hu_eq⟩ := List.length_eq_one_iff.mp hprim_len1
    have hprim_poly : coeffsToPoly primCs = Polynomial.C u := by
      rw [hu_eq]
      simp [coeffsToPoly]
    have hu_unit : IsUnit u := by
      exact hprim_isPrim u ⟨1, by rw [hprim_poly, mul_one]⟩
    have hu_pm : u = 1 ∨ u = -1 := Int.isUnit_iff.mp hu_unit
    have hhead : primCs.headD 1 = u := by rw [hu_eq]; rfl
    rw [hhead]
    cases hcf : contentFactors with
    | nil =>
      refine ⟨u, [], rfl, hu_pm, by simp, ?_, ?_⟩
      · simp [hscale_prim, hprim_poly, ← hcf_prod, hcf]
      · intro hnot_unit
        exfalso
        apply hnot_unit
        have hc1 : Polynomial.C (c : ℤ) = (1 : ℤ[X]) := by
          rw [← hcf_prod, hcf]
          simp
        rw [hscale_prim, hc1, one_mul, hprim_poly]
        exact hu_unit.map Polynomial.C
    | cons f0 fs =>
      refine ⟨1, coeffsScale u f0 :: fs, rfl, Or.inl rfl, ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · rw [coeffsToPoly_scale]
          have hf0_irr : Irreducible (coeffsToPoly f0) :=
            hcf_irr f0 (hcf ▸ List.mem_cons_self)
          have hass : Associated (coeffsToPoly f0) (Polynomial.C u * coeffsToPoly f0) :=
            ⟨(hu_unit.map Polynomial.C).unit, by simp [mul_comm]⟩
          exact hass.irreducible hf0_irr
        · exact hcf_irr q (hcf ▸ List.mem_cons_of_mem f0 hmem)
      · have hprod_cf : Polynomial.C (c : ℤ) =
            coeffsToPoly f0 * (fs.map coeffsToPoly).prod := by
          rw [← hcf_prod, hcf, List.map_cons, List.prod_cons]
        simp only [map_one, one_mul, List.map_cons, List.prod_cons, coeffsToPoly_scale]
        rw [hscale_prim, hprim_poly, hprod_cf]
        ring
      · intro _
        refine ⟨rfl, List.cons_ne_nil _ _, ?_⟩
        have hprod_cf : Polynomial.C (c : ℤ) =
            coeffsToPoly f0 * (fs.map coeffsToPoly).prod := by
          rw [← hcf_prod, hcf, List.map_cons, List.prod_cons]
        simp only [List.map_cons, List.prod_cons, coeffsToPoly_scale]
        rw [hscale_prim, hprim_poly, hprod_cf]
        ring
  · simp only [hle1, ↓reduceIte]
    have hge2 : 2 ≤ (coeffsTrim primCs).length := by
      dsimp [primCs] at hle1 ⊢
      rw [coeffsTrim_idem]
      omega
    have hlen_self : (coeffsTrim primCs).length ≤ primCs.length := by
      dsimp [primCs]; rw [coeffsTrim_idem]
    obtain ⟨hpf_ne, hpf_irr, hpf_prod⟩ :=
      kroneckerFactorPrimAux_spec primCs.length primCs hge2 hlen_self hprim_isPrim
    refine ⟨1, contentFactors ++ kroneckerFactorPrimAux primCs.length primCs, rfl, Or.inl rfl,
      ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hqc | hqp
      · exact hcf_irr q hqc
      · exact hpf_irr q hqp
    · simp only [map_one, one_mul, List.map_append, List.prod_append]
      rw [hcf_prod, hpf_prod, ← hscale_prim]
    · intro _
      refine ⟨rfl, List.append_ne_nil_of_right_ne_nil _ hpf_ne, ?_⟩
      rw [List.map_append, List.prod_append, hcf_prod, hpf_prod, ← hscale_prim]

/-- Kronecker factorization map on `ℤ[X]` induced by the computable `kroneckerProgramme` (§5.1,
pp. 49–50). -/
noncomputable def kroneckerFactorWithUnit (f : ℤ[X]) : ℤ × List ℤ[X] :=
  match kroneckerProgramme (polyToCoeffs f) with
  | none => (0, [])
  | some (u, L) => (u, L.map coeffsToPoly)

/-- Kronecker irreducible-factor list on non-zero non-units of `ℤ[X]` (§5.1, pp. 49–50). -/
noncomputable def kroneckerFactorList (f : ℤ[X]) : List ℤ[X] :=
  (kroneckerFactorWithUnit f).2

/-- **Theorem 5.1 (with unit prefix for all non-zero polynomials)** (§5.1, printed p. 49):
Every non-zero polynomial `f ∈ ℤ[X]` is factored by Kronecker's algorithm `kroneckerFactorWithUnit`
as `f = C u * L.prod` with `u ∈ {1, -1}` and every `p ∈ L` irreducible in `ℤ[X]`. -/
theorem theorem_5_1_with_unit {f : ℤ[X]} (hf0 : f ≠ 0) :
    let (u, L) := kroneckerFactorWithUnit f
    (u = 1 ∨ u = -1) ∧
    (∀ p ∈ L, Irreducible p ∧ IsGarlingIrreducible p) ∧
    Polynomial.C u * L.prod = f := by
  have hpoly : coeffsToPoly (polyToCoeffs f) = f := (coeffsToPoly_polyToCoeffs f).1
  have hne0 : coeffsToPoly (polyToCoeffs f) ≠ 0 := by rwa [hpoly]
  obtain ⟨u, Lc, hprog, hu, hirr, hprod, _⟩ := (exercise_5_1 (polyToCoeffs f)).2 hne0
  unfold kroneckerFactorWithUnit
  rw [hprog]
  refine ⟨hu, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqi := hirr q hq
    exact ⟨hqi, (isGarlingIrreducible_iff _).mpr hqi⟩
  · rwa [hpoly] at hprod

/-- **Theorem 5.1 (Kronecker's factorization algorithm on non-zero non-units)** (§5.1, printed
pp. 49–50): Every non-zero non-unit element `f ∈ ℤ[X]` is expressed by Kronecker's Lagrange
interpolation algorithm (`kroneckerFactorList`) as a non-empty product of irreducible factors in
`ℤ[X]`. (See `theorem_5_1_zero_counterexample`, `theorem_5_1_unit_counterexample`, and `QUEUE.md`
for the literal `"any element"` edge cases `0` and units.) -/
theorem theorem_5_1 {f : ℤ[X]} (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    kroneckerFactorList f ≠ [] ∧
    (∀ p ∈ kroneckerFactorList f, Irreducible p ∧ IsGarlingIrreducible p) ∧
    (kroneckerFactorList f).prod = f := by
  have hpoly : coeffsToPoly (polyToCoeffs f) = f := (coeffsToPoly_polyToCoeffs f).1
  have hne0 : coeffsToPoly (polyToCoeffs f) ≠ 0 := by rwa [hpoly]
  have hnu : ¬ IsUnit (coeffsToPoly (polyToCoeffs f)) := by rwa [hpoly]
  obtain ⟨_, Lc, hprog, _, hirr, _, hnonunit⟩ := (exercise_5_1 (polyToCoeffs f)).2 hne0
  obtain ⟨_, hLc_ne, hprod1⟩ := hnonunit hnu
  unfold kroneckerFactorList kroneckerFactorWithUnit
  rw [hprog]
  simp only []
  refine ⟨by simpa using hLc_ne, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqi := hirr q hq
    exact ⟨hqi, (isGarlingIrreducible_iff _).mpr hqi⟩
  · rwa [hpoly] at hprod1

/-! #### Exercise 5.2: Explicit upper bound on Kronecker irreducibility-test calculations -/

/-- Closed-form elementary upper bound in terms of `n = deg f` and `K = max_i |a_i|` for the number
of candidate checks performed by Kronecker's irreducibility decision procedure (§5.1, Ex. 5.2,
printed p. 50). -/
def kroneckerCalcBound (n K : ℕ) : ℕ :=
  K + (n / 2 + 1) + 1 + (2 * K * (n + 1) ^ (n + 1)) ^ (n / 2 + 1)

/-- Computable step-counting Kronecker irreducibility decision procedure on `List ℤ`: returns
`(isIrred, steps)` where `isIrred` decides irreducibility in `ℤ[X]` and `steps` counts the divisor,
evaluation, and Lagrange-interpolant candidate tests performed. -/
def kroneckerIsIrreducibleWithSteps (cs : List ℤ) : Bool × ℕ :=
  let cs' := coeffsTrim cs
  match cs' with
  | [] => (false, 1)
  | [a0] =>
    let K := a0.natAbs
    let hasProperDiv := ((List.range K).filter (fun d => 2 ≤ d)).any (fun d => d ∣ K)
    (decide (2 ≤ K) && !hasProperDiv, K)
  | _ :: _ :: [] =>
    (coeffsNatGcd cs' == 1, 1)
  | _ =>
    if coeffsNatGcd cs' != 1 then (false, 1)
    else
      let n := cs'.length - 1
      let r := n / 2
      let pts := List.range (r + 1)
      if pts.any (fun j : ℕ => coeffsEval cs' (j : ℤ) == 0) then
        (false, 1 + (r + 1))
      else
        let divLists := pts.map (fun j : ℕ => intDivisorsList (coeffsEval cs' (j : ℤ)))
        let tuples := cartesianTuples divLists
        let foundFactor := tuples.any fun t =>
          match lagrangeInterpCoeffs? r t with
          | some g =>
            if 2 ≤ g.length ∧ g.length ≤ r + 1 then
              (coeffsDivExact? cs' g).isSome
            else false
          | none => false
        (!foundFactor, 1 + (r + 1) + tuples.length)

private theorem eval_natAbs_le_of_coeff_le {f : ℤ[X]} {n K : ℕ}
    (hdeg : f.natDegree ≤ n) (hK : ∀ i ≤ n, (f.coeff i).natAbs ≤ K)
    {j : ℕ} (hj : j ≤ n) :
    (f.eval (j : ℤ)).natAbs ≤ K * (n + 1) ^ (n + 1) := by
  have heval_sum : f.eval (j : ℤ) = ∑ i ∈ Finset.range (n + 1), f.coeff i * (j : ℤ) ^ i := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  have htri : ∀ s : Finset ℕ,
      (∑ i ∈ s, f.coeff i * (j : ℤ) ^ i).natAbs ≤
        ∑ i ∈ s, (f.coeff i * (j : ℤ) ^ i).natAbs := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)
  rw [heval_sum]
  calc (∑ i ∈ Finset.range (n + 1), f.coeff i * (j : ℤ) ^ i).natAbs
    _ ≤ ∑ i ∈ Finset.range (n + 1), (f.coeff i * (j : ℤ) ^ i).natAbs := htri _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), K * (n + 1) ^ n := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have hj_lt : j ≤ n + 1 := by omega
      have hpow : j ^ i ≤ (n + 1) ^ n :=
        calc j ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left hj_lt i
          _ ≤ (n + 1) ^ n := Nat.pow_le_pow_right (by omega) hi_le
      exact Nat.mul_le_mul (hK i hi_le) hpow
    _ = (n + 1) * (K * (n + 1) ^ n) := by simp
    _ = K * (n + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- **Exercise 5.2** (§5.1, printed p. 50):
Suppose that `f = a_0 + ⋯ + a_n x^n ∈ ℤ[X]` is non-zero of degree `n` (`garlingDegree f hf = n`)
and `max_{0 ≤ i ≤ n} |a_i| = K`. Then the computable Kronecker irreducibility procedure
`kroneckerIsIrreducibleWithSteps (polyToCoeffs f)`:
1. decides irreducibility of `f` in `ℤ[X]` (`fst = true ↔ Irreducible f`), and
2. performs at most `kroneckerCalcBound n K = K + (n/2 + 1) + 1 + (2 K (n + 1)^(n + 1))^(n/2 + 1)`
   candidate/divisor tests (`snd ≤ kroneckerCalcBound n K`). -/
theorem exercise_5_2 {f : ℤ[X]} (hf : f ≠ 0) {n K : ℕ}
    (hdeg : garlingDegree f hf = n)
    (hK_ge : ∀ i ≤ n, (f.coeff i).natAbs ≤ K)
    (hK_mem : ∃ i ≤ n, (f.coeff i).natAbs = K) :
    let res := kroneckerIsIrreducibleWithSteps (polyToCoeffs f)
    (res.1 = true ↔ Irreducible f) ∧
    res.2 ≤ kroneckerCalcBound n K := by
  have hn_eq : f.natDegree = n := hdeg
  obtain ⟨hpoly_eq, htrim_eq⟩ := coeffsToPoly_polyToCoeffs f
  have hcs_ne : polyToCoeffs f ≠ [] := by
    intro hnil
    apply hf
    rw [← hpoly_eq, hnil]
    rfl
  have hcs_len : (polyToCoeffs f).length = n + 1 := by
    simp [polyToCoeffs, hf, hn_eq]
  dsimp only []
  unfold kroneckerIsIrreducibleWithSteps
  rw [htrim_eq]
  dsimp only []
  rcases hcs : polyToCoeffs f with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
  · exact absurd hcs hcs_ne
  · dsimp only []
    have hn0 : n = 0 := by rw [hcs] at hcs_len; simpa using hcs_len
    subst hn0
    have hf_eq : f = Polynomial.C a0 := by
      rw [← hpoly_eq, hcs]
      simp [coeffsToPoly]
    have ha0_coeff : f.coeff 0 = a0 := by simp [hf_eq]
    have hK_eq : K = a0.natAbs := by
      obtain ⟨i, hi, rfl⟩ := hK_mem
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      rw [ha0_coeff]
    subst hK_eq
    refine ⟨?_, ?_⟩
    · rw [hf_eq, corollary_gauss_lemma ℚ (Polynomial.C a0)]
      have hnot_prim_rat : ¬ (IsGarlingPrimitive (Polynomial.C a0) ∧
          Irreducible ((Polynomial.C a0).map (algebraMap ℤ ℚ))) := by
        rintro ⟨_, hirrQ⟩
        rw [Polynomial.map_C] at hirrQ
        have ha0_ne : (a0 : ℚ) ≠ 0 := by
          intro hz
          apply hf
          rw [hf_eq, show a0 = 0 by exact_mod_cast hz, map_zero]
        exact hirrQ.not_isUnit ((isUnit_iff_ne_zero.mpr ha0_ne).map Polynomial.C)
      simp only [hnot_prim_rat, or_false]
      have hprime_iff : (∃ a : ℤ, Irreducible a ∧ (Polynomial.C a0 : ℤ[X]) = Polynomial.C a) ↔
          Nat.Prime a0.natAbs := by
        constructor
        · rintro ⟨a, ha_irr, heq⟩
          have ha_eq : a0 = a := Polynomial.C_injective heq
          subst ha_eq
          exact (int_irreducible_iff_natAbs_prime a0).mp ha_irr
        · intro hp
          exact ⟨a0, (int_irreducible_iff_natAbs_prime a0).mpr hp, rfl⟩
      rw [hprime_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        List.any_eq_false, List.mem_filter, List.mem_range]
      constructor
      · rintro ⟨hge2, hnodiv⟩
        rw [Nat.prime_def_lt']
        exact ⟨hge2, fun m hm2 hmlt hmdvd => hnodiv m ⟨hmlt, hm2⟩ hmdvd⟩
      · intro hp
        rw [Nat.prime_def_lt'] at hp
        exact ⟨hp.1, fun m ⟨hmlt, hm2⟩ => hp.2 m hm2 hmlt⟩
    · unfold kroneckerCalcBound
      omega
  · dsimp only []
    have hn1 : n = 1 := by rw [hcs] at hcs_len; simp at hcs_len; omega
    subst hn1
    have hf_poly : coeffsToPoly [a0, a1] = f := hcs ▸ hpoly_eq
    refine ⟨?_, ?_⟩
    · rw [beq_iff_eq, coeffsNatGcd_eq_one_iff_isPrimitive, hf_poly]
      constructor
      · intro hprim
        refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
        · have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
          omega
        · have hg0 : g ≠ 0 := fun hz => hf (by rw [hgh, hz, zero_mul])
          have hh0 : h ≠ 0 := fun hz => hf (by rw [hgh, hz, mul_zero])
          have hsum : g.natDegree + h.natDegree = 1 := by
            rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hn_eq]
          rcases (show g.natDegree = 0 ∨ h.natDegree = 0 by omega) with hgd | hhd
          · left
            have hgC := Polynomial.eq_C_of_natDegree_eq_zero hgd
            exact hgC ▸ (hprim (g.coeff 0) ⟨h, by rw [← hgC, hgh]⟩).map Polynomial.C
          · right
            have hhC := Polynomial.eq_C_of_natDegree_eq_zero hhd
            exact hhC ▸ (hprim (h.coeff 0) ⟨g, by rw [← hhC, mul_comm, hgh]⟩).map Polynomial.C
      · intro hirr
        rcases (corollary_gauss_lemma ℚ f).mp hirr with ⟨a, _, hfC⟩ | ⟨hprim, _⟩
        · have hd0 : f.natDegree = 0 := by rw [hfC, Polynomial.natDegree_C]
          omega
        · exact (isGarlingPrimitive_iff f).mp hprim
    · unfold kroneckerCalcBound
      omega
  · dsimp only []
    set cs3 := a0 :: a1 :: a2 :: rest
    have hcs3_poly : coeffsToPoly cs3 = f := hcs ▸ hpoly_eq
    have hcs3_trim : coeffsTrim cs3 = cs3 := by
      have ht := htrim_eq
      rwa [hcs] at ht
    have hn_ge2 : 2 ≤ n := by
      rw [hcs] at hcs_len
      simp [cs3] at hcs_len
      omega
    have hlen_sub1 : cs3.length - 1 = n := by
      rw [hcs] at hcs_len
      omega
    by_cases hgcd : (coeffsNatGcd cs3 != 1) = true
    · simp only [hgcd, ↓reduceIte]
      refine ⟨?_, by unfold kroneckerCalcBound; omega⟩
      simp only [Bool.false_eq_true, false_iff]
      intro hirr
      have hne1 : ¬ f.IsPrimitive := by
        rw [← hcs3_poly, ← coeffsNatGcd_eq_one_iff_isPrimitive]
        simpa [bne_iff_ne] using hgcd
      rcases (corollary_gauss_lemma ℚ f).mp hirr with ⟨a, _, hfC⟩ | ⟨hprim, _⟩
      · have hd0 : f.natDegree = 0 := by rw [hfC, Polynomial.natDegree_C]
        omega
      · exact hne1 ((isGarlingPrimitive_iff f).mp hprim)
    · simp only [hgcd, Bool.false_eq_true, ↓reduceIte]
      rw [hlen_sub1]
      have hgcd_eq1 : coeffsNatGcd cs3 = 1 := by
        revert hgcd
        simp [bne_iff_ne]
      have hprim : f.IsPrimitive := by
        rwa [← hcs3_poly, ← coeffsNatGcd_eq_one_iff_isPrimitive]
      set r := n / 2
      set pts := List.range (r + 1)
      by_cases hroot_any : pts.any (fun j : ℕ => coeffsEval cs3 (j : ℤ) == 0) = true
      · simp only [hroot_any, ↓reduceIte]
        refine ⟨?_, by unfold kroneckerCalcBound; omega⟩
        simp only [Bool.false_eq_true, false_iff]
        intro hirr
        obtain ⟨j, _, hj_zero⟩ := List.any_eq_true.mp hroot_any
        rw [beq_iff_eq, coeffsEval_eq, hcs3_poly] at hj_zero
        obtain ⟨q, hfq⟩ := Polynomial.dvd_iff_isRoot.mpr hj_zero
        have hlin_not_unit : ¬ IsUnit (Polynomial.X - Polynomial.C (j : ℤ)) := by
          intro hu
          have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
          have hd1 : (Polynomial.X - Polynomial.C (j : ℤ)).natDegree = 1 := by compute_degree!
          omega
        have hq_ne0 : q ≠ 0 := fun hz => hf (by rw [hfq, hz, mul_zero])
        have hq_not_unit : ¬ IsUnit q := by
          intro hu
          have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
          have hdeg_f := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero (j : ℤ)) hq_ne0
          have hd1 : (Polynomial.X - Polynomial.C (j : ℤ)).natDegree = 1 := by compute_degree!
          rw [← hfq, hn_eq, hd1, hd0] at hdeg_f
          omega
        rcases hirr.isUnit_or_isUnit hfq with hu1 | hu2
        · exact hlin_not_unit hu1
        · exact hq_not_unit hu2
      · simp only [hroot_any, Bool.false_eq_true, ↓reduceIte]
        have hroot_false : pts.any (fun j : ℕ => coeffsEval cs3 (j : ℤ) == 0) = false :=
          Bool.eq_false_iff.mpr hroot_any
        let divLists := pts.map (fun j : ℕ => intDivisorsList (coeffsEval cs3 (j : ℤ)))
        let tuples := cartesianTuples divLists
        have hfind_none : pts.find? (fun j : ℕ => coeffsEval cs3 (j : ℤ) == 0) = none := by
          rw [List.find?_eq_none]
          intro j hj hsat
          have hany : pts.any (fun k : ℕ => coeffsEval cs3 (k : ℤ) == 0) = true :=
            List.any_eq_true.mpr ⟨j, hj, hsat⟩
          rw [hroot_false] at hany
          cases hany
        have hiff_find :
            (tuples.any fun t =>
              match lagrangeInterpCoeffs? r t with
              | some g =>
                if 2 ≤ g.length ∧ g.length ≤ r + 1 then (coeffsDivExact? cs3 g).isSome
                else false
              | none => false) = false ↔
            kroneckerFindProperFactor cs3 = none := by
          unfold kroneckerFindProperFactor
          have hnot_lt3 : ¬ cs3.length < 3 := by simp [cs3]
          simp only [hcs3_trim, hnot_lt3, ↓reduceIte, hlen_sub1]
          change _ ↔
            (match pts.find? (fun j : ℕ => coeffsEval cs3 (j : ℤ) == 0) with
              | some j => _
              | none => _) = none
          rw [hfind_none]
          simp only [List.any_eq_false, List.findSome?_eq_none_iff]
          refine forall₂_congr fun t _ => ?_
          cases lagrangeInterpCoeffs? r t with
          | none => simp
          | some g =>
            dsimp only [r]
            by_cases hgl : 2 ≤ g.length ∧ g.length ≤ n / 2 + 1
            · simp only [hgl, and_self, ↓reduceIte]
              cases coeffsDivExact? cs3 g <;> simp
            · simp [hgl]
        refine ⟨?_, ?_⟩
        · rw [Bool.not_eq_true', hiff_find]
          constructor
          · intro hnone
            exact hcs3_poly ▸ kroneckerFindProperFactor_eq_none_irreducible
              (hcs3_poly.symm ▸ hprim) (by rw [hcs3_poly, hn_eq]; omega) hnone
          · intro hirr
            by_contra hsome
            obtain ⟨⟨g, q⟩, hgq⟩ := Option.ne_none_iff_exists'.mp hsome
            obtain ⟨hg_trim, hq_trim, hg_ge2, _, hq_ge2, _, hmul⟩ :=
              kroneckerFindProperFactor_sound hgq
            rw [hcs3_poly] at hmul
            have hg_ne0 : coeffsToPoly g ≠ 0 :=
              fun hz => hf (by rw [hmul, hz, zero_mul])
            have hq_ne0 : coeffsToPoly q ≠ 0 :=
              fun hz => hf (by rw [hmul, hz, mul_zero])
            have hg_nu : ¬ IsUnit (coeffsToPoly g) := by
              intro hu
              have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
              have hne : coeffsTrim g ≠ [] := fun hnil => hg_ne0 ((coeffsTrim_eq_nil_iff g).mp hnil)
              have hl := coeffsTrim_length_eq_natDegree_succ hne
              rw [← hg_trim, hd0] at hl
              omega
            have hq_nu : ¬ IsUnit (coeffsToPoly q) := by
              intro hu
              have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
              have hne : coeffsTrim q ≠ [] := fun hnil => hq_ne0 ((coeffsTrim_eq_nil_iff q).mp hnil)
              have hl := coeffsTrim_length_eq_natDegree_succ hne
              rw [← hq_trim, hd0] at hl
              omega
            rcases hirr.isUnit_or_isUnit hmul with hug | huq
            · exact hg_nu hug
            · exact hq_nu huq
        · unfold kroneckerCalcBound
          have htuples_len : tuples.length ≤ (2 * K * (n + 1) ^ (n + 1)) ^ (r + 1) := by
            dsimp [tuples, divLists]
            rw [cartesianTuples_length, List.map_map]
            have hprod_le : ∀ (L : List ℕ) (B : ℕ),
                (∀ j ∈ L, ((intDivisorsList (coeffsEval cs3 (j : ℤ))).length) ≤ B) →
                (L.map (List.length ∘ fun j : ℕ => intDivisorsList (coeffsEval cs3 (j : ℤ)))).prod ≤
                  B ^ L.length := by
              intro L B hLB
              induction L with
              | nil => simp
              | cons j js ih =>
                simp only [List.map_cons, List.prod_cons, Function.comp_apply, List.length_cons, pow_succ']
                exact Nat.mul_le_mul (hLB j List.mem_cons_self)
                  (ih fun i hi => hLB i (List.mem_cons_of_mem j hi))
            have hlen_pts : pts.length = r + 1 := by simp [pts]
            rw [← hlen_pts]
            apply hprod_le
            intro j hj
            have hj_le_r : j ≤ r := by
              have hlt := List.mem_range.mp hj
              omega
            have hj_le_n : j ≤ n := by omega
            rw [coeffsEval_eq, hcs3_poly]
            calc (intDivisorsList (f.eval (j : ℤ))).length
              _ ≤ 2 * (f.eval (j : ℤ)).natAbs := intDivisorsList_length_le _
              _ ≤ 2 * (K * (n + 1) ^ (n + 1)) :=
                Nat.mul_le_mul_left 2 (eval_natAbs_le_of_coeff_le (le_of_eq hn_eq) hK_ge hj_le_n)
              _ = 2 * K * (n + 1) ^ (n + 1) := by ring
          change 1 + (r + 1) + tuples.length ≤ _
          dsimp only [r] at htuples_len ⊢
          omega

/-! #### Exercise 5.3: Factorization algorithm over finite fields -/

/-- **Exercise 5.3 — Zero counterexample to literal `"any element"`** (§5.1, p. 50):
For every finite field `K`, `0 ∈ K[X]` cannot be expressed as a product of irreducible factors
(even up to a unit factor). -/
theorem exercise_5_3_zero_counterexample (K : Type*) [Field K] [Finite K] :
    (¬ ∃ L : List K[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = 0) ∧
    (¬ ∃ (u : K[X]) (L : List K[X]), IsUnit u ∧ (∀ p ∈ L, Irreducible p) ∧ u * L.prod = 0) :=
  zero_not_prod_irreducibles

/-- **Exercise 5.3 — Unit counterexamples to literal `"any element"`** (§5.1, p. 50):
Over `ℤ_3 = ZMod 3`, the non-one constant unit `2 ∈ ℤ_3[X]` cannot be expressed as a (possibly
empty) product of irreducible factors; and over every finite field `K`, `1 ∈ K[X]` cannot be
expressed as a non-empty product of irreducible factors. -/
theorem exercise_5_3_unit_counterexample :
    IsUnit (Polynomial.C (2 : ZMod 3)) ∧
    (¬ ∃ L : List (ZMod 3)[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = Polynomial.C (2 : ZMod 3)) ∧
    (∀ (K : Type) [Field K] [Finite K],
      ¬ ∃ L : List K[X], L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = 1) := by
  have h2ne0 : (2 : ZMod 3) ≠ 0 := by decide
  have h2ne1 : (2 : ZMod 3) ≠ 1 := by decide
  have hu2 : IsUnit (Polynomial.C (2 : ZMod 3)) := (isUnit_iff_ne_zero.mpr h2ne0).map Polynomial.C
  refine ⟨hu2, ?_, ?_⟩
  · rintro ⟨L, hL, hprod⟩
    cases L with
    | nil =>
      have hc := congrArg (fun p : (ZMod 3)[X] => p.coeff 0) hprod
      simp at hc
      exact h2ne1 hc.symm
    | cons p ps =>
      rw [List.prod_cons] at hprod
      exact (hL p List.mem_cons_self).not_isUnit (isUnit_of_dvd_unit ⟨ps.prod, hprod.symm⟩ hu2)
  · intro K _ _ ⟨L, hne, hL, hprod⟩
    cases L with
    | nil => exact hne rfl
    | cons p ps =>
      rw [List.prod_cons] at hprod
      exact (hL p List.mem_cons_self).not_isUnit (isUnit_of_dvd_one ⟨ps.prod, hprod.symm⟩)

/-- **Exercise 5.3 — Exact characterization in `K[X]`** (§5.1, p. 50). -/
theorem exercise_5_3_iff {K : Type*} [Field K] (f : K[X]) :
    ((∃ L : List K[X], (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ f = 1 ∨ (f ≠ 0 ∧ ¬ IsUnit f)) ∧
    ((∃ L : List K[X], L ≠ [] ∧ (∀ p ∈ L, Irreducible p) ∧ L.prod = f) ↔ (f ≠ 0 ∧ ¬ IsUnit f)) :=
  exists_prod_irreducibles_iff f

section FiniteFieldFactorization

open Classical

/-- Explicit finite enumeration of all polynomials in `K[X]` of degree `≤ d` over a finite field
`K` (`card = |K|^(d + 1)`), providing the finite search space for Exercise 5.3 (§5.1, p. 50). -/
noncomputable def polysBoundedDegree (K : Type*) [Semiring K] [Fintype K] : ℕ → Finset K[X]
  | 0 => Finset.univ.image Polynomial.C
  | d + 1 =>
    (Finset.univ ×ˢ polysBoundedDegree K d).image fun ap => Polynomial.C ap.1 + Polynomial.X * ap.2

theorem mem_polysBoundedDegree_iff (K : Type*) [Semiring K] [Fintype K] (d : ℕ) (p : K[X]) :
    p ∈ polysBoundedDegree K d ↔ p.natDegree ≤ d := by
  induction d generalizing p with
  | zero =>
    unfold polysBoundedDegree
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Nat.le_zero]
    constructor
    · rintro ⟨a, rfl⟩
      exact Polynomial.natDegree_C a
    · intro hd0
      exact ⟨p.coeff 0, (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩
  | succ d ih =>
    unfold polysBoundedDegree
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨a, q, hq, rfl⟩
      have hqd : q.natDegree ≤ d := (ih q).mp hq
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      by_cases hq0 : q = 0
      · simp [hq0]
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have hX : (Polynomial.X : K[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
        omega
    · intro hpd
      let q : K[X] := ∑ i ∈ Finset.range (d + 1), Polynomial.C (p.coeff (i + 1)) * Polynomial.X ^ i
      have hq_coeff : ∀ k : ℕ, q.coeff k = if k ≤ d then p.coeff (k + 1) else 0 := by
        intro k
        dsimp [q]
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
        by_cases hk : k ≤ d
        · have hlt : k < d + 1 := by omega
          simp [hk, hlt]
        · have hlt : ¬ k < d + 1 := by omega
          simp [hk, hlt]
      have hq_deg : q.natDegree ≤ d := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hq_coeff]
        simp [show ¬ N ≤ d by omega]
      refine ⟨p.coeff 0, q, (ih q).mpr hq_deg, ?_⟩
      ext k
      cases k with
      | zero => simp
      | succ m =>
        simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add,
          Polynomial.coeff_X_mul, hq_coeff]
        by_cases hm : m ≤ d
        · simp [hm]
        · simp only [hm, ↓reduceIte]
          exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem card_polysBoundedDegree (K : Type*) [Semiring K] [Fintype K] (d : ℕ) :
    (polysBoundedDegree K d).card = Fintype.card K ^ (d + 1) := by
  induction d with
  | zero =>
    unfold polysBoundedDegree
    rw [Finset.card_image_of_injective _ Polynomial.C_injective, Finset.card_univ, pow_one]
  | succ d ih =>
    unfold polysBoundedDegree
    have hinj : Function.Injective (fun ap : K × K[X] => Polynomial.C ap.1 + Polynomial.X * ap.2) := by
      rintro ⟨a1, p1⟩ ⟨a2, p2⟩ heq
      have hc0 := congrArg (fun f : K[X] => f.coeff 0) heq
      simp at hc0
      subst hc0
      have hp_eq : p1 = p2 := by
        ext k
        have hck := congrArg (fun f : K[X] => f.coeff (k + 1)) heq
        simpa using hck
      subst hp_eq
      rfl
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ, ih]
    ring

/-- Explicit finite candidate set of monic proper divisors of degree `1 ≤ deg g ≤ r` over a finite
field `K`, tested via `Polynomial.modByMonic` (§5.1, Ex. 5.3, p. 50). -/
noncomputable def finiteFieldProperMonicDivisors {K : Type*} [Field K] [Fintype K] (m : K[X]) :
    Finset K[X] :=
  (polysBoundedDegree K (m.natDegree / 2)).filter fun g =>
    g.Monic ∧ 1 ≤ g.natDegree ∧ m %ₘ g = 0

/-- Step-bounded recursive factorization of a monic polynomial `m ∈ K[X]` of degree `≥ 1` over a
finite field `K`, searching `finiteFieldProperMonicDivisors m` (at most `|K|^(⌊deg m / 2⌋ + 1)`
polynomials per step) and recursing at most `deg m` times. -/
noncomputable def finiteFieldFactorMonicAux {K : Type*} [Field K] [Fintype K] :
    ℕ → K[X] → List K[X]
  | 0, _ => []
  | fuel + 1, m =>
    if m.natDegree ≤ 1 then [m]
    else
      let divs := finiteFieldProperMonicDivisors m
      if h : divs.Nonempty then
        let g := Classical.choose h
        let q := m /ₘ g
        finiteFieldFactorMonicAux fuel g ++ finiteFieldFactorMonicAux fuel q
      else [m]

theorem finiteFieldFactorMonicAux_spec {K : Type*} [Field K] [Fintype K] :
    ∀ (fuel : ℕ) (m : K[X]),
      m.Monic → 1 ≤ m.natDegree → m.natDegree ≤ fuel →
      finiteFieldFactorMonicAux fuel m ≠ [] ∧
      (∀ p ∈ finiteFieldFactorMonicAux fuel m, p.Monic ∧ Irreducible p) ∧
      (finiteFieldFactorMonicAux fuel m).prod = m := by
  intro fuel
  induction fuel with
  | zero =>
    intro m _ hge1 hle0
    omega
  | succ f ih =>
    intro m hmonic hge1 hle
    unfold finiteFieldFactorMonicAux
    by_cases hle1 : m.natDegree ≤ 1
    · simp only [hle1, ↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true, List.mem_singleton,
        forall_eq, List.prod_cons, List.prod_nil, mul_one, true_and, and_true]
      have hd1 : m.natDegree = 1 := by omega
      have hdeg1 : m.degree = 1 := by
        rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hd1]
        rfl
      exact ⟨hmonic, Polynomial.irreducible_of_degree_eq_one hdeg1⟩
    · simp only [hle1, ↓reduceIte]
      let divs := finiteFieldProperMonicDivisors m
      by_cases hne : divs.Nonempty
      · simp only [divs, hne, ↓reduceDIte]
        let g := Classical.choose hne
        have hg_mem : g ∈ finiteFieldProperMonicDivisors m := Classical.choose_spec hne
        unfold finiteFieldProperMonicDivisors at hg_mem
        simp only [Finset.mem_filter, mem_polysBoundedDegree_iff] at hg_mem
        rcases hg_mem with ⟨hg_le_r, hg_monic, hg_ge1, hmod0⟩
        let q := m /ₘ g
        have hmul : g * q = m := by
          have h := Polynomial.modByMonic_add_div m g
          rwa [hmod0, zero_add] at h
        have hq_ne0 : q ≠ 0 := fun hz => hmonic.ne_zero (by rw [← hmul, hz, mul_zero])
        have hq_monic : q.Monic := by
          have hlead : g.leadingCoeff * q.leadingCoeff = 1 := by
            rw [← Polynomial.leadingCoeff_mul, hmul, hmonic.leadingCoeff]
          rw [Polynomial.Monic]
          rw [hg_monic.leadingCoeff, one_mul] at hlead
          exact hlead
        have hdeg_sum : g.natDegree + q.natDegree = m.natDegree := by
          rw [← Polynomial.natDegree_mul hg_monic.ne_zero hq_ne0, hmul]
        have hg_le_f : g.natDegree ≤ f := by omega
        have hq_ge1 : 1 ≤ q.natDegree := by omega
        have hq_le_f : q.natDegree ≤ f := by omega
        obtain ⟨hg_ne, hg_irr, hg_prod⟩ := ih g hg_monic hg_ge1 hg_le_f
        obtain ⟨_, hq_irr, hq_prod⟩ := ih q hq_monic hq_ge1 hq_le_f
        refine ⟨List.append_ne_nil_of_left_ne_nil hg_ne _, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hpg | hpq
          · exact hg_irr p hpg
          · exact hq_irr p hpq
        · rw [List.prod_append, hg_prod, hq_prod, hmul]
      · simp only [divs, hne, ↓reduceDIte, ne_eq, List.cons_ne_nil, not_false_eq_true,
          List.mem_singleton, forall_eq, List.prod_cons, List.prod_nil, mul_one, true_and, and_true]
        refine ⟨hmonic, ⟨Polynomial.not_isUnit_of_natDegree_pos m (by omega), fun a b hab => ?_⟩⟩
        by_contra hboth
        push Not at hboth
        rcases hboth with ⟨hau, hbu⟩
        have ha0 : a ≠ 0 := fun hz => hmonic.ne_zero (by rw [hab, hz, zero_mul])
        have hb0 : b ≠ 0 := fun hz => hmonic.ne_zero (by rw [hab, hz, mul_zero])
        have ha_pos : 1 ≤ a.natDegree := by
          by_contra h0
          have hd0 : a.natDegree = 0 := by omega
          have haC := Polynomial.eq_C_of_natDegree_eq_zero hd0
          have hc0 : a.coeff 0 ≠ 0 := fun hz => ha0 (by rw [haC, hz, map_zero])
          exact hau (haC ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
        have hb_pos : 1 ≤ b.natDegree := by
          by_contra h0
          have hd0 : b.natDegree = 0 := by omega
          have hbC := Polynomial.eq_C_of_natDegree_eq_zero hd0
          have hc0 : b.coeff 0 ≠ 0 := fun hz => hb0 (by rw [hbC, hz, map_zero])
          exact hbu (hbC ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
        have hsum : a.natDegree + b.natDegree = m.natDegree := by
          rw [← Polynomial.natDegree_mul ha0 hb0, ← hab]
        obtain ⟨u, hu0, hu_pos, hu_le_r, hu_dvd⟩ :
            ∃ u : K[X], u ≠ 0 ∧ 1 ≤ u.natDegree ∧ u.natDegree ≤ m.natDegree / 2 ∧ u ∣ m := by
          by_cases hal : a.natDegree ≤ m.natDegree / 2
          · exact ⟨a, ha0, ha_pos, hal, ⟨b, hab⟩⟩
          · exact ⟨b, hb0, hb_pos, by omega, ⟨a, hab.trans (mul_comm a b)⟩⟩
        let g := Polynomial.C u.leadingCoeff⁻¹ * u
        have hlead_ne0 : u.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu0
        have hg_monic : g.Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            inv_mul_cancel₀ hlead_ne0]
        have hg_deg : g.natDegree = u.natDegree :=
          Polynomial.natDegree_C_mul (inv_ne_zero hlead_ne0)
        have hg_dvd : g ∣ m := by
          obtain ⟨v, huv⟩ := hu_dvd
          refine ⟨Polynomial.C u.leadingCoeff * v, ?_⟩
          dsimp [g]
          have h1 : Polynomial.C u.leadingCoeff⁻¹ * Polynomial.C u.leadingCoeff = (1 : K[X]) := by
            rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne0, map_one]
          calc m = 1 * (u * v) := by rw [one_mul, huv]
            _ = (Polynomial.C u.leadingCoeff⁻¹ * Polynomial.C u.leadingCoeff) * (u * v) := by rw [h1]
            _ = Polynomial.C u.leadingCoeff⁻¹ * u * (Polynomial.C u.leadingCoeff * v) := by ring
        have hg_mem : g ∈ divs := by
          dsimp [divs, finiteFieldProperMonicDivisors]
          simp only [Finset.mem_filter, mem_polysBoundedDegree_iff]
          exact ⟨hg_deg ▸ hu_le_r, hg_monic, hg_deg ▸ hu_pos,
            (Polynomial.modByMonic_eq_zero_iff_dvd hg_monic).mpr hg_dvd⟩
        exact hne ⟨g, hg_mem⟩

/-- Step-bounded factorization procedure over a finite field `K` (`Fintype K`) returning `(u, L)`
with `f = C u * L.prod` for `f ≠ 0`, and absorbing `u` into the first factor for `finiteFieldFactorList`
on non-zero non-units (§5.1, Ex. 5.3, p. 50). -/
noncomputable def finiteFieldFactorWithUnit {K : Type*} [Field K] [Fintype K] (f : K[X]) :
    K × List K[X] :=
  if f = 0 then (0, [])
  else if f.natDegree = 0 then (f.coeff 0, [])
  else
    let u := f.leadingCoeff
    let m := Polynomial.C u⁻¹ * f
    (u, finiteFieldFactorMonicAux m.natDegree m)

/-- Explicit irreducible-factor list over a finite field `K` for non-zero non-units `f ∈ K[X]`
(§5.1, Ex. 5.3, p. 50). -/
noncomputable def finiteFieldFactorList {K : Type*} [Field K] [Fintype K] (f : K[X]) :
    List K[X] :=
  let (u, L) := finiteFieldFactorWithUnit f
  match L with
  | [] => []
  | p :: ps => (Polynomial.C u * p) :: ps

/-- **Exercise 5.3 (with unit prefix for all non-zero polynomials)** (§5.1, printed p. 50):
Over a finite field `K`, every non-zero polynomial `f ∈ K[X]` is factored by
`finiteFieldFactorWithUnit f = (u, L)` into `u ∈ Kˣ` and monic irreducibles `L` with
`C u * L.prod = f`, testing at most `|K|^(⌊deg / 2⌋ + 1)` candidate divisors per step. -/
theorem exercise_5_3_with_unit {K : Type*} [Field K] [Fintype K] {f : K[X]} (hf0 : f ≠ 0) :
    let (u, L) := finiteFieldFactorWithUnit f
    u ≠ 0 ∧
    (∀ p ∈ L, p.Monic ∧ Irreducible p ∧ IsGarlingIrreducible p) ∧
    Polynomial.C u * L.prod = f ∧
    (finiteFieldProperMonicDivisors f).card ≤ Fintype.card K ^ (f.natDegree / 2 + 1) := by
  have hcard : (finiteFieldProperMonicDivisors f).card ≤ Fintype.card K ^ (f.natDegree / 2 + 1) := by
    unfold finiteFieldProperMonicDivisors
    exact le_trans (Finset.card_filter_le _ _) (le_of_eq (card_polysBoundedDegree K (f.natDegree / 2)))
  dsimp only []
  unfold finiteFieldFactorWithUnit
  simp only [hf0, ↓reduceIte]
  by_cases hd0 : f.natDegree = 0
  · simp only [hd0, ↓reduceIte]
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hc0 : f.coeff 0 ≠ 0 := fun hz => hf0 (by rw [hfC, hz, map_zero])
    refine ⟨hc0, ?_, ?_, by simpa [hd0] using hcard⟩
    · intro _ hp; cases hp
    · simp [hfC.symm]
  · simp only [hd0, ↓reduceIte]
    let u := f.leadingCoeff
    have hu0 : u ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    let m := Polynomial.C u⁻¹ * f
    have hm_monic : m.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hu0]
    have hm_deg : m.natDegree = f.natDegree := Polynomial.natDegree_C_mul (inv_ne_zero hu0)
    obtain ⟨_, hm_irr, hm_prod⟩ :=
      finiteFieldFactorMonicAux_spec m.natDegree m hm_monic (by omega) le_rfl
    refine ⟨hu0, ?_, ?_, hcard⟩
    · intro p hp
      obtain ⟨hpm, hpi⟩ := hm_irr p hp
      exact ⟨hpm, hpi, (isGarlingIrreducible_iff _).mpr hpi⟩
    · rw [hm_prod]
      dsimp [m]
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hu0, map_one, one_mul]

/-- **Exercise 5.3** (§5.1, printed p. 50):
Suppose that `K` is a field with finitely many elements (`[Field K] [Fintype K]`). Then
`finiteFieldFactorList` expresses every non-zero non-unit `f ∈ K[X]` as a non-empty product of
irreducible factors in `K[X]`, searching at most `|K|^(⌊deg f / 2⌋ + 1)` candidates per step over at
most `deg f` splitting steps. -/
theorem exercise_5_3 {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    finiteFieldFactorList f ≠ [] ∧
    (∀ p ∈ finiteFieldFactorList f, Irreducible p ∧ IsGarlingIrreducible p) ∧
    (finiteFieldFactorList f).prod = f ∧
    (finiteFieldProperMonicDivisors f).card ≤ Fintype.card K ^ (f.natDegree / 2 + 1) := by
  have hd_pos : 1 ≤ f.natDegree := by
    by_contra hle0
    have hd0 : f.natDegree = 0 := by omega
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hc0 : f.coeff 0 ≠ 0 := fun hz => hf0 (by rw [hfC, hz, map_zero])
    exact hfu (hfC ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)
  have hspec := exercise_5_3_with_unit hf0
  dsimp only [] at hspec
  unfold finiteFieldFactorList
  unfold finiteFieldFactorWithUnit at hspec ⊢
  have hd_ne0 : f.natDegree ≠ 0 := by omega
  simp only [hf0, hd_ne0, ↓reduceIte] at hspec ⊢
  rcases hspec with ⟨hu0, hL_irr, hprod, hcard⟩
  let u := f.leadingCoeff
  let m := Polynomial.C u⁻¹ * f
  have hm_monic : m.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hu0]
  have hm_deg : m.natDegree = f.natDegree := Polynomial.natDegree_C_mul (inv_ne_zero hu0)
  obtain ⟨hL_ne, _, _⟩ :=
    finiteFieldFactorMonicAux_spec m.natDegree m hm_monic (by omega) le_rfl
  cases hL : finiteFieldFactorMonicAux m.natDegree m with
  | nil => exact absurd hL hL_ne
  | cons p ps =>
    rw [hL] at hL_irr hprod
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, hcard⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · have hp_irr : Irreducible p := (hL_irr p List.mem_cons_self).2.1
        have hCu_unit : IsUnit (Polynomial.C u) := (isUnit_iff_ne_zero.mpr hu0).map Polynomial.C
        have hass : Associated p (Polynomial.C u * p) :=
          ⟨hCu_unit.unit, by simp [mul_comm]⟩
        have hcp_irr : Irreducible (Polynomial.C u * p) := hass.irreducible hp_irr
        exact ⟨hcp_irr, (isGarlingIrreducible_iff _).mpr hcp_irr⟩
      · have hqi := (hL_irr q (List.mem_cons_of_mem p hmem)).2.1
        exact ⟨hqi, (isGarlingIrreducible_iff _).mpr hqi⟩
    · simp only [List.prod_cons] at hprod ⊢
      rwa [mul_assoc]

/-- `Finite K` formulation of `Exercise 5.3` (§5.1, p. 50) without requiring a pre-existing
`Fintype K` instance. -/
theorem exercise_5_3_finite {K : Type*} [Field K] [Finite K] {f : K[X]}
    (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    ∃ L : List K[X], L ≠ [] ∧ (∀ p ∈ L, Irreducible p ∧ IsGarlingIrreducible p) ∧ L.prod = f := by
  let _ : Fintype K := Fintype.ofFinite K
  exact ⟨finiteFieldFactorList f, (exercise_5_3 hf0 hfu).1,
    (exercise_5_3 hf0 hfu).2.1, (exercise_5_3 hf0 hfu).2.2.1⟩

end FiniteFieldFactorization


/-! #### Exercise 5.4: Irreducibility of `f(x) - y g(x)` in `K(y)[x]` -/

/-- The canonical indeterminate `y ∈ K(y) = FractionRing K[X]` (§5.1, Ex. 5.4, p. 50). -/
noncomputable def ratFuncVar (K : Type*) [Field K] : FractionRing K[X] :=
  algebraMap K[X] (FractionRing K[X]) Polynomial.X

/-- Garling's polynomial `f(x) - y g(x) ∈ K(y)[x]` (`K(y) = FractionRing K[X]`, §5.1, Ex. 5.4,
printed p. 50 / PDF p. 58). -/
noncomputable def linearPencilRatFunc {K : Type*} [Field K] (f g : K[X]) :
    (FractionRing K[X])[X] :=
  f.map (algebraMap K (FractionRing K[X])) -
    Polynomial.C (ratFuncVar K) * g.map (algebraMap K (FractionRing K[X]))

/-- **Exercise 5.4 — Constant counterexamples to the literal printed statement** (§5.1, p. 50):
Over every field `K`, each of the pairs `(1, 1)`, `(1, 0)`, and `(0, 1)` in `K[X]` is relatively
prime (`IsGarlingRelativelyPrime` and `IsRelPrime`), yet `f(x) - y g(x)` equals `1 - y`, `1`, and
`-y` respectively in `K(y)[x]`, each of which is a non-zero constant unit in `K(y)[x]` and hence
not irreducible. -/
theorem exercise_5_4_constant_counterexample (K : Type*) [Field K] :
    (IsGarlingRelativelyPrime ({(1 : K[X]), (1 : K[X])} : Set K[X]) ∧
      IsRelPrime (1 : K[X]) (1 : K[X]) ∧
      IsUnit (linearPencilRatFunc (1 : K[X]) (1 : K[X])) ∧
      ¬ Irreducible (linearPencilRatFunc (1 : K[X]) (1 : K[X]))) ∧
    (IsGarlingRelativelyPrime ({(1 : K[X]), (0 : K[X])} : Set K[X]) ∧
      IsRelPrime (1 : K[X]) (0 : K[X]) ∧
      IsUnit (linearPencilRatFunc (1 : K[X]) (0 : K[X])) ∧
      ¬ Irreducible (linearPencilRatFunc (1 : K[X]) (0 : K[X]))) ∧
    (IsGarlingRelativelyPrime ({(0 : K[X]), (1 : K[X])} : Set K[X]) ∧
      IsRelPrime (0 : K[X]) (1 : K[X]) ∧
      IsUnit (linearPencilRatFunc (0 : K[X]) (1 : K[X])) ∧
      ¬ Irreducible (linearPencilRatFunc (0 : K[X]) (1 : K[X]))) := by
  have hrel11 : IsRelPrime (1 : K[X]) (1 : K[X]) := fun _ hd _ => isUnit_of_dvd_one hd
  have hrel10 : IsRelPrime (1 : K[X]) (0 : K[X]) := fun _ hd _ => isUnit_of_dvd_one hd
  have hrel01 : IsRelPrime (0 : K[X]) (1 : K[X]) := fun _ _ hd => isUnit_of_dvd_one hd
  have hgar11 : IsGarlingRelativelyPrime ({(1 : K[X]), (1 : K[X])} : Set K[X]) :=
    ⟨⟨1, by simp⟩, ⟨fun _ _ => one_dvd _, fun d hd => hd 1 (by simp)⟩⟩
  have hgar10 : IsGarlingRelativelyPrime ({(1 : K[X]), (0 : K[X])} : Set K[X]) :=
    ⟨⟨1, by simp⟩, ⟨fun _ _ => one_dvd _, fun d hd => hd 1 (by simp)⟩⟩
  have hgar01 : IsGarlingRelativelyPrime ({(0 : K[X]), (1 : K[X])} : Set K[X]) :=
    ⟨⟨0, by simp⟩, ⟨fun _ _ => one_dvd _, fun d hd => hd 1 (by simp)⟩⟩
  have hinj : Function.Injective (algebraMap K[X] (FractionRing K[X])) :=
    IsFractionRing.injective K[X] (FractionRing K[X])
  have hy_ne1 : (1 : FractionRing K[X]) - ratFuncVar K ≠ 0 := by
    intro hz
    have heq : algebraMap K[X] (FractionRing K[X]) 1 =
        algebraMap K[X] (FractionRing K[X]) Polynomial.X := by
      rw [map_one]
      exact sub_eq_zero.mp hz
    have h1X : (1 : K[X]) = Polynomial.X := hinj heq
    have hc := congrArg (fun p : K[X] => p.coeff 1) h1X
    rw [Polynomial.coeff_one] at hc
    simp at hc
  have hy_ne0 : -(ratFuncVar K) ≠ 0 := by
    rw [neg_ne_zero]
    intro hz
    have hX0 : (Polynomial.X : K[X]) = 0 :=
      hinj (hz.trans (map_zero (algebraMap K[X] (FractionRing K[X]))).symm)
    exact Polynomial.X_ne_zero hX0
  have hu11 : IsUnit (linearPencilRatFunc (1 : K[X]) (1 : K[X])) := by
    have heq : linearPencilRatFunc (1 : K[X]) (1 : K[X]) = Polynomial.C (1 - ratFuncVar K) := by
      unfold linearPencilRatFunc
      simp [map_sub]
    rw [heq]
    exact (isUnit_iff_ne_zero.mpr hy_ne1).map Polynomial.C
  have hu10 : IsUnit (linearPencilRatFunc (1 : K[X]) (0 : K[X])) := by
    have heq : linearPencilRatFunc (1 : K[X]) (0 : K[X]) = 1 := by
      unfold linearPencilRatFunc
      simp
    rw [heq]
    exact isUnit_one
  have hu01 : IsUnit (linearPencilRatFunc (0 : K[X]) (1 : K[X])) := by
    have heq : linearPencilRatFunc (0 : K[X]) (1 : K[X]) = Polynomial.C (-ratFuncVar K) := by
      unfold linearPencilRatFunc
      simp
    rw [heq]
    exact (isUnit_iff_ne_zero.mpr hy_ne0).map Polynomial.C
  exact ⟨⟨hgar11, hrel11, hu11, fun hi => hi.not_isUnit hu11⟩,
    ⟨hgar10, hrel10, hu10, fun hi => hi.not_isUnit hu10⟩,
    ⟨hgar01, hrel01, hu01, fun hi => hi.not_isUnit hu01⟩⟩

/-- Indeterminate-swapping ring endomorphism on `K[X][X]` (`K[y][x] →+* K[x][y]`). -/
noncomputable def polySwapHom (K : Type*) [CommRing K] : K[X][X] →+* K[X][X] :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) Polynomial.X)
    (Polynomial.C Polynomial.X)

private theorem polySwapHom_involutive (K : Type*) [CommRing K] :
    (polySwapHom K).comp (polySwapHom K) = RingHom.id K[X][X] := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext a
      simp [polySwapHom]
    · simp [polySwapHom]
  · simp [polySwapHom]

/-- Indeterminate-swapping ring isomorphism `K[y][x] ≃+* K[x][y]`. -/
noncomputable def polySwapEquiv (K : Type*) [CommRing K] : K[X][X] ≃+* K[X][X] :=
  { polySwapHom K with
    invFun := polySwapHom K
    left_inv := fun P => RingHom.congr_fun (polySwapHom_involutive K) P
    right_inv := fun P => RingHom.congr_fun (polySwapHom_involutive K) P }

private theorem polySwapHom_map_C {K : Type*} [CommRing K] (p : K[X]) :
    polySwapHom K (p.map Polynomial.C) = Polynomial.C p := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [Polynomial.map_add, map_add, ihp, ihq, ← Polynomial.C_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_mul, map_pow]
    have h1 : polySwapHom K (Polynomial.C (Polynomial.C a)) = Polynomial.C (Polynomial.C a) := by
      simp [polySwapHom]
    have h2 : polySwapHom K Polynomial.X = Polynomial.C Polynomial.X := by
      simp [polySwapHom]
    rw [h1, h2, ← Polynomial.C_pow, ← Polynomial.C_mul]

/-- Bridge between Garling's `IsGarlingRelativelyPrime ({f, g} : Set R)` and Mathlib's
`IsRelPrime f g` in any commutative ring `R`. -/
theorem isGarlingRelativelyPrime_pair_iff {R : Type*} [CommRing R] (f g : R) :
    IsGarlingRelativelyPrime ({f, g} : Set R) ↔ IsRelPrime f g := by
  constructor
  · rintro ⟨_, ⟨_, hmax⟩⟩ d hdf hdg
    exact isUnit_of_dvd_one (hmax d fun b hb => by
      rcases hb with rfl | rfl
      · exact hdf
      · exact hdg)
  · intro hrel
    refine ⟨⟨f, by simp⟩, ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩⟩
    exact (hrel (hd f (by simp)) (hd g (by simp))).dvd

/-- **Exercise 5.4** (§5.1, printed p. 50):
Suppose that `f` and `g` are relatively prime elements of `K[X]` (`K` a field) that are not both
constant (`0 < f.natDegree ∨ 0 < g.natDegree`). Then `f(x) - y g(x)` is irreducible in `K(y)[x]`
(`(FractionRing K[X])[X]`), where `K(y) = FractionRing K[X]` is the field of rational functions in
`y` over `K`. -/
theorem exercise_5_4 {K : Type*} [Field K] {f g : K[X]}
    (hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]))
    (hdeg : 0 < f.natDegree ∨ 0 < g.natDegree) :
    Irreducible (linearPencilRatFunc f g) ∧
    IsGarlingIrreducible (linearPencilRatFunc f g) := by
  have hrel : IsRelPrime f g := (isGarlingRelativelyPrime_pair_iff f g).mp hcop
  have hg0 : g ≠ 0 := by
    intro hgz
    subst hgz
    have hfu : IsUnit f := hrel dvd_rfl (dvd_zero f)
    have hfd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hfu
    simp [hfd0] at hdeg
  let P0 : K[X][X] := f.map Polynomial.C - Polynomial.C Polynomial.X * g.map Polynomial.C
  let Q0 : K[X][X] := Polynomial.C f - Polynomial.C g * Polynomial.X
  have hswap : polySwapEquiv K P0 = Q0 := by
    change polySwapHom K P0 = Q0
    dsimp [P0, Q0]
    have hCX : polySwapHom K (Polynomial.C Polynomial.X) = Polynomial.X := by
      simp [polySwapHom]
    rw [map_sub, map_mul, polySwapHom_map_C, polySwapHom_map_C, hCX, mul_comm]
  have hQ0_prim : IsGarlingPrimitive Q0 := by
    rw [isGarlingPrimitive_iff]
    intro d hdvd
    obtain ⟨q, hq⟩ := hdvd
    have hc0 := congrArg (fun H : K[X][X] => H.coeff 0) hq
    have hc1 := congrArg (fun H : K[X][X] => H.coeff 1) hq
    simp only [Q0, Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_C_succ,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one, mul_zero,
      mul_one, sub_zero, zero_sub] at hc0 hc1
    have hdf : d ∣ f := ⟨q.coeff 0, hc0⟩
    have hdg : d ∣ g := dvd_neg.mp ⟨q.coeff 1, hc1⟩
    exact hrel hdf hdg
  have hinj_FR : Function.Injective (algebraMap K[X] (FractionRing K[X])) :=
    IsFractionRing.injective K[X] (FractionRing K[X])
  have hQ0_map_deg : (Q0.map (algebraMap K[X] (FractionRing K[X]))).degree = 1 := by
    have hmap_eq : Q0.map (algebraMap K[X] (FractionRing K[X])) =
        Polynomial.C (algebraMap K[X] (FractionRing K[X]) f) -
        Polynomial.C (algebraMap K[X] (FractionRing K[X]) g) * Polynomial.X := by
      simp [Q0]
    rw [hmap_eq]
    have hg_fr : algebraMap K[X] (FractionRing K[X]) g ≠ 0 :=
      fun hz => hg0 (hinj_FR (hz.trans (map_zero _).symm))
    compute_degree!
  have hQ0_map_irr : Irreducible (Q0.map (algebraMap K[X] (FractionRing K[X]))) :=
    Polynomial.irreducible_of_degree_eq_one hQ0_map_deg
  have hQ0_irr : Irreducible Q0 :=
    (corollary_gauss_lemma (FractionRing K[X]) Q0).mpr (Or.inr ⟨hQ0_prim, hQ0_map_irr⟩)
  have hP0_irr : Irreducible P0 := by
    have heq : (polySwapEquiv K).symm Q0 = P0 := (polySwapEquiv K).symm_apply_eq.mpr hswap.symm
    rw [← heq]
    exact (MulEquiv.irreducible_iff (polySwapEquiv K).symm.toMulEquiv).mpr hQ0_irr
  have hP0_coeff : ∀ k : ℕ, P0.coeff k = Polynomial.C (f.coeff k) - Polynomial.X * Polynomial.C (g.coeff k) := by
    intro k
    dsimp [P0]
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have hP0_not_C : ¬ ∃ a : K[X], Irreducible a ∧ P0 = Polynomial.C a := by
    rintro ⟨a, _, hPa⟩
    have hex_pos : ∃ k : ℕ, 1 ≤ k ∧ (f.coeff k ≠ 0 ∨ g.coeff k ≠ 0) := by
      rcases hdeg with hfd | hgd
      · exact ⟨f.natDegree, hfd, Or.inl (Polynomial.leadingCoeff_ne_zero.mpr
          (fun hz => by simp [hz] at hfd))⟩
      · exact ⟨g.natDegree, hgd, Or.inr (Polynomial.leadingCoeff_ne_zero.mpr hg0)⟩
    obtain ⟨k, hk1, hk_ne⟩ := hex_pos
    have hck := congrArg (fun H : K[X][X] => H.coeff k) hPa
    have hk_ne0 : k ≠ 0 := by omega
    rw [hP0_coeff k, Polynomial.coeff_C] at hck
    simp only [hk_ne0, ↓reduceIte] at hck
    have hc0 := congrArg (fun p : K[X] => p.coeff 0) hck
    have hc1 := congrArg (fun p : K[X] => p.coeff 1) hck
    simp at hc0 hc1
    rcases hk_ne with hfk | hgk
    · exact hfk hc0
    · exact hgk hc1
  have hP0_gauss := (corollary_gauss_lemma (FractionRing K[X]) P0).mp hP0_irr
  rcases hP0_gauss with hC | ⟨_, hmap_irr⟩
  · exact False.elim (hP0_not_C hC)
  · have hmap_eq : P0.map (algebraMap K[X] (FractionRing K[X])) = linearPencilRatFunc f g := by
      dsimp [P0, linearPencilRatFunc, ratFuncVar]
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_map, Polynomial.map_map]
      have hcomp : (algebraMap K[X] (FractionRing K[X])).comp Polynomial.C =
          algebraMap K (FractionRing K[X]) := by
        ext c
        exact (IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]) c).symm
      rw [hcomp]
    rw [hmap_eq] at hmap_irr
    exact ⟨hmap_irr, (isGarlingIrreducible_iff _).mpr hmap_irr⟩

/-- `IsRelPrime` companion for `Exercise 5.4` (§5.1, p. 50). -/
theorem exercise_5_4_relPrime {K : Type*} [Field K] {f g : K[X]}
    (hcop : IsRelPrime f g) (hdeg : 0 < f.natDegree ∨ 0 < g.natDegree) :
    Irreducible (linearPencilRatFunc f g) :=
  (exercise_5_4 ((isGarlingRelativelyPrime_pair_iff f g).mpr hcop) hdeg).1

/-- **Exercise 5.4 — Exact `iff` characterization** (§5.1, p. 50):
For relatively prime `f, g ∈ K[X]` (`K` a field), `f(x) - y g(x)` is irreducible in `K(y)[x]` if
and only if `0 < f.natDegree ∨ 0 < g.natDegree`. -/
theorem exercise_5_4_iff {K : Type*} [Field K] {f g : K[X]}
    (hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X])) :
    Irreducible (linearPencilRatFunc f g) ↔ (0 < f.natDegree ∨ 0 < g.natDegree) := by
  constructor
  · intro hirr
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨hf0, hg0⟩
    have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hgC : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hC : linearPencilRatFunc f g =
        Polynomial.C (algebraMap K (FractionRing K[X]) (f.coeff 0) -
          ratFuncVar K * algebraMap K (FractionRing K[X]) (g.coeff 0)) := by
      unfold linearPencilRatFunc
      rw [hfC, hgC]
      simp [map_sub, map_mul]
    by_cases hc : algebraMap K (FractionRing K[X]) (f.coeff 0) -
        ratFuncVar K * algebraMap K (FractionRing K[X]) (g.coeff 0) = 0
    · rw [hC, hc, map_zero] at hirr
      exact hirr.ne_zero rfl
    · exact hirr.not_isUnit (hC ▸ (isUnit_iff_ne_zero.mpr hc).map Polynomial.C)
  · exact fun hdeg => (exercise_5_4 hcop hdeg).1

/-! #### Exercise 5.5: Simple transcendental extensions `K(α) : K` and `[K(α) : K(β)]` -/

private theorem aeval_mem_adjoin_simple {K L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) (p : K[X]) :
    Polynomial.aeval α p ∈ IntermediateField.adjoin K {α} :=
  (IntermediateField.mem_adjoin_simple_iff K _).mpr ⟨p, 1, by simp⟩

private theorem aeval_intermediateField_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) (x : F) (p : K[X]) :
    ((Polynomial.aeval x p : F) : L) = Polynomial.aeval (x : L) p :=
  (Polynomial.aeval_algHom_apply F.val x p).symm

private theorem aeval_map_eq_of_algebraMap_eq {K B M : Type*} [CommSemiring K] [CommSemiring B]
    [CommSemiring M] [Algebra K B] [Algebra K M] [Algebra B M]
    (hcomp : ∀ c : K, algebraMap B M (algebraMap K B c) = algebraMap K M c)
    (x : M) (p : K[X]) :
    Polynomial.aeval x (p.map (algebraMap K B)) = Polynomial.aeval x p := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [Polynomial.map_add, map_add, map_add, ihp, ihq]
  | monomial n c =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, hcomp c]

/-- **Exercise 5.5 (Sentence 2)** (§5.1, printed p. 51):
Suppose that `α ∈ L` is transcendental over `K` (`IsGarlingTranscendental K α`) and that
`β ∈ K(α)` with `β ∉ K` (`β ∉ (⊥ : IntermediateField K L)`). Then:
1. `K(α) : K(β)` is finite (`IsFiniteExtension (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α})`)
   and `α` is algebraic over `K(β)` (`IsGarlingAlgebraic (IntermediateField.adjoin K {β}) α`); and
2. `β` is transcendental over `K` (`IsGarlingTranscendental K β`). -/
theorem exercise_5_5_algebraic_and_transcendental
    {K L : Type*} [Field K] [Field L] [Algebra K L] {α β : L}
    (htrans : IsGarlingTranscendental K α)
    (hβ_mem : β ∈ IntermediateField.adjoin K {α})
    (hβ_not_K : β ∉ (⊥ : IntermediateField K L)) :
    let inc : IntermediateField.adjoin K {β} →+* IntermediateField.adjoin K {α} :=
      Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_mem))
    letI : Algebra (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) := inc.toAlgebra
    IsFiniteExtension (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) ∧
    IsGarlingAlgebraic (IntermediateField.adjoin K {β}) α ∧
    IsGarlingTranscendental K β := by
  let inc : IntermediateField.adjoin K {β} →+* IntermediateField.adjoin K {α} :=
    Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_mem))
  let _ : Algebra (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) := inc.toAlgebra
  obtain ⟨f, g, hβ_eq⟩ := (IntermediateField.mem_adjoin_simple_iff K β).mp hβ_mem
  have hg_eval_ne : Polynomial.aeval α g ≠ 0 := by
    intro hz
    apply hβ_not_K
    rw [hβ_eq, hz, div_zero]
    exact zero_mem _
  have hg0 : g ≠ 0 := fun hz => hg_eval_ne (by simp [hz])
  let B : IntermediateField K L := IntermediateField.adjoin K {β}
  let βB : B := IntermediateField.AdjoinSimple.gen K β
  let P : B[X] := f.map (algebraMap K B) - Polynomial.C βB * g.map (algebraMap K B)
  have hP_ne0 : P ≠ 0 := by
    intro hP0
    have hgk : g.coeff g.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hck := congrArg (fun H : B[X] => (H.coeff g.natDegree : L)) hP0
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero, ZeroMemClass.coe_zero, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul] at hck
    have hβB_coe : (βB : L) = β := rfl
    have halg_coe : ∀ c : K, ((algebraMap K B c : B) : L) = algebraMap K L c := fun _ => rfl
    rw [hβB_coe, halg_coe, halg_coe, sub_eq_zero] at hck
    have hgk_L : algebraMap K L (g.coeff g.natDegree) ≠ 0 :=
      fun hz => hgk ((injective_iff_map_eq_zero (algebraMap K L)).mp (algebraMap K L).injective _ hz)
    have hβ_in_K : β = algebraMap K L (f.coeff g.natDegree * (g.coeff g.natDegree)⁻¹) := by
      rw [map_mul, map_inv₀]
      apply mul_right_cancel₀ hgk_L
      rw [mul_assoc, inv_mul_cancel₀ hgk_L, mul_one, ← hck]
    exact hβ_not_K (hβ_in_K ▸ (⊥ : IntermediateField K L).algebraMap_mem _)
  have hP_aeval : Polynomial.aeval α P = 0 := by
    dsimp [P]
    rw [map_sub, map_mul, Polynomial.aeval_C,
      aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) α f,
      aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) α g]
    change Polynomial.aeval α f - β * Polynomial.aeval α g = 0
    rw [hβ_eq, div_mul_cancel₀ _ hg_eval_ne, sub_self]
  have halg_α : IsGarlingAlgebraic B α := ⟨P, hP_ne0, hP_aeval⟩
  let M0 := IntermediateField.adjoin K {α}
  let αM0 : M0 := IntermediateField.AdjoinSimple.gen K α
  have hP_aeval_M0 : Polynomial.aeval αM0 P = 0 := by
    apply Subtype.ext
    dsimp [P]
    rw [map_sub, map_mul, Polynomial.aeval_C,
      aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) αM0 f,
      aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) αM0 g]
    have halg_βB : (algebraMap B M0 βB : M0).1 = β := rfl
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul,
      aeval_intermediateField_coe M0 αM0, halg_βB]
    change Polynomial.aeval α f - β * Polynomial.aeval α g = 0
    rw [hβ_eq, div_mul_cancel₀ _ hg_eval_ne, sub_self]
  have halg_αM0 : IsGarlingAlgebraic B αM0 := ⟨P, hP_ne0, hP_aeval_M0⟩
  have hB_top_M0 : IntermediateField.adjoin B ({αM0} : Set M0) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K (x : L)).mp x.2
    have hx_eq : x = Polynomial.aeval αM0 r / Polynomial.aeval αM0 s := by
      apply Subtype.ext
      change M0.val x = M0.val (Polynomial.aeval αM0 r / Polynomial.aeval αM0 s)
      rw [map_div₀]
      change (x : L) = ((Polynomial.aeval αM0 r : M0) : L) / ((Polynomial.aeval αM0 s : M0) : L)
      rw [aeval_intermediateField_coe M0 αM0 r, aeval_intermediateField_coe M0 αM0 s]
      exact hrs
    rw [hx_eq,
      ← aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) αM0 r,
      ← aeval_map_eq_of_algebraMap_eq (B := B) (fun _ : K => rfl) αM0 s]
    exact div_mem (aeval_mem_adjoin_simple (K := B) αM0 _)
      (aeval_mem_adjoin_simple (K := B) αM0 _)
  have hfin_BM0 : IsFiniteExtension B M0 := by
    have hfin_adj : extDegree B (IntermediateField.adjoin B ({αM0} : Set M0)) < ⊤ :=
      (theorem_4_4 αM0).1.mp halg_αM0
    let eTop : IntermediateField.adjoin B ({αM0} : Set M0) ≃ₐ[B] M0 :=
      (IntermediateField.equivOfEq hB_top_M0).trans IntermediateField.topEquiv
    have _ : Module.Finite B (IntermediateField.adjoin B ({αM0} : Set M0)) :=
      (isFiniteExtension_iff_moduleFinite B _).mp hfin_adj
    exact (isFiniteExtension_iff_moduleFinite B M0).mpr (Module.Finite.equiv eTop.toLinearEquiv)
  refine ⟨hfin_BM0, halg_α, ?_⟩
  intro hβ_alg
  let M := IntermediateField.adjoin K {α}
  let αM : M := IntermediateField.AdjoinSimple.gen K α
  let βM : M := ⟨β, hβ_mem⟩
  let BM : IntermediateField K M := IntermediateField.adjoin K {βM}
  have hβM_alg : IsGarlingAlgebraic K βM := by
    obtain ⟨q, hq0, hqeval⟩ := hβ_alg
    refine ⟨q, hq0, Subtype.ext ?_⟩
    rw [aeval_intermediateField_coe M βM q]
    exact hqeval
  let βBM : BM := IntermediateField.AdjoinSimple.gen K βM
  let PM : BM[X] := f.map (algebraMap K BM) - Polynomial.C βBM * g.map (algebraMap K BM)
  have hPM_ne0 : PM ≠ 0 := by
    intro hPM0
    apply hP_ne0
    ext k
    have hck := congrArg (fun H : BM[X] => ((H.coeff k : BM) : M).1) hPM0
    simp only [PM, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero, ZeroMemClass.coe_zero, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul] at hck
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero, ZeroMemClass.coe_zero, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul]
    exact hck
  have hPM_aeval : Polynomial.aeval αM PM = 0 := by
    apply Subtype.ext
    dsimp [PM]
    rw [map_sub, map_mul, Polynomial.aeval_C,
      aeval_map_eq_of_algebraMap_eq (B := BM) (fun _ : K => rfl) αM f,
      aeval_map_eq_of_algebraMap_eq (B := BM) (fun _ : K => rfl) αM g]
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul,
      aeval_intermediateField_coe M αM]
    change Polynomial.aeval α f - β * Polynomial.aeval α g = 0
    rw [hβ_eq, div_mul_cancel₀ _ hg_eval_ne, sub_self]
  have halg_αM : IsGarlingAlgebraic BM αM := ⟨PM, hPM_ne0, hPM_aeval⟩
  have hBM_top : IntermediateField.adjoin BM ({αM} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K (x : L)).mp x.2
    have hx_eq : x = Polynomial.aeval αM r / Polynomial.aeval αM s := by
      apply Subtype.ext
      change M.val x = M.val (Polynomial.aeval αM r / Polynomial.aeval αM s)
      rw [map_div₀]
      change (x : L) = ((Polynomial.aeval αM r : M) : L) / ((Polynomial.aeval αM s : M) : L)
      rw [aeval_intermediateField_coe M αM r, aeval_intermediateField_coe M αM s]
      exact hrs
    rw [hx_eq,
      ← aeval_map_eq_of_algebraMap_eq (B := BM) (fun _ : K => rfl) αM r,
      ← aeval_map_eq_of_algebraMap_eq (B := BM) (fun _ : K => rfl) αM s]
    exact div_mem (aeval_mem_adjoin_simple (K := BM) αM _)
      (aeval_mem_adjoin_simple (K := BM) αM _)
  have hdeg_BM_M : extDegree BM M < ⊤ := by
    have hfin_adj : extDegree BM (IntermediateField.adjoin BM ({αM} : Set M)) < ⊤ :=
      (theorem_4_4 αM).1.mp halg_αM
    let eTop : IntermediateField.adjoin BM ({αM} : Set M) ≃ₐ[BM] M :=
      (IntermediateField.equivOfEq hBM_top).trans IntermediateField.topEquiv
    have hfd_adj : Module.Finite BM (IntermediateField.adjoin BM ({αM} : Set M)) :=
      (isFiniteExtension_iff_moduleFinite BM _).mp hfin_adj
    exact (isFiniteExtension_iff_moduleFinite BM M).mpr (Module.Finite.equiv eTop.toLinearEquiv)
  have hdeg_K_BM : extDegree K BM < ⊤ := (theorem_4_4 βM).1.mp hβM_alg
  have hdeg_K_M : extDegree K M < ⊤ := by
    rw [theorem_4_2 K BM M]
    exact WithTop.mul_lt_top hdeg_BM_M hdeg_K_BM
  exact htrans ((theorem_4_4 α).1.mpr hdeg_K_M)

/-- **Exercise 5.5** (§5.1, printed p. 51 / PDF p. 59):
Suppose that `K(α) : K` is a simple transcendental extension (`IsGarlingTranscendental K α`),
that `β ∈ K(α)` with `β ∉ K`, and that `β = f(α)/g(α)` where `f` and `g` are relatively prime
elements of `K[X]` (`IsGarlingRelativelyPrime ({f, g} : Set K[X])`). Then:
1. `α` is algebraic over `K(β)` and `β` is transcendental over `K`;
2. `f ≠ 0`, `g ≠ 0`, `g(α) ≠ 0`, and `0 < max (deg f) (deg g)`; and
3. `[K(α) : K(β)] = max (degree f, degree g)` (both for `natDegree` and for Garling's
   `garlingDegree`). -/
theorem exercise_5_5
    {K L : Type*} [Field K] [Field L] [Algebra K L] {α β : L} {f g : K[X]}
    (htrans : IsGarlingTranscendental K α)
    (hβ_not_K : β ∉ (⊥ : IntermediateField K L))
    (hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]))
    (hβ_eq : β = Polynomial.aeval α f / Polynomial.aeval α g) :
    have hβ_mem : β ∈ IntermediateField.adjoin K {α} := by
      rw [hβ_eq]
      exact div_mem (aeval_mem_adjoin_simple α f) (aeval_mem_adjoin_simple α g)
    have hf0 : f ≠ 0 := fun hfz => hβ_not_K (by rw [hβ_eq, hfz, map_zero, zero_div]; exact zero_mem _)
    have hg0 : g ≠ 0 := fun hgz => hβ_not_K (by rw [hβ_eq, hgz, map_zero, div_zero]; exact zero_mem _)
    let inc : IntermediateField.adjoin K {β} →+* IntermediateField.adjoin K {α} :=
      Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_mem))
    letI : Algebra (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) := inc.toAlgebra
    IsFiniteExtension (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) ∧
    IsGarlingAlgebraic (IntermediateField.adjoin K {β}) α ∧
    IsGarlingTranscendental K β ∧
    Polynomial.aeval α g ≠ 0 ∧
    extDegree (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) =
      ((max (garlingDegree f hf0) (garlingDegree g hg0) : ℕ) : ℕ∞) ∧
    extDegree (IntermediateField.adjoin K {β}) (IntermediateField.adjoin K {α}) =
      ((max f.natDegree g.natDegree : ℕ) : ℕ∞) := by
  have hβ_mem : β ∈ IntermediateField.adjoin K {α} := by
    rw [hβ_eq]
    exact div_mem (aeval_mem_adjoin_simple α f) (aeval_mem_adjoin_simple α g)
  have hf0 : f ≠ 0 :=
    fun hfz => hβ_not_K (by rw [hβ_eq, hfz, map_zero, zero_div]; exact zero_mem _)
  have hg_eval_ne : Polynomial.aeval α g ≠ 0 :=
    fun hz => hβ_not_K (by rw [hβ_eq, hz, div_zero]; exact zero_mem _)
  have hg0 : g ≠ 0 := fun hgz => hg_eval_ne (by simp [hgz])
  have hdeg_pos : 0 < f.natDegree ∨ 0 < g.natDegree := by
    by_contra hboth0
    push Not at hboth0
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : f.natDegree = 0)
    have hgC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : g.natDegree = 0)
    apply hβ_not_K
    rw [hβ_eq, hfC, hgC, Polynomial.aeval_C, Polynomial.aeval_C, ← map_div₀]
    exact (⊥ : IntermediateField K L).algebraMap_mem _
  obtain ⟨hfin_BM, halg_α, htrans_β⟩ := exercise_5_5_algebraic_and_transcendental htrans hβ_mem hβ_not_K
  let B := IntermediateField.adjoin K {β}
  let M := IntermediateField.adjoin K {α}
  let inc : B →+* M :=
    Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_mem))
  let _ : Algebra B M := inc.toAlgebra
  let βB : B := IntermediateField.AdjoinSimple.gen K β
  have htrans_βB : IsGarlingTranscendental K βB := by
    intro ⟨q, hq0, hqeval⟩
    apply htrans_β
    refine ⟨q, hq0, ?_⟩
    have hval := aeval_intermediateField_coe B βB q
    rw [hqeval, ZeroMemClass.coe_zero] at hval
    exact hval.symm
  have heval_inj : Function.Injective (Polynomial.aeval βB : K[X] →ₐ[K] B) :=
    (evalRingHom_injective_iff K βB).1.mpr htrans_βB
  have h_units : ∀ y : nonZeroDivisors K[X], IsUnit ((Polynomial.aeval βB : K[X] →ₐ[K] B) y) := by
    intro y
    have hy0 : (y : K[X]) ≠ 0 := nonZeroDivisors.ne_zero y.2
    have hmap0 : (Polynomial.aeval βB : K[X] →ₐ[K] B) y ≠ 0 :=
      fun hz => hy0 (heval_inj (hz.trans (map_zero _).symm))
    exact isUnit_iff_ne_zero.mpr hmap0
  let ψ : FractionRing K[X] →+* B :=
    IsLocalization.lift (M := nonZeroDivisors K[X]) (g := (Polynomial.aeval βB).toRingHom) h_units
  have hψ_inj : Function.Injective ψ := RingHom.injective ψ
  have hψ_surj : Function.Surjective ψ := by
    intro b
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K (b : L)).mp b.2
    by_cases hq0 : q = 0
    · have hb0 : b = 0 := by
        apply Subtype.ext
        change (b : L) = 0
        rw [hpq, hq0, map_zero, div_zero]
      exact ⟨0, by rw [hb0, map_zero]⟩
    · refine ⟨algebraMap K[X] (FractionRing K[X]) p / algebraMap K[X] (FractionRing K[X]) q, ?_⟩
      rw [map_div₀, IsLocalization.lift_eq, IsLocalization.lift_eq]
      apply Subtype.ext
      change B.val (Polynomial.aeval βB p / Polynomial.aeval βB q) = (b : L)
      rw [map_div₀]
      change ((Polynomial.aeval βB p : B) : L) / ((Polynomial.aeval βB q : B) : L) = (b : L)
      rw [aeval_intermediateField_coe B βB p, aeval_intermediateField_coe B βB q]
      exact hpq.symm
  let ψEquiv : FractionRing K[X] ≃+* B := RingEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
  have hψ_K : ∀ c : K, ψEquiv (algebraMap K (FractionRing K[X]) c) = algebraMap K B c := by
    intro c
    change ψ (algebraMap K[X] (FractionRing K[X]) (Polynomial.C c)) = algebraMap K B c
    rw [IsLocalization.lift_eq]
    simp
  have hψ_y : ψEquiv (ratFuncVar K) = βB := by
    change ψ (algebraMap K[X] (FractionRing K[X]) Polynomial.X) = βB
    rw [IsLocalization.lift_eq]
    simp
  let PB : B[X] := f.map (algebraMap K B) - Polynomial.C βB * g.map (algebraMap K B)
  have hmap_pencil : (linearPencilRatFunc f g).map ψEquiv.toRingHom = PB := by
    dsimp [linearPencilRatFunc, PB]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_map, Polynomial.map_map]
    simp only [RingHom.coe_coe, hψ_y]
    have hcomp : (↑ψEquiv : FractionRing K[X] →+* B).comp (algebraMap K (FractionRing K[X])) =
        algebraMap K B := by
      apply RingHom.ext
      intro c
      exact hψ_K c
    rw [hcomp]
  have hPB_irr : Irreducible PB := by
    have hirr_F := (exercise_5_4 hcop hdeg_pos).1
    have heq : Polynomial.mapEquiv ψEquiv (linearPencilRatFunc f g) = PB := hmap_pencil
    rw [← heq]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv ψEquiv).toMulEquiv).mpr hirr_F
  have hPB_coeff_zero_iff : ∀ k : ℕ, PB.coeff k = 0 ↔ f.coeff k = 0 ∧ g.coeff k = 0 := by
    intro k
    have hmap_k : ψEquiv ((linearPencilRatFunc f g).coeff k) = PB.coeff k := by
      rw [← hmap_pencil, Polynomial.coeff_map]
      rfl
    rw [← hmap_k, map_eq_zero_iff ψEquiv ψEquiv.injective]
    have hcoeff_F : (linearPencilRatFunc f g).coeff k =
        algebraMap K[X] (FractionRing K[X])
          (Polynomial.C (f.coeff k) - Polynomial.X * Polynomial.C (g.coeff k)) := by
      dsimp [linearPencilRatFunc, ratFuncVar]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_map,
        map_sub, map_mul]
      rfl
    rw [hcoeff_F, map_eq_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))]
    constructor
    · intro hz
      have hc0 := congrArg (fun p : K[X] => p.coeff 0) hz
      have hc1 := congrArg (fun p : K[X] => p.coeff 1) hz
      simp at hc0 hc1
      exact ⟨hc0, hc1⟩
    · rintro ⟨hfk, hgk⟩
      simp [hfk, hgk]
  have hPB_deg : PB.natDegree = max f.natDegree g.natDegree := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hPB_coeff_zero_iff]
      exact ⟨Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_left _ _) hk),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right _ _) hk)⟩
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [ne_eq, hPB_coeff_zero_iff, not_and_or]
      rcases le_total f.natDegree g.natDegree with hle | hle
      · rw [max_eq_right hle]
        exact Or.inr (Polynomial.leadingCoeff_ne_zero.mpr hg0)
      · rw [max_eq_left hle]
        exact Or.inl (Polynomial.leadingCoeff_ne_zero.mpr hf0)
  let αM : M := IntermediateField.AdjoinSimple.gen K α
  have hcomp_BM : ∀ c : K, algebraMap B M (algebraMap K B c) = algebraMap K M c :=
    fun _ => rfl
  have hPB_aeval : Polynomial.aeval αM PB = 0 := by
    apply Subtype.ext
    dsimp [PB]
    rw [map_sub, map_mul, Polynomial.aeval_C,
      aeval_map_eq_of_algebraMap_eq hcomp_BM αM f,
      aeval_map_eq_of_algebraMap_eq hcomp_BM αM g]
    have halg_βB : (algebraMap B M βB : M).1 = β := rfl
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul,
      aeval_intermediateField_coe M αM, halg_βB]
    change Polynomial.aeval α f - β * Polynomial.aeval α g = 0
    rw [hβ_eq, div_mul_cancel₀ _ hg_eval_ne, sub_self]
  let mB : B[X] := Polynomial.C PB.leadingCoeff⁻¹ * PB
  have hPB_lc_ne : PB.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPB_irr.ne_zero
  have hmB_monic : mB.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hPB_lc_ne]
  have hmB_irr : Irreducible mB := by
    have hass : Associated PB mB :=
      ⟨(isUnit_iff_ne_zero.mpr (inv_ne_zero hPB_lc_ne)).map Polynomial.C |>.unit, by simp [mB, mul_comm]⟩
    exact hass.irreducible hPB_irr
  have hmB_aeval : Polynomial.aeval αM mB = 0 := by
    dsimp [mB]
    rw [map_mul, hPB_aeval, mul_zero]
  have hmin_eq : minpoly B αM = mB :=
    (minpoly.eq_of_irreducible_of_monic hmB_irr hmB_aeval hmB_monic).symm
  have hmB_deg : mB.natDegree = PB.natDegree :=
    Polynomial.natDegree_C_mul (inv_ne_zero hPB_lc_ne)
  have hB_top : IntermediateField.adjoin B ({αM} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K (x : L)).mp x.2
    have hx_eq : x = Polynomial.aeval αM r / Polynomial.aeval αM s := by
      apply Subtype.ext
      change M.val x = M.val (Polynomial.aeval αM r / Polynomial.aeval αM s)
      rw [map_div₀]
      change (x : L) = ((Polynomial.aeval αM r : M) : L) / ((Polynomial.aeval αM s : M) : L)
      rw [aeval_intermediateField_coe M αM r, aeval_intermediateField_coe M αM s]
      exact hrs
    rw [hx_eq,
      ← aeval_map_eq_of_algebraMap_eq hcomp_BM αM r,
      ← aeval_map_eq_of_algebraMap_eq hcomp_BM αM s]
    exact div_mem (aeval_mem_adjoin_simple (K := B) αM _)
      (aeval_mem_adjoin_simple (K := B) αM _)
  have halg_αM : IsGarlingAlgebraic B αM := ⟨mB, hmB_monic.ne_zero, hmB_aeval⟩
  have hdeg_adj : extDegree B (IntermediateField.adjoin B ({αM} : Set M)) =
      ((max f.natDegree g.natDegree : ℕ) : ℕ∞) := by
    rw [(theorem_4_4 αM).2 halg_αM |>.2, hmin_eq, hmB_deg, hPB_deg]
  let eTop : IntermediateField.adjoin B ({αM} : Set M) ≃ₐ[B] M :=
    (IntermediateField.equivOfEq hB_top).trans IntermediateField.topEquiv
  have hdeg_BM : extDegree B M = ((max f.natDegree g.natDegree : ℕ) : ℕ∞) := by
    have hfin_adj : extDegree B (IntermediateField.adjoin B ({αM} : Set M)) < ⊤ := by
      rw [hdeg_adj]
      exact ENat.natCast_lt_top _
    have _ : Module.Finite B (IntermediateField.adjoin B ({αM} : Set M)) :=
      (isFiniteExtension_iff_moduleFinite B _).mp hfin_adj
    have _ : Module.Finite B M := Module.Finite.equiv eTop.toLinearEquiv
    rw [extDegree_eq_finrank B M, ← eTop.toLinearEquiv.finrank_eq,
      ← extDegree_eq_finrank B (IntermediateField.adjoin B ({αM} : Set M)), hdeg_adj]
  exact ⟨hfin_BM, halg_α, htrans_β, hg_eval_ne, hdeg_BM, hdeg_BM⟩

/-- **Exercise 5.5 — Standalone sentence-3 constant counterexample** (§5.1, p. 51):
If Sentence 3 of `Exercise 5.5` is read in isolation without Sentence 2's hypothesis `β ∉ K`, taking
`K(α) = FractionRing K[X]` (`α = X`), `f = 1`, `g = 1` gives `β = f(α)/g(α) = 1 ∈ K`, so
`K(β) = K`, `[K(α) : K(β)] = [K(α) : K] = ⊤`, whereas `max (deg f, deg g) = 0`. -/
theorem exercise_5_5_standalone_constant_counterexample (K : Type*) [Field K] :
    let L := FractionRing K[X]
    let α : L := ratFuncVar K
    let f : K[X] := 1
    let g : K[X] := 1
    let β : L := Polynomial.aeval α f / Polynomial.aeval α g
    IsGarlingTranscendental K α ∧
    IntermediateField.adjoin K ({α} : Set L) = ⊤ ∧
    IsGarlingRelativelyPrime ({f, g} : Set K[X]) ∧
    β ∈ (⊥ : IntermediateField K L) ∧
    extDegree K L = ⊤ ∧
    max f.natDegree g.natDegree = 0 := by
  intro L α f g β
  have hinj : Function.Injective (algebraMap K[X] L) := IsFractionRing.injective K[X] L
  have haeval_eq : ∀ q : K[X], Polynomial.aeval α q = algebraMap K[X] L q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add u v ihu ihv =>
      rw [map_add, map_add, ihu, ihv]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      have hc : algebraMap K L c = algebraMap K[X] L (Polynomial.C c) :=
        IsScalarTower.algebraMap_apply K K[X] L c
      rw [hc]
      rfl
  have htrans : IsGarlingTranscendental K α := by
    intro ⟨p, hp0, hpeval⟩
    rw [haeval_eq] at hpeval
    exact hp0 (hinj (hpeval.trans (map_zero _).symm))
  have htop : IntermediateField.adjoin K ({α} : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨p, s, _, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) x
    rw [← haeval_eq p, ← haeval_eq s]
    exact div_mem (aeval_mem_adjoin_simple α p) (aeval_mem_adjoin_simple α s)
  have hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]) :=
    ⟨⟨1, by simp [f]⟩, ⟨fun _ _ => one_dvd _, fun d hd => hd 1 (by simp [f])⟩⟩
  have hβ_bot : β ∈ (⊥ : IntermediateField K L) := by
    have hβ1 : β = 1 := by simp [β, f, g]
    rw [hβ1]
    exact one_mem _
  have hinf : extDegree K L = ⊤ := by
    by_contra hlt_top
    have hlt : extDegree K L < ⊤ := lt_top_iff_ne_top.mpr hlt_top
    have hlt_adj : extDegree K (IntermediateField.adjoin K ({α} : Set L)) < ⊤ := by
      let eTop : IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K] L :=
        (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
      have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hlt
      have _ : Module.Finite K (IntermediateField.adjoin K ({α} : Set L)) :=
        Module.Finite.equiv eTop.symm.toLinearEquiv
      exact (isFiniteExtension_iff_moduleFinite K _).mpr inferInstance
    exact htrans ((theorem_4_4 α).1.mpr hlt_adj)
  exact ⟨htrans, htop, hcop, hβ_bot, hinf, by simp [f, g]⟩

/-! ## §5.2 Eisenstein's criterion (printed pp. 51–52, PDF pp. 59–60) -/

/-- **Theorem 5.2 — Degree-zero counterexample to the literal printed statement** (§5.2, p. 51):
At `n = 0`, taking `R = ℤ`, `f = 1 = a_0 ∈ ℤ[X]`, and `p = 2` satisfies all printed hypotheses of
`Theorem 5.2` (`{a_0} = {1}` is relatively prime in `ℤ`, `2` is prime in `ℤ`, `2` vacuously divides
`a_i` for `i < 0`, `2 ∤ a_0 = 1`, and `2^2 ∤ a_0 = 1`), yet `f = 1` is a unit in `ℤ[X]` and hence
not irreducible. -/
theorem theorem_5_2_zero_counterexample :
    let f : ℤ[X] := 1
    let p : ℤ := 2
    f.natDegree = 0 ∧
    IsGarlingRelativelyPrime (Set.range fun i : Fin 1 => f.coeff i) ∧
    IsGarlingPrime p ∧ Prime p ∧
    (∀ i < 0, p ∣ f.coeff i) ∧
    ¬ (p ∣ f.coeff 0) ∧
    ¬ (p ^ 2 ∣ f.coeff 0) ∧
    IsUnit f ∧ ¬ Irreducible f ∧ ¬ IsGarlingIrreducible f := by
  intro f p
  have hrel : IsGarlingRelativelyPrime (Set.range fun i : Fin 1 => f.coeff i) := by
    refine ⟨⟨f.coeff 0, ⟨0, rfl⟩⟩, ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩⟩
    have hd0 := hd (f.coeff 0) ⟨0, rfl⟩
    simpa [f] using hd0
  have hp : Prime p := Int.prime_two
  have hgp : IsGarlingPrime p := (isGarlingPrime_iff p).mpr hp
  have hu : IsUnit f := isUnit_one
  exact ⟨by simp [f], hrel, hgp, hp, fun _ hi => absurd hi (Nat.not_lt_zero _),
    by simp [f, p], by simp [f, p], hu, fun hi => hi.not_isUnit hu,
    fun hi => (isGarlingIrreducible_iff f).mp hi |>.not_isUnit hu⟩

/-- Helper for `Theorem 5.2` and `Exercise 5.6`: in an integral domain `R`, if `f = g * h` has
`f.natDegree = n` with `f ≠ 0`, the coefficients `{f.coeff 0, ..., f.coeff n}` are relatively prime
(`IsGarlingRelativelyPrime`), and `g` is not a unit in `R[X]`, then `1 ≤ g.natDegree`. -/
theorem one_le_natDegree_left_of_mul_of_relPrime_coeffs
    {R : Type*} [CommRing R] [IsDomain R] {f g h : R[X]} {n : ℕ}
    (hf0 : f ≠ 0) (hdeg : f.natDegree = n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hgh : f = g * h) (hgu : ¬ IsUnit g) :
    1 ≤ g.natDegree := by
  by_contra hlt
  have hd0 : g.natDegree = 0 := by omega
  have hgC : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
  rcases hcop with ⟨_, ⟨_, hmax⟩⟩
  have hdvd_all : ∀ b ∈ (Set.range fun i : Fin (n + 1) => f.coeff i), g.coeff 0 ∣ b := by
    rintro _ ⟨i, rfl⟩
    refine ⟨h.coeff i, ?_⟩
    have hc := congrArg (fun P : R[X] => P.coeff i) hgh
    rw [hgC, Polynomial.coeff_C_mul] at hc
    exact hc
  have hu0 : IsUnit (g.coeff 0) := isUnit_of_dvd_one (hmax (g.coeff 0) hdvd_all)
  have _ := hf0
  have _ := hdeg
  exact hgu (hgC ▸ hu0.map Polynomial.C)

/-- **Theorem 5.2 (Eisenstein's criterion)** (§5.2, printed p. 51 / PDF p. 59):
Suppose that `R` is an integral domain (`[CommRing R] [IsDomain R]`), `1 ≤ n`, and
`f = a_0 + a_1 x + ... + a_n x^n ∈ R[X]` (`f.natDegree ≤ n`) where `a_0, ..., a_n` are relatively
prime (`IsGarlingRelativelyPrime`). Suppose that `p` is a prime in `R` which divides
`a_0, ..., a_{n-1}`, does not divide `a_n`, and is such that `p^2` does not divide `a_0`.
Then `f` is irreducible in `R[X]`. -/
theorem theorem_5_2 {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {n : ℕ} {p : R}
    (hn : 1 ≤ n)
    (hdeg_le : f.natDegree ≤ n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hp : Prime p)
    (hdvd : ∀ i < n, p ∣ f.coeff i)
    (hndvd_n : ¬ (p ∣ f.coeff n))
    (hndvd_sq : ¬ (p ^ 2 ∣ f.coeff 0)) :
    f.natDegree = n ∧ Irreducible f ∧ IsGarlingIrreducible f := by
  classical
  have hfn_ne0 : f.coeff n ≠ 0 := fun hz => hndvd_n (hz ▸ dvd_zero p)
  have hf0 : f ≠ 0 := fun hz => hfn_ne0 (by simp [hz])
  have hdeg : f.natDegree = n := le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hfn_ne0)
  have hirr : Irreducible f := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hg0 : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
      have hg_pos : 1 ≤ g.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop hgh hgu
      have hh_pos : 1 ≤ h.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop (hgh.trans (mul_comm g h)) hhu
      have hsum_deg : g.natDegree + h.natDegree = n := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      have hlead_mul : g.coeff g.natDegree * h.coeff h.natDegree = f.coeff n := by
        rw [← Polynomial.leadingCoeff, ← Polynomial.leadingCoeff, ← Polynomial.leadingCoeff_mul,
          ← hgh, ← hdeg, Polynomial.leadingCoeff]
      have hndvd_glc : ¬ (p ∣ g.coeff g.natDegree) :=
        fun hd => hndvd_n (hlead_mul ▸ dvd_mul_of_dvd_left hd _)
      have hndvd_hlc : ¬ (p ∣ h.coeff h.natDegree) :=
        fun hd => hndvd_n (hlead_mul ▸ dvd_mul_of_dvd_right hd _)
      have hex_g : ∃ i : ℕ, ¬ (p ∣ g.coeff i) := ⟨g.natDegree, hndvd_glc⟩
      have hex_h : ∃ j : ℕ, ¬ (p ∣ h.coeff j) := ⟨h.natDegree, hndvd_hlc⟩
      let r : ℕ := Nat.find hex_g
      let s : ℕ := Nat.find hex_h
      have hr_ndvd : ¬ (p ∣ g.coeff r) := Nat.find_spec hex_g
      have hs_ndvd : ¬ (p ∣ h.coeff s) := Nat.find_spec hex_h
      have hr_le : r ≤ g.natDegree := Nat.find_min' hex_g hndvd_glc
      have hs_le : s ≤ h.natDegree := Nat.find_min' hex_h hndvd_hlc
      have hr_min : ∀ i < r, p ∣ g.coeff i := fun i hi => not_not.mp (Nat.find_min hex_g hi)
      have hs_min : ∀ j < s, p ∣ h.coeff j := fun j hj => not_not.mp (Nat.find_min hex_h hj)
      by_cases hrs_lt : r + s < n
      · have hdvd_rs : p ∣ f.coeff (r + s) := hdvd (r + s) hrs_lt
        rw [hgh, Polynomial.coeff_mul] at hdvd_rs
        have hmem_anti : (r, s) ∈ Finset.antidiagonal (r + s) := Finset.mem_antidiagonal.mpr rfl
        rw [← Finset.add_sum_erase _ _ hmem_anti] at hdvd_rs
        have hdvd_rest : p ∣ ∑ x ∈ (Finset.antidiagonal (r + s)).erase (r, s),
            g.coeff x.1 * h.coeff x.2 := by
          refine Finset.dvd_sum fun x hx => ?_
          have hx_ne : x ≠ (r, s) := (Finset.mem_erase.mp hx).1
          have hx_sum : x.1 + x.2 = r + s :=
            Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hx)
          have hlt_or : x.1 < r ∨ x.2 < s := by
            by_contra hge
            push Not at hge
            have hx1 : x.1 = r := by omega
            have hx2 : x.2 = s := by omega
            exact hx_ne (Prod.ext hx1 hx2)
          rcases hlt_or with h1 | h2
          · exact dvd_mul_of_dvd_left (hr_min x.1 h1) _
          · exact dvd_mul_of_dvd_right (hs_min x.2 h2) _
        have hdvd_prod : p ∣ g.coeff r * h.coeff s := (dvd_add_left hdvd_rest).mp hdvd_rs
        rcases hp.dvd_or_dvd hdvd_prod with h1 | h2
        · exact hr_ndvd h1
        · exact hs_ndvd h2
      · have hr_eq : r = g.natDegree := by omega
        have hs_eq : s = h.natDegree := by omega
        have hr0 : 0 < r := by omega
        have hs0 : 0 < s := by omega
        have hdvd_g0 : p ∣ g.coeff 0 := hr_min 0 hr0
        have hdvd_h0 : p ∣ h.coeff 0 := hs_min 0 hs0
        have hc0 : f.coeff 0 = g.coeff 0 * h.coeff 0 := by
          rw [hgh, Polynomial.mul_coeff_zero]
        have hdvd_sq : p ^ 2 ∣ f.coeff 0 := by
          rw [sq, hc0]
          exact mul_dvd_mul hdvd_g0 hdvd_h0
        exact hndvd_sq hdvd_sq
  exact ⟨hdeg, hirr, (isGarlingIrreducible_iff f).mpr hirr⟩

/-- **Theorem 5.2 (Garling explicit sum form `a_0 + a_1 x + ... + a_n x^n`)** (§5.2, p. 51):
Using `IsGarlingPrime p` and explicit coefficient tuple `a : Fin (n + 1) → R`. -/
theorem theorem_5_2_garling {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hn : 1 ≤ n) (a : Fin (n + 1) → R) {p : R}
    (hcop : IsGarlingRelativelyPrime (Set.range a))
    (hp : IsGarlingPrime p)
    (hdvd : ∀ i : Fin (n + 1), (i : ℕ) < n → p ∣ a i)
    (hndvd_n : ¬ (p ∣ a ⟨n, Nat.lt_succ_self n⟩))
    (hndvd_sq : ¬ (p ^ 2 ∣ a ⟨0, Nat.zero_lt_succ n⟩)) :
    let f : R[X] := ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)
    IsGarlingIrreducible f ∧ Irreducible f := by
  intro f
  have hcoeff : ∀ k : ℕ, f.coeff k = if hk : k < n + 1 then a ⟨k, hk⟩ else 0 := by
    intro k
    dsimp [f]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hk : k < n + 1
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp [hk]
      · intro j _ hjk
        have hval : (j : ℕ) ≠ k := fun hv => hjk (Fin.ext hv)
        simp [hval]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · simp only [hk, ↓reduceDIte]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hval : (j : ℕ) ≠ k := by omega
      simp [hval]
  have hdeg_le : f.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hcoeff k]
    have hnot : ¬ (k < n + 1) := by omega
    simp [hnot]
  have hfun : (fun i : Fin (n + 1) => f.coeff i) = a :=
    funext fun i => by rw [hcoeff i]; simp [i.isLt]
  rw [← hfun] at hcop
  have hres := theorem_5_2 hn hdeg_le hcop ((isGarlingPrime_iff p).mp hp)
    (fun i hi => by
      have hi1 : i < n + 1 := by omega
      rw [hcoeff i]
      simp only [hi1, ↓reduceDIte]
      exact hdvd ⟨i, hi1⟩ hi)
    (by
      rw [hcoeff n]
      simp only [Nat.lt_succ_self n, ↓reduceDIte]
      exact hndvd_n)
    (by
      rw [hcoeff 0]
      simp only [Nat.zero_lt_succ n, ↓reduceDIte]
      exact hndvd_sq)
  exact ⟨hres.2.2, hres.2.1⟩

/-- **Theorem 5.2 — Exact `iff` characterization across all `n : ℕ`** (§5.2, p. 51):
Under the hypotheses of `Theorem 5.2`, `f` is irreducible if and only if `1 ≤ n`. -/
theorem theorem_5_2_iff_pos {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {n : ℕ} {p : R}
    (hdeg : f.natDegree = n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hp : Prime p)
    (hdvd : ∀ i < n, p ∣ f.coeff i)
    (hndvd_n : ¬ (p ∣ f.coeff n))
    (hndvd_sq : ¬ (p ^ 2 ∣ f.coeff 0)) :
    Irreducible f ↔ 1 ≤ n := by
  constructor
  · intro hirr
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rcases hcop with ⟨_, ⟨_, hmax⟩⟩
    have hu0 : IsUnit (f.coeff 0) :=
      isUnit_of_dvd_one (hmax (f.coeff 0) (by rintro _ ⟨i, rfl⟩; fin_cases i; exact dvd_rfl))
    exact hirr.not_isUnit (hfC ▸ hu0.map Polynomial.C)
  · intro hn
    exact (theorem_5_2 hn (le_of_eq hdeg) hcop hp hdvd hndvd_n hndvd_sq).2.1

/-- Helper: every monic polynomial `f : R[X]` of degree `n` has relatively prime coefficients
`{f.coeff 0, ..., f.coeff n}`. -/
theorem isGarlingRelativelyPrime_coeffs_of_monic {R : Type*} [CommRing R] {f : R[X]} {n : ℕ}
    (hm : f.Monic) (hdeg : f.natDegree = n) :
    IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i) := by
  refine ⟨⟨f.coeff n, ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩⟩, ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩⟩
  have hdn : d ∣ f.coeff n := hd (f.coeff n) ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  have hfn1 : f.coeff n = 1 := by
    rw [← hdeg, ← Polynomial.leadingCoeff, hm.leadingCoeff]
  rwa [hfn1] at hdn

/-- **Main-text worked example (`x^5 - 4x + 2`)** (§5.2, printed p. 51 / PDF p. 59):
`x^5 - 4x + 2` is irreducible in `ℤ[X]` (by `Theorem 5.2` with `p = 2`) and hence in `ℚ[X]` (by
`Corollary to Theorem 3.13`, `corollary_gauss_lemma`). -/
theorem example_5_2_quintic_irreducible :
    Irreducible (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 : ℤ[X]) ∧
    Irreducible (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 : ℚ[X]) ∧
    IsGarlingIrreducible
      (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 : ℚ[X]) := by
  let fZ : ℤ[X] := Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  have hdegZ : fZ.natDegree = 5 := by
    dsimp [fZ]
    compute_degree!
  have hmonZ : fZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdegZ]
    dsimp [fZ]
    simp [Polynomial.coeff_X]
  have hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin 6 => fZ.coeff i) :=
    isGarlingRelativelyPrime_coeffs_of_monic hmonZ hdegZ
  have hdvd : ∀ i < 5, (2 : ℤ) ∣ fZ.coeff i := by
    intro i hi
    dsimp [fZ]
    interval_cases i <;> simp [Polynomial.coeff_X]
  have hndvd5 : ¬ ((2 : ℤ) ∣ fZ.coeff 5) := by
    have hc5 : fZ.coeff 5 = 1 := by
      rw [← hdegZ, ← Polynomial.leadingCoeff, hmonZ.leadingCoeff]
    rw [hc5]
    decide
  have hndvd_sq : ¬ ((2 : ℤ) ^ 2 ∣ fZ.coeff 0) := by
    have hc0 : fZ.coeff 0 = 2 := by
      dsimp [fZ]
      simp [Polynomial.coeff_X]
    rw [hc0]
    decide
  have hirrZ : Irreducible fZ :=
    (theorem_5_2 (by decide : 1 ≤ 5) (le_of_eq hdegZ) hcop Int.prime_two hdvd hndvd5 hndvd_sq).2.1
  have hgauss := (corollary_gauss_lemma ℚ fZ).mp hirrZ
  rcases hgauss with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
  · exfalso
    have hd := congrArg Polynomial.natDegree hC
    rw [hdegZ, Polynomial.natDegree_C] at hd
    omega
  · have hmap_eq : fZ.map (algebraMap ℤ ℚ) =
        (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 : ℚ[X]) := by
      dsimp [fZ]
      simp [map_ofNat]
    rw [hmap_eq] at hmap_irr
    exact ⟨hirrZ, hmap_irr, (isGarlingIrreducible_iff _).mpr hmap_irr⟩

/-! ### Exercises 5.6–5.10 (§5.2, printed pp. 51–52, PDF pp. 59–60) -/

/-- **Exercise 5.6 — Degree-zero counterexample to the literal printed statement** (§5.2, p. 51):
At `n = 0`, `R = ℤ`, `f = 1 = a_0 ∈ ℤ[X]`, and `p = 2` satisfy all printed hypotheses of
`Exercise 5.6` (`{a_0} = {1}` is relatively prime, `2` is prime in `ℤ`, `2` vacuously divides
`a_1, ..., a_0`, `2 ∤ a_0 = 1`, and `2^2 ∤ a_0 = 1`), yet `f = 1` is a unit in `ℤ[X]` and hence
not irreducible. -/
theorem exercise_5_6_zero_counterexample :
    let f : ℤ[X] := 1
    let p : ℤ := 2
    f.natDegree = 0 ∧
    IsGarlingRelativelyPrime (Set.range fun i : Fin 1 => f.coeff i) ∧
    IsGarlingPrime p ∧ Prime p ∧
    (∀ i, 1 ≤ i → i ≤ 0 → p ∣ f.coeff i) ∧
    ¬ (p ∣ f.coeff 0) ∧
    ¬ (p ^ 2 ∣ f.coeff 0) ∧
    IsUnit f ∧ ¬ Irreducible f ∧ ¬ IsGarlingIrreducible f := by
  intro f p
  have h0 := theorem_5_2_zero_counterexample
  exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun i hi1 hi0 => by omega,
    h0.2.2.2.2.2.1, h0.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.1,
    h0.2.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.2⟩

/-- **Exercise 5.6 (Reversed Eisenstein criterion)** (§5.2, printed p. 51 / PDF p. 59):
Suppose that `R` is an integral domain (`[CommRing R] [IsDomain R]`), `1 ≤ n`, and
`f = a_0 + a_1 x + ... + a_n x^n ∈ R[X]` (`f.natDegree ≤ n`) where `a_0, ..., a_n` are relatively
prime (`IsGarlingRelativelyPrime`). Suppose that `p` is a prime in `R` which divides
`a_1, ..., a_n`, does not divide `a_0`, and is such that `p^2` does not divide `a_n`.
Then `f.natDegree = n` and `f` is irreducible in `R[X]`. -/
theorem exercise_5_6 {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {n : ℕ} {p : R}
    (hn : 1 ≤ n)
    (hdeg_le : f.natDegree ≤ n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hp : Prime p)
    (hdvd : ∀ i, 1 ≤ i → i ≤ n → p ∣ f.coeff i)
    (hndvd_0 : ¬ (p ∣ f.coeff 0))
    (hndvd_sq : ¬ (p ^ 2 ∣ f.coeff n)) :
    f.natDegree = n ∧ Irreducible f ∧ IsGarlingIrreducible f := by
  classical
  have hfn_ne0 : f.coeff n ≠ 0 := fun hz => hndvd_sq (hz ▸ dvd_zero (p ^ 2))
  have hf0 : f ≠ 0 := fun hz => hfn_ne0 (by simp [hz])
  have hdeg : f.natDegree = n := le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hfn_ne0)
  have hirr : Irreducible f := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hg0 : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
      have hg_pos : 1 ≤ g.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop hgh hgu
      have hh_pos : 1 ≤ h.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop (hgh.trans (mul_comm g h)) hhu
      have hsum_deg : g.natDegree + h.natDegree = n := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      have hc0_mul : g.coeff 0 * h.coeff 0 = f.coeff 0 := by
        rw [hgh, Polynomial.mul_coeff_zero]
      have hndvd_g0 : ¬ (p ∣ g.coeff 0) :=
        fun hd => hndvd_0 (hc0_mul ▸ dvd_mul_of_dvd_left hd _)
      have hndvd_h0 : ¬ (p ∣ h.coeff 0) :=
        fun hd => hndvd_0 (hc0_mul ▸ dvd_mul_of_dvd_right hd _)
      let Sg : Finset ℕ := (Finset.range (g.natDegree + 1)).filter (fun i => ¬ (p ∣ g.coeff i))
      let Sh : Finset ℕ := (Finset.range (h.natDegree + 1)).filter (fun j => ¬ (p ∣ h.coeff j))
      have hSg_ne : Sg.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨by simp, hndvd_g0⟩⟩
      have hSh_ne : Sh.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨by simp, hndvd_h0⟩⟩
      let r : ℕ := Sg.max' hSg_ne
      let s : ℕ := Sh.max' hSh_ne
      have hr_mem : r ∈ Sg := Finset.max'_mem Sg hSg_ne
      have hs_mem : s ∈ Sh := Finset.max'_mem Sh hSh_ne
      have hr_le : r ≤ g.natDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hr_mem).1)
      have hs_le : s ≤ h.natDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hs_mem).1)
      have hr_ndvd : ¬ (p ∣ g.coeff r) := (Finset.mem_filter.mp hr_mem).2
      have hs_ndvd : ¬ (p ∣ h.coeff s) := (Finset.mem_filter.mp hs_mem).2
      have hr_above : ∀ i, r < i → p ∣ g.coeff i := by
        intro i hi
        by_cases hi_le : i ≤ g.natDegree
        · by_contra hni
          have himem : i ∈ Sg :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), hni⟩
          have hle_r : i ≤ r := Finset.le_max' Sg i himem
          omega
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          exact dvd_zero p
      have hs_above : ∀ j, s < j → p ∣ h.coeff j := by
        intro j hj
        by_cases hj_le : j ≤ h.natDegree
        · by_contra hnj
          have hjmem : j ∈ Sh :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le), hnj⟩
          have hle_s : j ≤ s := Finset.le_max' Sh j hjmem
          omega
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          exact dvd_zero p
      by_cases hrs_pos : 1 ≤ r + s
      · have hrs_le_n : r + s ≤ n := by omega
        have hdvd_rs : p ∣ f.coeff (r + s) := hdvd (r + s) hrs_pos hrs_le_n
        rw [hgh, Polynomial.coeff_mul] at hdvd_rs
        have hmem_anti : (r, s) ∈ Finset.antidiagonal (r + s) := Finset.mem_antidiagonal.mpr rfl
        rw [← Finset.add_sum_erase _ _ hmem_anti] at hdvd_rs
        have hdvd_rest : p ∣ ∑ x ∈ (Finset.antidiagonal (r + s)).erase (r, s),
            g.coeff x.1 * h.coeff x.2 := by
          refine Finset.dvd_sum fun x hx => ?_
          have hx_ne : x ≠ (r, s) := (Finset.mem_erase.mp hx).1
          have hx_sum : x.1 + x.2 = r + s :=
            Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hx)
          have hgt_or : r < x.1 ∨ s < x.2 := by
            by_contra hle
            push Not at hle
            have hx1 : x.1 = r := by omega
            have hx2 : x.2 = s := by omega
            exact hx_ne (Prod.ext hx1 hx2)
          rcases hgt_or with h1 | h2
          · exact dvd_mul_of_dvd_left (hr_above x.1 h1) _
          · exact dvd_mul_of_dvd_right (hs_above x.2 h2) _
        have hdvd_prod : p ∣ g.coeff r * h.coeff s := (dvd_add_left hdvd_rest).mp hdvd_rs
        rcases hp.dvd_or_dvd hdvd_prod with h1 | h2
        · exact hr_ndvd h1
        · exact hs_ndvd h2
      · have hr0 : r = 0 := by omega
        have hs0 : s = 0 := by omega
        have hdvd_glc : p ∣ g.coeff g.natDegree := hr_above g.natDegree (by omega)
        have hdvd_hlc : p ∣ h.coeff h.natDegree := hs_above h.natDegree (by omega)
        have hlead_mul : f.coeff n = g.coeff g.natDegree * h.coeff h.natDegree := by
          rw [← hdeg, ← Polynomial.leadingCoeff, hgh, Polynomial.leadingCoeff_mul,
            Polynomial.leadingCoeff, Polynomial.leadingCoeff]
        have hdvd_sq : p ^ 2 ∣ f.coeff n := by
          rw [sq, hlead_mul]
          exact mul_dvd_mul hdvd_glc hdvd_hlc
        exact hndvd_sq hdvd_sq
  exact ⟨hdeg, hirr, (isGarlingIrreducible_iff f).mpr hirr⟩

/-- **Exercise 5.6 (Garling explicit sum form `a_0 + a_1 x + ... + a_n x^n`)** (§5.2, p. 51). -/
theorem exercise_5_6_garling {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hn : 1 ≤ n) (a : Fin (n + 1) → R) {p : R}
    (hcop : IsGarlingRelativelyPrime (Set.range a))
    (hp : IsGarlingPrime p)
    (hdvd : ∀ i : Fin (n + 1), 1 ≤ (i : ℕ) → p ∣ a i)
    (hndvd_0 : ¬ (p ∣ a ⟨0, Nat.zero_lt_succ n⟩))
    (hndvd_sq : ¬ (p ^ 2 ∣ a ⟨n, Nat.lt_succ_self n⟩)) :
    let f : R[X] := ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)
    IsGarlingIrreducible f ∧ Irreducible f := by
  intro f
  have hcoeff : ∀ k : ℕ, f.coeff k = if hk : k < n + 1 then a ⟨k, hk⟩ else 0 := by
    intro k
    dsimp [f]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hk : k < n + 1
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp [hk]
      · intro j _ hjk
        have hval : (j : ℕ) ≠ k := fun hv => hjk (Fin.ext hv)
        simp [hval]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · simp only [hk, ↓reduceDIte]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hval : (j : ℕ) ≠ k := by omega
      simp [hval]
  have hdeg_le : f.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hcoeff k]
    have hnot : ¬ (k < n + 1) := by omega
    simp [hnot]
  have hfun : (fun i : Fin (n + 1) => f.coeff i) = a :=
    funext fun i => by rw [hcoeff i]; simp [i.isLt]
  rw [← hfun] at hcop
  have hres := exercise_5_6 hn hdeg_le hcop ((isGarlingPrime_iff p).mp hp)
    (fun i hi1 hin => by
      have hi_lt : i < n + 1 := by omega
      rw [hcoeff i]
      simp only [hi_lt, ↓reduceDIte]
      exact hdvd ⟨i, hi_lt⟩ hi1)
    (by
      rw [hcoeff 0]
      simp only [Nat.zero_lt_succ n, ↓reduceDIte]
      exact hndvd_0)
    (by
      rw [hcoeff n]
      simp only [Nat.lt_succ_self n, ↓reduceDIte]
      exact hndvd_sq)
  exact ⟨hres.2.2, hres.2.1⟩

/-- **Exercise 5.6 — Exact `iff` characterization across all `n : ℕ`** (§5.2, p. 51):
Under the hypotheses of `Exercise 5.6`, `f` is irreducible if and only if `1 ≤ n`. -/
theorem exercise_5_6_iff_pos {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {n : ℕ} {p : R}
    (hdeg_le : f.natDegree ≤ n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hp : Prime p)
    (hdvd : ∀ i, 1 ≤ i → i ≤ n → p ∣ f.coeff i)
    (hndvd_0 : ¬ (p ∣ f.coeff 0))
    (hndvd_sq : ¬ (p ^ 2 ∣ f.coeff n)) :
    Irreducible f ↔ 1 ≤ n := by
  constructor
  · intro hirr
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hd0 : f.natDegree = 0 := by omega
    have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    rcases hcop with ⟨_, ⟨_, hmax⟩⟩
    have hu0 : IsUnit (f.coeff 0) :=
      isUnit_of_dvd_one (hmax (f.coeff 0) (by rintro _ ⟨i, rfl⟩; fin_cases i; exact dvd_rfl))
    exact hirr.not_isUnit (hfC ▸ hu0.map Polynomial.C)
  · intro hn
    exact (exercise_5_6 hn hdeg_le hcop hp hdvd hndvd_0 hndvd_sq).2.1

/-- **Exercise 5.7 — Degree-zero counterexample to the literal printed statement** (§5.2, p. 52):
At `n = 0`, for every prime number `p : ℕ`, `X^0 - p = 1 - p` in `ℚ[X]` is a non-zero constant
unit (`1 - p ≠ 0` since `p ≥ 2`) and hence not irreducible in `ℚ[X]`. -/
theorem exercise_5_7_zero_counterexample {p : ℕ} (hp : Nat.Prime p) :
    IsUnit (Polynomial.X ^ 0 - Polynomial.C (p : ℚ) : ℚ[X]) ∧
    ¬ Irreducible (Polynomial.X ^ 0 - Polynomial.C (p : ℚ) : ℚ[X]) ∧
    ¬ IsGarlingIrreducible (Polynomial.X ^ 0 - Polynomial.C (p : ℚ) : ℚ[X]) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hne : (1 : ℚ) - (p : ℚ) ≠ 0 := by
    have hlt : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (show 1 < p by omega)
    linarith
  have heq : (Polynomial.X ^ 0 - Polynomial.C (p : ℚ) : ℚ[X]) = Polynomial.C (1 - (p : ℚ)) := by
    simp [map_sub]
  have hu : IsUnit (Polynomial.X ^ 0 - Polynomial.C (p : ℚ) : ℚ[X]) :=
    heq ▸ (isUnit_iff_ne_zero.mpr hne).map Polynomial.C
  exact ⟨hu, fun hi => hi.not_isUnit hu,
    fun hi => (isGarlingIrreducible_iff _).mp hi |>.not_isUnit hu⟩

/-- **Exercise 5.7 (`ℤ[X]` companion)** (§5.2, p. 52):
For every prime number `p : ℕ` and every `n ≥ 1`, `X^n - p` is irreducible in `ℤ[X]`. -/
theorem exercise_5_7_int {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (p : ℤ) : ℤ[X]) := by
  let f : ℤ[X] := Polynomial.X ^ n - Polynomial.C (p : ℤ)
  have hmon : f.Monic := Polynomial.monic_X_pow_sub_C (p : ℤ) (by omega)
  have hdeg : f.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i) :=
    isGarlingRelativelyPrime_coeffs_of_monic hmon hdeg
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : ∀ i < n, (p : ℤ) ∣ f.coeff i := by
    intro i hi
    dsimp [f]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    have hi_ne_n : i ≠ n := by omega
    simp only [hi_ne_n, ↓reduceIte, zero_sub]
    by_cases hi0 : i = 0
    · simp [hi0]
    · simp [hi0]
  have hndvd_n : ¬ ((p : ℤ) ∣ f.coeff n) := by
    have hfn1 : f.coeff n = 1 := by
      rw [← hdeg, ← Polynomial.leadingCoeff, hmon.leadingCoeff]
    rw [hfn1]
    exact fun hd => hpZ.not_isUnit (isUnit_of_dvd_one hd)
  have hndvd_sq : ¬ ((p : ℤ) ^ 2 ∣ f.coeff 0) := by
    have hf0 : f.coeff 0 = -(p : ℤ) := by
      dsimp [f]
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have h0n : (0 : ℕ) ≠ n := by omega
      simp [h0n]
    rw [hf0, dvd_neg]
    intro hd
    have hd_nat : p ^ 2 ∣ p := Int.natCast_dvd_natCast.mp (by simpa [ Nat.cast_pow ] using hd)
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hd_nat
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  exact (theorem_5_2 hn (le_of_eq hdeg) hcop hpZ hdvd hndvd_n hndvd_sq).2.1

/-- **Exercise 5.7** (§5.2, printed p. 52 / PDF p. 60):
If `p` is a prime number and `1 ≤ n`, then `X^n - p` is irreducible in `ℚ[X]`. -/
theorem exercise_5_7 {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (p : ℚ) : ℚ[X]) ∧
    IsGarlingIrreducible (Polynomial.X ^ n - Polynomial.C (p : ℚ) : ℚ[X]) := by
  let fZ : ℤ[X] := Polynomial.X ^ n - Polynomial.C (p : ℤ)
  have hirrZ : Irreducible fZ := exercise_5_7_int hp hn
  have hgauss := (corollary_gauss_lemma ℚ fZ).mp hirrZ
  rcases hgauss with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
  · exfalso
    have hd := congrArg Polynomial.natDegree hC
    rw [Polynomial.natDegree_X_pow_sub_C (R := ℤ), Polynomial.natDegree_C] at hd
    omega
  · have hmap_eq : fZ.map (algebraMap ℤ ℚ) =
        (Polynomial.X ^ n - Polynomial.C (p : ℚ) : ℚ[X]) := by
      dsimp [fZ]
      simp
    rw [hmap_eq] at hmap_irr
    exact ⟨hmap_irr, (isGarlingIrreducible_iff _).mpr hmap_irr⟩

/-- **Exercise 5.7 — Exact `iff` characterization across all `n : ℕ`** (§5.2, p. 52):
For any prime number `p : ℕ`, `X^n - p` is irreducible in `ℚ[X]` if and only if `1 ≤ n`. -/
theorem exercise_5_7_iff {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (p : ℚ) : ℚ[X]) ↔ 1 ≤ n := by
  constructor
  · intro hirr
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact (exercise_5_7_zero_counterexample hp).2.1 hirr
  · exact fun hn => (exercise_5_7 hp hn).1

/-- Helper for `Exercises 5.8` and `5.9`: for any prime `p` and `n ≥ 1`, the positive real `n`-th
root `(p : ℝ) ^ (1 / n)` is algebraic over `ℚ` with minimal polynomial `X^n - p` of degree `n`. -/
theorem real_rpow_inv_nat_minpoly_of_prime {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    let α : ℝ := (p : ℝ) ^ ((1 : ℝ) / (n : ℝ))
    α ^ n = (p : ℝ) ∧
    IsGarlingAlgebraic ℚ α ∧
    minpoly ℚ α = Polynomial.X ^ n - Polynomial.C (p : ℚ) ∧
    (minpoly ℚ α).natDegree = n := by
  intro α
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hn_ne0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : α ^ n = (p : ℝ) := by
    dsimp [α]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg, one_div_mul_cancel hn_ne0, Real.rpow_one]
  let P : ℚ[X] := Polynomial.X ^ n - Polynomial.C (p : ℚ)
  have hP_mon : P.Monic := Polynomial.monic_X_pow_sub_C (p : ℚ) (by omega)
  have hP_irr : Irreducible P := (exercise_5_7 hp hn).1
  have hP_eval : Polynomial.aeval α P = 0 := by
    dsimp [P]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    simp [hpow]
  have hmin : minpoly ℚ α = P :=
    (minpoly.eq_of_irreducible_of_monic hP_irr hP_eval hP_mon).symm
  have hdeg : (minpoly ℚ α).natDegree = n := by
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C
  exact ⟨hpow, ⟨P, hP_mon.ne_zero, hP_eval⟩, hmin, hdeg⟩

/-- **Exercise 5.8** (§5.2, printed p. 52 / PDF p. 60):
Let `A` (`algebraicSubfield ℚ ℝ` / `algebraicIntermediateField ℚ ℝ`) be the subfield of `ℝ`
consisting of the algebraic numbers in `ℝ`. Then `[A : ℚ] = ∞`. -/
theorem exercise_5_8 :
    extDegree ℚ (algebraicSubfield ℚ ℝ) = ⊤ ∧
    extDegree ℚ (algebraicIntermediateField ℚ ℝ) = ⊤ ∧
    IsInfiniteExtension ℚ (algebraicSubfield ℚ ℝ) ∧
    IsInfiniteExtension ℚ (algebraicIntermediateField ℚ ℝ) := by
  let A := algebraicIntermediateField ℚ ℝ
  have hbound : ∀ n : ℕ, 1 ≤ n → (n : ℕ∞) ≤ extDegree ℚ A := by
    intro n hn
    obtain ⟨hpow, hα_alg, _, _⟩ := real_rpow_inv_nat_minpoly_of_prime Nat.prime_two hn
    norm_num only [Nat.cast_ofNat] at hpow hα_alg
    let αA : A := ⟨(2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)), hα_alg⟩
    let P : ℚ[X] := Polynomial.X ^ n - Polynomial.C (2 : ℚ)
    have hP_mon : P.Monic := Polynomial.monic_X_pow_sub_C (2 : ℚ) (by omega)
    have hP_irr : Irreducible P := (exercise_5_7 Nat.prime_two hn).1
    have hP_evalA : Polynomial.aeval αA P = 0 := by
      apply Subtype.ext
      have hval : ((Polynomial.aeval αA P : A) : ℝ) = Polynomial.aeval (αA : ℝ) P :=
        (Polynomial.aeval_algHom_apply A.val αA P).symm
      change ((Polynomial.aeval αA P : A) : ℝ) = 0
      rw [hval]
      dsimp [P, αA]
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      simpa using sub_eq_zero.mpr hpow
    have hminA : minpoly ℚ αA = P :=
      (minpoly.eq_of_irreducible_of_monic hP_irr hP_evalA hP_mon).symm
    have hαA_alg : IsGarlingAlgebraic ℚ αA := ⟨P, hP_mon.ne_zero, hP_evalA⟩
    have hdeg_adj : extDegree ℚ (IntermediateField.adjoin ℚ ({αA} : Set A)) = (n : ℕ∞) := by
      rw [(theorem_4_4 αA).2 hαA_alg |>.2, hminA]
      exact congrArg Nat.cast (Polynomial.natDegree_X_pow_sub_C (R := ℚ))
    rw [theorem_4_2 ℚ (IntermediateField.adjoin ℚ ({αA} : Set A)) A, hdeg_adj]
    calc (n : ℕ∞) = 1 * (n : ℕ∞) := (one_mul _).symm
      _ ≤ extDegree (IntermediateField.adjoin ℚ ({αA} : Set A)) A * (n : ℕ∞) :=
          mul_le_mul_of_nonneg_right (one_le_extDegree _ _) zero_le
  have htopA : extDegree ℚ A = ⊤ := by
    by_contra hne
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hne
    have hle : ((d + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
      have hb := hbound (d + 1) (by omega)
      rwa [← hd] at hb
    exact absurd (Nat.cast_le.mp hle) (by omega)
  have htopSub : extDegree ℚ (algebraicSubfield ℚ ℝ) = ⊤ := htopA
  exact ⟨htopSub, htopA, htopSub, htopA⟩

/-- Indexed family `p ↦ 2^{1/p} ∈ ℝ` over all prime numbers `p` (§5.2, Ex. 5.9, p. 52). -/
noncomputable def primeRootsOfTwoFamily (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / (p.1 : ℝ))

/-- Garling's set `{2^{1/p} : p prime} ⊆ ℝ` (§5.2, Ex. 5.9, p. 52). -/
def primeRootsOfTwoSet : Set ℝ :=
  {x : ℝ | ∃ p : ℕ, Nat.Prime p ∧ x = (2 : ℝ) ^ ((1 : ℝ) / (p : ℝ))}

/-- **Exercise 5.9** (§5.2, printed p. 52 / PDF p. 60):
The set `{2^{1/p} : p prime}` (`primeRootsOfTwoSet`, and the indexed family `primeRootsOfTwoFamily`)
is linearly independent over `ℚ` (`IsLinearlyIndependent ℚ` and `LinearIndependent ℚ`). -/
theorem exercise_5_9 :
    IsLinearlyIndependent ℚ primeRootsOfTwoSet ∧
    LinearIndependent ℚ primeRootsOfTwoFamily := by
  classical
  have hli : LinearIndependent ℚ primeRootsOfTwoFamily := by
    rw [linearIndependent_iff']
    intro s g hsum p₀ hp₀
    let N : ℕ := ∏ p ∈ s, p.1
    have hN_pos : 1 ≤ N := Finset.one_le_prod fun p _ => p.2.pos
    obtain ⟨_, _, _, hdegγ⟩ := real_rpow_inv_nat_minpoly_of_prime Nat.prime_two hN_pos
    norm_num only [Nat.cast_ofNat] at hdegγ
    let γ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / (N : ℝ))
    have hγ_pow : ∀ p ∈ s, γ ^ (N / p.1) = primeRootsOfTwoFamily p := by
      intro p hp_mem
      have hdvd : p.1 ∣ N := Finset.dvd_prod_of_mem (fun q : {p : ℕ // Nat.Prime p} => q.1) hp_mem
      have hmul_N : N / p.1 * p.1 = N := Nat.div_mul_cancel hdvd
      have hm_ne0_nat : N / p.1 ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hmul_N
        omega
      dsimp [γ, primeRootsOfTwoFamily]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      have hp_ne0 : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
      have hm_ne0 : ((N / p.1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_ne0_nat
      have hN_cast : (N : ℝ) = ((N / p.1 : ℕ) : ℝ) * (p.1 : ℝ) := by exact_mod_cast hmul_N.symm
      rw [hN_cast]
      field_simp [hp_ne0, hm_ne0]
    let P : ℚ[X] := ∑ p ∈ s, Polynomial.monomial (N / p.1) (g p)
    have hP_eval : Polynomial.aeval γ P = 0 := by
      dsimp [P]
      rw [map_sum]
      have hterm : ∀ p ∈ s,
          Polynomial.aeval γ (Polynomial.monomial (N / p.1) (g p)) =
            g p • primeRootsOfTwoFamily p := by
        intro p hp_mem
        rw [Polynomial.aeval_monomial, hγ_pow p hp_mem, Algebra.smul_def]
      rw [Finset.sum_congr rfl hterm]
      exact hsum
    have hP_zero : P = 0 := by
      by_contra hP_ne0
      have hP_deg_lt : P.natDegree < N := by
        have hN_gt0 : 0 < N := by omega
        have hle : P.natDegree ≤ N - 1 := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro k hk
          dsimp [P]
          rw [Polynomial.finsetSum_coeff]
          refine Finset.sum_eq_zero fun p _ => ?_
          rw [Polynomial.coeff_monomial]
          have hdiv_lt : N / p.1 < N := Nat.div_lt_self hN_gt0 p.2.one_lt
          have hne : N / p.1 ≠ k := by omega
          simp [hne]
        omega
      have hdvd : minpoly ℚ γ ∣ P := minpoly.dvd ℚ γ hP_eval
      have hdeg_le : (minpoly ℚ γ).natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hP_ne0
      dsimp [γ] at hdeg_le
      rw [hdegγ] at hdeg_le
      omega
    have hcoeff0 : P.coeff (N / p₀.1) = 0 := by simp [hP_zero]
    dsimp [P] at hcoeff0
    rw [Polynomial.finsetSum_coeff] at hcoeff0
    rw [Finset.sum_eq_single p₀] at hcoeff0
    · simpa [Polynomial.coeff_monomial] using hcoeff0
    · intro p hp_mem hp_ne
      rw [Polynomial.coeff_monomial]
      have hdiv_ne : N / p.1 ≠ N / p₀.1 := by
        intro heq
        have hdvd_p : p.1 ∣ N :=
          Finset.dvd_prod_of_mem (fun q : {p : ℕ // Nat.Prime p} => q.1) hp_mem
        have hdvd_p0 : p₀.1 ∣ N :=
          Finset.dvd_prod_of_mem (fun q : {p : ℕ // Nat.Prime p} => q.1) hp₀
        have hm1 : N / p.1 * p.1 = N := Nat.div_mul_cancel hdvd_p
        have hm2 : N / p₀.1 * p₀.1 = N := Nat.div_mul_cancel hdvd_p0
        have hm_pos : 0 < N / p₀.1 := by
          apply Nat.pos_of_ne_zero
          intro hz
          rw [hz, zero_mul] at hm2
          omega
        rw [heq] at hm1
        have hp_eq : p.1 = p₀.1 := Nat.mul_left_cancel hm_pos (hm1.trans hm2.symm)
        exact hp_ne (Subtype.ext hp_eq)
      simp [hdiv_ne]
    · intro habs
      exact absurd hp₀ habs
  have hrange : primeRootsOfTwoSet = Set.range primeRootsOfTwoFamily := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  exact ⟨hrange ▸ (isLinearlyIndependent_iff _).mpr hli.linearIndepOn_id, hli⟩

/-- Gaussian rationals `ℚ(i)` realized as `IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)`
(§5.2, Ex. 5.10, p. 52). -/
noncomputable abbrev gaussianRationals : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)

private theorem extDegree_adjoin_real_and_I {α : ℝ} {n : ℕ}
    (hdeg_Qα : extDegree ℚ (IntermediateField.adjoin ℚ ({(α : ℂ)} : Set ℂ)) = (n : ℕ∞)) :
    extDegree ℚ (IntermediateField.adjoin ℚ ({(α : ℂ), Complex.I} : Set ℂ)) = 2 * (n : ℕ∞) := by
  let αC : ℂ := (α : ℂ)
  let Qα : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({αC} : Set ℂ)
  let Rsub : IntermediateField ℚ ℂ :=
    { Complex.ofRealHom.fieldRange with
      algebraMap_mem' := fun q => ⟨(q : ℝ), by simp⟩ }
  have hQα_le_R : Qα ≤ Rsub := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨α, rfl⟩
  have hI_not_Qα : Complex.I ∉ Qα := by
    intro hmem
    obtain ⟨r, hr⟩ := hQα_le_R hmem
    have him := congrArg Complex.im hr
    simp at him
  let M : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({αC, Complex.I} : Set ℂ)
  have hQα_le_M : Qα ≤ M := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  let inc_α : Qα →+* M := Subfield.inclusion hQα_le_M
  let _ : Algebra Qα M := inc_α.toAlgebra
  let iM : M := ⟨Complex.I, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let P_Qα : Qα[X] := Polynomial.X ^ 2 + 1
  have hPQα_mon : P_Qα.Monic := Polynomial.monic_X_pow_add_C 1 (by decide)
  have hPQα_eval : Polynomial.aeval iM P_Qα = 0 := by
    apply Subtype.ext
    dsimp [P_Qα]
    rw [map_add, map_pow, Polynomial.aeval_X, map_one]
    simp [iM, Complex.I_sq]
  have hiM_alg : IsGarlingAlgebraic Qα iM := ⟨P_Qα, hPQα_mon.ne_zero, hPQα_eval⟩
  have hiM_int : IsIntegral Qα iM := (isGarlingAlgebraic_iff_isIntegral Qα iM).mp hiM_alg
  have hdvd_iM : minpoly Qα iM ∣ P_Qα := minpoly.dvd Qα iM hPQα_eval
  have hdeg_iM_le : (minpoly Qα iM).natDegree ≤ 2 := by
    calc (minpoly Qα iM).natDegree ≤ P_Qα.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd_iM hPQα_mon.ne_zero
      _ = 2 := Polynomial.natDegree_X_pow_add_C
  have hdeg_iM_ne1 : (minpoly Qα iM).natDegree ≠ 1 := by
    intro hd1
    have hmon_m := minpoly.monic hiM_int
    have hm_eq : minpoly Qα iM = Polynomial.C ((minpoly Qα iM).coeff 0) + Polynomial.X := by
      ext k
      rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X]
      rcases k with _ | _ | k
      · simp
      · have hlc : (minpoly Qα iM).coeff 1 = 1 := by
          rw [← hd1, ← Polynomial.leadingCoeff, hmon_m.leadingCoeff]
        simp [hlc]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    have hev := minpoly.aeval Qα iM
    rw [hm_eq, map_add, Polynomial.aeval_C, Polynomial.aeval_X] at hev
    have hiM_eq : iM = -(algebraMap Qα M ((minpoly Qα iM).coeff 0)) := eq_neg_of_add_eq_zero_right hev
    have hval := congrArg Subtype.val hiM_eq
    change Complex.I = -(((minpoly Qα iM).coeff 0 : Qα) : ℂ) at hval
    exact hI_not_Qα (hval ▸ neg_mem (((minpoly Qα iM).coeff 0).2))
  have hdeg_iM_pos : 0 < (minpoly Qα iM).natDegree := minpoly.natDegree_pos hiM_int
  have hdeg_iM_eq2 : (minpoly Qα iM).natDegree = 2 := by omega
  have hM_top_Qα : IntermediateField.adjoin Qα ({iM} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxM : (x : ℂ) ∈ M := x.2
    let F_Qα : IntermediateField ℚ ℂ :=
      { (IntermediateField.adjoin Qα ({iM} : Set M)).toSubfield.map M.val.toRingHom with
        algebraMap_mem' := fun q =>
          ⟨algebraMap Qα M (algebraMap ℚ Qα q),
            (IntermediateField.adjoin Qα ({iM} : Set M)).algebraMap_mem _, rfl⟩ }
    have hle_M : M ≤ F_Qα := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rcases hz with rfl | hzI
      · let αQα : Qα := IntermediateField.AdjoinSimple.gen ℚ αC
        exact ⟨algebraMap Qα M αQα,
          (IntermediateField.adjoin Qα ({iM} : Set M)).algebraMap_mem αQα, rfl⟩
      · rw [Set.mem_singleton_iff.mp hzI]
        exact ⟨iM, IntermediateField.mem_adjoin_simple_self Qα iM, rfl⟩
    obtain ⟨y, hy_mem, hy_eq⟩ := hle_M hxM
    have hxy : y = x := Subtype.ext hy_eq
    exact hxy ▸ hy_mem
  have hdeg_Qα_M : extDegree Qα M = 2 := by
    have hdeg_adj : extDegree Qα (IntermediateField.adjoin Qα ({iM} : Set M)) = 2 := by
      rw [(theorem_4_4 iM).2 hiM_alg |>.2, hdeg_iM_eq2]
      rfl
    let eTop : IntermediateField.adjoin Qα ({iM} : Set M) ≃ₐ[Qα] M :=
      (IntermediateField.equivOfEq hM_top_Qα).trans IntermediateField.topEquiv
    have hfin_adj : IsFiniteExtension Qα (IntermediateField.adjoin Qα ({iM} : Set M)) := by
      unfold IsFiniteExtension
      rw [hdeg_adj]
      exact (by decide : (2 : ℕ∞) < ⊤)
    have _ : Module.Finite Qα (IntermediateField.adjoin Qα ({iM} : Set M)) :=
      (isFiniteExtension_iff_moduleFinite Qα _).mp hfin_adj
    have _ : Module.Finite Qα M := Module.Finite.equiv eTop.toLinearEquiv
    rw [extDegree_eq_finrank Qα M, ← eTop.toLinearEquiv.finrank_eq,
      ← extDegree_eq_finrank Qα (IntermediateField.adjoin Qα ({iM} : Set M)), hdeg_adj]
  have _ : IsScalarTower ℚ Qα M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [theorem_4_2 ℚ Qα M, hdeg_Qα_M, hdeg_Qα]

/-- General criterion for `Exercise 5.10`: any monic polynomial `f ∈ ℚ[X]` that is irreducible in
`ℚ[X]` and has a real root `α ∈ ℝ` remains irreducible in `ℚ(i)[X]` (`gaussianRationals[X]`). -/
theorem irreducible_gaussianRationals_of_irreducible_rat_of_real_root
    {f : ℚ[X]} (hmon : f.Monic) (hirr : Irreducible f) {α : ℝ}
    (hroot : Polynomial.aeval α f = 0) :
    Irreducible (f.map (algebraMap ℚ gaussianRationals)) ∧
    IsGarlingIrreducible (f.map (algebraMap ℚ gaussianRationals)) := by
  let n : ℕ := f.natDegree
  let αC : ℂ := (α : ℂ)
  have hrootC : Polynomial.aeval αC f = 0 := by
    have hhom := (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) α f).symm
    change ((Polynomial.aeval α f : ℝ) : ℂ) = Polynomial.aeval αC f at hhom
    rw [← hhom, hroot, Complex.ofReal_zero]
  have hmin_αC : minpoly ℚ αC = f :=
    (minpoly.eq_of_irreducible_of_monic hirr hrootC hmon).symm
  have hαC_alg : IsGarlingAlgebraic ℚ αC := ⟨f, hmon.ne_zero, hrootC⟩
  have hdeg_Qα : extDegree ℚ (IntermediateField.adjoin ℚ ({αC} : Set ℂ)) = (n : ℕ∞) := by
    rw [(theorem_4_4 αC).2 hαC_alg |>.2, hmin_αC]
  have hdeg_Q_M : extDegree ℚ (IntermediateField.adjoin ℚ ({αC, Complex.I} : Set ℂ)) =
      2 * (n : ℕ∞) :=
    extDegree_adjoin_real_and_I hdeg_Qα
  let P_I : ℚ[X] := Polynomial.X ^ 2 + 1
  have hPI_mon : P_I.Monic := Polynomial.monic_X_pow_add_C 1 (by decide)
  have hPI_deg : P_I.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hPI_irr : Irreducible P_I := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hg0 : g ≠ 0 := fun hz => hPI_mon.ne_zero (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hPI_mon.ne_zero (by rw [hgh, hz, mul_zero])
      have hgd_pos : 0 < g.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hg0 hgu)
      have hhd_pos : 0 < h.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hh0 hhu)
      have hsum : g.natDegree + h.natDegree = 2 := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hPI_deg]
      have hg1 : g.natDegree = 1 := by omega
      have hglc : g.coeff 1 ≠ 0 := by
        rw [← hg1, ← Polynomial.leadingCoeff]
        exact Polynomial.leadingCoeff_ne_zero.mpr hg0
      let r : ℚ := -g.coeff 0 / g.coeff 1
      have hg_eq : g = Polynomial.C (g.coeff 0) + Polynomial.C (g.coeff 1) * Polynomial.X := by
        ext k
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X]
        rcases k with _ | _ | k
        · simp
        · simp
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < k + 2 by omega)]
          simp
      have hg_eval : g.eval r = 0 := by
        rw [hg_eq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        dsimp [r]
        field_simp [hglc]
        ring
      have hPI_eval : P_I.eval r = 0 := by
        rw [hgh, Polynomial.eval_mul, hg_eval, zero_mul]
      have hPI_pos : 0 < P_I.eval r := by
        dsimp [P_I]
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        positivity
      linarith
  have hPI_eval_I : Polynomial.aeval Complex.I P_I = 0 := by
    dsimp [P_I]
    simp [Complex.I_sq]
  have hI_alg : IsGarlingAlgebraic ℚ Complex.I := ⟨P_I, hPI_mon.ne_zero, hPI_eval_I⟩
  have hmin_I : minpoly ℚ Complex.I = P_I :=
    (minpoly.eq_of_irreducible_of_monic hPI_irr hPI_eval_I hPI_mon).symm
  have hdeg_Qi : extDegree ℚ gaussianRationals = 2 := by
    rw [(theorem_4_4 Complex.I).2 hI_alg |>.2, hmin_I, hPI_deg]
    rfl
  let M : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({αC, Complex.I} : Set ℂ)
  have hQi_le_M : gaussianRationals ≤ M := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  let inc_i : gaussianRationals →+* M := Subfield.inclusion hQi_le_M
  let _ : Algebra gaussianRationals M := inc_i.toAlgebra
  have _ : IsScalarTower ℚ gaussianRationals M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have htower_i : extDegree ℚ M = extDegree gaussianRationals M * 2 := by
    rw [theorem_4_2 ℚ gaussianRationals M, hdeg_Qi]
  have hfin_Qi_M : extDegree gaussianRationals M < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have h1 : extDegree ℚ M = ⊤ := by
      rw [htower_i, htop]
      exact WithTop.top_mul (by decide)
    rw [hdeg_Q_M] at h1
    exact absurd h1 (ne_of_lt (WithTop.mul_lt_top (by decide : (2 : ℕ∞) < ⊤) (ENat.natCast_lt_top n)))
  have _ : Module.Finite gaussianRationals M :=
    (isFiniteExtension_iff_moduleFinite gaussianRationals M).mp hfin_Qi_M
  let d : ℕ := Module.finrank gaussianRationals M
  have hd : extDegree gaussianRationals M = (d : ℕ∞) := extDegree_eq_finrank gaussianRationals M
  have hd_eq : d = n := by
    have heq : ((d * 2 : ℕ) : ℕ∞) = ((2 * n : ℕ) : ℕ∞) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ← hd, ← htower_i, hdeg_Q_M, Nat.cast_mul, Nat.cast_ofNat]
    have hnat : d * 2 = 2 * n := Nat.cast_injective heq
    omega
  let αM : M := ⟨αC, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hM_top_Qi : IntermediateField.adjoin gaussianRationals ({αM} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxM : (x : ℂ) ∈ M := x.2
    let F_Qi : IntermediateField ℚ ℂ :=
      { (IntermediateField.adjoin gaussianRationals ({αM} : Set M)).toSubfield.map M.val.toRingHom with
        algebraMap_mem' := fun q =>
          ⟨algebraMap gaussianRationals M (algebraMap ℚ gaussianRationals q),
            (IntermediateField.adjoin gaussianRationals ({αM} : Set M)).algebraMap_mem _, rfl⟩ }
    have hle_M : M ≤ F_Qi := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rcases hz with rfl | hzI
      · exact ⟨αM, IntermediateField.mem_adjoin_simple_self gaussianRationals αM, rfl⟩
      · rw [Set.mem_singleton_iff.mp hzI]
        let iQi : gaussianRationals := IntermediateField.AdjoinSimple.gen ℚ Complex.I
        exact ⟨algebraMap gaussianRationals M iQi,
          (IntermediateField.adjoin gaussianRationals ({αM} : Set M)).algebraMap_mem iQi, rfl⟩
    obtain ⟨y, hy_mem, hy_eq⟩ := hle_M hxM
    have hxy : y = x := Subtype.ext hy_eq
    exact hxy ▸ hy_mem
  let fQi : gaussianRationals[X] := f.map (algebraMap ℚ gaussianRationals)
  have hfQi_mon : fQi.Monic := hmon.map (algebraMap ℚ gaussianRationals)
  have hfQi_deg : fQi.natDegree = n := hmon.natDegree_map (algebraMap ℚ gaussianRationals)
  have hfQi_eval : Polynomial.aeval αM fQi = 0 := by
    apply Subtype.ext
    have hcomp : Polynomial.aeval αM fQi = Polynomial.aeval αM f := by
      dsimp [fQi]
      rw [Polynomial.aeval_def, Polynomial.eval₂_map,
        ← IsScalarTower.algebraMap_eq ℚ gaussianRationals M, ← Polynomial.aeval_def]
    rw [hcomp]
    have hval : ((Polynomial.aeval αM f : M) : ℂ) = Polynomial.aeval αC f :=
      (Polynomial.aeval_algHom_apply M.val αM f).symm
    change ((Polynomial.aeval αM f : M) : ℂ) = 0
    rw [hval]
    exact hrootC
  have hαM_alg : IsGarlingAlgebraic gaussianRationals αM := ⟨fQi, hfQi_mon.ne_zero, hfQi_eval⟩
  have hαM_int : IsIntegral gaussianRationals αM :=
    (isGarlingAlgebraic_iff_isIntegral gaussianRationals αM).mp hαM_alg
  have hdeg_adj_Qi : extDegree gaussianRationals
      (IntermediateField.adjoin gaussianRationals ({αM} : Set M)) = (n : ℕ∞) := by
    let eTop : IntermediateField.adjoin gaussianRationals ({αM} : Set M) ≃ₐ[gaussianRationals] M :=
      (IntermediateField.equivOfEq hM_top_Qi).trans IntermediateField.topEquiv
    have _ : Module.Finite gaussianRationals
        (IntermediateField.adjoin gaussianRationals ({αM} : Set M)) :=
      Module.Finite.equiv eTop.symm.toLinearEquiv
    rw [extDegree_eq_finrank gaussianRationals _, eTop.toLinearEquiv.finrank_eq,
      ← extDegree_eq_finrank gaussianRationals M, hd, hd_eq]
  have hmin_αM_deg : (minpoly gaussianRationals αM).natDegree = n := by
    have h44 := (theorem_4_4 αM).2 hαM_alg |>.2
    rw [hdeg_adj_Qi] at h44
    exact Nat.cast_injective h44.symm
  have hdvd_fQi : minpoly gaussianRationals αM ∣ fQi :=
    minpoly.dvd gaussianRationals αM hfQi_eval
  obtain ⟨q, hq⟩ := hdvd_fQi
  have hq0 : q ≠ 0 := fun hz => hfQi_mon.ne_zero (by rw [hq, hz, mul_zero])
  have hq_deg0 : q.natDegree = 0 := by
    have hsum := Polynomial.natDegree_mul (minpoly.ne_zero hαM_int) hq0
    rw [← hq, hfQi_deg, hmin_αM_deg] at hsum
    omega
  have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
  have hq1 : q.coeff 0 = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [hfQi_mon.leadingCoeff, Polynomial.leadingCoeff_mul,
      (minpoly.monic hαM_int).leadingCoeff, one_mul, Polynomial.leadingCoeff, hq_deg0] at hlc
    exact hlc.symm
  have hfQi_eq : fQi = minpoly gaussianRationals αM := by
    rw [hq, hqC, hq1, map_one, mul_one]
  have hfQi_irr : Irreducible fQi := hfQi_eq ▸ minpoly.irreducible hαM_int
  exact ⟨hfQi_irr, (isGarlingIrreducible_iff fQi).mpr hfQi_irr⟩

/-- **Exercise 5.10** (§5.2, printed p. 52 / PDF p. 60):
Both `x^5 - 4x + 2` and `x^4 - 4x + 2` are irreducible in `ℚ(i)[X]` (`gaussianRationals[X]`). -/
theorem exercise_5_10 :
    Irreducible (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
      gaussianRationals[X]) ∧
    IsGarlingIrreducible (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
      gaussianRationals[X]) ∧
    Irreducible (Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
      gaussianRationals[X]) ∧
    IsGarlingIrreducible (Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
      gaussianRationals[X]) := by
  -- Part 1: x^5 - 4x + 2
  let f1 : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  have hf1_deg : f1.natDegree = 5 := by dsimp [f1]; compute_degree!
  have hf1_mon : f1.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf1_deg]
    dsimp [f1]; simp
  have hf1_irr : Irreducible f1 := example_5_2_quintic_irreducible.2.1
  have hcont1 : Continuous (fun x : ℝ => x ^ 5 - 4 * x + 2) := by fun_prop
  have hivt1 : (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 5 - 4 * (1 : ℝ) + 2)
      ((0 : ℝ) ^ 5 - 4 * (0 : ℝ) + 2) := by norm_num
  obtain ⟨α1, _, hα1⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont1.continuousOn hivt1
  have hroot1 : Polynomial.aeval α1 f1 = 0 := by
    dsimp [f1]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    simpa [map_ofNat] using hα1
  have hmap1 : f1.map (algebraMap ℚ gaussianRationals) =
      (Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
        gaussianRationals[X]) := by
    dsimp [f1]; simp [map_ofNat]
  have hirr1 := irreducible_gaussianRationals_of_irreducible_rat_of_real_root hf1_mon hf1_irr hroot1
  rw [hmap1] at hirr1
  -- Part 2: x^4 - 4x + 2
  let f2Z : ℤ[X] := Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  have hf2Z_deg : f2Z.natDegree = 4 := by dsimp [f2Z]; compute_degree!
  have hf2Z_mon : f2Z.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf2Z_deg]
    dsimp [f2Z]; simp [Polynomial.coeff_X]
  have hf2Z_irr : Irreducible f2Z := by
    refine (theorem_5_2 (by decide : 1 ≤ 4) (le_of_eq hf2Z_deg)
      (isGarlingRelativelyPrime_coeffs_of_monic hf2Z_mon hf2Z_deg) Int.prime_two ?_ ?_ ?_).2.1
    · intro i hi
      dsimp [f2Z]
      interval_cases i <;> simp [Polynomial.coeff_X]
    · have hc4 : f2Z.coeff 4 = 1 := by
        rw [← hf2Z_deg, ← Polynomial.leadingCoeff, hf2Z_mon.leadingCoeff]
      rw [hc4]; decide
    · have hc0 : f2Z.coeff 0 = 2 := by dsimp [f2Z]; simp [Polynomial.coeff_X]
      rw [hc0]; decide
  let f2 : ℚ[X] := Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  have hf2_deg : f2.natDegree = 4 := by dsimp [f2]; compute_degree!
  have hf2_mon : f2.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf2_deg]
    dsimp [f2]; simp
  have hf2_irr : Irreducible f2 := by
    rcases (corollary_gauss_lemma ℚ f2Z).mp hf2Z_irr with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
    · exfalso
      have hd := congrArg Polynomial.natDegree hC
      rw [hf2Z_deg, Polynomial.natDegree_C] at hd
      omega
    · have hmap_eq : f2Z.map (algebraMap ℤ ℚ) = f2 := by dsimp [f2Z, f2]; simp [map_ofNat]
      rwa [hmap_eq] at hmap_irr
  have hcont2 : Continuous (fun x : ℝ => x ^ 4 - 4 * x + 2) := by fun_prop
  have hivt2 : (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 4 - 4 * (1 : ℝ) + 2)
      ((0 : ℝ) ^ 4 - 4 * (0 : ℝ) + 2) := by norm_num
  obtain ⟨α2, _, hα2⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont2.continuousOn hivt2
  have hroot2 : Polynomial.aeval α2 f2 = 0 := by
    dsimp [f2]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    simpa [map_ofNat] using hα2
  have hmap2 : f2.map (algebraMap ℚ gaussianRationals) =
      (Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 :
        gaussianRationals[X]) := by
    dsimp [f2]; simp [map_ofNat]
  have hirr2 := irreducible_gaussianRationals_of_irreducible_rat_of_real_root hf2_mon hf2_irr hroot2
  rw [hmap2] at hirr2
  exact ⟨hirr1.1, hirr1.2, hirr2.1, hirr2.2⟩


/-! ## §5.3 Other methods for establishing irreducibility (printed pp. 52–53, PDF pp. 60–61) -/

/-- Evaluation-at-`X + C c` ring endomorphism `R[X] →+* R[X]` (`X ↦ X + c`, §5.3, p. 52). -/
noncomputable def polyShiftHom (R : Type*) [CommRing R] (c : R) : R[X] →+* R[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C c)

theorem polyShiftHom_comp {R : Type*} [CommRing R] (c₁ c₂ : R) :
    (polyShiftHom R c₁).comp (polyShiftHom R c₂) = polyShiftHom R (c₁ + c₂) := by
  apply Polynomial.ringHom_ext'
  · ext a
    simp [polyShiftHom]
  · simp [polyShiftHom, add_assoc]

theorem polyShiftHom_zero (R : Type*) [CommRing R] :
    polyShiftHom R 0 = RingHom.id R[X] := by
  apply Polynomial.ringHom_ext'
  · ext a
    simp [polyShiftHom]
  · simp [polyShiftHom]

/-- Linear substitution ring automorphism `R[X] ≃+* R[X]` sending `X ↦ X + C c` with inverse
`X ↦ X + C (-c)` (§5.3, printed p. 52 / PDF p. 60). -/
noncomputable def polyShiftEquiv (R : Type*) [CommRing R] (c : R) : R[X] ≃+* R[X] :=
  { polyShiftHom R c with
    invFun := polyShiftHom R (-c)
    left_inv := fun f => by
      have h := RingHom.congr_fun (polyShiftHom_comp (-c) c) f
      simpa [neg_add_cancel, polyShiftHom_zero] using h
    right_inv := fun f => by
      have h := RingHom.congr_fun (polyShiftHom_comp c (-c)) f
      simpa [add_neg_cancel, polyShiftHom_zero] using h }

/-- **Main-text worked example (`x^4 + 4x^3 + 10x^2 + 12x + 7`)** (§5.3, printed p. 52 / PDF p. 60):
Under `y = x + 1` (`x = y - 1`), `f = x^4 + 4x^3 + 10x^2 + 12x + 7 ∈ ℤ[X]` transforms into
`g = y^4 + 4y^2 + 2 ∈ ℤ[X]`, which is irreducible in `ℤ[X]` by `Theorem 5.2` (`p = 2`); hence `f`
is irreducible in `ℤ[X]` (and in `ℚ[X]` by Gauss' lemma). -/
theorem example_5_3_quartic_shift_irreducible :
    let fZ : ℤ[X] := Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 3 +
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 12 * Polynomial.X + Polynomial.C 7
    let gZ : ℤ[X] := Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 2
    let fQ : ℚ[X] := Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 3 +
      Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 12 * Polynomial.X + Polynomial.C 7
    polyShiftEquiv ℤ (-1) fZ = gZ ∧
    Irreducible gZ ∧
    Irreducible fZ ∧
    IsGarlingIrreducible fZ ∧
    Irreducible fQ ∧
    IsGarlingIrreducible fQ := by
  intro fZ gZ fQ
  have hshift : polyShiftEquiv ℤ (-1) fZ = gZ := by
    change polyShiftHom ℤ (-1) fZ = gZ
    dsimp [fZ, gZ, polyShiftHom]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hgZ_deg : gZ.natDegree = 4 := by dsimp [gZ]; compute_degree!
  have hgZ_mon : gZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hgZ_deg]
    dsimp [gZ]; simp
  have hgZ_irr : Irreducible gZ := by
    refine (theorem_5_2 (p := (2 : ℤ)) (n := 4) (by omega) (le_of_eq hgZ_deg)
      (isGarlingRelativelyPrime_coeffs_of_monic hgZ_mon hgZ_deg) Int.prime_two ?_ ?_ ?_).2.1
    · intro i hi
      dsimp [gZ]
      interval_cases i <;> simp
    · dsimp [gZ]; simp
    · dsimp [gZ]; norm_num
  have hfZ_irr : Irreducible fZ :=
    (MulEquiv.irreducible_iff (polyShiftEquiv ℤ (-1)).toMulEquiv).mp
      (by simpa [hshift] using hgZ_irr)
  have hfZ_deg : fZ.natDegree = 4 := by dsimp [fZ]; compute_degree!
  have hfQ_irr : Irreducible fQ := by
    rcases (corollary_gauss_lemma ℚ fZ).mp hfZ_irr with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
    · exfalso
      have hd := congrArg Polynomial.natDegree hC
      rw [hfZ_deg, Polynomial.natDegree_C] at hd
      omega
    · have hmap_eq : fZ.map (algebraMap ℤ ℚ) = fQ := by dsimp [fZ, fQ]; simp [map_ofNat]
      rwa [hmap_eq] at hmap_irr
  exact ⟨hshift, hgZ_irr, hfZ_irr, (isGarlingIrreducible_iff fZ).mpr hfZ_irr,
    hfQ_irr, (isGarlingIrreducible_iff fQ).mpr hfQ_irr⟩

/-! ### Reduction modulo `p` and Theorem 5.3 (Localization principle) -/

/-- Garling's reduction-modulo-`p` ring homomorphism `ℤ[X] →+* (ZMod p)[X]`, `f ↦ f̄`
(§5.3, printed p. 52 / PDF p. 60). -/
noncomputable def modPrimePolyHom (p : ℕ) : ℤ[X] →+* (ZMod p)[X] :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod p))

@[simp]
theorem modPrimePolyHom_coeff (p : ℕ) (f : ℤ[X]) (k : ℕ) :
    (modPrimePolyHom p f).coeff k = (f.coeff k : ZMod p) := by
  simp [modPrimePolyHom]

/-- Surjectivity of the reduction-modulo-`p` homomorphism `ℤ[X] →+* (ZMod p)[X]` (§5.3, p. 52). -/
theorem modPrimePolyHom_surjective (p : ℕ) :
    Function.Surjective (modPrimePolyHom p) := by
  refine Polynomial.map_surjective (Int.castRingHom (ZMod p)) ?_
  rcases p with _ | p
  · exact fun x => ⟨x, rfl⟩
  · exact fun x => ⟨x.val, by simp⟩

/-- **Theorem 5.3 (Localization principle)** (§5.3, printed p. 52 / PDF p. 60, proof pp. 52–53):
Suppose that `f = a_0 + a_1 x + ... + a_n x^n ∈ ℤ[X]` (`f.natDegree ≤ n`), and that `a_0, ..., a_n`
are relatively prime (`IsGarlingRelativelyPrime`). Suppose that `p` is a prime number which does not
divide `a_n`. If `f̄` (`modPrimePolyHom p f`) is irreducible in `(ZMod p)[X]`, then `f` is
irreducible in `ℤ[X]`.

Proved literally for **all** `n : ℕ` (at `n = 0`, `f̄ ∈ (ZMod p)[X]` is a constant over the field
`ZMod p` and so is never irreducible). -/
theorem theorem_5_3 {f : ℤ[X]} {n p : ℕ}
    (hdeg_le : f.natDegree ≤ n)
    (hcop : IsGarlingRelativelyPrime (Set.range fun i : Fin (n + 1) => f.coeff i))
    (hp : Nat.Prime p)
    (hndvd_n : ¬ ((p : ℤ) ∣ f.coeff n))
    (hirr_bar : Irreducible (modPrimePolyHom p f)) :
    f.natDegree = n ∧ Irreducible f ∧ IsGarlingIrreducible f := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hfn_ne0 : f.coeff n ≠ 0 := fun hz => hndvd_n (hz ▸ dvd_zero (p : ℤ))
  have hf0 : f ≠ 0 := fun hz => hfn_ne0 (by simp [hz])
  have hdeg : f.natDegree = n := le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hfn_ne0)
  have hfbar_coeff_n : (modPrimePolyHom p f).coeff n ≠ 0 := by
    rw [modPrimePolyHom_coeff]
    intro hz
    exact hndvd_n ((ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff n) p).mp hz)
  have hfbar_deg_le : (modPrimePolyHom p f).natDegree ≤ n := by
    dsimp [modPrimePolyHom]
    exact Polynomial.natDegree_map_le.trans hdeg_le
  have hfbar_deg : (modPrimePolyHom p f).natDegree = n :=
    le_antisymm hfbar_deg_le (Polynomial.le_natDegree_of_ne_zero hfbar_coeff_n)
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hfbarC : modPrimePolyHom p f = Polynomial.C ((modPrimePolyHom p f).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hfbar_deg
    have hu : IsUnit (modPrimePolyHom p f) :=
      hfbarC ▸ (isUnit_iff_ne_zero.mpr hfbar_coeff_n).map Polynomial.C
    exact hirr_bar.not_isUnit hu
  have hirr : Irreducible f := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hg0 : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
      have hg_pos : 1 ≤ g.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop hgh hgu
      have hh_pos : 1 ≤ h.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop
          (hgh.trans (mul_comm g h)) hhu
      have hsum_deg : g.natDegree + h.natDegree = n := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      let gbar : (ZMod p)[X] := modPrimePolyHom p g
      let hbar : (ZMod p)[X] := modPrimePolyHom p h
      have hgh_bar : modPrimePolyHom p f = gbar * hbar := by
        dsimp [gbar, hbar]
        rw [hgh, map_mul]
      have hgbar0 : gbar ≠ 0 := fun hz => hirr_bar.ne_zero (by rw [hgh_bar, hz, zero_mul])
      have hhbar0 : hbar ≠ 0 := fun hz => hirr_bar.ne_zero (by rw [hgh_bar, hz, mul_zero])
      have hgbar_le : gbar.natDegree ≤ g.natDegree := by
        dsimp [gbar, modPrimePolyHom]
        exact Polynomial.natDegree_map_le
      have hhbar_le : hbar.natDegree ≤ h.natDegree := by
        dsimp [hbar, modPrimePolyHom]
        exact Polynomial.natDegree_map_le
      have hsum_bar : gbar.natDegree + hbar.natDegree = n := by
        rw [← Polynomial.natDegree_mul hgbar0 hhbar0, ← hgh_bar, hfbar_deg]
      have hgbar_pos : 1 ≤ gbar.natDegree := by omega
      have hhbar_pos : 1 ≤ hbar.natDegree := by omega
      rcases hirr_bar.isUnit_or_isUnit hgh_bar with hgu_bar | hhu_bar
      · have hd0 : gbar.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hgu_bar
        omega
      · have hd0 : hbar.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hhu_bar
        omega
  exact ⟨hdeg, hirr, (isGarlingIrreducible_iff f).mpr hirr⟩

/-- **Theorem 5.3 (Garling explicit sum form `a_0 + a_1 x + ... + a_n x^n`)** (§5.3, p. 52):
Explicit coefficient-tuple presentation using `IsGarlingIrreducible`. -/
theorem theorem_5_3_garling {n p : ℕ} (a : Fin (n + 1) → ℤ)
    (hcop : IsGarlingRelativelyPrime (Set.range a))
    (hp : Nat.Prime p)
    (hndvd_n : ¬ ((p : ℤ) ∣ a ⟨n, Nat.lt_succ_self n⟩))
    (hirr_bar : Irreducible
      (modPrimePolyHom p (∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)))) :
    let f : ℤ[X] := ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)
    IsGarlingIrreducible f ∧ Irreducible f := by
  intro f
  have hcoeff : ∀ k : ℕ, f.coeff k = if hk : k < n + 1 then a ⟨k, hk⟩ else 0 := by
    intro k
    dsimp [f]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hk : k < n + 1
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp [hk]
      · intro j _ hjk
        have hval : (j : ℕ) ≠ k := fun hv => hjk (Fin.ext hv)
        simp [hval]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    · simp only [hk, ↓reduceDIte]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hval : (j : ℕ) ≠ k := by omega
      simp [hval]
  have hdeg_le : f.natDegree ≤ n := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [hcoeff k]
    have hnot : ¬ k < n + 1 := by omega
    simp [hnot]
  have hrange : (Set.range fun i : Fin (n + 1) => f.coeff i) = Set.range a := by
    have hfun : (fun i : Fin (n + 1) => f.coeff i) = a := by
      funext i
      rw [hcoeff i.1]
      simp [i.2]
    rw [hfun]
  have hres := theorem_5_3 hdeg_le (hrange ▸ hcop) hp
    (by simpa [hcoeff n, Nat.lt_succ_self n] using hndvd_n) hirr_bar
  exact ⟨hres.2.2, hres.2.1⟩

/-- Main-text localization remark (§5.3, printed p. 53 / PDF p. 61): if `f ∈ ℤ[X]` has
`f.natDegree ≤ n` and `p ∣ f_i` for `0 ≤ i < n`, then `f̄ = f̄_n x^n` in `(ZMod p)[X]`. -/
theorem eisenstein_int_mod_prime_eq_monomial {f : ℤ[X]} {n p : ℕ}
    (hdeg_le : f.natDegree ≤ n) (hdvd : ∀ i < n, (p : ℤ) ∣ f.coeff i) :
    modPrimePolyHom p f = Polynomial.monomial n (f.coeff n : ZMod p) := by
  ext k
  rw [modPrimePolyHom_coeff, Polynomial.coeff_monomial]
  by_cases hkn : k = n
  · subst hkn; simp
  · simp only [Ne.symm hkn, ↓reduceIte]
    by_cases hlt : k < n
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff k) p).mpr (hdvd k hlt)
    · have hgt : n < k := by omega
      have hc0 : f.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg_le hgt)
      simp [hc0]

/-! ### Main-text worked localization example: `x^n + px + p^2` (§5.3, p. 53) -/

private theorem irreducible_int_and_rat_of_natDegree_eq_one_bezout {f : ℤ[X]}
    (hdeg : f.natDegree = 1) {u v : ℤ} (hbez : f.coeff 0 * u + f.coeff 1 * v = 1) :
    Irreducible f ∧ Irreducible (f.map (algebraMap ℤ ℚ)) := by
  have hprim : f.IsPrimitive := by
    refine Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr fun r hr => ?_
    have hd0 : r ∣ f.coeff 0 := by
      rcases hr with ⟨q, hq⟩
      exact ⟨q.coeff 0, by simpa [Polynomial.coeff_C_mul] using congrArg (fun P => P.coeff 0) hq⟩
    have hd1 : r ∣ f.coeff 1 := by
      rcases hr with ⟨q, hq⟩
      exact ⟨q.coeff 1, by simpa [Polynomial.coeff_C_mul] using congrArg (fun P => P.coeff 1) hq⟩
    refine isUnit_of_dvd_one ?_
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_left hd0 u) (dvd_mul_of_dvd_left hd1 v)
  have hf1_ne0 : f.coeff 1 ≠ 0 := by
    have hlc : f.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz] at hdeg; simp at hdeg)
    rwa [Polynomial.leadingCoeff, hdeg] at hlc
  have hmap_deg : (f.map (algebraMap ℤ ℚ)).degree = 1 := by
    have hnd : (f.map (algebraMap ℤ ℚ)).natDegree = 1 := by
      refine le_antisymm (Polynomial.natDegree_map_le.trans (le_of_eq hdeg)) ?_
      refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [Polynomial.coeff_map]
      exact Int.cast_ne_zero.mpr hf1_ne0
    rw [Polynomial.degree_eq_natDegree (fun hz => by rw [hz] at hnd; simp at hnd), hnd]
    rfl
  have hmap_irr : Irreducible (f.map (algebraMap ℤ ℚ)) :=
    Polynomial.irreducible_of_degree_eq_one hmap_deg
  have hf_irr : Irreducible f :=
    (corollary_gauss_lemma ℚ f).mpr (Or.inr ⟨(isGarlingPrimitive_iff f).mpr hprim, hmap_irr⟩)
  exact ⟨hf_irr, hmap_irr⟩

/-- **Main-text worked example (`x^n + px + p^2`)** (§5.3, printed p. 53 / PDF p. 61):
For every prime number `p` and **every** `n : ℕ`, `f = x^n + px + p^2` is irreducible in `ℤ[X]`
and in `ℚ[X]` (combining localization modulo `p` with degree-1 root exclusion and constant/linear
coefficient inspection for `n ≥ 2`, plus primitive linear cases for `n = 0, 1`). -/
theorem example_5_3_trinomial_irreducible {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    let fZ : ℤ[X] := Polynomial.X ^ n + Polynomial.C (p : ℤ) * Polynomial.X +
      Polynomial.C ((p : ℤ) ^ 2)
    let fQ : ℚ[X] := Polynomial.X ^ n + Polynomial.C (p : ℚ) * Polynomial.X +
      Polynomial.C ((p : ℚ) ^ 2)
    Irreducible fZ ∧ IsGarlingIrreducible fZ ∧
    Irreducible fQ ∧ IsGarlingIrreducible fQ := by
  classical
  intro fZ fQ
  have hp2 : 2 ≤ p := hp.two_le
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmap_eq : fZ.map (algebraMap ℤ ℚ) = fQ := by
    dsimp [fZ, fQ]
    simp
  have hfZ_coeff : ∀ k : ℕ,
      fZ.coeff k = (if k = n then 1 else 0) + (if k = 1 then (p : ℤ) else 0) +
        (if k = 0 then (p : ℤ) ^ 2 else 0) := by
    intro k
    dsimp [fZ]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have h1k : (1 : ℕ) ≠ k := Ne.symm hk1
      simp [hk1, h1k]
  rcases eq_or_ne n 0 with rfl | hn0
  · have hdeg : fZ.natDegree = 1 := by
      refine le_antisymm ?_ ?_
      · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
        rw [hfZ_coeff k]
        have hk0 : k ≠ 0 := by omega
        have hk1 : k ≠ 1 := by omega
        simp [hk0, hk1]
      · refine Polynomial.le_natDegree_of_ne_zero ?_
        rw [hfZ_coeff 1]
        simp
        omega
    have hbez : fZ.coeff 0 * 1 + fZ.coeff 1 * (-(p : ℤ)) = 1 := by
      rw [hfZ_coeff 0, hfZ_coeff 1]
      simp
      ring
    obtain ⟨hfZ_irr, hmap_irr⟩ := irreducible_int_and_rat_of_natDegree_eq_one_bezout hdeg hbez
    rw [hmap_eq] at hmap_irr
    exact ⟨hfZ_irr, (isGarlingIrreducible_iff fZ).mpr hfZ_irr,
      hmap_irr, (isGarlingIrreducible_iff fQ).mpr hmap_irr⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · have hdeg : fZ.natDegree = 1 := by
      refine le_antisymm ?_ ?_
      · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
        rw [hfZ_coeff k]
        have hk0 : k ≠ 0 := by omega
        have hk1 : k ≠ 1 := by omega
        simp [hk0, hk1]
      · refine Polynomial.le_natDegree_of_ne_zero ?_
        rw [hfZ_coeff 1]
        simp
        omega
    have hbez : fZ.coeff 0 * 1 + fZ.coeff 1 * (1 - (p : ℤ)) = 1 := by
      rw [hfZ_coeff 0, hfZ_coeff 1]
      simp
      ring
    obtain ⟨hfZ_irr, hmap_irr⟩ := irreducible_int_and_rat_of_natDegree_eq_one_bezout hdeg hbez
    rw [hmap_eq] at hmap_irr
    exact ⟨hfZ_irr, (isGarlingIrreducible_iff fZ).mpr hfZ_irr,
      hmap_irr, (isGarlingIrreducible_iff fQ).mpr hmap_irr⟩
  have hn2 : 2 ≤ n := by omega
  have hcoeff_n : fZ.coeff n = 1 := by
    rw [hfZ_coeff n]
    simp [hn0, hn1]
  have hcoeff_gt : ∀ k : ℕ, n < k → fZ.coeff k = 0 := by
    intro k hk
    rw [hfZ_coeff k]
    have hkn : k ≠ n := by omega
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp [hkn, hk0, hk1]
  have hdeg : fZ.natDegree = n := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hcoeff_gt) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hcoeff_n]
    exact one_ne_zero
  have hmon : fZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcoeff_n]
  have hcoeff_0 : fZ.coeff 0 = (p : ℤ) ^ 2 := by
    rw [hfZ_coeff 0]
    simp [Ne.symm hn0]
  have hcoeff_1 : fZ.coeff 1 = (p : ℤ) := by
    rw [hfZ_coeff 1]
    simp [Ne.symm hn1]
  have hdvd_lt : ∀ k < n, (p : ℤ) ∣ fZ.coeff k := by
    intro k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hcoeff_0]; exact ⟨(p : ℤ), sq (p : ℤ)⟩
    rcases eq_or_ne k 1 with rfl | hk1
    · rw [hcoeff_1]
    · have hkn : k ≠ n := by omega
      rw [hfZ_coeff k]
      simp [hkn, hk0, hk1]
  have hno_root : ∀ r : ℤ, fZ.eval r ≠ 0 := by
    intro r hr
    have hev : r ^ n + (p : ℤ) * r + (p : ℤ) ^ 2 = 0 := by
      dsimp [fZ] at hr
      simpa using hr
    have hdvd_rn : (p : ℤ) ∣ r ^ n := ⟨-r - (p : ℤ), by linarith⟩
    obtain ⟨k, rfl⟩ := hpZ.dvd_of_dvd_pow hdvd_rn
    have hn_eq : n = (n - 2) + 2 := by omega
    have hmul0 : (p : ℤ) ^ 2 * ((p : ℤ) ^ (n - 2) * k ^ n + k + 1) = 0 := by
      have hev' := hev
      conv_lhs at hev' =>
        arg 1; arg 1; rw [mul_pow]
        arg 1; rw [hn_eq, pow_add]
      linarith
    have hp2_ne0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hpZ.ne_zero
    have hred : (p : ℤ) ^ (n - 2) * k ^ n + k + 1 = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left hp2_ne0
    have hn1_eq : n = (n - 1) + 1 := by omega
    have hk_unit : IsUnit k := by
      refine isUnit_iff_exists_inv.mpr ⟨-(p : ℤ) ^ (n - 2) * k ^ (n - 1) - 1, ?_⟩
      have hkn : k ^ n = k ^ (n - 1) * k := by
        conv_lhs => rw [hn1_eq, pow_add, pow_one]
      linear_combination -hred + (p : ℤ) ^ (n - 2) * hkn
    rcases Int.isUnit_iff.mp hk_unit with rfl | rfl
    · have hnn : 0 ≤ (p : ℤ) ^ (n - 2) := pow_nonneg (by omega) (n - 2)
      simp only [one_pow, mul_one] at hred
      omega
    · have hred' : (p : ℤ) ^ (n - 2) * (-1 : ℤ) ^ n = 0 := by linarith
      exact pow_ne_zero (n - 2) hpZ.ne_zero
        ((mul_eq_zero.mp hred').resolve_right (pow_ne_zero n (by decide)))
  have hfZ_irr : Irreducible fZ := by
    refine ⟨?_, fun g h hgh => ?_⟩
    · intro hu
      have hd0 : fZ.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hgu, hhu⟩
      have hf0 : fZ ≠ 0 := hmon.ne_zero
      have hg0 : g ≠ 0 := fun hz => hf0 (by rw [hgh, hz, zero_mul])
      have hh0 : h ≠ 0 := fun hz => hf0 (by rw [hgh, hz, mul_zero])
      have hcop := isGarlingRelativelyPrime_coeffs_of_monic hmon hdeg
      have hg_pos : 1 ≤ g.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop hgh hgu
      have hh_pos : 1 ≤ h.natDegree :=
        one_le_natDegree_left_of_mul_of_relPrime_coeffs hf0 hdeg hcop
          (hgh.trans (mul_comm g h)) hhu
      have hsum_deg : g.natDegree + h.natDegree = n := by
        rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hdeg]
      have hlc_prod : g.leadingCoeff * h.leadingCoeff = 1 := by
        rw [← Polynomial.leadingCoeff_mul, ← hgh, hmon.leadingCoeff]
      have hg_deg_ge2 : 2 ≤ g.natDegree := by
        by_contra hlt2
        have hgd1 : g.natDegree = 1 := by omega
        have hg_eq : g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) := by
          ext m
          simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
            Polynomial.coeff_C]
          rcases eq_or_ne m 0 with rfl | hm0
          · simp
          rcases eq_or_ne m 1 with rfl | hm1
          · simp
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < m)]
            have h1m : (1 : ℕ) ≠ m := Ne.symm hm1
            simp [hm0, h1m]
        have hgc1_unit : IsUnit (g.coeff 1) := by
          refine isUnit_iff_exists_inv.mpr ⟨h.leadingCoeff, ?_⟩
          rwa [← hgd1, ← Polynomial.leadingCoeff]
        have hsq1 : (g.coeff 1) ^ 2 = 1 := by
          rcases Int.isUnit_iff.mp hgc1_unit with hc1 | hc1 <;> simp [hc1]
        let r : ℤ := -g.coeff 0 * g.coeff 1
        have hgeval0 : g.eval r = 0 := by
          rw [hg_eq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          dsimp [r]
          linear_combination -g.coeff 0 * hsq1
        exact hno_root r (by rw [hgh, Polynomial.eval_mul, hgeval0, zero_mul])
      have hh_deg_ge2 : 2 ≤ h.natDegree := by
        by_contra hlt2
        have hhd1 : h.natDegree = 1 := by omega
        have hh_eq : h = Polynomial.C (h.coeff 1) * Polynomial.X + Polynomial.C (h.coeff 0) := by
          ext m
          simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
            Polynomial.coeff_C]
          rcases eq_or_ne m 0 with rfl | hm0
          · simp
          rcases eq_or_ne m 1 with rfl | hm1
          · simp
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : h.natDegree < m)]
            have h1m : (1 : ℕ) ≠ m := Ne.symm hm1
            simp [hm0, h1m]
        have hhc1_unit : IsUnit (h.coeff 1) := by
          refine isUnit_iff_exists_inv.mpr ⟨g.leadingCoeff, ?_⟩
          rw [mul_comm, ← hhd1, ← Polynomial.leadingCoeff]
          exact hlc_prod
        have hsq1 : (h.coeff 1) ^ 2 = 1 := by
          rcases Int.isUnit_iff.mp hhc1_unit with hc1 | hc1 <;> simp [hc1]
        let r : ℤ := -h.coeff 0 * h.coeff 1
        have hheval0 : h.eval r = 0 := by
          rw [hh_eq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          dsimp [r]
          linear_combination -h.coeff 0 * hsq1
        exact hno_root r (by rw [hgh, Polynomial.eval_mul, hheval0, mul_zero])
      have hndvd_glc : ¬ ((p : ℤ) ∣ g.coeff g.natDegree) := by
        intro hd
        have h1 : (p : ℤ) ∣ (1 : ℤ) := by
          rw [← hlc_prod, Polynomial.leadingCoeff]
          exact dvd_mul_of_dvd_left hd _
        exact hpZ.not_dvd_one h1
      have hndvd_hlc : ¬ ((p : ℤ) ∣ h.coeff h.natDegree) := by
        intro hd
        have h1 : (p : ℤ) ∣ (1 : ℤ) := by
          rw [← hlc_prod, Polynomial.leadingCoeff, Polynomial.leadingCoeff]
          exact dvd_mul_of_dvd_right hd _
        exact hpZ.not_dvd_one h1
      have hex_g : ∃ i : ℕ, ¬ ((p : ℤ) ∣ g.coeff i) := ⟨g.natDegree, hndvd_glc⟩
      have hex_h : ∃ j : ℕ, ¬ ((p : ℤ) ∣ h.coeff j) := ⟨h.natDegree, hndvd_hlc⟩
      let a : ℕ := Nat.find hex_g
      let b : ℕ := Nat.find hex_h
      have ha_ndvd : ¬ ((p : ℤ) ∣ g.coeff a) := Nat.find_spec hex_g
      have hb_ndvd : ¬ ((p : ℤ) ∣ h.coeff b) := Nat.find_spec hex_h
      have ha_le : a ≤ g.natDegree := Nat.find_min' hex_g hndvd_glc
      have hb_le : b ≤ h.natDegree := Nat.find_min' hex_h hndvd_hlc
      have ha_min : ∀ i < a, (p : ℤ) ∣ g.coeff i := fun i hi => not_not.mp (Nat.find_min hex_g hi)
      have hb_min : ∀ j < b, (p : ℤ) ∣ h.coeff j := fun j hj => not_not.mp (Nat.find_min hex_h hj)
      by_cases hab_lt : a + b < n
      · have hdvd_ab : (p : ℤ) ∣ fZ.coeff (a + b) := hdvd_lt (a + b) hab_lt
        rw [hgh, Polynomial.coeff_mul] at hdvd_ab
        have hmem_anti : (a, b) ∈ Finset.antidiagonal (a + b) := Finset.mem_antidiagonal.mpr rfl
        rw [← Finset.add_sum_erase _ _ hmem_anti] at hdvd_ab
        have hdvd_rest : (p : ℤ) ∣ ∑ x ∈ (Finset.antidiagonal (a + b)).erase (a, b),
            g.coeff x.1 * h.coeff x.2 := by
          refine Finset.dvd_sum fun x hx => ?_
          have hx_ne : x ≠ (a, b) := (Finset.mem_erase.mp hx).1
          have hx_sum : x.1 + x.2 = a + b :=
            Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hx)
          have hlt_or : x.1 < a ∨ x.2 < b := by
            by_contra hge
            push Not at hge
            exact hx_ne (Prod.ext (by omega) (by omega))
          rcases hlt_or with h1 | h2
          · exact dvd_mul_of_dvd_left (ha_min x.1 h1) _
          · exact dvd_mul_of_dvd_right (hb_min x.2 h2) _
        rcases hpZ.dvd_or_dvd ((dvd_add_left hdvd_rest).mp hdvd_ab) with h1 | h2
        · exact ha_ndvd h1
        · exact hb_ndvd h2
      · have ha_ge2 : 2 ≤ a := by omega
        have hb_ge2 : 2 ≤ b := by omega
        have hd_g0 : (p : ℤ) ∣ g.coeff 0 := ha_min 0 (by omega)
        have hd_g1 : (p : ℤ) ∣ g.coeff 1 := ha_min 1 (by omega)
        have hd_h0 : (p : ℤ) ∣ h.coeff 0 := hb_min 0 (by omega)
        have hd_h1 : (p : ℤ) ∣ h.coeff 1 := hb_min 1 (by omega)
        have hc1_eq : fZ.coeff 1 = g.coeff 0 * h.coeff 1 + g.coeff 1 * h.coeff 0 := by
          rw [hgh, Polynomial.coeff_mul,
            show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by decide]
          simp
        have hdvd_sq : (p : ℤ) ^ 2 ∣ fZ.coeff 1 := by
          rw [hc1_eq, sq]
          exact dvd_add (mul_dvd_mul hd_g0 hd_h1) (mul_dvd_mul hd_g1 hd_h0)
        rw [hcoeff_1] at hdvd_sq
        rcases hdvd_sq with ⟨d, hd⟩
        have hmul0 : (p : ℤ) * ((p : ℤ) * d - 1) = 0 := by linear_combination -hd
        have hpd1 : (p : ℤ) * d = 1 := by
          have := (mul_eq_zero.mp hmul0).resolve_left hpZ.ne_zero
          linarith
        exact hpZ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨d, hpd1⟩)
  have hfQ_irr : Irreducible fQ := by
    rcases (corollary_gauss_lemma ℚ fZ).mp hfZ_irr with ⟨c, _, hC⟩ | ⟨_, hmap_irr⟩
    · exfalso
      have hd := congrArg Polynomial.natDegree hC
      rw [hdeg, Polynomial.natDegree_C] at hd
      omega
    · rwa [hmap_eq] at hmap_irr
  exact ⟨hfZ_irr, (isGarlingIrreducible_iff fZ).mpr hfZ_irr,
    hfQ_irr, (isGarlingIrreducible_iff fQ).mpr hfQ_irr⟩

/-! ### Exercises 5.11–5.12 (printed p. 53, PDF p. 61) -/

/-- The polynomial `1 + x + ... + x^{p-1} ∈ ℤ[X]` (`Exercise 5.11`, §5.3, p. 53). -/
noncomputable def garlingPrimeCyclotomicInt (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range p, Polynomial.X ^ i

/-- The polynomial `1 + x + ... + x^{p-1} ∈ ℚ[X]` (`Exercise 5.11`, §5.3, p. 53). -/
noncomputable def garlingPrimeCyclotomicRat (p : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range p, Polynomial.X ^ i

private theorem geom_sum_X_mul_X_sub_one (R : Type*) [CommRing R] (k : ℕ) :
    (∑ i ∈ Finset.range k, (Polynomial.X : R[X]) ^ i) * (Polynomial.X - 1) =
      (Polynomial.X : R[X]) ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

private theorem prime_not_dvd_factorial_of_lt {p m : ℕ} (hp : Nat.Prime p) :
    m < p → ¬ (p ∣ m.factorial) := by
  induction m with
  | zero =>
    intro _
    exact hp.not_dvd_one
  | succ m ih =>
    intro hlt hdvd
    rw [Nat.factorial_succ] at hdvd
    rcases hp.dvd_mul.mp hdvd with h1 | h2
    · have hle := Nat.le_of_dvd (Nat.succ_pos m) h1
      omega
    · exact ih (by omega) h2

private theorem prime_dvd_choose_of_pos_of_lt {p k : ℕ} (hp : Nat.Prime p)
    (hk0 : 0 < k) (hkp : k < p) : p ∣ p.choose k := by
  have hfac : p ∣ p.choose k * (k.factorial * (p - k).factorial) := by
    rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial (le_of_lt hkp)]
    exact Nat.dvd_factorial hp.pos le_rfl
  rcases hp.dvd_mul.mp hfac with hd | hd2
  · exact hd
  · rcases hp.dvd_mul.mp hd2 with hk | hpk
    · exact absurd hk (prime_not_dvd_factorial_of_lt hp hkp)
    · exact absurd hpk (prime_not_dvd_factorial_of_lt hp (by omega))

/-- **Exercise 5.11 — Integer-ring companion** (§5.3, printed p. 53 / PDF p. 61):
For every prime number `p`, making the transformation `y = x - 1` (`x = y + 1`,
`polyShiftEquiv ℤ 1`) carries `1 + x + ... + x^{p-1}` to
`∑_{j=0}^{p-1} C(p, j+1) y^j ∈ ℤ[y]`, which is Eisenstein at `p`; hence
`1 + x + ... + x^{p-1}` is irreducible in `ℤ[X]`. -/
theorem exercise_5_11_int {p : ℕ} (hp : Nat.Prime p) :
    polyShiftEquiv ℤ 1 (garlingPrimeCyclotomicInt p) =
      ∑ j ∈ Finset.range p, Polynomial.monomial j (p.choose (j + 1) : ℤ) ∧
    Irreducible (garlingPrimeCyclotomicInt p) ∧
    IsGarlingIrreducible (garlingPrimeCyclotomicInt p) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let g : ℤ[X] := polyShiftEquiv ℤ 1 (garlingPrimeCyclotomicInt p)
  let h : ℤ[X] := ∑ j ∈ Finset.range p, Polynomial.monomial j (p.choose (j + 1) : ℤ)
  have hg_mul : g * Polynomial.X = (Polynomial.X + 1 : ℤ[X]) ^ p - 1 := by
    have hgeom := congrArg (polyShiftEquiv ℤ 1) (geom_sum_X_mul_X_sub_one ℤ p)
    rw [map_mul, map_sub, map_sub, map_pow] at hgeom
    have hX : polyShiftEquiv ℤ 1 (Polynomial.X : ℤ[X]) = Polynomial.X + 1 := by
      change polyShiftHom ℤ 1 (Polynomial.X : ℤ[X]) = Polynomial.X + 1
      simp [polyShiftHom]
    have h1 : polyShiftEquiv ℤ 1 (1 : ℤ[X]) = 1 := map_one _
    simpa [g, garlingPrimeCyclotomicInt, hX, h1] using hgeom
  have hh_mul : h * Polynomial.X = (Polynomial.X + 1 : ℤ[X]) ^ p - 1 := by
    rw [add_pow, Finset.sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one]
    rw [add_sub_cancel_right]
    dsimp [h]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_eq_natCast, pow_succ]
    ring
  have hgh : g = h := mul_right_cancel₀ Polynomial.X_ne_zero (hg_mul.trans hh_mul.symm)
  have hh_coeff : ∀ k : ℕ, h.coeff k = if k < p then (p.choose (k + 1) : ℤ) else 0 := by
    intro k
    dsimp [h]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hk : k < p
    · rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro j _ hjk; simp [hjk]
      · intro habs; exact absurd (Finset.mem_range.mpr hk) habs
    · simp only [hk, ↓reduceIte]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk : j ≠ k := by have := Finset.mem_range.mp hj; omega
      simp [hjk]
  have hh_deg_le : h.natDegree ≤ p - 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [hh_coeff k]
    have hnot : ¬ k < p := by omega
    simp [hnot]
  have hh_coeff_top : h.coeff (p - 1) = 1 := by
    rw [hh_coeff (p - 1)]
    have hlt : p - 1 < p := by omega
    have hsucc : p - 1 + 1 = p := by omega
    simp [hlt, hsucc, Nat.choose_self]
  have hh_deg : h.natDegree = p - 1 :=
    le_antisymm hh_deg_le (Polynomial.le_natDegree_of_ne_zero (hh_coeff_top ▸ one_ne_zero))
  have hh_mon : h.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hh_deg, hh_coeff_top]
  have hh_irr : Irreducible h := by
    refine (theorem_5_2 (p := (p : ℤ)) (n := p - 1) (by omega) hh_deg_le
      (isGarlingRelativelyPrime_coeffs_of_monic hh_mon hh_deg) hpZ ?_ ?_ ?_).2.1
    · intro i hi
      rw [hh_coeff i]
      have hlt : i < p := by omega
      simp only [hlt, ↓reduceIte]
      exact Int.natCast_dvd_natCast.mpr
        (prime_dvd_choose_of_pos_of_lt hp (Nat.succ_pos i) (by omega))
    · rw [hh_coeff_top]
      exact hpZ.not_dvd_one
    · rw [hh_coeff 0]
      have h0p : 0 < p := by omega
      simp only [h0p, ↓reduceIte, zero_add, Nat.choose_one_right]
      rintro ⟨d, hd⟩
      have hmul0 : (p : ℤ) * ((p : ℤ) * d - 1) = 0 := by linear_combination -hd
      have hpd1 : (p : ℤ) * d = 1 := by
        have := (mul_eq_zero.mp hmul0).resolve_left hpZ.ne_zero
        linarith
      exact hpZ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨d, hpd1⟩)
  have hg_irr : Irreducible (polyShiftEquiv ℤ 1 (garlingPrimeCyclotomicInt p)) := by
    simpa [g, hgh] using hh_irr
  have hf_irr : Irreducible (garlingPrimeCyclotomicInt p) :=
    (MulEquiv.irreducible_iff (polyShiftEquiv ℤ 1).toMulEquiv).mp hg_irr
  exact ⟨hgh, hf_irr, (isGarlingIrreducible_iff _).mpr hf_irr⟩

/-- **Exercise 5.11** (§5.3, printed p. 53 / PDF p. 61):
*"Show (by making the transformation `y = x - 1`) that if `p` is a prime number then
`1 + x + ... + x^{p-1}` is irreducible over `ℚ`."* -/
theorem exercise_5_11 {p : ℕ} (hp : Nat.Prime p) :
    Irreducible (garlingPrimeCyclotomicRat p) ∧
    IsGarlingIrreducible (garlingPrimeCyclotomicRat p) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hfZ_irr : Irreducible (garlingPrimeCyclotomicInt p) := (exercise_5_11_int hp).2.1
  have hfZ_coeff_top : (garlingPrimeCyclotomicInt p).coeff (p - 1) = 1 := by
    dsimp [garlingPrimeCyclotomicInt]
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (p - 1)]
    · simp [Polynomial.coeff_X_pow]
    · intro j _ hjp; simp [Polynomial.coeff_X_pow, Ne.symm hjp]
    · intro habs; exact absurd (Finset.mem_range.mpr (by omega)) habs
  have hfZ_not_C : ∀ a : ℤ, garlingPrimeCyclotomicInt p ≠ Polynomial.C a := by
    intro a hC
    have hc := congrArg (fun P : ℤ[X] => P.coeff (p - 1)) hC
    have hne0 : p - 1 ≠ 0 := by omega
    rw [hfZ_coeff_top, Polynomial.coeff_C] at hc
    simp [hne0] at hc
  rcases (corollary_gauss_lemma ℚ (garlingPrimeCyclotomicInt p)).mp hfZ_irr with
      ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
  · exact False.elim (hfZ_not_C a hC)
  · have hmap_eq : (garlingPrimeCyclotomicInt p).map (algebraMap ℤ ℚ) =
        garlingPrimeCyclotomicRat p := by
      dsimp [garlingPrimeCyclotomicInt, garlingPrimeCyclotomicRat]
      simp [Polynomial.map_sum]
    rw [hmap_eq] at hmap_irr
    exact ⟨hmap_irr, (isGarlingIrreducible_iff _).mpr hmap_irr⟩

/-! #### Exercise 5.12: Minimal polynomials of `e^{iθ}` and `2 cos θ` for `θ = 2π/7` -/

/-- **Exercise 5.12 — Part 1 (`e^{iθ}` for `θ = 2π/7`)** (§5.3, printed p. 53 / PDF p. 61):
For `θ = 2π/7`, the minimal polynomial of `e^{iθ} ∈ ℂ` over `ℚ` is
`x^6 + x^5 + x^4 + x^3 + x^2 + x + 1` (both as `minpoly ℚ` and as the unique monic generator of
`evalKer ℚ`). -/
theorem exercise_5_12_exp :
    let θ : ℝ := 2 * Real.pi / 7
    let ζ : ℂ := Complex.exp (Complex.I * (θ : ℂ))
    let p : ℚ[X] := Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 +
      Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1
    minpoly ℚ ζ = p ∧ evalKer ℚ ζ = Ideal.span {p} := by
  intro θ ζ p
  have hζ7 : ζ ^ 7 = 1 := by
    dsimp [ζ, θ]
    rw [← Complex.exp_nat_mul]
    have hexp : (7 : ℕ) * (Complex.I * ((2 * Real.pi / 7 : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_two_pi_mul_I]
  have hζ_euler : ζ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    dsimp [ζ]
    rw [mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsin_pos : 0 < Real.sin θ := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · dsimp [θ]; positivity
    · dsimp [θ]; linarith [Real.pi_pos]
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    have him := congrArg Complex.im (hζ_euler.symm.trans h1)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.one_im, mul_one, mul_zero, add_zero, zero_add] at him
    linarith
  have hsum : ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have hmul : (ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) * (ζ - 1) = 0 := by
      calc (ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) * (ζ - 1)
          = ζ ^ 7 - 1 := by ring
        _ = 0 := sub_eq_zero.mpr hζ7
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hζ_ne1)
  have hp_eq : p = garlingPrimeCyclotomicRat 7 := by
    dsimp [p, garlingPrimeCyclotomicRat]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    ring
  have hp_irr : Irreducible p := by
    rw [hp_eq]
    exact (exercise_5_11 (by decide : Nat.Prime 7)).1
  have hp_deg : p.natDegree = 6 := by dsimp [p]; compute_degree!
  have hp_mon : p.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hp_deg]
    dsimp [p]
    simp [Polynomial.coeff_X, Polynomial.coeff_one]
  have hp_aeval : Polynomial.aeval ζ p = 0 := by
    dsimp [p]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hsum
  have hmin : minpoly ℚ ζ = p :=
    (minpoly.eq_of_irreducible_of_monic hp_irr hp_aeval hp_mon).symm
  have hgar : IsGarlingAlgebraic ℚ ζ := ⟨p, hp_mon.ne_zero, hp_aeval⟩
  have hker : evalKer ℚ ζ = Ideal.span {p} := by
    rw [← hmin]
    exact (exists_unique_monic_generator_evalKer hgar).2.1
  exact ⟨hmin, hker⟩

/-- **Exercise 5.12 — Part 2 (`2 cos θ` for `θ = 2π/7`)** (§5.3, printed p. 53 / PDF p. 61):
For `θ = 2π/7`, the minimal polynomial of `2 cos θ ∈ ℝ` over `ℚ` is `x^3 + x^2 - 2x - 1`
(both as `minpoly ℚ` and as the unique monic generator of `evalKer ℚ`). -/
theorem exercise_5_12_two_cos :
    let θ : ℝ := 2 * Real.pi / 7
    let α : ℝ := 2 * Real.cos θ
    let q : ℚ[X] := Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1
    minpoly ℚ α = q ∧ evalKer ℚ α = Ideal.span {q} := by
  intro θ α q
  let ζ : ℂ := Complex.exp (Complex.I * (θ : ℂ))
  have hζ7 : ζ ^ 7 = 1 := by
    dsimp [ζ, θ]
    rw [← Complex.exp_nat_mul]
    have hexp : (7 : ℕ) * (Complex.I * ((2 * Real.pi / 7 : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_two_pi_mul_I]
  have hζ_euler : ζ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    dsimp [ζ]
    rw [mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsin_pos : 0 < Real.sin θ := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · dsimp [θ]; positivity
    · dsimp [θ]; linarith [Real.pi_pos]
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    have him := congrArg Complex.im (hζ_euler.symm.trans h1)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.one_im, mul_one, mul_zero, add_zero, zero_add] at him
    linarith
  have hsum : ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have hmul : (ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) * (ζ - 1) = 0 := by
      calc (ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) * (ζ - 1)
          = ζ ^ 7 - 1 := by ring
        _ = 0 := sub_eq_zero.mpr hζ7
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hζ_ne1)
  have hζ_ne0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ6_eq_inv : ζ ^ 6 = ζ⁻¹ := by
    have hmul1 : ζ * ζ ^ 6 = 1 := by
      rw [← pow_succ', hζ7]
    calc ζ ^ 6 = ζ⁻¹ * (ζ * ζ ^ 6) := (inv_mul_cancel_left₀ hζ_ne0 (ζ ^ 6)).symm
      _ = ζ⁻¹ := by rw [hmul1, mul_one]
  have hζ_inv_euler : ζ⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    dsimp [ζ]
    rw [← Complex.exp_neg]
    have hneg : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hneg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have hα_coe : (α : ℂ) = ζ + ζ ^ 6 := by
    rw [hζ6_eq_inv, hζ_inv_euler, hζ_euler]
    dsimp [α]
    push_cast
    ring
  have hζ7_sub : ζ ^ 7 - 1 = 0 := sub_eq_zero.mpr hζ7
  have hw_root : (ζ + ζ ^ 6) ^ 3 + (ζ + ζ ^ 6) ^ 2 - 2 * (ζ + ζ ^ 6) - 1 = 0 := by
    linear_combination
      (ζ ^ 11 + 3 * ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + 3 * ζ + 2) * hζ7_sub + hsum
  have hα_root : α ^ 3 + α ^ 2 - 2 * α - 1 = 0 := by
    apply Complex.ofReal_injective
    push_cast
    rwa [hα_coe]
  let qZ : ℤ[X] := Polynomial.X ^ 3 + Polynomial.X ^ 2 - Polynomial.C 2 * Polynomial.X - 1
  have hqZ_deg : qZ.natDegree = 3 := by dsimp [qZ]; compute_degree!
  have hqZ_mon : qZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hqZ_deg]
    dsimp [qZ]
    simp [Polynomial.coeff_X, Polynomial.coeff_one]
  have hqZ_no_root : ∀ r : ℤ, qZ.eval r ≠ 0 := by
    intro r hr
    have hev : r ^ 3 + r ^ 2 - 2 * r - 1 = 0 := by
      dsimp [qZ] at hr
      simpa using hr
    have hunit : IsUnit r :=
      isUnit_iff_exists_inv.mpr ⟨r ^ 2 + r - 2, by linarith⟩
    rcases Int.isUnit_iff.mp hunit with rfl | rfl <;> omega
  have hq_map : qZ.map (algebraMap ℤ ℚ) = q := by
    dsimp [qZ, q]
    simp [map_ofNat]
  have hq_irr : Irreducible q := by
    rw [← hq_map]
    exact (irreducible_int_and_rat_of_monic_deg_three hqZ_mon hqZ_deg hqZ_no_root).2
  have hq_mon : q.Monic := hq_map ▸ hqZ_mon.map (algebraMap ℤ ℚ)
  have hq_aeval : Polynomial.aeval α q = 0 := by
    dsimp [q]
    simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat,
      Polynomial.aeval_X] using hα_root
  have hmin : minpoly ℚ α = q :=
    (minpoly.eq_of_irreducible_of_monic hq_irr hq_aeval hq_mon).symm
  have hgar : IsGarlingAlgebraic ℚ α := ⟨q, hq_mon.ne_zero, hq_aeval⟩
  have hker : evalKer ℚ α = Ideal.span {q} := by
    rw [← hmin]
    exact (exists_unique_monic_generator_evalKer hgar).2.1
  exact ⟨hmin, hker⟩

/-- **Exercise 5.12** (§5.3, printed p. 53 / PDF p. 61):
Combined statement for `θ = 2π/7`: the minimal polynomial of `e^{iθ}` over `ℚ` is
`x^6 + x^5 + x^4 + x^3 + x^2 + x + 1`, and the minimal polynomial of `2 cos θ` over `ℚ` is
`x^3 + x^2 - 2x - 1`. -/
theorem exercise_5_12 :
    let θ : ℝ := 2 * Real.pi / 7
    minpoly ℚ (Complex.exp (Complex.I * (θ : ℂ))) =
      (Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 +
        Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 : ℚ[X]) ∧
    minpoly ℚ (2 * Real.cos θ) =
      (Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1 : ℚ[X]) :=
  ⟨exercise_5_12_exp.1, exercise_5_12_two_cos.1⟩

end Garling.Chapter05
