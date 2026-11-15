import Garling.Chapter01
import Garling.Chapter02
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Sym.Card
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.Tactic.FinCases

/-!
# Chapter 3: Rings

Formalization of Chapter 3 (printed pp. 18–36, PDF pp. 26–44; followed by the Part 2 divider leaf
at printed pp. 37–38, PDF pp. 45–46) of D. J. H. Garling, *A Course in Galois Theory* (Cambridge
University Press, 1986), following the chapter's nine sections (§3.1–§3.9) and all numbered/headed
items in source order.
-/

namespace Garling.Chapter03

open Garling.Chapter01 Garling.Chapter02
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## §3.1 Rings (printed pp. 18–20, PDF pp. 26–28) -/

/-- Garling's literal definition of a *commutative ring with a 1* (abbreviated to *ring*, §3.1,
p. 18): a non-empty set `R` with addition and multiplication such that `(R, +)` is an abelian group
with neutral element `0`, and multiplication satisfies:
(a) `(rs)t = r(st)`, (b) `rs = sr`, (c) `(r + s)t = rt + st`, and
(d) there exists an identity element `1`, different from `0`, such that `r * 1 = r`. -/
structure IsGarlingRing (R : Type*) (add mul : LawOfComposition R) : Prop where
  nonempty : Nonempty R
  exists_zero_one : ∃ (zero one : R),
    (∀ r s t : R, add (add r s) t = add r (add s t)) ∧
    (∀ r s : R, add r s = add s r) ∧
    (∀ r : R, add zero r = r ∧ add r zero = r) ∧
    (∀ r : R, ∃ nr : R, add r nr = zero ∧ add nr r = zero) ∧
    (∀ r s t : R, mul (mul r s) t = mul r (mul s t)) ∧
    (∀ r s : R, mul r s = mul s r) ∧
    (∀ r s t : R, mul (add r s) t = add (mul r t) (mul s t)) ∧
    one ≠ zero ∧
    (∀ r : R, mul r one = r)

/-- Every nontrivial `CommRing` satisfies Garling's ring axioms (§3.1, p. 18). -/
theorem CommRing.isGarlingRing (R : Type*) [CommRing R] [Nontrivial R] :
    IsGarlingRing R (· + ·) (· * ·) where
  nonempty := ⟨0⟩
  exists_zero_one := ⟨0, 1,
    add_assoc,
    add_comm,
    fun r => ⟨zero_add r, add_zero r⟩,
    fun r => ⟨-r, add_neg_cancel r, neg_add_cancel r⟩,
    mul_assoc,
    mul_comm,
    add_mul,
    one_ne_zero,
    mul_one⟩

/-- For any `CommRing R`, Garling's ring axioms hold if and only if `R` is `Nontrivial` (`1 ≠ 0`,
§3.1, p. 18). -/
theorem isGarlingRing_iff_nontrivial (R : Type*) [CommRing R] :
    IsGarlingRing R (· + ·) (· * ·) ↔ Nontrivial R := by
  refine ⟨fun h => ?_, fun _ => CommRing.isGarlingRing R⟩
  rcases h.exists_zero_one with ⟨zero, one, _, _, _, _, _, _, _, hne, _⟩
  exact ⟨⟨one, zero, hne⟩⟩

/-- Example 1 (§3.1, p. 18): Every field is a ring. -/
theorem field_isGarlingRing (K : Type*) [Field K] :
    IsGarlingRing K (· + ·) (· * ·) :=
  CommRing.isGarlingRing K

/-- Example 2 (§3.1, p. 18): The integers `ℤ` form a ring under usual addition and multiplication. -/
theorem int_isGarlingRing : IsGarlingRing ℤ (· + ·) (· * ·) :=
  CommRing.isGarlingRing ℤ

/-- Example 3 (§3.1, p. 18): The Gaussian integers `ℤ + iℤ = {m + in : m, n ∈ ℤ} ⊆ ℂ` form a ring. -/
def GaussianIntSubring : Subring ℂ where
  carrier := {z : ℂ | ∃ m n : ℤ, z = (m : ℂ) + Complex.I * (n : ℂ)}
  mul_mem' := by
    rintro _ _ ⟨m₁, n₁, rfl⟩ ⟨m₂, n₂, rfl⟩
    refine ⟨m₁ * m₂ - n₁ * n₂, m₁ * n₂ + n₁ * m₂, ?_⟩
    push_cast
    linear_combination (n₁ : ℂ) * (n₂ : ℂ) * Complex.I_sq
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m₁, n₁, rfl⟩ ⟨m₂, n₂, rfl⟩
    exact ⟨m₁ + m₂, n₁ + n₂, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

theorem gaussianIntSubring_isGarlingRing :
    IsGarlingRing GaussianIntSubring (· + ·) (· * ·) :=
  CommRing.isGarlingRing GaussianIntSubring

/-- Example 4 (§3.1, p. 19; also §3.4 Ex. 3.12–3.13): The ring `ℤ + i√5 ℤ` of complex numbers of
the form `m + i√5 n` (`m, n ∈ ℤ`). -/
noncomputable def ZAdjoinI5 : Subring ℂ where
  carrier := {z : ℂ | ∃ m n : ℤ, z = (m : ℂ) + Complex.I * (Real.sqrt 5 : ℝ) * (n : ℂ)}
  mul_mem' := by
    rintro _ _ ⟨m₁, n₁, rfl⟩ ⟨m₂, n₂, rfl⟩
    refine ⟨m₁ * m₂ - 5 * n₁ * n₂, m₁ * n₂ + n₁ * m₂, ?_⟩
    have hs : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      rw [sq]
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    push_cast
    calc ((m₁ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₁) *
          (↑m₂ + Complex.I * ↑(Real.sqrt 5) * ↑n₂)
      _ = ↑m₁ * ↑m₂ + Complex.I ^ 2 * ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 * ↑n₁ * ↑n₂ +
          Complex.I * ↑(Real.sqrt 5) * (↑m₁ * ↑n₂ + ↑n₁ * ↑m₂) := by ring
      _ = ↑m₁ * ↑m₂ - 5 * ↑n₁ * ↑n₂ +
          Complex.I * ↑(Real.sqrt 5) * (↑m₁ * ↑n₂ + ↑n₁ * ↑m₂) := by
          rw [Complex.I_sq, hs]; ring
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m₁, n₁, rfl⟩ ⟨m₂, n₂, rfl⟩
    exact ⟨m₁ + m₂, n₁ + n₂, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

theorem zAdjoinI5_isGarlingRing :
    IsGarlingRing ZAdjoinI5 (· + ·) (· * ·) :=
  CommRing.isGarlingRing ZAdjoinI5

/-- Unique integer coordinates `m, n ∈ ℤ` for elements `m + i√5 n` of `ℤ + i√5 ℤ` (§3.1, p. 19). -/
theorem zAdjoinI5_coords_unique {m₁ n₁ m₂ n₂ : ℤ}
    (h : ((m₁ : ℂ) + Complex.I * (Real.sqrt 5 : ℝ) * (n₁ : ℂ)) =
      (m₂ : ℂ) + Complex.I * (Real.sqrt 5 : ℝ) * (n₂ : ℂ)) :
    m₁ = m₂ ∧ n₁ = n₂ := by
  have hre : (m₁ : ℝ) = (m₂ : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re h
  have him : Real.sqrt 5 * (n₁ : ℝ) = Real.sqrt 5 * (n₂ : ℝ) := by
    simpa [Complex.add_im, Complex.mul_im, mul_assoc] using congrArg Complex.im h
  have hs5 : (Real.sqrt 5 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  exact ⟨Int.cast_injective hre, Int.cast_injective (mul_left_cancel₀ hs5 him)⟩

/-- Example 5 (§3.1, p. 19): For any Garling ring `R`, `R[x]` (`Polynomial R`) is a Garling ring,
and `a ↦ C a` embeds `R` injectively into `R[x]`. -/
theorem polynomial_isGarlingRing (R : Type*) [CommRing R] [Nontrivial R] :
    IsGarlingRing R[X] (· + ·) (· * ·) ∧ Function.Injective (Polynomial.C : R →+* R[X]) :=
  ⟨CommRing.isGarlingRing R[X], Polynomial.C_injective⟩

/-- Garling's degree of a non-zero polynomial `a ∈ R[x]` (§3.1, p. 19), requiring an explicit
non-zero proof `ha : a ≠ 0` so no junk value is assigned to `0`. -/
def garlingDegree {R : Type*} [Semiring R] (a : R[X]) (_ : a ≠ 0) : ℕ :=
  a.natDegree

theorem garlingDegree_spec {R : Type*} [Semiring R] (a : R[X]) (ha : a ≠ 0) :
    a.coeff (garlingDegree a ha) ≠ 0 ∧
      (∀ m : ℕ, garlingDegree a ha < m → a.coeff m = 0) ∧
      a = ∑ i ∈ Finset.range (garlingDegree a ha + 1), Polynomial.C (a.coeff i) * Polynomial.X ^ i :=
  ⟨Polynomial.leadingCoeff_ne_zero.mpr ha,
    fun _ hm => Polynomial.coeff_eq_zero_of_natDegree_lt hm,
    Polynomial.as_sum_range_C_mul_X_pow a⟩

/-- Example 6 (§3.1, pp. 19–20): Polynomials in `n` variables `R[x_1, ..., x_n]` (`MvPolynomial
(Fin n) R`) satisfy `R[x_1, ..., x_{n+1}] ≃ₐ[R] (R[x_1, ..., x_n])[x_{n+1}]`, and for an arbitrary
index set `S`, every element of `R[X_S]` (`MvPolynomial S R`) lies in `R[x_{s_1}, ..., x_{s_k}]`
for some finite subset of `S`. -/
noncomputable def mvPolynomialSuccEquiv (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] (MvPolynomial (Fin n) R)[X] :=
  MvPolynomial.finSuccEquiv R n

theorem mvPolynomial_mem_finite_vars {R S : Type*} [CommRing R] (p : MvPolynomial S R) :
    ∃ (t : Finset S) (q : MvPolynomial t R), MvPolynomial.rename Subtype.val q = p := by
  obtain ⟨t, q, hq⟩ := MvPolynomial.exists_finset_rename p
  exact ⟨t, q, hq.symm⟩

/-! ### Exercise 3.1 (§3.1, printed p. 20, PDF p. 28) -/

/-- **Exercise 3.1 (`S = ∅` counterexample to Part 1)** (§3.1, p. 20): When `S = Empty`, the set of
all mappings `R^S` (`Empty → R`) has a single element, so `1 = 0` in `R^S`, violating Garling's
ring condition (d) (`1 ≠ 0`, §3.1, p. 18) even when `R = ℤ`. -/
theorem exercise_3_1_empty_counterexample :
    IsGarlingRing ℤ (· + ·) (· * ·) ∧
      ¬ IsGarlingRing (Empty → ℤ) (· + ·) (· * ·) := by
  refine ⟨int_isGarlingRing, ?_⟩
  rw [isGarlingRing_iff_nontrivial]
  intro hnt
  rcases hnt with ⟨f, g, hfg⟩
  exact hfg (Subsingleton.elim f g)

/-- Exact characterization for Exercise 3.1 Part 1 (§3.1, p. 20): for a Garling ring `R`, `R^S`
(`S → R`) satisfies Garling's ring axioms (`1 ≠ 0`) if and only if `S` is non-empty. -/
theorem exercise_3_1_isGarlingRing_iff {S R : Type*} [CommRing R] [Nontrivial R] :
    IsGarlingRing (S → R) (· + ·) (· * ·) ↔ Nonempty S := by
  rw [isGarlingRing_iff_nontrivial]
  constructor
  · rintro ⟨f, g, hfg⟩
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    exact hfg (funext fun s => hempty.elim s)
  · rintro ⟨s₀⟩
    refine ⟨⟨1, 0, fun h => one_ne_zero (congrFun h s₀)⟩⟩

/-- **Exercise 3.1 (repaired Part 1 under `[Nonempty S]` + literal Part 2)** (§3.1, p. 20):
For any Garling ring `R` and non-empty set `S`, `R^S` (`S → R`) is a Garling ring under pointwise
addition and multiplication; and for any set `S` with `|S| > 1` (`1 < setOrder S`), there exist
non-zero `f, g ∈ R^S` with `f * g = 0`. -/
theorem exercise_3_1 {S R : Type*} [CommRing R] [Nontrivial R] [Nonempty S] :
    IsGarlingRing (S → R) (· + ·) (· * ·) ∧
      ((1 : ℕ∞) < setOrder S → ∃ f g : S → R, f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0) := by
  refine ⟨exercise_3_1_isGarlingRing_iff.mpr ‹Nonempty S›, fun hS => ?_⟩
  classical
  have h0 : (∅ : Finset S).card < ENat.card S := by
    simp only [Finset.card_empty, Nat.cast_zero]
    exact lt_trans (by decide : (0 : ℕ∞) < 1) hS
  obtain ⟨s₁, _⟩ := Finset.exists_not_mem_of_card_lt_enatCard h0
  have h1 : ({s₁} : Finset S).card < ENat.card S := by
    simpa [setOrder] using hS
  obtain ⟨s₂, hs₂⟩ := Finset.exists_not_mem_of_card_lt_enatCard h1
  have hne : s₁ ≠ s₂ := fun h => hs₂ (h ▸ Finset.mem_singleton_self s₁)
  refine ⟨fun s => if s = s₁ then 1 else 0, fun s => if s = s₂ then 1 else 0, ?_, ?_, ?_⟩
  · intro hf
    have := congrFun hf s₁
    simp at this
  · intro hg
    have := congrFun hg s₂
    simp at this
  · ext s
    by_cases hs : s = s₁
    · subst hs
      simp [hne]
    · simp [hs]

/-- **Exercise 3.1 (Part 2 unconditional)** (§3.1, p. 20): Part 2 holds literally for every set `S`
with no extra hypothesis, since `1 < setOrder S` already implies `S` has at least two distinct
elements. -/
theorem exercise_3_1_zero_divisors {S R : Type*} [CommRing R] [Nontrivial R]
    (hS : (1 : ℕ∞) < setOrder S) :
    ∃ f g : S → R, f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 := by
  classical
  have h0 : (∅ : Finset S).card < ENat.card S :=
    lt_trans (by decide : (0 : ℕ∞) < 1) hS
  obtain ⟨s₁, _⟩ := Finset.exists_not_mem_of_card_lt_enatCard h0
  have _ : Nonempty S := ⟨s₁⟩
  exact exercise_3_1.2 hS

/-! ## §3.2 Integral domains (printed pp. 20–21, PDF pp. 28–29) -/

/-- Garling's literal definition of an *integral domain* (§3.2, p. 20): a Garling ring in which
`rs = 0` implies `r = 0` or `s = 0`. -/
structure IsGarlingIntegralDomain (R : Type*) [CommRing R] : Prop where
  isRing : IsGarlingRing R (· + ·) (· * ·)
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ r s : R, r * s = 0 → r = 0 ∨ s = 0

/-- Equivalence between `IsGarlingIntegralDomain R` and Mathlib's `IsDomain R` (§3.2, p. 20). -/
theorem isGarlingIntegralDomain_iff (R : Type*) [CommRing R] :
    IsGarlingIntegralDomain R ↔ IsDomain R := by
  constructor
  · rintro ⟨hring, hnz⟩
    have _ : Nontrivial R := (isGarlingRing_iff_nontrivial R).mp hring
    have _ : NoZeroDivisors R := ⟨fun {a b} hab => hnz a b hab⟩
    exact NoZeroDivisors.to_isDomain R
  · intro _
    exact ⟨CommRing.isGarlingRing R, fun _ _ hrs => mul_eq_zero.mp hrs⟩

/-- Examples 1–4 & polynomial rings (§3.2, p. 20): fields, `ℤ`, `ℤ + iℤ`, `ℤ + i√5 ℤ`, and `R[x]`
(when `R` is an integral domain) are integral domains. -/
theorem examples_3_2_integralDomains :
    IsGarlingIntegralDomain ℤ ∧
      IsGarlingIntegralDomain GaussianIntSubring ∧
      IsGarlingIntegralDomain ZAdjoinI5 ∧
      (∀ (R : Type) [CommRing R], IsGarlingIntegralDomain R → IsGarlingIntegralDomain R[X]) := by
  refine ⟨(isGarlingIntegralDomain_iff ℤ).mpr inferInstance,
    (isGarlingIntegralDomain_iff GaussianIntSubring).mpr inferInstance,
    (isGarlingIntegralDomain_iff ZAdjoinI5).mpr inferInstance,
    fun R _ hR => ?_⟩
  have _ : IsDomain R := (isGarlingIntegralDomain_iff R).mp hR
  exact (isGarlingIntegralDomain_iff R[X]).mpr inferInstance

/-- Garling's fraction relation `(r₁, s₁) ~ (r₂, s₂) ↔ r₁ s₂ = r₂ s₁` on `R × R*` (§3.2, p. 20). -/
def fracRel (R : Type*) [CommRing R] (p₁ p₂ : R × {s : R // s ≠ 0}) : Prop :=
  p₁.1 * p₂.2.1 = p₂.1 * p₁.2.1

/-- Explicit proof of Garling's properties (a) reflexivity, (b) symmetry, and (c) transitivity of
`~` on `R × R*` when `R` is an integral domain (§3.2, p. 20). -/
theorem fracRel_equivalence (R : Type*) [CommRing R] [IsDomain R] :
    Equivalence (fracRel R) where
  refl p := rfl
  symm h := h.symm
  trans {p₁ p₂ p₃} h12 h23 := by
    unfold fracRel at *
    have key : (p₁.1 * p₃.2.1 - p₃.1 * p₁.2.1) * p₂.2.1 = 0 := by
      calc (p₁.1 * p₃.2.1 - p₃.1 * p₁.2.1) * p₂.2.1
        _ = (p₁.1 * p₂.2.1) * p₃.2.1 - p₃.1 * p₂.2.1 * p₁.2.1 := by ring
        _ = (p₂.1 * p₁.2.1) * p₃.2.1 - (p₂.1 * p₃.2.1) * p₁.2.1 := by rw [h12, h23]
        _ = 0 := by ring
    rcases mul_eq_zero.mp key with h0 | hs2
    · exact sub_eq_zero.mp h0
    · exact absurd hs2 p₂.2.2

/-- Setoid on `R × R*` from `fracRel R` (§3.2, p. 20). -/
def fracSetoid (R : Type*) [CommRing R] [IsDomain R] : Setoid (R × {s : R // s ≠ 0}) :=
  ⟨fracRel R, fracRel_equivalence R⟩

/-- Garling's explicit quotient `F = (R × R*) / ~` (§3.2, p. 21), identified canonically as a
bijection with Mathlib's `FractionRing R` (which constructs the same localization at `R⁰`). -/
def GarlingFieldOfFractions (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  Quotient (fracSetoid R)

/-- Canonical bijection between Garling's quotient `(R × R*) / ~` and `FractionRing R`, sending the
class `r / s` of `(r, s)` to `algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s`
(§3.2, p. 21). -/
noncomputable def garlingFieldOfFractionsEquiv (R : Type*) [CommRing R] [IsDomain R] :
    GarlingFieldOfFractions R ≃ FractionRing R where
  toFun := Quotient.lift
    (fun p => algebraMap R (FractionRing R) p.1 / algebraMap R (FractionRing R) p.2.1)
    (fun p₁ p₂ h => by
      have hrel : p₁.1 * p₂.2.1 = p₂.1 * p₁.2.1 := h
      have hs₁ : algebraMap R (FractionRing R) p₁.2.1 ≠ 0 :=
        fun h0 => p₁.2.2 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R _) _ h0)
      have hs₂ : algebraMap R (FractionRing R) p₂.2.1 ≠ 0 :=
        fun h0 => p₂.2.2 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R _) _ h0)
      rw [div_eq_div_iff hs₁ hs₂, ← map_mul, ← map_mul, hrel])
  invFun z :=
    let r := (IsLocalization.sec R⁰ z).1
    let s := (IsLocalization.sec R⁰ z).2
    Quotient.mk (fracSetoid R) ⟨r, ⟨s.1, mem_nonZeroDivisors_iff_ne_zero.mp s.2⟩⟩
  left_inv q := by
    induction q using Quotient.inductionOn with | h p =>
    dsimp only [Quotient.lift_mk]
    apply Quotient.sound
    let z : FractionRing R :=
      algebraMap R (FractionRing R) p.1 / algebraMap R (FractionRing R) p.2.1
    change (IsLocalization.sec R⁰ z).1 * p.2.1 = p.1 * (IsLocalization.sec R⁰ z).2.1
    have hsec := IsLocalization.sec_spec R⁰ z
    have hs : algebraMap R (FractionRing R) p.2.1 ≠ 0 :=
      fun h0 => p.2.2 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R _) _ h0)
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_mul, map_mul]
    calc algebraMap R (FractionRing R) (IsLocalization.sec R⁰ z).1 *
          algebraMap R (FractionRing R) p.2.1
      _ = (z * algebraMap R (FractionRing R) (IsLocalization.sec R⁰ z).2.1) *
            algebraMap R (FractionRing R) p.2.1 := by rw [← hsec]
      _ = (z * algebraMap R (FractionRing R) p.2.1) *
            algebraMap R (FractionRing R) (IsLocalization.sec R⁰ z).2.1 := by ring
      _ = algebraMap R (FractionRing R) p.1 *
            algebraMap R (FractionRing R) (IsLocalization.sec R⁰ z).2.1 := by
          dsimp only [z]
          rw [div_mul_cancel₀ _ hs]
  right_inv z := by
    dsimp only [Quotient.lift_mk]
    have hsec := IsLocalization.sec_spec R⁰ z
    have hs : algebraMap R (FractionRing R) (IsLocalization.sec R⁰ z).2.1 ≠ 0 :=
      fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp (IsLocalization.sec R⁰ z).2.2)
        ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R _) _ h0)
    exact (div_eq_iff hs).mpr hsec.symm

/-! ### Exercises 3.2–3.3 (§3.2, printed p. 21, PDF p. 29) -/

/-- Natural ring isomorphism `Frac(R[X_σ]) ≃+* Frac(F[X_σ])` for any integral domain `R` with field
of fractions `F` and variable indexing type `σ` (§3.2, Ex. 3.2, p. 21). -/
noncomputable def fractionRingMvPolynomialEquiv (σ R F : Type*) [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] :
    FractionRing (MvPolynomial σ R) ≃+* FractionRing (MvPolynomial σ F) := by
  let A := MvPolynomial σ R
  let B := MvPolynomial σ F
  let KA := FractionRing A
  let KB := FractionRing B
  have hinjRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hinjAB : Function.Injective (MvPolynomial.map (algebraMap R F) : A →+* B) :=
    MvPolynomial.map_injective (algebraMap R F) hinjRF
  let ιAB : A →+* KB := (algebraMap B KB).comp (MvPolynomial.map (algebraMap R F))
  have hinj_ιAB : Function.Injective ιAB :=
    (IsFractionRing.injective B KB).comp hinjAB
  let toFun : KA →+* KB := IsFractionRing.lift hinj_ιAB
  let ρR : R →+* KA := (algebraMap A KA).comp MvPolynomial.C
  have hinj_ρR : Function.Injective ρR :=
    (IsFractionRing.injective A KA).comp (MvPolynomial.C_injective σ R)
  let ρF : F →+* KA := IsFractionRing.lift hinj_ρR
  let β : B →+* KA := MvPolynomial.eval₂Hom ρF (fun i => algebraMap A KA (MvPolynomial.X i))
  have hβ_comp : β.comp (MvPolynomial.map (algebraMap R F)) = algebraMap A KA := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change β (MvPolynomial.map (algebraMap R F) (MvPolynomial.C r)) = _
      rw [MvPolynomial.map_C]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_C]
      exact IsFractionRing.lift_algebraMap hinj_ρR r
    · intro i
      change β (MvPolynomial.map (algebraMap R F) (MvPolynomial.X i)) = _
      rw [MvPolynomial.map_X]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_X']
  have hinj_β : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    classical
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset R⁰
      (p.support.image p.coeff)
    have hdp_in : ∀ m : σ →₀ ℕ,
        algebraMap R F (d : R) * p.coeff m ∈ Set.range (algebraMap R F) := by
      intro m
      by_cases hm : m ∈ p.support
      · have hmem := hd (p.coeff m) (Finset.mem_image_of_mem _ hm)
        rwa [Algebra.smul_def] at hmem
      · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
        exact ⟨0, map_zero _⟩
    let q : A := ∑ m ∈ p.support,
      MvPolynomial.monomial m (Classical.choose (hdp_in m))
    have hq_map : MvPolynomial.map (algebraMap R F) q =
        MvPolynomial.C (algebraMap R F (d : R)) * p := by
      ext m
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
      by_cases hm : m ∈ p.support
      · have hq_coeff : q.coeff m = Classical.choose (hdp_in m) := by
          dsimp only [q]
          rw [MvPolynomial.coeff_sum]
          simp [MvPolynomial.coeff_monomial, hm]
        rw [hq_coeff]
        exact Classical.choose_spec (hdp_in m)
      · have hq_coeff : q.coeff m = 0 := by
          dsimp only [q]
          rw [MvPolynomial.coeff_sum]
          refine Finset.sum_eq_zero fun x hx => ?_
          rw [MvPolynomial.coeff_monomial, ite_eq_right_iff]
          rintro rfl
          exact absurd hx hm
        rw [hq_coeff, MvPolynomial.notMem_support_iff.mp hm, map_zero, mul_zero]
    have hβq : algebraMap A KA q = 0 := by
      have h1 : β (MvPolynomial.map (algebraMap R F) q) = algebraMap A KA q :=
        RingHom.congr_fun hβ_comp q
      rw [← h1, hq_map, map_mul, hp, mul_zero]
    have hq0 : q = 0 := (injective_iff_map_eq_zero _).mp (IsFractionRing.injective A KA) q hβq
    have hmul0 : MvPolynomial.C (algebraMap R F (d : R)) * p = 0 := by
      simpa [hq0] using hq_map.symm
    have hd_ne0 : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.2
    have hCd_ne0 : (MvPolynomial.C (algebraMap R F (d : R)) : B) ≠ 0 := by
      intro hc0
      apply hd_ne0
      apply hinjRF
      apply MvPolynomial.C_injective σ F
      simp at hc0
    exact (mul_eq_zero.mp hmul0).resolve_left hCd_ne0
  let invFun : KB →+* KA := IsFractionRing.lift hinj_β
  have hleft : invFun.comp toFun = RingHom.id KA := by
    apply IsLocalization.ringHom_ext A⁰
    apply MvPolynomial.ringHom_ext
    · intro r
      change invFun (toFun (algebraMap A KA (MvPolynomial.C r))) =
        algebraMap A KA (MvPolynomial.C r)
      dsimp only [toFun, invFun]
      rw [IsFractionRing.lift_algebraMap hinj_ιAB]
      change IsFractionRing.lift hinj_β
        (algebraMap B KB (MvPolynomial.map (algebraMap R F) (MvPolynomial.C r))) = _
      rw [MvPolynomial.map_C, IsFractionRing.lift_algebraMap hinj_β]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_C]
      exact IsFractionRing.lift_algebraMap hinj_ρR r
    · intro i
      change invFun (toFun (algebraMap A KA (MvPolynomial.X i))) =
        algebraMap A KA (MvPolynomial.X i)
      dsimp only [toFun, invFun]
      rw [IsFractionRing.lift_algebraMap hinj_ιAB]
      change IsFractionRing.lift hinj_β
        (algebraMap B KB (MvPolynomial.map (algebraMap R F) (MvPolynomial.X i))) = _
      rw [MvPolynomial.map_X, IsFractionRing.lift_algebraMap hinj_β]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_X']
  have hright : toFun.comp invFun = RingHom.id KB := by
    apply IsLocalization.ringHom_ext B⁰
    apply MvPolynomial.ringHom_ext
    · intro x
      obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective (A := R) x
      change toFun (invFun (algebraMap B KB
        (MvPolynomial.C (algebraMap R F r / algebraMap R F s)))) = _
      dsimp only [toFun, invFun]
      rw [IsFractionRing.lift_algebraMap hinj_β]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_C, map_div₀]
      have hρr : ρF (algebraMap R F r) = algebraMap A KA (MvPolynomial.C r) :=
        IsFractionRing.lift_algebraMap hinj_ρR r
      have hρs : ρF (algebraMap R F s) = algebraMap A KA (MvPolynomial.C s) :=
        IsFractionRing.lift_algebraMap hinj_ρR s
      rw [hρr, hρs, map_div₀, IsFractionRing.lift_algebraMap hinj_ιAB,
        IsFractionRing.lift_algebraMap hinj_ιAB]
      change ιAB (MvPolynomial.C r) / ιAB (MvPolynomial.C s) =
        ((algebraMap B KB).comp MvPolynomial.C) (algebraMap R F r / algebraMap R F s)
      rw [map_div₀ ((algebraMap B KB).comp MvPolynomial.C)]
      dsimp only [ιAB, RingHom.comp_apply]
      rw [MvPolynomial.map_C, MvPolynomial.map_C]
    · intro i
      change toFun (invFun (algebraMap B KB (MvPolynomial.X i))) =
        algebraMap B KB (MvPolynomial.X i)
      dsimp only [toFun, invFun]
      rw [IsFractionRing.lift_algebraMap hinj_β]
      dsimp only [β]
      rw [MvPolynomial.eval₂Hom_X', IsFractionRing.lift_algebraMap hinj_ιAB]
      change algebraMap B KB (MvPolynomial.map (algebraMap R F) (MvPolynomial.X i)) = _
      rw [MvPolynomial.map_X]
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := fun x => RingHom.congr_fun hleft x
    right_inv := fun y => RingHom.congr_fun hright y
    map_mul' := toFun.map_mul
    map_add' := toFun.map_add
  }

/-- **Exercise 3.2** (§3.2, p. 21): For an integral domain `R` with field of fractions `F`, the
field of fractions of `R[x_1, ..., x_n]` is naturally ring-isomorphic to `F(x_1, ..., x_n)`,
commuting with the canonical embeddings of `R[x_1, ..., x_n]`. -/
theorem exercise_3_2 (n : ℕ) (R F : Type*) [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] :
    ∃ e : FractionRing (MvPolynomial (Fin n) R) ≃+* FractionRing (MvPolynomial (Fin n) F),
      ∀ p : MvPolynomial (Fin n) R,
        e (algebraMap _ _ p) =
          algebraMap _ _ (MvPolynomial.map (algebraMap R F) p) := by
  refine ⟨fractionRingMvPolynomialEquiv (Fin n) R F, fun p => ?_⟩
  unfold fractionRingMvPolynomialEquiv
  dsimp only [RingEquiv.coe_mk, Equiv.coe_fn_mk]
  exact IsFractionRing.lift_algebraMap _ p

/-- **Exercise 3.3** (§3.2, p. 21): An integral domain with a finite number of elements is always a
field (proved both as `IsField R` and in Garling's §1.2 `IsGarlingField` sense). -/
theorem exercise_3_3 (R : Type*) [CommRing R] [IsDomain R] [Finite R] :
    IsField R ∧ IsGarlingField R (· + ·) (· * ·) := by
  have hf : IsField R := Finite.isField_of_domain R
  let _ : Field R := hf.toField
  exact ⟨hf, Field.isGarlingField R⟩

/-! ## §3.3 Ideals (printed pp. 21–24, PDF pp. 29–32) -/

/-- Garling's three-condition definition of a *ring homomorphism* `ϕ : R → S` (§3.3, p. 21). -/
structure IsGarlingRingHom {R S : Type*} [CommRing R] [CommRing S] (ϕ : R → S) : Prop where
  map_add : ∀ r₁ r₂ : R, ϕ (r₁ + r₂) = ϕ r₁ + ϕ r₂
  map_mul : ∀ r₁ r₂ : R, ϕ (r₁ * r₂) = ϕ r₁ * ϕ r₂
  map_one : ϕ 1 = 1

theorem ringHom_isGarlingRingHom {R S : Type*} [CommRing R] [CommRing S] (ϕ : R →+* S) :
    IsGarlingRingHom ϕ :=
  ⟨ϕ.map_add, ϕ.map_mul, ϕ.map_one⟩

/-- Monomorphism, epimorphism, and isomorphism of rings (§3.3, p. 21). -/
def IsRingMonomorphism {R S : Type*} [CommRing R] [CommRing S] (ϕ : R →+* S) : Prop :=
  Function.Injective ϕ

def IsRingEpimorphism {R S : Type*} [CommRing R] [CommRing S] (ϕ : R →+* S) : Prop :=
  Function.Surjective ϕ

def IsRingIsomorphism {R S : Type*} [CommRing R] [CommRing S] (ϕ : R →+* S) : Prop :=
  Function.Bijective ϕ

/-- Garling's two-clause definition of an *ideal* `J` of a ring `R` (§3.3, p. 21): a non-empty
subset closed under addition and multiplication by arbitrary elements of `R`. -/
structure IsGarlingIdeal {R : Type*} [CommRing R] (J : Set R) : Prop where
  nonempty : J.Nonempty
  add_mem : ∀ ⦃r s : R⦄, r ∈ J → s ∈ J → r + s ∈ J
  mul_mem_left : ∀ (r : R) ⦃s : R⦄, s ∈ J → r * s ∈ J

/-- Equivalence between Garling's subset definition `IsGarlingIdeal J` and Mathlib's `Ideal R`
(§3.3, pp. 21–22). -/
theorem isGarlingIdeal_iff {R : Type*} [CommRing R] (J : Set R) :
    IsGarlingIdeal J ↔ ∃ I : Ideal R, (I : Set R) = J := by
  constructor
  · rintro ⟨⟨x₀, hx₀⟩, hadd, hmul⟩
    have h0 : (0 : R) ∈ J := by simpa using hmul 0 hx₀
    refine ⟨{
      carrier := J
      add_mem' := fun hr hs => hadd hr hs
      zero_mem' := h0
      smul_mem' := fun r s hs => hmul r hs
    }, rfl⟩
  · rintro ⟨I, rfl⟩
    exact ⟨⟨0, I.zero_mem⟩, fun _ _ hr hs => I.add_mem hr hs, fun r _ hs => I.mul_mem_left r hs⟩

/-- A *proper ideal* in `R` is an ideal other than `R` (`J ≠ ⊤`, §3.3, p. 22). -/
def IsProperIdeal {R : Type*} [CommRing R] (J : Ideal R) : Prop :=
  J ≠ ⊤

/-- Example 1 (§3.3, p. 22): Every ideal of `ℤ` has the form `nℤ` (`Ideal.span {(n : ℤ)}`). -/
theorem int_ideal_eq_span_nat (I : Ideal ℤ) :
    ∃ n : ℕ, I = Ideal.span {(n : ℤ)} := by
  obtain ⟨n, hn⟩ := int_addSubgroup_eq_zmultiples I.toAddSubgroup
  refine ⟨n, ?_⟩
  ext x
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hxI
    have hxm : x ∈ AddSubgroup.zmultiples (n : ℤ) := hn ▸ hxI
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hxm
    exact ⟨k, by rw [← hk, zsmul_eq_mul, Int.cast_id, mul_comm]⟩
  · rintro ⟨k, rfl⟩
    change (n : ℤ) * k ∈ I.toAddSubgroup
    rw [hn]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [zsmul_eq_mul, Int.cast_id, mul_comm]⟩

/-- Example 2 (§3.3, p. 22): For a non-empty subset `A` of a ring `R`, the ideal `(A)` generated by
`A` equals both the intersection of all ideals containing `A` and the set of finite `R`-linear
combinations `r₁ a₁ + ⋯ + r_n a_n` (`n ≥ 1`, `r_i ∈ R`, `a_i ∈ A`). -/
theorem ideal_span_nonempty_eq {R : Type*} [CommRing R] {A : Set R} (hA : A.Nonempty) :
    Ideal.span A = sInf {I : Ideal R | A ⊆ I} ∧
      (Ideal.span A : Set R) =
        {r : R | ∃ (n : ℕ) (_ : 0 < n) (rv av : Fin n → R),
          (∀ i, av i ∈ A) ∧ r = ∑ i, rv i * av i} := by
  refine ⟨rfl, ?_⟩
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro a ha
      exact ⟨1, Nat.zero_lt_one, fun _ => 1, fun _ => a, fun _ => ha, by simp⟩
    · obtain ⟨a₀, ha₀⟩ := hA
      exact ⟨1, Nat.zero_lt_one, fun _ => 0, fun _ => a₀, fun _ => ha₀, by simp⟩
    · rintro y z _ _ ⟨n₁, hn₁, rv₁, av₁, hav₁, rfl⟩ ⟨n₂, hn₂, rv₂, av₂, hav₂, rfl⟩
      refine ⟨n₁ + n₂, by omega, Fin.append rv₁ rv₂, Fin.append av₁ av₂, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · simpa using hav₁ i₁
        · simpa using hav₂ i₂
      · rw [Fin.sum_univ_add]
        simp
    · rintro c y _ ⟨n, hn, rv, av, hav, rfl⟩
      refine ⟨n, hn, fun i => c * rv i, av, hav, ?_⟩
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc c (rv i) (av i)).symm
  · rintro ⟨n, _, rv, av, hav, rfl⟩
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (hav i))

/-- Kernel of a ring homomorphism between Garling rings is a proper ideal, and the quotient `R / J`
by any proper ideal `J` is a Garling ring (§3.3, p. 22). -/
theorem ker_isProperIdeal_and_quotient_nontrivial {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [Nontrivial S] (ϕ : R →+* S) {J : Ideal R} (hJ : IsProperIdeal J) :
    IsProperIdeal (RingHom.ker ϕ) ∧ Nontrivial (R ⧸ J) := by
  refine ⟨?_, Ideal.Quotient.nontrivial_iff.mpr hJ⟩
  intro htop
  have h1 : (1 : R) ∈ RingHom.ker ϕ := htop ▸ Submodule.mem_top
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- **Theorem 3.1** (§3.3, pp. 22–23): Suppose that `ϕ` is a ring homomorphism from a ring `R` to a
ring `S`, with kernel `J`. There is a (unique) ring isomorphism `ϕ̃` from `R / J` onto `ϕ(R)` such
that `ϕ = ϕ̃ ∘ q`. -/
theorem theorem_3_1 {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
    (ϕ : R →+* S) :
    ∃ e : (R ⧸ RingHom.ker ϕ) ≃+* ϕ.range,
      (∀ r : R, (e (Ideal.Quotient.mk (RingHom.ker ϕ) r) : S) = ϕ r) ∧
      ∀ e' : (R ⧸ RingHom.ker ϕ) ≃+* ϕ.range,
        (∀ r : R, (e' (Ideal.Quotient.mk (RingHom.ker ϕ) r) : S) = ϕ r) → e' = e := by
  refine ⟨RingHom.quotientKerEquivRange ϕ, fun r => rfl, fun e' he' => ?_⟩
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact he' r

/-- Characteristic of an integral domain (§3.3, p. 23): if `R` is an integral domain, `char R`
(`ringChar R`) is either `0` or a prime number. -/
theorem integralDomain_char_zero_or_prime (R : Type*) [CommRing R] [IsDomain R] :
    ringChar R = 0 ∨ Nat.Prime (ringChar R) := by
  rcases CharP.char_is_prime_or_zero R (ringChar R) with hp | hz
  · exact Or.inr hp
  · exact Or.inl hz

/-! ### Exercises 3.4–3.9 (§3.3, printed pp. 23–24, PDF pp. 31–32) -/

/-- **Exercise 3.4** (§3.3, p. 23): If `a` and `b` are elements of a ring `R` for which
`(a, b) = R`, then `(a^m, b^n) = R` for any positive integers `m` and `n`. -/
theorem exercise_3_4 {R : Type*} [CommRing R] {a b : R}
    (hab : Ideal.span {a, b} = ⊤) {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) :
    Ideal.span {a ^ m, b ^ n} = ⊤ := by
  rw [Ideal.eq_top_iff_one] at hab ⊢
  rw [Ideal.mem_span_pair] at hab ⊢
  obtain ⟨u, v, huv⟩ := hab
  have hpow : (u * a + v * b) ^ (m + n) = 1 := by rw [huv, one_pow]
  rw [add_pow] at hpow
  have hmem : ∑ i ∈ Finset.range (m + n + 1),
      (u * a) ^ i * (v * b) ^ (m + n - i) * ((m + n).choose i : R) ∈
      Ideal.span {a ^ m, b ^ n} := by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases him : m ≤ i
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
      have ha : a ^ m ∣ (u * a) ^ (m + k) * (v * b) ^ (m + n - (m + k)) *
          ((m + n).choose (m + k) : R) := by
        refine ⟨u ^ (m + k) * a ^ k * (v * b) ^ (m + n - (m + k)) *
          ((m + n).choose (m + k) : R), ?_⟩
        rw [mul_pow, pow_add]
        ring
      rcases ha with ⟨c, hc⟩
      rw [hc, mul_comm]
      exact Ideal.mul_mem_left _ c (Ideal.subset_span (by simp))
    · have hni : n ≤ m + n - i := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hni
      have hb : b ^ n ∣ (u * a) ^ i * (v * b) ^ (m + n - i) *
          ((m + n).choose i : R) := by
        refine ⟨(u * a) ^ i * v ^ (n + k) * b ^ k * ((m + n).choose i : R), ?_⟩
        rw [hk, mul_pow, pow_add]
        ring
      rcases hb with ⟨c, hc⟩
      rw [hc, mul_comm]
      exact Ideal.mul_mem_left _ c (Ideal.subset_span (by simp))
  rw [hpow] at hmem
  exact Ideal.mem_span_pair.mp hmem

/-- **Exercise 3.5** (§3.3, p. 24): In an integral domain `R` with characteristic `k = ringChar R`,
every non-zero element `r ∈ R` has additive order `k` (if `k > 0`) or infinite additive order
(if `k = 0`), proved both for `addOrderOf` and for Garling's subgroup cardinality `setOrder`. -/
theorem exercise_3_5 {R : Type*} [CommRing R] [IsDomain R] {r : R} (hr : r ≠ 0) :
    (0 < ringChar R →
      addOrderOf r = ringChar R ∧ setOrder (AddSubgroup.zmultiples r) = ringChar R) ∧
    (ringChar R = 0 →
      ¬ IsOfFinAddOrder r ∧ setOrder (AddSubgroup.zmultiples r) = ⊤) := by
  have hnsmul_zero_iff : ∀ n : ℕ, n • r = 0 ↔ ringChar R ∣ n := by
    intro n
    rw [nsmul_eq_mul, mul_eq_zero]
    constructor
    · rintro (hn0 | hr0)
      · exact (ringChar.spec R n).mp hn0
      · exact absurd hr0 hr
    · intro hdvd
      exact Or.inl ((ringChar.spec R n).mpr hdvd)
  refine ⟨fun hk => ?_, fun hk0 => ?_⟩
  · have hkr : ringChar R • r = 0 := (hnsmul_zero_iff (ringChar R)).mpr dvd_rfl
    have hdvd1 : addOrderOf r ∣ ringChar R := addOrderOf_dvd_of_nsmul_eq_zero hkr
    have hfin_ord : IsOfFinAddOrder r := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨ringChar R, hk, hkr⟩
    have hdvd2 : ringChar R ∣ addOrderOf r :=
      (hnsmul_zero_iff (addOrderOf r)).mp (addOrderOf_nsmul_eq_zero r)
    have ha : addOrderOf r = ringChar R := Nat.dvd_antisymm hdvd1 hdvd2
    refine ⟨ha, ?_⟩
    have hcard : Nat.card (AddSubgroup.zmultiples r) = addOrderOf r :=
      Nat.card_zmultiples r
    have _ : Finite (AddSubgroup.zmultiples r) :=
      Nat.finite_of_card_ne_zero (by rw [hcard, ha]; exact hk.ne')
    let _ : Fintype (AddSubgroup.zmultiples r) := Fintype.ofFinite (AddSubgroup.zmultiples r)
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard, ha]
  · have hinf_ord : ¬ IsOfFinAddOrder r := by
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      rintro ⟨n, hn, hnr⟩
      have hdvd : 0 ∣ n := hk0 ▸ (hnsmul_zero_iff n).mp hnr
      exact hn.ne' (zero_dvd_iff.mp hdvd)
    refine ⟨hinf_ord, ?_⟩
    have hinj : Function.Injective (fun n : ℕ =>
        (⟨n • r, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, natCast_zsmul r n⟩⟩ :
          AddSubgroup.zmultiples r)) := by
      intro n₁ n₂ h
      have heq : n₁ • r = n₂ • r := congrArg Subtype.val h
      rcases le_total n₁ n₂ with hle | hle
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [add_nsmul] at heq
        have hdr : d • r = 0 := add_left_cancel (by rw [add_zero]; exact heq.symm)
        have := zero_dvd_iff.mp (hk0 ▸ (hnsmul_zero_iff d).mp hdr)
        omega
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [add_nsmul] at heq
        have hdr : d • r = 0 := add_left_cancel (by rw [add_zero]; exact heq)
        have := zero_dvd_iff.mp (hk0 ▸ (hnsmul_zero_iff d).mp hdr)
        omega
    have _ : Infinite (AddSubgroup.zmultiples r) := Infinite.of_injective _ hinj
    simp [setOrder]

/-- **Exercise 3.6** (§3.3, p. 24): If `R` is an integral domain of characteristic `k > 0`, then
`k` is prime (so `ℤ_k = ZMod k` is a field) and `R` becomes a vector space (`Module (ZMod k) R`)
over `ℤ_k` via `(n mod k) • r = ϕ(n) * r`. -/
theorem exercise_3_6 (R : Type*) [CommRing R] [IsDomain R] (k : ℕ) [CharP R k] (hk : 0 < k) :
    Nat.Prime k ∧
      ∃ (_ : Field (ZMod k)) (m : Module (ZMod k) R),
        ∀ (c : ZMod k) (r : R), @SMul.smul _ _ m.toSMul c r =
          ZMod.castHom (dvd_refl k) R c * r := by
  have hk_eq : ringChar R = k := ringChar.eq R k
  have hprime : Nat.Prime k := by
    rcases integralDomain_char_zero_or_prime R with hz | hp
    · omega
    · exact hk_eq ▸ hp
  have _ : Fact (Nat.Prime k) := ⟨hprime⟩
  let f : ZMod k →+* R := ZMod.castHom (dvd_refl k) R
  let modR : Module (ZMod k) R := Module.compHom R f
  exact ⟨hprime, inferInstance, modR, fun _ _ => rfl⟩

/-- Explicit `n`-generator ideal `I_n = (2^{n-1}, 2^{n-2} x, ..., x^{n-1})` in `ℤ[x]` for
Exercise 3.7 (§3.3, p. 24). -/
noncomputable def ex37Gen (n : ℕ) (i : Fin n) : ℤ[X] :=
  Polynomial.C ((2 : ℤ) ^ (n - 1 - (i : ℕ))) * Polynomial.X ^ (i : ℕ)

noncomputable def ex37Ideal (n : ℕ) : Ideal ℤ[X] :=
  Ideal.span (Set.range (ex37Gen n))

theorem mem_ex37Ideal_iff {n : ℕ} (hn : 0 < n) (f : ℤ[X]) :
    f ∈ ex37Ideal n ↔ ∀ j : ℕ, j < n - 1 → ((2 : ℤ) ^ (n - 1 - j)) ∣ f.coeff j := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i, rfl⟩ j hj
      simp only [ex37Gen, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs with hji
      · subst hji
        rw [mul_one]
      · rw [mul_zero]
        exact ⟨0, (mul_zero _).symm⟩
    · intro j _
      rw [Polynomial.coeff_zero]
      exact ⟨0, (mul_zero _).symm⟩
    · intro g h _ _ hg hh j hj
      rw [Polynomial.coeff_add]
      exact dvd_add (hg j hj) (hh j hj)
    · intro p g _ hg j hj
      rw [smul_eq_mul, Polynomial.coeff_mul]
      refine Finset.dvd_sum fun uv huv => ?_
      rw [Finset.mem_antidiagonal] at huv
      have h2le : n - 1 - j ≤ n - 1 - uv.2 := by omega
      have hdvd : (2 : ℤ) ^ (n - 1 - j) ∣ g.coeff uv.2 :=
        dvd_trans (pow_dvd_pow 2 h2le) (hg uv.2 (by omega))
      exact dvd_mul_of_dvd_right hdvd _
  · intro hcoeff
    have hsplit : f =
        (∑ j ∈ Finset.range (n - 1), Polynomial.C (f.coeff j) * Polynomial.X ^ j) +
        Polynomial.X ^ (n - 1) *
          (∑ j ∈ Finset.range (f.natDegree + 1 - (n - 1)),
            Polynomial.C (f.coeff (n - 1 + j)) * Polynomial.X ^ j) := by
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
      by_cases hk : k < n - 1
      · have hnot : ¬ n - 1 ≤ k := by omega
        simp [hk, hnot]
      · have hle : n - 1 ≤ k := by omega
        by_cases hdeg : k < f.natDegree + 1
        · have hsub : k - (n - 1) < f.natDegree + 1 - (n - 1) := by omega
          have hadd : n - 1 + (k - (n - 1)) = k := by omega
          simp [hk, hle, hsub, hadd]
        · have hsub : ¬ k - (n - 1) < f.natDegree + 1 - (n - 1) := by omega
          have hc0 : f.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [hk, hle, hsub, hc0]
    rw [hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · refine Ideal.sum_mem _ fun j hj => ?_
      rw [Finset.mem_range] at hj
      obtain ⟨c, hc⟩ := hcoeff j hj
      have hgen : ex37Gen n ⟨j, by omega⟩ =
          Polynomial.C ((2 : ℤ) ^ (n - 1 - j)) * Polynomial.X ^ j := rfl
      have hterm : Polynomial.C (f.coeff j) * Polynomial.X ^ j =
          Polynomial.C c * ex37Gen n ⟨j, by omega⟩ := by
        rw [hgen, hc, Polynomial.C_mul]
        ring
      rw [hterm]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, by omega⟩, rfl⟩)
    · have hlast : ex37Gen n ⟨n - 1, by omega⟩ = Polynomial.X ^ (n - 1) := by
        simp [ex37Gen]
      rw [mul_comm, ← hlast]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨n - 1, by omega⟩, rfl⟩)

/-- Surjective `ZMod 2`-valued reduction map `Φ : ex37Ideal n → (Fin n → ZMod 2)` sending
`f ∈ ex37Ideal n` to `((f.coeff j / 2^{n-1-j}) : ZMod 2)` (§3.3, Ex. 3.7). -/
noncomputable def ex37Proj (n : ℕ) (f : ℤ[X]) : Fin n → ZMod 2 :=
  fun j => ((f.coeff j / ((2 : ℤ) ^ (n - 1 - (j : ℕ)))) : ℤ)

theorem ex37Proj_zero (n : ℕ) : ex37Proj n 0 = 0 := by
  ext j
  simp [ex37Proj]

theorem ex37Proj_add {n : ℕ} (hn : 0 < n) {f g : ℤ[X]}
    (hf : f ∈ ex37Ideal n) (hg : g ∈ ex37Ideal n) :
    ex37Proj n (f + g) = ex37Proj n f + ex37Proj n g := by
  ext j
  simp only [ex37Proj, Pi.add_apply, Polynomial.coeff_add]
  have hp2 : ((2 : ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hj : (j : ℕ) < n - 1
  · obtain ⟨cf, hcf⟩ := (mem_ex37Ideal_iff hn f).mp hf j hj
    obtain ⟨cg, hcg⟩ := (mem_ex37Ideal_iff hn g).mp hg j hj
    rw [hcf, hcg, ← mul_add, Int.mul_ediv_cancel_left _ hp2,
      Int.mul_ediv_cancel_left _ hp2, Int.mul_ediv_cancel_left _ hp2, Int.cast_add]
  · have hj_eq : (j : ℕ) = n - 1 := by omega
    simp [hj_eq]

theorem ex37Proj_mul {n : ℕ} (hn : 0 < n) (p : ℤ[X]) {f : ℤ[X]} (hf : f ∈ ex37Ideal n) :
    ex37Proj n (p * f) = ((p.coeff 0 : ZMod 2)) • ex37Proj n f := by
  ext j
  simp only [ex37Proj, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_mul]
  let d : ℤ := (2 : ℤ) ^ (n - 1 - (j : ℕ))
  have hd_ne : d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdvd_term : ∀ uv ∈ Finset.antidiagonal (j : ℕ),
      d ∣ p.coeff uv.1 * f.coeff uv.2 := by
    intro uv huv
    rw [Finset.mem_antidiagonal] at huv
    by_cases huv2 : uv.2 < n - 1
    · have hle : n - 1 - (j : ℕ) ≤ n - 1 - uv.2 := by omega
      exact dvd_mul_of_dvd_right
        (dvd_trans (pow_dvd_pow 2 hle) ((mem_ex37Ideal_iff hn f).mp hf uv.2 huv2)) _
    · have hd1 : d = 1 := by
        have : n - 1 - (j : ℕ) = 0 := by omega
        simp [d, this]
      rw [hd1]
      exact one_dvd _
  have hdvd_2d_pos : ∀ uv ∈ Finset.antidiagonal (j : ℕ), uv.1 ≠ 0 →
      (2 * d) ∣ p.coeff uv.1 * f.coeff uv.2 := by
    intro uv huv huv1
    rw [Finset.mem_antidiagonal] at huv
    have huv2 : uv.2 < n - 1 := by omega
    have hexp : n - 1 - uv.2 = (n - 1 - (j : ℕ)) + uv.1 := by omega
    have hle : (n - 1 - (j : ℕ)) + 1 ≤ n - 1 - uv.2 := by omega
    have hpow : 2 * d = (2 : ℤ) ^ ((n - 1 - (j : ℕ)) + 1) := by
      simp [d, pow_succ, mul_comm]
    rw [hpow]
    exact dvd_mul_of_dvd_right
      (dvd_trans (pow_dvd_pow 2 hle) ((mem_ex37Ideal_iff hn f).mp hf uv.2 huv2)) _
  have hmem0 : ((0 : ℕ), (j : ℕ)) ∈ Finset.antidiagonal (j : ℕ) := by simp
  rw [← Finset.add_sum_erase _ _ hmem0]
  have herase_dvd : (2 * d) ∣ ∑ uv ∈ (Finset.antidiagonal (j : ℕ)).erase (0, (j : ℕ)),
      p.coeff uv.1 * f.coeff uv.2 := by
    refine Finset.dvd_sum fun uv huv => ?_
    rcases Finset.mem_erase.mp huv with ⟨hne, hanti⟩
    have huv1 : uv.1 ≠ 0 := by
      intro h0
      rw [Finset.mem_antidiagonal] at hanti
      apply hne
      ext <;> omega
    exact hdvd_2d_pos uv hanti huv1
  obtain ⟨q0, hq0⟩ : d ∣ f.coeff (j : ℕ) := by
    by_cases hj : (j : ℕ) < n - 1
    · exact (mem_ex37Ideal_iff hn f).mp hf j hj
    · have : n - 1 - (j : ℕ) = 0 := by omega
      simp [d, this]
  obtain ⟨qrest, hqrest⟩ := herase_dvd
  have htot : p.coeff 0 * f.coeff (j : ℕ) +
      (∑ uv ∈ (Finset.antidiagonal (j : ℕ)).erase (0, (j : ℕ)), p.coeff uv.1 * f.coeff uv.2) =
      d * (p.coeff 0 * q0 + 2 * qrest) := by
    rw [hq0, hqrest]
    ring
  rw [htot, hq0, Int.mul_ediv_cancel_left _ hd_ne, Int.mul_ediv_cancel_left _ hd_ne]
  push_cast
  have h2z : ((2 : ZMod 2)) = 0 := rfl
  simp [h2z]

/-- **Exercise 3.7** (§3.3, p. 24): For every positive integer `n`, the ideal `ex37Ideal n` in
`ℤ[x]` is generated by `n` elements and is not generated by fewer than `n` elements. -/
theorem exercise_3_7 (n : ℕ) (hn : 0 < n) :
    ∃ I : Ideal ℤ[X],
      (∃ A : Set ℤ[X], A.Finite ∧ A.ncard = n ∧ Ideal.span A = I) ∧
      ¬ ∃ B : Set ℤ[X], B.Finite ∧ B.ncard < n ∧ Ideal.span B = I := by
  refine ⟨ex37Ideal n, ?_, ?_⟩
  · refine ⟨Set.range (ex37Gen n), Set.finite_range _, ?_, rfl⟩
    have hinj : Function.Injective (ex37Gen n) := by
      intro i₁ i₂ h
      have hc := congrArg (fun p => p.coeff (i₁ : ℕ)) h
      simp only [ex37Gen, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_true, mul_one] at hc
      by_contra hne
      have hne_val : (i₁ : ℕ) ≠ (i₂ : ℕ) := Fin.val_ne_of_ne hne
      rw [ite_eq_right_iff.mpr (fun heq => absurd heq hne_val), mul_zero] at hc
      exact pow_ne_zero _ (by norm_num) hc
    rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
  · rintro ⟨B, hBfin, hBcard, hBspan⟩
    classical
    let S : Finset (Fin n → ZMod 2) := (hBfin.image (ex37Proj n)).toFinset
    have hScard : S.card < n := by
      have h1 : S.card = (ex37Proj n '' B).ncard := by
        rw [← Set.ncard_coe_finset]
        simp [S]
      have h2 : (ex37Proj n '' B).ncard ≤ B.ncard := Set.ncard_image_le hBfin
      omega
    let linComb : (S → ZMod 2) → (Fin n → ZMod 2) := fun c => ∑ v : S, c v • v.1
    have hzero_mem : (0 : Fin n → ZMod 2) ∈ Set.range linComb :=
      ⟨0, by simp [linComb]⟩
    have hadd_mem : ∀ {x y}, x ∈ Set.range linComb → y ∈ Set.range linComb →
        x + y ∈ Set.range linComb := by
      rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, by simp [linComb, add_smul, Finset.sum_add_distrib]⟩
    have hsmul_mem : ∀ (a : ZMod 2) {x}, x ∈ Set.range linComb →
        a • x ∈ Set.range linComb := by
      rintro a _ ⟨c, rfl⟩
      refine ⟨a • c, ?_⟩
      simp only [linComb, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun v _ => by ext j; simp [mul_assoc]
    have hsub_range : ∀ f ∈ ex37Ideal n, ex37Proj n f ∈ Set.range linComb := by
      intro f hf
      rw [← hBspan] at hf
      refine Submodule.span_induction
        (p := fun g _ => ex37Proj n g ∈ Set.range linComb) ?_ ?_ ?_ ?_ hf
      · intro b hb
        have hmemS : ex37Proj n b ∈ S := (Set.Finite.mem_toFinset _).mpr ⟨b, hb, rfl⟩
        refine ⟨fun v => if v = ⟨ex37Proj n b, hmemS⟩ then 1 else 0, ?_⟩
        simp [linComb]
      · rw [ex37Proj_zero]
        exact hzero_mem
      · intro g₁ g₂ hg₁ hg₂ h₁ h₂
        have hg₁' : g₁ ∈ ex37Ideal n := hBspan ▸ hg₁
        have hg₂' : g₂ ∈ ex37Ideal n := hBspan ▸ hg₂
        rw [ex37Proj_add hn hg₁' hg₂']
        exact hadd_mem h₁ h₂
      · intro p g hg hproj
        have hg' : g ∈ ex37Ideal n := hBspan ▸ hg
        rw [smul_eq_mul, ex37Proj_mul hn p hg']
        exact hsmul_mem _ hproj
    have hsurj : Function.Surjective linComb := by
      intro v
      have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ZMod 2) := by
        ext j
        simp [Pi.single_apply]
      rw [hv]
      have hsum_mem : ∀ s : Finset (Fin n),
          (∑ i ∈ s, v i • Pi.single i (1 : ZMod 2)) ∈ Set.range linComb := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using hzero_mem
        | insert i s hi ih =>
          rw [Finset.sum_insert hi]
          refine hadd_mem (hsmul_mem (v i) ?_) ih
          have hgi : ex37Gen n i ∈ ex37Ideal n := Ideal.subset_span ⟨i, rfl⟩
          have hproj_gi : ex37Proj n (ex37Gen n i) = Pi.single i (1 : ZMod 2) := by
            ext j
            simp only [ex37Proj, ex37Gen, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            by_cases hji : (j : ℕ) = (i : ℕ)
            · have hfin_eq : j = i := Fin.ext hji
              subst hfin_eq
              simp
            · have hfin_ne : j ≠ i := fun h => hji (congrArg Fin.val h)
              simp [hji, hfin_ne]
          rw [← hproj_gi]
          exact hsub_range _ hgi
      exact hsum_mem Finset.univ
    have hcard_le : Fintype.card (Fin n → ZMod 2) ≤ Fintype.card (S → ZMod 2) :=
      Fintype.card_le_of_surjective linComb hsurj
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_coe] at hcard_le
    have hpow_lt : 2 ^ S.card < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hScard
    omega

/-- Polynomial evaluation homomorphism `ϕ : K[x] →+* K^K` for Exercise 3.8 (§3.3, p. 24). -/
noncomputable def polyEvalRingHom (K : Type*) [CommRing K] : K[X] →+* (K → K) where
  toFun f k := f.eval k
  map_one' := by ext k; simp
  map_mul' f g := by ext k; simp
  map_zero' := by ext k; simp
  map_add' f g := by ext k; simp

/-- **Exercise 3.8** (§3.3, p. 24): For any field `K`, `ϕ = polyEvalRingHom K : K[x] →+* K^K` is a
ring homomorphism; if `K` is finite, `ϕ` is an epimorphism and not a monomorphism; if `K` is
infinite, `ϕ` is a monomorphism and not an epimorphism. -/
theorem exercise_3_8 (K : Type*) [Field K] :
    IsGarlingRingHom (polyEvalRingHom K) ∧
      (Finite K → IsRingEpimorphism (polyEvalRingHom K) ∧ ¬ IsRingMonomorphism (polyEvalRingHom K)) ∧
      (Infinite K → IsRingMonomorphism (polyEvalRingHom K) ∧ ¬ IsRingEpimorphism (polyEvalRingHom K)) := by
  refine ⟨ringHom_isGarlingRingHom (polyEvalRingHom K), fun hfin => ?_, fun hinf => ?_⟩
  · classical
    let _ : Fintype K := Fintype.ofFinite K
    refine ⟨?_, ?_⟩
    · intro g
      let delta : K → K[X] := fun a =>
        ∏ b ∈ Finset.univ.erase a, Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C b)
      let f : K[X] := ∑ a ∈ Finset.univ, Polynomial.C (g a) * delta a
      refine ⟨f, ?_⟩
      ext k
      have hdelta_self : (delta k).eval k = 1 := by
        simp only [delta, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
        refine Finset.prod_eq_one fun b hb => ?_
        have hkb : k ≠ b := (Finset.mem_erase.mp hb).1.symm
        exact inv_mul_cancel₀ (sub_ne_zero.mpr hkb)
      have hdelta_ne : ∀ a : K, a ≠ k → (delta a).eval k = 0 := by
        intro a hak
        simp only [delta, Polynomial.eval_prod]
        refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hak.symm, Finset.mem_univ k⟩) ?_
        simp
      simp only [polyEvalRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, f,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
      rw [Finset.sum_eq_single k]
      · rw [hdelta_self, mul_one]
      · intro a _ hak
        rw [hdelta_ne a hak, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · intro hinj
      let p : K[X] := ∏ a ∈ Finset.univ, (Polynomial.X - Polynomial.C a)
      have hp_eval : polyEvalRingHom K p = polyEvalRingHom K 0 := by
        ext k
        simp only [polyEvalRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, p,
          Polynomial.eval_prod, Polynomial.eval_zero]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
      have hp_monic : p.Monic := Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
      exact hp_monic.ne_zero (hinj hp_eval)
  · classical
    have _ : Infinite K := hinf
    refine ⟨?_, ?_⟩
    · rw [IsRingMonomorphism, injective_iff_map_eq_zero]
      intro f hf
      by_contra hf0
      have hroots : ∀ k : K, k ∈ f.roots := fun k =>
        (Polynomial.mem_roots hf0).mpr (congrFun hf k)
      have _ : Finite K := Finite.of_injective
        (fun k : K => (⟨k, Multiset.mem_toFinset.mpr (hroots k)⟩ : f.roots.toFinset))
        (fun _ _ h => Subtype.mk.inj h)
      exact not_finite K
    · intro hsurj
      obtain ⟨f, hf⟩ := hsurj (fun k : K => if k = 0 then (1 : K) else 0)
      have hf0 : f ≠ 0 := by
        intro h0
        have := congrFun hf 0
        simp [polyEvalRingHom, h0] at this
      have hsub : (Set.univ \ {0} : Set K) ⊆ (f.roots.toFinset : Set K) := by
        intro k hk
        have hk0 : k ≠ 0 := hk.2
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf0]
        have := congrFun hf k
        simpa [polyEvalRingHom, hk0] using this
      have hinf_compl : (Set.univ \ {0} : Set K).Infinite :=
        (Set.infinite_univ (α := K)).sdiff (Set.finite_singleton (0 : K))
      exact hinf_compl (f.roots.toFinset.finite_toSet.subset hsub)

/-- **Exercise 3.9** (§3.3, p. 24): Suppose that `R` is an infinite ring such that `R / I` is
finite for each non-trivial ideal `I`. Then `R` is an integral domain. -/
theorem exercise_3_9 {R : Type*} [CommRing R] [Nontrivial R] [Infinite R]
    (hfin : ∀ I : Ideal R, I ≠ ⊥ → I ≠ ⊤ → Finite (R ⧸ I)) :
    IsDomain R := by
  have hno : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hnot
    rw [not_or] at hnot
    rcases hnot with ⟨ha, hb⟩
    let I : Ideal R := Ideal.span {a}
    have hI_bot : I ≠ ⊥ := by
      intro hbot
      apply ha
      have : a ∈ (⊥ : Ideal R) := hbot ▸ Ideal.subset_span (Set.mem_singleton a)
      simpa using this
    have hI_top : I ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
      rw [Ideal.mem_span_singleton] at h1
      rcases h1 with ⟨c, hc⟩
      apply hb
      calc b = 1 * b := (one_mul b).symm
        _ = (a * c) * b := by rw [hc]
        _ = c * (a * b) := by ring
        _ = 0 := by rw [hab, mul_zero]
    let J : Ideal R := {
      carrier := {x : R | x * a = 0}
      add_mem' := fun {x y} hx hy => by dsimp at hx hy ⊢; rw [add_mul, hx, hy, add_zero]
      zero_mem' := zero_mul a
      smul_mem' := fun r x hx => by
        dsimp at hx ⊢
        calc (r • x) * a = r * (x * a) := by simp [smul_eq_mul, mul_assoc]
          _ = 0 := by rw [hx, mul_zero]
    }
    have hJ_bot : J ≠ ⊥ := by
      intro hbot
      apply hb
      have hbJ : b ∈ J := by change b * a = 0; rw [mul_comm, hab]
      have : b ∈ (⊥ : Ideal R) := hbot ▸ hbJ
      simpa using this
    have hJ_top : J ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ J := htop ▸ Submodule.mem_top
      change 1 * a = 0 at h1
      exact ha (by simpa using h1)
    have _ : Finite (R ⧸ I) := hfin I hI_bot hI_top
    have _ : Finite (R ⧸ J) := hfin J hJ_bot hJ_top
    let μ : R ⧸ J → I := Quotient.lift
      (fun r : R => (⟨r * a, Ideal.mem_span_singleton.mpr ⟨r, mul_comm r a⟩⟩ : I))
      (fun r₁ r₂ h => by
        apply Subtype.ext
        have hmem : -r₁ + r₂ ∈ J := QuotientAddGroup.leftRel_apply.mp h
        change (-r₁ + r₂) * a = 0 at hmem
        linear_combination -hmem)
    have hμ_surj : Function.Surjective μ := by
      rintro ⟨y, hy⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
      refine ⟨Ideal.Quotient.mk J r, ?_⟩
      apply Subtype.ext
      exact mul_comm r a
    have _ : Finite I := Finite.of_surjective μ hμ_surj
    let splitMap : R → (R ⧸ I) × I := fun r =>
      let q := Ideal.Quotient.mk I r
      let rep := Quotient.out q
      have hdiff : r - rep ∈ I := Ideal.Quotient.eq.mp (by simp [q, rep])
      (q, ⟨r - rep, hdiff⟩)
    have hsplit_inj : Function.Injective splitMap := by
      intro r₁ r₂ h
      have hq : Ideal.Quotient.mk I r₁ = Ideal.Quotient.mk I r₂ := congrArg Prod.fst h
      have hsub : r₁ - Quotient.out (Ideal.Quotient.mk I r₁) =
          r₂ - Quotient.out (Ideal.Quotient.mk I r₂) :=
        congrArg (fun p => p.2.1) h
      rw [hq] at hsub
      exact sub_left_inj.mp hsub
    have _ : Finite R := Finite.of_injective splitMap hsplit_inj
    exact not_finite R
  exact @NoZeroDivisors.to_isDomain R _ _ hno

/-! ## §3.4 Irreducibles, primes and unique factorization domains (printed pp. 24–27, PDF pp. 32–35) -/

/-- Garling's definition of a *unit* in a ring `R` (§3.4, p. 24): an element `a` for which there
exists `b ∈ R` with `ab = 1`. -/
def IsGarlingUnit {R : Type*} [CommRing R] (a : R) : Prop :=
  ∃ b : R, a * b = 1

theorem isGarlingUnit_iff {R : Type*} [CommRing R] (a : R) :
    IsGarlingUnit a ↔ IsUnit a := by
  constructor
  · rintro ⟨b, hab⟩
    exact .of_mul_eq_one b hab
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u.mul_inv⟩

/-- Garling's definition of an *irreducible* element of an integral domain `R` (§3.4, p. 24):
a non-zero non-unit `a` such that whenever `a = b * c`, either `b` or `c` is a unit. -/
structure IsGarlingIrreducible {R : Type*} [CommRing R] (a : R) : Prop where
  ne_zero : a ≠ 0
  not_unit : ¬ IsGarlingUnit a
  isUnit_or_isUnit : ∀ b c : R, a = b * c → IsGarlingUnit b ∨ IsGarlingUnit c

theorem isGarlingIrreducible_iff {R : Type*} [CommRing R] [IsDomain R] (a : R) :
    IsGarlingIrreducible a ↔ Irreducible a := by
  constructor
  · rintro ⟨ha0, hnu, hfac⟩
    refine ⟨fun hu => hnu ((isGarlingUnit_iff a).mpr hu), fun b c hab => ?_⟩
    rcases hfac b c hab with hb | hc
    · exact Or.inl ((isGarlingUnit_iff b).mp hb)
    · exact Or.inr ((isGarlingUnit_iff c).mp hc)
  · intro hirr
    refine ⟨hirr.ne_zero, fun hu => hirr.not_isUnit ((isGarlingUnit_iff a).mp hu),
      fun b c hab => ?_⟩
    rcases hirr.isUnit_or_isUnit hab with hb | hc
    · exact Or.inl ((isGarlingUnit_iff b).mpr hb)
    · exact Or.inr ((isGarlingUnit_iff c).mpr hc)

/-- `PP R` denotes Garling's collection of *proper principal ideals* of `R` (§3.4, p. 24). -/
def PP (R : Type*) [CommRing R] : Set (Ideal R) :=
  {I : Ideal R | I.IsPrincipal ∧ I ≠ ⊤}

theorem mem_PP_iff {R : Type*} [CommRing R] (I : Ideal R) :
    I ∈ PP R ↔ (∃ a : R, I = Ideal.span {a}) ∧ I ≠ ⊤ :=
  and_congr_left' (Submodule.isPrincipal_iff I)

/-- **Theorem 3.2** (§3.4, pp. 24–25): A non-zero element `a` of an integral domain `R` is
irreducible if and only if `(a)` is a maximal element of `PP` (with respect to inclusion). -/
theorem theorem_3_2 {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha0 : a ≠ 0) :
    Irreducible a ↔
      (Ideal.span {a} ∈ PP R ∧
        ∀ J ∈ PP R, Ideal.span {a} ≤ J → J = Ideal.span {a}) := by
  constructor
  · intro hirr
    refine ⟨⟨⟨⟨a, rfl⟩⟩, ?_⟩, ?_⟩
    · rw [ne_eq, Ideal.span_singleton_eq_top]
      exact hirr.not_isUnit
    · rintro J ⟨⟨b, rfl⟩, hJne⟩ hle
      have hbu : ¬ IsUnit b := by
        rwa [ne_eq, Ideal.span_singleton_eq_top] at hJne
      rw [Ideal.span_singleton_le_span_singleton] at hle
      rcases hle with ⟨c, hac⟩
      have hcu : IsUnit c := (hirr.isUnit_or_isUnit hac).resolve_left hbu
      exact Ideal.span_singleton_eq_span_singleton.mpr ⟨hcu.unit, hac.symm⟩
  · rintro ⟨⟨_, ha_ne⟩, hmax⟩
    have hau : ¬ IsUnit a := by
      rwa [ne_eq, Ideal.span_singleton_eq_top] at ha_ne
    refine ⟨hau, fun b c hac => ?_⟩
    by_cases hbu : IsUnit b
    · exact Or.inl hbu
    · right
      have hJne : Ideal.span ({b} : Set R) ≠ ⊤ := by
        rwa [ne_eq, Ideal.span_singleton_eq_top]
      have hle : Ideal.span ({a} : Set R) ≤ Ideal.span {b} :=
        Ideal.span_singleton_le_span_singleton.mpr ⟨c, hac⟩
      have heq : Ideal.span ({b} : Set R) = Ideal.span {a} :=
        hmax (Ideal.span {b}) ⟨⟨⟨b, rfl⟩⟩, hJne⟩ hle
      obtain ⟨d, hbd⟩ := Ideal.span_singleton_le_span_singleton.mp heq.le
      have key : a * (d * c) = a * 1 := by
        calc a * (d * c) = (a * d) * c := by ring
          _ = b * c := by rw [← hbd]
          _ = a * 1 := by rw [← hac, mul_one]
      have hdc : d * c = 1 := mul_left_cancel₀ ha0 key
      exact .of_mul_eq_one d (by rw [mul_comm, hdc])

/-- Garling's *ascending chain condition for principal ideals* (**ACCPI**, §3.4, p. 25):
whenever `I₁ ⊆ I₂ ⊆ I₃ ⊆ ⋯` is an increasing sequence of principal ideals in `R`, there
exists `n₀` such that `I_n = I_{n₀}` for all `n ≥ n₀`. -/
def SatisfiesACCPI (R : Type*) [CommRing R] : Prop :=
  ∀ J : ℕ → Ideal R, (∀ n, (J n).IsPrincipal) → (∀ n, J n ≤ J (n + 1)) →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → J n = J n₀

/-- Equivalence between `SatisfiesACCPI R` and `WellFoundedGT {I : Ideal R // I.IsPrincipal}`
(§3.4, p. 25). -/
theorem satisfiesACCPI_iff_wellFoundedGT (R : Type*) [CommRing R] :
    SatisfiesACCPI R ↔ WellFoundedGT {I : Ideal R // I.IsPrincipal} := by
  rw [wellFoundedGT_iff_monotone_chain_condition]
  constructor
  · intro hacc f
    obtain ⟨n₀, hn₀⟩ := hacc (fun n => (f n).1) (fun n => (f n).2)
      (fun n => f.mono (Nat.le_succ n))
    exact ⟨n₀, fun m hm => Subtype.ext (hn₀ m hm).symm⟩
  · intro hwf J hJp hmono
    have hmon : Monotone (fun n : ℕ => (⟨J n, hJp n⟩ : {I : Ideal R // I.IsPrincipal})) :=
      monotone_nat_of_le_succ fun n => hmono n
    obtain ⟨n₀, hn₀⟩ := hwf ⟨fun n => ⟨J n, hJp n⟩, hmon⟩
    exact ⟨n₀, fun n hn => (congrArg Subtype.val (hn₀ n hn)).symm⟩

/-- For an integral domain `R`, `SatisfiesACCPI R` is equivalent to Mathlib's `WfDvdMonoid R`
(§3.4, p. 25). -/
theorem satisfiesACCPI_iff_wfDvdMonoid (R : Type*) [CommRing R] [IsDomain R] :
    SatisfiesACCPI R ↔ WfDvdMonoid R := by
  rw [satisfiesACCPI_iff_wellFoundedGT]
  constructor
  · intro hwf
    exact WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt hwf
  · intro _
    exact Ideal.setOfPred_isPrincipal_wellFoundedOn_gt

/-- **Theorem 3.3** (§3.4, p. 25): If `R` satisfies the ACCPI, every element of `PP` is contained
in a maximal element of `PP`. -/
theorem theorem_3_3 {R : Type*} [CommRing R] (hacc : SatisfiesACCPI R)
    {J : Ideal R} (hJ : J ∈ PP R) :
    ∃ M ∈ PP R, J ≤ M ∧ ∀ K ∈ PP R, M ≤ K → K = M := by
  have hwf : WellFoundedGT {I : Ideal R // I.IsPrincipal} :=
    (satisfiesACCPI_iff_wellFoundedGT R).mp hacc
  let S : Set {I : Ideal R // I.IsPrincipal} := {I | I.1 ≠ ⊤ ∧ J ≤ I.1}
  have hne : S.Nonempty := ⟨⟨J, hJ.1⟩, hJ.2, le_rfl⟩
  obtain ⟨⟨M, hMp⟩, ⟨hMne, hJM⟩, hmin⟩ := hwf.has_min S hne
  refine ⟨M, ⟨hMp, hMne⟩, hJM, fun K ⟨hKp, hKne⟩ hMK => ?_⟩
  by_contra hKM
  exact hmin ⟨K, hKp⟩ ⟨hKne, le_trans hJM hMK⟩
    (show M < K from lt_of_le_of_ne hMK (Ne.symm hKM))

/-- **Theorem 3.4** (§3.4, p. 25): Suppose that `R` is an integral domain which satisfies ACCPI,
and that `a` is a non-zero non-unit in `R`. Then `a` is a product of irreducibles. -/
theorem theorem_3_4 {R : Type*} [CommRing R] [IsDomain R] (hacc : SatisfiesACCPI R)
    {a : R} (ha0 : a ≠ 0) (hau : ¬ IsUnit a) :
    ∃ (m : ℕ) (_ : 0 < m) (p : Fin m → R),
      (∀ i, Irreducible (p i)) ∧ ∏ i, p i = a := by
  have _ : WfDvdMonoid R := (satisfiesACCPI_iff_wfDvdMonoid R).mp hacc
  obtain ⟨f, hf_irr, hf_prod, hf_ne⟩ :=
    (WfDvdMonoid.not_isUnit_iff_exists_factors_eq a ha0).mp hau
  let L : List R := Quotient.out f
  have hL_eq : (L : Multiset R) = f := Quotient.out_eq f
  have hL_ne : L ≠ [] := by
    intro hnil
    apply hf_ne
    rw [← hL_eq, hnil]
    rfl
  refine ⟨L.length, List.length_pos_of_ne_nil hL_ne, L.get, ?_, ?_⟩
  · intro i
    apply hf_irr
    rw [← hL_eq]
    exact List.get_mem L i
  · rw [← Fin.prod_ofFn L.get, List.ofFn_get, ← Multiset.prod_coe, hL_eq, hf_prod]

/-- Garling's definition of *associates* in an integral domain `R` (§3.4, p. 25): elements `a` and
`b` such that `a = u * b` for some unit `u ∈ R`. -/
def IsGarlingAssociates {R : Type*} [CommRing R] (a b : R) : Prop :=
  ∃ u : R, IsUnit u ∧ a = u * b

theorem isGarlingAssociates_iff {R : Type*} [CommRing R] (a b : R) :
    IsGarlingAssociates a b ↔ Associated a b := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Associated.symm ⟨hu.unit, mul_comm b u⟩
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u⁻¹.isUnit, by simp [mul_comm]⟩

/-- Garling's literal two-clause definition of a *unique factorization domain* (**UFD**, §3.4,
pp. 25–26): an integral domain `R` such that
(a) every non-zero non-unit `a ∈ R` is a product `p₁ ⋯ p_m` (`m ≥ 1`) of irreducibles, and
(b) if `p₁ ⋯ p_m = q₁ ⋯ q_n` expresses an element in two ways as a non-empty product of
irreducibles, then `m = n` and there is a bijection `e : Fin m ≃ Fin n` such that `p_i` and
`q_{e(i)}` are associates for all `i`. -/
structure IsGarlingUFD (R : Type*) [CommRing R] : Prop where
  isDomain : IsDomain R
  exists_factorization : ∀ a : R, a ≠ 0 → ¬ IsUnit a →
    ∃ (m : ℕ) (_ : 0 < m) (p : Fin m → R), (∀ i, Irreducible (p i)) ∧ ∏ i, p i = a
  unique_factorization : ∀ (m n : ℕ) (_ : 0 < m) (_ : 0 < n) (p : Fin m → R) (q : Fin n → R),
    (∀ i, Irreducible (p i)) → (∀ j, Irreducible (q j)) → ∏ i, p i = ∏ j, q j →
      m = n ∧ ∃ e : Fin m ≃ Fin n, ∀ i : Fin m, Associated (p i) (q (e i))

/-- Helper: in any `IsGarlingUFD`, if `u₁ * ∏ i, p i = u₂ * ∏ j, q j` where `u₁, u₂` are units
and `p, q` are (possibly empty) tuples of irreducibles, then `m = n` and there is a bijection
`e : Fin m ≃ Fin n` pairing associated factors (§3.4, p. 26). -/
theorem IsGarlingUFD.unique_factorization_with_units {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    {m n : ℕ} {u₁ u₂ : R} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂)
    {p : Fin m → R} {q : Fin n → R}
    (hp : ∀ i, Irreducible (p i)) (hq : ∀ j, Irreducible (q j))
    (heq : u₁ * ∏ i, p i = u₂ * ∏ j, q j) :
    m = n ∧ ∃ e : Fin m ≃ Fin n, ∀ i : Fin m, Associated (p i) (q (e i)) := by
  have _ : IsDomain R := hUFD.isDomain
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at heq
    by_cases hn : n = 0
    · subst hn
      exact ⟨rfl, Equiv.refl (Fin 0), fun i => Fin.elim0 i⟩
    · exfalso
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h0_mem : (⟨0, hn_pos⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
      have hdvd : q ⟨0, hn_pos⟩ ∣ u₁ := by
        rw [heq]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem q h0_mem) u₂
      exact (hq ⟨0, hn_pos⟩).not_isUnit (isUnit_of_dvd_unit hdvd hu₁)
  · by_cases hn : n = 0
    · subst hn
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at heq
      exfalso
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have h0_mem : (⟨0, hm_pos⟩ : Fin m) ∈ Finset.univ := Finset.mem_univ _
      have hdvd : p ⟨0, hm_pos⟩ ∣ u₂ := by
        rw [← heq]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p h0_mem) u₁
      exact (hp ⟨0, hm_pos⟩).not_isUnit (isUnit_of_dvd_unit hdvd hu₂)
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      classical
      let p' : Fin m → R := fun i => if i = ⟨0, hm_pos⟩ then u₁ * p i else p i
      let q' : Fin n → R := fun j => if j = ⟨0, hn_pos⟩ then u₂ * q j else q j
      have hp'_irr : ∀ i, Irreducible (p' i) := by
        intro i
        dsimp only [p']
        split_ifs with hi
        · have hass : Associated (p i) (u₁ * p i) := ⟨hu₁.unit, mul_comm (p i) u₁⟩
          exact hass.irreducible (hp i)
        · exact hp i
      have hq'_irr : ∀ j, Irreducible (q' j) := by
        intro j
        dsimp only [q']
        split_ifs with hj
        · have hass : Associated (q j) (u₂ * q j) := ⟨hu₂.unit, mul_comm (q j) u₂⟩
          exact hass.irreducible (hq j)
        · exact hq j
      have hp'_prod : ∏ i, p' i = u₁ * ∏ i, p i := by
        have hmem : (⟨0, hm_pos⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase Finset.univ p' hmem,
          ← Finset.mul_prod_erase Finset.univ p hmem]
        have h0 : p' ⟨0, hm_pos⟩ = u₁ * p ⟨0, hm_pos⟩ := by simp [p']
        have herase : ∏ i ∈ Finset.univ.erase ⟨0, hm_pos⟩, p' i =
            ∏ i ∈ Finset.univ.erase ⟨0, hm_pos⟩, p i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ ⟨0, hm_pos⟩ := (Finset.mem_erase.mp hi).1
          simp [p', hne]
        rw [h0, herase, mul_assoc]
      have hq'_prod : ∏ j, q' j = u₂ * ∏ j, q j := by
        have hmem : (⟨0, hn_pos⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase Finset.univ q' hmem,
          ← Finset.mul_prod_erase Finset.univ q hmem]
        have h0 : q' ⟨0, hn_pos⟩ = u₂ * q ⟨0, hn_pos⟩ := by simp [q']
        have herase : ∏ j ∈ Finset.univ.erase ⟨0, hn_pos⟩, q' j =
            ∏ j ∈ Finset.univ.erase ⟨0, hn_pos⟩, q j := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hne : j ≠ ⟨0, hn_pos⟩ := (Finset.mem_erase.mp hj).1
          simp [q', hne]
        rw [h0, herase, mul_assoc]
      obtain ⟨hmn, e, he⟩ := hUFD.unique_factorization m n hm_pos hn_pos p' q'
        hp'_irr hq'_irr (by rw [hp'_prod, hq'_prod, heq])
      refine ⟨hmn, e, fun i => ?_⟩
      have hp_ass : Associated (p i) (p' i) := by
        dsimp only [p']
        split_ifs
        · exact ⟨hu₁.unit, mul_comm (p i) u₁⟩
        · exact Associated.refl _
      have hq_ass : Associated (q' (e i)) (q (e i)) := by
        dsimp only [q']
        split_ifs
        · have hass : Associated (q (e i)) (u₂ * q (e i)) :=
            ⟨hu₂.unit, mul_comm (q (e i)) u₂⟩
          exact hass.symm
        · exact Associated.refl _
      exact hp_ass.trans ((he i).trans hq_ass)

/-- Garling's UFD length `ufdLength hUFD a` of a non-zero element `a` in a UFD `R` (§3.4, p. 26):
`0` if `a` is a unit, and `m` if `a = p₁ ⋯ p_m` is a product of irreducibles. -/
noncomputable def ufdLength {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    (a : R) (ha0 : a ≠ 0) : ℕ := by
  classical
  exact if hau : IsUnit a then 0 else Classical.choose (hUFD.exists_factorization a ha0 hau)

theorem ufdLength_spec {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    {a : R} (ha0 : a ≠ 0) {m : ℕ} {u : R} (hu : IsUnit u) {p : Fin m → R}
    (hp : ∀ i, Irreducible (p i)) (ha : a = u * ∏ i, p i) :
    ufdLength hUFD a ha0 = m := by
  classical
  unfold ufdLength
  split_ifs with hau
  · obtain ⟨u', rfl⟩ := hau
    have h1 : (u' : R) * ∏ _ : Fin 0, (1 : R) = u * ∏ i, p i := by
      simpa using ha
    exact (hUFD.unique_factorization_with_units u'.isUnit hu
      (fun i => Fin.elim0 i) hp h1).1
  · let k := Classical.choose (hUFD.exists_factorization a ha0 hau)
    obtain ⟨hk, q, hq_irr, hq_prod⟩ :=
      Classical.choose_spec (hUFD.exists_factorization a ha0 hau)
    have h1 : (1 : R) * ∏ j : Fin k, q j = u * ∏ i, p i := by
      rw [one_mul, hq_prod, ha]
    exact (hUFD.unique_factorization_with_units isUnit_one hu hq_irr hp h1).1

theorem ufdLength_exists_rep {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    (a : R) (ha0 : a ≠ 0) :
    ∃ (u : R) (p : Fin (ufdLength hUFD a ha0) → R),
      IsUnit u ∧ (∀ i, Irreducible (p i)) ∧ a = u * ∏ i, p i := by
  classical
  by_cases hau : IsUnit a
  · have hlen : ufdLength hUFD a ha0 = 0 := by simp [ufdLength, hau]
    have hempty : ∀ (k : ℕ) (_ : k = 0) (f : Fin k → R), ∏ i, f i = 1 := by
      rintro _ rfl f
      simp
    refine ⟨a, fun i => Fin.elim0 (hlen ▸ i), hau, fun i => Fin.elim0 (hlen ▸ i), ?_⟩
    rw [hempty _ hlen _, mul_one]
  · have hlen : ufdLength hUFD a ha0 =
        Classical.choose (hUFD.exists_factorization a ha0 hau) := by
      simp [ufdLength, hau]
    obtain ⟨_, q, hq_irr, hq_prod⟩ :=
      Classical.choose_spec (hUFD.exists_factorization a ha0 hau)
    refine ⟨1, fun i => q (Fin.cast hlen i), isUnit_one,
      fun i => hq_irr (Fin.cast hlen i), ?_⟩
    rw [one_mul]
    exact hq_prod.symm.trans
      (Finset.prod_equiv (Fin.castOrderIso hlen.symm).toEquiv (by simp) (by simp))

/-- Additivity of Garling's UFD length (`l(ab) = l(a) + l(b)`, §3.4, p. 26). -/
theorem ufdLength_mul {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    {a b : R} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    have _ : IsDomain R := hUFD.isDomain
    ufdLength hUFD (a * b) (mul_ne_zero ha0 hb0) =
      ufdLength hUFD a ha0 + ufdLength hUFD b hb0 := by
  have _ : IsDomain R := hUFD.isDomain
  obtain ⟨ua, pa, hua, hpa, ha_eq⟩ := ufdLength_exists_rep hUFD a ha0
  obtain ⟨ub, pb, hub, hpb, hb_eq⟩ := ufdLength_exists_rep hUFD b hb0
  refine ufdLength_spec hUFD (mul_ne_zero ha0 hb0) (hua.mul hub)
    (p := Fin.append pa pb) ?_ ?_
  · intro i
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · simpa using hpa i₁
    · simpa using hpb i₂
  · rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    calc a * b = (ua * ∏ x, pa x) * (ub * ∏ x, pb x) := congrArg₂ (· * ·) ha_eq hb_eq
      _ = ua * ub * ((∏ x, pa x) * ∏ x, pb x) := by ring

theorem ufdLength_eq_zero_iff {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R)
    {a : R} (ha0 : a ≠ 0) :
    ufdLength hUFD a ha0 = 0 ↔ IsUnit a := by
  classical
  unfold ufdLength
  split_ifs with hau
  · exact ⟨fun _ => hau, fun _ => rfl⟩
  · obtain ⟨hm, _, _, _⟩ := Classical.choose_spec (hUFD.exists_factorization a ha0 hau)
    exact ⟨fun h0 => absurd h0 hm.ne', fun hu => absurd hu hau⟩

/-- First half of Garling's proof of Theorem 3.6 (§3.4, p. 26): if `R` is a unique factorization
domain, then `R` satisfies the ACCPI (via decreasing `ufdLength`). -/
theorem ufd_satisfiesACCPI {R : Type*} [CommRing R] (hUFD : IsGarlingUFD R) :
    SatisfiesACCPI R := by
  have _ : IsDomain R := hUFD.isDomain
  intro J hJp hmono
  by_cases hall0 : ∀ n : ℕ, J n = ⊥
  · exact ⟨0, fun n _ => by rw [hall0 n, hall0 0]⟩
  · push Not at hall0
    obtain ⟨n₁, hn₁⟩ := hall0
    have ha_ex : ∀ n, ∃ a : R, J n = Ideal.span {a} := fun n => (hJp n).principal
    let a : ℕ → R := fun n => Classical.choose (ha_ex n)
    have ha_span : ∀ n, J n = Ideal.span {a n} := fun n => Classical.choose_spec (ha_ex n)
    have ha_ne0 : ∀ n, n₁ ≤ n → a n ≠ 0 := by
      intro n hn
      have hle : J n₁ ≤ J n := by
        induction hn with
        | refl => exact le_rfl
        | step _ ih => exact le_trans ih (hmono _)
      intro h0
      apply hn₁
      rw [← le_bot_iff]
      rw [ha_span n, h0, Ideal.span_singleton_eq_bot.mpr rfl] at hle
      exact hle
    let f : ℕ → ℕ := fun k => ufdLength hUFD (a (n₁ + k)) (ha_ne0 (n₁ + k) (Nat.le_add_right _ _))
    have hf_anti : ∀ k : ℕ, f (k + 1) ≤ f k := by
      intro k
      have hle_J : Ideal.span {a (n₁ + k)} ≤ Ideal.span {a (n₁ + (k + 1))} := by
        rw [← ha_span (n₁ + k), ← ha_span (n₁ + (k + 1))]
        exact hmono (n₁ + k)
      obtain ⟨c, hc⟩ := Ideal.span_singleton_le_span_singleton.mp hle_J
      have hc0 : c ≠ 0 := by
        intro h0
        apply ha_ne0 (n₁ + k) (Nat.le_add_right _ _)
        rw [hc, h0, mul_zero]
      have hlen_eq : ufdLength hUFD (a (n₁ + k)) (ha_ne0 (n₁ + k) (Nat.le_add_right _ _)) =
          ufdLength hUFD (a (n₁ + (k + 1))) (ha_ne0 (n₁ + (k + 1)) (Nat.le_add_right _ _)) +
          ufdLength hUFD c hc0 := by
        have h1 := ufdLength_mul hUFD (ha_ne0 (n₁ + (k + 1)) (Nat.le_add_right _ _)) hc0
        have hcongr : ufdLength hUFD (a (n₁ + k)) (ha_ne0 (n₁ + k) (Nat.le_add_right _ _)) =
            ufdLength hUFD (a (n₁ + (k + 1)) * c)
              (mul_ne_zero (ha_ne0 (n₁ + (k + 1)) (Nat.le_add_right _ _)) hc0) := by
          congr 1
        omega
      dsimp only [f]
      omega
    have hmin_ex : ∃ k₀ : ℕ, ∀ k : ℕ, f k₀ ≤ f k := by
      classical
      have hne_set : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
      let m := Nat.find (hne_set)
      have hm : m ∈ Set.range f := Nat.find_spec hne_set
      obtain ⟨k₀, hk₀⟩ := hm
      refine ⟨k₀, fun k => ?_⟩
      rw [hk₀]
      exact Nat.find_min' hne_set ⟨k, rfl⟩
    obtain ⟨k₀, hk₀⟩ := hmin_ex
    have hf_const : ∀ k, k₀ ≤ k → f k = f k₀ := by
      intro k hk
      have hle : f k ≤ f k₀ := by
        induction hk with
        | refl => exact le_rfl
        | step _ ih => exact le_trans (hf_anti _) ih
      exact le_antisymm hle (hk₀ k)
    refine ⟨n₁ + k₀, fun n hn => ?_⟩
    have hstep_eq : ∀ k, k₀ ≤ k → J (n₁ + (k + 1)) = J (n₁ + k) := by
      intro k hk
      have hle_J : Ideal.span {a (n₁ + k)} ≤ Ideal.span {a (n₁ + (k + 1))} := by
        rw [← ha_span (n₁ + k), ← ha_span (n₁ + (k + 1))]
        exact hmono (n₁ + k)
      obtain ⟨c, hc⟩ := Ideal.span_singleton_le_span_singleton.mp hle_J
      have hc0 : c ≠ 0 := by
        intro h0
        apply ha_ne0 (n₁ + k) (Nat.le_add_right _ _)
        rw [hc, h0, mul_zero]
      have hlen_sum : f k = f (k + 1) + ufdLength hUFD c hc0 := by
        dsimp only [f]
        have h1 := ufdLength_mul hUFD (ha_ne0 (n₁ + (k + 1)) (Nat.le_add_right _ _)) hc0
        have hcongr : ufdLength hUFD (a (n₁ + k)) (ha_ne0 (n₁ + k) (Nat.le_add_right _ _)) =
            ufdLength hUFD (a (n₁ + (k + 1)) * c)
              (mul_ne_zero (ha_ne0 (n₁ + (k + 1)) (Nat.le_add_right _ _)) hc0) := by
          congr 1
        omega
      have hc_len0 : ufdLength hUFD c hc0 = 0 := by
        have hfk := hf_const k hk
        have hfk1 := hf_const (k + 1) (by omega)
        omega
      have hcu : IsUnit c := (ufdLength_eq_zero_iff hUFD hc0).mp hc_len0
      rw [ha_span (n₁ + (k + 1)), ha_span (n₁ + k)]
      exact Ideal.span_singleton_eq_span_singleton.mpr ⟨hcu.unit, hc.symm⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction d with
    | zero => rfl
    | succ d ih =>
      have heq : n₁ + k₀ + (d + 1) = n₁ + (k₀ + d + 1) := by omega
      have heq' : n₁ + k₀ + d = n₁ + (k₀ + d) := by omega
      rw [heq, hstep_eq (k₀ + d) (by omega), ← heq', ih (by omega)]

/-- Garling's definition of a *prime* element of an integral domain `R` (§3.4, p. 26):
a non-zero non-unit `a ∈ R` such that whenever `a ∣ bc`, either `a ∣ b` or `a ∣ c`. -/
structure IsGarlingPrime {R : Type*} [CommRing R] (a : R) : Prop where
  ne_zero : a ≠ 0
  not_unit : ¬ IsGarlingUnit a
  dvd_or_dvd : ∀ b c : R, a ∣ b * c → a ∣ b ∨ a ∣ c

theorem isGarlingPrime_iff {R : Type*} [CommRing R] (a : R) :
    IsGarlingPrime a ↔ Prime a := by
  constructor
  · rintro ⟨ha0, hnu, hdvd⟩
    exact ⟨ha0, fun hu => hnu ((isGarlingUnit_iff a).mpr hu), hdvd⟩
  · rintro ⟨ha0, hnu, hdvd⟩
    exact ⟨ha0, fun hu => hnu ((isGarlingUnit_iff a).mp hu), hdvd⟩

/-- **Theorem 3.5** (§3.4, p. 26): A prime element of an integral domain `R` is irreducible. -/
theorem theorem_3_5 {R : Type*} [CommRing R] [IsDomain R] {a : R} :
    (IsGarlingPrime a → IsGarlingIrreducible a) ∧ (Prime a → Irreducible a) :=
  ⟨fun ha => (isGarlingIrreducible_iff a).mpr (((isGarlingPrime_iff a).mp ha).irreducible),
    fun ha => ha.irreducible⟩

/-- Helper: convert `Multiset.Rel Associated (s.val.map p) (t.val.map q)` on finite sets `s, t`
into an explicit index bijection `e : {x // x ∈ s} ≃ {y // y ∈ t}` pairing associated values. -/
theorem finset_rel_associated_equiv {α β R : Type*} [CommRing R]
    [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → R) (q : β → R)
    (hrel : Multiset.Rel Associated (s.val.map p) (t.val.map q)) :
    ∃ e : {x : α // x ∈ s} ≃ {y : β // y ∈ t},
      ∀ x : {x : α // x ∈ s}, Associated (p x.1) (q (e x).1) := by
  induction s using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.empty_val, Multiset.map_zero, Multiset.rel_zero_left] at hrel
    have ht : t = ∅ := Finset.val_eq_zero.mp (Multiset.map_eq_zero.mp hrel)
    subst ht
    exact ⟨{
      toFun := fun x => nomatch x.2
      invFun := fun y => nomatch y.2
      left_inv := fun x => nomatch x.2
      right_inv := fun y => nomatch y.2
    }, fun x => nomatch x.2⟩
  | insert a s ha ih =>
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons, Multiset.rel_cons_left] at hrel
    obtain ⟨y, ms, hay, hrel', ht_eq⟩ := hrel
    have hy_mem : y ∈ t.val.map q := by
      rw [ht_eq]
      exact Multiset.mem_cons_self y ms
    obtain ⟨b, hbt, hqb⟩ := Multiset.mem_map.mp hy_mem
    have ht_decomp : t.val.map q = y ::ₘ (t.erase b).val.map q := by
      rw [← hqb, ← Multiset.map_cons, ← Finset.insert_val_of_notMem (Finset.notMem_erase b t),
        Finset.insert_erase hbt]
    have hms : ms = (t.erase b).val.map q :=
      (Multiset.cons_inj_right y).mp (ht_eq.symm.trans ht_decomp)
    rw [hms] at hrel'
    obtain ⟨e', he'⟩ := ih (t.erase b) hrel'
    let toFun : {x : α // x ∈ insert a s} → {z : β // z ∈ t} := fun x =>
      if hxa : x.1 = a then ⟨b, hbt⟩
      else
        let xs : {x : α // x ∈ s} := ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hxa⟩
        ⟨(e' xs).1, Finset.mem_of_mem_erase (e' xs).2⟩
    let invFun : {z : β // z ∈ t} → {x : α // x ∈ insert a s} := fun z =>
      if hzb : z.1 = b then ⟨a, Finset.mem_insert_self a s⟩
      else
        let ze : {z : β // z ∈ t.erase b} := ⟨z.1, Finset.mem_erase.mpr ⟨hzb, z.2⟩⟩
        ⟨(e'.symm ze).1, Finset.mem_insert_of_mem (e'.symm ze).2⟩
    refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := fun x => by
        apply Subtype.ext
        by_cases hxa : x.1 = a
        · simp [toFun, invFun, hxa]
        · have hneb : (e' ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hxa⟩).1 ≠ b :=
            (Finset.mem_erase.mp (e' ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hxa⟩).2).1
          simp [toFun, invFun, hxa, hneb]
      right_inv := fun z => by
        apply Subtype.ext
        by_cases hzb : z.1 = b
        · simp [toFun, invFun, hzb]
        · have hnea : (e'.symm ⟨z.1, Finset.mem_erase.mpr ⟨hzb, z.2⟩⟩).1 ≠ a :=
            fun h => ha (h ▸ (e'.symm ⟨z.1, Finset.mem_erase.mpr ⟨hzb, z.2⟩⟩).2)
          simp [toFun, invFun, hzb, hnea]
    }, fun x => ?_⟩
    by_cases hxa : x.1 = a
    · have hto : (toFun x).1 = b := by simp [toFun, hxa]
      change Associated (p x.1) (q (toFun x).1)
      rw [hxa, hto, hqb]
      exact hay
    · have hto : (toFun x).1 = (e' ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hxa⟩).1 := by
        simp [toFun, hxa]
      change Associated (p x.1) (q (toFun x).1)
      rw [hto]
      exact he' ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hxa⟩

/-- Equivalence between `IsGarlingUFD R` and Mathlib's `UniqueFactorizationMonoid R` on any
integral domain `R`, and **Theorem 3.6** (§3.4, pp. 26–27): an integral domain `R` is a UFD if and
only if `R` satisfies ACCPI and every irreducible in `R` is prime. -/
theorem theorem_3_6 (R : Type*) [CommRing R] [IsDomain R] :
    IsGarlingUFD R ↔ SatisfiesACCPI R ∧ (∀ a : R, Irreducible a → Prime a) := by
  constructor
  · intro hUFD
    refine ⟨ufd_satisfiesACCPI hUFD, fun q hq => ?_⟩
    refine ⟨hq.ne_zero, hq.not_isUnit, fun b c hbc => ?_⟩
    by_cases hb0 : b = 0
    · subst hb0; exact Or.inl (dvd_zero q)
    by_cases hc0 : c = 0
    · subst hc0; exact Or.inr (dvd_zero q)
    by_cases hbu : IsUnit b
    · right
      rcases hbc with ⟨d, hd⟩
      obtain ⟨ub, rfl⟩ := hbu
      exact ⟨↑ub⁻¹ * d, by linear_combination (↑ub⁻¹ : R) * hd - c * ub.inv_val⟩
    by_cases hcu : IsUnit c
    · left
      rcases hbc with ⟨d, hd⟩
      obtain ⟨uc, rfl⟩ := hcu
      exact ⟨↑uc⁻¹ * d, by linear_combination (↑uc⁻¹ : R) * hd - b * uc.inv_val⟩
    rcases hbc with ⟨d, hd⟩
    have hd0 : d ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hd
      exact mul_ne_zero hb0 hc0 hd
    obtain ⟨mb, hmb, pb, hpb, hpb_prod⟩ := hUFD.exists_factorization b hb0 hbu
    obtain ⟨mc, hmc, pc, hpc, hpc_prod⟩ := hUFD.exists_factorization c hc0 hcu
    obtain ⟨ud, pd, hud, hpd, hd_eq⟩ := ufdLength_exists_rep hUFD d hd0
    let lhs_factors : Fin (mb + mc) → R := Fin.append pb pc
    have hlhs_irr : ∀ i, Irreducible (lhs_factors i) := fun i =>
      Fin.addCases (fun i₁ => by simpa [lhs_factors] using hpb i₁)
        (fun i₂ => by simpa [lhs_factors] using hpc i₂) i
    let rhs_factors : Fin (1 + ufdLength hUFD d hd0) → R :=
      Fin.append (fun _ : Fin 1 => q) pd
    have hrhs_irr : ∀ j, Irreducible (rhs_factors j) := fun j =>
      Fin.addCases (fun _ => by simpa [rhs_factors] using hq)
        (fun j₂ => by simpa [rhs_factors] using hpd j₂) j
    have hprod_eq : (1 : R) * ∏ i, lhs_factors i = ud * ∏ j, rhs_factors j := by
      rw [one_mul]
      have hl : ∏ i, lhs_factors i = b * c := by
        dsimp only [lhs_factors]
        rw [Fin.prod_univ_add]
        simp [hpb_prod, hpc_prod]
      have hr : ud * ∏ j, rhs_factors j = q * d := by
        dsimp only [rhs_factors]
        rw [Fin.prod_univ_add]
        simp only [Fin.append_left, Fin.append_right, Fin.prod_univ_one]
        calc ud * (q * ∏ x, pd x) = q * (ud * ∏ x, pd x) := by ring
          _ = q * d := by rw [← hd_eq]
      rw [hl, hr, hd]
    obtain ⟨_, e, he⟩ :=
      hUFD.unique_factorization_with_units isUnit_one hud hlhs_irr hrhs_irr hprod_eq
    let idx := e.symm ⟨0, by omega⟩
    have hass : Associated (lhs_factors idx) q := by
      have h := he idx
      have he_idx : e idx = ⟨0, by omega⟩ := e.apply_symm_apply _
      rw [he_idx] at h
      have hr0 : rhs_factors ⟨0, by omega⟩ = q := by
        change Fin.append (fun _ : Fin 1 => q) pd (Fin.castAdd _ (0 : Fin 1)) = q
        simp
      rwa [hr0] at h
    have hqdvd : q ∣ lhs_factors idx := hass.symm.dvd
    refine Fin.addCases (m := mb) (n := mc)
      (motive := fun i => q ∣ lhs_factors i → q ∣ b ∨ q ∣ c)
      (fun i₁ hi₁ => ?_) (fun i₂ hi₂ => ?_) idx hqdvd
    · left
      have hval : lhs_factors (Fin.castAdd mc i₁) = pb i₁ := by simp [lhs_factors]
      rw [hval] at hi₁
      rw [← hpb_prod]
      exact dvd_trans hi₁ (Finset.dvd_prod_of_mem pb (Finset.mem_univ i₁))
    · right
      have hval : lhs_factors (Fin.natAdd mb i₂) = pc i₂ := by simp [lhs_factors]
      rw [hval] at hi₂
      rw [← hpc_prod]
      exact dvd_trans hi₂ (Finset.dvd_prod_of_mem pc (Finset.mem_univ i₂))
  · rintro ⟨hacc, hirr_prime⟩
    have hwf : WfDvdMonoid R := (satisfiesACCPI_iff_wfDvdMonoid R).mp hacc
    have _ : UniqueFactorizationMonoid R := {
      toIsCancelMulZero := inferInstance
      toWellFounded := hwf
      irreducible_iff_prime := fun {a} => ⟨hirr_prime a, Prime.irreducible⟩
    }
    refine ⟨inferInstance, fun a ha0 hau => theorem_3_4 hacc ha0 hau,
      fun m n _ _ p q hp hq hprod => ?_⟩
    have hrel : Multiset.Rel Associated
        ((Finset.univ : Finset (Fin m)).val.map p)
        ((Finset.univ : Finset (Fin n)).val.map q) := by
      apply UniqueFactorizationMonoid.factors_unique
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
        exact hp i
      · intro y hy
        obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hy
        exact hq j
      · have hp1 : ((Finset.univ : Finset (Fin m)).val.map p).prod = ∏ i, p i := rfl
        have hq1 : ((Finset.univ : Finset (Fin n)).val.map q).prod = ∏ j, q j := rfl
        rw [hp1, hq1, hprod]
        exact Associated.rfl
    obtain ⟨e_sub, he_sub⟩ := finset_rel_associated_equiv
      (Finset.univ : Finset (Fin m)) (Finset.univ : Finset (Fin n)) p q hrel
    let e : Fin m ≃ Fin n := {
      toFun := fun i => (e_sub ⟨i, Finset.mem_univ i⟩).1
      invFun := fun j => (e_sub.symm ⟨j, Finset.mem_univ j⟩).1
      left_inv := fun i => congrArg Subtype.val (e_sub.symm_apply_apply ⟨i, Finset.mem_univ i⟩)
      right_inv := fun j => congrArg Subtype.val (e_sub.apply_symm_apply ⟨j, Finset.mem_univ j⟩)
    }
    have hmn : m = n := by
      simpa using Fintype.card_congr e
    exact ⟨hmn, e, fun i => he_sub ⟨i, Finset.mem_univ i⟩⟩

theorem isGarlingUFD_iff_uniqueFactorizationMonoid (R : Type*) [CommRing R] [IsDomain R] :
    IsGarlingUFD R ↔ UniqueFactorizationMonoid R := by
  rw [theorem_3_6 R, satisfiesACCPI_iff_wfDvdMonoid R]
  constructor
  · rintro ⟨hwf, hp⟩
    exact {
      toIsCancelMulZero := inferInstance
      toWellFounded := hwf
      irreducible_iff_prime := fun {a} => ⟨hp a, Prime.irreducible⟩
    }
  · intro _
    exact ⟨inferInstance, fun _ ha => UniqueFactorizationMonoid.irreducible_iff_prime.mp ha⟩

/-! ### Exercises 3.10–3.14 (§3.4, printed p. 27, PDF p. 35) -/

/-- **Exercise 3.10** (§3.4, p. 27):
(1) In `R[x]` over an integral domain `R`, the units are precisely the constant polynomials `C u`
with `u` a unit of `R`.
(2) In `ℤ_4[x]` (`(ZMod 4)[X]`), `f` is a unit if and only if `f.coeff 0 ∈ {1, 3}` and
`f.coeff n ∈ {0, 2}` for all `n ≥ 1` (in particular, `1 + 2x` is a non-constant unit). -/
theorem exercise_3_10 :
    (∀ (R : Type) [CommRing R] [IsDomain R] (f : R[X]),
      IsUnit f ↔ ∃ u : R, IsUnit u ∧ f = Polynomial.C u) ∧
    (∀ f : (ZMod 4)[X],
      IsUnit f ↔ (f.coeff 0 = 1 ∨ f.coeff 0 = 3) ∧
        ∀ n : ℕ, 1 ≤ n → f.coeff n = 0 ∨ f.coeff n = 2) ∧
    (IsUnit (1 + Polynomial.C (2 : ZMod 4) * Polynomial.X : (ZMod 4)[X]) ∧
      (1 + Polynomial.C (2 : ZMod 4) * Polynomial.X : (ZMod 4)[X]).natDegree = 1) := by
  refine ⟨fun R _ _ f => ?_, fun f => ?_, ?_⟩
  · rw [Polynomial.isUnit_iff]
    constructor
    · rintro ⟨u, hu, huf⟩
      exact ⟨u, hu, huf.symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  · have zmod4_cases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
    constructor
    · rintro ⟨u, rfl⟩
      have hc0 : (u : (ZMod 4)[X]).coeff 0 * (↑u⁻¹ : (ZMod 4)[X]).coeff 0 = 1 := by
        have h1 : ((u : (ZMod 4)[X]) * ↑u⁻¹).coeff 0 = (1 : (ZMod 4)[X]).coeff 0 :=
          congrArg (fun p => p.coeff 0) u.mul_inv
        rwa [Polynomial.mul_coeff_zero, Polynomial.coeff_one_zero] at h1
      have hu0 : (u : (ZMod 4)[X]).coeff 0 = 1 ∨ (u : (ZMod 4)[X]).coeff 0 = 3 := by
        generalize (u : (ZMod 4)[X]).coeff 0 = a, (↑u⁻¹ : (ZMod 4)[X]).coeff 0 = b at hc0
        rcases zmod4_cases a with rfl | rfl | rfl | rfl <;>
          rcases zmod4_cases b with rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert hc0; decide)
      refine ⟨hu0, fun n hn => ?_⟩
      let π : ZMod 4 →+* ZMod 2 := ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)
      let πP : (ZMod 4)[X] →+* (ZMod 2)[X] := Polynomial.mapRingHom π
      have hunit2 : IsUnit (πP (u : (ZMod 4)[X])) := IsUnit.map πP u.isUnit
      obtain ⟨c, _, hc_eq⟩ := Polynomial.isUnit_iff.mp hunit2
      have hcoeff2 : (πP (u : (ZMod 4)[X])).coeff n = 0 := by
        rw [← hc_eq, Polynomial.coeff_C]
        have hne : n ≠ 0 := by omega
        simp [hne]
      have hπc : π ((u : (ZMod 4)[X]).coeff n) = 0 := by
        simpa [πP, Polynomial.coeff_map] using hcoeff2
      generalize (u : (ZMod 4)[X]).coeff n = a at hπc
      rcases zmod4_cases a with rfl | rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert hπc; decide)
    · rintro ⟨hu0, hrest⟩
      let u0 : ZMod 4 := f.coeff 0
      let g : (ZMod 4)[X] := f - Polynomial.C u0
      have hf_eq : f = Polynomial.C u0 + g := by simp [g]
      have hg_coeff : ∀ k : ℕ, g.coeff k = 0 ∨ g.coeff k = 2 := by
        intro k
        by_cases hk0 : k = 0
        · subst hk0
          left
          simp [g, u0]
        · have hfg : g.coeff k = f.coeff k := by simp [g, Polynomial.coeff_C, hk0]
          rw [hfg]
          exact hrest k (by omega)
      have hgsq : g * g = 0 := by
        ext k
        rw [Polynomial.coeff_zero, Polynomial.coeff_mul]
        refine Finset.sum_eq_zero fun ij _ => ?_
        rcases hg_coeff ij.1 with h1 | h1 <;> rcases hg_coeff ij.2 with h2 | h2 <;>
          rw [h1, h2] <;> decide
      have hu0_sq : u0 * u0 = 1 := by
        rcases hu0 with h | h <;> (change u0 = _ at h; rw [h]; decide)
      refine .of_mul_eq_one (Polynomial.C u0 - g) ?_
      calc f * (Polynomial.C u0 - g)
        _ = (Polynomial.C u0 + g) * (Polynomial.C u0 - g) := by rw [hf_eq]
        _ = Polynomial.C u0 * Polynomial.C u0 - g * g := by ring
        _ = Polynomial.C (u0 * u0) - 0 := by rw [← Polynomial.C_mul, hgsq]
        _ = 1 := by rw [hu0_sq, sub_zero, Polynomial.C_1]
  · refine ⟨?_, ?_⟩
    · refine .of_mul_eq_one (1 + Polynomial.C (2 : ZMod 4) * Polynomial.X) ?_
      have h22 : Polynomial.C (2 : ZMod 4) * Polynomial.C (2 : ZMod 4) = 0 := by
        rw [← Polynomial.C_mul]
        have : (2 : ZMod 4) * 2 = 0 := by decide
        rw [this, Polynomial.C_0]
      have h2add : Polynomial.C (2 : ZMod 4) + Polynomial.C (2 : ZMod 4) = 0 := by
        rw [← Polynomial.C_add]
        have : (2 : ZMod 4) + 2 = 0 := by decide
        rw [this, Polynomial.C_0]
      calc (1 + Polynomial.C (2 : ZMod 4) * Polynomial.X) *
            (1 + Polynomial.C (2 : ZMod 4) * Polynomial.X)
        _ = 1 + (Polynomial.C (2 : ZMod 4) + Polynomial.C (2 : ZMod 4)) * Polynomial.X +
            (Polynomial.C (2 : ZMod 4) * Polynomial.C (2 : ZMod 4)) * Polynomial.X ^ 2 := by ring
        _ = 1 := by rw [h2add, h22]; simp
    · compute_degree!

theorem bot_isPrime_of_isDomain (R : Type*) [CommRing R] [IsDomain R] :
    (⊥ : Ideal R).IsPrime :=
  ⟨bot_ne_top, fun {_ _} hab => by rw [Ideal.mem_bot] at hab ⊢; exact mul_eq_zero.mp hab⟩

/-- **Exercise 3.11 (`a = 0` counterexample)** (§3.4, p. 27): In `ℤ`, `ℤ / (0)` is an integral
domain while `0` is not prime (`0` is excluded by Garling's non-zero requirement on p. 26). -/
theorem exercise_3_11_zero_counterexample :
    IsDomain (ℤ ⧸ Ideal.span {(0 : ℤ)}) ∧ ¬ Prime (0 : ℤ) ∧ ¬ IsGarlingPrime (0 : ℤ) := by
  refine ⟨?_, not_prime_zero, fun h => h.ne_zero rfl⟩
  rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_eq_bot.mpr rfl]
  exact bot_isPrime_of_isDomain ℤ

/-- **Exercise 3.11 (repaired under `a ≠ 0`)** (§3.4, p. 27): A non-zero element `a` of an integral
domain `R` is prime if and only if `R / (a)` is an integral domain. -/
theorem exercise_3_11 {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha : a ≠ 0) :
    Prime a ↔ IsDomain (R ⧸ Ideal.span {a}) := by
  rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime ha]

/-- **Exercise 3.11 (unconditional characterization)** (§3.4, p. 27): For any element `a` of an
integral domain `R`, `R / (a)` is an integral domain if and only if `a = 0` or `a` is prime. -/
theorem exercise_3_11_iff_zero_or_prime {R : Type*} [CommRing R] [IsDomain R] (a : R) :
    IsDomain (R ⧸ Ideal.span {a}) ↔ a = 0 ∨ Prime a := by
  by_cases ha : a = 0
  · subst ha
    simp only [true_or, iff_true, Ideal.Quotient.isDomain_iff_prime]
    rw [Ideal.span_singleton_eq_bot.mpr rfl]
    exact bot_isPrime_of_isDomain R
  · simp [ha, (exercise_3_11 ha).symm]

/-- Constructor `mkI5 m n = m + i√5 n` in `ZAdjoinI5` (`ℤ + i√5 ℤ`, §3.4, Ex. 3.12). -/
noncomputable def mkI5 (m n : ℤ) : ZAdjoinI5 :=
  ⟨(m : ℂ) + Complex.I * ↑(Real.sqrt 5) * (n : ℂ), ⟨m, n, rfl⟩⟩

noncomputable def zAdjoinI5Re (z : ZAdjoinI5) : ℤ :=
  Classical.choose z.2

noncomputable def zAdjoinI5Im (z : ZAdjoinI5) : ℤ :=
  Classical.choose (Classical.choose_spec z.2)

theorem zAdjoinI5_eq_mkI5 (z : ZAdjoinI5) :
    z = mkI5 (zAdjoinI5Re z) (zAdjoinI5Im z) := by
  apply Subtype.ext
  exact Classical.choose_spec (Classical.choose_spec z.2)

theorem zAdjoinI5Re_mkI5 (m n : ℤ) : zAdjoinI5Re (mkI5 m n) = m :=
  (zAdjoinI5_coords_unique (Subtype.ext_iff.mp (zAdjoinI5_eq_mkI5 (mkI5 m n)).symm)).1

theorem zAdjoinI5Im_mkI5 (m n : ℤ) : zAdjoinI5Im (mkI5 m n) = n :=
  (zAdjoinI5_coords_unique (Subtype.ext_iff.mp (zAdjoinI5_eq_mkI5 (mkI5 m n)).symm)).2

theorem mkI5_add (m₁ n₁ m₂ n₂ : ℤ) :
    mkI5 m₁ n₁ + mkI5 m₂ n₂ = mkI5 (m₁ + m₂) (n₁ + n₂) := by
  apply Subtype.ext
  dsimp only [mkI5]
  change ((m₁ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₁) +
    ((m₂ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₂) = _
  push_cast
  ring

theorem mkI5_mul (m₁ n₁ m₂ n₂ : ℤ) :
    mkI5 m₁ n₁ * mkI5 m₂ n₂ = mkI5 (m₁ * m₂ - 5 * n₁ * n₂) (m₁ * n₂ + n₁ * m₂) := by
  apply Subtype.ext
  dsimp only [mkI5]
  change ((m₁ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₁) *
    ((m₂ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₂) = _
  have hs : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  push_cast
  calc ((m₁ : ℂ) + Complex.I * ↑(Real.sqrt 5) * ↑n₁) *
        (↑m₂ + Complex.I * ↑(Real.sqrt 5) * ↑n₂)
    _ = ↑m₁ * ↑m₂ + Complex.I ^ 2 * ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 * ↑n₁ * ↑n₂ +
        Complex.I * ↑(Real.sqrt 5) * (↑m₁ * ↑n₂ + ↑n₁ * ↑m₂) := by ring
    _ = ↑m₁ * ↑m₂ - 5 * ↑n₁ * ↑n₂ +
        Complex.I * ↑(Real.sqrt 5) * (↑m₁ * ↑n₂ + ↑n₁ * ↑m₂) := by
        rw [Complex.I_sq, hs]; ring

/-- Garling's norm `ϕ(m + i√5 n) = m^2 + 5 n^2` on `ℤ + i√5 ℤ` (§3.4, Ex. 3.12, p. 27). -/
noncomputable def zAdjoinI5Phi (z : ZAdjoinI5) : ℤ :=
  zAdjoinI5Re z ^ 2 + 5 * zAdjoinI5Im z ^ 2

theorem zAdjoinI5Phi_mkI5 (m n : ℤ) :
    zAdjoinI5Phi (mkI5 m n) = m ^ 2 + 5 * n ^ 2 := by
  simp [zAdjoinI5Phi, zAdjoinI5Re_mkI5, zAdjoinI5Im_mkI5]

theorem zAdjoinI5Phi_mul (a b : ZAdjoinI5) :
    zAdjoinI5Phi (a * b) = zAdjoinI5Phi a * zAdjoinI5Phi b := by
  conv_lhs => rw [zAdjoinI5_eq_mkI5 a, zAdjoinI5_eq_mkI5 b]
  rw [mkI5_mul, zAdjoinI5Phi_mkI5]
  unfold zAdjoinI5Phi
  ring

theorem zAdjoinI5Phi_nonneg (a : ZAdjoinI5) : 0 ≤ zAdjoinI5Phi a := by
  unfold zAdjoinI5Phi
  positivity

theorem zAdjoinI5_isUnit_iff (a : ZAdjoinI5) :
    IsUnit a ↔ a = 1 ∨ a = -1 := by
  have h1 : (1 : ZAdjoinI5) = mkI5 1 0 := by apply Subtype.ext; simp [mkI5]
  have hm1 : (-1 : ZAdjoinI5) = mkI5 (-1) 0 := by apply Subtype.ext; simp [mkI5]
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : zAdjoinI5Phi (u : ZAdjoinI5) * zAdjoinI5Phi (↑u⁻¹ : ZAdjoinI5) = 1 := by
      rw [← zAdjoinI5Phi_mul, u.mul_inv, h1, zAdjoinI5Phi_mkI5]
      norm_num
    have hnn1 : 0 ≤ zAdjoinI5Phi (u : ZAdjoinI5) := zAdjoinI5Phi_nonneg _
    have hnn2 : 0 ≤ zAdjoinI5Phi (↑u⁻¹ : ZAdjoinI5) := zAdjoinI5Phi_nonneg _
    have hphi1 : zAdjoinI5Phi (u : ZAdjoinI5) = 1 := by
      by_cases h2z : zAdjoinI5Phi (↑u⁻¹ : ZAdjoinI5) = 0
      · rw [h2z, mul_zero] at hmul; norm_num at hmul
      · have h2pos : 1 ≤ zAdjoinI5Phi (↑u⁻¹ : ZAdjoinI5) := by omega
        by_cases h1z : zAdjoinI5Phi (u : ZAdjoinI5) = 0
        · rw [h1z, zero_mul] at hmul; norm_num at hmul
        · have h1pos : 1 ≤ zAdjoinI5Phi (u : ZAdjoinI5) := by omega
          nlinarith
    unfold zAdjoinI5Phi at hphi1
    have him_sq_le0 : zAdjoinI5Im (u : ZAdjoinI5) ^ 2 ≤ 0 := by
      have h5 : 5 * zAdjoinI5Im (u : ZAdjoinI5) ^ 2 ≤ 1 := by
        linarith [sq_nonneg (zAdjoinI5Re u)]
      omega
    have him0 : zAdjoinI5Im (u : ZAdjoinI5) = 0 :=
      sq_eq_zero_iff.mp (le_antisymm him_sq_le0 (sq_nonneg _))
    have hre_sq : zAdjoinI5Re (u : ZAdjoinI5) ^ 2 = 1 := by
      rw [him0] at hphi1
      linarith
    have hre : zAdjoinI5Re (u : ZAdjoinI5) = 1 ∨ zAdjoinI5Re (u : ZAdjoinI5) = -1 := by
      have : (zAdjoinI5Re (u : ZAdjoinI5) - 1) * (zAdjoinI5Re (u : ZAdjoinI5) + 1) = 0 := by
        linarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hre with hre1 | hrem1
    · left; rw [zAdjoinI5_eq_mkI5 (u : ZAdjoinI5), hre1, him0, h1]
    · right; rw [zAdjoinI5_eq_mkI5 (u : ZAdjoinI5), hrem1, him0, hm1]
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

theorem zAdjoinI5Phi_gt_three {a : ZAdjoinI5} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) :
    3 < zAdjoinI5Phi a := by
  have h0 : (0 : ZAdjoinI5) = mkI5 0 0 := by apply Subtype.ext; simp [mkI5]
  have h1 : (1 : ZAdjoinI5) = mkI5 1 0 := by apply Subtype.ext; simp [mkI5]
  have hm1 : (-1 : ZAdjoinI5) = mkI5 (-1) 0 := by apply Subtype.ext; simp [mkI5]
  unfold zAdjoinI5Phi
  by_cases hn : zAdjoinI5Im a = 0
  · have hm_ne0 : zAdjoinI5Re a ≠ 0 := fun hm =>
      ha0 (by rw [zAdjoinI5_eq_mkI5 a, hm, hn, h0])
    have hm_ne1 : zAdjoinI5Re a ≠ 1 := fun hm =>
      ha1 (by rw [zAdjoinI5_eq_mkI5 a, hm, hn, h1])
    have hm_nem1 : zAdjoinI5Re a ≠ -1 := fun hm =>
      ham1 (by rw [zAdjoinI5_eq_mkI5 a, hm, hn, hm1])
    have hge2 : 2 ≤ zAdjoinI5Re a ∨ zAdjoinI5Re a ≤ -2 := by omega
    rcases hge2 with h | h <;> nlinarith
  · have hnsq : 1 ≤ zAdjoinI5Im a ^ 2 := by
      have : 1 ≤ |zAdjoinI5Im a| := Int.one_le_abs hn
      nlinarith [sq_abs (zAdjoinI5Im a)]
    nlinarith [sq_nonneg (zAdjoinI5Re a)]

/-- **Exercise 3.12** (§3.4, p. 27): In `R = ℤ + i√5 ℤ` (`ZAdjoinI5`),
(1) the units of `R` are `1` and `-1`;
(2) `ϕ(a) = m^2 + 5 n^2` satisfies `ϕ(ab) = ϕ(a) ϕ(b)` and `ϕ(a) > 3` if `a ∉ {0, 1, -1}`;
(3) `2 + i√5` and `2 - i√5` are irreducibles in `R`, while `2 + i√5` is not prime (since
`(2 + i√5)(2 - i√5) = 9 = 3 · 3` and `2 + i√5 ∤ 3`), so `R` is not a UFD. -/
theorem exercise_3_12 :
    (∀ a : ZAdjoinI5, IsUnit a ↔ a = 1 ∨ a = -1) ∧
    (∀ a b : ZAdjoinI5, zAdjoinI5Phi (a * b) = zAdjoinI5Phi a * zAdjoinI5Phi b) ∧
    (∀ a : ZAdjoinI5, a ≠ 0 → a ≠ 1 → a ≠ -1 → 3 < zAdjoinI5Phi a) ∧
    Irreducible (mkI5 2 1) ∧
    Irreducible (mkI5 2 (-1)) ∧
    ¬ Prime (mkI5 2 1) ∧
    ¬ IsGarlingUFD ZAdjoinI5 ∧
    ¬ UniqueFactorizationMonoid ZAdjoinI5 := by
  have hirr_9 : ∀ x : ZAdjoinI5, zAdjoinI5Phi x = 9 → Irreducible x := by
    intro x hx9
    have hx_nu : ¬ IsUnit x := by
      rw [zAdjoinI5_isUnit_iff]
      rintro (rfl | rfl)
      · have : zAdjoinI5Phi 1 = 1 := by
          have h1 : (1 : ZAdjoinI5) = mkI5 1 0 := by apply Subtype.ext; simp [mkI5]
          rw [h1, zAdjoinI5Phi_mkI5]; norm_num
        omega
      · have : zAdjoinI5Phi (-1) = 1 := by
          have hm1 : (-1 : ZAdjoinI5) = mkI5 (-1) 0 := by apply Subtype.ext; simp [mkI5]
          rw [hm1, zAdjoinI5Phi_mkI5]; norm_num
        omega
    refine ⟨hx_nu, fun b c hbc => ?_⟩
    by_contra hnot
    rw [not_or] at hnot
    rcases hnot with ⟨hbu, hcu⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hbc
      rw [hbc] at hx9
      have : zAdjoinI5Phi 0 = 0 := by
        have h0 : (0 : ZAdjoinI5) = mkI5 0 0 := by apply Subtype.ext; simp [mkI5]
        rw [h0, zAdjoinI5Phi_mkI5]; norm_num
      omega
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hbc
      rw [hbc] at hx9
      have : zAdjoinI5Phi 0 = 0 := by
        have h0 : (0 : ZAdjoinI5) = mkI5 0 0 := by apply Subtype.ext; simp [mkI5]
        rw [h0, zAdjoinI5Phi_mkI5]; norm_num
      omega
    rw [zAdjoinI5_isUnit_iff, not_or] at hbu hcu
    have hb4 : 3 < zAdjoinI5Phi b := zAdjoinI5Phi_gt_three hb0 hbu.1 hbu.2
    have hc4 : 3 < zAdjoinI5Phi c := zAdjoinI5Phi_gt_three hc0 hcu.1 hcu.2
    have hprod9 : zAdjoinI5Phi b * zAdjoinI5Phi c = 9 := by
      rw [← zAdjoinI5Phi_mul, ← hbc, hx9]
    nlinarith
  have hirr_plus : Irreducible (mkI5 2 1) :=
    hirr_9 (mkI5 2 1) (by rw [zAdjoinI5Phi_mkI5]; norm_num)
  have hirr_minus : Irreducible (mkI5 2 (-1)) :=
    hirr_9 (mkI5 2 (-1)) (by rw [zAdjoinI5Phi_mkI5]; norm_num)
  have hnot_prime : ¬ Prime (mkI5 2 1) := by
    intro hp
    have hdvd9 : mkI5 2 1 ∣ mkI5 3 0 * mkI5 3 0 := by
      refine ⟨mkI5 2 (-1), ?_⟩
      rw [mkI5_mul, mkI5_mul]
      norm_num
    have hdvd3 : mkI5 2 1 ∣ mkI5 3 0 := by
      rcases hp.dvd_or_dvd hdvd9 with h | h <;> exact h
    rcases hdvd3 with ⟨q, hq⟩
    have hphi_q : zAdjoinI5Phi q = 1 := by
      have h9 := congrArg zAdjoinI5Phi hq
      rw [zAdjoinI5Phi_mul, zAdjoinI5Phi_mkI5, zAdjoinI5Phi_mkI5] at h9
      linarith
    have hqu : q = 1 ∨ q = -1 := by
      rw [← zAdjoinI5_isUnit_iff]
      by_contra hnu
      rw [zAdjoinI5_isUnit_iff, not_or] at hnu
      have hq0 : q ≠ 0 := by
        rintro rfl
        have : zAdjoinI5Phi 0 = 0 := by
          have h0 : (0 : ZAdjoinI5) = mkI5 0 0 := by apply Subtype.ext; simp [mkI5]
          rw [h0, zAdjoinI5Phi_mkI5]; norm_num
        omega
      have := zAdjoinI5Phi_gt_three hq0 hnu.1 hnu.2
      omega
    rcases hqu with rfl | rfl
    · rw [mul_one] at hq
      have him := congrArg zAdjoinI5Im hq
      rw [zAdjoinI5Im_mkI5, zAdjoinI5Im_mkI5] at him
      norm_num at him
    · have hm1 : (-1 : ZAdjoinI5) = mkI5 (-1) 0 := by apply Subtype.ext; simp [mkI5]
      rw [hm1, mkI5_mul] at hq
      have him := congrArg zAdjoinI5Im hq
      rw [zAdjoinI5Im_mkI5, zAdjoinI5Im_mkI5] at him
      norm_num at him
  have hnot_ufd : ¬ IsGarlingUFD ZAdjoinI5 := fun h =>
    hnot_prime (((theorem_3_6 ZAdjoinI5).mp h).2 _ hirr_plus)
  have hnot_ufm : ¬ UniqueFactorizationMonoid ZAdjoinI5 :=
    fun h => hnot_ufd ((isGarlingUFD_iff_uniqueFactorizationMonoid ZAdjoinI5).mpr h)
  exact ⟨zAdjoinI5_isUnit_iff, zAdjoinI5Phi_mul,
    fun a ha0 ha1 ham1 => zAdjoinI5Phi_gt_three ha0 ha1 ham1,
    hirr_plus, hirr_minus, hnot_prime, hnot_ufd, hnot_ufm⟩

/-- **Exercise 3.13** (§3.4, p. 27): `ℤ + i√5 ℤ` (`ZAdjoinI5`) satisfies ACCPI (and `WfDvdMonoid`),
showing that ACCPI alone does not imply unique factorization. -/
theorem exercise_3_13 :
    SatisfiesACCPI ZAdjoinI5 ∧ WfDvdMonoid ZAdjoinI5 := by
  classical
  have hwf : WfDvdMonoid ZAdjoinI5 := by
    let μ : ZAdjoinI5 → WithTop ℕ := fun z =>
      if z = 0 then ⊤ else ((zAdjoinI5Phi z).toNat : WithTop ℕ)
    have hsub : Subrelation (@DvdNotUnit ZAdjoinI5 _) (InvImage (· < ·) μ) := by
      rintro a b ⟨ha0, c, hcu, rfl⟩
      dsimp only [InvImage, μ]
      rw [ite_eq_right ha0]
      by_cases hc0 : c = 0
      · subst hc0
        simp
      · have hac0 : a * c ≠ 0 := mul_ne_zero ha0 hc0
        rw [ite_eq_right hac0]
        refine WithTop.coe_lt_coe.mpr ?_
        simp only [Nat.cast_id]
        have ha_pos : 0 < zAdjoinI5Phi a := by
          have hnn := zAdjoinI5Phi_nonneg a
          have hne0 : zAdjoinI5Phi a ≠ 0 := by
            intro hz
            unfold zAdjoinI5Phi at hz
            have hr0 : zAdjoinI5Re a = 0 := by
              nlinarith [sq_nonneg (zAdjoinI5Re a), sq_nonneg (zAdjoinI5Im a)]
            have hi0 : zAdjoinI5Im a = 0 := by
              nlinarith [sq_nonneg (zAdjoinI5Re a), sq_nonneg (zAdjoinI5Im a)]
            apply ha0
            rw [zAdjoinI5_eq_mkI5 a, hr0, hi0]
            apply Subtype.ext; simp [mkI5]
          omega
        rw [zAdjoinI5_isUnit_iff, not_or] at hcu
        have hc4 : 3 < zAdjoinI5Phi c := zAdjoinI5Phi_gt_three hc0 hcu.1 hcu.2
        rw [zAdjoinI5Phi_mul]
        have hlt : zAdjoinI5Phi a < zAdjoinI5Phi a * zAdjoinI5Phi c := by nlinarith
        have hnn_prod : 0 ≤ zAdjoinI5Phi a * zAdjoinI5Phi c := by positivity
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hnn_prod]
        exact hlt
    exact Subrelation.wf hsub (InvImage.wf _ wellFounded_lt)
  exact ⟨(satisfiesACCPI_iff_wfDvdMonoid ZAdjoinI5).mpr hwf, hwf⟩

/-- Garling's definition of a *prime ideal* `J` of a ring `R` (§3.4, Ex. 3.14, p. 27): a proper
ideal `J ≠ R` such that `ab ∈ J` implies `a ∈ J` or `b ∈ J`. -/
structure IsGarlingPrimeIdeal {R : Type*} [CommRing R] (J : Ideal R) : Prop where
  ne_top : J ≠ ⊤
  mem_or_mem : ∀ a b : R, a * b ∈ J → a ∈ J ∨ b ∈ J

theorem isGarlingPrimeIdeal_iff {R : Type*} [CommRing R] (J : Ideal R) :
    IsGarlingPrimeIdeal J ↔ J.IsPrime :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, fun {a b} hab => h2 a b hab⟩,
    fun h => ⟨h.ne_top, fun _ _ hab => h.mem_or_mem hab⟩⟩

/-- **Exercise 3.14** (§3.4, p. 27):
(1) `R / J` is an integral domain if and only if `J` is a prime ideal;
(2) in an integral domain `R`, `{0}` is a prime ideal;
(3) for any ring `R` (in particular any integral domain) and any non-zero element `c` of `R`, `c`
is prime if and only if `(c)` is a prime ideal. -/
theorem exercise_3_14 :
    (∀ (R : Type) [CommRing R] [Nontrivial R] (J : Ideal R),
      IsDomain (R ⧸ J) ↔ IsGarlingPrimeIdeal J) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R],
      IsGarlingPrimeIdeal (⊥ : Ideal R)) ∧
    (∀ (R : Type) [CommRing R] {c : R}, c ≠ 0 →
      (IsGarlingPrime c ↔ IsGarlingPrimeIdeal (Ideal.span {c})) ∧
      (Prime c ↔ (Ideal.span {c}).IsPrime)) := by
  refine ⟨fun R _ _ J => ?_, fun R _ _ => ?_, fun R _ {c} hc => ?_⟩
  · rw [Ideal.Quotient.isDomain_iff_prime, isGarlingPrimeIdeal_iff]
  · rw [isGarlingPrimeIdeal_iff]
    exact bot_isPrime_of_isDomain R
  · have hmain : Prime c ↔ (Ideal.span {c}).IsPrime := by
      constructor
      · intro hp
        refine ⟨mt Ideal.span_singleton_eq_top.mp hp.not_isUnit, fun {a b} hab => ?_⟩
        rw [Ideal.mem_span_singleton] at hab ⊢
        rw [Ideal.mem_span_singleton]
        exact hp.dvd_or_dvd hab
      · intro hI
        refine ⟨hc, mt Ideal.span_singleton_eq_top.mpr hI.ne_top, fun a b hab => ?_⟩
        rw [← Ideal.mem_span_singleton] at hab ⊢
        rw [← Ideal.mem_span_singleton]
        exact hI.mem_or_mem hab
    exact ⟨(isGarlingPrime_iff c).trans (hmain.trans (isGarlingPrimeIdeal_iff _).symm), hmain⟩

/-! ## §3.5 Principal ideal domains (printed pp. 28–29, PDF pp. 36–37) -/

/-- Garling's definition of a *principal ideal domain* (**PID**, §3.5, p. 28): an integral domain
in which every ideal is principal. -/
structure IsGarlingPID (R : Type*) [CommRing R] : Prop where
  isIntegralDomain : IsGarlingIntegralDomain R
  all_principal : ∀ I : Ideal R, ∃ a : R, I = Ideal.span {a}

theorem isGarlingPID_iff (R : Type*) [CommRing R] :
    IsGarlingPID R ↔ IsDomain R ∧ IsPrincipalIdealRing R := by
  rw [show IsGarlingPID R ↔ IsGarlingIntegralDomain R ∧ (∀ I : Ideal R, ∃ a : R, I = Ideal.span {a}) from
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩, isGarlingIntegralDomain_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hall
    exact ⟨fun I => ⟨hall I⟩⟩
  · intro hpir I
    exact (hpir.principal I).principal

/-- Prose examples (§3.5, p. 28): `ℤ` and fields are PIDs; `K[x, y]` (`MvPolynomial (Fin 2) K` for a
field `K`) and `ℤ[x]` are NOT PIDs (`(x, y)` and `(2, x)` are not principal). -/
theorem examples_3_5_pid_and_non_pid (K : Type*) [Field K] :
    IsGarlingPID ℤ ∧
    IsGarlingPID K ∧
    ¬ IsPrincipalIdealRing (MvPolynomial (Fin 2) K) ∧
    ¬ IsPrincipalIdealRing ℤ[X] := by
  refine ⟨(isGarlingPID_iff ℤ).mpr ⟨inferInstance, inferInstance⟩,
    (isGarlingPID_iff K).mpr ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro hpir
    let I : Ideal (MvPolynomial (Fin 2) K) :=
      Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}
    obtain ⟨g, hg0_span⟩ := (hpir.principal I).principal
    have hg : I = Ideal.span {g} := hg0_span
    have hx0 : MvPolynomial.X 0 ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    have hx1 : MvPolynomial.X 1 ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    rw [Ideal.mem_span_singleton] at hx0 hx1
    obtain ⟨q₀, hq₀⟩ := hx0
    obtain ⟨q₁, hq₁⟩ := hx1
    have hg0 : g ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hq₀
      exact MvPolynomial.X_ne_zero (0 : Fin 2) hq₀
    have hq₀0 : q₀ ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hq₀
      exact MvPolynomial.X_ne_zero (0 : Fin 2) hq₀
    have hdeg0 : g.totalDegree + q₀.totalDegree = 1 := by
      rw [← MvPolynomial.totalDegree_mul_of_isDomain hg0 hq₀0, ← hq₀, MvPolynomial.totalDegree_X]
    by_cases hgt : g.totalDegree = 0
    · obtain ⟨c, rfl⟩ : ∃ c : K, g = MvPolynomial.C c :=
        ⟨g.coeff 0, (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hgt).trans rfl⟩
      have hc0 : c ≠ 0 := fun h0 => hg0 (by simp [h0])
      have hgu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) K) :=
        (IsUnit.mk0 c hc0).map MvPolynomial.C
      have hItop : I = ⊤ := by
        rw [hg, Ideal.span_singleton_eq_top]
        exact hgu
      have h1mem : (1 : MvPolynomial (Fin 2) K) ∈ I := hItop ▸ Submodule.mem_top
      let ε : MvPolynomial (Fin 2) K →+* K := MvPolynomial.eval 0
      have hεI : ∀ p ∈ I, ε p = 0 := by
        intro p hp
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
        · rintro _ (rfl | rfl) <;> simp [ε]
        · simp [ε]
        · intro a b _ _ ha hb; simp [ha, hb]
        · intro a b _ hb; simp [smul_eq_mul, hb]
      have h10 : (1 : K) = 0 := by simpa [ε] using hεI 1 h1mem
      exact one_ne_zero h10
    · have hgt1 : g.totalDegree = 1 := by omega
      have hqt0 : q₀.totalDegree = 0 := by omega
      have hq₀C : q₀ = MvPolynomial.C (q₀.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hqt0
      have hc0 : q₀.coeff 0 ≠ 0 := fun h0 => hq₀0 (by rw [hq₀C, h0, map_zero])
      have hg_eq : g = MvPolynomial.C (q₀.coeff 0)⁻¹ * MvPolynomial.X 0 := by
        calc g = MvPolynomial.C (q₀.coeff 0)⁻¹ * (g * MvPolynomial.C (q₀.coeff 0)) := by
              rw [mul_comm g, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
          _ = MvPolynomial.C (q₀.coeff 0)⁻¹ * MvPolynomial.X 0 := by rw [← hq₀C, ← hq₀]
      let ev0 : MvPolynomial (Fin 2) K →+* K :=
        MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (0 : K) else 1)
      have hev1 : ev0 (MvPolynomial.X 1) = 1 := by simp [ev0]
      have hevg : ev0 (g * q₁) = 0 := by simp [ev0, hg_eq]
      rw [← hq₁, hev1] at hevg
      exact one_ne_zero hevg
  · intro hpir
    let I : Ideal ℤ[X] := Ideal.span {Polynomial.C (2 : ℤ), Polynomial.X}
    obtain ⟨g, hg0_span⟩ := (hpir.principal I).principal
    have hg : I = Ideal.span {g} := hg0_span
    have h2 : Polynomial.C (2 : ℤ) ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    have hx : (Polynomial.X : ℤ[X]) ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    rw [Ideal.mem_span_singleton] at h2 hx
    have h2ne : (Polynomial.C (2 : ℤ) : ℤ[X]) ≠ 0 := by simp
    have hg_deg : g.natDegree = 0 := by
      have hle := Polynomial.natDegree_le_of_dvd h2 h2ne
      simpa using hle
    rw [Polynomial.eq_C_of_natDegree_eq_zero hg_deg] at h2 hx hg
    rcases hx with ⟨q, hq⟩
    have hcoeff1 : (1 : ℤ) = g.coeff 0 * q.coeff 1 := by
      have := congrArg (fun p : ℤ[X] => p.coeff 1) hq
      simpa using this
    have hgu : IsUnit (Polynomial.C (g.coeff 0) : ℤ[X]) :=
      (IsUnit.of_mul_eq_one (q.coeff 1) hcoeff1.symm).map Polynomial.C
    have hItop : I = ⊤ := by
      rw [hg, Ideal.span_singleton_eq_top]
      exact hgu
    have h1mem : (1 : ℤ[X]) ∈ I := hItop ▸ Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1mem
    obtain ⟨u, v, huv⟩ := h1mem
    have hev0 := congrArg (Polynomial.eval 0) huv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_zero, add_zero, Polynomial.eval_one] at hev0
    omega

/-- **Theorem 3.7** (§3.5, p. 28): Suppose that `f` and `g` are elements of `K[x]` over a field `K`
with `f ≠ 0` (in particular for non-zero `f, g ∈ K[x]`). Then there exist `q, r ∈ K[x]` such that
`g = q * f + r` and either `r = 0` or `r ≠ 0` with `garlingDegree r < garlingDegree f`
(`r.natDegree < f.natDegree`). -/
theorem theorem_3_7 {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) (g : K[X]) :
    ∃ q r : K[X], g = q * f + r ∧
      (r = 0 ∨ ∃ hr : r ≠ 0, garlingDegree r hr < garlingDegree f hf) := by
  suffices hmain : ∀ n : ℕ, ∀ g : K[X], g.natDegree ≤ n →
      ∃ q r : K[X], g = q * f + r ∧
        (r = 0 ∨ ∃ hr : r ≠ 0, garlingDegree r hr < garlingDegree f hf) from
    hmain g.natDegree g le_rfl
  intro n
  induction n with
  | zero =>
    intro g hg0
    by_cases hg : g = 0
    · exact ⟨0, 0, by simp [hg], Or.inl rfl⟩
    · by_cases hlt : f.natDegree = 0
      · have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hlt
        have hgC : g = Polynomial.C (g.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hg0)
        have hfc0 : f.coeff 0 ≠ 0 := fun h0 => hf (by rw [hfC, h0, map_zero])
        refine ⟨Polynomial.C (g.coeff 0 * (f.coeff 0)⁻¹), 0, ?_, Or.inl rfl⟩
        calc g = Polynomial.C (g.coeff 0) := hgC
          _ = Polynomial.C (g.coeff 0 * ((f.coeff 0)⁻¹ * f.coeff 0)) := by
                rw [inv_mul_cancel₀ hfc0, mul_one]
          _ = Polynomial.C (g.coeff 0 * (f.coeff 0)⁻¹) * Polynomial.C (f.coeff 0) + 0 := by
                rw [add_zero, ← map_mul, mul_assoc]
          _ = Polynomial.C (g.coeff 0 * (f.coeff 0)⁻¹) * f + 0 := by rw [← hfC]
      · refine ⟨0, g, by simp, Or.inr ⟨hg, ?_⟩⟩
        change g.natDegree < f.natDegree
        omega
  | succ n ih =>
    intro g hgn
    by_cases hle : g.natDegree ≤ n
    · exact ih g hle
    · have hg_deg : g.natDegree = n + 1 := by omega
      have hg : g ≠ 0 := by
        rintro rfl
        simp at hg_deg
      by_cases hlt : g.natDegree < f.natDegree
      · exact ⟨0, g, by simp, Or.inr ⟨hg, hlt⟩⟩
      · have hfle : f.natDegree ≤ g.natDegree := Nat.le_of_not_lt hlt
        have hflc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
        let c : K := g.leadingCoeff * f.leadingCoeff⁻¹
        let m : ℕ := g.natDegree - f.natDegree
        let t : K[X] := Polynomial.C c * Polynomial.X ^ m
        let h : K[X] := g - t * f
        have h_deg_le : h.natDegree ≤ n := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro i hi
          have hig : g.natDegree ≤ i := by omega
          rw [Polynomial.coeff_sub]
          rcases eq_or_lt_of_le hig with rfl | hgt
          · have htf_coeff : (t * f).coeff g.natDegree = g.leadingCoeff := by
              have hmk : f.natDegree + m = g.natDegree := by omega
              calc (t * f).coeff g.natDegree
                  = (Polynomial.C c * (f * Polynomial.X ^ m)).coeff (f.natDegree + m) := by
                      rw [hmk, mul_assoc, mul_comm (Polynomial.X ^ m) f]
                _ = c * (f * Polynomial.X ^ m).coeff (f.natDegree + m) :=
                      Polynomial.coeff_C_mul _
                _ = c * f.coeff f.natDegree := by
                      rw [Polynomial.coeff_mul_X_pow]
                _ = g.leadingCoeff * f.leadingCoeff⁻¹ * f.leadingCoeff := rfl
                _ = g.leadingCoeff := inv_mul_cancel_right₀ hflc g.leadingCoeff
            rw [htf_coeff, Polynomial.coeff_natDegree, sub_self]
          · have hg_i : g.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
            have htf_deg : (t * f).natDegree < i := by
              calc (t * f).natDegree
                  ≤ t.natDegree + f.natDegree := Polynomial.natDegree_mul_le
                _ ≤ m + f.natDegree := by
                    have ht_le : t.natDegree ≤ m := by
                      calc t.natDegree
                          ≤ (Polynomial.C c).natDegree + (Polynomial.X ^ m : K[X]).natDegree :=
                              Polynomial.natDegree_mul_le
                        _ = m := by simp
                    omega
                _ = g.natDegree := Nat.sub_add_cancel hfle
                _ < i := hgt
            rw [hg_i, Polynomial.coeff_eq_zero_of_natDegree_lt htf_deg, sub_zero]
        obtain ⟨q', r, hq'r, hr_cond⟩ := ih h h_deg_le
        refine ⟨t + q', r, ?_, hr_cond⟩
        calc g = t * f + h := (add_sub_cancel _ _).symm
          _ = t * f + (q' * f + r) := by rw [hq'r]
          _ = (t + q') * f + r := by ring

/-- **Theorem 3.8** (§3.5, p. 28): If `K` is a field, `K[x]` is a principal ideal domain (proved
directly from `theorem_3_7` via a minimal-degree element of `J`, plus uniqueness of the monic
generator). -/
theorem theorem_3_8 (K : Type*) [Field K] :
    IsGarlingPID K[X] ∧ IsPrincipalIdealRing K[X] ∧
      ∀ J : Ideal K[X], J ≠ ⊥ → ∃! g : K[X], g.Monic ∧ J = Ideal.span {g} := by
  have hpir : IsPrincipalIdealRing K[X] := ⟨fun J => by
    classical
    by_cases hJ : J = ⊥
    · exact ⟨⟨0, by simp [hJ]⟩⟩
    · obtain ⟨f₀, hf₀J, hf₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      have hex_deg : ∃ d : ℕ, ∃ f ∈ J, f ≠ 0 ∧ f.natDegree = d :=
        ⟨f₀.natDegree, f₀, hf₀J, hf₀0, rfl⟩
      let d := Nat.find hex_deg
      obtain ⟨f, hfJ, hf0, hfd⟩ := Nat.find_spec hex_deg
      refine ⟨⟨f, le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfJ))⟩⟩
      intro g hgJ
      obtain ⟨q, r, hg_eq, hr_cond⟩ := theorem_3_7 hf0 g
      rcases hr_cond with rfl | ⟨hr0, hr_lt⟩
      · rw [add_zero, mul_comm] at hg_eq
        exact Ideal.mem_span_singleton.mpr ⟨q, hg_eq⟩
      · have hrJ : r ∈ J := by
          have hsub : g - q * f ∈ J := J.sub_mem hgJ (J.mul_mem_left q hfJ)
          rwa [hg_eq, add_sub_cancel_left] at hsub
        have hr_lt' : r.natDegree < d := by
          change r.natDegree < f.natDegree at hr_lt
          rwa [hfd] at hr_lt
        exact False.elim (Nat.find_min hex_deg hr_lt' ⟨r, hrJ, hr0, rfl⟩)⟩
  refine ⟨(isGarlingPID_iff K[X]).mpr ⟨inferInstance, hpir⟩, hpir, fun J hJ => ?_⟩
  obtain ⟨f, hf0_span⟩ := (hpir.principal J).principal
  have hf : J = Ideal.span {f} := hf0_span
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hJ
    rw [hf, Ideal.span_singleton_eq_bot]
  let g : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hlc0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hg_monic : g.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc0]
  have hg_span : J = Ideal.span {g} := by
    rw [hf]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    exact ⟨((IsUnit.mk0 f.leadingCoeff⁻¹ (inv_ne_zero hlc0)).map Polynomial.C).unit,
      by simp [g, mul_comm]⟩
  refine ⟨g, ⟨hg_monic, hg_span⟩, fun h ⟨hh_monic, hh_span⟩ => ?_⟩
  have hass : Associated g h :=
    Ideal.span_singleton_eq_span_singleton.mp (hg_span.symm.trans hh_span)
  rcases hass with ⟨u, hu⟩
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hg_h : g * Polynomial.C c = h := by rwa [← hcu] at hu
  have hlc : c = 1 := by
    have := congrArg Polynomial.leadingCoeff hg_h
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hg_monic.leadingCoeff,
      hh_monic.leadingCoeff, one_mul] at this
    exact this
  rw [← hg_h, hlc, Polynomial.C_1, mul_one]

/-- **Theorem 3.9** (§3.5, p. 29): A principal ideal domain `R` is a unique factorization domain. -/
theorem theorem_3_9 {R : Type*} [CommRing R] (hPID : IsGarlingPID R) :
    IsGarlingUFD R := by
  obtain ⟨_, _⟩ := (isGarlingPID_iff R).mp hPID
  exact (isGarlingUFD_iff_uniqueFactorizationMonoid R).mpr inferInstance

/-- Mathlib typeclass companion to **Theorem 3.9** (§3.5, p. 29). -/
theorem theorem_3_9_pir (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsGarlingUFD R ∧ UniqueFactorizationMonoid R :=
  ⟨theorem_3_9 ((isGarlingPID_iff R).mpr ⟨inferInstance, inferInstance⟩), inferInstance⟩

/-- Auxiliary characterization of non-zero ideals in a PID (§3.5, p. 29 & §3.9, p. 35): for a
non-zero ideal `J ≠ ⊥` in a PID `R`, `(1) J = (p)` with `p` irreducible, `(2) J = (p)` with `p`
prime, `(3) J` is prime, `(4) J` is maximal, and `(5) R / J` is a field are all equivalent. -/
theorem pid_nonzero_ideal_tfae {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {J : Ideal R} (hJ : J ≠ ⊥) :
    List.TFAE [
      ∃ p : R, Irreducible p ∧ J = Ideal.span {p},
      ∃ p : R, Prime p ∧ J = Ideal.span {p},
      J.IsPrime,
      J.IsMaximal,
      IsField (R ⧸ J)
    ] := by
  tfae_have 1 → 2 := by
    rintro ⟨p, hp, rfl⟩
    exact ⟨p, UniqueFactorizationMonoid.irreducible_iff_prime.mp hp, rfl⟩
  tfae_have 2 → 3 := by
    rintro ⟨p, hp, rfl⟩
    exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  tfae_have 3 → 4 := by
    intro hp
    exact @IsPrime.to_maximal_ideal R _ _ _ J hp hJ
  tfae_have 4 → 5 := by
    intro hm
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mp hm
  tfae_have 5 → 1 := by
    intro hf
    have hm : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hf
    have hp : J.IsPrime := hm.isPrime
    obtain ⟨p, hp_span⟩ := (IsPrincipalIdealRing.principal J).principal
    have hJp : J = Ideal.span {p} := hp_span
    rw [hJp] at hp hJ ⊢
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hJ (Ideal.span_singleton_eq_bot.mpr rfl)
    exact ⟨p, ((Ideal.span_singleton_prime hp0).mp hp).irreducible, rfl⟩
  tfae_finish

/-! ### Exercises 3.15–3.18 (§3.5, printed p. 29, PDF p. 37) -/

/-- **Exercise 3.15** (§3.5, p. 29): Suppose `K` is a field and `f ∈ K[x]`.
(1) `α ∈ K` is a root of `f` (`f.eval α = 0`) if and only if `f ∈ (x - α)`.
(2) If `f ≠ 0` has degree `n`, then `f` has at most `n` distinct roots in `K`. -/
theorem exercise_3_15 {K : Type*} [Field K] (f : K[X]) :
    (∀ α : K, f.eval α = 0 ↔ f ∈ Ideal.span {Polynomial.X - Polynomial.C α}) ∧
    (f ≠ 0 → ∀ S : Finset K, (∀ α ∈ S, f.eval α = 0) → S.card ≤ f.natDegree) := by
  refine ⟨fun α => ?_, fun hf0 S hS => ?_⟩
  · rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  · classical
    have hsub : S ⊆ f.roots.toFinset := by
      intro α hα
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0]
      exact hS α hα
    calc S.card ≤ f.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ f.roots.card := Multiset.toFinset_card_le f.roots
      _ ≤ f.natDegree := Polynomial.card_roots' f

/-- **Exercise 3.16** (§3.5, p. 29):
(1) The ideals of `ℤ_6` (`ZMod 6`) are precisely `(0)`, `(2)`, `(3)`, and `(1)` (four distinct
ideals), so every ideal of `ℤ_6` is principal (`IsPrincipalIdealRing (ZMod 6)`);
(2) `ℤ_6` is NOT a principal ideal domain (`¬ IsGarlingPID (ZMod 6)`), because `ℤ_6` is not an
integral domain (`2 ≠ 0`, `3 ≠ 0`, `2 · 3 = 0`). -/
theorem exercise_3_16 :
    ((Set.univ : Set (Ideal (ZMod 6))) =
      {Ideal.span {(0 : ZMod 6)}, Ideal.span {(2 : ZMod 6)},
       Ideal.span {(3 : ZMod 6)}, Ideal.span {(1 : ZMod 6)}}) ∧
    [Ideal.span {(0 : ZMod 6)}, Ideal.span {(2 : ZMod 6)},
     Ideal.span {(3 : ZMod 6)}, Ideal.span {(1 : ZMod 6)}].Nodup ∧
    IsPrincipalIdealRing (ZMod 6) ∧
    ¬ IsDomain (ZMod 6) ∧
    ¬ IsGarlingPID (ZMod 6) := by
  have zmod6_cases : ∀ x : ZMod 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by decide
  have hall_ideals : ∀ I : Ideal (ZMod 6),
      I = Ideal.span {0} ∨ I = Ideal.span {2} ∨ I = Ideal.span {3} ∨ I = Ideal.span {1} := by
    intro I
    by_cases h1 : (1 : ZMod 6) ∈ I
    · right; right; right
      ext x
      simp only [Ideal.mem_span_singleton, one_dvd, iff_true]
      simpa using I.mul_mem_left x h1
    have h5 : (5 : ZMod 6) ∉ I := by
      intro h
      apply h1
      have h55 : (5 : ZMod 6) * 5 = 1 := by decide
      rw [← h55]
      exact I.mul_mem_left 5 h
    have h24 : (2 : ZMod 6) ∈ I ↔ (4 : ZMod 6) ∈ I := by
      have h22 : (2 : ZMod 6) * 2 = 4 := by decide
      have h24_eq : (2 : ZMod 6) * 4 = 2 := by decide
      exact ⟨fun h => h22 ▸ I.mul_mem_left 2 h, fun h => h24_eq ▸ I.mul_mem_left 2 h⟩
    by_cases h2 : (2 : ZMod 6) ∈ I
    · by_cases h3 : (3 : ZMod 6) ∈ I
      · exfalso
        apply h1
        have : (3 : ZMod 6) + (-1) * 2 = 1 := by decide
        rw [← this]
        exact I.add_mem h3 (I.mul_mem_left (-1) h2)
      · right; left
        ext x
        rw [Ideal.mem_span_singleton]
        have h4 : (4 : ZMod 6) ∈ I := h24.mp h2
        rcases zmod6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨fun _ => ⟨0, by decide⟩, fun _ => I.zero_mem⟩
        · exact ⟨fun hx => absurd hx h1, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
        · exact ⟨fun _ => ⟨1, by decide⟩, fun _ => h2⟩
        · exact ⟨fun hx => absurd hx h3, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
        · exact ⟨fun _ => ⟨2, by decide⟩, fun _ => h4⟩
        · exact ⟨fun hx => absurd hx h5, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
    · have h4 : (4 : ZMod 6) ∉ I := fun h => h2 (h24.mpr h)
      by_cases h3 : (3 : ZMod 6) ∈ I
      · right; right; left
        ext x
        rw [Ideal.mem_span_singleton]
        rcases zmod6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨fun _ => ⟨0, by decide⟩, fun _ => I.zero_mem⟩
        · exact ⟨fun hx => absurd hx h1, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
        · exact ⟨fun hx => absurd hx h2, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
        · exact ⟨fun _ => ⟨1, by decide⟩, fun _ => h3⟩
        · exact ⟨fun hx => absurd hx h4, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
        · exact ⟨fun hx => absurd hx h5, fun ⟨c, hc⟩ => by
            exfalso; rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide⟩
      · left
        ext x
        rw [Ideal.mem_span_singleton, zero_dvd_iff]
        rcases zmod6_cases x with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨fun _ => rfl, fun _ => I.zero_mem⟩
        · exact ⟨fun hx => absurd hx h1, fun h => by exfalso; revert h; decide⟩
        · exact ⟨fun hx => absurd hx h2, fun h => by exfalso; revert h; decide⟩
        · exact ⟨fun hx => absurd hx h3, fun h => by exfalso; revert h; decide⟩
        · exact ⟨fun hx => absurd hx h4, fun h => by exfalso; revert h; decide⟩
        · exact ⟨fun hx => absurd hx h5, fun h => by exfalso; revert h; decide⟩
  have hset : (Set.univ : Set (Ideal (ZMod 6))) =
      {Ideal.span {0}, Ideal.span {2}, Ideal.span {3}, Ideal.span {1}} := by
    ext I
    simp only [Set.mem_univ, true_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hall_ideals I
  have hnodup : [Ideal.span {(0 : ZMod 6)}, Ideal.span {(2 : ZMod 6)},
      Ideal.span {(3 : ZMod 6)}, Ideal.span {(1 : ZMod 6)}].Nodup := by
    have h02 : Ideal.span {(0 : ZMod 6)} ≠ Ideal.span {2} := by
      intro h
      have : (2 : ZMod 6) ∈ Ideal.span {(0 : ZMod 6)} := h ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton, zero_dvd_iff] at this
      revert this; decide
    have h03 : Ideal.span {(0 : ZMod 6)} ≠ Ideal.span {3} := by
      intro h
      have : (3 : ZMod 6) ∈ Ideal.span {(0 : ZMod 6)} := h ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton, zero_dvd_iff] at this
      revert this; decide
    have h01 : Ideal.span {(0 : ZMod 6)} ≠ Ideal.span {1} := by
      intro h
      have : (1 : ZMod 6) ∈ Ideal.span {(0 : ZMod 6)} := h ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton, zero_dvd_iff] at this
      revert this; decide
    have h23 : Ideal.span {(2 : ZMod 6)} ≠ Ideal.span {3} := by
      intro h
      have : (2 : ZMod 6) ∈ Ideal.span {(3 : ZMod 6)} := h ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton] at this
      rcases this with ⟨c, hc⟩
      rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide
    have h21 : Ideal.span {(2 : ZMod 6)} ≠ Ideal.span {1} := by
      intro h
      have : (1 : ZMod 6) ∈ Ideal.span {(2 : ZMod 6)} := h.symm ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton] at this
      rcases this with ⟨c, hc⟩
      rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide
    have h31 : Ideal.span {(3 : ZMod 6)} ≠ Ideal.span {1} := by
      intro h
      have : (1 : ZMod 6) ∈ Ideal.span {(3 : ZMod 6)} := h.symm ▸ Ideal.subset_span (by simp)
      rw [Ideal.mem_span_singleton] at this
      rcases this with ⟨c, hc⟩
      rcases zmod6_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hc <;> decide
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, and_true]
    exact ⟨⟨h02, h03, h01⟩, ⟨h23, h21⟩, h31, not_false⟩
  have hpir : IsPrincipalIdealRing (ZMod 6) :=
    ⟨fun I => by
      rcases hall_ideals I with rfl | rfl | rfl | rfl
      · exact ⟨⟨0, rfl⟩⟩
      · exact ⟨⟨2, rfl⟩⟩
      · exact ⟨⟨3, rfl⟩⟩
      · exact ⟨⟨1, rfl⟩⟩⟩
  have hndom : ¬ IsDomain (ZMod 6) := by
    intro _
    have hmul : (2 : ZMod 6) * 3 = 0 := by decide
    rcases mul_eq_zero.mp hmul with h2 | h3
    · revert h2; decide
    · revert h3; decide
  exact ⟨hset, hnodup, hpir, hndom, fun hpid => hndom ((isGarlingPID_iff (ZMod 6)).mp hpid).1⟩

private theorem natPrime_int_dvd_or_dvd {p : ℕ} (hp : Nat.Prime p) {a b : ℤ}
    (h : (p : ℤ) ∣ a * b) : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul, hp.dvd_mul,
    ← Int.ofNat_dvd_left, ← Int.ofNat_dvd_left] at h
  exact h

/-- Garling's subring `R = {r / s ∈ ℚ : p ∤ s}` of `ℚ` for a prime `p` (§3.5, Ex. 3.17, p. 29;
reused in §3.9, Ex. 3.27, p. 36). -/
def RatLocalAtPrime (p : ℕ) (hp : Nat.Prime p) : Subring ℚ where
  carrier := {q : ℚ | ∃ r s : ℤ, ¬ ((p : ℤ) ∣ s) ∧ q = (r : ℚ) / (s : ℚ)}
  mul_mem' := by
    rintro _ _ ⟨r₁, s₁, hs₁, rfl⟩ ⟨r₂, s₂, hs₂, rfl⟩
    refine ⟨r₁ * r₂, s₁ * s₂, ?_, by push_cast; ring⟩
    intro hdvd
    rcases natPrime_int_dvd_or_dvd hp hdvd with h1 | h2
    · exact hs₁ h1
    · exact hs₂ h2
  one_mem' := ⟨1, 1, fun h => hp.ne_one (Nat.dvd_one.mp (Int.ofNat_dvd_left.mp h)), by simp⟩
  add_mem' := by
    rintro _ _ ⟨r₁, s₁, hs₁, rfl⟩ ⟨r₂, s₂, hs₂, rfl⟩
    have hs₁0 : (s₁ : ℚ) ≠ 0 := by
      exact_mod_cast (fun h0 : s₁ = 0 => hs₁ (h0 ▸ dvd_zero (p : ℤ)))
    have hs₂0 : (s₂ : ℚ) ≠ 0 := by
      exact_mod_cast (fun h0 : s₂ = 0 => hs₂ (h0 ▸ dvd_zero (p : ℤ)))
    refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, ?_, ?_⟩
    · intro hdvd
      rcases natPrime_int_dvd_or_dvd hp hdvd with h1 | h2
      · exact hs₁ h1
      · exact hs₂ h2
    · push_cast
      rw [div_add_div _ _ hs₁0 hs₂0]
      ring
  zero_mem' := ⟨0, 1, fun h => hp.ne_one (Nat.dvd_one.mp (Int.ofNat_dvd_left.mp h)), by simp⟩
  neg_mem' := by
    rintro _ ⟨r, s, hs, rfl⟩
    exact ⟨-r, s, hs, by push_cast; ring⟩

theorem mem_ratLocalAtPrime_iff {p : ℕ} (hp : Nat.Prime p) (q : ℚ) :
    q ∈ RatLocalAtPrime p hp ↔ ¬ (p ∣ q.den) := by
  constructor
  · rintro ⟨r, s, hs, hq⟩ hpdvd
    have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero (p : ℤ))
    have hq_eq : (q.num : ℚ) / (q.den : ℚ) = (r : ℚ) / (s : ℚ) := by
      rw [Rat.num_div_den, hq]
    have hden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hs0_q : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs0
    have hcross_q : (q.num : ℚ) * (s : ℚ) = (r : ℚ) * (q.den : ℚ) :=
      (div_eq_div_iff hden0 hs0_q).mp hq_eq
    have hcross : q.num * s = r * (q.den : ℤ) := by exact_mod_cast hcross_q
    have hp_dvd_rhs : (p : ℤ) ∣ q.num * s := by
      rw [hcross]
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpdvd) r
    have hp_num : (p : ℤ) ∣ q.num := (natPrime_int_dvd_or_dvd hp hp_dvd_rhs).resolve_right hs
    have hp_abs : p ∣ q.num.natAbs := Int.ofNat_dvd_left.mp hp_num
    have hp_gcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hp_abs hpdvd
    rw [q.reduced] at hp_gcd
    exact hp.ne_one (Nat.dvd_one.mp hp_gcd)
  · intro hndvd
    refine ⟨q.num, (q.den : ℤ), ?_, (Rat.num_div_den q).symm⟩
    exact fun h => hndvd (Int.natCast_dvd_natCast.mp h)

/-- Elementary `p`-adic valuation decomposition on `ℕ`: every `n ≠ 0` and `p ≥ 2` satisfies
`n = p ^ k * m` with `¬ (p ∣ m)`. -/
theorem nat_exists_eq_pow_mul_not_dvd {p : ℕ} (hp : 1 < p) :
    ∀ n : ℕ, n ≠ 0 → ∃ k m : ℕ, ¬ (p ∣ m) ∧ n = p ^ k * m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn0
    by_cases hd : p ∣ n
    · obtain ⟨q, rfl⟩ := hd
      have hq0 : q ≠ 0 := fun h0 => hn0 (by simp [h0])
      have hq_lt : q < p * q := by
        calc q = 1 * q := (one_mul q).symm
          _ < p * q := Nat.mul_lt_mul_of_pos_right hp (Nat.pos_of_ne_zero hq0)
      obtain ⟨k, m, hm, hqm⟩ := ih q hq_lt hq0
      exact ⟨k + 1, m, hm, by rw [hqm, pow_succ', mul_assoc]⟩
    · exact ⟨0, n, hd, by simp⟩

theorem ratLocalAtPrime_isUnit_iff {p : ℕ} (hp : Nat.Prime p) (x : RatLocalAtPrime p hp) :
    IsUnit x ↔ ∃ r s : ℤ, ¬ ((p : ℤ) ∣ r) ∧ ¬ ((p : ℤ) ∣ s) ∧ (x : ℚ) = (r : ℚ) / (s : ℚ) := by
  constructor
  · rintro ⟨u, rfl⟩
    let q : ℚ := (u : RatLocalAtPrime p hp)
    have hmul1 : q * ((↑u⁻¹ : RatLocalAtPrime p hp) : ℚ) = 1 :=
      congrArg Subtype.val u.mul_inv
    have hx_ne0 : q ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hmul1
      exact zero_ne_one hmul1
    have hq_mem : q ∈ RatLocalAtPrime p hp := (u : RatLocalAtPrime p hp).2
    have hqinv_mem : q⁻¹ ∈ RatLocalAtPrime p hp := by
      have hinv_eq : q⁻¹ = ((↑u⁻¹ : RatLocalAtPrime p hp) : ℚ) :=
        inv_eq_of_mul_eq_one_right hmul1
      rw [hinv_eq]
      exact (↑u⁻¹ : RatLocalAtPrime p hp).2
    have hndvd_den : ¬ (p ∣ q.den) := (mem_ratLocalAtPrime_iff hp q).mp hq_mem
    refine ⟨q.num, q.den, ?_, fun h => hndvd_den (Int.natCast_dvd_natCast.mp h),
      (Rat.num_div_den q).symm⟩
    intro hp_num
    obtain ⟨r', s', hs', hinv⟩ := hqinv_mem
    have hs'0 : (s' : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h0 => hs' (h0 ▸ dvd_zero (p : ℤ)))
    have hnum0 : (q.num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hx_ne0)
    have hinv_frac : q⁻¹ = (q.den : ℚ) / (q.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den q, inv_div]
    have hcross_q : (q.den : ℚ) * (s' : ℚ) = (r' : ℚ) * (q.num : ℚ) :=
      (div_eq_div_iff hnum0 hs'0).mp (hinv_frac.symm.trans hinv)
    have hcross : (q.den : ℤ) * s' = r' * q.num := by exact_mod_cast hcross_q
    have hdvd_lhs : (p : ℤ) ∣ (q.den : ℤ) * s' := by
      rw [hcross]
      exact dvd_mul_of_dvd_right hp_num r'
    rcases natPrime_int_dvd_or_dvd hp hdvd_lhs with hden | hs_bad
    · exact hndvd_den (Int.natCast_dvd_natCast.mp hden)
    · exact hs' hs_bad
  · rintro ⟨r, s, hr, hs, hx⟩
    have hr0 : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h0 => hr (h0 ▸ dvd_zero (p : ℤ)))
    have hs0 : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h0 => hs (h0 ▸ dvd_zero (p : ℤ)))
    let y : RatLocalAtPrime p hp := ⟨(s : ℚ) / (r : ℚ), ⟨s, r, hr, rfl⟩⟩
    refine .of_mul_eq_one y ?_
    apply Subtype.ext
    change (x : ℚ) * ((s : ℚ) / (r : ℚ)) = 1
    rw [hx, div_mul_div_cancel₀ hs0, div_self hr0]

theorem ratLocalAtPrime_eq_pow_mul_unit {p : ℕ} (hp : Nat.Prime p)
    {x : RatLocalAtPrime p hp} (hx0 : x ≠ 0) :
    ∃ (k : ℕ) (u : RatLocalAtPrime p hp),
      IsUnit u ∧ x = (p : RatLocalAtPrime p hp) ^ k * u := by
  let q : ℚ := x
  have hq0 : q ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0)
  obtain ⟨k, m, hm_ndvd, hnum_eq⟩ := nat_exists_eq_pow_mul_not_dvd hp.one_lt q.num.natAbs hnum0
  let r' : ℤ := if 0 ≤ q.num then (m : ℤ) else -(m : ℤ)
  have hsign : q.num = (p : ℤ) ^ k * r' := by
    have habs : (q.num.natAbs : ℤ) = (p : ℤ) ^ k * (m : ℤ) := by exact_mod_cast hnum_eq
    dsimp only [r']
    split_ifs with hnn
    · rw [← habs, Int.natAbs_of_nonneg hnn]
    · have hneg : q.num = -(q.num.natAbs : ℤ) := by omega
      rw [hneg, habs, mul_neg]
  have hr'_ndvd : ¬ ((p : ℤ) ∣ r') := by
    dsimp only [r']
    split_ifs with hnn
    · exact fun h => hm_ndvd (Int.natCast_dvd_natCast.mp h)
    · exact fun h => hm_ndvd (Int.natCast_dvd_natCast.mp (dvd_neg.mp h))
  have hs_ndvd : ¬ ((p : ℤ) ∣ (q.den : ℤ)) := fun h =>
    ((mem_ratLocalAtPrime_iff hp q).mp x.2) (Int.natCast_dvd_natCast.mp h)
  let u : RatLocalAtPrime p hp := ⟨(r' : ℚ) / (q.den : ℚ), ⟨r', q.den, hs_ndvd, rfl⟩⟩
  have hu : IsUnit u := (ratLocalAtPrime_isUnit_iff hp u).mpr ⟨r', q.den, hr'_ndvd, hs_ndvd, rfl⟩
  refine ⟨k, u, hu, ?_⟩
  apply Subtype.ext
  change q = (p : ℚ) ^ k * ((r' : ℚ) / (q.den : ℚ))
  conv_lhs => rw [← Rat.num_div_den q]
  have hnum_cast : (q.num : ℚ) = (p : ℚ) ^ k * (r' : ℚ) := by exact_mod_cast hsign
  rw [hnum_cast, mul_div_assoc]

theorem ratLocalAtPrime_pow_mul_unit_unique {p : ℕ} (hp : Nat.Prime p)
    {k₁ k₂ : ℕ} {u₁ u₂ : RatLocalAtPrime p hp} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂)
    (heq : (p : RatLocalAtPrime p hp) ^ k₁ * u₁ = (p : RatLocalAtPrime p hp) ^ k₂ * u₂) :
    k₁ = k₂ ∧ u₁ = u₂ := by
  have hp_not_unit : ¬ IsUnit (p : RatLocalAtPrime p hp) := by
    rw [ratLocalAtPrime_isUnit_iff]
    rintro ⟨r, s, hr, hs, hpeq⟩
    have hs0 : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h0 => hs (h0 ▸ dvd_zero (p : ℤ)))
    have hq : (p : ℚ) * (s : ℚ) = (r : ℚ) := (eq_div_iff hs0).mp hpeq
    have hz : (p : ℤ) * s = r := by exact_mod_cast hq
    exact hr ⟨s, hz.symm⟩
  have hk_eq : k₁ = k₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨d, hd_pos, rfl⟩ : ∃ d, 0 < d ∧ k₂ = k₁ + d := ⟨k₂ - k₁, by omega, by omega⟩
      have hp0 : (p : RatLocalAtPrime p hp) ^ k₁ ≠ 0 := by
        intro h0
        have hq0 : ((p : ℚ) ^ k₁) = 0 := congrArg Subtype.val h0
        exact pow_ne_zero k₁ (Nat.cast_ne_zero.mpr hp.ne_zero) hq0
      have hcancel : u₁ = (p : RatLocalAtPrime p hp) ^ d * u₂ := by
        apply mul_left_cancel₀ hp0
        rw [heq, pow_add, mul_assoc]
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hdvd_u₁ : (p : RatLocalAtPrime p hp) ∣ u₁ :=
        ⟨(p : RatLocalAtPrime p hp) ^ d' * u₂, by rw [hcancel, pow_succ', mul_assoc]⟩
      exact hp_not_unit (isUnit_of_dvd_unit hdvd_u₁ hu₁)
    · obtain ⟨d, hd_pos, rfl⟩ : ∃ d, 0 < d ∧ k₁ = k₂ + d := ⟨k₁ - k₂, by omega, by omega⟩
      have hp0 : (p : RatLocalAtPrime p hp) ^ k₂ ≠ 0 := by
        intro h0
        have hq0 : ((p : ℚ) ^ k₂) = 0 := congrArg Subtype.val h0
        exact pow_ne_zero k₂ (Nat.cast_ne_zero.mpr hp.ne_zero) hq0
      have hcancel : (p : RatLocalAtPrime p hp) ^ d * u₁ = u₂ := by
        apply mul_left_cancel₀ hp0
        rw [← mul_assoc, ← pow_add, heq]
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hdvd_u₂ : (p : RatLocalAtPrime p hp) ∣ u₂ :=
        ⟨(p : RatLocalAtPrime p hp) ^ d' * u₁, by rw [← hcancel, pow_succ', mul_assoc]⟩
      exact hp_not_unit (isUnit_of_dvd_unit hdvd_u₂ hu₂)
  subst hk_eq
  have hp0 : (p : RatLocalAtPrime p hp) ^ k₁ ≠ 0 := by
    intro h0
    have hq0 : ((p : ℚ) ^ k₁) = 0 := congrArg Subtype.val h0
    exact pow_ne_zero k₁ (Nat.cast_ne_zero.mpr hp.ne_zero) hq0
  exact ⟨rfl, mul_left_cancel₀ hp0 heq⟩

/-- Every non-zero ideal of `RatLocalAtPrime p hp` is of the form `(p^k)` for a unique `k : ℕ`,
hence `RatLocalAtPrime p hp` is a principal ideal domain (§3.5, Ex. 3.17, p. 29). -/
theorem ratLocalAtPrime_ideal_eq_span_pow {p : ℕ} (hp : Nat.Prime p)
    {I : Ideal (RatLocalAtPrime p hp)} (hI : I ≠ ⊥) :
    ∃! k : ℕ, I = Ideal.span {(p : RatLocalAtPrime p hp) ^ k} := by
  classical
  have hex_mem : ∃ k : ℕ, (p : RatLocalAtPrime p hp) ^ k ∈ I := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨k, u, hu, rfl⟩ := ratLocalAtPrime_eq_pow_mul_unit hp hx0
    obtain ⟨u', rfl⟩ := hu
    refine ⟨k, ?_⟩
    have := I.mul_mem_right (↑u'⁻¹ : RatLocalAtPrime p hp) hxI
    simpa [mul_assoc] using this
  let k₀ := Nat.find hex_mem
  have hk₀_mem : (p : RatLocalAtPrime p hp) ^ k₀ ∈ I := Nat.find_spec hex_mem
  have hI_eq : I = Ideal.span {(p : RatLocalAtPrime p hp) ^ k₀} := by
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · subst hx0; exact Submodule.zero_mem _
      · obtain ⟨k, u, hu, rfl⟩ := ratLocalAtPrime_eq_pow_mul_unit hp hx0
        obtain ⟨u', rfl⟩ := hu
        have hpk_mem : (p : RatLocalAtPrime p hp) ^ k ∈ I := by
          have := I.mul_mem_right (↑u'⁻¹ : RatLocalAtPrime p hp) hxI
          simpa [mul_assoc] using this
        have hk_ge : k₀ ≤ k := Nat.find_min' hex_mem hpk_mem
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk_ge
        rw [Ideal.mem_span_singleton]
        exact ⟨(p : RatLocalAtPrime p hp) ^ d * u', by rw [pow_add, mul_assoc]⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hk₀_mem
  refine ⟨k₀, hI_eq, fun k hk => ?_⟩
  have hass : Associated ((p : RatLocalAtPrime p hp) ^ k) ((p : RatLocalAtPrime p hp) ^ k₀) :=
    Ideal.span_singleton_eq_span_singleton.mp (hk.symm.trans hI_eq)
  rcases hass with ⟨u, hu⟩
  exact (ratLocalAtPrime_pow_mul_unit_unique hp u.isUnit isUnit_one (by simpa using hu)).1

instance ratLocalAtPrime_isPrincipalIdealRing (p : ℕ) (hp : Nat.Prime p) :
    IsPrincipalIdealRing (RatLocalAtPrime p hp) where
  principal I := by
    by_cases hI : I = ⊥
    · subst hI; exact ⟨⟨0, by simp⟩⟩
    · obtain ⟨k, hk, _⟩ := ratLocalAtPrime_ideal_eq_span_pow hp hI
      exact ⟨⟨(p : RatLocalAtPrime p hp) ^ k, hk⟩⟩

/-- **Exercise 3.17** (§3.5, p. 29): For any prime `p`, `R = RatLocalAtPrime p hp` is a subring of
`ℚ`, its units are `{r / s ∈ ℚ : p ∤ r ∧ p ∤ s}`, every non-zero element has the unique form
`p^k * u` (`k ∈ ℕ`, `u` a unit), every non-zero ideal has the unique form `(p^k)`, and `R` is a
principal ideal domain. -/
theorem exercise_3_17 (p : ℕ) (hp : Nat.Prime p) :
    (∀ x : RatLocalAtPrime p hp,
      IsUnit x ↔ ∃ r s : ℤ, ¬ ((p : ℤ) ∣ r) ∧ ¬ ((p : ℤ) ∣ s) ∧ (x : ℚ) = (r : ℚ) / (s : ℚ)) ∧
    (∀ x : RatLocalAtPrime p hp, x ≠ 0 →
      ∃ (k : ℕ) (u : RatLocalAtPrime p hp),
        IsUnit u ∧ x = (p : RatLocalAtPrime p hp) ^ k * u) ∧
    (∀ I : Ideal (RatLocalAtPrime p hp), I ≠ ⊥ →
      ∃! k : ℕ, I = Ideal.span {(p : RatLocalAtPrime p hp) ^ k}) ∧
    IsGarlingPID (RatLocalAtPrime p hp) :=
  ⟨ratLocalAtPrime_isUnit_iff hp,
    fun _ hx0 => ratLocalAtPrime_eq_pow_mul_unit hp hx0,
    fun _ hI => ratLocalAtPrime_ideal_eq_span_pow hp hI,
    (isGarlingPID_iff (RatLocalAtPrime p hp)).mpr ⟨inferInstance, inferInstance⟩⟩

/-- **Exercise 3.18** (§3.5, p. 29): Suppose that `R` is a principal ideal domain which is not a
field. Then `R[x]` is not a principal ideal domain. -/
theorem exercise_3_18 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (hnf : ¬ IsField R) :
    ¬ IsPrincipalIdealRing R[X] ∧ ¬ IsGarlingPID R[X] := by
  have hnpir : ¬ IsPrincipalIdealRing R[X] := by
    intro hpir
    have hex_nonunit : ∃ a : R, a ≠ 0 ∧ ¬ IsUnit a := by
      by_contra hall
      apply hnf
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha0 => ?_⟩
      have hau : IsUnit a := by
        by_contra hnu
        exact hall ⟨a, ha0, hnu⟩
      exact isUnit_iff_exists_inv.mp hau
    obtain ⟨a, ha0, hau⟩ := hex_nonunit
    let I : Ideal R[X] := Ideal.span {Polynomial.C a, Polynomial.X}
    obtain ⟨g, hg0_span⟩ := (hpir.principal I).principal
    have hg : I = Ideal.span {g} := hg0_span
    have ha_mem : Polynomial.C a ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    have hx_mem : (Polynomial.X : R[X]) ∈ Ideal.span {g} := hg ▸ Ideal.subset_span (by simp)
    rw [Ideal.mem_span_singleton] at ha_mem hx_mem
    have hCa0 : (Polynomial.C a : R[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ha0
    have hg_deg : g.natDegree = 0 := by
      have hle := Polynomial.natDegree_le_of_dvd ha_mem hCa0
      simpa using hle
    rw [Polynomial.eq_C_of_natDegree_eq_zero hg_deg] at ha_mem hx_mem hg
    rcases hx_mem with ⟨q, hq⟩
    have hcoeff1 : (1 : R) = g.coeff 0 * q.coeff 1 := by
      have := congrArg (fun p : R[X] => p.coeff 1) hq
      simpa using this
    have hgu : IsUnit (Polynomial.C (g.coeff 0) : R[X]) :=
      (IsUnit.of_mul_eq_one (q.coeff 1) hcoeff1.symm).map Polynomial.C
    have hItop : I = ⊤ := by
      rw [hg, Ideal.span_singleton_eq_top]
      exact hgu
    have h1mem : (1 : R[X]) ∈ I := hItop ▸ Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1mem
    obtain ⟨u, v, huv⟩ := h1mem
    have hev0 := congrArg (Polynomial.eval 0) huv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_zero, add_zero, Polynomial.eval_one] at hev0
    exact hau (.of_mul_eq_one (u.eval 0) (by rw [mul_comm, hev0]))
  exact ⟨hnpir, fun hpid => hnpir ((isGarlingPID_iff R[X]).mp hpid).2⟩

/-! ## §3.6 Highest common factors (printed pp. 29–31, PDF pp. 37–39) -/

/-- Garling's definition of a *highest common factor* (`a`) of a subset `B` of a ring `R`
(§3.6, p. 29): `a ∣ b` for each `b ∈ B`, and whenever `a' ∣ b` for each `b ∈ B`, `a' ∣ a`. -/
def IsGarlingHCF {R : Type*} [CommRing R] (B : Set R) (a : R) : Prop :=
  (∀ b ∈ B, a ∣ b) ∧ (∀ a' : R, (∀ b ∈ B, a' ∣ b) → a' ∣ a)

/-- Ideal formulation of `IsGarlingHCF` (§3.6, p. 29): `B ⊆ (a)` and whenever `B ⊆ (a')`,
`(a) ⊆ (a')`. -/
theorem isGarlingHCF_iff_ideal_span {R : Type*} [CommRing R] (B : Set R) (a : R) :
    IsGarlingHCF B a ↔
      (B ⊆ (Ideal.span {a} : Set R)) ∧
      (∀ a' : R, B ⊆ (Ideal.span {a'} : Set R) → Ideal.span {a} ≤ Ideal.span {a'}) := by
  constructor
  · rintro ⟨hdvd, hmax⟩
    refine ⟨fun b hb => Ideal.mem_span_singleton.mpr (hdvd b hb), fun a' hsub => ?_⟩
    rw [Ideal.span_singleton_le_span_singleton]
    exact hmax a' (fun b hb => Ideal.mem_span_singleton.mp (hsub hb))
  · rintro ⟨hsub, hmax⟩
    refine ⟨fun b hb => Ideal.mem_span_singleton.mp (hsub hb), fun a' hdvd => ?_⟩
    rw [← Ideal.span_singleton_le_span_singleton]
    exact hmax a' (fun b hb => Ideal.mem_span_singleton.mpr (hdvd b hb))

/-- Two highest common factors of the same subset `B` generate the same principal ideal, and in an
integral domain are associates (§3.6, p. 30). -/
theorem isGarlingHCF_associated {R : Type*} [CommRing R] [IsDomain R]
    {B : Set R} {a a' : R} (ha : IsGarlingHCF B a) (ha' : IsGarlingHCF B a') :
    Ideal.span {a} = Ideal.span {a'} ∧ Associated a a' := by
  have hspan : Ideal.span {a} = Ideal.span {a'} :=
    le_antisymm
      (((isGarlingHCF_iff_ideal_span B a).mp ha).2 a' ((isGarlingHCF_iff_ideal_span B a').mp ha').1)
      (((isGarlingHCF_iff_ideal_span B a').mp ha').2 a ((isGarlingHCF_iff_ideal_span B a).mp ha).1)
  exact ⟨hspan, Ideal.span_singleton_eq_span_singleton.mp hspan⟩

theorem isGarlingHCF_of_associated {R : Type*} [CommRing R] {B : Set R} {a a' : R}
    (ha : IsGarlingHCF B a) (hass : Associated a a') :
    IsGarlingHCF B a' := by
  refine ⟨fun b hb => hass.symm.dvd.trans (ha.1 b hb),
    fun c hc => (ha.2 c hc).trans hass.dvd⟩

/-- In a principal ideal domain `R`, every non-empty subset `B` has a highest common factor `a`
with `(B) = (a)`, expressible as a finite `R`-linear combination `r₁ b₁ + ⋯ + r_n b_n` of elements
of `B` (§3.6, p. 30). -/
theorem pid_exists_hcf_linear_combination {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {B : Set R} (hB : B.Nonempty) :
    ∃ a : R, Ideal.span B = Ideal.span {a} ∧ IsGarlingHCF B a ∧
      ∃ (n : ℕ) (b : Fin n → R) (r : Fin n → R),
        (∀ i, b i ∈ B) ∧ a = ∑ i, r i * b i := by
  obtain ⟨a, ha_span⟩ := (IsPrincipalIdealRing.principal (Ideal.span B)).principal
  have hspan : Ideal.span B = Ideal.span {a} := ha_span
  have hhcf : IsGarlingHCF B a := by
    rw [isGarlingHCF_iff_ideal_span]
    refine ⟨fun b hb => hspan ▸ Ideal.subset_span hb, fun a' hsub => ?_⟩
    rw [← hspan, Ideal.span_le]
    exact hsub
  have ha_mem : a ∈ Ideal.span B := hspan ▸ Ideal.subset_span (Set.mem_singleton a)
  obtain ⟨b₀, hb₀⟩ := hB
  have hlin : ∀ x ∈ Ideal.span B,
      ∃ (n : ℕ) (b : Fin n → R) (r : Fin n → R),
        (∀ i, b i ∈ B) ∧ x = ∑ i, r i * b i := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact ⟨1, fun _ => y, fun _ => 1, fun _ => hy, by simp⟩
    · exact ⟨1, fun _ => b₀, fun _ => 0, fun _ => hb₀, by simp⟩
    · rintro y z _ _ ⟨n₁, b₁, r₁, hb₁, rfl⟩ ⟨n₂, b₂, r₂, hb₂, rfl⟩
      refine ⟨n₁ + n₂, Fin.append b₁ b₂, Fin.append r₁ r₂, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
        · simpa [Fin.append_left] using hb₁ i₁
        · simpa [Fin.append_right] using hb₂ i₂
      · rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
    · rintro s y _ ⟨n, b, r, hb, rfl⟩
      refine ⟨n, b, fun i => s * r i, hb, ?_⟩
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  obtain ⟨n, b, r, hb, ha_eq⟩ := hlin a ha_mem
  exact ⟨a, hspan, hhcf, n, b, r, hb, ha_eq⟩

/-- **Theorem 3.10** (§3.6, p. 30, Mathlib `UniqueFactorizationMonoid` version): If `B` is a
non-empty set of non-zero elements of a unique factorization domain `R`, then `B` has a highest
common factor. -/
theorem theorem_3_10_ufm {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {B : Set R} (hBne : B.Nonempty) (hB0 : ∀ b ∈ B, b ≠ 0) :
    ∃ a : R, IsGarlingHCF B a := by
  classical
  have hUFD : IsGarlingUFD R := (isGarlingUFD_iff_uniqueFactorizationMonoid R).mpr inferInstance
  let _ : GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R
  obtain ⟨b₀, hb₀⟩ := hBne
  have hb₀0 : b₀ ≠ 0 := hB0 b₀ hb₀
  let D : Set R := {r : R | ∀ b ∈ B, r ∣ b}
  have h1D : (1 : R) ∈ D := fun _ _ => one_dvd _
  have hdvd_ne0 : ∀ r ∈ D, r ≠ 0 := by
    intro r hr h0
    obtain ⟨q, hq⟩ := hr b₀ hb₀
    exact hb₀0 (by rw [hq, h0, zero_mul])
  have hdvd_len : ∀ r (hr : r ∈ D),
      ufdLength hUFD r (hdvd_ne0 r hr) ≤ ufdLength hUFD b₀ hb₀0 := by
    intro r hr
    obtain ⟨q, hq⟩ := hr b₀ hb₀
    have hr0 : r ≠ 0 := hdvd_ne0 r hr
    have hq0 : q ≠ 0 := fun h0 => hb₀0 (by rw [hq, h0, mul_zero])
    have hlen := ufdLength_mul hUFD hr0 hq0
    have hcongr : ufdLength hUFD b₀ hb₀0 = ufdLength hUFD (r * q) (mul_ne_zero hr0 hq0) := by
      simp only [hq]
    omega
  let L : Finset ℕ :=
    (Finset.range (ufdLength hUFD b₀ hb₀0 + 1)).filter
      (fun k => ∃ r, ∃ hr : r ∈ D, ufdLength hUFD r (hdvd_ne0 r hr) = k)
  have h0L : 0 ∈ L := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), 1, h1D, ?_⟩
    exact (ufdLength_eq_zero_iff hUFD (hdvd_ne0 1 h1D)).mpr isUnit_one
  let k_max : ℕ := L.max' ⟨0, h0L⟩
  have hk_mem : k_max ∈ L := Finset.max'_mem L ⟨0, h0L⟩
  obtain ⟨_, a, haD, ha_len⟩ := Finset.mem_filter.mp hk_mem
  have ha_max : ∀ r (hr : r ∈ D),
      ufdLength hUFD r (hdvd_ne0 r hr) ≤ ufdLength hUFD a (hdvd_ne0 a haD) := by
    intro r hr
    have hle := hdvd_len r hr
    have hrL : ufdLength hUFD r (hdvd_ne0 r hr) ∈ L :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), r, hr, rfl⟩
    rw [ha_len]
    exact Finset.le_max' L _ hrL
  refine ⟨a, haD, fun a' ha'D => ?_⟩
  let m : R := lcm a' a
  have hmD : m ∈ D := fun b hb => lcm_dvd (ha'D b hb) (haD b hb)
  have hm0 : m ≠ 0 := hdvd_ne0 m hmD
  have ha_dvd_m : a ∣ m := dvd_lcm_right a' a
  obtain ⟨d, hdm⟩ := ha_dvd_m
  have ha0 : a ≠ 0 := hdvd_ne0 a haD
  have hd0 : d ≠ 0 := fun h0 => hm0 (by rw [hdm, h0, mul_zero])
  have hmlen : ufdLength hUFD m hm0 = ufdLength hUFD a ha0 + ufdLength hUFD d hd0 := by
    have h1 := ufdLength_mul hUFD ha0 hd0
    have hcongr : ufdLength hUFD m hm0 = ufdLength hUFD (a * d) (mul_ne_zero ha0 hd0) := by
      simp only [hdm]
    omega
  have hm_le : ufdLength hUFD m hm0 ≤ ufdLength hUFD a ha0 := ha_max m hmD
  have hd_len0 : ufdLength hUFD d hd0 = 0 := by omega
  have hdu : IsUnit d := (ufdLength_eq_zero_iff hUFD hd0).mp hd_len0
  have hm_dvd_a : m ∣ a := by
    refine ⟨↑hdu.unit⁻¹, ?_⟩
    rw [hdm, mul_assoc]
    simp
  exact (dvd_lcm_left a' a).trans hm_dvd_a

/-- **Theorem 3.10** (§3.6, p. 30, Garling `IsGarlingUFD` version): If `B` is a non-empty set of
non-zero elements of a unique factorization domain `R`, then `B` has a highest common factor. -/
theorem theorem_3_10 {R : Type*} [CommRing R] (hufd : IsGarlingUFD R)
    {B : Set R} (hBne : B.Nonempty) (hB0 : ∀ b ∈ B, b ≠ 0) :
    ∃ a : R, IsGarlingHCF B a := by
  have _ : IsDomain R := hufd.isDomain
  have _ : UniqueFactorizationMonoid R :=
    (isGarlingUFD_iff_uniqueFactorizationMonoid R).mp hufd
  exact theorem_3_10_ufm hBne hB0

/-- Garling's definition of a *relatively prime* subset `B` of a ring `R` (§3.6, p. 30): `B` is
non-empty and `1` is a highest common factor of `B`. -/
def IsGarlingRelativelyPrime {R : Type*} [CommRing R] (B : Set R) : Prop :=
  B.Nonempty ∧ IsGarlingHCF B 1

/-- Prose proposition (§3.6, p. 30): If `a` is a highest common factor of a non-empty subset `B` of
an integral domain `R`, then `{c : c * a ∈ B}` is relatively prime. -/
theorem relativelyPrime_div_hcf {R : Type*} [CommRing R] [IsDomain R]
    {B : Set R} (hB : B.Nonempty) {a : R} (ha : IsGarlingHCF B a) :
    IsGarlingRelativelyPrime {c : R | c * a ∈ B} := by
  obtain ⟨b₀, hb₀⟩ := hB
  obtain ⟨c₀, hc₀⟩ := ha.1 b₀ hb₀
  have hc₀_mem : c₀ ∈ {c : R | c * a ∈ B} := by
    change c₀ * a ∈ B
    rwa [mul_comm, ← hc₀]
  refine ⟨⟨c₀, hc₀_mem⟩, ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩⟩
  by_cases ha0 : a = 0
  · subst ha0
    have h0B : (0 : R) ∈ B := by simpa using hc₀_mem
    have h1_mem : (1 : R) ∈ {c : R | c * 0 ∈ B} := by simpa using h0B
    exact hd 1 h1_mem
  · have hda_common : ∀ b ∈ B, d * a ∣ b := by
      intro b hb
      obtain ⟨c, rfl⟩ := ha.1 b hb
      have hc_mem : c ∈ {x : R | x * a ∈ B} := by
        change c * a ∈ B
        rwa [mul_comm]
      obtain ⟨q, rfl⟩ := hd c hc_mem
      exact ⟨q, by ring⟩
    obtain ⟨u, hu⟩ := ha.2 (d * a) hda_common
    refine ⟨u, ?_⟩
    apply mul_left_cancel₀ ha0
    linear_combination hu

/-- Garling's definition of a *least common multiple* (`m`) of a subset `B` of a ring `R`
(§3.6, Ex. 3.19, pp. 30–31): `b ∣ m` for each `b ∈ B`, and whenever `b ∣ m'` for each `b ∈ B`,
`m ∣ m'`. -/
def IsGarlingLCM {R : Type*} [CommRing R] (B : Set R) (m : R) : Prop :=
  (∀ b ∈ B, b ∣ m) ∧ (∀ m' : R, (∀ b ∈ B, b ∣ m') → m ∣ m')

/-- **Exercise 3.19** (§3.6, pp. 30–31): In an integral domain `R`, the following are equivalent:
(i) every finite non-empty set of non-zero elements of `R` has a highest common factor;
(ii) every finite non-empty set of non-zero elements of `R` has a least common multiple. -/
theorem exercise_3_19 (R : Type*) [CommRing R] [IsDomain R] :
    (∀ S : Finset R, S.Nonempty → (∀ b ∈ S, b ≠ 0) → ∃ d : R, IsGarlingHCF (S : Set R) d) ↔
    (∀ S : Finset R, S.Nonempty → (∀ b ∈ S, b ≠ 0) → ∃ m : R, IsGarlingLCM (S : Set R) m) := by
  classical
  have pair_hcf_to_finset :
      (∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d : R, IsGarlingHCF ({a, b} : Set R) d) →
      (∀ S : Finset R, S.Nonempty → (∀ b ∈ S, b ≠ 0) → ∃ d : R, IsGarlingHCF (S : Set R) d) := by
    intro hpair S
    refine Finset.induction_on S ?_ (fun x T _ ih => ?_)
    · intro hne
      exact False.elim (Finset.not_nonempty_empty hne)
    · intro _ h0
      have hx0 : x ≠ 0 := h0 x (Finset.mem_insert_self x T)
      by_cases hT : T.Nonempty
      · obtain ⟨dT, hdT⟩ := ih hT (fun b hb => h0 b (Finset.mem_insert_of_mem hb))
        obtain ⟨t₀, ht₀⟩ := hT
        have hdT0 : dT ≠ 0 := by
          intro hz
          obtain ⟨q, hq⟩ := hdT.1 t₀ ht₀
          exact h0 t₀ (Finset.mem_insert_of_mem ht₀) (by rw [hq, hz, zero_mul])
        obtain ⟨d, hd⟩ := hpair x dT hx0 hdT0
        refine ⟨d, fun b hb => ?_, fun c hc => ?_⟩
        · rcases Finset.mem_insert.mp hb with hbx | hbT
          · rw [hbx]; exact hd.1 x (by simp)
          · exact (hd.1 dT (by simp)).trans (hdT.1 b hbT)
        · apply hd.2 c
          intro y hy
          rcases hy with hyx | hydT
          · rw [hyx]; exact hc x (Finset.mem_insert_self x T)
          · rw [hydT]; exact hdT.2 c (fun b hbT => hc b (Finset.mem_insert_of_mem hbT))
      · have hTeq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        subst hTeq
        refine ⟨x, ?_, ?_⟩
        · intro b hb
          simp only [Finset.insert_empty, Finset.coe_singleton, Set.mem_singleton_iff] at hb
          subst hb; exact dvd_rfl
        · intro c hc
          exact hc x (by simp)
  have pair_lcm_to_finset :
      (∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ m : R, IsGarlingLCM ({a, b} : Set R) m) →
      (∀ S : Finset R, S.Nonempty → (∀ b ∈ S, b ≠ 0) → ∃ m : R, IsGarlingLCM (S : Set R) m) := by
    intro hpair S
    refine Finset.induction_on S ?_ (fun x T _ ih => ?_)
    · intro hne
      exact False.elim (Finset.not_nonempty_empty hne)
    · intro _ h0
      have hx0 : x ≠ 0 := h0 x (Finset.mem_insert_self x T)
      by_cases hT : T.Nonempty
      · have hT0 : ∀ b ∈ T, b ≠ 0 := fun b hb => h0 b (Finset.mem_insert_of_mem hb)
        obtain ⟨mT, hmT⟩ := ih hT hT0
        have hprod0 : (∏ b ∈ T, b) ≠ 0 := Finset.prod_ne_zero_iff.mpr hT0
        have hmT_dvd_prod : mT ∣ ∏ b ∈ T, b :=
          hmT.2 (∏ b ∈ T, b) (fun b hb => Finset.dvd_prod_of_mem _ hb)
        have hmT0 : mT ≠ 0 := by
          intro hz
          rcases hmT_dvd_prod with ⟨q, hq⟩
          exact hprod0 (by rw [hq, hz, zero_mul])
        obtain ⟨m, hm⟩ := hpair x mT hx0 hmT0
        refine ⟨m, fun b hb => ?_, fun c hc => ?_⟩
        · rcases Finset.mem_insert.mp hb with hbx | hbT
          · rw [hbx]; exact hm.1 x (by simp)
          · exact (hmT.1 b hbT).trans (hm.1 mT (by simp))
        · apply hm.2 c
          intro y hy
          rcases hy with hyx | hymT
          · rw [hyx]; exact hc x (Finset.mem_insert_self x T)
          · rw [hymT]; exact hmT.2 c (fun b hbT => hc b (Finset.mem_insert_of_mem hbT))
      · have hTeq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        subst hTeq
        refine ⟨x, ?_, ?_⟩
        · intro b hb
          simp only [Finset.insert_empty, Finset.coe_singleton, Set.mem_singleton_iff] at hb
          subst hb; exact dvd_rfl
        · intro c hc
          exact hc x (by simp)
  constructor
  · intro hhcf
    have hpair_hcf : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d : R, IsGarlingHCF ({a, b} : Set R) d := by
      intro a b ha0 hb0
      let S : Finset R := {a, b}
      have hSne : S.Nonempty := ⟨a, by simp [S]⟩
      have hS0 : ∀ x ∈ S, x ≠ 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxb
        · exact ha0
        · rw [Finset.mem_singleton.mp hxb]; exact hb0
      obtain ⟨d, hd⟩ := hhcf S hSne hS0
      have hcoe : (S : Set R) = {a, b} := by simp [S]
      rw [hcoe] at hd
      exact ⟨d, hd⟩
    have hcf_mul_left : ∀ {x y k d : R}, x ≠ 0 → y ≠ 0 → k ≠ 0 →
        IsGarlingHCF ({x, y} : Set R) d → IsGarlingHCF ({k * x, k * y} : Set R) (k * d) := by
      intro x y k d hx0 hy0 hk0 hd
      obtain ⟨e, he⟩ := hpair_hcf (k * x) (k * y) (mul_ne_zero hk0 hx0) (mul_ne_zero hk0 hy0)
      have hk_dvd_e : k ∣ e := he.2 k (fun z hz => by
        rcases hz with rfl | rfl <;> exact dvd_mul_right k _)
      obtain ⟨d', rfl⟩ := hk_dvd_e
      have hd'_x : d' ∣ x := by
        obtain ⟨q, hq⟩ := he.1 (k * x) (by simp)
        exact ⟨q, mul_left_cancel₀ hk0 (by linear_combination hq)⟩
      have hd'_y : d' ∣ y := by
        obtain ⟨q, hq⟩ := he.1 (k * y) (by simp)
        exact ⟨q, mul_left_cancel₀ hk0 (by linear_combination hq)⟩
      have hd'_d : d' ∣ d := hd.2 d' (fun z hz => by
        rcases hz with rfl | rfl
        · exact hd'_x
        · exact hd'_y)
      have he_kd : k * d' ∣ k * d := mul_dvd_mul_left k hd'_d
      refine ⟨fun z hz => ?_, fun c hc => (he.2 c hc).trans he_kd⟩
      rcases hz with rfl | rfl
      · exact mul_dvd_mul_left k (hd.1 x (by simp))
      · exact mul_dvd_mul_left k (hd.1 y (by simp))
    refine pair_lcm_to_finset (fun a b ha0 hb0 => ?_)
    obtain ⟨d, hd⟩ := hpair_hcf a b ha0 hb0
    have hd0 : d ≠ 0 := by
      intro hz
      obtain ⟨q, hq⟩ := hd.1 a (by simp)
      exact ha0 (by rw [hq, hz, zero_mul])
    obtain ⟨a₁, ha₁⟩ := hd.1 a (by simp)
    obtain ⟨b₁, hb₁⟩ := hd.1 b (by simp)
    have ha₁0 : a₁ ≠ 0 := fun hz => ha0 (by rw [ha₁, hz, mul_zero])
    have hb₁0 : b₁ ≠ 0 := fun hz => hb0 (by rw [hb₁, hz, mul_zero])
    have hcoprime : IsGarlingHCF ({a₁, b₁} : Set R) 1 := by
      refine ⟨fun _ _ => one_dvd _, fun c hc => ?_⟩
      have hdc_a : d * c ∣ a := by
        obtain ⟨q, rfl⟩ := hc a₁ (by simp)
        exact ⟨q, by rw [ha₁]; ring⟩
      have hdc_b : d * c ∣ b := by
        obtain ⟨q, rfl⟩ := hc b₁ (by simp)
        exact ⟨q, by rw [hb₁]; ring⟩
      obtain ⟨u, hu⟩ := hd.2 (d * c) (fun z hz => by
        rcases hz with rfl | rfl
        · exact hdc_a
        · exact hdc_b)
      exact ⟨u, mul_left_cancel₀ hd0 (by linear_combination hu)⟩
    refine ⟨d * a₁ * b₁, fun z hz => ?_, fun c hc => ?_⟩
    · rcases hz with rfl | rfl
      · exact ⟨b₁, by rw [ha₁]⟩
      · exact ⟨a₁, by rw [hb₁]; ring⟩
    · by_cases hc0 : c = 0
      · subst hc0; exact dvd_zero _
      · have hc_hcf : IsGarlingHCF ({c * a₁, c * b₁} : Set R) c := by
          simpa using hcf_mul_left ha₁0 hb₁0 hc0 hcoprime
        apply hc_hcf.2 (d * a₁ * b₁)
        intro z hz
        rcases hz with rfl | rfl
        · obtain ⟨v, hv⟩ := hc b (by simp)
          exact ⟨v, by rw [hv, hb₁]; ring⟩
        · obtain ⟨u, hu⟩ := hc a (by simp)
          exact ⟨u, by rw [hu, ha₁]; ring⟩
  · intro hlcm
    have hpair_lcm : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ m : R, IsGarlingLCM ({a, b} : Set R) m := by
      intro a b ha0 hb0
      let S : Finset R := {a, b}
      have hSne : S.Nonempty := ⟨a, by simp [S]⟩
      have hS0 : ∀ x ∈ S, x ≠ 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxb
        · exact ha0
        · rw [Finset.mem_singleton.mp hxb]; exact hb0
      obtain ⟨m, hm⟩ := hlcm S hSne hS0
      have hcoe : (S : Set R) = {a, b} := by simp [S]
      rw [hcoe] at hm
      exact ⟨m, hm⟩
    refine pair_hcf_to_finset (fun a b ha0 hb0 => ?_)
    obtain ⟨m, hm⟩ := hpair_lcm a b ha0 hb0
    have hm_ab : m ∣ a * b := hm.2 (a * b) (fun z hz => by
      rcases hz with hza | hzb
      · rw [hza]; exact dvd_mul_right a b
      · rw [hzb]; exact dvd_mul_left b a)
    obtain ⟨d, hdm⟩ := hm_ab
    have hm0 : m ≠ 0 := fun hz => mul_ne_zero ha0 hb0 (by rw [hdm, hz, zero_mul])
    refine ⟨d, fun z hz => ?_, fun c hc => ?_⟩
    · rcases hz with hza | hzb
      · rw [hza]
        obtain ⟨q₁, hq₁⟩ := hm.1 b (by simp)
        refine ⟨q₁, mul_right_cancel₀ hb0 ?_⟩
        calc a * b = m * d := hdm
          _ = (b * q₁) * d := by rw [hq₁]
          _ = d * q₁ * b := by ring
      · rw [hzb]
        obtain ⟨q₂, hq₂⟩ := hm.1 a (by simp)
        refine ⟨q₂, mul_left_cancel₀ ha0 ?_⟩
        calc a * b = m * d := hdm
          _ = (a * q₂) * d := by rw [hq₂]
          _ = a * (d * q₂) := by ring
    · have hc0 : c ≠ 0 := by
        intro hz
        obtain ⟨q, hq⟩ := hc a (by simp)
        exact ha0 (by rw [hq, hz, zero_mul])
      obtain ⟨a', ha'⟩ := hc a (by simp)
      obtain ⟨b', hb'⟩ := hc b (by simp)
      have hm_dvd_n : m ∣ c * a' * b' := hm.2 (c * a' * b') (fun z hz => by
        rcases hz with hza | hzb
        · rw [hza]; exact ⟨b', by rw [ha']⟩
        · rw [hzb]; exact ⟨a', by rw [hb']; ring⟩)
      obtain ⟨k, hk⟩ := hm_dvd_n
      refine ⟨k, mul_left_cancel₀ hm0 ?_⟩
      calc m * d = a * b := hdm.symm
        _ = (c * a') * (c * b') := by rw [ha', hb']
        _ = c * (c * a' * b') := by ring
        _ = c * (m * k) := by rw [hk]
        _ = m * (c * k) := by ring

/-- **Exercise 3.20** (§3.6, p. 31): In `ℤ[x]`, `1` and `-1` are the highest common factors of
`2` and `x`, and neither can be written in the form `2a + xb` with `a, b ∈ ℤ[x]`. -/
theorem exercise_3_20 :
    ({d : ℤ[X] | IsGarlingHCF ({Polynomial.C (2 : ℤ), Polynomial.X} : Set ℤ[X]) d} = {1, -1}) ∧
    (∀ d : ℤ[X], IsGarlingHCF ({Polynomial.C (2 : ℤ), Polynomial.X} : Set ℤ[X]) d →
      ¬ ∃ a b : ℤ[X], d = Polynomial.C (2 : ℤ) * a + Polynomial.X * b) := by
  have hhcf1 : IsGarlingHCF ({Polynomial.C (2 : ℤ), Polynomial.X} : Set ℤ[X]) 1 := by
    refine ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩
    have hd2 : d ∣ Polynomial.C (2 : ℤ) := hd _ (by simp)
    have hdx : d ∣ (Polynomial.X : ℤ[X]) := hd _ (by simp)
    have h2ne : (Polynomial.C (2 : ℤ) : ℤ[X]) ≠ 0 := by simp
    have hd_deg : d.natDegree = 0 := by
      have hle := Polynomial.natDegree_le_of_dvd hd2 h2ne
      simpa using hle
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd_deg] at hdx ⊢
    rcases hdx with ⟨q, hq⟩
    have h1 : (1 : ℤ) = d.coeff 0 * q.coeff 1 := by
      have := congrArg (fun p : ℤ[X] => p.coeff 1) hq
      simpa using this
    exact ⟨Polynomial.C (q.coeff 1), by rw [← map_mul, ← h1, map_one]⟩
  have hset : {d : ℤ[X] | IsGarlingHCF ({Polynomial.C (2 : ℤ), Polynomial.X} : Set ℤ[X]) d} =
      {1, -1} := by
    ext d
    change IsGarlingHCF _ d ↔ d = 1 ∨ d = -1
    constructor
    · intro hd
      obtain ⟨_, hass⟩ := isGarlingHCF_associated hhcf1 hd
      rcases hass with ⟨u, hu⟩
      have hu_poly : IsUnit (u : ℤ[X]) := u.isUnit
      obtain ⟨c, hc_unit, hc_eq⟩ := Polynomial.isUnit_iff.mp hu_poly
      have hc_pm : c = 1 ∨ c = -1 := Int.isUnit_iff.mp hc_unit
      rcases hc_pm with rfl | rfl
      · left; simpa [← hc_eq] using hu.symm
      · right; simpa [← hc_eq] using hu.symm
    · rintro (rfl | rfl)
      · exact hhcf1
      · refine isGarlingHCF_of_associated hhcf1 ?_
        exact ⟨-1, by simp⟩
  refine ⟨hset, fun d hd ⟨a, b, hab⟩ => ?_⟩
  have hd_mem : d ∈ ({1, -1} : Set ℤ[X]) := hset ▸ hd
  have hev := congrArg (Polynomial.eval 0) hab
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, zero_mul, add_zero] at hev
  rcases hd_mem with rfl | rfl
  · simp only [Polynomial.eval_one] at hev; omega
  · simp only [Polynomial.eval_neg, Polynomial.eval_one] at hev; omega

/-- **Exercise 3.21** (§3.6, p. 31): Suppose that `R` is an integral domain in which every
non-empty set `B` of non-zero elements has a highest common factor of the form
`y₁ b₁ + ⋯ + y_n b_n` with `b_i ∈ B` and `y_i ∈ R`. Then `R` is a principal ideal domain. -/
theorem exercise_3_21 {R : Type*} [CommRing R] [IsDomain R]
    (hhcf_lin : ∀ B : Set R, B.Nonempty → (∀ b ∈ B, b ≠ 0) →
      ∃ (a : R) (n : ℕ) (b : Fin n → R) (y : Fin n → R),
        IsGarlingHCF B a ∧ (∀ i, b i ∈ B) ∧ a = ∑ i, y i * b i) :
    IsPrincipalIdealRing R ∧ IsGarlingPID R := by
  have hpir : IsPrincipalIdealRing R := ⟨fun I => by
    by_cases hI : I = ⊥
    · subst hI; exact ⟨⟨0, by simp⟩⟩
    · let B : Set R := {x : R | x ∈ I ∧ x ≠ 0}
      obtain ⟨x₀, hx₀I, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have hBne : B.Nonempty := ⟨x₀, hx₀I, hx₀0⟩
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun _ hb => hb.2
      obtain ⟨a, n, b, y, ha_hcf, hbB, ha_eq⟩ := hhcf_lin B hBne hB0
      have haI : a ∈ I := by
        rw [ha_eq]
        exact I.sum_mem (fun i _ => I.mul_mem_left (y i) (hbB i).1)
      refine ⟨⟨a, le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haI))⟩⟩
      intro x hxI
      by_cases hx0 : x = 0
      · subst hx0; exact Submodule.zero_mem _
      · exact Ideal.mem_span_singleton.mpr (ha_hcf.1 x ⟨hxI, hx0⟩)⟩
  exact ⟨hpir, (isGarlingPID_iff R).mpr ⟨inferInstance, hpir⟩⟩

/-! ## §3.7 Polynomials over unique factorization domains (printed pp. 31–34, PDF pp. 39–42) -/

/-- The set of non-zero coefficients of a polynomial `f ∈ R[x]` (§3.7, p. 31). -/
def coeffSet {R : Type*} [CommRing R] (f : R[X]) : Set R :=
  {a : R | ∃ n : ℕ, f.coeff n = a ∧ a ≠ 0}

/-- Garling's definition of *content* of a non-zero polynomial `f ∈ R[x]` (§3.7, p. 31): a highest
common factor of the set of non-zero coefficients of `f`. -/
def IsGarlingContent {R : Type*} [CommRing R] (f : R[X]) (c : R) : Prop :=
  f ≠ 0 ∧ IsGarlingHCF (coeffSet f) c

/-- Garling's definition of a *primitive* polynomial `f ∈ R[x]` (§3.7, p. 31): a non-zero polynomial
with content `1`. -/
def IsGarlingPrimitive {R : Type*} [CommRing R] (f : R[X]) : Prop :=
  IsGarlingContent f 1

/-- Bridge between Garling's `IsGarlingPrimitive` and Mathlib's `Polynomial.IsPrimitive` over any
integral domain `R`. -/
theorem isGarlingPrimitive_iff {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) :
    IsGarlingPrimitive f ↔ f.IsPrimitive := by
  constructor
  · rintro ⟨_, _, hmax⟩ r hr
    have hdvd : ∀ a ∈ coeffSet f, r ∣ a := by
      rintro a ⟨n, rfl, _⟩
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
      exact hr n
    exact isUnit_of_dvd_one (hmax r hdvd)
  · intro hf
    refine ⟨hf.ne_zero, fun _ _ => one_dvd _, fun r hr => ?_⟩
    have hCr : Polynomial.C r ∣ f := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      by_cases hn : f.coeff n = 0
      · rw [hn]; exact dvd_zero r
      · exact hr (f.coeff n) ⟨n, rfl, hn⟩
    exact (hf r hCr).dvd

/-- Over a UFD `R` equipped with `NormalizedGCDMonoid R`, `f.content` is a Garling content of every
non-zero `f ∈ R[x]`, and `f = C f.content * f.primPart` with `f.primPart` primitive (§3.7, p. 31). -/
theorem isGarlingContent_content {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {f : R[X]} (hf : f ≠ 0) :
    IsGarlingContent f f.content ∧
    f = Polynomial.C f.content * f.primPart ∧
    IsGarlingPrimitive f.primPart := by
  refine ⟨⟨hf, ?_, ?_⟩, f.eq_C_content_mul_primPart,
    (isGarlingPrimitive_iff f.primPart).mpr f.isPrimitive_primPart⟩
  · rintro a ⟨n, rfl, _⟩
    exact Polynomial.content_dvd_coeff n
  · intro c hc
    rw [Polynomial.dvd_content_iff_C_dvd, Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    by_cases hn : f.coeff n = 0
    · rw [hn]; exact dvd_zero c
    · exact hc (f.coeff n) ⟨n, rfl, hn⟩

/-- **Theorem 3.11** (§3.7, pp. 31–32): Suppose that `R` is a unique factorization domain with
field of fractions `F`.
(1) An element of `R[x]` is a unit if and only if it is a constant unit in `R`.
(2) Every non-zero `f ∈ F[x]` can be written as `f = C β * g.map (algebraMap R F)` with `β ∈ F`
(`β ≠ 0`) and `g ∈ R[x]` primitive.
(3) If `f = C β' * g'.map (algebraMap R F)` is another such expression (`g'` primitive), then `g`
and `g'` are associates in `R[x]`, with `g = C ε * g'` for a unit `ε ∈ R`. -/
theorem theorem_3_11 {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    (∀ g : R[X], IsUnit g ↔ ∃ u : R, IsUnit u ∧ g = Polynomial.C u) ∧
    (∀ f : F[X], f ≠ 0 →
      ∃ (β : F) (g : R[X]), β ≠ 0 ∧ IsGarlingPrimitive g ∧
        f = Polynomial.C β * g.map (algebraMap R F)) ∧
    (∀ (f : F[X]) (β β' : F) (g g' : R[X]),
      f ≠ 0 →
      IsGarlingPrimitive g → IsGarlingPrimitive g' →
      f = Polynomial.C β * g.map (algebraMap R F) →
      f = Polynomial.C β' * g'.map (algebraMap R F) →
      Associated g g' ∧ ∃ ε : R, IsUnit ε ∧ g = Polynomial.C ε * g') := by
  classical
  let _ : NormalizedGCDMonoid R := Classical.arbitrary (NormalizedGCDMonoid R)
  refine ⟨fun g => ?_, fun f hf0 => ?_, fun f β β' g g' hf0 hg hg' hf1 hf2 => ?_⟩
  · rw [Polynomial.isUnit_iff]
    constructor
    · rintro ⟨u, hu, hgu⟩
      exact ⟨u, hu, hgu.symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  · let h : R[X] := IsLocalization.integerNormalization R⁰ f
    obtain ⟨b, hb_mem, hb_eq⟩ := IsLocalization.integerNormalization_spec R⁰ f
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb_mem
    have hbF0 : algebraMap R F (b : R) ≠ 0 :=
      (IsFractionRing.injective R F).ne_iff' (map_zero _) |>.mpr hb0
    have hb_mul : h.map (algebraMap R F) = Polynomial.C (algebraMap R F (b : R)) * f := by
      rw [hb_eq, Algebra.smul_def, Polynomial.algebraMap_apply]
    have hh0 : h ≠ 0 := by
      intro hz
      rw [hz, Polynomial.map_zero] at hb_mul
      rcases mul_eq_zero.mp hb_mul.symm with hc0 | hfz
      · exact hbF0 (Polynomial.C_eq_zero.mp hc0)
      · exact hf0 hfz
    have hcont0 : h.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hh0
    have hcontF0 : algebraMap R F h.content ≠ 0 :=
      (IsFractionRing.injective R F).ne_iff' (map_zero _) |>.mpr hcont0
    let β : F := (algebraMap R F (b : R))⁻¹ * algebraMap R F h.content
    have hβ0 : β ≠ 0 := mul_ne_zero (inv_ne_zero hbF0) hcontF0
    refine ⟨β, h.primPart, hβ0,
      (isGarlingPrimitive_iff h.primPart).mpr h.isPrimitive_primPart, ?_⟩
    have hmap_decomp : h.map (algebraMap R F) =
        Polynomial.C (algebraMap R F h.content) * h.primPart.map (algebraMap R F) := by
      conv_lhs => rw [h.eq_C_content_mul_primPart]
      rw [Polynomial.map_mul, Polynomial.map_C]
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hbF0)
    rw [← hb_mul, hmap_decomp, ← mul_assoc, ← Polynomial.C_mul]
    congr 1
    dsimp only [β]
    rw [← mul_assoc, mul_inv_cancel₀ hbF0, one_mul]
  · have hg_prim : g.IsPrimitive := (isGarlingPrimitive_iff g).mp hg
    have hg'_prim : g'.IsPrimitive := (isGarlingPrimitive_iff g').mp hg'
    have hβ0 : β ≠ 0 := by
      intro hz
      rw [hz, map_zero, zero_mul] at hf1
      exact hf0 hf1
    have hβ'0 : β' ≠ 0 := by
      intro hz
      rw [hz, map_zero, zero_mul] at hf2
      exact hf0 hf2
    obtain ⟨r₁, s₁, hs₁, hr₁s₁⟩ := IsFractionRing.div_surjective (A := R) β
    obtain ⟨r₂, s₂, hs₂, hr₂s₂⟩ := IsFractionRing.div_surjective (A := R) β'
    have hs₁0 : s₁ ≠ 0 := nonZeroDivisors.ne_zero hs₁
    have hs₂0 : s₂ ≠ 0 := nonZeroDivisors.ne_zero hs₂
    have hs₁F0 : algebraMap R F s₁ ≠ 0 :=
      (IsFractionRing.injective R F).ne_iff' (map_zero _) |>.mpr hs₁0
    have hs₂F0 : algebraMap R F s₂ ≠ 0 :=
      (IsFractionRing.injective R F).ne_iff' (map_zero _) |>.mpr hs₂0
    have hr₁0 : r₁ ≠ 0 := by
      intro hz
      rw [← hr₁s₁, hz, map_zero, zero_div] at hβ0
      exact hβ0 rfl
    have heqF : Polynomial.C (algebraMap R F (r₁ * s₂)) * g.map (algebraMap R F) =
        Polynomial.C (algebraMap R F (r₂ * s₁)) * g'.map (algebraMap R F) := by
      have h12 : Polynomial.C β * g.map (algebraMap R F) =
          Polynomial.C β' * g'.map (algebraMap R F) := hf1.symm.trans hf2
      have hmul := congrArg (fun p : F[X] =>
        Polynomial.C (algebraMap R F s₁ * algebraMap R F s₂) * p) h12
      rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul] at hmul
      have hc1 : (algebraMap R F s₁ * algebraMap R F s₂) * β = algebraMap R F (r₁ * s₂) := by
        rw [← hr₁s₁, map_mul]
        field_simp
      have hc2 : (algebraMap R F s₁ * algebraMap R F s₂) * β' = algebraMap R F (r₂ * s₁) := by
        rw [← hr₂s₂, map_mul]
        field_simp
      rwa [hc1, hc2] at hmul
    have heqR : Polynomial.C (r₁ * s₂) * g = Polynomial.C (r₂ * s₁) * g' := by
      apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
      simpa [Polynomial.map_mul, Polynomial.map_C] using heqF
    have hass_cont : Associated (r₁ * s₂) (r₂ * s₁) := by
      have h1 := Polynomial.associated_content_C_mul (r₁ * s₂) g
      have h2 := Polynomial.associated_content_C_mul (r₂ * s₁) g'
      rw [hg_prim.content_eq_one, mul_one] at h1
      rw [hg'_prim.content_eq_one, mul_one] at h2
      rw [heqR] at h1
      exact h1.symm.trans h2
    rcases hass_cont with ⟨u, hu⟩
    have hr₁s₂0 : Polynomial.C (r₁ * s₂) ≠ (0 : R[X]) :=
      Polynomial.C_ne_zero.mpr (mul_ne_zero hr₁0 hs₂0)
    have hg_eq : g = Polynomial.C (u : R) * g' := by
      apply mul_left_cancel₀ hr₁s₂0
      rw [heqR, ← hu, map_mul, mul_assoc]
    let uP : R[X]ˣ := Units.map Polynomial.C.toMonoidHom u
    refine ⟨⟨uP⁻¹, ?_⟩, (u : R), u.isUnit, hg_eq⟩
    change g * Polynomial.C (↑u⁻¹ : R) = g'
    rw [hg_eq, mul_comm (Polynomial.C (u : R)) g', mul_assoc, ← Polynomial.C_mul,
      Units.mul_inv, map_one, mul_one]

/-- **Theorem 3.12** (§3.7, p. 32, Mathlib `UniqueFactorizationMonoid` version): Over a unique
factorization domain `R`, if `f` and `g` are primitive elements of `R[x]`, then `f * g` is
primitive. -/
theorem theorem_3_12_ufm {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {f g : R[X]} (hf : f.IsPrimitive) (hg : g.IsPrimitive) :
    (f * g).IsPrimitive := by
  classical
  let _ : NormalizedGCDMonoid R := Classical.arbitrary (NormalizedGCDMonoid R)
  exact hf.mul hg

/-- **Theorem 3.12** (§3.7, p. 32, Garling `IsGarlingUFD` / `IsGarlingPrimitive` version): Over a
unique factorization domain `R`, if `f` and `g` are primitive elements of `R[x]`, so is `f * g`. -/
theorem theorem_3_12 {R : Type*} [CommRing R] (hufd : IsGarlingUFD R)
    {f g : R[X]} (hf : IsGarlingPrimitive f) (hg : IsGarlingPrimitive g) :
    IsGarlingPrimitive (f * g) := by
  have _ : IsDomain R := hufd.isDomain
  have _ : UniqueFactorizationMonoid R :=
    (isGarlingUFD_iff_uniqueFactorizationMonoid R).mp hufd
  rw [isGarlingPrimitive_iff] at hf hg ⊢
  exact theorem_3_12_ufm hf hg

/-- **Corollary (Gauss' lemma)** [to Theorem 3.12] (§3.7, p. 32): Over a unique factorization domain
`R` with field of fractions `F`, an element `g` of `R[x]` is irreducible if and only if either `g`
is an irreducible constant from `R` or `g` is primitive and irreducible in `F[x]`. -/
theorem corollary_gauss_lemma {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] (g : R[X]) :
    Irreducible g ↔
      (∃ a : R, Irreducible a ∧ g = Polynomial.C a) ∨
      (IsGarlingPrimitive g ∧ Irreducible (g.map (algebraMap R F))) := by
  have hirr_C : ∀ a : R, Irreducible (Polynomial.C a : R[X]) ↔ Irreducible a := by
    intro a
    constructor
    · intro hCa
      refine ⟨fun hu => hCa.not_isUnit (hu.map Polynomial.C), fun b c hbc => ?_⟩
      have hprod : (Polynomial.C a : R[X]) = Polynomial.C b * Polynomial.C c := by
        rw [hbc, map_mul]
      rcases hCa.isUnit_or_isUnit hprod with hub | huc
      · obtain ⟨u, hu, heq⟩ := Polynomial.isUnit_iff.mp hub
        exact Or.inl (Polynomial.C_injective heq ▸ hu)
      · obtain ⟨u, hu, heq⟩ := Polynomial.isUnit_iff.mp huc
        exact Or.inr (Polynomial.C_injective heq ▸ hu)
    · intro ha
      have ha0 : a ≠ 0 := ha.ne_zero
      refine ⟨fun hu => ?_, fun p q hpq => ?_⟩
      · obtain ⟨u, hu', heq⟩ := Polynomial.isUnit_iff.mp hu
        exact ha.not_isUnit (Polynomial.C_injective heq ▸ hu')
      · have hp0 : p ≠ 0 := fun hz => Polynomial.C_ne_zero.mpr ha0 (by rw [hpq, hz, zero_mul])
        have hq0 : q ≠ 0 := fun hz => Polynomial.C_ne_zero.mpr ha0 (by rw [hpq, hz, mul_zero])
        have hdeg : p.natDegree + q.natDegree = 0 := by
          have := congrArg Polynomial.natDegree hpq
          rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hp0 hq0] at this
          exact this.symm
        have hp_deg0 : p.natDegree = 0 := by omega
        have hq_deg0 : q.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hp_deg0,
          Polynomial.eq_C_of_natDegree_eq_zero hq_deg0] at hpq ⊢
        rw [← map_mul] at hpq
        rcases ha.isUnit_or_isUnit (Polynomial.C_injective hpq) with hub | huc
        · exact Or.inl (hub.map Polynomial.C)
        · exact Or.inr (huc.map Polynomial.C)
  constructor
  · intro hg
    by_cases hdeg : g.natDegree = 0
    · left
      refine ⟨g.coeff 0, ?_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
      rw [← hirr_C]
      rwa [← Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    · right
      have hprim : g.IsPrimitive := hg.isPrimitive hdeg
      exact ⟨(isGarlingPrimitive_iff g).mpr hprim,
        (hprim.irreducible_iff_irreducible_map_fraction_map (K := F)).mp hg⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨hprim, hirrF⟩)
    · exact (hirr_C a).mpr ha
    · exact ((isGarlingPrimitive_iff g).mp hprim).irreducible_iff_irreducible_map_fraction_map.mpr
        hirrF

/-- **Theorem 3.13** (§3.7, pp. 32–33): If `R` is a unique factorization domain, so is `R[x]`
(both in Garling's `IsGarlingUFD` formulation and Mathlib's `UniqueFactorizationMonoid`). -/
theorem theorem_3_13 {R : Type*} [CommRing R] (hufd : IsGarlingUFD R) :
    IsGarlingUFD R[X] := by
  have _ : IsDomain R := hufd.isDomain
  have _ : UniqueFactorizationMonoid R :=
    (isGarlingUFD_iff_uniqueFactorizationMonoid R).mp hufd
  exact (isGarlingUFD_iff_uniqueFactorizationMonoid R[X]).mpr inferInstance

theorem theorem_3_13_ufm (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[X] :=
  inferInstance

/-- **Corollary 1** [to Theorem 3.13] (§3.7, p. 33): Over a unique factorization domain `R` with
field of fractions `F`, if `f ∈ R[x]` is primitive, `g ∈ R[x]` is non-zero, and `f` divides `g` in
`F[x]`, then `f` divides `g` in `R[x]`. -/
theorem corollary_1_to_theorem_3_13 {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    {f g : R[X]} (hf : IsGarlingPrimitive f) (_hg : g ≠ 0)
    (hdvd : f.map (algebraMap R F) ∣ g.map (algebraMap R F)) :
    f ∣ g :=
  ((isGarlingPrimitive_iff f).mp hf).dvd_of_fraction_map_dvd_fraction_map hdvd

/-- **Corollary 2** [to Theorem 3.13] (§3.7, p. 33): If `R` is a unique factorization domain, then
so is `R[x₁, ..., x_n]` (`MvPolynomial (Fin n) R`), in both Garling's `IsGarlingUFD` formulation and
Mathlib's `UniqueFactorizationMonoid`. -/
theorem corollary_2_to_theorem_3_13 {R : Type*} [CommRing R] (hufd : IsGarlingUFD R) (n : ℕ) :
    IsGarlingUFD (MvPolynomial (Fin n) R) := by
  have _ : IsDomain R := hufd.isDomain
  have _ : UniqueFactorizationMonoid R :=
    (isGarlingUFD_iff_uniqueFactorizationMonoid R).mp hufd
  exact (isGarlingUFD_iff_uniqueFactorizationMonoid (MvPolynomial (Fin n) R)).mpr inferInstance

theorem corollary_2_to_theorem_3_13_ufm (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (n : ℕ) :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) R) :=
  inferInstance

/-- Helper over any field `K`: every degree-1 polynomial in `K[x]` is irreducible, and every
degree-2 or degree-3 polynomial in `K[x]` with no root in `K` is irreducible. -/
theorem field_poly_irreducible_of_natDegree_eq_one {K : Type*} [Field K] {f : K[X]}
    (hd : f.natDegree = 1) : Irreducible f := by
  have hf0 : f ≠ 0 := by
    intro hz; rw [hz, Polynomial.natDegree_zero] at hd; omega
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have ha0 : a ≠ 0 := fun hz => hf0 (by rw [hab, hz, zero_mul])
    have hb0 : b ≠ 0 := fun hz => hf0 (by rw [hab, hz, mul_zero])
    have hsum : a.natDegree + b.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hd]
    rcases (show a.natDegree = 0 ∨ b.natDegree = 0 by omega) with ha_deg0 | hb_deg0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero ha_deg0] at ha0 ⊢
      exact (IsUnit.mk0 (a.coeff 0) (Polynomial.C_ne_zero.mp ha0)).map Polynomial.C
    · right
      rw [Polynomial.eq_C_of_natDegree_eq_zero hb_deg0] at hb0 ⊢
      exact (IsUnit.mk0 (b.coeff 0) (Polynomial.C_ne_zero.mp hb0)).map Polynomial.C

theorem field_poly_irreducible_of_natDegree_two_or_three_no_root {K : Type*} [Field K] {f : K[X]}
    (hd : f.natDegree = 2 ∨ f.natDegree = 3) (hroot : ∀ x : K, f.eval x ≠ 0) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by
    intro hz; rw [hz, Polynomial.natDegree_zero] at hd; omega
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · by_contra hnot
    rw [not_or] at hnot
    rcases hnot with ⟨hau, hbu⟩
    have ha0 : a ≠ 0 := fun hz => hf0 (by rw [hab, hz, zero_mul])
    have hb0 : b ≠ 0 := fun hz => hf0 (by rw [hab, hz, mul_zero])
    have ha_pos : 0 < a.natDegree := by
      by_contra hle
      have ha_deg0 : a.natDegree = 0 := by omega
      apply hau
      rw [Polynomial.eq_C_of_natDegree_eq_zero ha_deg0] at ha0 ⊢
      exact (IsUnit.mk0 (a.coeff 0) (Polynomial.C_ne_zero.mp ha0)).map Polynomial.C
    have hb_pos : 0 < b.natDegree := by
      by_contra hle
      have hb_deg0 : b.natDegree = 0 := by omega
      apply hbu
      rw [Polynomial.eq_C_of_natDegree_eq_zero hb_deg0] at hb0 ⊢
      exact (IsUnit.mk0 (b.coeff 0) (Polynomial.C_ne_zero.mp hb0)).map Polynomial.C
    have hsum : a.natDegree + b.natDegree = f.natDegree :=
      (Polynomial.natDegree_mul ha0 hb0).symm.trans (congrArg Polynomial.natDegree hab).symm
    have hdeg1_has_root : ∀ g : K[X], g.natDegree = 1 → g ∣ f → False := by
      intro g hg1 ⟨q, hqf⟩
      have hg_lead0 : g.coeff 1 ≠ 0 := by
        rw [← hg1]
        exact Polynomial.leadingCoeff_ne_zero.mpr (by
          intro hz; rw [hz, Polynomial.natDegree_zero] at hg1; omega)
      have hg_eq : g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) := by
        ext n
        rcases n with _ | _ | n
        · simp
        · simp
        · have hgt : g.natDegree < n + 2 := by omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
      let r : K := -(g.coeff 0) / (g.coeff 1)
      have hgeval : g.eval r = 0 := by
        rw [hg_eq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, r]
        field_simp
        ring
      apply hroot r
      rw [hqf, Polynomial.eval_mul, hgeval, zero_mul]
    rcases (show a.natDegree = 1 ∨ b.natDegree = 1 by omega) with ha1 | hb1
    · exact hdeg1_has_root a ha1 ⟨b, hab⟩
    · exact hdeg1_has_root b hb1 ⟨a, hab.trans (mul_comm a b)⟩

/-- **Exercise 3.22** (§3.7, p. 34): Complete classification and irreducible factorizations of all
eight cubic polynomials (`f.natDegree = 3`) in `ℤ_2[x]` (`(ZMod 2)[X]`):
1. `x^3 = x · x · x`
2. `x^3 + x^2 = x · x · (x + 1)`
3. `x^3 + x = x · (x + 1) · (x + 1)`
4. `x^3 + x^2 + x + 1 = (x + 1) · (x + 1) · (x + 1)`
5. `x^3 + 1 = (x + 1) · (x^2 + x + 1)`
6. `x^3 + x^2 + x = x · (x^2 + x + 1)`
7. `x^3 + x + 1` (irreducible)
8. `x^3 + x^2 + 1` (irreducible) -/
theorem exercise_3_22 :
    (∀ f : (ZMod 2)[X], f.natDegree = 3 ↔
      f ∈ ({Polynomial.X ^ 3,
            Polynomial.X ^ 3 + Polynomial.X ^ 2,
            Polynomial.X ^ 3 + Polynomial.X,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1,
            Polynomial.X ^ 3 + 1,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X,
            Polynomial.X ^ 3 + Polynomial.X + 1,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1} : Set (ZMod 2)[X])) ∧
    Irreducible (Polynomial.X : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X + 1 : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X ^ 3 + Polynomial.X + 1 : (ZMod 2)[X]) ∧
    Irreducible (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : (ZMod 2)[X]) ∧
    (Polynomial.X ^ 3 : (ZMod 2)[X]) = Polynomial.X * Polynomial.X * Polynomial.X ∧
    (Polynomial.X ^ 3 + Polynomial.X ^ 2 : (ZMod 2)[X]) =
      Polynomial.X * Polynomial.X * (Polynomial.X + 1) ∧
    (Polynomial.X ^ 3 + Polynomial.X : (ZMod 2)[X]) =
      Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 1) ∧
    (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]) =
      (Polynomial.X + 1) * (Polynomial.X + 1) * (Polynomial.X + 1) ∧
    (Polynomial.X ^ 3 + 1 : (ZMod 2)[X]) =
      (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) ∧
    (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X : (ZMod 2)[X]) =
      Polynomial.X * (Polynomial.X ^ 2 + Polynomial.X + 1) := by
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h2z : (2 : (ZMod 2)[X]) = 0 := by
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = Polynomial.C 1 + Polynomial.C 1 := by simp [one_add_one_eq_two]
      _ = Polynomial.C (1 + 1 : ZMod 2) := (map_add Polynomial.C 1 1).symm
      _ = Polynomial.C 0 := by rw [h11]
      _ = 0 := map_zero _
  have hdeg_helper : ∀ (c₂ c₁ c₀ : ZMod 2),
      (Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2 +
        Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀ : (ZMod 2)[X]).natDegree = 3 := by
    intro c₂ c₁ c₀
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_C]
      split_ifs <;> first | omega | ring
    · simp
  have hdeg_x2 : (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]).natDegree = 2 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one]
      split_ifs <;> first | omega | ring
    · simp [Polynomial.coeff_X, Polynomial.coeff_one]
  have hclass : ∀ f : (ZMod 2)[X], f.natDegree = 3 ↔
      f ∈ ({Polynomial.X ^ 3,
            Polynomial.X ^ 3 + Polynomial.X ^ 2,
            Polynomial.X ^ 3 + Polynomial.X,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1,
            Polynomial.X ^ 3 + 1,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X,
            Polynomial.X ^ 3 + Polynomial.X + 1,
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1} : Set (ZMod 2)[X]) := by
    intro f
    constructor
    · intro hd3
      have hc3 : f.coeff 3 = 1 := by
        have hne0 : f.coeff 3 ≠ 0 := by
          rw [← hd3]
          exact Polynomial.leadingCoeff_ne_zero.mpr (by
            intro hz; rw [hz, Polynomial.natDegree_zero] at hd3; omega)
        rcases zmod2_cases (f.coeff 3) with h0 | h1
        · exact absurd h0 hne0
        · exact h1
      have hf_eq : f = Polynomial.X ^ 3 + Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
          Polynomial.C (f.coeff 1) * Polynomial.X + Polynomial.C (f.coeff 0) := by
        ext n
        rcases n with _ | _ | _ | _ | n
        · simp
        · simp
        · simp
        · simp [hc3]
        · have hgt : f.natDegree < n + 4 := by omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
      rw [hf_eq]
      rcases zmod2_cases (f.coeff 2) with h2 | h2 <;>
        rcases zmod2_cases (f.coeff 1) with h1 | h1 <;>
        rcases zmod2_cases (f.coeff 0) with h0 | h0 <;>
        simp [h2, h1, h0, add_assoc]
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · simp
      · simpa using hdeg_helper 1 0 0
      · simpa using hdeg_helper 0 1 0
      · simpa [add_assoc] using hdeg_helper 1 1 1
      · simp
      · simpa [add_assoc] using hdeg_helper 1 1 0
      · simpa [add_assoc] using hdeg_helper 0 1 1
      · simpa [add_assoc] using hdeg_helper 1 0 1
  have hirr_X : Irreducible (Polynomial.X : (ZMod 2)[X]) :=
    field_poly_irreducible_of_natDegree_eq_one Polynomial.natDegree_X
  have hirr_X1 : Irreducible (Polynomial.X + 1 : (ZMod 2)[X]) :=
    field_poly_irreducible_of_natDegree_eq_one (by simp)
  have hirr_quad : Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X]) := by
    refine field_poly_irreducible_of_natDegree_two_or_three_no_root (Or.inl hdeg_x2) (fun x => ?_)
    (rcases zmod2_cases x with rfl | rfl <;> simp); decide
  have hirr_cub1 : Irreducible (Polynomial.X ^ 3 + Polynomial.X + 1 : (ZMod 2)[X]) := by
    have hd : (Polynomial.X ^ 3 + Polynomial.X + 1 : (ZMod 2)[X]).natDegree = 3 := by
      simpa [add_assoc] using hdeg_helper 0 1 1
    refine field_poly_irreducible_of_natDegree_two_or_three_no_root (Or.inr hd) (fun x => ?_)
    (rcases zmod2_cases x with rfl | rfl <;> simp); decide
  have hirr_cub2 : Irreducible (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : (ZMod 2)[X]) := by
    have hd : (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by
      simpa [add_assoc] using hdeg_helper 1 0 1
    refine field_poly_irreducible_of_natDegree_two_or_three_no_root (Or.inr hd) (fun x => ?_)
    (rcases zmod2_cases x with rfl | rfl <;> simp); decide
  refine ⟨hclass, hirr_X, hirr_X1, hirr_quad, hirr_cub1, hirr_cub2,
    by ring, by ring, ?_, ?_, ?_, by ring⟩
  · calc (Polynomial.X ^ 3 + Polynomial.X : (ZMod 2)[X])
        = Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 + Polynomial.X := by
          rw [h2z, zero_mul, add_zero]
      _ = Polynomial.X * (Polynomial.X + 1) * (Polynomial.X + 1) := by ring
  · calc (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 : (ZMod 2)[X])
        = Polynomial.X ^ 3 + (1 + 2) * Polynomial.X ^ 2 + (1 + 2) * Polynomial.X + 1 := by
          rw [h2z, add_zero, one_mul, one_mul]
      _ = (Polynomial.X + 1) * (Polynomial.X + 1) * (Polynomial.X + 1) := by ring
  · calc (Polynomial.X ^ 3 + 1 : (ZMod 2)[X])
        = Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1 := by
          rw [h2z, zero_mul, add_zero, zero_mul, add_zero]
      _ = (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) := by ring

/-- Non-zero homogeneous linear forms in `ℤ_2[x, y, z]` (`MvPolynomial (Fin 3) (ZMod 2)`). -/
def IsHomogLinZ2 (p : MvPolynomial (Fin 3) (ZMod 2)) : Prop :=
  p ≠ 0 ∧ p.IsHomogeneous 1

/-- Non-zero homogeneous quadratic forms in `ℤ_2[x, y, z]` (`MvPolynomial (Fin 3) (ZMod 2)`). -/
def IsHomogQuadZ2 (p : MvPolynomial (Fin 3) (ZMod 2)) : Prop :=
  p ≠ 0 ∧ p.IsHomogeneous 2

private noncomputable def quadExpZ2 : Fin 6 → (Fin 3 →₀ ℕ)
  | ⟨0, _⟩ => Finsupp.single 0 2
  | ⟨1, _⟩ => Finsupp.single 1 2
  | ⟨2, _⟩ => Finsupp.single 2 2
  | ⟨3, _⟩ => Finsupp.single 0 1 + Finsupp.single 1 1
  | ⟨4, _⟩ => Finsupp.single 0 1 + Finsupp.single 2 1
  | ⟨5, _⟩ => Finsupp.single 1 1 + Finsupp.single 2 1

private theorem finsupp_fin3_degree_eq (d : Fin 3 →₀ ℕ) :
    d.degree = d 0 + d 1 + d 2 := by
  rw [Finsupp.degree_apply,
    Finset.sum_subset (Finset.subset_univ d.support)
      (fun i _ hi => Finsupp.notMem_support_iff.mp hi),
    Fin.sum_univ_three]

private theorem finsupp_fin3_deg1_iff (d : Fin 3 →₀ ℕ) :
    d.degree = 1 ↔ ∃ i : Fin 3, d = Finsupp.single i 1 := by
  rw [finsupp_fin3_degree_eq]
  constructor
  · intro hd
    rcases (show (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1) by omega) with
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · refine ⟨0, ?_⟩
      ext j; fin_cases j <;> simp [h0, h1, h2]
    · refine ⟨1, ?_⟩
      ext j; fin_cases j <;> simp [h0, h1, h2]
    · refine ⟨2, ?_⟩
      ext j; fin_cases j <;> simp [h0, h1, h2]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

private theorem finsupp_fin3_deg2_iff (d : Fin 3 →₀ ℕ) :
    d.degree = 2 ↔ ∃ k : Fin 6, d = quadExpZ2 k := by
  rw [finsupp_fin3_degree_eq]
  constructor
  · intro hd
    rcases (show (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) ∨
        (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
        (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨
        (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) by omega) with
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · refine ⟨0, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
    · refine ⟨1, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
    · refine ⟨2, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
    · refine ⟨3, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
    · refine ⟨4, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
    · refine ⟨5, ?_⟩; ext j; fin_cases j <;> simp [quadExpZ2, h0, h1, h2]
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [quadExpZ2]

private theorem quadExpZ2_injective : Function.Injective quadExpZ2 := by
  intro i j hij
  have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) hij
  have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) hij
  have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) hij
  fin_cases i <;> fin_cases j <;> simp [quadExpZ2] at h0 h1 h2 ⊢

/-- Bijection between the `7` non-zero homogeneous linear forms in `ℤ_2[x, y, z]` and the `7`
non-zero coefficient vectors in `Fin 3 → ZMod 2`. -/
noncomputable def homogLinZ2Equiv :
    {p : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 p} ≃
      {v : Fin 3 → ZMod 2 // v ≠ 0} where
  toFun p := ⟨fun i => p.1.coeff (Finsupp.single i 1), by
    intro hv0
    apply p.2.1
    ext d
    change p.1.coeff d = 0
    by_cases hd : d.degree = 1
    · obtain ⟨i, rfl⟩ := (finsupp_fin3_deg1_iff d).mp hd
      exact congrFun hv0 i
    · exact p.2.2.coeff_eq_zero hd⟩
  invFun v := ⟨∑ i : Fin 3, MvPolynomial.monomial (Finsupp.single i 1) (v.1 i), by
    have hcoeff : ∀ j : Fin 3,
        (∑ i : Fin 3, MvPolynomial.monomial (Finsupp.single i 1) (v.1 i)).coeff
          (Finsupp.single j 1) = v.1 j := by
      intro j
      rw [MvPolynomial.coeff_sum]
      simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj Nat.one_ne_zero]
    refine ⟨?_, ?_⟩
    · intro hz
      apply v.2
      ext j
      simpa [hz] using (hcoeff j).symm
    · refine MvPolynomial.IsHomogeneous.sum _ _ 1 (fun i _ => ?_)
      apply MvPolynomial.isHomogeneous_monomial
      exact (finsupp_fin3_deg1_iff _).mpr ⟨i, rfl⟩,
    ⟩
  left_inv p := by
    apply Subtype.ext
    ext d
    dsimp only
    rw [MvPolynomial.coeff_sum]
    by_cases hd : d.degree = 1
    · obtain ⟨j, rfl⟩ := (finsupp_fin3_deg1_iff d).mp hd
      simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj Nat.one_ne_zero]
    · rw [p.2.2.coeff_eq_zero hd]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [MvPolynomial.coeff_monomial, ite_eq_right_iff]
      intro hdi
      exact False.elim (hd (hdi ▸ (finsupp_fin3_deg1_iff _).mpr ⟨i, rfl⟩))
  right_inv v := by
    apply Subtype.ext
    ext j
    dsimp only
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj Nat.one_ne_zero]

/-- Bijection between the `63` non-zero homogeneous quadratic forms in `ℤ_2[x, y, z]` and the `63`
non-zero coefficient vectors in `Fin 6 → ZMod 2`. -/
noncomputable def homogQuadZ2Equiv :
    {p : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 p} ≃
      {v : Fin 6 → ZMod 2 // v ≠ 0} where
  toFun p := ⟨fun k => p.1.coeff (quadExpZ2 k), by
    intro hv0
    apply p.2.1
    ext d
    change p.1.coeff d = 0
    by_cases hd : d.degree = 2
    · obtain ⟨k, rfl⟩ := (finsupp_fin3_deg2_iff d).mp hd
      exact congrFun hv0 k
    · exact p.2.2.coeff_eq_zero hd⟩
  invFun v := ⟨∑ k : Fin 6, MvPolynomial.monomial (quadExpZ2 k) (v.1 k), by
    have hcoeff : ∀ j : Fin 6,
        (∑ k : Fin 6, MvPolynomial.monomial (quadExpZ2 k) (v.1 k)).coeff (quadExpZ2 j) =
          v.1 j := by
      intro j
      rw [MvPolynomial.coeff_sum]
      simp [MvPolynomial.coeff_monomial, quadExpZ2_injective.eq_iff]
    refine ⟨?_, ?_⟩
    · intro hz
      apply v.2
      ext j
      simpa [hz] using (hcoeff j).symm
    · refine MvPolynomial.IsHomogeneous.sum _ _ 2 (fun k _ => ?_)
      apply MvPolynomial.isHomogeneous_monomial
      exact (finsupp_fin3_deg2_iff _).mpr ⟨k, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    ext d
    dsimp only
    rw [MvPolynomial.coeff_sum]
    by_cases hd : d.degree = 2
    · obtain ⟨j, rfl⟩ := (finsupp_fin3_deg2_iff d).mp hd
      simp [MvPolynomial.coeff_monomial, quadExpZ2_injective.eq_iff]
    · rw [p.2.2.coeff_eq_zero hd]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [MvPolynomial.coeff_monomial, ite_eq_right_iff]
      intro hdk
      exact False.elim (hd (hdk ▸ (finsupp_fin3_deg2_iff _).mpr ⟨k, rfl⟩))
  right_inv v := by
    apply Subtype.ext
    ext j
    dsimp only
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, quadExpZ2_injective.eq_iff]

/-- In `ℤ_2[x, y, z]`, `1` is the unique unit, so `Associated f g ↔ f = g`. -/
theorem mvPolyZ2_isUnit_iff (u : MvPolynomial (Fin 3) (ZMod 2)) :
    IsUnit u ↔ u = 1 := by
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  constructor
  · intro hu
    have hdeg0 : u.totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hu_eq : u = MvPolynomial.C (u.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    have hc0 : u.coeff 0 ≠ 0 := by
      intro hz
      rw [hu_eq, hz, map_zero] at hu
      exact not_isUnit_zero hu
    rcases zmod2_cases (u.coeff 0) with h0 | h1
    · exact absurd h0 hc0
    · rw [hu_eq, h1, map_one]
  · rintro rfl
    exact isUnit_one

theorem mvPolyZ2_associated_iff (f g : MvPolynomial (Fin 3) (ZMod 2)) :
    Associated f g ↔ f = g := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu1 : (u : MvPolynomial (Fin 3) (ZMod 2)) = 1 :=
      (mvPolyZ2_isUnit_iff _).mp u.isUnit
    rw [hu1, mul_one]
  · rintro rfl
    exact Associated.rfl

/-- Every non-zero homogeneous linear form in `ℤ_2[x, y, z]` is irreducible. -/
theorem isHomogLinZ2_irreducible {L : MvPolynomial (Fin 3) (ZMod 2)} (hL : IsHomogLinZ2 L) :
    Irreducible L := by
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  apply MvPolynomial.irreducible_of_totalDegree_eq_one (hL.2.totalDegree hL.1)
  intro r hr
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hL.1
  have hr0 : r ≠ 0 := by
    intro hz
    rcases hr d with ⟨q, hq⟩
    exact hd (by rw [hq, hz, zero_mul])
  rcases zmod2_cases r with h0 | h1
  · exact absurd h0 hr0
  · rw [h1]; exact isUnit_one

/-- Unordered multiplication map sending an unordered pair `s(L₁, L₂)` of the `7` non-zero
homogeneous linear forms in `ℤ_2[x, y, z]` to the homogeneous quadratic `L₁ * L₂`. -/
noncomputable def homogLinPairMulZ2 :
    Sym2 {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L} →
      {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} :=
  Sym2.lift ⟨fun L₁ L₂ => ⟨L₁.1 * L₂.1, mul_ne_zero L₁.2.1 L₂.2.1, L₁.2.2.mul L₂.2.2⟩,
    fun L₁ L₂ => Subtype.ext (mul_comm L₁.1 L₂.1)⟩

theorem homogLinPairMulZ2_injective : Function.Injective homogLinPairMulZ2 := by
  intro z₁ z₂ heq
  induction z₁ using Sym2.ind with
  | _ L₁ L₂ =>
    induction z₂ using Sym2.ind with
    | _ M₁ M₂ =>
      have hprod : L₁.1 * L₂.1 = M₁.1 * M₂.1 := congrArg Subtype.val heq
      have hpL₁ : Prime L₁.1 :=
        UniqueFactorizationMonoid.irreducible_iff_prime.mp (isHomogLinZ2_irreducible L₁.2)
      have hdvd : L₁.1 ∣ M₁.1 * M₂.1 := ⟨L₂.1, hprod.symm⟩
      rcases hpL₁.dvd_or_dvd hdvd with hM₁ | hM₂
      · obtain ⟨u, hu⟩ := hM₁
        have hu_unit : IsUnit u := by
          rcases (isHomogLinZ2_irreducible M₁.2).isUnit_or_isUnit hu with hL₁u | huu
          · exact absurd hL₁u (isHomogLinZ2_irreducible L₁.2).not_isUnit
          · exact huu
        rw [(mvPolyZ2_isUnit_iff u).mp hu_unit, mul_one] at hu
        have hL₁_eq : L₁ = M₁ := Subtype.ext hu.symm
        subst hL₁_eq
        have hL₂_eq : L₂ = M₂ := Subtype.ext (mul_left_cancel₀ L₁.2.1 hprod)
        subst hL₂_eq
        rfl
      · obtain ⟨u, hu⟩ := hM₂
        have hu_unit : IsUnit u := by
          rcases (isHomogLinZ2_irreducible M₂.2).isUnit_or_isUnit hu with hL₁u | huu
          · exact absurd hL₁u (isHomogLinZ2_irreducible L₁.2).not_isUnit
          · exact huu
        rw [(mvPolyZ2_isUnit_iff u).mp hu_unit, mul_one] at hu
        have hL₁_eq : L₁ = M₂ := Subtype.ext hu.symm
        subst hL₁_eq
        have hL₂_eq : L₂ = M₁ := Subtype.ext (mul_left_cancel₀ L₁.2.1 (hprod.trans (mul_comm M₁.1 L₁.1)))
        subst hL₂_eq
        exact Sym2.eq_swap

/-- A non-zero homogeneous quadratic `Q` in `ℤ_2[x, y, z]` is reducible if and only if `Q = L₁ * L₂`
for two (unique up to order) non-zero homogeneous linear forms `L₁, L₂`. -/
theorem isHomogQuadZ2_not_irreducible_iff {Q : MvPolynomial (Fin 3) (ZMod 2)}
    (hQ : IsHomogQuadZ2 Q) :
    ¬ Irreducible Q ↔
      ∃ L₁ L₂ : MvPolynomial (Fin 3) (ZMod 2),
        IsHomogLinZ2 L₁ ∧ IsHomogLinZ2 L₂ ∧ Q = L₁ * L₂ := by
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  constructor
  · intro hred
    have hQ_deg : Q.totalDegree = 2 := hQ.2.totalDegree hQ.1
    have hQ_nu : ¬ IsUnit Q := by
      intro hu
      rw [(mvPolyZ2_isUnit_iff Q).mp hu] at hQ_deg
      simp at hQ_deg
    have hex_fac : ∃ A B : MvPolynomial (Fin 3) (ZMod 2),
        Q = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
      by_contra hall
      apply hred
      refine ⟨hQ_nu, fun A B hAB => ?_⟩
      by_contra hnot
      rw [not_or] at hnot
      exact hall ⟨A, B, hAB, hnot.1, hnot.2⟩
    obtain ⟨A, B, hAB, hAu, hBu⟩ := hex_fac
    have hA0 : A ≠ 0 := fun hz => hQ.1 (by rw [hAB, hz, zero_mul])
    have hB0 : B ≠ 0 := fun hz => hQ.1 (by rw [hAB, hz, mul_zero])
    have hdeg_pos : ∀ {P : MvPolynomial (Fin 3) (ZMod 2)}, P ≠ 0 → ¬ IsUnit P →
        0 < P.totalDegree := by
      intro P hP0 hPu
      by_contra hle
      have h0 : P.totalDegree = 0 := by omega
      have hPC : P = MvPolynomial.C (P.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
      have hc0 : P.coeff 0 ≠ 0 := fun hz => hP0 (by rw [hPC, hz, map_zero])
      rcases zmod2_cases (P.coeff 0) with h0' | h1'
      · exact hc0 h0'
      · rw [hPC, h1', map_one] at hPu
        exact hPu isUnit_one
    have hA_pos : 0 < A.totalDegree := hdeg_pos hA0 hAu
    have hB_pos : 0 < B.totalDegree := hdeg_pos hB0 hBu
    have hsum : A.totalDegree + B.totalDegree = 2 := by
      rw [← MvPolynomial.totalDegree_mul_of_isDomain hA0 hB0, ← hAB, hQ_deg]
    have hA1 : A.totalDegree = 1 := by omega
    have hB1 : B.totalDegree = 1 := by omega
    have hdecomp1 : ∀ {P : MvPolynomial (Fin 3) (ZMod 2)}, P.totalDegree = 1 →
        (P - MvPolynomial.C (P.coeff 0)).IsHomogeneous 1 ∧
        P - MvPolynomial.C (P.coeff 0) ≠ 0 := by
      intro P hP1
      refine ⟨fun d hd => ?_, ?_⟩
      · rw [Pi.one_def, ← Finsupp.degree_eq_weight_one]
        have hd_le : d.degree ≤ 1 := by
          have hd_mem : d ∈ P.support := by
            by_contra hnot
            rw [MvPolynomial.coeff_sub, MvPolynomial.notMem_support_iff.mp hnot] at hd
            by_cases hd0 : d = 0
            · subst hd0; simp at hd; exact hd (MvPolynomial.notMem_support_iff.mp hnot)
            · simp [MvPolynomial.coeff_C, Ne.symm hd0] at hd
          have hle := MvPolynomial.le_totalDegree hd_mem
          rw [hP1] at hle
          rwa [Finsupp.degree_apply]
        have hd_ne0 : d ≠ 0 := by
          intro hz
          subst hz
          simp at hd
        have hd_pos : 0 < d.degree := by
          by_contra h0
          have hdeg0 : d.degree = 0 := by omega
          rw [finsupp_fin3_degree_eq] at hdeg0
          apply hd_ne0
          ext i; fin_cases i <;> simp <;> omega
        omega
      · intro hsub0
        have hPC : P = MvPolynomial.C (P.coeff 0) := sub_eq_zero.mp hsub0
        rw [hPC, MvPolynomial.totalDegree_C] at hP1
        omega
    obtain ⟨hA1_hom, hA1_ne0⟩ := hdecomp1 hA1
    obtain ⟨hB1_hom, hB1_ne0⟩ := hdecomp1 hB1
    let A₁ := A - MvPolynomial.C (A.coeff 0)
    let B₁ := B - MvPolynomial.C (B.coeff 0)
    have hA_eq : A = A₁ + MvPolynomial.C (A.coeff 0) := (sub_add_cancel _ _).symm
    have hB_eq : B = B₁ + MvPolynomial.C (B.coeff 0) := (sub_add_cancel _ _).symm
    have hQ0_coeff : Q.coeff 0 = 0 := hQ.2.coeff_eq_zero (by simp)
    have hAB0_coeff : (A * B).coeff 0 = A.coeff 0 * B.coeff 0 :=
      map_mul (MvPolynomial.constantCoeff : MvPolynomial (Fin 3) (ZMod 2) →+* ZMod 2) A B
    have hprod_c0 : A.coeff 0 * B.coeff 0 = 0 := by rw [← hAB0_coeff, ← hAB, hQ0_coeff]
    have ha0_eq0 : A.coeff 0 = 0 := by
      by_contra ha0_ne
      rcases zmod2_cases (A.coeff 0) with ha0 | ha1
      · exact ha0_ne ha0
      · have hb0 : B.coeff 0 = 0 := by
          rw [ha1, one_mul] at hprod_c0
          exact hprod_c0
        have hB_only : B = B₁ := by rw [hB_eq, hb0, map_zero, add_zero]
        have hB₁_eq : B₁ = Q - A₁ * B₁ := by
          have : Q = A₁ * B₁ + B₁ := by
            rw [hAB, hA_eq, hB_only, ha1, map_one, add_mul, one_mul]
          linear_combination -this
        obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hB1_ne0
        have hd_deg1 : d.degree = 1 := by
          by_contra hne
          exact hd (hB1_hom.coeff_eq_zero hne)
        have hQ_sub_hom2 : (Q - A₁ * B₁).IsHomogeneous 2 :=
          hQ.2.sub (hA1_hom.mul hB1_hom)
        have h0_coeff : (Q - A₁ * B₁).coeff d = 0 :=
          hQ_sub_hom2.coeff_eq_zero (by omega)
        rw [← hB₁_eq] at h0_coeff
        exact hd h0_coeff
    have hb0_eq0 : B.coeff 0 = 0 := by
      by_contra hb0_ne
      rcases zmod2_cases (B.coeff 0) with hb0 | hb1
      · exact hb0_ne hb0
      · have hA_only : A = A₁ := by rw [hA_eq, ha0_eq0, map_zero, add_zero]
        have hA₁_eq : A₁ = Q - A₁ * B₁ := by
          have : Q = A₁ * B₁ + A₁ := by
            rw [hAB, hA_only, hB_eq, hb1, map_one, mul_add, mul_one]
          linear_combination -this
        obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hA1_ne0
        have hd_deg1 : d.degree = 1 := by
          by_contra hne
          exact hd (hA1_hom.coeff_eq_zero hne)
        have hQ_sub_hom2 : (Q - A₁ * B₁).IsHomogeneous 2 :=
          hQ.2.sub (hA1_hom.mul hB1_hom)
        have h0_coeff : (Q - A₁ * B₁).coeff d = 0 :=
          hQ_sub_hom2.coeff_eq_zero (by omega)
        rw [← hA₁_eq] at h0_coeff
        exact hd h0_coeff
    have hA_only : A = A₁ := by rw [hA_eq, ha0_eq0, map_zero, add_zero]
    have hB_only : B = B₁ := by rw [hB_eq, hb0_eq0, map_zero, add_zero]
    exact ⟨A, B, ⟨hA0, hA_only ▸ hA1_hom⟩, ⟨hB0, hB_only ▸ hB1_hom⟩, hAB⟩
  · rintro ⟨L₁, L₂, hL₁, hL₂, rfl⟩ hirr
    rcases hirr.isUnit_or_isUnit rfl with h1 | h2
    · exact (isHomogLinZ2_irreducible hL₁).not_isUnit h1
    · exact (isHomogLinZ2_irreducible hL₂).not_isUnit h2

noncomputable instance instFintypeHomogLinZ2 :
    Fintype {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L} :=
  Fintype.ofEquiv _ homogLinZ2Equiv.symm

noncomputable instance instFintypeHomogQuadZ2 :
    Fintype {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} :=
  Fintype.ofEquiv _ homogQuadZ2Equiv.symm

/-- **Exercise 3.23** (§3.7, p. 34): Complete classification and irreducible factorizations of all
homogeneous quadratic polynomials (`IsHomogQuadZ2`) in `ℤ_2[x, y, z]`
(`MvPolynomial (Fin 3) (ZMod 2)`):
- There are `7` non-zero homogeneous linear forms, each irreducible;
- There are `63` non-zero homogeneous quadratic polynomials in total;
- Exactly `28` are reducible, and `homogLinPairMulZ2` gives a bijection from unordered pairs
  `Sym2 {L // IsHomogLinZ2 L}` onto `{Q // IsHomogQuadZ2 Q ∧ ¬ Irreducible Q}`, expressing each
  reducible quadratic uniquely (up to order) as `L₁ * L₂` of two irreducible homogeneous linear
  forms;
- The remaining `63 - 28 = 35` non-zero homogeneous quadratic polynomials (characterized as the
  complement of `Set.range homogLinPairMulZ2`) are themselves irreducible (1-factor products). -/
theorem exercise_3_23 :
    Nat.card {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L} = 7 ∧
    Nat.card {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} = 63 ∧
    (∀ L : MvPolynomial (Fin 3) (ZMod 2), IsHomogLinZ2 L → Irreducible L) ∧
    Function.Injective homogLinPairMulZ2 ∧
    (∀ Q : MvPolynomial (Fin 3) (ZMod 2), IsHomogQuadZ2 Q →
      (Irreducible Q ∨
        ∃! z : Sym2 {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L},
          (homogLinPairMulZ2 z).1 = Q)) ∧
    Nat.card {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ ¬ Irreducible Q} = 28 ∧
    Nat.card {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ Irreducible Q} = 35 := by
  classical
  have hcard_lin : Fintype.card {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L} = 7 := by
    rw [Fintype.card_congr homogLinZ2Equiv, Fintype.card_subtype_compl, Fintype.card_pi]
    simp
  have hcard_quad : Fintype.card {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} = 63 := by
    rw [Fintype.card_congr homogQuadZ2Equiv, Fintype.card_subtype_compl, Fintype.card_pi]
    simp
  have hdichot : ∀ Q : MvPolynomial (Fin 3) (ZMod 2), IsHomogQuadZ2 Q →
      (Irreducible Q ∨
        ∃! z : Sym2 {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L},
          (homogLinPairMulZ2 z).1 = Q) := by
    intro Q hQ
    by_cases hirr : Irreducible Q
    · exact Or.inl hirr
    · right
      obtain ⟨L₁, L₂, hL₁, hL₂, hQ_eq⟩ := (isHomogQuadZ2_not_irreducible_iff hQ).mp hirr
      refine ⟨s(⟨L₁, hL₁⟩, ⟨L₂, hL₂⟩), hQ_eq.symm, fun z hz => ?_⟩
      apply homogLinPairMulZ2_injective
      apply Subtype.ext
      exact hz.trans hQ_eq
  have hequiv_red :
      Sym2 {L : MvPolynomial (Fin 3) (ZMod 2) // IsHomogLinZ2 L} ≃
        {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ ¬ Irreducible Q} := by
    refine Equiv.ofBijective
      (fun z => ⟨(homogLinPairMulZ2 z).1, (homogLinPairMulZ2 z).2, ?_⟩) ⟨?_, ?_⟩
    · induction z using Sym2.ind with
      | _ L₁ L₂ =>
        exact (isHomogQuadZ2_not_irreducible_iff (homogLinPairMulZ2 s(L₁, L₂)).2).mpr
          ⟨L₁.1, L₂.1, L₁.2, L₂.2, rfl⟩
    · intro z₁ z₂ h
      have hval : (homogLinPairMulZ2 z₁).1 = (homogLinPairMulZ2 z₂).1 :=
        congrArg
          (fun x : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ ¬ Irreducible Q} => x.1) h
      exact homogLinPairMulZ2_injective (Subtype.ext hval)
    · rintro ⟨Q, hQ, hred⟩
      obtain ⟨L₁, L₂, hL₁, hL₂, rfl⟩ := (isHomogQuadZ2_not_irreducible_iff hQ).mp hred
      exact ⟨s(⟨L₁, hL₁⟩, ⟨L₂, hL₂⟩), rfl⟩
  have hequiv_sub_red :
      {Q : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} // ¬ Irreducible Q.1} ≃
        {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ ¬ Irreducible Q} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hequiv_sub_irr :
      {Q : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} // Irreducible Q.1} ≃
        {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q ∧ Irreducible Q} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard_red_sub :
      Fintype.card {Q : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} //
        ¬ Irreducible Q.1} = 28 := by
    rw [Fintype.card_congr (hequiv_sub_red.trans hequiv_red.symm), Sym2.card, hcard_lin]
    decide
  have hcard_irr_sub :
      Fintype.card {Q : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} //
        Irreducible Q.1} = 35 := by
    have hcompl := Fintype.card_subtype_compl
      (fun Q : {Q : MvPolynomial (Fin 3) (ZMod 2) // IsHomogQuadZ2 Q} => ¬ Irreducible Q.1)
    simp only [Classical.not_not] at hcompl
    rw [hcompl, hcard_quad, hcard_red_sub]
  refine ⟨?_, ?_, fun _ hL => isHomogLinZ2_irreducible hL,
    homogLinPairMulZ2_injective, hdichot, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, hcard_lin]
  · rw [Nat.card_eq_fintype_card, hcard_quad]
  · rw [← Nat.card_congr hequiv_sub_red, Nat.card_eq_fintype_card, hcard_red_sub]
  · rw [← Nat.card_congr hequiv_sub_irr, Nat.card_eq_fintype_card, hcard_irr_sub]

/-! ## §3.8 The existence of maximal proper ideals (printed pp. 34–35, PDF pp. 42–43) -/

/-- Garling's definition of a *maximal proper ideal* `M` in a ring `R` (§3.4, p. 24; §3.8, p. 34):
`M` is a proper ideal (`M ≠ ⊤`) and whenever `I` is a proper ideal (`I ≠ ⊤`) with `M ≤ I`, we have
`I = M`. -/
def IsGarlingMaximalProperIdeal {R : Type*} [CommRing R] (M : Ideal R) : Prop :=
  M ≠ ⊤ ∧ ∀ I : Ideal R, I ≠ ⊤ → M ≤ I → I = M

/-- Bridge between Garling's `IsGarlingMaximalProperIdeal` and Mathlib's `Ideal.IsMaximal`. -/
theorem isGarlingMaximalProperIdeal_iff {R : Type*} [CommRing R] (M : Ideal R) :
    IsGarlingMaximalProperIdeal M ↔ M.IsMaximal := by
  rw [Ideal.isMaximal_def, IsGarlingMaximalProperIdeal]
  constructor
  · rintro ⟨hne, hmax⟩
    refine ⟨hne, fun I hlt => ?_⟩
    by_contra hItop
    exact hlt.ne' (hmax I hItop hlt.le)
  · rintro ⟨hne, hmax⟩
    refine ⟨hne, fun I hItop hle => ?_⟩
    by_contra hne'
    exact hItop (hmax I (lt_of_le_of_ne hle (Ne.symm hne')))

/-- **Theorem 3.14** (§3.8, p. 34): Suppose that `J` is a proper ideal of a ring `R`. Then there
exists a maximal proper ideal which contains `J`.

Proved explicitly following Garling's Zorn's-lemma argument on `P_J = {I : Ideal R | I ≠ ⊤ ∧ J ≤ I}`
using Chapter 2's `zorn_lemma_set`. -/
theorem theorem_3_14 {R : Type*} [CommRing R] {J : Ideal R} (hJ : J ≠ ⊤) :
    ∃ M : Ideal R, J ≤ M ∧ IsGarlingMaximalProperIdeal M ∧ M.IsMaximal := by
  let P_J : Set (Ideal R) := {I : Ideal R | I ≠ ⊤ ∧ J ≤ I}
  have hJP : J ∈ P_J := ⟨hJ, le_rfl⟩
  have hpo : IsGarlingPartialOrder P_J (· ≤ ·) :=
    ⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ => le_trans, fun _ _ _ _ => le_antisymm⟩
  have hchains : ∀ C : Set (Ideal R), IsGarlingChain P_J (· ≤ ·) C →
      ∃ I₀ : Ideal R, IsGarlingUpperBound P_J (· ≤ ·) C I₀ := by
    rintro C ⟨hCP, ⟨I₁, hI₁C⟩, hCtot⟩
    let I₀ : Ideal R :=
      { carrier := {a : R | ∃ I ∈ C, a ∈ I}
        zero_mem' := ⟨I₁, hI₁C, I₁.zero_mem⟩
        add_mem' := by
          rintro a₁ a₂ ⟨Ia, hIaC, ha₁⟩ ⟨Ib, hIbC, ha₂⟩
          rcases hCtot Ia hIaC Ib hIbC with hab | hba
          · exact ⟨Ib, hIbC, Ib.add_mem (hab ha₁) ha₂⟩
          · exact ⟨Ia, hIaC, Ia.add_mem ha₁ (hba ha₂)⟩
        smul_mem' := by
          rintro r a ⟨Ia, hIaC, ha⟩
          exact ⟨Ia, hIaC, Ia.smul_mem r ha⟩ }
    have hI₀_proper : I₀ ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ I₀ := htop ▸ Submodule.mem_top
      obtain ⟨Ia, hIaC, h1Ia⟩ := h1
      exact (hCP hIaC).1 (Ideal.eq_top_of_isUnit_mem Ia h1Ia isUnit_one)
    have hJI₀ : J ≤ I₀ := (hCP hI₁C).2.trans (fun x hx => ⟨I₁, hI₁C, hx⟩)
    exact ⟨I₀, ⟨hI₀_proper, hJI₀⟩, fun I hIC x hx => ⟨I, hIC, hx⟩⟩
  obtain ⟨M, ⟨hM_proper, hJM⟩, hM_max⟩ := zorn_lemma_set hpo ⟨J, hJP⟩ hchains
  have hGarling : IsGarlingMaximalProperIdeal M :=
    ⟨hM_proper, fun I hI_proper hMI => (hM_max I ⟨hI_proper, hJM.trans hMI⟩ hMI).symm⟩
  exact ⟨M, hJM, hGarling, (isGarlingMaximalProperIdeal_iff M).mp hGarling⟩

/-- Explicit enumeration helper for **Exercise 3.24** (§3.8, p. 34): given a surjective enumeration
`r : ℕ → R` of `R`, constructs a maximal proper ideal containing `J` recursively without Zorn's
lemma. -/
theorem exercise_3_24_of_surjective {R : Type*} [CommRing R] {r : ℕ → R}
    (hr : Function.Surjective r) {J : Ideal R} (hJ : J ≠ ⊤) :
    ∃ M : Ideal R, J ≤ M ∧ IsGarlingMaximalProperIdeal M ∧ M.IsMaximal := by
  classical
  let step : Ideal R → R → Ideal R := fun I x =>
    if I ⊔ Ideal.span {x} ≠ ⊤ then I ⊔ Ideal.span {x} else I
  let chain : ℕ → Ideal R := Nat.rec J (fun n I_n => step I_n (r n))
  have hmono_step : ∀ n : ℕ, chain n ≤ chain (n + 1) := by
    intro n
    change chain n ≤ step (chain n) (r n)
    dsimp only [step]
    split_ifs
    · exact le_sup_left
    · exact le_rfl
  have hmono : ∀ {m n : ℕ}, m ≤ n → chain m ≤ chain n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono_step _)
  have hproper : ∀ n : ℕ, chain n ≠ ⊤ := by
    intro n
    induction n with
    | zero => exact hJ
    | succ n ih =>
      change step (chain n) (r n) ≠ ⊤
      dsimp only [step]
      split_ifs with hne
      · exact hne
      · exact ih
  let M : Ideal R :=
    { carrier := {x : R | ∃ n : ℕ, x ∈ chain n}
      zero_mem' := ⟨0, J.zero_mem⟩
      add_mem' := by
        rintro x y ⟨m, hx⟩ ⟨n, hy⟩
        exact ⟨max m n, (chain (max m n)).add_mem
          (hmono (le_max_left m n) hx) (hmono (le_max_right m n) hy)⟩
      smul_mem' := by
        rintro c x ⟨n, hx⟩
        exact ⟨n, (chain n).smul_mem c hx⟩ }
  have hJM : J ≤ M := fun x hx => ⟨0, hx⟩
  have hM_proper : M ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ M := htop ▸ Submodule.mem_top
    obtain ⟨n, h1n⟩ := h1
    exact hproper n (Ideal.eq_top_of_isUnit_mem (chain n) h1n isUnit_one)
  have hGarling : IsGarlingMaximalProperIdeal M := by
    refine ⟨hM_proper, fun I hItop hMI => le_antisymm ?_ hMI⟩
    intro y hyI
    obtain ⟨n, rfl⟩ := hr y
    have hle_I : chain n ⊔ Ideal.span {r n} ≤ I :=
      sup_le (fun z hz => hMI ⟨n, hz⟩)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hyI))
    have hspan_proper : chain n ⊔ Ideal.span {r n} ≠ ⊤ := by
      intro htop
      apply hItop
      exact top_unique (htop ▸ hle_I)
    have hrn_step : r n ∈ chain (n + 1) := by
      change r n ∈ step (chain n) (r n)
      dsimp only [step]
      rw [ite_eq_left_iff.mpr (fun hn => absurd hspan_proper hn)]
      exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton (r n)))
    exact ⟨n + 1, hrn_step⟩
  exact ⟨M, hJM, hGarling, (isGarlingMaximalProperIdeal_iff M).mp hGarling⟩

/-- **Exercise 3.24** (§3.8, p. 34): Prove Theorem 3.14 in the case where `R` has countably many
elements, without using Zorn's lemma. -/
theorem exercise_3_24 {R : Type*} [CommRing R] [Countable R] {J : Ideal R} (hJ : J ≠ ⊤) :
    ∃ M : Ideal R, J ≤ M ∧ IsGarlingMaximalProperIdeal M ∧ M.IsMaximal := by
  have _ : Nonempty R := ⟨0⟩
  obtain ⟨r, hr⟩ := exists_surjective_nat R
  exact exercise_3_24_of_surjective hr hJ

/-- **Exercise 3.25** (§3.8, p. 34): An element of a ring `R` is invertible if and only if it is
contained in no maximal proper ideal in `R`. -/
theorem exercise_3_25 {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (IsUnit a ↔ ∀ M : Ideal R, IsGarlingMaximalProperIdeal M → a ∉ M) ∧
    (IsUnit a ↔ ∀ M : Ideal R, M.IsMaximal → a ∉ M) := by
  have hmain : IsUnit a ↔ ∀ M : Ideal R, IsGarlingMaximalProperIdeal M → a ∉ M := by
    constructor
    · intro hu M hM haM
      exact hM.1 (Ideal.eq_top_of_isUnit_mem M haM hu)
    · intro hall
      by_contra hnu
      have hproper : Ideal.span ({a} : Set R) ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hnu
      obtain ⟨M, haM, hM, _⟩ := theorem_3_14 hproper
      exact hall M hM (haM (Ideal.subset_span (Set.mem_singleton a)))
  refine ⟨hmain, hmain.trans ?_⟩
  constructor
  · intro h M hM
    exact h M ((isGarlingMaximalProperIdeal_iff M).mpr hM)
  · intro h M hM
    exact h M ((isGarlingMaximalProperIdeal_iff M).mp hM)

/-- The polynomial ideal `J[x]` in `R[x]` consisting of polynomials whose coefficients all lie in
`J` (§3.8, Ex. 3.26, p. 35). -/
def polyIdeal {R : Type*} [CommRing R] (J : Ideal R) : Ideal R[X] where
  carrier := {f : R[X] | ∀ n : ℕ, f.coeff n ∈ J}
  zero_mem' _ := by simp [J.zero_mem]
  add_mem' {f g} hf hg n := by
    rw [Polynomial.coeff_add]
    exact J.add_mem (hf n) (hg n)
  smul_mem' c {f} hf n := by
    rw [smul_eq_mul, Polynomial.coeff_mul]
    exact J.sum_mem (fun p _ => J.mul_mem_left (c.coeff p.1) (hf p.2))

theorem polyIdeal_eq_ker {R : Type*} [CommRing R] (J : Ideal R) :
    polyIdeal J = RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk J)) := by
  ext f
  rw [RingHom.mem_ker, Polynomial.ext_iff]
  change (∀ n : ℕ, f.coeff n ∈ J) ↔
    ∀ n : ℕ, (Polynomial.mapRingHom (Ideal.Quotient.mk J) f).coeff n = 0
  simp [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]

/-- **Exercise 3.26** (§3.8, p. 35): Suppose that `J` is a proper prime ideal in an integral domain
`R`. Then `J[x]` (`polyIdeal J`) is a proper prime ideal in `R[x]`, and `J[x]` is not a maximal
proper ideal in `R[x]`. -/
theorem exercise_3_26 {R : Type*} [CommRing R] [IsDomain R] {J : Ideal R}
    (hJ : IsGarlingPrimeIdeal J) :
    IsGarlingPrimeIdeal (polyIdeal J) ∧ (polyIdeal J).IsPrime ∧
    ¬ IsGarlingMaximalProperIdeal (polyIdeal J) ∧ ¬ (polyIdeal J).IsMaximal := by
  have hJp : J.IsPrime := (isGarlingPrimeIdeal_iff J).mp hJ
  have _ : IsDomain (R ⧸ J) := (Ideal.Quotient.isDomain_iff_prime J).mpr hJp
  let ψ : R[X] →+* (R ⧸ J)[X] := Polynomial.mapRingHom (Ideal.Quotient.mk J)
  have hpoly_prime : (polyIdeal J).IsPrime := by
    rw [polyIdeal_eq_ker]
    refine ⟨?_, fun {f g} hfg => ?_⟩
    · intro htop
      have h1 : (1 : R[X]) ∈ RingHom.ker ψ := htop ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    · rw [RingHom.mem_ker, map_mul] at hfg
      rcases mul_eq_zero.mp hfg with hf | hg
      · exact Or.inl hf
      · exact Or.inr hg
  let K : Ideal R[X] :=
    { carrier := {f : R[X] | f.coeff 0 ∈ J}
      zero_mem' := by simp [J.zero_mem]
      add_mem' := fun {f g} hf hg => by
        change (f + g).coeff 0 ∈ J
        rw [Polynomial.coeff_add]
        exact J.add_mem hf hg
      smul_mem' := fun c {f} hf => by
        change (c * f).coeff 0 ∈ J
        rw [Polynomial.mul_coeff_zero]
        exact J.mul_mem_left (c.coeff 0) hf }
  have hK_proper : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : R[X]) ∈ K := htop ▸ Submodule.mem_top
    change (1 : R[X]).coeff 0 ∈ J at h1
    simp only [Polynomial.coeff_one_zero] at h1
    exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J h1 isUnit_one)
  have hle_K : polyIdeal J ≤ K := fun f hf => hf 0
  have hX_K : (Polynomial.X : R[X]) ∈ K := by
    change (Polynomial.X : R[X]).coeff 0 ∈ J
    simp [J.zero_mem]
  have hX_not_poly : (Polynomial.X : R[X]) ∉ polyIdeal J := by
    intro hX
    have h1J : (1 : R) ∈ J := by simpa using hX 1
    exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J h1J isUnit_one)
  have hnot_max : ¬ IsGarlingMaximalProperIdeal (polyIdeal J) := by
    intro hmax
    have heq : K = polyIdeal J := hmax.2 K hK_proper hle_K
    exact hX_not_poly (heq ▸ hX_K)
  exact ⟨(isGarlingPrimeIdeal_iff _).mpr hpoly_prime, hpoly_prime, hnot_max,
    fun hm => hnot_max ((isGarlingMaximalProperIdeal_iff _).mpr hm)⟩

/-! ## §3.9 More about fields (printed pp. 35–36, PDF pp. 43–44) -/

/-- **Theorem 3.15** (§3.9, p. 35): A ring `R` (`1 ≠ 0`) is a field if and only if `{0}` (`⊥`) and
`R` (`⊤`) are the only ideals in `R`. -/
theorem theorem_3_15 {R : Type*} [CommRing R] [Nontrivial R] :
    IsField R ↔ ∀ I : Ideal R, I = ⊥ ∨ I = ⊤ := by
  constructor
  · intro hf I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨b, hab⟩ := hf.mul_inv_cancel ha0
      have h1I : (1 : R) ∈ I := hab ▸ I.mul_mem_right b haI
      exact Ideal.eq_top_of_isUnit_mem I h1I isUnit_one
  · intro hall
    refine ⟨exists_pair_ne R, mul_comm, fun {a} ha0 => ?_⟩
    have hne_bot : Ideal.span ({a} : Set R) ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
    have htop : Ideal.span ({a} : Set R) = ⊤ := (hall (Ideal.span {a})).resolve_left hne_bot
    have h1 : (1 : R) ∈ Ideal.span ({a} : Set R) := htop ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h1
    exact ⟨b, hb.symm⟩

/-- Prose corollary noted after Theorem 3.15 (§3.9, p. 35): If `ϕ` is a ring homomorphism from a
field `K` into a ring `R` (`1 ≠ 0`), then `ker ϕ` is a proper ideal of `K` (`= {0}`) and `ϕ` is
injective. -/
theorem field_ringHom_injective {K R : Type*} [Field K] [CommRing R] [Nontrivial R]
    (ϕ : K →+* R) :
    RingHom.ker ϕ = ⊥ ∧ Function.Injective ϕ := by
  have hproper : RingHom.ker ϕ ≠ ⊤ := by
    intro htop
    have h1 : (1 : K) ∈ RingHom.ker ϕ := htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hbot : RingHom.ker ϕ = ⊥ :=
    (theorem_3_15.mp (Field.toIsField K) (RingHom.ker ϕ)).resolve_right hproper
  exact ⟨hbot, (RingHom.injective_iff_ker_eq_bot ϕ).mpr hbot⟩

/-- **Theorem 3.16** (§3.9, p. 35): If `J` is a proper ideal in a ring `R`, then `R / J` is a field
if and only if `J` is a maximal proper ideal in `R`. -/
theorem theorem_3_16 {R : Type*} [CommRing R] {J : Ideal R} (hJ : J ≠ ⊤) :
    (IsField (R ⧸ J) ↔ IsGarlingMaximalProperIdeal J) ∧
    (IsField (R ⧸ J) ↔ J.IsMaximal) := by
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hnt : Nontrivial (R ⧸ J) :=
    ⟨⟨1, 0, fun h10 => hJ (Ideal.eq_top_of_isUnit_mem J
      (Ideal.Quotient.eq_zero_iff_mem.mp h10) isUnit_one)⟩⟩
  have hmain : IsField (R ⧸ J) ↔ IsGarlingMaximalProperIdeal J := by
    constructor
    · intro hf
      refine ⟨hJ, fun I hItop hJI => ?_⟩
      by_contra hIJ
      have hex : ∃ a ∈ I, a ∉ J := by
        by_contra hall
        apply hIJ
        exact le_antisymm (fun x hx => by_contra fun hnx => hall ⟨x, hx, hnx⟩) hJI
      obtain ⟨a, haI, haJ⟩ := hex
      have hqa0 : q a ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp haJ
      obtain ⟨y, hqy⟩ := hf.mul_inv_cancel hqa0
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have habJ : a * b - 1 ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change q (a * b - 1) = 0
        rw [map_sub, map_mul, map_one, hqy, sub_self]
      have h1I : (1 : R) ∈ I := by
        have hsub : a * b - (a * b - 1) ∈ I := I.sub_mem (I.mul_mem_right b haI) (hJI habJ)
        simpa using hsub
      exact hItop (Ideal.eq_top_of_isUnit_mem I h1I isUnit_one)
    · intro hmax
      rw [@theorem_3_15 (R ⧸ J) _ hnt]
      intro I
      let I' : Ideal R := I.comap q
      have hJI' : J ≤ I' := by
        intro x hx
        rw [Ideal.mem_comap]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact I.zero_mem
      by_cases hI'top : I' = ⊤
      · right
        have h1I' : (1 : R) ∈ I' := hI'top ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h1I'
        exact Ideal.eq_top_of_isUnit_mem I h1I' isUnit_one
      · left
        have hI'J : I' = J := hmax.2 I' hI'top hJI'
        rw [eq_bot_iff]
        intro y hyI
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hxI' : x ∈ I' := hyI
        rw [hI'J] at hxI'
        change q x ∈ (⊥ : Ideal (R ⧸ J))
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hxI']
        exact Submodule.zero_mem _
  exact ⟨hmain, hmain.trans (isGarlingMaximalProperIdeal_iff J)⟩

/-- **Corollary** [to Theorem 3.16] (§3.9, p. 35): If `a` is a non-zero non-unit element of a
principal ideal domain `R`, then `R / (a)` is a field if and only if `a` is irreducible. -/
theorem corollary_to_theorem_3_16 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {a : R} (ha0 : a ≠ 0) (hau : ¬ IsUnit a) :
    IsField (R ⧸ Ideal.span {a}) ↔ Irreducible a := by
  have hproper : Ideal.span ({a} : Set R) ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hau
  rw [(theorem_3_16 hproper).1, theorem_3_2 ha0]
  constructor
  · rintro ⟨hne, hmax⟩
    exact ⟨⟨IsPrincipalIdealRing.principal _, hne⟩, fun J ⟨_, hJtop⟩ hle => hmax J hJtop hle⟩
  · rintro ⟨⟨_, hne⟩, hmax⟩
    exact ⟨hne, fun J hJtop hle => hmax J ⟨IsPrincipalIdealRing.principal J, hJtop⟩ hle⟩

/-- Prose consequence noted after Corollary to Theorem 3.16 (§3.9, p. 35): `ℤ_n` (`ZMod n`) is a
field if and only if `n` is a prime number. -/
theorem zmod_isField_iff_prime (n : ℕ) :
    IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro hf
    rcases eq_or_ne n 0 with rfl | hn0
    · change IsField ℤ at hf
      obtain ⟨b, hb⟩ := hf.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
      omega
    · let _ : Field (ZMod n) := hf.toField
      exact (exercise_3_6 (ZMod n) n (Nat.pos_of_ne_zero hn0)).1
  · intro hp
    have _ : Fact (Nat.Prime n) := ⟨hp⟩
    exact Field.toIsField (ZMod n)

/-- Garling's *prime subfield* of a field `K` (§3.9, p. 35): the intersection of all subfields of
`K`, i.e., the smallest subfield of `K`. -/
def primeSubfield (K : Type*) [Field K] : Subfield K :=
  sInf Set.univ

theorem primeSubfield_eq_bot (K : Type*) [Field K] :
    primeSubfield K = ⊥ :=
  sInf_univ

/-- **Theorem 3.17** (§3.9, p. 36): Suppose that `K` is a field. If `K` has characteristic `0`, the
prime subfield of `K` is isomorphic to `ℚ`. Otherwise, `K` has prime characteristic `p = ringChar K`,
and the prime subfield of `K` is isomorphic to `ℤ_p` (`ZMod (ringChar K)`). -/
theorem theorem_3_17 (K : Type*) [Field K] :
    (ringChar K = 0 → Nonempty (primeSubfield K ≃+* ℚ)) ∧
    (ringChar K ≠ 0 →
      Nat.Prime (ringChar K) ∧ Nonempty (primeSubfield K ≃+* ZMod (ringChar K))) := by
  constructor
  · intro hc0
    have _ : CharP K 0 := hc0 ▸ inferInstance
    have _ : CharZero K := CharP.charP_to_charZero K
    let f : ℚ →+* K := Rat.castHom K
    have hf_mem : ∀ q : ℚ, f q ∈ primeSubfield K := by
      intro q
      rw [primeSubfield, Subfield.mem_sInf]
      intro S _
      change (q : K) ∈ S
      rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      exact S.div_mem (S.intCast_mem q.num) (by simp)
    let φ : ℚ →+* primeSubfield K :=
      { toFun := fun q => ⟨f q, hf_mem q⟩
        map_one' := Subtype.ext f.map_one
        map_mul' := fun x y => Subtype.ext (f.map_mul x y)
        map_zero' := Subtype.ext f.map_zero
        map_add' := fun x y => Subtype.ext (f.map_add x y) }
    have hinj : Function.Injective φ :=
      fun x y h => f.injective (congrArg Subtype.val h)
    have hsurj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      have hy_range : y ∈ f.fieldRange :=
        Subfield.mem_sInf.mp hy f.fieldRange (Set.mem_univ _)
      obtain ⟨q, rfl⟩ := hy_range
      exact ⟨q, rfl⟩
    exact ⟨(RingEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩
  · intro hcnz
    have hp : Nat.Prime (ringChar K) :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hcnz
    have _ : Fact (Nat.Prime (ringChar K)) := ⟨hp⟩
    let f : ZMod (ringChar K) →+* K := ZMod.castHom (dvd_refl (ringChar K)) K
    have hf_mem : ∀ x : ZMod (ringChar K), f x ∈ primeSubfield K := by
      intro x
      rw [primeSubfield, Subfield.mem_sInf]
      intro S _
      rw [← ZMod.natCast_zmod_val x, map_natCast]
      simpa using S.intCast_mem (x.val : ℤ)
    let φ : ZMod (ringChar K) →+* primeSubfield K :=
      { toFun := fun x => ⟨f x, hf_mem x⟩
        map_one' := Subtype.ext f.map_one
        map_mul' := fun x y => Subtype.ext (f.map_mul x y)
        map_zero' := Subtype.ext f.map_zero
        map_add' := fun x y => Subtype.ext (f.map_add x y) }
    have hinj : Function.Injective φ :=
      fun x y h => f.injective (congrArg Subtype.val h)
    have hsurj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      have hy_range : y ∈ f.fieldRange :=
        Subfield.mem_sInf.mp hy f.fieldRange (Set.mem_univ _)
      obtain ⟨x, rfl⟩ := hy_range
      exact ⟨x, rfl⟩
    exact ⟨hp, ⟨(RingEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩⟩

/-- **Exercise 3.27** (§3.9, p. 36): Let `R = RatLocalAtPrime p hp` be the ring of Exercise 3.17
(`{r / s ∈ ℚ : p ∤ s}` for a prime `p`).
(1) A quotient ring `R / J` is a field if and only if `J = (p)`, so `R / (p)` is the unique
    quotient ring of `R` that is a field;
(2) `R / (p)` is isomorphic to `ℤ_p` (`ZMod p`);
(3) Under the alternative reading of "quotient field" as field of fractions, `Frac(R)` is
    isomorphic to `ℚ`. -/
theorem exercise_3_27 (p : ℕ) (hp : Nat.Prime p) :
    (∀ J : Ideal (RatLocalAtPrime p hp),
      IsField (RatLocalAtPrime p hp ⧸ J) ↔
        J = Ideal.span {(p : RatLocalAtPrime p hp)}) ∧
    Nonempty ((RatLocalAtPrime p hp ⧸ Ideal.span {(p : RatLocalAtPrime p hp)}) ≃+* ZMod p) ∧
    Nonempty (FractionRing (RatLocalAtPrime p hp) ≃+* ℚ) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  let R := RatLocalAtPrime p hp
  have hp_nu : ¬ IsUnit (p : R) := by
    rw [ratLocalAtPrime_isUnit_iff]
    rintro ⟨r, s, hr, hs, hpeq⟩
    have hs0 : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (fun h0 => hs (h0 ▸ dvd_zero (p : ℤ)))
    have hq : (p : ℚ) * (s : ℚ) = (r : ℚ) := (eq_div_iff hs0).mp hpeq
    have hz : (p : ℤ) * s = r := by exact_mod_cast hq
    exact hr ⟨s, hz.symm⟩
  have hp_proper : Ideal.span ({(p : R)} : Set R) ≠ ⊤ :=
    mt Ideal.span_singleton_eq_top.mp hp_nu
  have hle_span_p : ∀ I : Ideal R, I ≠ ⊤ → I ≤ Ideal.span {(p : R)} := by
    intro I hItop x hxI
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    · obtain ⟨k, u, hu, rfl⟩ := ratLocalAtPrime_eq_pow_mul_unit hp hx0
      rcases eq_or_ne k 0 with rfl | hk0
      · simp only [pow_zero, one_mul] at hxI
        exact False.elim (hItop (Ideal.eq_top_of_isUnit_mem I hxI hu))
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [Ideal.mem_span_singleton]
        exact ⟨(p : R) ^ d * u, by rw [pow_succ', mul_assoc]⟩
  have hp_max : IsGarlingMaximalProperIdeal (Ideal.span {(p : R)}) :=
    ⟨hp_proper, fun I hItop hle => le_antisymm (hle_span_p I hItop) hle⟩
  have hpart1 : ∀ J : Ideal R, IsField (R ⧸ J) ↔ J = Ideal.span {(p : R)} := by
    intro J
    constructor
    · intro hf
      have hJ_proper : J ≠ ⊤ := by
        intro htop
        subst htop
        rcases hf.exists_pair_ne with ⟨x, y, hxy⟩
        exact hxy (Subsingleton.elim x y)
      have hJ_max : IsGarlingMaximalProperIdeal J := (theorem_3_16 hJ_proper).1.mp hf
      exact (hJ_max.2 (Ideal.span {(p : R)}) hp_proper (hle_span_p J hJ_proper)).symm
    · rintro rfl
      exact (theorem_3_16 hp_proper).1.mpr hp_max
  have hpart2 : Nonempty ((R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p) := by
    let F := R ⧸ Ideal.span {(p : R)}
    let q : R →+* F := Ideal.Quotient.mk (Ideal.span {(p : R)})
    have _ : Nontrivial F :=
      ⟨⟨1, 0, fun h10 => hp_proper (Ideal.eq_top_of_isUnit_mem _
        (Ideal.Quotient.eq_zero_iff_mem.mp h10) isUnit_one)⟩⟩
    have hchar : CharP F p :=
      { cast_eq_zero_iff := fun n => by
          change q (n : R) = 0 ↔ p ∣ n
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          constructor
          · rintro ⟨y, hy⟩
            obtain ⟨r, s, hs, hyq⟩ := y.2
            have hs0 : (s : ℚ) ≠ 0 :=
              Int.cast_ne_zero.mpr (fun h0 => hs (h0 ▸ dvd_zero (p : ℤ)))
            have hq_eq : (n : ℚ) = (p : ℚ) * ((r : ℚ) / (s : ℚ)) := by
              have hval := congrArg Subtype.val hy
              simpa [hyq] using hval
            have hmul_q : (n : ℚ) * (s : ℚ) = (p : ℚ) * (r : ℚ) := by
              rw [hq_eq, mul_assoc, div_mul_cancel₀ _ hs0]
            have hmul_z : (n : ℤ) * s = (p : ℤ) * r := by exact_mod_cast hmul_q
            have hdvd_ns : (p : ℤ) ∣ (n : ℤ) * s := ⟨r, hmul_z⟩
            have hdvd_n : (p : ℤ) ∣ (n : ℤ) :=
              (natPrime_int_dvd_or_dvd hp hdvd_ns).resolve_right hs
            exact Int.natCast_dvd_natCast.mp hdvd_n
          · rintro ⟨m, rfl⟩
            exact ⟨(m : R), by push_cast; rfl⟩ }
    let φ : ZMod p →+* F := @ZMod.castHom p p (dvd_refl p) F _ hchar
    have hinj : Function.Injective φ := φ.injective
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨r, s, hs, hxq⟩ := x.2
      have hs0_q : (s : ℚ) ≠ 0 :=
        Int.cast_ne_zero.mpr (fun h0 => hs (h0 ▸ dvd_zero (p : ℤ)))
      have hx_mul_s : x * (s : R) = (r : R) := by
        apply Subtype.ext
        change (x : ℚ) * (s : ℚ) = (r : ℚ)
        rw [hxq, div_mul_cancel₀ _ hs0_q]
      have hs_unit : IsUnit (s : R) :=
        (ratLocalAtPrime_isUnit_iff hp (s : R)).mpr
          ⟨s, 1, hs, fun h => hp.ne_one (Nat.dvd_one.mp (Int.ofNat_dvd_left.mp h)), by simp⟩
      obtain ⟨us, hus⟩ := hs_unit
      have hs_zmod : (s : ZMod p) ≠ 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd s p).not.mpr hs
      let c : ZMod p := (r : ZMod p) * (s : ZMod p)⁻¹
      have hc_mul : c * (s : ZMod p) = (r : ZMod p) := inv_mul_cancel_right₀ hs_zmod (r : ZMod p)
      refine ⟨c, ?_⟩
      have hmul_F : φ c * q (s : R) = q x * q (s : R) := by
        have hφs : φ (s : ZMod p) = q (s : R) := by simp [φ, q]
        have hφr : φ (r : ZMod p) = q (r : R) := by simp [φ, q]
        calc φ c * q (s : R) = φ c * φ (s : ZMod p) := by rw [hφs]
          _ = φ (c * (s : ZMod p)) := (φ.map_mul _ _).symm
          _ = φ (r : ZMod p) := by rw [hc_mul]
          _ = q (r : R) := hφr
          _ = q (x * (s : R)) := by rw [hx_mul_s]
          _ = q x * q (s : R) := q.map_mul x (s : R)
      have hinv := congrArg (fun w : F => w * q (↑us⁻¹ : R)) hmul_F
      rw [mul_assoc, ← q.map_mul, ← hus, Units.mul_inv, map_one, mul_one,
        mul_assoc, ← q.map_mul, Units.mul_inv, map_one, mul_one] at hinv
      exact hinv
    exact ⟨(RingEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩
  have hpart3 : Nonempty (FractionRing R ≃+* ℚ) := by
    let _ : Algebra R (FractionRing R) := inferInstance
    let φ : FractionRing R →+* ℚ :=
      IsFractionRing.lift (A := R) (K := FractionRing R) (g := R.subtype) Subtype.val_injective
    have hinj : Function.Injective φ := φ.injective
    have hsurj : Function.Surjective φ := by
      intro q
      let a : R := (q.num : R)
      let b : R := (q.den : R)
      refine ⟨algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b, ?_⟩
      rw [map_div₀]
      have ha : φ (algebraMap R (FractionRing R) a) = (q.num : ℚ) :=
        IsFractionRing.lift_algebraMap Subtype.val_injective a
      have hb : φ (algebraMap R (FractionRing R) b) = (q.den : ℚ) :=
        IsFractionRing.lift_algebraMap Subtype.val_injective b
      rw [ha, hb, Rat.num_div_den]
    exact ⟨RingEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩
  exact ⟨hpart1, hpart2, hpart3⟩

end Garling.Chapter03
