import Garling.Chapter01
import Garling.Chapter04
import Garling.Chapter06
import Garling.Chapter07
import Garling.Chapter10
import Garling.Chapter11
import Garling.Chapter14
import Garling.Chapter15
import Garling.Chapter17
import Garling.Chapter18
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum.Prime

/-!
# Chapter 19: Some further topics

Formalization of Chapter 19 (*Some further topics*, printed pp. 147–154 / PDF pp. 155–162) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986).

## Structure (verified against the 1986 CUP scan)
- **§19.1 Generic polynomials** (pp. 147–150 / PDF pp. 155–158):
  `Theorem 19.1`, `Corollary` [to `Theorem 19.1`], `Theorem 19.2`, `Theorem 19.3`,
  `Theorem 19.4`, `Corollary` [to `Theorem 19.4`], `Exercise 19.1`, `Exercise 19.2`,
  plus inline prose definitions and derivations (generic monic polynomial, elementary symmetric
  polynomials `s_1, …, s_n`, symmetric polynomials, tower `M_j` degrees/minimal polynomials and
  unique multi-index expansion, `ℤ`-integrality remark, lexicographic order and principal term).
- **§19.2 The normal basis theorem** (pp. 150–152 / PDF pp. 158–160):
  `Theorem 19.5`, `Theorem 19.6 (The normal basis theorem)`, `Exercise 19.3`,
  plus normal-basis definitions.
- **§19.3 Constructing regular polygons** (pp. 152–154 / PDF pp. 160–162):
  `Theorem 19.7`, `Theorem 19.8`, `Theorem 19.9 (Gauss)`,
  plus *possible* (`n > 2`), small-`n` examples, angle/coprime/divisor reductions, complex
  quadratic-tower constructibility, *Fermat primes* (`k ≥ 1`), and `2^k + 1` prime `⇒ k = 2^l`.
-/

open scoped Polynomial IntermediateField
open Garling.Chapter01 Garling.Chapter03 Garling.Chapter04 Garling.Chapter06
  Garling.Chapter07 Garling.Chapter10 Garling.Chapter11 Garling.Chapter14
  Garling.Chapter15 Garling.Chapter17 Garling.Chapter18

namespace Garling.Chapter19

universe u v w

/-! ## §19.1 Generic polynomials (printed pp. 147–150 / PDF pp. 155–158) -/

/-! ### Inline prose definitions: generic polynomial, elementary symmetric polynomials, and `G` -/

/-- Garling's inline prose definition of the *elementary symmetric polynomials in `n` variables*
`s₁, …, sₙ ∈ R[t₁, …, tₙ]` (§19.1, printed pp. 147–148 / PDF pp. 155–156), indexed by `k : Fin n`
so that `k = 0` is `s₁ = t₁ + ⋯ + tₙ` and `k = n - 1` is `sₙ = t₁ ⋯ tₙ`. -/
noncomputable def elemSymmPoly (R : Type*) [CommRing R] (n : ℕ) (k : Fin n) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.esymm (Fin n) R (k.1 + 1)

/-- Elementary symmetric values `s₁(t), …, sₙ(t) ∈ E` evaluated at a tuple `t : Fin n → E`. -/
noncomputable def elemSymmVal (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) (k : Fin n) : E :=
  evalMvRingHom K t (elemSymmPoly K n k)

/-- Garling's inline prose definition of the *generic (monic) polynomial of degree `n`*
`xⁿ - a₁ x^{n-1} + ⋯ + (-1)ⁿ aₙ ∈ R[x]` (§19.1, printed p. 147 / PDF p. 155). -/
noncomputable def garlingGenericPoly {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) : R[X] :=
  Polynomial.X ^ n +
    ∑ k : Fin n, Polynomial.C ((-1 : R) ^ (k.1 + 1) * a k) * Polynomial.X ^ (n - 1 - k.1)

/-- The polynomial with general roots `f = (x - t₁)⋯(x - tₙ)` (§19.1, printed p. 147 /
PDF p. 155; deleted by OCR in `garling1986_pages.txt`). -/
noncomputable def generalRootsPoly {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) : R[X] :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))

/-- Explicit formulas for `s₁`, `s₂`, and `sₙ` displayed on printed p. 148 (PDF p. 156):
`s₁ = t₁ + ⋯ + tₙ`, `s₂ = ∑_{i < j} t_i t_j`, and `sₙ = t₁ ⋯ tₙ`. -/
theorem elemSymmPoly_explicit (R : Type*) [CommRing R] :
    (∀ {n : ℕ} (h1 : 0 < n),
      elemSymmPoly R n ⟨0, h1⟩ = ∑ i : Fin n, MvPolynomial.X i) ∧
    (∀ {n : ℕ} (h2 : 1 < n),
      elemSymmPoly R n ⟨1, h2⟩ =
        ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
          MvPolynomial.X p.1 * MvPolynomial.X p.2) ∧
    (∀ {n : ℕ} (hpos : 0 < n),
      elemSymmPoly R n ⟨n - 1, Nat.sub_lt hpos Nat.one_pos⟩ =
        ∏ i : Fin n, MvPolynomial.X i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n h1
    simp [elemSymmPoly, MvPolynomial.esymm_one]
  · intro n h2
    change MvPolynomial.esymm (Fin n) R 2 = _
    rw [MvPolynomial.esymm]
    let S := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
    refine (Finset.sum_bij (fun (p : Fin n × Fin n) (_ : p ∈ S) => ({p.1, p.2} : Finset (Fin n)))
      ?_ ?_ ?_ ?_).symm
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt hlt)⟩
    · intro p hp q hq hpq
      have hp_lt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hq_lt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
      have h1 : p.1 ∈ ({q.1, q.2} : Finset (Fin n)) := hpq ▸ Finset.mem_insert_self _ _
      have h2 : p.2 ∈ ({q.1, q.2} : Finset (Fin n)) :=
        hpq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (ne_of_lt hp_lt)
      · exact Prod.ext h1 h2
      · omega
      · exact absurd (h1.trans h2.symm) (ne_of_lt hp_lt)
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht.2
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, Finset.pair_comm b a⟩
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      rw [Finset.prod_pair (ne_of_lt hlt)]
  · intro n hpos
    change MvPolynomial.esymm (Fin n) R (n - 1 + 1) = _
    rw [Nat.sub_add_cancel hpos, MvPolynomial.esymm]
    have hps : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
      have hcard : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
      simpa [hcard] using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rw [hps, Finset.sum_singleton]

theorem garlingGenericPoly_monic {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (garlingGenericPoly a).Monic := by
  unfold garlingGenericPoly
  apply Polynomial.monic_X_pow_add
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  have hlt : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (Polynomial.C ((-1 : R) ^ (k.1 + 1) * a k) * Polynomial.X ^ (n - 1 - k.1)).degree < (n : WithBot ℕ) := by
    intro k _
    have hk := k.2
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (Nat.cast_lt.mpr (show n - 1 - k.1 < n by omega))
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr hlt

theorem garlingGenericPoly_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) :
    (garlingGenericPoly a).natDegree = n := by
  by_cases hn : n = 0
  · subst hn; simp [garlingGenericPoly]
  · unfold garlingGenericPoly
    set tail : R[X] :=
      ∑ k : Fin n, Polynomial.C ((-1 : R) ^ (k.1 + 1) * a k) * Polynomial.X ^ (n - 1 - k.1)
    by_cases htail : tail = 0
    · rw [htail, add_zero, Polynomial.natDegree_X_pow]
    · have hlt : tail.natDegree < (Polynomial.X ^ n : R[X]).natDegree := by
        rw [Polynomial.natDegree_X_pow]
        have hdeg : tail.degree < (n : WithBot ℕ) := by
          refine (Polynomial.degree_sum_le _ _).trans_lt ?_
          exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k _ => by
            have hk := k.2
            exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
              (Nat.cast_lt.mpr (show n - 1 - k.1 < n by omega))
        exact (Polynomial.natDegree_lt_iff_degree_lt htail).mpr hdeg
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]

theorem garlingGenericPoly_coeff {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) (k : Fin n) :
    (garlingGenericPoly a).coeff (n - 1 - k.1) = (-1 : R) ^ (k.1 + 1) * a k := by
  unfold garlingGenericPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ite_eq_right_iff.mpr (fun h => absurd h (by omega)), zero_add, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  · intro j _ hjk
    rw [Polynomial.coeff_C_mul_X_pow]
    exact ite_eq_right_iff.mpr fun heq => absurd (Fin.ext (by omega)) hjk
  · intro hk; exact (hk (Finset.mem_univ k)).elim

theorem garlingGenericPoly_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {n : ℕ} (a : Fin n → R) :
    (garlingGenericPoly a).map φ = garlingGenericPoly (fun k => φ (a k)) := by
  unfold garlingGenericPoly
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]

/-- Vieta expansion (§19.1, printed p. 147 / PDF p. 155):
`f = (x - t₁)⋯(x - tₙ) = xⁿ - s₁ x^{n-1} + ⋯ + (-1)ⁿ sₙ`. -/
theorem generalRootsPoly_eq_garlingGenericPoly {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) :
    generalRootsPoly t =
      garlingGenericPoly (fun k => MvPolynomial.eval t (elemSymmPoly R n k)) := by
  let s : Multiset R := (Finset.univ : Finset (Fin n)).val.map t
  have hcard : Multiset.card s = n := by
    simp [s]
  have hprod : generalRootsPoly t = (s.map fun r => Polynomial.X - Polynomial.C r).prod := by
    unfold generalRootsPoly
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [hprod, Multiset.prod_X_sub_X_eq_sum_esymm, hcard, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Multiset.esymm_zero, map_one, Nat.sub_zero, add_comm]
  unfold garlingGenericPoly
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hes : s.esymm (k.1 + 1) = MvPolynomial.eval t (elemSymmPoly R n k) := by
    change ((Finset.univ : Finset (Fin n)).val.map t).esymm (k.1 + 1) =
      MvPolynomial.eval t (MvPolynomial.esymm (Fin n) R (k.1 + 1))
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := R) (S := R) (k.1 + 1) t]
    rfl
  rw [hes]
  have hpow : (-1 : R[X]) ^ (k.1 + 1) = Polynomial.C ((-1 : R) ^ (k.1 + 1)) := by
    simp
  rw [hpow, ← mul_assoc, ← map_mul]
  have hsub : n - (k.1 + 1) = n - 1 - k.1 := by omega
  rw [hsub]

theorem generalRootsPoly_eq_garlingGenericPoly_eval {K E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} (t : Fin n → E) :
    generalRootsPoly t = garlingGenericPoly (elemSymmVal K t) := by
  rw [generalRootsPoly_eq_garlingGenericPoly t]
  congr 1
  funext k
  unfold elemSymmVal elemSymmPoly evalMvRingHom
  change MvPolynomial.aeval t (MvPolynomial.esymm (Fin n) E (k.1 + 1)) =
    MvPolynomial.aeval t (MvPolynomial.esymm (Fin n) K (k.1 + 1))
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm]

theorem generalRootsPoly_monic {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) :
    (generalRootsPoly t).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (t i)

theorem generalRootsPoly_natDegree {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (t : Fin n → R) :
    (generalRootsPoly t).natDegree = n := by
  rw [generalRootsPoly_eq_garlingGenericPoly, garlingGenericPoly_natDegree]

theorem generalRootsPoly_eval_root {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) (i : Fin n) :
    (generalRootsPoly t).eval (t i) = 0 := by
  unfold generalRootsPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Helper: given an algebraically independent generating tuple `t : Fin n → E` over `K`,
the canonical `K`-algebra isomorphism `FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K] E`
from `Theorem 18.2`. -/
noncomputable def ratFuncEquivOfGen {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K] E :=
  (Classical.choose (theorem_18_2_algEquiv ht)).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)

theorem ratFuncEquivOfGen_algebraMap {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (p : MvPolynomial (Fin n) K) :
    ratFuncEquivOfGen ht hgen
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) p) =
      evalMvRingHom K t p :=
  (Classical.choose_spec (theorem_18_2_algEquiv ht)).1 p

/-- Permutation `K`-automorphism of `E = K(t₁, …, tₙ)` induced by `σ ∈ Σₙ`
(§19.1, printed p. 148 / PDF p. 156: sending `f(t₁, …, tₙ) / g(t₁, …, tₙ)` to
`f(t_{σ(1)}, …, t_{σ(n)}) / g(t_{σ(1)}, …, t_{σ(n)})`). -/
noncomputable def permAut {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (σ : SigmaN n) :
    E ≃ₐ[K] E :=
  let e := ratFuncEquivOfGen ht hgen
  let rEquiv : FractionRing (MvPolynomial (Fin n) K) ≃+*
      FractionRing (MvPolynomial (Fin n) K) :=
    IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.renameEquiv K σ).toRingEquiv
  let aEquiv : FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin n) K) :=
    { rEquiv with
      commutes' := fun k => by
        change IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.renameEquiv K σ).toRingEquiv
          (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
            (MvPolynomial.C k)) =
          algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
            (MvPolynomial.C k)
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
        simp }
  e.symm.trans (aEquiv.trans e)

theorem permAut_evalMvRingHom {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    (σ : SigmaN n) (p : MvPolynomial (Fin n) K) :
    permAut ht hgen σ (evalMvRingHom K t p) = evalMvRingHom K t (MvPolynomial.rename σ p) := by
  unfold permAut
  dsimp only [AlgEquiv.trans_apply]
  have h1 : (ratFuncEquivOfGen ht hgen).symm (evalMvRingHom K t p) =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) p := by
    apply (ratFuncEquivOfGen ht hgen).injective
    rw [AlgEquiv.apply_symm_apply, ratFuncEquivOfGen_algebraMap]
  rw [h1]
  change ratFuncEquivOfGen ht hgen
    (IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.renameEquiv K σ).toRingEquiv
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) p)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact ratFuncEquivOfGen_algebraMap ht hgen (MvPolynomial.rename σ p)

theorem permAut_eval_ratio {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    (σ : SigmaN n) (p q : MvPolynomial (Fin n) K) :
    permAut ht hgen σ (evalMvRingHom K t p / evalMvRingHom K t q) =
      evalMvRingHom K (t ∘ σ) p / evalMvRingHom K (t ∘ σ) q := by
  rw [map_div₀, permAut_evalMvRingHom, permAut_evalMvRingHom]
  have hcomp : ∀ r : MvPolynomial (Fin n) K,
      evalMvRingHom K t (MvPolynomial.rename σ r) = evalMvRingHom K (t ∘ σ) r := by
    intro r
    change MvPolynomial.aeval t (MvPolynomial.rename σ r) = MvPolynomial.aeval (t ∘ σ) r
    exact MvPolynomial.aeval_rename σ t r
  rw [hcomp p, hcomp q]

@[simp]
theorem permAut_apply_gen {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    (σ : SigmaN n) (i : Fin n) :
    permAut ht hgen σ (t i) = t (σ i) := by
  have h := permAut_evalMvRingHom ht hgen σ (MvPolynomial.X i)
  simpa [evalMvRingHom_X] using h

/-- Two `K`-algebra homomorphisms from `E = K(t₁, …, tₙ)` agreeing on each `t_i` are equal. -/
private theorem algHom_ext_of_adjoin_range {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] {n : ℕ} {t : Fin n → E}
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    {φ ψ : E →ₐ[K] F} (h : ∀ i : Fin n, φ (t i) = ψ (t i)) : φ = ψ := by
  let EqF : IntermediateField K E :=
    { carrier := {x : E | φ x = ψ x}
      add_mem' := fun {a b} ha hb => by change φ (a + b) = ψ (a + b); rw [map_add, map_add, ha, hb]
      zero_mem' := by change φ 0 = ψ 0; rw [map_zero, map_zero]
      mul_mem' := fun {a b} ha hb => by change φ (a * b) = ψ (a * b); rw [map_mul, map_mul, ha, hb]
      one_mem' := by change φ 1 = ψ 1; rw [map_one, map_one]
      inv_mem' := fun {a} ha => by change φ a⁻¹ = ψ a⁻¹; rw [map_inv₀, map_inv₀, ha]
      algebraMap_mem' := fun k => by change φ (algebraMap K E k) = ψ (algebraMap K E k); simp }
  have htop : (⊤ : IntermediateField K E) ≤ EqF := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  ext x
  exact htop IntermediateField.mem_top

/-- Group homomorphism `Σₙ →* Aut_K(E)` (`σ ↦ permAut σ`). -/
noncomputable def permAutAlgHom {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    SigmaN n →* (E ≃ₐ[K] E) where
  toFun := permAut ht hgen
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply algHom_ext_of_adjoin_range hgen
    intro i
    simp
  map_mul' σ τ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply algHom_ext_of_adjoin_range hgen
    intro i
    change permAut ht hgen (σ * τ) (t i) = permAut ht hgen σ (permAut ht hgen τ (t i))
    simp

/-- Group homomorphism `Σₙ →* GarlingAut E` (`σ ↦ (permAut σ).toRingEquiv`). -/
noncomputable def permAutHom {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    SigmaN n →* GarlingAut E where
  toFun σ := (permAut ht hgen σ).toRingEquiv
  map_one' := congrArg AlgEquiv.toRingEquiv (permAutAlgHom ht hgen).map_one
  map_mul' σ τ := congrArg AlgEquiv.toRingEquiv ((permAutAlgHom ht hgen).map_mul σ τ)

theorem permAutHom_injective {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Function.Injective (permAutHom ht hgen) := by
  intro σ τ hστ
  ext i
  have hi : permAut ht hgen σ (t i) = permAut ht hgen τ (t i) :=
    congrArg (fun f : GarlingAut E => f (t i)) hστ
  rw [permAut_apply_gen, permAut_apply_gen] at hi
  exact congrArg Fin.val (ht.injective hi)

/-- Garling's permutation automorphism subgroup `G ≤ Aut E` (§19.1, printed p. 148). -/
noncomputable def permAutSubgroup {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Subgroup (GarlingAut E) :=
  (permAutHom ht hgen).range

/-- Canonical group isomorphism `Σₙ ≃* G` (§19.1, p. 148). -/
noncomputable def permAutSubgroupMulEquiv {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    SigmaN n ≃* permAutSubgroup ht hgen :=
  MulEquiv.ofBijective (permAutHom ht hgen).rangeRestrict
    ⟨fun _ _ h => permAutHom_injective ht hgen (congrArg Subtype.val h),
      (permAutHom ht hgen).rangeRestrict_surjective⟩

instance permAutSubgroup_finite {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Finite (permAutSubgroup ht hgen) :=
  Finite.of_equiv (SigmaN n) (permAutSubgroupMulEquiv ht hgen).toEquiv

theorem permAutSubgroup_card {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Nat.card (permAutSubgroup ht hgen) = n.factorial := by
  rw [← Nat.card_congr (permAutSubgroupMulEquiv ht hgen).toEquiv, Nat.card_perm, Nat.card_fin]

/-- Garling's fixed field `L = φ(G) ≤ E` (§19.1, printed p. 148). -/
noncomputable def permFixedField {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Subfield E :=
  garlingPhi (permAutSubgroup ht hgen : Set (GarlingAut E))

/-- The subfield `K(s₁, …, sₙ)` of `E = K(t₁, …, tₙ)` generated over `K` by the elementary
symmetric polynomials in `t₁, …, tₙ`. -/
noncomputable def elemSymmField (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) : IntermediateField K E :=
  IntermediateField.adjoin K (Set.range (elemSymmVal K t))

theorem permAut_elemSymmVal {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤)
    (σ : SigmaN n) (k : Fin n) :
    permAut ht hgen σ (elemSymmVal K t k) = elemSymmVal K t k := by
  unfold elemSymmVal elemSymmPoly
  rw [permAut_evalMvRingHom, MvPolynomial.rename_esymm]

theorem elemSymmField_le_permFixedField {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    (elemSymmField K t).toSubfield ≤ permFixedField ht hgen := by
  have hK : ∀ c : K, algebraMap K E c ∈ permFixedField ht hgen := by
    rintro c _ ⟨σ, rfl⟩
    exact (permAut ht hgen σ).commutes c
  let L_int : IntermediateField K E := (permFixedField ht hgen).toIntermediateField hK
  have hle : elemSymmField K t ≤ L_int := by
    rw [elemSymmField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩ _ ⟨σ, rfl⟩
    exact permAut_elemSymmVal ht hgen σ k
  exact hle

/-- **§19.1 Prose Deduction via `Theorem 11.3`** (printed p. 148 / PDF p. 156):
*"Then, by Theorem 11.3, `K(t₁, …, tₙ) : L` is a Galois extension, with Galois group `G`."* -/
theorem section_19_1_galois_over_fixedField {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    let L := permFixedField ht hgen
    IsGarlingGaloisExtension L E ∧
    permAutSubgroup ht hgen = garlingGamma L ∧
    Module.finrank L E = n.factorial ∧
    extDegree L E = (n.factorial : ℕ∞) := by
  intro L
  have h113 := theorem_11_3 (permAutSubgroup ht hgen)
  have hcard := permAutSubgroup_card ht hgen
  refine ⟨h113.2.2.2.2, h113.2.2.2.1, ?_, ?_⟩
  · exact h113.2.2.1.symm.trans hcard
  · have hdeg : extDegree L E = setOrder (permAutSubgroup ht hgen) := h113.2.1.symm
    rw [hdeg]
    have _ : Fintype (permAutSubgroup ht hgen) := Fintype.ofFinite _
    rw [setOrder, ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard]

/-- The general-roots polynomial `f = xⁿ - s₁ x^{n-1} + ⋯ + (-1)ⁿ sₙ` viewed as an element of
`K(s₁, …, sₙ)[x]` (§19.1, printed p. 148). -/
noncomputable def generalRootsPolyOverElemSymm (K : Type*) {E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} (t : Fin n → E) : (elemSymmField K t)[X] :=
  garlingGenericPoly (fun k =>
    (⟨elemSymmVal K t k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩ : elemSymmField K t))

theorem generalRootsPolyOverElemSymm_map (K : Type*) {E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} (t : Fin n → E) :
    (generalRootsPolyOverElemSymm K t).map (algebraMap (elemSymmField K t) E) =
      generalRootsPoly t := by
  rw [generalRootsPolyOverElemSymm, garlingGenericPoly_map,
    generalRootsPoly_eq_garlingGenericPoly_eval (K := K) t]
  rfl

/-- `E = K(t₁, …, tₙ)` is a splitting field extension of `f` over `K(s₁, …, sₙ)` (§19.1, p. 148). -/
theorem isGarlingSplittingFieldExtension_generalRootsPoly {K E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} {t : Fin n → E}
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    IsGarlingSplittingFieldExtension (elemSymmField K t) E (generalRootsPolyOverElemSymm K t) := by
  let S := elemSymmField K t
  let fS := generalRootsPolyOverElemSymm K t
  have hmap : fS.map (algebraMap S E) = generalRootsPoly t :=
    generalRootsPolyOverElemSymm_map K t
  have hspl : GarlingSplitsOver S E fS := by
    refine ⟨n, 1, t, ?_⟩
    unfold GarlingSplitsExplicit
    rw [hmap, map_one, map_one, one_mul]
    rfl
  refine ⟨hspl, fun M hM hMspl => ?_⟩
  rcases hMspl with ⟨m, lam, α, hMexp⟩
  have hmap_eq : generalRootsPoly t =
      Polynomial.C (algebraMap S E lam) * ∏ j : Fin m, (Polynomial.X - Polynomial.C (α j : E)) := by
    have h1 := congrArg (Polynomial.map M.val.toRingHom) hMexp
    have hcomp : Polynomial.map M.val.toRingHom (fS.map (algebraMap S M)) =
        fS.map (algebraMap S E) := by
      rw [Polynomial.map_map]; rfl
    rw [hcomp, hmap] at h1
    simpa [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] using h1
  have hlam0 : (algebraMap S E lam) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hmap_eq
    exact (generalRootsPoly_monic t).ne_zero hmap_eq
  have ht_mem : ∀ i : Fin n, t i ∈ M := by
    intro i
    have hroot := generalRootsPoly_eval_root t i
    rw [hmap_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hroot
    have hprod0 := (mul_eq_zero.mp hroot).resolve_left hlam0
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hprod0
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    rw [hj]
    exact (α j).2
  apply hM
  have hK_le : IntermediateField.adjoin K (Set.range t) ≤ M.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact ht_mem i
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (⊤ : IntermediateField K E) := IntermediateField.mem_top
  rw [← hgen] at hx
  exact hK_le hx

/-- **Theorem 19.1** (§19.1, printed p. 148 / PDF p. 156):
*"`L = K(s₁, …, sₙ)`."*

Proved literally for all `n : ℕ` (including `n = 0`) and all fields `K`, following Garling's
exact proof via `Theorem 7.3` (`[E : K(s₁,…,sₙ)] ≤ n!`), `Theorem 11.3` (`[E : L] = n!`), and
`Theorem 4.2` (tower law). -/
theorem theorem_19_1 {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    permFixedField ht hgen = (elemSymmField K t).toSubfield := by
  let S := elemSymmField K t
  let L := permFixedField ht hgen
  have hSL : S.toSubfield ≤ L := elemSymmField_le_permFixedField ht hgen
  have hsf := isGarlingSplittingFieldExtension_generalRootsPoly (K := K) hgen
  have hdeg_fS : (generalRootsPolyOverElemSymm K t).natDegree = n :=
    garlingGenericPoly_natDegree _
  have hne_fS : generalRootsPolyOverElemSymm K t ≠ 0 :=
    (garlingGenericPoly_monic _).ne_zero
  -- By Theorem 7.3 (`splittingField_finrank_dvd_factorial`), `[E : S] ≤ n!`:
  have hmsf : (generalRootsPolyOverElemSymm K t).IsSplittingField S E :=
    (isGarlingSplittingFieldExtension_iff S E _).mp hsf
  have _ : Polynomial.IsSplittingField S E (generalRootsPolyOverElemSymm K t) := hmsf
  have _ : Module.Finite S E :=
    Polynomial.IsSplittingField.finiteDimensional E (generalRootsPolyOverElemSymm K t)
  have hdvd : Module.finrank S E ∣ n.factorial :=
    splittingField_finrank_dvd_factorial n hdeg_fS hsf
  have hle_fact : Module.finrank S E ≤ n.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos n) hdvd
  -- By Theorem 11.3, `[E : L] = n!`:
  obtain ⟨hgalLE, _, hfin_LE, _⟩ := section_19_1_galois_over_fixedField ht hgen
  -- Tower law (`Theorem 4.2`) on `S.toSubfield ≤ L ≤ E`:
  let _ : Algebra S L := (Subfield.inclusion hSL).toAlgebra
  have _ : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : Module.Finite S L := Module.Finite.left S L E
  have _ : Module.Finite L E := (isFiniteExtension_iff_moduleFinite L E).mp hgalLE.1
  have htower := Module.finrank_mul_finrank S L E
  have hfin_SL_pos : 0 < Module.finrank S L := Module.finrank_pos
  have hfin_SL_eq_one : Module.finrank S L = 1 := by
    rw [hfin_LE] at htower
    have hfact_pos : 0 < n.factorial := Nat.factorial_pos n
    nlinarith
  apply le_antisymm _ hSL
  intro x hx
  have hbot_eq_top : (⊥ : IntermediateField S L) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hfin1 : Module.finrank S L = 1 := hfin_SL_eq_one
    have hcard : ∀ z : L, ∃ c : S, algebraMap S L c = z := by
      intro z
      by_contra hnz
      have hli : LinearIndependent S ![((1 : L)), z] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hsum : (g 0 : S) • (1 : L) + (g 1 : S) • z = 0 := by
          simpa [Fin.sum_univ_two] using hg
        by_cases hg1 : g 1 = 0
        · rw [hg1, zero_smul, add_zero, Algebra.smul_def, mul_one] at hsum
          have hg0 : g 0 = 0 := (algebraMap S L).injective (by rw [hsum, map_zero])
          intro i; fin_cases i <;> assumption
        · exfalso
          apply hnz
          refine ⟨-(g 1)⁻¹ * g 0, ?_⟩
          have h1 : (algebraMap S L (g 1)) * z = -(algebraMap S L (g 0)) := by
            rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsum
            exact eq_neg_of_add_eq_zero_right hsum
          have hg1' : algebraMap S L (g 1) ≠ 0 :=
            fun h0 => hg1 ((algebraMap S L).injective (h0.trans (map_zero _).symm))
          calc algebraMap S L (-(g 1)⁻¹ * g 0)
              = (algebraMap S L (g 1))⁻¹ * (-(algebraMap S L (g 0))) := by
                simp [map_mul, map_neg, map_inv₀]
            _ = (algebraMap S L (g 1))⁻¹ * (algebraMap S L (g 1) * z) := by rw [h1]
            _ = z := inv_mul_cancel_left₀ hg1' z
      have hle2 := hli.fintype_card_le_finrank
      simp [hfin1] at hle2
    obtain ⟨c, hc⟩ := hcard y
    exact ⟨c, hc⟩
  have hx' : (⟨x, hx⟩ : L) ∈ (⊥ : IntermediateField S L) := by
    rw [hbot_eq_top]; trivial
  rcases IntermediateField.mem_bot.mp hx' with ⟨c, hc⟩
  have hval : (c : E) = x := congrArg Subtype.val hc
  rw [← hval]
  exact c.2

/-- **Corollary** [to **Theorem 19.1**] — Galois group part (holds unconditionally for all `n : ℕ`):
`Γ_f ≅ Σₙ` for every splitting field `F` of `f` over `K(s₁, …, sₙ)`. -/
theorem corollary_to_theorem_19_1_galoisGroup {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Nonempty (GarlingPolyGaloisGroup (elemSymmField K t) E (generalRootsPolyOverElemSymm K t) ≃*
      SigmaN n) ∧
    ∀ (F : Type w) [Field F] [Algebra (elemSymmField K t) F],
      IsGarlingSplittingFieldExtension (elemSymmField K t) F (generalRootsPolyOverElemSymm K t) →
      Nonempty (GarlingPolyGaloisGroup (elemSymmField K t) F (generalRootsPolyOverElemSymm K t) ≃*
        SigmaN n) := by
  let S := elemSymmField K t
  let L := permFixedField ht hgen
  have hLS : L = S.toSubfield := theorem_19_1 ht hgen
  obtain ⟨_, hG_eq, _, _⟩ := section_19_1_galois_over_fixedField ht hgen
  have hG_S : permAutSubgroup ht hgen = garlingGaloisSubgroup S E := by
    change permAutSubgroup ht hgen = garlingGamma L at hG_eq
    rw [hG_eq, hLS]
    ext σ
    simp only [mem_garlingGamma_iff, mem_garlingGaloisSubgroup_iff]
    constructor
    · intro h k; exact h k.1 k.2
    · intro h x hx; exact h ⟨x, hx⟩
  let e1 : GarlingPolyGaloisGroup S E (generalRootsPolyOverElemSymm K t) ≃*
      garlingGaloisSubgroup S E := garlingGaloisGroupMulEquiv S E
  let e2 : garlingGaloisSubgroup S E ≃* permAutSubgroup ht hgen :=
    MulEquiv.subgroupCongr hG_S.symm
  let eE : GarlingPolyGaloisGroup S E (generalRootsPolyOverElemSymm K t) ≃* SigmaN n :=
    e1.trans (e2.trans (permAutSubgroupMulEquiv ht hgen).symm)
  refine ⟨⟨eE⟩, fun F _ _ hsfF => ?_⟩
  have hsfE := isGarlingSplittingFieldExtension_generalRootsPoly (K := K) hgen
  obtain ⟨eFE⟩ := garlingPolyGaloisGroup_independent_of_splittingField hsfF hsfE
  exact ⟨eFE.trans eE⟩

/-- **Counterexample to the literal `Corollary` [to `Theorem 19.1`] at `n = 0`** (`QUEUE.md` hold):
At `n = 0`, `f = 1` is a unit in `K[x]` and hence **not** irreducible (`¬ Irreducible 1`). -/
theorem corollary_to_theorem_19_1_n0_counterexample (K : Type u) [Field K] :
    let t : Fin 0 → K := Fin.elim0
    IsGarlingAlgIndepTuple K t ∧
    IntermediateField.adjoin K (Set.range t) = ⊤ ∧
    generalRootsPolyOverElemSymm K t = 1 ∧
    ¬ Irreducible (generalRootsPolyOverElemSymm K t) ∧
    ¬ IsGarlingIrreducible (generalRootsPolyOverElemSymm K t) := by
  intro t
  have ht : IsGarlingAlgIndepTuple K t := by
    rw [isGarlingAlgIndepTuple_iff]
    exact algebraicIndependent_empty_type_iff.mpr (algebraMap K K).injective
  have hgen : IntermediateField.adjoin K (Set.range t) = ⊤ :=
    Subsingleton.elim _ _
  have hf1 : generalRootsPolyOverElemSymm K t = 1 := by
    simp [generalRootsPolyOverElemSymm, garlingGenericPoly]
  have hni : ¬ Irreducible (generalRootsPolyOverElemSymm K t) := by
    rw [hf1]; exact not_irreducible_one
  exact ⟨ht, hgen, hf1, hni, fun h => hni ((isGarlingIrreducible_iff _).mp h)⟩

/-- Helper: over `K(s₁, …, sₙ)`, the polynomial `f = (x - t₁)⋯(x - tₙ)` is irreducible for `1 ≤ n`
(by transitivity of `G ≅ Σₙ` on the `n` distinct roots `t₁, …, tₙ`). -/
private theorem generalRootsPolyOverElemSymm_irreducible {K E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} (hn : 1 ≤ n) {t : Fin n → E}
    (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Irreducible (generalRootsPolyOverElemSymm K t) := by
  classical
  let S := elemSymmField K t
  let fS := generalRootsPolyOverElemSymm K t
  have hfS_mon : fS.Monic := garlingGenericPoly_monic _
  have hfS_deg : fS.natDegree = n := garlingGenericPoly_natDegree _
  let i0 : Fin n := ⟨0, hn⟩
  have ht0_root : Polynomial.aeval (t i0) fS = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, generalRootsPolyOverElemSymm_map]
    exact generalRootsPoly_eval_root t i0
  have ht0_int : IsIntegral S (t i0) := ⟨fS, hfS_mon, ht0_root⟩
  let m := minpoly S (t i0)
  have hm_irr : Irreducible m := minpoly.irreducible ht0_int
  have hm_mon : m.Monic := minpoly.monic ht0_int
  have hm_dvd : m ∣ fS := minpoly.dvd S (t i0) ht0_root
  -- Every `t i` is a root of `m` because `permAut (Equiv.swap i0 i)` fixes `S` and sends `t i0 ↦ t i`:
  have h_all_roots : ∀ i : Fin n, (m.map (algebraMap S E)).eval (t i) = 0 := by
    intro i
    let σ : SigmaN n := Equiv.swap i0 i
    let τ : E ≃ₐ[K] E := permAut ht hgen σ
    have hτS : ∀ s : S, τ s.1 = s.1 := by
      intro s
      have hsL : s.1 ∈ permFixedField ht hgen := elemSymmField_le_permFixedField ht hgen s.2
      exact hsL (permAutHom ht hgen σ) ⟨σ, rfl⟩
    have hm0 : (m.map (algebraMap S E)).eval (t i0) = 0 := by
      have h := minpoly.aeval S (t i0)
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
      exact h
    have hmap_τ : (m.map (algebraMap S E)).map τ.toRingHom = m.map (algebraMap S E) := by
      rw [Polynomial.map_map]
      congr 1
      ext s
      exact hτS s
    have hstep : τ.toRingHom ((m.map (algebraMap S E)).eval (t i0)) = 0 := by
      change τ ((m.map (algebraMap S E)).eval (t i0)) = 0
      rw [hm0, map_zero]
    rw [← Polynomial.eval_map_apply, hmap_τ] at hstep
    have hti : τ.toRingHom (t i0) = t i := by
      change permAut ht hgen (Equiv.swap i0 i) (t i0) = t i
      rw [permAut_apply_gen, Equiv.swap_apply_left]
    rwa [hti] at hstep
  have hcard_le : n ≤ (m.map (algebraMap S E)).natDegree := by
    have hsub : (Finset.univ.image t) ⊆ (m.map (algebraMap S E)).roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hm_mon.map (algebraMap S E)).ne_zero)]
      exact h_all_roots i
    calc n = (Finset.univ : Finset (Fin n)).card := (Finset.card_fin n).symm
      _ = (Finset.univ.image t).card := (Finset.card_image_of_injective _ ht.injective).symm
      _ ≤ (m.map (algebraMap S E)).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (m.map (algebraMap S E)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (m.map (algebraMap S E)).natDegree := Polynomial.card_roots' _
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap S E).injective] at hcard_le
  have hmf_eq : fS = m :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm_mon hfS_mon hm_dvd (hfS_deg.symm ▸ hcard_le)
  change Irreducible fS
  rw [hmf_eq]
  exact hm_irr

/-- **Corollary** [to **Theorem 19.1**] (repaired with `1 ≤ n`; §19.1, printed p. 148 / PDF p. 156):
*"`f` is irreducible over `K(s₁, …, sₙ)` and `Γ_f ≅ Σₙ`, the group of permutations of `{1, …, n}`."* -/
theorem corollary_to_theorem_19_1 {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    (hn : 1 ≤ n) {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Irreducible (generalRootsPolyOverElemSymm K t) ∧
    IsGarlingIrreducible (generalRootsPolyOverElemSymm K t) ∧
    Nonempty (GarlingPolyGaloisGroup (elemSymmField K t) E (generalRootsPolyOverElemSymm K t) ≃*
      SigmaN n) ∧
    ∀ (F : Type w) [Field F] [Algebra (elemSymmField K t) F],
      IsGarlingSplittingFieldExtension (elemSymmField K t) F (generalRootsPolyOverElemSymm K t) →
      Nonempty (GarlingPolyGaloisGroup (elemSymmField K t) F (generalRootsPolyOverElemSymm K t) ≃*
        SigmaN n) := by
  have hirr := generalRootsPolyOverElemSymm_irreducible hn ht hgen
  obtain ⟨hgalE, hgalF⟩ := corollary_to_theorem_19_1_galoisGroup ht hgen
  exact ⟨hirr, (isGarlingIrreducible_iff _).mpr hirr, hgalE, hgalF⟩

/-- Unconditional characterization of irreducibility in `Corollary` [to `Theorem 19.1`] across all
`n : ℕ`: `Irreducible f ↔ 1 ≤ n`. -/
theorem corollary_to_theorem_19_1_irred_iff {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    Irreducible (generalRootsPolyOverElemSymm K t) ↔ 1 ≤ n := by
  constructor
  · intro hirr
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hf1 : generalRootsPolyOverElemSymm K t = 1 := by
      simp [generalRootsPolyOverElemSymm, garlingGenericPoly]
    rw [hf1] at hirr
    exact not_irreducible_one hirr
  · intro hn
    exact generalRootsPolyOverElemSymm_irreducible hn ht hgen

private theorem setOrder_eq_finset_card {α : Type*} {S : Set α} (hS : S.Finite) :
    setOrder S = (hS.toFinset.card : ℕ∞) := by
  rw [setOrder, ENat.card_coe_set_eq]
  conv_lhs => rw [← hS.coe_toFinset]
  exact Set.encard_coe_eq_coe_finsetCard hS.toFinset

/-- **Theorem 19.2** (§19.1, printed p. 148 / PDF p. 156):
*"The elementary symmetric polynomials `s₁, …, sₙ` are algebraically independent over `K`."*

Proved literally for all `n : ℕ` (including `n = 0`) and all fields `K`, following Garling's
exact proof via `Theorem 18.5` and `Corollary` [to `Theorem 18.6`]. -/
theorem theorem_19_2 {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    IsGarlingAlgIndepTuple K (elemSymmVal K t) ∧
    IsGarlingAlgebraicallyIndependent K (Set.range (elemSymmVal K t)) := by
  classical
  -- `Set.range t` is a transcendence basis of `E : K` of cardinality `n`:
  have ht_tb : IsGarlingTranscendenceBasis K (Set.range t) := by
    rw [theorem_18_4]
    refine ⟨(isGarlingAlgebraicallyIndependent_range_iff ht.injective).mpr ht, ?_⟩
    rw [hgen]
    intro x
    exact ⟨Polynomial.X - Polynomial.C (⟨x, trivial⟩ : (⊤ : IntermediateField K E)),
      Polynomial.X_sub_C_ne_zero _, by simp⟩
  -- `E : K(s₁, …, sₙ)` is finite, hence algebraic:
  have hS_alg : IsAlgebraicExtension (elemSymmField K t) E := by
    have hsf := isGarlingSplittingFieldExtension_generalRootsPoly (K := K) hgen
    have hmsf : (generalRootsPolyOverElemSymm K t).IsSplittingField (elemSymmField K t) E :=
      (isGarlingSplittingFieldExtension_iff (elemSymmField K t) E _).mp hsf
    have _ : Polynomial.IsSplittingField (elemSymmField K t) E
        (generalRootsPolyOverElemSymm K t) := hmsf
    have _ : Module.Finite (elemSymmField K t) E :=
      Polynomial.IsSplittingField.finiteDimensional E (generalRootsPolyOverElemSymm K t)
    exact (isAlgebraicExtension_iff _ _).mpr
      (Algebra.IsAlgebraic.of_finite (elemSymmField K t) E)
  -- By `Theorem 18.5`, `Set.range (elemSymmVal K t)` contains a transcendence basis `B` of `E : K`:
  obtain ⟨B, hB_tb, _, hB_sub⟩ :=
    theorem_18_5 (K := K) (L := E) (C := ∅) (A := Set.range (elemSymmVal K t))
      hS_alg (Set.empty_subset _) (isGarlingAlgebraicallyIndependent_empty K)
  -- By `Corollary` [to `Theorem 18.6`], `B` and `Set.range t` have the same cardinality `n`:
  have hord := setOrder_eq_of_isGarlingTranscendenceBasis hB_tb ht_tb
  have hfin_t : (Set.range t).Finite := Set.finite_range t
  have hfin_s : (Set.range (elemSymmVal K t)).Finite := Set.finite_range _
  have hfin_B : B.Finite := hfin_s.subset hB_sub
  have hcard_t : (hfin_t.toFinset).card = n := by
    have : hfin_t.toFinset = Finset.univ.image t := by ext x; simp
    rw [this, Finset.card_image_of_injective _ ht.injective, Finset.card_fin]
  have hcard_B_eq_t : hfin_B.toFinset.card = hfin_t.toFinset.card := by
    rw [setOrder_eq_finset_card hfin_B, setOrder_eq_finset_card hfin_t] at hord
    exact Nat.cast_injective hord
  have hcard_B : hfin_B.toFinset.card = n := hcard_B_eq_t.trans hcard_t
  have hcard_s_le : hfin_s.toFinset.card ≤ n := by
    have : hfin_s.toFinset = Finset.univ.image (elemSymmVal K t) := by ext x; simp
    rw [this]
    exact Finset.card_image_le.trans (by simp)
  have hB_le_s : hfin_B.toFinset ⊆ hfin_s.toFinset := by
    intro x hx
    exact hfin_s.mem_toFinset.mpr (hB_sub (hfin_B.mem_toFinset.mp hx))
  have hB_eq_s_fin : hfin_B.toFinset = hfin_s.toFinset :=
    Finset.eq_of_subset_of_card_le hB_le_s (by omega)
  have hB_eq_s : B = Set.range (elemSymmVal K t) := by
    ext x
    rw [← hfin_B.mem_toFinset, ← hfin_s.mem_toFinset, hB_eq_s_fin]
  have hs_indep_set : IsGarlingAlgebraicallyIndependent K (Set.range (elemSymmVal K t)) := by
    rw [← hB_eq_s]
    exact ((theorem_18_4 B).mp hB_tb).1
  have hs_card : (Finset.univ.image (elemSymmVal K t)).card = (Finset.univ : Finset (Fin n)).card := by
    have : hfin_s.toFinset = Finset.univ.image (elemSymmVal K t) := by ext x; simp
    rw [← this, ← hB_eq_s_fin, hcard_B, Finset.card_fin]
  have hs_inj : Function.Injective (elemSymmVal K t) := by
    intro i j hij
    have hinjOn := Finset.injOn_of_card_image_eq hs_card
    exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
  exact ⟨(isGarlingAlgebraicallyIndependent_range_iff hs_inj).mp hs_indep_set, hs_indep_set⟩

/-- **§19.1 Prose Isomorphism via `Theorem 18.2`** (printed p. 148 / PDF p. 156; noting the
printed typo `xⁿ - a₁ xⁿ` for `xⁿ - a₁ x^{n-1}` on p. 148 l. 28):
There is a unique `K`-algebra isomorphism `K(a₁, …, aₙ) ≃ₐ[K] K(s₁, …, sₙ)` sending `a_i ↦ s_i`
and sending the generic polynomial `xⁿ - a₁ x^{n-1} + ⋯ + (-1)ⁿ aₙ` to `f`. -/
noncomputable def genericPolyIsoElemSymm {K E₁ E₂ : Type*} [Field K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] {n : ℕ}
    {a : Fin n → E₁} (ha : IsGarlingAlgIndepTuple K a)
    {t : Fin n → E₂} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    IntermediateField.adjoin K (Set.range a) ≃ₐ[K] elemSymmField K t :=
  (Classical.choose (theorem_18_2_algEquiv ha)).symm.trans
    (Classical.choose (theorem_18_2_algEquiv (theorem_19_2 ht hgen).1))

theorem genericPolyIsoElemSymm_apply_gen {K E₁ E₂ : Type*} [Field K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] {n : ℕ}
    {a : Fin n → E₁} (ha : IsGarlingAlgIndepTuple K a)
    {t : Fin n → E₂} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (k : Fin n) :
    genericPolyIsoElemSymm ha ht hgen
      ⟨a k, IntermediateField.subset_adjoin K (Set.range a) ⟨k, rfl⟩⟩ =
      ⟨elemSymmVal K t k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩ := by
  unfold genericPolyIsoElemSymm
  dsimp only [AlgEquiv.trans_apply]
  have h1 : (Classical.choose (theorem_18_2_algEquiv ha)).symm
      ⟨a k, IntermediateField.subset_adjoin K (Set.range a) ⟨k, rfl⟩⟩ =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.X k) := by
    apply (Classical.choose (theorem_18_2_algEquiv ha)).injective
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    have hspec := (Classical.choose_spec (theorem_18_2_algEquiv ha)).1 (MvPolynomial.X k)
    rw [evalMvRingHom_X] at hspec
    exact hspec.symm
  rw [h1]
  apply Subtype.ext
  have hspec := (Classical.choose_spec (theorem_18_2_algEquiv (theorem_19_2 ht hgen).1)).1 (MvPolynomial.X k)
  rw [evalMvRingHom_X] at hspec
  exact hspec

/-- The generic polynomial viewed in `K(a₁, …, aₙ)[x]` for an algebraically independent tuple
`a : Fin n → E`. -/
noncomputable def garlingGenericPolyOverAdjoin (K : Type*) {E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} (a : Fin n → E) : (IntermediateField.adjoin K (Set.range a))[X] :=
  garlingGenericPoly (fun k =>
    (⟨a k, IntermediateField.subset_adjoin K (Set.range a) ⟨k, rfl⟩⟩ :
      IntermediateField.adjoin K (Set.range a)))

theorem genericPolyIsoElemSymm_map_poly {K E₁ E₂ : Type*} [Field K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] {n : ℕ}
    {a : Fin n → E₁} (ha : IsGarlingAlgIndepTuple K a)
    {t : Fin n → E₂} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    (garlingGenericPolyOverAdjoin K a).map (genericPolyIsoElemSymm ha ht hgen).toRingHom =
      generalRootsPolyOverElemSymm K t := by
  rw [garlingGenericPolyOverAdjoin, garlingGenericPoly_map, generalRootsPolyOverElemSymm]
  congr 1
  funext k
  exact genericPolyIsoElemSymm_apply_gen ha ht hgen k

/-! ### `Theorem 19.3`: Clauses 1–3, positive-characteristic counterexamples, and exact characterization -/

/-- Canonical free purely transcendental extension `E_n = FractionRing (MvPolynomial (Fin n) K)`
with canonical algebraically independent generators `t_i = X_i`. -/
private noncomputable def canonVar (K : Type u) [Field K] (n : ℕ) (i : Fin n) :
    FractionRing (MvPolynomial (Fin n) K) :=
  algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X i)

private theorem canonVar_algIndep (K : Type u) [Field K] (n : ℕ) :
    IsGarlingAlgIndepTuple K (canonVar K n) := by
  intro p q hpq
  have h : ∀ r : MvPolynomial (Fin n) K,
      evalMvRingHom K (canonVar K n) r =
        algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) r := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      rw [evalMvRingHom_C]
      exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) c).symm
    | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | mul_X p₁ i h₁ => rw [map_mul, map_mul, evalMvRingHom_X, h₁]; rfl
  rw [h p, h q] at hpq
  exact IsFractionRing.injective (MvPolynomial (Fin n) K)
    (FractionRing (MvPolynomial (Fin n) K)) hpq

private theorem canonVar_adjoin_eq_top (K : Type u) [Field K] (n : ℕ) :
    IntermediateField.adjoin K (Set.range (canonVar K n)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K) z
  have hmem : ∀ r : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) r ∈
        IntermediateField.adjoin K (Set.range (canonVar K n)) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)]
      exact (IntermediateField.adjoin K _).algebraMap_mem c
    | add p₁ p₂ h₁ h₂ => rw [map_add]; exact (IntermediateField.adjoin K _).add_mem h₁ h₂
    | mul_X p₁ i h₁ =>
      rw [map_mul]
      exact (IntermediateField.adjoin K _).mul_mem h₁
        (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
  exact (IntermediateField.adjoin K _).div_mem (hmem p) (hmem q)

/-- Helper: `generalRootsPolyOverElemSymm` is separable (both `Polynomial.Separable` and Garling's
`IsGarlingSeparablePoly`) for every `n : ℕ` and every field `K`. -/
private theorem generalRootsPolyOverElemSymm_separable {K E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t) :
    (generalRootsPolyOverElemSymm K t).Separable ∧
    IsGarlingSeparablePoly (generalRootsPolyOverElemSymm K t) := by
  let S := elemSymmField K t
  let fS := generalRootsPolyOverElemSymm K t
  have hsepE : (fS.map (algebraMap S E)).Separable := by
    rw [generalRootsPolyOverElemSymm_map, generalRootsPoly]
    rw [Polynomial.separable_prod_X_sub_C_iff]
    exact ht.injective
  have hsepS : fS.Separable := (Polynomial.separable_map (algebraMap S E)).mp hsepE
  exact ⟨hsepS, ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly fS).mp hsepS).2.2⟩

/-- Transporting splitting fields and polynomial Galois groups along a base-field ring isomorphism
`φ : F₁ ≃+* F₂`. Keeping `φ` abstract prevents kernel unfolding of concrete fraction-field maps. -/
private theorem galoisGroup_map_of_ringEquiv {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (φ : F₁ ≃+* F₂) {f : F₁[X]}
    (F : Type w) [Field F] [Algebra F₁ F] [Algebra F₂ F]
    (hcomp : (algebraMap F₂ F).comp φ.toRingHom = algebraMap F₁ F)
    (hsf : IsGarlingSplittingFieldExtension F₁ F f) :
    IsGarlingSplittingFieldExtension F₂ F (f.map φ.toRingHom) ∧
    Nonempty (GarlingPolyGaloisGroup F₁ F f ≃* GarlingPolyGaloisGroup F₂ F (f.map φ.toRingHom)) := by
  have hcomp_apply : ∀ x : F₁, algebraMap F₂ F (φ x) = algebraMap F₁ F x :=
    fun x => RingHom.congr_fun hcomp x
  have hcomp_symm : ∀ y : F₂, algebraMap F₁ F (φ.symm y) = algebraMap F₂ F y := fun y => by
    have h := hcomp_apply (φ.symm y)
    rw [φ.apply_symm_apply] at h
    exact h.symm
  have hrange : Set.range (algebraMap F₁ F) = Set.range (algebraMap F₂ F) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => ⟨φ x, by rw [hcomp_apply, hx]⟩,
      fun ⟨x, hx⟩ => ⟨φ.symm x, by rw [hcomp_symm, hx]⟩⟩
  have hsplits_iff : ∀ {m : ℕ} {c : F₂} {α : Fin m → F},
      GarlingSplitsExplicit F₂ F (f.map φ.toRingHom) m c α ↔
        GarlingSplitsExplicit F₁ F f m (φ.symm c) α := by
    intro m c α
    unfold GarlingSplitsExplicit
    rw [Polynomial.map_map, hcomp, hcomp_symm]
  have hsf' : IsGarlingSplittingFieldExtension F₂ F (f.map φ.toRingHom) := by
    rw [isGarlingSplittingFieldExtension_iff_subfield] at hsf ⊢
    rcases hsf with ⟨⟨m, c, α, hexp⟩, hmin⟩
    refine ⟨⟨m, φ c, α, ?_⟩, fun L' hsub hne ⟨m', c', α', hα', hexp'⟩ => ?_⟩
    · rw [hsplits_iff, φ.symm_apply_apply]; exact hexp
    · exact hmin L' (hrange ▸ hsub) hne ⟨m', φ.symm c', α', hα', hsplits_iff.mp hexp'⟩
  let eGal : GarlingPolyGaloisGroup F₁ F f ≃* GarlingPolyGaloisGroup F₂ F (f.map φ.toRingHom) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := fun y => by
            rw [← hcomp_symm y]
            exact σ.commutes (φ.symm y) }
      invFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := fun x => by
            rw [← hcomp_apply x]
            exact σ.commutes (φ x) }
      left_inv := fun _ => AlgEquiv.ext fun _ => rfl
      right_inv := fun _ => AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  exact ⟨hsf', ⟨eGal⟩⟩

/-- **Theorem 19.3 (Clauses 1–3, repaired with `1 ≤ n`)** (§19.1, printed pp. 148–149 /
PDF pp. 156–157):
Over every field `K` (of arbitrary characteristic) and every `1 ≤ n`, the generic polynomial
`xⁿ - a₁ x^{n-1} + ⋯ + (-1)ⁿ aₙ` over `K(a₁, …, aₙ)` is irreducible, separable, and has Galois
group isomorphic to `Σₙ` across every splitting field `F`. -/
theorem theorem_19_3_clauses_1_to_3 {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    (hn : 1 ≤ n) {a : Fin n → E} (ha : IsGarlingAlgIndepTuple K a) :
    let K_a := IntermediateField.adjoin K (Set.range a)
    let f := garlingGenericPolyOverAdjoin K a
    Irreducible f ∧
    IsGarlingIrreducible f ∧
    f.Separable ∧
    IsGarlingSeparablePoly f ∧
    ∀ (F : Type w) [Field F] [Algebra K_a F],
      IsGarlingSplittingFieldExtension K_a F f →
      Nonempty (GarlingPolyGaloisGroup K_a F f ≃* SigmaN n) := by
  intro K_a f
  let t := canonVar K n
  have ht := canonVar_algIndep K n
  have hgen := canonVar_adjoin_eq_top K n
  let φ : K_a ≃ₐ[K] elemSymmField K t := genericPolyIsoElemSymm ha ht hgen
  have hmap : f.map φ.toRingHom = generalRootsPolyOverElemSymm K t :=
    genericPolyIsoElemSymm_map_poly ha ht hgen
  have hcor := corollary_to_theorem_19_1 hn ht hgen
  have hsep_t := generalRootsPolyOverElemSymm_separable ht
  have hirr_f : Irreducible f := by
    have h1 : Irreducible (f.map φ.toRingHom) := hmap ▸ hcor.1
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv φ.toRingEquiv).toMulEquiv).mp h1
  have hsep_f : f.Separable := by
    have h1 : (f.map φ.toRingHom).Separable := hmap ▸ hsep_t.1
    exact (Polynomial.separable_map φ.toRingHom).mp h1
  have hgsep_f : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep_f).2.2
  refine ⟨hirr_f, (isGarlingIrreducible_iff f).mpr hirr_f, hsep_f, hgsep_f, fun F _ _ hsfF => ?_⟩
  let _ : Algebra (elemSymmField K t) F :=
    RingHom.toAlgebra ((algebraMap K_a F).comp φ.symm.toRingHom)
  have hcomp_φ : (algebraMap (elemSymmField K t) F).comp φ.toRingHom = algebraMap K_a F := by
    ext x; change algebraMap K_a F (φ.symm (φ x)) = algebraMap K_a F x; simp
  obtain ⟨hsfF_map, ⟨eGal⟩⟩ := galoisGroup_map_of_ringEquiv φ.toRingEquiv F hcomp_φ hsfF
  have hsfF' : IsGarlingSplittingFieldExtension (elemSymmField K t) F
      (generalRootsPolyOverElemSymm K t) := hmap ▸ hsfF_map
  obtain ⟨eF⟩ := hcor.2.2.2 F hsfF'
  exact ⟨eGal.trans eF⟩

/-- **Counterexample to Clause 1 of `Theorem 19.3` at `n = 0`** (`QUEUE.md` hold):
At `n = 0`, the generic polynomial `1` is a unit, not irreducible. -/
theorem theorem_19_3_n0_not_irreducible (K : Type u) [Field K] :
    let a : Fin 0 → K := Fin.elim0
    IsGarlingAlgIndepTuple K a ∧
    garlingGenericPolyOverAdjoin K a = 1 ∧
    ¬ Irreducible (garlingGenericPolyOverAdjoin K a) ∧
    ¬ IsGarlingIrreducible (garlingGenericPolyOverAdjoin K a) := by
  intro a
  have ha : IsGarlingAlgIndepTuple K a := by
    rw [isGarlingAlgIndepTuple_iff]
    exact algebraicIndependent_empty_type_iff.mpr (algebraMap K K).injective
  have hf1 : garlingGenericPolyOverAdjoin K a = 1 := by
    simp [garlingGenericPolyOverAdjoin, garlingGenericPoly]
  have hni : ¬ Irreducible (garlingGenericPolyOverAdjoin K a) := by
    rw [hf1]; exact not_irreducible_one
  exact ⟨ha, hf1, hni, fun h => hni ((isGarlingIrreducible_iff _).mp h)⟩

private theorem ringChar_eq_of_ringHom {A B : Type*} [Field A] [Field B] (f : A →+* B) :
    ringChar B = ringChar A :=
  ringChar.eq_iff.mpr (charP_of_injective_ringHom f.injective (ringChar A))

private theorem ringChar_eq_of_algebra (A B : Type*) [Field A] [Field B] [Algebra A B] :
    ringChar B = ringChar A :=
  ringChar_eq_of_ringHom (algebraMap A B)

/-- Helper Lemma A (Frobenius reduction of a radical tower in prime characteristic `p > 0`):
If `L : F` is an extension by radicals over a field `F` of prime characteristic `p`, then there
exists an intermediate field `N ≤ L` (with `F`-radical tower exponents all coprime to `p`,
i.e., `IsGarlingRadicalExtensionNotCharDvd F N`) and an exponent `D : ℕ` such that:
1. `x ^ (p ^ D) ∈ N` for every `x ∈ L`, and
2. every element `α ∈ L` that is separable over `F` already belongs to `N`. -/
private theorem frobenius_reduction_of_radical_extension {F L : Type*} [Field F] [Field L]
    [Algebra F L] {p : ℕ} (hp : Nat.Prime p) (hcharF : ringChar F = p)
    (hrad : IsGarlingExtensionByRadicals F L) :
    ∃ (N : IntermediateField F L) (D : ℕ),
      IsGarlingRadicalExtensionNotCharDvd F N ∧
      (∀ x : L, x ^ (p ^ D) ∈ N) ∧
      (∀ α : L, IsSeparable F α → α ∈ N) := by
  classical
  have _ : Fact p.Prime := ⟨hp⟩
  have _ : CharP F p := hcharF ▸ ringChar.charP F
  have hcharL : ringChar L = p := (ringChar_eq_of_algebra F L).trans hcharF
  have _ : CharP L p := hcharL ▸ ringChar.charP L
  rcases hrad with ⟨r, T, β, hT0, hTlast, hTstep⟩
  -- For each step `i : Fin r`, extract `m i ≥ 1` with `β i ^ m i ∈ T i`, and factor `m i = p^(e i) * q i`
  -- with `p ∤ q i`:
  have hex : ∀ i : Fin r, ∃ (e q : ℕ), 1 ≤ q ∧ ¬ (p ∣ q) ∧
      (β i) ^ (p ^ e * q) ∈ T i.castSucc := by
    intro i
    obtain ⟨⟨m, hm1, hpow⟩, _⟩ := hTstep i
    have hm0 : m ≠ 0 := by omega
    let e := padicValNat p m
    let q := m / p ^ e
    have hdvd : p ^ e ∣ m := pow_padicValNat_dvd
    have hmul : p ^ e * q = m := Nat.mul_div_cancel' hdvd
    have hq_pos : 1 ≤ q := by
      have hq_ne0 : q ≠ 0 := by
        intro hq0
        rw [hq0, mul_zero] at hmul
        exact hm0 hmul.symm
      exact Nat.pos_of_ne_zero hq_ne0
    have hpq : ¬ (p ∣ q) := by
      intro hdiv
      have hdvd' : p ^ (e + 1) ∣ m := by
        rcases hdiv with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [← hmul, hc, pow_succ]
        ring
      have hle : e + 1 ≤ padicValNat p m :=
        (padicValNat_dvd_iff_le hm0).mp hdvd'
      omega
    exact ⟨e, q, hq_pos, hpq, hmul.symm ▸ hpow⟩
  choose e q hq_pos hpq hβ_pow using hex
  -- Cumulative Frobenius exponent `D k = ∑_{i < k} e i`:
  let D : Fin (r + 1) → ℕ := fun k =>
    ∑ i ∈ (Finset.univ : Finset (Fin r)).filter (fun i => i.1 < k.1), e i
  have hD0 : D 0 = 0 := by simp [D]
  have hDsucc : ∀ i : Fin r, D i.succ = D i.castSucc + e i := by
    intro i
    unfold D
    have hset : (Finset.univ : Finset (Fin r)).filter (fun j => j.1 < i.succ.1) =
        insert i ((Finset.univ : Finset (Fin r)).filter (fun j => j.1 < i.castSucc.1)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc]
      constructor
      · intro hj
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr h
      · rintro (rfl | hj) <;> omega
    rw [hset, Finset.sum_insert]
    · ring
    · simp
  -- Define `η i = (β i) ^ (p ^ D i.succ)` and tower `N_k ≤ L`:
  let η : Fin r → L := fun i => (β i) ^ (p ^ D i.succ)
  let N : Fin (r + 1) → IntermediateField F L := fun k =>
    IntermediateField.adjoin F (η '' {i : Fin r | i.1 < k.1})
  have hN0 : N 0 = ⊥ := by
    have hempty : η '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1} = ∅ := by
      ext x; simp
    rw [show N 0 = IntermediateField.adjoin F (η '' {i : Fin r | i.1 < (0 : Fin (r + 1)).1}) from rfl,
      hempty, IntermediateField.adjoin_empty]
  have hNsucc : ∀ i : Fin r,
      N i.succ = IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) := by
    intro i
    have hset : η '' {j : Fin r | j.1 < i.succ.1} =
        insert (η i) (η '' {j : Fin r | j.1 < i.castSucc.1}) := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.val_succ,
        Fin.val_castSucc]
      constructor
      · rintro ⟨j, hj, rfl⟩
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · exact Or.inl (congrArg η (Fin.ext h))
        · exact Or.inr ⟨j, h, rfl⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨i, Nat.lt_succ_self _, rfl⟩
        · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    apply le_antisymm
    · rw [show N i.succ = IntermediateField.adjoin F (η '' {j : Fin r | j.1 < i.succ.1}) from rfl,
        hset, IntermediateField.adjoin_le_iff]
      rintro x (rfl | ⟨j, hj, rfl⟩)
      · exact IntermediateField.subset_adjoin F _ (Or.inr rfl)
      · exact IntermediateField.subset_adjoin F _
          (Or.inl (IntermediateField.subset_adjoin F _ ⟨j, hj, rfl⟩))
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · have hle : N i.castSucc ≤ N i.succ :=
          IntermediateField.adjoin.mono F _ _ (by rw [hset]; exact Set.subset_insert _ _)
        exact hle hx
      · exact IntermediateField.subset_adjoin F _ ⟨i, Nat.lt_succ_self _, rfl⟩
  -- Key induction: for every `k : Fin (r + 1)` and `x ∈ T k`, `x ^ (p ^ D k) ∈ N k`:
  have h_frob_mem : ∀ (k : ℕ) (hk : k ≤ r) (x : L),
      x ∈ T ⟨k, Nat.lt_succ_of_le hk⟩ → x ^ (p ^ D ⟨k, Nat.lt_succ_of_le hk⟩) ∈
        N ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk x hx
      have hx0 : x ∈ T 0 := hx
      rw [hT0] at hx0
      rcases IntermediateField.mem_bot.mp hx0 with ⟨c, rfl⟩
      rw [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (r + 1)) = 0 from rfl, hD0, pow_zero, pow_one, hN0]
      exact (⊥ : IntermediateField F L).algebraMap_mem c
    | succ k ih =>
      intro hk x hx
      let i : Fin r := ⟨k, hk⟩
      let E_frob : IntermediateField F L :=
        { carrier := {y : L | y ^ (p ^ D i.succ) ∈ N i.succ}
          add_mem' := fun {a b} ha hb => by
            change (a + b) ^ (p ^ D i.succ) ∈ N i.succ
            rw [add_pow_char_pow]
            exact (N i.succ).add_mem ha hb
          zero_mem' := by
            change (0 : L) ^ (p ^ D i.succ) ∈ N i.succ
            rw [zero_pow (pow_ne_zero _ hp.ne_zero)]
            exact (N i.succ).zero_mem
          mul_mem' := fun {a b} ha hb => by
            change (a * b) ^ (p ^ D i.succ) ∈ N i.succ
            rw [mul_pow]
            exact (N i.succ).mul_mem ha hb
          one_mem' := by
            change (1 : L) ^ (p ^ D i.succ) ∈ N i.succ
            rw [one_pow]
            exact (N i.succ).one_mem
          inv_mem' := fun {a} ha => by
            change a⁻¹ ^ (p ^ D i.succ) ∈ N i.succ
            rw [inv_pow]
            exact (N i.succ).inv_mem ha
          algebraMap_mem' := fun c => by
            change (algebraMap F L c) ^ (p ^ D i.succ) ∈ N i.succ
            rw [← map_pow]
            exact (N i.succ).algebraMap_mem _ }
      have hTi_le : T i.succ ≤ E_frob := by
        rw [(hTstep i).2, IntermediateField.adjoin_le_iff]
        rintro y (hy | rfl)
        · change y ^ (p ^ D i.succ) ∈ N i.succ
          rw [hDsucc i, pow_add, pow_mul]
          have hy' : y ^ (p ^ D i.castSucc) ∈ N i.castSucc :=
            ih (Nat.le_of_lt hk) y hy
          have hN_le : N i.castSucc ≤ N i.succ := by
            rw [hNsucc i]
            exact fun z hz => IntermediateField.subset_adjoin F _ (Or.inl hz)
          exact pow_mem (hN_le hy') (p ^ e i)
        · change (β i) ^ (p ^ D i.succ) ∈ N i.succ
          exact IntermediateField.subset_adjoin F _ ⟨i, Nat.lt_succ_self _, rfl⟩
      exact hTi_le hx
  -- Now verify `η i ^ q i ∈ N i.castSucc` for each `i : Fin r`:
  have hη_pow : ∀ i : Fin r, (η i) ^ (q i) ∈ N i.castSucc := by
    intro i
    change ((β i) ^ (p ^ D i.succ)) ^ (q i) ∈ N i.castSucc
    have heq : ((β i) ^ (p ^ D i.succ)) ^ (q i) =
        ((β i) ^ (p ^ e i * q i)) ^ (p ^ D i.castSucc) := by
      rw [← pow_mul, ← pow_mul, hDsucc i, pow_add]
      congr 1; ring
    rw [heq]
    exact h_frob_mem i.1 (Nat.le_of_lt i.2) _ (hβ_pow i)
  -- Package `N_top = N (Fin.last r)` with its coprime-to-`p` radical tower:
  let Ntop : IntermediateField F L := N (Fin.last r)
  have hN_le_top : ∀ j : Fin (r + 1), N j ≤ Ntop := fun j =>
    IntermediateField.adjoin.mono F _ _ (Set.image_mono fun i hi => lt_of_lt_of_le hi (Nat.le_of_lt_succ j.2))
  let NT : Fin (r + 1) → IntermediateField F Ntop := fun j =>
    { carrier := {x : Ntop | x.1 ∈ N j}
      add_mem' := fun {a b} ha hb => (N j).add_mem ha hb
      zero_mem' := (N j).zero_mem
      mul_mem' := fun {a b} ha hb => (N j).mul_mem ha hb
      one_mem' := (N j).one_mem
      inv_mem' := fun {a} ha => (N j).inv_mem ha
      algebraMap_mem' := fun c => (N j).algebraMap_mem c }
  let η' : Fin r → Ntop := fun i =>
    ⟨η i, IntermediateField.subset_adjoin F _ ⟨i, i.2, rfl⟩⟩
  have hchar_prod : ¬ (ringChar F ∣ ∏ i : Fin r, q i) := by
    rw [hcharF]
    intro hdiv
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff q).mp hdiv
    exact hpq i hi
  have hrad_Ntop : IsGarlingRadicalExtensionNotCharDvd F Ntop := by
    refine ⟨r, NT, η', q, ?_, ?_, hchar_prod, fun i => ?_⟩
    · ext ⟨x, hx⟩
      change x ∈ N 0 ↔ (⟨x, hx⟩ : Ntop) ∈ (⊥ : IntermediateField F Ntop)
      rw [hN0, IntermediateField.mem_bot, IntermediateField.mem_bot]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, hc⟩
        exact ⟨c, congrArg Subtype.val hc⟩
    · ext ⟨x, hx⟩
      change x ∈ Ntop ↔ True
      simp [hx]
    · refine ⟨?_, ?_⟩
      · change (η i) ^ (q i) ∈ N i.castSucc
        exact hη_pow i
      · apply le_antisymm
        · intro ⟨x, hx⟩ hxi
          have hmem : x ∈ IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) := by
            rw [← hNsucc i]; exact hxi
          let M : IntermediateField F L :=
            (IntermediateField.adjoin F ((NT i.castSucc : Set Ntop) ∪ {η' i})).map Ntop.val
          have hsub : IntermediateField.adjoin F ((N i.castSucc : Set L) ∪ {η i}) ≤ M := by
            rw [IntermediateField.adjoin_le_iff]
            rintro y (hy | rfl)
            · exact ⟨⟨y, hN_le_top i.castSucc hy⟩,
                IntermediateField.subset_adjoin F _ (Or.inl hy), rfl⟩
            · exact ⟨η' i, IntermediateField.subset_adjoin F _ (Or.inr rfl), rfl⟩
          obtain ⟨z, hz, hzx⟩ := hsub hmem
          exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
        · rw [IntermediateField.adjoin_le_iff]
          rintro ⟨y, hy⟩ (hyi | hyi)
          · change y ∈ N i.succ
            rw [hNsucc i]
            exact IntermediateField.subset_adjoin F _ (Or.inl hyi)
          · rw [Set.mem_singleton_iff] at hyi
            have hyeq : y = η i := congrArg Subtype.val hyi
            change y ∈ N i.succ
            rw [hyeq, hNsucc i]
            exact IntermediateField.subset_adjoin F _ (Or.inr rfl)
  -- Property 1: `x ^ (p ^ D (Fin.last r)) ∈ Ntop` for every `x : L`:
  have hall_pow : ∀ x : L, x ^ (p ^ D (Fin.last r)) ∈ Ntop := fun x =>
    h_frob_mem r le_rfl x (by rw [show (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1)) = Fin.last r from rfl, hTlast]; trivial)
  -- Property 2: every `F`-separable `α ∈ L` already lies in `Ntop`:
  have hsep_mem : ∀ α : L, IsSeparable F α → α ∈ Ntop := by
    intro α hα_sep
    have hα_int : IsIntegral Ntop α := (hα_sep.isIntegral).tower_top
    have hα_sep_N : (minpoly Ntop α).Separable := by
      have hm_dvd : minpoly Ntop α ∣ (minpoly F α).map (algebraMap F Ntop) :=
        minpoly.dvd Ntop α (by
          rw [Polynomial.aeval_def, Polynomial.eval₂_map]
          exact minpoly.aeval F α)
      have hmap_sep : ((minpoly F α).map (algebraMap F Ntop)).Separable :=
        (Polynomial.separable_map (algebraMap F Ntop)).mpr hα_sep
      exact hmap_sep.of_dvd hm_dvd
    have hpow_mem : α ^ (p ^ D (Fin.last r)) ∈ Ntop := hall_pow α
    let c : Ntop := ⟨α ^ (p ^ D (Fin.last r)), hpow_mem⟩
    have hm_dvd_p : minpoly Ntop α ∣ Polynomial.X ^ (p ^ D (Fin.last r)) - Polynomial.C c := by
      apply minpoly.dvd Ntop α
      simp [c]
    have hfactor : (Polynomial.X ^ (p ^ D (Fin.last r)) - Polynomial.C c).map (algebraMap Ntop L) =
        (Polynomial.X - Polynomial.C α) ^ (p ^ D (Fin.last r)) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        sub_pow_char_pow, ← map_pow]
      rfl
    have hm_map_dvd : (minpoly Ntop α).map (algebraMap Ntop L) ∣
        (Polynomial.X - Polynomial.C α) ^ (p ^ D (Fin.last r)) := by
      rw [← hfactor]
      exact Polynomial.map_dvd (algebraMap Ntop L) hm_dvd_p
    have hm_deg1 : (minpoly Ntop α).natDegree = 1 := by
      let mL : L[X] := (minpoly Ntop α).map (algebraMap Ntop L)
      have hm_sep_L : mL.Separable :=
        (Polynomial.separable_map (algebraMap Ntop L)).mpr hα_sep_N
      have hsq : Squarefree mL := hm_sep_L.squarefree
      have hmL_ne0 : mL ≠ 0 :=
        ((minpoly.monic hα_int).map (algebraMap Ntop L)).ne_zero
      -- `mL` splits over `L` since it divides `(X - C α)^(p^D)`:
      have hspl_mL : mL.Splits :=
        (Polynomial.Splits.pow (Polynomial.Splits.X_sub_C α) _).of_dvd
          (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hm_map_dvd
      -- Every root of `mL` in `L` equals `α`, and `mL` is squarefree, so `mL.roots.card ≤ 1`:
      have hroots_nd : mL.roots.Nodup := Polynomial.nodup_roots hm_sep_L
      have hroots_sub : ∀ x ∈ mL.roots, x = α := by
        intro x hx
        have hzero : mL.eval x = 0 := (Polynomial.mem_roots hmL_ne0).mp hx
        rcases hm_map_dvd with ⟨q, hq⟩
        have hpow0 : (x - α) ^ (p ^ D (Fin.last r)) = 0 := by
          have := congrArg (Polynomial.eval x) hq
          rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
            Polynomial.eval_mul, hzero, zero_mul] at this
          exact this
        exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow0)
      have hcard_le1 : mL.roots.card ≤ 1 := by
        have hsub : mL.roots.toFinset ⊆ ({α} : Finset L) := by
          intro x hx
          exact Finset.mem_singleton.mpr (hroots_sub x (Multiset.mem_toFinset.mp hx))
        calc mL.roots.card = mL.roots.toFinset.card := (Multiset.toFinset_card_of_nodup hroots_nd).symm
          _ ≤ ({α} : Finset L).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton α
      have hdeg_eq : mL.natDegree = mL.roots.card :=
        (Polynomial.splits_iff_card_roots.mp hspl_mL).symm
      have hle1 : (minpoly Ntop α).natDegree ≤ 1 := by
        rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap Ntop L).injective]
        change mL.natDegree ≤ 1
        omega
      have hpos := minpoly.natDegree_pos hα_int
      omega
    -- A monic degree-1 minimal polynomial over `Ntop` forces `α ∈ Ntop`:
    have hm_mon : (minpoly Ntop α).Monic := minpoly.monic hα_int
    have hm_eval : Polynomial.aeval α (minpoly Ntop α) = 0 := minpoly.aeval Ntop α
    have hm_eq : minpoly Ntop α = Polynomial.X + Polynomial.C ((minpoly Ntop α).coeff 0) := by
      apply Polynomial.ext
      intro k
      rcases k with _ | _ | k
      · simp
      · change (minpoly Ntop α).coeff 1 = (Polynomial.X + Polynomial.C ((minpoly Ntop α).coeff 0)).coeff 1
        rw [Polynomial.coeff_add, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, add_zero,
          ← hm_deg1, hm_mon.coeff_natDegree]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X]
    rw [hm_eq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hm_eval
    have hα_eq : α = algebraMap Ntop L (-((minpoly Ntop α).coeff 0)) := by
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left hm_eval
    rw [hα_eq]
    exact (-((minpoly Ntop α).coeff 0)).2
  exact ⟨Ntop, D (Fin.last r), hrad_Ntop, hall_pow, hsep_mem⟩

/-- Helper Lemma B: if `Kbar` is an algebraically closed subfield of `F` and `N : F` has a radical
tower with step exponents `q_i` not divisible by `char F`, then `¬ (ringChar F ∣ Module.finrank F N)`. -/
private theorem not_char_dvd_finrank_of_radical_over_algClosed {Kbar : Type u} {F : Type v}
    {N : Type w} [Field Kbar] [Field F] [Field N] [Algebra Kbar F] [Algebra F N] [Algebra Kbar N]
    [IsScalarTower Kbar F N] [IsAlgClosed Kbar]
    {p : ℕ} (hp : Nat.Prime p) (hcharF : ringChar F = p)
    (hrad : IsGarlingRadicalExtensionNotCharDvd F N) :
    ¬ (p ∣ Module.finrank F N) := by
  classical
  have _ : CharP F p := hcharF ▸ ringChar.charP F
  have hcharKbar : ringChar Kbar = p := (ringChar_eq_of_algebra Kbar F).symm.trans hcharF
  -- First prove single-step degree divisibility: if `B = A(η)` with `η^q ∈ A`, `p ∤ q`, and
  -- `Kbar ≤ A`, then `[B : A] ∣ q`:
  have hstep_dvd : ∀ {A B : Type w} [Field A] [Field B] [Algebra Kbar A] [Algebra A B]
      {q : ℕ} {η : B}, 1 ≤ q → ¬ (p ∣ q) →
      (∃ c : A, η ^ q = algebraMap A B c) →
      IntermediateField.adjoin A ({η} : Set B) = ⊤ →
      Module.finrank A B ∣ q := by
    intro A B _ _ _ _ q η hq1 hpq ⟨c, hηq⟩ hadj
    by_cases hη0 : η = 0
    · have hbot : (⊥ : IntermediateField A B) = ⊤ := by
        rw [← hadj]
        apply le_antisymm bot_le
        rw [IntermediateField.adjoin_le_iff]
        rintro _ rfl
        rw [hη0]; exact (⊥ : IntermediateField A B).zero_mem
      have h1 : Module.finrank A B = 1 := by
        have hbot1 : Module.finrank A (⊥ : IntermediateField A B) = 1 :=
          IntermediateField.finrank_bot
        have htop1 : Module.finrank A (⊤ : IntermediateField A B) = Module.finrank A B :=
          LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
        rw [← htop1, ← hbot, hbot1]
      rw [h1]; exact one_dvd q
    · have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hηq
        exact hη0 (eq_zero_of_pow_eq_zero hηq)
      -- Since `Kbar` is algebraically closed and `p ∤ q`, `Kbar` contains a primitive `q`th root of unity:
      have hcharK_q : ¬ (ringChar Kbar ∣ q) := by rwa [hcharKbar]
      have hsf_Kbar : IsGarlingSplittingFieldExtension Kbar Kbar (Polynomial.X ^ q - Polynomial.C (1 : Kbar)) := by
        have hspl : ((Polynomial.X ^ q - Polynomial.C (1 : Kbar)).map (algebraMap Kbar Kbar)).Splits :=
          IsAlgClosed.splits _
        have hadj' : Algebra.adjoin Kbar ((Polynomial.X ^ q - Polynomial.C (1 : Kbar)).rootSet Kbar) = ⊤ :=
          Subsingleton.elim _ _
        exact (isGarlingSplittingFieldExtension_iff Kbar Kbar _).mpr ⟨hspl, hadj'⟩
      obtain ⟨_, ⟨ωK, hωK⟩, _⟩ :=
        Garling.Chapter16.theorem_16_1 (one_ne_zero : (1 : Kbar) ≠ 0) hcharK_q hsf_Kbar
      let ωA : A := algebraMap Kbar A ωK
      have hωA : IsPrimitiveRoot ωA q := hωK.map_of_injective (algebraMap Kbar A).injective
      let ωB : B := algebraMap A B ωA
      have hωB : IsPrimitiveRoot ωB q := hωA.map_of_injective (algebraMap A B).injective
      -- `X^q - c` splits into distinct roots `ωB^j * η` in `B = A(η)`:
      have hfac : (Polynomial.X ^ q - Polynomial.C c).map (algebraMap A B) =
          ∏ j : Fin q, (Polynomial.X - Polynomial.C (ωB ^ (j : ℕ) * η)) := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hηq]
        exact Garling.Chapter16.X_pow_sub_C_pow_eq_prod hq1 hωB η
      have hspl_B : ((Polynomial.X ^ q - Polynomial.C c).map (algebraMap A B)).Splits := by
        rw [hfac]; exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
      have hη_root : η ∈ (Polynomial.X ^ q - Polynomial.C c).rootSet B := by
        rw [Polynomial.mem_rootSet]
        refine ⟨(Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero, ?_⟩
        simp [hηq]
      have hint_η : IsIntegral A η :=
        ⟨Polynomial.X ^ q - Polynomial.C c, Polynomial.monic_X_pow_sub_C c (by omega),
          (Polynomial.mem_rootSet.mp hη_root).2⟩
      have hsf_B : IsGarlingSplittingFieldExtension A B (Polynomial.X ^ q - Polynomial.C c) := by
        rw [isGarlingSplittingFieldExtension_iff]
        refine ⟨hspl_B, ?_⟩
        have hAlg : Algebra.adjoin A ({η} : Set B) = ⊤ := by
          rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_η.isAlgebraic, hadj]
          rfl
        exact eq_top_iff.mpr (hAlg ▸ Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hη_root))
      have hcharA : ¬ (ringChar A ∣ q) := by
        rwa [ringChar_eq_of_algebra Kbar A]
      have hpoly_sep : IsGarlingSeparablePoly (Polynomial.X ^ q - Polynomial.C c : A[X]) :=
        (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero hc0 hcharA).2.2.2.2
      have hgal_B : IsGarlingGaloisExtension A B :=
        Garling.Chapter16.isGarlingGalois_of_splittingField
          (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero hsf_B hpoly_sep
      have h161 := (Garling.Chapter16.theorem_16_1 hc0 hcharA hsf_B).2.2 ωB hωB
      have hAω_eq_bot : (A⟮ωB⟯ : IntermediateField A B) = ⊥ := by
        apply le_antisymm _ bot_le
        rw [IntermediateField.adjoin_le_iff]
        rintro _ rfl
        exact ⟨ωA, rfl⟩
      have hfin_eq : Module.finrank A B = Nat.card (B ≃ₐ[A] B) :=
        ((theorem_10_4_algEquiv (K := A) (L := B) hgal_B.1).1 hgal_B).symm
      let eGal : (B ≃ₐ[A] B) ≃* (B ≃ₐ[A⟮ωB⟯] B) :=
        { toFun := fun σ =>
            { σ.toRingEquiv with
              commutes' := fun ⟨y, hy⟩ => by
                rw [hAω_eq_bot, IntermediateField.mem_bot] at hy
                rcases hy with ⟨a, rfl⟩; exact σ.commutes a }
          invFun := fun σ =>
            { σ.toRingEquiv with
              commutes' := fun a => σ.commutes ⟨algebraMap A B a, (A⟮ωB⟯).algebraMap_mem a⟩ }
          left_inv := fun _ => by ext x; rfl
          right_inv := fun _ => by ext x; rfl
          map_mul' := fun _ _ => by ext x; rfl }
      rw [hfin_eq, Nat.card_congr eGal.toEquiv]
      exact h161.2.2.1
  -- Induct on tower length `r`:
  rcases hrad with ⟨r, T, η, q, hT0, hTlast, hchar_prod, hTstep⟩
  have hchar_q : ∀ i : Fin r, 1 ≤ q i ∧ ¬ (p ∣ q i) := by
    intro i
    have hi : ¬ (ringChar F ∣ q i) := (not_ringChar_dvd_prod_iff F q).mp hchar_prod i
    rw [hcharF] at hi
    refine ⟨?_, hi⟩
    by_contra h0
    have hq0 : q i = 0 := by omega
    rw [hq0] at hi
    exact hi (dvd_zero p)
  have hind : ∀ (k : ℕ) (hk : k ≤ r),
      ¬ (p ∣ Module.finrank F (T ⟨k, Nat.lt_succ_of_le hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (r + 1)) = 0 from rfl, hT0,
        IntermediateField.finrank_bot]
      exact hp.not_dvd_one
    | succ k ih =>
      intro hk
      let i : Fin r := ⟨k, hk⟩
      have hle : T i.castSucc ≤ T i.succ := by
        rw [(hTstep i).2]
        exact fun z hz => IntermediateField.subset_adjoin F _ (Or.inl hz)
      let _ : Algebra (T i.castSucc) (T i.succ) := (IntermediateField.inclusion hle).toAlgebra
      have _ : IsScalarTower F (T i.castSucc) (T i.succ) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let _ : Algebra Kbar (T i.castSucc) :=
        RingHom.toAlgebra ((algebraMap F (T i.castSucc)).comp (algebraMap Kbar F))
      let ηi : T i.succ := ⟨η i, by
        rw [(hTstep i).2]; exact IntermediateField.subset_adjoin F _ (Or.inr rfl)⟩
      have hη_pow : ∃ c : T i.castSucc, ηi ^ (q i) = algebraMap (T i.castSucc) (T i.succ) c :=
        ⟨⟨(η i) ^ (q i), (hTstep i).1⟩, Subtype.ext rfl⟩
      have hadj_step : IntermediateField.adjoin (T i.castSucc) ({ηi} : Set (T i.succ)) = ⊤ := by
        rw [eq_top_iff]
        intro ⟨x, hx⟩ _
        have hx' : x ∈ IntermediateField.adjoin F ((T i.castSucc : Set N) ∪ {η i}) := by
          rw [← (hTstep i).2]; exact hx
        let M : IntermediateField F N :=
          ((IntermediateField.adjoin (T i.castSucc) ({ηi} : Set (T i.succ))).restrictScalars F).map
            (T i.succ).val
        have hsub : IntermediateField.adjoin F ((T i.castSucc : Set N) ∪ {η i}) ≤ M := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y (hy | rfl)
          · exact ⟨⟨y, hle hy⟩,
              (IntermediateField.adjoin (T i.castSucc) _).algebraMap_mem ⟨y, hy⟩, rfl⟩
          · exact ⟨ηi, IntermediateField.subset_adjoin (T i.castSucc) _ rfl, rfl⟩
        obtain ⟨z, hz, hzx⟩ := hsub hx'
        exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
      have hdvd_step : Module.finrank (T i.castSucc) (T i.succ) ∣ q i :=
        hstep_dvd (A := T i.castSucc) (B := T i.succ) (hchar_q i).1 (hchar_q i).2 hη_pow hadj_step
      have hp_step : ¬ (p ∣ Module.finrank (T i.castSucc) (T i.succ)) :=
        fun hdiv => (hchar_q i).2 (hdiv.trans hdvd_step)
      have hfin_FN : IsFiniteExtension F N :=
        isFiniteExtension_of_isGarlingExtensionByRadicals
          (isGarlingExtensionByRadicals_of_notCharDvd ⟨r, T, η, q, hT0, hTlast, hchar_prod, hTstep⟩)
      have _ : Module.Finite F N := (isFiniteExtension_iff_moduleFinite F N).mp hfin_FN
      have _ : Module.Finite F (T i.succ) := inferInstance
      have _ : Module.Finite F (T i.castSucc) := inferInstance
      have _ : Module.Finite (T i.castSucc) (T i.succ) := Module.Finite.right F (T i.castSucc) (T i.succ)
      have htower := Module.finrank_mul_finrank F (T i.castSucc) (T i.succ)
      have hp_prev : ¬ (p ∣ Module.finrank F (T i.castSucc)) := ih (Nat.le_of_lt hk)
      change ¬ (p ∣ Module.finrank F (T i.succ))
      rw [← htower]
      exact fun hdiv => (hp.dvd_mul.mp hdiv).elim hp_prev hp_step
  have htop := hind r le_rfl
  rw [show (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1)) = Fin.last r from rfl, hTlast] at htop
  have htop_eq : Module.finrank F (⊤ : IntermediateField F N) = Module.finrank F N :=
    LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
  rwa [htop_eq] at htop

/-- Helper: if `Kbar : K` is algebraic inside an extension `Ω : K`, any `K`-algebraically
independent tuple `a : Fin n → Ω` remains algebraically independent over `Kbar`. -/
private theorem isGarlingAlgIndepTuple_over_algebraic {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] (Kbar : IntermediateField K Ω) (halg : IsAlgebraicExtension K Kbar)
    {n : ℕ} {a : Fin n → Ω} (ha : IsGarlingAlgIndepTuple K a) :
    IsGarlingAlgIndepTuple Kbar a := by
  classical
  have htr0 : transcendenceDegree K Kbar = 0 :=
    (transcendenceDegree_eq_zero_iff (K := K) (L := Kbar)).mpr halg
  let M : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar (Set.range a)
  have hM_tr_K : transcendenceDegree K M = (n : ℕ∞) := by
    have hKa_le : IntermediateField.adjoin K (Set.range a) ≤ M.restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin Kbar (Set.range a) ⟨i, rfl⟩
    let Ka := IntermediateField.adjoin K (Set.range a)
    let _ : Algebra Ka M := (IntermediateField.inclusion hKa_le).toAlgebra
    have _ : IsScalarTower K Ka M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    -- `Ka : K` has transcendence degree `n`:
    let aKa : Fin n → Ka := fun i => ⟨a i, IntermediateField.subset_adjoin K (Set.range a) ⟨i, rfl⟩⟩
    have ha_tb : IsGarlingTranscendenceBasis K (Set.range aKa) := by
      rw [theorem_18_4]
      have ha' : IsGarlingAlgIndepTuple K aKa := by
        intro p q hpq
        apply ha
        have hev : ∀ r : MvPolynomial (Fin n) K, ((evalMvRingHom K aKa r : Ka) : Ω) = evalMvRingHom K a r := by
          intro r
          exact AlgHom.congr_fun
            (MvPolynomial.algHom_ext
              (f := Ka.val.comp (MvPolynomial.aeval aKa))
              (g := MvPolynomial.aeval a) fun i => by simp [aKa]) r
        rw [← hev p, ← hev q]
        exact congrArg Subtype.val hpq
      refine ⟨(isGarlingAlgebraicallyIndependent_range_iff ha'.injective).mpr ha', ?_⟩
      have hadj : IntermediateField.adjoin K (Set.range aKa) = ⊤ := by
        rw [eq_top_iff]
        intro ⟨x, hx⟩ _
        let M0 : IntermediateField K Ω :=
          (IntermediateField.adjoin K (Set.range aKa)).map Ka.val
        have hsub : Ka ≤ M0 := by
          rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨i, rfl⟩
          exact ⟨aKa i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩
        obtain ⟨z, hz, hzx⟩ := hsub hx
        exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
      rw [hadj]
      intro x
      exact ⟨Polynomial.X - Polynomial.C (⟨x, trivial⟩ : (⊤ : IntermediateField K Ka)),
        Polynomial.X_sub_C_ne_zero _, by simp⟩
    have htr_Ka : transcendenceDegree K Ka = (n : ℕ∞) := by
      rw [transcendenceDegree_eq_setOrder ha_tb]
      have hfin : (Set.range aKa).Finite := Set.finite_range _
      rw [setOrder_eq_finset_card hfin]
      have : hfin.toFinset = Finset.univ.image aKa := by ext x; simp
      rw [this, Finset.card_image_of_injective _ (fun i j hij => ha.injective (congrArg Subtype.val hij)),
        Finset.card_fin]
    -- `M : Ka` is algebraic (generated over `Ka` by `Kbar`, which is algebraic over `K` hence over `Ka`):
    have hM_alg_Ka : IsAlgebraicExtension Ka M := by
      rw [isAlgebraicExtension_iff]
      have hsub : ∀ x : M, IsGarlingAlgebraic Ka x := by
        rintro ⟨x, hx⟩
        have hM_eq : (M : Set Ω) ⊆ (IntermediateField.adjoin K ((Kbar : Set Ω) ∪ Set.range a) : Set Ω) := by
          intro y hy
          let N1 : IntermediateField Kbar Ω :=
            { (IntermediateField.adjoin K ((Kbar : Set Ω) ∪ Set.range a)).toSubfield with
              algebraMap_mem' := fun z =>
                IntermediateField.subset_adjoin K _ (Or.inl z.2) }
          have hle1 : M ≤ N1 := IntermediateField.adjoin_le_iff.mpr fun z hz =>
            IntermediateField.subset_adjoin K _ (Or.inr hz)
          exact hle1 hy
        have hx' : x ∈ IntermediateField.adjoin K ((Kbar : Set Ω) ∪ Set.range a) := hM_eq hx
        let AlgM : IntermediateField K Ω :=
          { (algebraicIntermediateField Ka M).toSubfield.map M.val.toRingHom with
            algebraMap_mem' := fun c => by
              refine ⟨algebraMap K M c, ?_, rfl⟩
              exact (algebraicIntermediateField Ka M).algebraMap_mem (algebraMap K Ka c) }
        have hle2 : IntermediateField.adjoin K ((Kbar : Set Ω) ∪ Set.range a) ≤ AlgM := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y (hy | ⟨i, rfl⟩)
          · refine ⟨⟨y, M.algebraMap_mem ⟨y, hy⟩⟩, ?_, rfl⟩
            obtain ⟨f, hf0, hfy⟩ := halg ⟨y, hy⟩
            refine ⟨f.map (algebraMap K Ka), (Polynomial.map_ne_zero_iff (algebraMap K Ka).injective).mpr hf0, ?_⟩
            rw [Polynomial.aeval_map_algebraMap]
            apply Subtype.ext
            have h1 : (Polynomial.aeval (⟨y, M.algebraMap_mem ⟨y, hy⟩⟩ : M) f : Ω) =
                Polynomial.aeval y f := by
              change (M.val.restrictScalars K) (Polynomial.aeval (⟨y, M.algebraMap_mem ⟨y, hy⟩⟩ : M) f) = _
              rw [← Polynomial.aeval_algHom_apply]
              rfl
            have h2 : (Polynomial.aeval (⟨y, hy⟩ : Kbar) f : Ω) = Polynomial.aeval y f := by
              change Kbar.val (Polynomial.aeval (⟨y, hy⟩ : Kbar) f) = _
              rw [← Polynomial.aeval_algHom_apply]
              rfl
            rw [h1, ← h2]
            exact congrArg Subtype.val hfy
          · refine ⟨⟨a i, IntermediateField.subset_adjoin Kbar _ ⟨i, rfl⟩⟩, ?_, rfl⟩
            exact (algebraicIntermediateField Ka M).algebraMap_mem
              ⟨a i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
        obtain ⟨z, hz, hzx⟩ := hle2 hx'
        have hz_eq : z = ⟨x, hx⟩ := Subtype.ext hzx
        rw [← hz_eq]
        exact hz
      exact ⟨fun x => (isGarlingAlgebraic_iff Ka x).mp (hsub x)⟩
    have htr_M_Ka : transcendenceDegree Ka M = 0 :=
      (transcendenceDegree_eq_zero_iff (K := Ka) (L := M)).mpr hM_alg_Ka
    rw [corollary_to_theorem_18_8 K Ka M, htr_M_Ka, htr_Ka, zero_add]
  have hM_tr_Kbar : transcendenceDegree Kbar M = (n : ℕ∞) := by
    have h := corollary_to_theorem_18_8 K Kbar M
    rw [hM_tr_K, htr0, add_zero] at h
    exact h.symm
  -- Now `a` generates `M` over `Kbar`, so by `Theorem 18.5` it contains a transcendence basis of
  -- size `n`, hence `a` itself is `Kbar`-algebraically independent:
  let aM : Fin n → M := fun i => ⟨a i, IntermediateField.subset_adjoin Kbar _ ⟨i, rfl⟩⟩
  have haM_alg : IsAlgebraicExtension (IntermediateField.adjoin Kbar (Set.range aM)) M := by
    have hadj : IntermediateField.adjoin Kbar (Set.range aM) = ⊤ := by
      rw [eq_top_iff]
      intro ⟨x, hx⟩ _
      let N2 : IntermediateField Kbar Ω :=
        (IntermediateField.adjoin Kbar (Set.range aM)).map M.val
      have hsub : M ≤ N2 := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact ⟨aM i, IntermediateField.subset_adjoin Kbar _ ⟨i, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hsub hx
      exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
    rw [hadj]
    intro x
    exact ⟨Polynomial.X - Polynomial.C (⟨x, trivial⟩ : (⊤ : IntermediateField Kbar M)),
      Polynomial.X_sub_C_ne_zero _, by simp⟩
  obtain ⟨B, hB_tb, _, hB_sub⟩ :=
    theorem_18_5 (K := Kbar) (L := M) (C := ∅) (A := Set.range aM)
      haM_alg (Set.empty_subset _) (isGarlingAlgebraicallyIndependent_empty Kbar)
  have hord := transcendenceDegree_eq_setOrder hB_tb
  rw [hM_tr_Kbar] at hord
  have hfin_a : (Set.range aM).Finite := Set.finite_range aM
  have hfin_B : B.Finite := hfin_a.subset hB_sub
  have hcard_B : hfin_B.toFinset.card = n := by
    rw [setOrder_eq_finset_card hfin_B] at hord
    exact Nat.cast_injective hord.symm
  have hcard_a_le : hfin_a.toFinset.card ≤ n := by
    have : hfin_a.toFinset = Finset.univ.image aM := by ext x; simp
    rw [this]
    exact Finset.card_image_le.trans (by simp)
  have hB_eq_a_fin : hfin_B.toFinset = hfin_a.toFinset :=
    Finset.eq_of_subset_of_card_le (fun x hx => hfin_a.mem_toFinset.mpr (hB_sub (hfin_B.mem_toFinset.mp hx)))
      (by omega)
  have hB_eq_a : B = Set.range aM := by
    ext x; rw [← hfin_B.mem_toFinset, ← hfin_a.mem_toFinset, hB_eq_a_fin]
  have haM_indep : IsGarlingAlgebraicallyIndependent Kbar (Set.range aM) :=
    hB_eq_a ▸ ((theorem_18_4 B).mp hB_tb).1
  have haM_inj : Function.Injective aM := fun i j hij => ha.injective (congrArg Subtype.val hij)
  have haM_tup : IsGarlingAlgIndepTuple Kbar aM :=
    (isGarlingAlgebraicallyIndependent_range_iff haM_inj).mp haM_indep
  intro p q hpq
  apply haM_tup
  apply Subtype.ext
  have hev : ∀ r : MvPolynomial (Fin n) Kbar,
      ((evalMvRingHom Kbar aM r : M) : Ω) = evalMvRingHom Kbar a r := by
    intro r
    exact AlgHom.congr_fun
      (MvPolynomial.algHom_ext
        (f := M.val.comp (MvPolynomial.aeval aM))
        (g := MvPolynomial.aeval a) fun i => by simp [aM]) r
  rw [hev p, hev q]
  exact hpq

private theorem isGarlingSoluble_sigmaN_of_le_four {n : ℕ} (hn : n ≤ 4) :
    IsGarlingSoluble (SigmaN n) := by
  interval_cases n
  · exact isGarlingSoluble_of_subsingleton
  · exact isGarlingSoluble_of_subsingleton
  · have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have _ : IsCyclic (SigmaN 2) :=
      isCyclic_of_prime_card (p := 2) (by rw [Nat.card_perm, Nat.card_fin]; decide)
    exact isGarlingSoluble_of_isCyclic
  · exact section_17_1_soluble_examples.2.1
  · exact section_17_1_soluble_examples.2.2.2.1

/-- Helper: if a non-zero polynomial `f : F[X]` splits over `N : F`, then the intermediate field
generated by its roots in `N` is a Garling splitting field extension of `f` over `F`. -/
private theorem exists_splittingField_intermediateField_of_splits {F N : Type*} [Field F] [Field N]
    [Algebra F N] {f : F[X]} (hf : f ≠ 0) (hspl : GarlingSplitsOver F N f) :
    ∃ S : IntermediateField F N, IsGarlingSplittingFieldExtension F S f := by
  rcases hspl with ⟨m, lam, α, hexp⟩
  unfold GarlingSplitsExplicit at hexp
  let S : IntermediateField F N := IntermediateField.adjoin F (Set.range α)
  refine ⟨S, ?_, ?_⟩
  · refine ⟨m, lam, fun j => ⟨α j, IntermediateField.subset_adjoin F _ ⟨j, rfl⟩⟩, ?_⟩
    unfold GarlingSplitsExplicit
    apply Polynomial.map_injective S.val.toRingHom S.val.injective
    have hcomp : (f.map (algebraMap F S)).map S.val.toRingHom = f.map (algebraMap F N) := by
      rw [Polynomial.map_map]; rfl
    rw [hcomp, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  · intro M hM hMspl
    rcases hMspl with ⟨k, mu, β, hMexp⟩
    unfold GarlingSplitsExplicit at hMexp
    let ι : M →+* N := S.val.toRingHom.comp M.val.toRingHom
    have hmapM : f.map (algebraMap F N) =
        Polynomial.C (algebraMap F N mu) *
          ∏ j : Fin k, (Polynomial.X - Polynomial.C (ι (β j))) := by
      have h1 := congrArg (Polynomial.map ι) hMexp
      have hcomp : (f.map (algebraMap F M)).map ι = f.map (algebraMap F N) := by
        rw [Polynomial.map_map]; rfl
      rw [hcomp] at h1
      simpa [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, ι] using h1
    have hmu0 : algebraMap F N mu ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hmapM
      exact (Polynomial.map_ne_zero_iff (algebraMap F N).injective).mpr hf hmapM
    have hα_mem : ∀ j : Fin m, α j ∈ M.map S.val := by
      intro j
      have hroot : (f.map (algebraMap F N)).eval (α j) = 0 := by
        rw [hexp, Polynomial.eval_mul, Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
      rw [hmapM, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hroot
      have hprod0 := (mul_eq_zero.mp hroot).resolve_left hmu0
      obtain ⟨l, _, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hl
      rw [hl]
      exact ⟨(β l : S), (β l).2, rfl⟩
    have hS_le : S ≤ M.map S.val := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hα_mem j
    apply hM
    rw [eq_top_iff]
    intro x _
    obtain ⟨z, hz, hzx⟩ := hS_le x.2
    exact (Subtype.ext hzx : z = x) ▸ hz

/-- Abstracted inner step for `Theorem 19.3` in prime characteristic `p`: over an algebraically
closed base `Kbar`, if the generic polynomial of degree `n ≥ 1` in `Kbar`-independent `aΩ : Fin n → Ω`
splits in a radical extension `L'` of `F' = Kbar(aΩ)`, then `¬ (p ∣ n!)`. -/
private theorem not_char_dvd_factorial_of_generic_splits_over_algClosed
    {Kbar Ω L' : Type*} [Field Kbar] [Field Ω] [Field L']
    [Algebra Kbar Ω] [IsAlgClosed Kbar]
    {n : ℕ} (hn1 : 1 ≤ n) {aΩ : Fin n → Ω} (haΩ : IsGarlingAlgIndepTuple Kbar aΩ)
    [Algebra (IntermediateField.adjoin Kbar (Set.range aΩ)) L']
    {p : ℕ} (hp : Nat.Prime p) (hcharF' : ringChar (IntermediateField.adjoin Kbar (Set.range aΩ)) = p)
    (hradL' : IsGarlingExtensionByRadicals (IntermediateField.adjoin Kbar (Set.range aΩ)) L')
    (hsplL' : GarlingSplitsOver (IntermediateField.adjoin Kbar (Set.range aΩ)) L'
      (garlingGenericPolyOverAdjoin Kbar aΩ)) :
    ¬ (p ∣ n.factorial) := by
  classical
  let F' := IntermediateField.adjoin Kbar (Set.range aΩ)
  let f' := garlingGenericPolyOverAdjoin Kbar aΩ
  let _ : Algebra Kbar L' := RingHom.toAlgebra ((algebraMap F' L').comp (algebraMap Kbar F'))
  have _ : IsScalarTower Kbar F' L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨N', _, hradN', _, hsepN'⟩ :=
    frobenius_reduction_of_radical_extension hp hcharF' hradL'
  have hp_not_dvd_N' : ¬ (p ∣ Module.finrank F' N') :=
    not_char_dvd_finrank_of_radical_over_algClosed (Kbar := Kbar) hp hcharF' hradN'
  obtain ⟨_, _, hf'_sep, _, hgal'⟩ := theorem_19_3_clauses_1_to_3 hn1 haΩ
  have hsplN' : GarlingSplitsOver F' N' f' := by
    rcases hsplL' with ⟨m, lam, α, hexp⟩
    unfold GarlingSplitsExplicit at hexp
    have hα_mem : ∀ j : Fin m, α j ∈ N' := by
      intro j
      apply hsepN' (α j)
      have hroot : Polynomial.aeval (α j) f' = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp,
          Polynomial.eval_mul, Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
      exact hf'_sep.of_dvd (minpoly.dvd F' (α j) hroot)
    refine ⟨m, lam, fun j => ⟨α j, hα_mem j⟩, ?_⟩
    unfold GarlingSplitsExplicit
    apply Polynomial.map_injective N'.val.toRingHom N'.val.injective
    have h1 : (f'.map (algebraMap F' N')).map N'.val.toRingHom = f'.map (algebraMap F' L') := by
      rw [Polynomial.map_map]; rfl
    rw [h1, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  obtain ⟨S', hsf_S'⟩ :=
    exists_splittingField_intermediateField_of_splits (garlingGenericPoly_monic _).ne_zero hsplN'
  obtain ⟨eGal'⟩ := hgal' S' hsf_S'
  have hgal_S' : IsGarlingGaloisExtension F' S' :=
    Garling.Chapter16.isGarlingGalois_of_splittingField
      (garlingGenericPoly_monic _).ne_zero hsf_S'
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f').mp hf'_sep).2.2
  have hfin_S' : Module.finrank F' S' = n.factorial := by
    have h1 := (theorem_10_4_algEquiv (K := F') (L := S') hgal_S'.1).1 hgal_S'
    rw [← h1, Nat.card_congr eGal'.toEquiv, Nat.card_perm, Nat.card_fin]
  have _ : Module.Finite F' N' :=
    (isFiniteExtension_iff_moduleFinite F' N').mp
      (isFiniteExtension_of_isGarlingExtensionByRadicals
        (isGarlingExtensionByRadicals_of_notCharDvd hradN'))
  have _ : Module.Finite F' S' := Module.Finite.left F' S' N'
  have _ : Module.Finite S' N' := Module.Finite.right F' S' N'
  have hdvd_fact : n.factorial ∣ Module.finrank F' N' := by
    rw [← hfin_S']
    exact ⟨Module.finrank S' N', (Module.finrank_mul_finrank F' S' N').symm⟩
  exact fun hp_dvd => hp_not_dvd_N' (hp_dvd.trans hdvd_fact)

/-- Abstracted helper for `Theorem 19.3` in prime characteristic `p`: given an algebraically closed
extension `Ω` of a radical extension `L` of `K(a₁, …, aₙ)` over which the generic polynomial
splits, `¬ (p ∣ n!)`. Abstracting `Ω` prevents `AlgebraicClosure L` unfolding during `isDefEq`. -/
private theorem not_char_dvd_factorial_of_generic_splits_in_algClosed
    {K E L Ω : Type*} [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] {n : ℕ} (hn1 : 1 ≤ n) {a : Fin n → E} (ha : IsGarlingAlgIndepTuple K a)
    [Algebra (IntermediateField.adjoin K (Set.range a)) L]
    [Algebra K L] [IsScalarTower K (IntermediateField.adjoin K (Set.range a)) L]
    [Algebra L Ω] [Algebra (IntermediateField.adjoin K (Set.range a)) Ω] [Algebra K Ω]
    [IsScalarTower (IntermediateField.adjoin K (Set.range a)) L Ω]
    [IsScalarTower K (IntermediateField.adjoin K (Set.range a)) Ω]
    [IsAlgClosed Ω]
    {p : ℕ} (hp : Nat.Prime p) (hcharK : ringChar K = p)
    (hradL : IsGarlingExtensionByRadicals (IntermediateField.adjoin K (Set.range a)) L)
    (hsplL : GarlingSplitsOver (IntermediateField.adjoin K (Set.range a)) L
      (garlingGenericPolyOverAdjoin K a)) :
    ¬ (p ∣ n.factorial) := by
  classical
  let K_a := IntermediateField.adjoin K (Set.range a)
  let f := garlingGenericPolyOverAdjoin K a
  have hcharKa : ringChar K_a = p := (ringChar_eq_of_algebra K K_a).trans hcharK
  let Kbar : IntermediateField K Ω := algebraicIntermediateField K Ω
  have hKbar_alg : IsAlgebraicExtension K Kbar := fun ⟨x, hx⟩ => by
    have ⟨g, hg0, hgx⟩ := hx
    refine ⟨g, hg0, ?_⟩
    apply Subtype.ext
    change Kbar.val (Polynomial.aeval (⟨x, hx⟩ : Kbar) g) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hgx
  have hKbar_closed : IsAlgClosed Kbar := by
    refine IsAlgClosed.of_exists_root Kbar fun g hg_mon hg_irr => ?_
    have hdeg_pos : 0 < g.natDegree := hg_irr.natDegree_pos
    have hdeg : (g.map (algebraMap Kbar Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective (algebraMap Kbar Ω).injective,
        Polynomial.degree_eq_natDegree hg_mon.ne_zero]
      exact ne_of_gt (by exact_mod_cast hdeg_pos)
    obtain ⟨rΩ, hrΩ⟩ := IsAlgClosed.exists_root (g.map (algebraMap Kbar Ω)) hdeg
    have hr_alg_Kbar : IsGarlingAlgebraic Kbar rΩ := by
      refine ⟨g, hg_mon.ne_zero, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact hrΩ
    have hr_alg_K : IsGarlingAlgebraic K rΩ := by
      have h1 : IsAlgebraic Kbar rΩ := (isGarlingAlgebraic_iff Kbar rΩ).mp hr_alg_Kbar
      have _ : Algebra.IsAlgebraic K Kbar := (isAlgebraicExtension_iff K Kbar).mp hKbar_alg
      exact (isGarlingAlgebraic_iff K rΩ).mpr (IsAlgebraic.restrictScalars K h1)
    refine ⟨⟨rΩ, hr_alg_K⟩, ?_⟩
    apply (algebraMap Kbar Ω).injective
    rw [map_zero, ← Polynomial.eval_map_apply]
    exact hrΩ
  let _ : IsAlgClosed Kbar := hKbar_closed
  let aΩ : Fin n → Ω := fun i =>
    algebraMap K_a Ω ⟨a i, IntermediateField.subset_adjoin K (Set.range a) ⟨i, rfl⟩⟩
  have haΩ_K : IsGarlingAlgIndepTuple K aΩ := by
    intro p1 p2 hpq
    apply ha
    have hmem_eval : ∀ r : MvPolynomial (Fin n) K, evalMvRingHom K a r ∈ K_a := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C c => rw [evalMvRingHom_C]; exact K_a.algebraMap_mem c
      | add u v hu hv => rw [map_add]; exact K_a.add_mem hu hv
      | mul_X u i hu =>
        rw [map_mul, evalMvRingHom_X]
        exact K_a.mul_mem hu (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
    have h1 : ∀ r : MvPolynomial (Fin n) K,
        evalMvRingHom K aΩ r = algebraMap K_a Ω ⟨evalMvRingHom K a r, hmem_eval r⟩ := by
      intro r
      induction r using MvPolynomial.induction_on with
      | C c =>
        rw [evalMvRingHom_C]
        have hc : (⟨evalMvRingHom K a (MvPolynomial.C c), hmem_eval (MvPolynomial.C c)⟩ : K_a) =
            algebraMap K K_a c := Subtype.ext (evalMvRingHom_C K a c)
        rw [hc, ← IsScalarTower.algebraMap_apply K K_a Ω c]
      | add u v hu hv =>
        have hadd : (⟨evalMvRingHom K a (u + v), hmem_eval (u + v)⟩ : K_a) =
            ⟨evalMvRingHom K a u, hmem_eval u⟩ + ⟨evalMvRingHom K a v, hmem_eval v⟩ :=
          Subtype.ext (map_add _ u v)
        rw [map_add, hu, hv, ← map_add, ← hadd]
      | mul_X u i hu =>
        have hmul : (⟨evalMvRingHom K a (u * MvPolynomial.X i), hmem_eval (u * MvPolynomial.X i)⟩ : K_a) =
            ⟨evalMvRingHom K a u, hmem_eval u⟩ * ⟨a i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩ :=
          Subtype.ext (show evalMvRingHom K a (u * MvPolynomial.X i) = evalMvRingHom K a u * a i by
            rw [map_mul, evalMvRingHom_X])
        rw [map_mul, evalMvRingHom_X, hu, ← map_mul, ← hmul]
    rw [h1 p1, h1 p2] at hpq
    exact congrArg Subtype.val ((algebraMap K_a Ω).injective hpq)
  have haΩ_Kbar : IsGarlingAlgIndepTuple Kbar aΩ :=
    isGarlingAlgIndepTuple_over_algebraic Kbar hKbar_alg haΩ_K
  let F' : IntermediateField Kbar Ω := IntermediateField.adjoin Kbar (Set.range aΩ)
  let f' : F'[X] := garlingGenericPolyOverAdjoin Kbar aΩ
  have hKa_le_F' : ∀ x : K_a, algebraMap K_a Ω x ∈ F' := by
    rintro ⟨x, hx⟩
    let M0 : IntermediateField K E :=
      { carrier := {y : E | ∃ hy : y ∈ K_a, algebraMap K_a Ω ⟨y, hy⟩ ∈ F'}
        add_mem' := fun {u v} ⟨hu, hu'⟩ ⟨hv, hv'⟩ =>
          ⟨K_a.add_mem hu hv, by
            have hadd : (⟨u + v, K_a.add_mem hu hv⟩ : K_a) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
            rw [hadd, map_add]; exact F'.add_mem hu' hv'⟩
        zero_mem' := ⟨K_a.zero_mem, by
          have hz : (⟨0, K_a.zero_mem⟩ : K_a) = 0 := rfl
          rw [hz, map_zero]; exact F'.zero_mem⟩
        mul_mem' := fun {u v} ⟨hu, hu'⟩ ⟨hv, hv'⟩ =>
          ⟨K_a.mul_mem hu hv, by
            have hmul : (⟨u * v, K_a.mul_mem hu hv⟩ : K_a) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
            rw [hmul, map_mul]; exact F'.mul_mem hu' hv'⟩
        one_mem' := ⟨K_a.one_mem, by
          have ho : (⟨1, K_a.one_mem⟩ : K_a) = 1 := rfl
          rw [ho, map_one]; exact F'.one_mem⟩
        inv_mem' := fun {u} ⟨hu, hu'⟩ =>
          ⟨K_a.inv_mem hu, by
            have hinv : (⟨u⁻¹, K_a.inv_mem hu⟩ : K_a) = ⟨u, hu⟩⁻¹ := rfl
            rw [hinv, map_inv₀]; exact F'.inv_mem hu'⟩
        algebraMap_mem' := fun c =>
          ⟨K_a.algebraMap_mem c, by
            have hc : (⟨algebraMap K E c, K_a.algebraMap_mem c⟩ : K_a) = algebraMap K K_a c := rfl
            rw [hc, ← IsScalarTower.algebraMap_apply K K_a Ω c]
            exact F'.algebraMap_mem (algebraMap K Kbar c)⟩ }
    have hle0 : K_a ≤ M0 := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨IntermediateField.subset_adjoin K _ ⟨i, rfl⟩,
        IntermediateField.subset_adjoin Kbar _ ⟨i, rfl⟩⟩
    exact (hle0 hx).2
  let ιKF' : K_a →+* F' :=
    { toFun := fun x => ⟨algebraMap K_a Ω x, hKa_le_F' x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hf_map_f' : f.map ιKF' = f' := by
    rw [show f = garlingGenericPolyOverAdjoin K a from rfl, garlingGenericPolyOverAdjoin,
      garlingGenericPoly_map, show f' = garlingGenericPolyOverAdjoin Kbar aΩ from rfl,
      garlingGenericPolyOverAdjoin]
    congr 1
  let L' : IntermediateField F' Ω :=
    IntermediateField.adjoin F' (Set.range (algebraMap L Ω))
  let ιLL' : L →+* L' :=
    { toFun := fun y => ⟨algebraMap L Ω y, IntermediateField.subset_adjoin F' _ ⟨y, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hι_comm : ∀ c : K_a, ιLL' (algebraMap K_a L c) = algebraMap F' L' (ιKF' c) := fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply K_a L Ω c).symm
  have hradL' : IsGarlingExtensionByRadicals F' L' := by
    rcases hradL with ⟨r, T, β, hT0, hTlast, hTstep⟩
    let T' : Fin (r + 1) → IntermediateField F' L' := fun j =>
      IntermediateField.adjoin F' (ιLL' '' (T j : Set L))
    let β' : Fin r → L' := fun i => ιLL' (β i)
    refine ⟨r, T', β', ?_, ?_, fun i => ?_⟩
    · apply le_antisymm _ bot_le
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [hT0] at hy
      rcases IntermediateField.mem_bot.mp hy with ⟨c, rfl⟩
      exact ⟨ιKF' c, (hι_comm c).symm⟩
    · rw [eq_top_iff]
      intro ⟨x, hx⟩ _
      let M1 : IntermediateField F' Ω := (T' (Fin.last r)).map L'.val
      have hsub1 : L' ≤ M1 := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨y, rfl⟩
        exact ⟨ιLL' y, IntermediateField.subset_adjoin F' _ ⟨y, by rw [hTlast]; trivial, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hsub1 hx
      exact (Subtype.ext hzx : z = ⟨x, hx⟩) ▸ hz
    · obtain ⟨⟨m, hm1, hpow⟩, hadj⟩ := hTstep i
      refine ⟨⟨m, hm1, ?_⟩, ?_⟩
      · change (ιLL' (β i)) ^ m ∈ T' i.castSucc
        rw [← map_pow]
        exact IntermediateField.subset_adjoin F' _ ⟨(β i) ^ m, hpow, rfl⟩
      · apply le_antisymm
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨y, hy, rfl⟩
          rw [hadj] at hy
          let A_step : IntermediateField F' L' :=
            IntermediateField.adjoin F' ((T' i.castSucc : Set L') ∪ {β' i})
          let M2 : IntermediateField K_a L :=
            { carrier := {w : L | ιLL' w ∈ A_step}
              add_mem' := fun {u v} hu hv => by
                show ιLL' (u + v) ∈ A_step
                rw [map_add]; exact A_step.add_mem hu hv
              zero_mem' := by
                show ιLL' 0 ∈ A_step
                rw [map_zero]; exact A_step.zero_mem
              mul_mem' := fun {u v} hu hv => by
                show ιLL' (u * v) ∈ A_step
                rw [map_mul]; exact A_step.mul_mem hu hv
              one_mem' := by
                show ιLL' 1 ∈ A_step
                rw [map_one]; exact A_step.one_mem
              inv_mem' := fun {u} hu => by
                show ιLL' u⁻¹ ∈ A_step
                rw [map_inv₀]; exact A_step.inv_mem hu
              algebraMap_mem' := fun c => by
                show ιLL' (algebraMap K_a L c) ∈ A_step
                rw [hι_comm c]
                exact A_step.algebraMap_mem (ιKF' c) }
          have hle2 : IntermediateField.adjoin K_a ((T i.castSucc : Set L) ∪ {β i}) ≤ M2 := by
            rw [IntermediateField.adjoin_le_iff]
            rintro w (hw | rfl)
            · exact IntermediateField.subset_adjoin F' _
                (Or.inl (IntermediateField.subset_adjoin F' _ ⟨w, hw, rfl⟩))
            · exact IntermediateField.subset_adjoin F' _ (Or.inr rfl)
          exact hle2 hy
        · rw [IntermediateField.adjoin_le_iff]
          rintro z (hz | rfl)
          · have hle_T : T' i.castSucc ≤ T' i.succ := by
              refine IntermediateField.adjoin.mono F' _ _ (Set.image_mono fun w hw => ?_)
              rw [hadj]
              exact IntermediateField.subset_adjoin K_a _ (Or.inl hw)
            exact hle_T hz
          · exact IntermediateField.subset_adjoin F' _
              ⟨β i, by rw [hadj]; exact IntermediateField.subset_adjoin K_a _ (Or.inr rfl), rfl⟩
  have hcharF' : ringChar F' = p := (ringChar_eq_of_ringHom ιKF').trans hcharKa
  have hsplL' : GarlingSplitsOver F' L' f' := by
    rcases hsplL with ⟨m, lam, α, hexp⟩
    unfold GarlingSplitsExplicit at hexp
    refine ⟨m, ιKF' lam, fun j => ιLL' (α j), ?_⟩
    unfold GarlingSplitsExplicit
    have hcomp : (algebraMap F' L').comp ιKF' = ιLL'.comp (algebraMap K_a L) :=
      RingHom.ext fun c => (hι_comm c).symm
    rw [← hf_map_f', Polynomial.map_map, hcomp, ← Polynomial.map_map, hexp,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, ← hι_comm lam]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact not_char_dvd_factorial_of_generic_splits_over_algClosed (Kbar := Kbar) (L' := L')
    hn1 haΩ_Kbar hp hcharF' hradL' hsplL'

/-- **Theorem 19.3 (Exact Universal Solvability Characterization across all fields `K` and all `n : ℕ`)**:
The generic polynomial `xⁿ - a₁ x^{n-1} + ⋯ + (-1)ⁿ aₙ` over `K(a₁, …, aₙ)` is solvable by radicals
**if and only if** `n ≤ 4 ∧ ¬ (ringChar K ∣ n.factorial)`.

In particular, Garling's printed Clause 4 (*"if and only if `n ≤ 4`"* without characteristic guard)
is **false** in characteristic `2` for `n = 2, 3, 4` and in characteristic `3` for `n = 3, 4`, and
**true** whenever `char K = 0` or `char K ≥ 5`. -/
theorem theorem_19_3_solvable_iff {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {a : Fin n → E} (ha : IsGarlingAlgIndepTuple K a) :
    IsGarlingSolvableByRadicals (garlingGenericPolyOverAdjoin K a) ↔
      n ≤ 4 ∧ ¬ (ringChar K ∣ n.factorial) := by
  classical
  let K_a := IntermediateField.adjoin K (Set.range a)
  let f := garlingGenericPolyOverAdjoin K a
  have hcharKa : ringChar K_a = ringChar K := ringChar_eq_of_algebra K K_a
  constructor
  · -- Forward direction: solvable by radicals ⟹ `n ≤ 4 ∧ ¬ (ringChar K ∣ n!)`:
    intro hsol
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨by omega, ?_⟩
      intro hdiv
      have h1 : ringChar K = 1 := Nat.eq_one_of_dvd_one hdiv
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
      · exact hp.ne_one h1
      · omega
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      obtain ⟨_, _, hf_sep, hf_gsep, hgal⟩ := theorem_19_3_clauses_1_to_3 hn1 ha
      let F := f.SplittingField
      have hsfF : IsGarlingSplittingFieldExtension K_a F f :=
        (isGarlingSplittingFieldExtension_iff K_a F f).mpr inferInstance
      obtain ⟨eGal⟩ := hgal F hsfF
      rcases hsol with ⟨L, hLfield, hLalg, hradL, hsplL⟩
      let _ : Field L := hLfield
      let _ : Algebra K_a L := hLalg
      by_cases hch0 : ringChar K = 0
      · -- Characteristic 0: `Theorem 17.6` directly gives `IsGarlingSoluble (Σₙ)`, hence `n ≤ 4`:
        have hchKa0 : ringChar K_a = 0 := hcharKa.trans hch0
        rcases hradL with ⟨r, T, β, hT0, hTlast, hTstep⟩
        choose m hm1 hpow using fun i => (hTstep i).1
        have hchar_m : ¬ (ringChar K_a ∣ ∏ i : Fin r, m i) := by
          rw [hchKa0, zero_dvd_iff]
          exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.pos_iff_ne_zero.mp (hm1 i)
        have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup K_a F f) :=
          theorem_17_6 hT0 hTlast (fun i => ⟨hpow i, (hTstep i).2⟩) hchar_m hsplL hsfF
        have hsol_Sn : IsGarlingSoluble (SigmaN n) := (isGarlingSoluble_congr eGal).mp hsol_gal
        have hn4 : n ≤ 4 := by
          by_contra h5
          exact (corollary_to_theorem_17_2 (by omega)).1 hsol_Sn
        refine ⟨hn4, ?_⟩
        rw [hch0, zero_dvd_iff]
        exact Nat.factorial_ne_zero n
      · -- Positive prime characteristic `p = ringChar K`:
        have hp : Nat.Prime (ringChar K) :=
          (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hch0
        set p := ringChar K with hp_eq
        -- Step 1: Apply Lemma A inside `L` to deduce `n ≤ 4` via `Theorem 17.6`:
        obtain ⟨N, _, hradN, _, hsepN⟩ :=
          frobenius_reduction_of_radical_extension hp hcharKa hradL
        have hsplN : GarlingSplitsOver K_a N f := by
          rcases hsplL with ⟨m, lam, α, hexp⟩
          unfold GarlingSplitsExplicit at hexp
          have hα_mem : ∀ j : Fin m, α j ∈ N := by
            intro j
            apply hsepN (α j)
            have hroot : Polynomial.aeval (α j) f = 0 := by
              rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp,
                Polynomial.eval_mul, Polynomial.eval_prod]
              exact mul_eq_zero_of_right _
                (Finset.prod_eq_zero (Finset.mem_univ j) (by simp))
            exact hf_sep.of_dvd (minpoly.dvd K_a (α j) hroot)
          refine ⟨m, lam, fun j => ⟨α j, hα_mem j⟩, ?_⟩
          unfold GarlingSplitsExplicit
          apply Polynomial.map_injective N.val.toRingHom N.val.injective
          have h1 : (f.map (algebraMap K_a N)).map N.val.toRingHom = f.map (algebraMap K_a L) := by
            rw [Polynomial.map_map]; rfl
          rw [h1, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
          rfl
        rcases hradN with ⟨rN, TN, βN, qN, hTN0, hTNlast, hchar_qN, hTNstep⟩
        have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup K_a F f) :=
          theorem_17_6 hTN0 hTNlast hTNstep hchar_qN hsplN hsfF
        have hsol_Sn : IsGarlingSoluble (SigmaN n) := (isGarlingSoluble_congr eGal).mp hsol_gal
        have hn4 : n ≤ 4 := by
          by_contra h5
          exact (corollary_to_theorem_17_2 (by omega)).1 hsol_Sn
        -- Step 2: Instantiate the abstracted `Ω`-lemma at `Ω := AlgebraicClosure L`:
        let _ : Algebra K L := RingHom.toAlgebra ((algebraMap K_a L).comp (algebraMap K K_a))
        have _ : IsScalarTower K K_a L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        exact ⟨hn4, not_char_dvd_factorial_of_generic_splits_in_algClosed
          (Ω := AlgebraicClosure L) hn1 ha hp hp_eq.symm hradL hsplL⟩
  · -- Backward direction: `n ≤ 4 ∧ ¬ (ringChar K ∣ n!) ⟹ IsGarlingSolvableByRadicals f`:
    rintro ⟨hn4, hchar_fact⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hf1 : f = 1 := by simp [f, garlingGenericPolyOverAdjoin, garlingGenericPoly]
      change IsGarlingSolvableByRadicals f
      rw [hf1]
      exact isGarlingSolvableByRadicals_of_extension (isGarlingExtensionByRadicals_self K_a)
        ⟨0, 1, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      obtain ⟨_, _, _, hf_gsep, hgal⟩ := theorem_19_3_clauses_1_to_3 hn1 ha
      let F := f.SplittingField
      have hsfF : IsGarlingSplittingFieldExtension K_a F f :=
        (isGarlingSplittingFieldExtension_iff K_a F f).mpr inferInstance
      obtain ⟨eGal⟩ := hgal F hsfF
      have hsol_Sn : IsGarlingSoluble (SigmaN n) := isGarlingSoluble_sigmaN_of_le_four hn4
      have hsol_gal : IsGarlingSoluble (GarlingPolyGaloisGroup K_a F f) :=
        (isGarlingSoluble_congr eGal).mpr hsol_Sn
      have hcard_gal : Nat.card (GarlingPolyGaloisGroup K_a F f) = n.factorial := by
        rw [Nat.card_congr eGal.toEquiv, Nat.card_perm, Nat.card_fin]
      have hchar_gal : ¬ (ringChar K_a ∣ Nat.card (GarlingPolyGaloisGroup K_a F f)) := by
        rwa [hcharKa, hcard_gal]
      exact theorem_17_3 hf_gsep hsfF hsol_gal hchar_gal

/-- Universal positive-characteristic refutation of Clause 4 of `Theorem 19.3`:
whenever `ringChar K ∣ n!` (in particular `char K = 2` with `n = 2, 3, 4` or `char K = 3` with
`n = 3, 4`), the generic polynomial of degree `n` is **not** solvable by radicals. -/
theorem theorem_19_3_char_dvd_factorial_not_solvable {K E : Type*} [Field K] [Field E]
    [Algebra K E] {n : ℕ} {a : Fin n → E} (ha : IsGarlingAlgIndepTuple K a)
    (hdvd : ringChar K ∣ n.factorial) :
    ¬ IsGarlingSolvableByRadicals (garlingGenericPolyOverAdjoin K a) := by
  rw [theorem_19_3_solvable_iff ha]
  intro h
  exact h.2 hdvd

/-- Concrete characteristic-2 counterexample (`K = ℤ₂`, `n = 2`) to Garling's printed Clause 4
of `Theorem 19.3` (`2 ≤ 4`, yet the generic quadratic `x² - a₁ x + a₂` over `ℤ₂(a₁, a₂)` is NOT
solvable by radicals). -/
theorem theorem_19_3_char_two_counterexample :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let a := canonVar (ZMod 2) 2
    IsGarlingAlgIndepTuple (ZMod 2) a ∧
    (2 : ℕ) ≤ 4 ∧
    ¬ IsGarlingSolvableByRadicals (garlingGenericPolyOverAdjoin (ZMod 2) a) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨canonVar_algIndep (ZMod 2) 2, by omega, ?_⟩
  apply theorem_19_3_char_dvd_factorial_not_solvable (canonVar_algIndep (ZMod 2) 2)
  rw [ZMod.ringChar_zmod_n]
  decide

/-- Concrete characteristic-3 counterexample (`K = ℤ₃`, `n = 3`) to Garling's printed Clause 4
of `Theorem 19.3` (`3 ≤ 4`, yet the generic cubic `x³ - a₁ x² + a₂ x - a₃` over `ℤ₃(a₁, a₂, a₃)`
is NOT solvable by radicals). -/
theorem theorem_19_3_char_three_counterexample :
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    let a := canonVar (ZMod 3) 3
    IsGarlingAlgIndepTuple (ZMod 3) a ∧
    (3 : ℕ) ≤ 4 ∧
    ¬ IsGarlingSolvableByRadicals (garlingGenericPolyOverAdjoin (ZMod 3) a) := by
  have _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨canonVar_algIndep (ZMod 3) 3, by omega, ?_⟩
  apply theorem_19_3_char_dvd_factorial_not_solvable (canonVar_algIndep (ZMod 3) 3)
  rw [ZMod.ringChar_zmod_n]
  decide

/-- **Theorem 19.3 (Repaired full statement)** (§19.1, printed pp. 148–149 / PDF pp. 156–157):
For `1 ≤ n`, the generic polynomial over `K(a₁, …, aₙ)` is irreducible, separable, has Galois
group `≅ Σₙ`, and is solvable by radicals iff `n ≤ 4 ∧ ¬ (ringChar K ∣ n!)`. -/
theorem theorem_19_3_repaired {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    (hn : 1 ≤ n) {a : Fin n → E} (ha : IsGarlingAlgIndepTuple K a) :
    let K_a := IntermediateField.adjoin K (Set.range a)
    let f := garlingGenericPolyOverAdjoin K a
    Irreducible f ∧
    IsGarlingIrreducible f ∧
    f.Separable ∧
    IsGarlingSeparablePoly f ∧
    (∀ (F : Type w) [Field F] [Algebra K_a F],
      IsGarlingSplittingFieldExtension K_a F f →
      Nonempty (GarlingPolyGaloisGroup K_a F f ≃* SigmaN n)) ∧
    (IsGarlingSolvableByRadicals f ↔ n ≤ 4 ∧ ¬ (ringChar K ∣ n.factorial)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_19_3_clauses_1_to_3 hn ha
  exact ⟨h1, h2, h3, h4, h5, theorem_19_3_solvable_iff ha⟩

/-- Literal Clause 4 (`solvable by radicals ↔ n ≤ 4`) holds whenever `char K = 0 ∨ 5 ≤ char K`. -/
theorem theorem_19_3_of_char_zero_or_ge_five {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (hchar : ringChar K = 0 ∨ 5 ≤ ringChar K) {a : Fin n → E}
    (ha : IsGarlingAlgIndepTuple K a) :
    IsGarlingSolvableByRadicals (garlingGenericPolyOverAdjoin K a) ↔ n ≤ 4 := by
  rw [theorem_19_3_solvable_iff ha]
  refine ⟨fun h => h.1, fun hn4 => ⟨hn4, ?_⟩⟩
  rcases hchar with h0 | h5
  · rw [h0, zero_dvd_iff]; exact Nat.factorial_ne_zero n
  · intro hdvd
    have hp : Nat.Prime (ringChar K) :=
      (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right (by omega)
    have hle : ringChar K ≤ n := (hp.dvd_factorial).mp hdvd
    omega

/-! ### Symmetric polynomials, tower `M_j`, `Exercise 19.1`, `Exercise 19.2`, `Theorem 19.4`, and `Corollary` (pp. 149–150) -/

/-- Garling's inline prose definition of a *symmetric polynomial* in `R[t₁, …, tₙ]`
(§19.1, printed p. 149 / PDF p. 157: *"We say that a polynomial `f` in `K[t₁, …, tₙ]` is
symmetric if `σ(f) = f` for each `σ` in `G`"*). -/
def IsGarlingSymmetricPoly {R : Type*} [CommRing R] {n : ℕ} (f : MvPolynomial (Fin n) R) : Prop :=
  ∀ σ : SigmaN n, MvPolynomial.rename σ f = f

theorem isGarlingSymmetricPoly_iff {R : Type*} [CommRing R] {n : ℕ} (f : MvPolynomial (Fin n) R) :
    IsGarlingSymmetricPoly f ↔ MvPolynomial.IsSymmetric f :=
  Iff.rfl

theorem isGarlingSymmetricPoly_iff_permAut {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (f : MvPolynomial (Fin n) K) :
    IsGarlingSymmetricPoly f ↔
      ∀ σ : SigmaN n, permAut ht hgen σ (evalMvRingHom K t f) = evalMvRingHom K t f := by
  constructor
  · intro hsym σ
    rw [permAut_evalMvRingHom, hsym σ]
  · intro hperm σ
    apply ht
    rw [← permAut_evalMvRingHom ht hgen σ f]
    exact hperm σ

theorem isGarlingSymmetricPoly_elemSymmPoly (R : Type*) [CommRing R] (n : ℕ) (k : Fin n) :
    IsGarlingSymmetricPoly (elemSymmPoly R n k) := fun σ => by
  rw [elemSymmPoly, MvPolynomial.rename_esymm]

theorem isGarlingSymmetricPoly_C {R : Type*} [CommRing R] {n : ℕ} (c : R) :
    IsGarlingSymmetricPoly (MvPolynomial.C c : MvPolynomial (Fin n) R) := fun σ =>
  MvPolynomial.rename_C σ c

theorem isGarlingSymmetricPoly_add {R : Type*} [CommRing R] {n : ℕ}
    {f g : MvPolynomial (Fin n) R} (hf : IsGarlingSymmetricPoly f) (hg : IsGarlingSymmetricPoly g) :
    IsGarlingSymmetricPoly (f + g) := fun σ => by rw [map_add, hf σ, hg σ]

theorem isGarlingSymmetricPoly_sub {R : Type*} [CommRing R] {n : ℕ}
    {f g : MvPolynomial (Fin n) R} (hf : IsGarlingSymmetricPoly f) (hg : IsGarlingSymmetricPoly g) :
    IsGarlingSymmetricPoly (f - g) := fun σ => by rw [map_sub, hf σ, hg σ]

theorem isGarlingSymmetricPoly_mul {R : Type*} [CommRing R] {n : ℕ}
    {f g : MvPolynomial (Fin n) R} (hf : IsGarlingSymmetricPoly f) (hg : IsGarlingSymmetricPoly g) :
    IsGarlingSymmetricPoly (f * g) := fun σ => by rw [map_mul, hf σ, hg σ]

theorem isGarlingSymmetricPoly_pow {R : Type*} [CommRing R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hf : IsGarlingSymmetricPoly f) (m : ℕ) :
    IsGarlingSymmetricPoly (f ^ m) := fun σ => by rw [map_pow, hf σ]

theorem isGarlingSymmetricPoly_prod {R ι : Type*} [CommRing R] {n : ℕ} (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) R) (hg : ∀ i ∈ s, IsGarlingSymmetricPoly (g i)) :
    IsGarlingSymmetricPoly (∏ i ∈ s, g i) := fun σ => by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi => hg i hi σ

/-- Elementary-symmetric substitution `g ↦ g(s₁, …, sₙ)` as an `R`-algebra endomorphism of
`MvPolynomial (Fin n) R`. -/
noncomputable def elemSymmSubst (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (elemSymmPoly R n)

theorem isGarlingSymmetricPoly_elemSymmSubst {R : Type*} [CommRing R] {n : ℕ}
    (g : MvPolynomial (Fin n) R) :
    IsGarlingSymmetricPoly (elemSymmSubst R n g) := by
  intro σ
  have hcomp :
      (MvPolynomial.rename σ).comp (elemSymmSubst R n) = elemSymmSubst R n := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [elemSymmSubst, isGarlingSymmetricPoly_elemSymmPoly R n k σ]
  exact AlgHom.congr_fun hcomp g

/-! #### Tower `M_j`, `G_j`, `f_j`, `g_j`, `Exercise 19.1`, and pp. 149–150 multi-index basis -/

/-- Garling's intermediate tower `M₀ = K(s₁, …, sₙ)` and `M_j = M₀(t₁, …, t_j)` for `0 ≤ j ≤ n`
(§19.1, printed p. 149 / PDF p. 157), with `t₁, …, t_j` indexed 0-based as `{t i | i.1 < j}`. -/
noncomputable def towerField (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) (j : ℕ) : IntermediateField K E :=
  IntermediateField.adjoin K
    (Set.range (elemSymmVal K t) ∪ {x : E | ∃ i : Fin n, i.1 < j ∧ t i = x})

theorem towerField_zero (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) :
    towerField K t 0 = elemSymmField K t := by
  unfold towerField elemSymmField
  congr 1
  ext x
  simp

theorem towerField_n_eq_top {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    towerField K t n = ⊤ := by
  rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact IntermediateField.subset_adjoin K _ (Or.inr ⟨i, i.2, rfl⟩)

theorem towerField_mono (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂) :
    towerField K t j₁ ≤ towerField K t j₂ := by
  refine IntermediateField.adjoin.mono K _ _ (Set.union_subset_union_right _ ?_)
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi h, rfl⟩

theorem towerField_succ_eq_adjoin (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) {j : ℕ} (hj : j < n) :
    (towerField K t (j + 1)).toSubfield =
      (IntermediateField.adjoin (towerField K t j) ({t ⟨j, hj⟩} : Set E)).toSubfield := by
  apply le_antisymm
  · let A : IntermediateField K E :=
      (IntermediateField.adjoin (towerField K t j) ({t ⟨j, hj⟩} : Set E)).restrictScalars K
    have hle : towerField K t (j + 1) ≤ A := by
      rw [towerField, IntermediateField.adjoin_le_iff]
      rintro x (hx | ⟨i, hi, rfl⟩)
      · exact (IntermediateField.adjoin (towerField K t j) _).algebraMap_mem
          ⟨x, IntermediateField.subset_adjoin K _ (Or.inl hx)⟩
      · by_cases hij : i.1 < j
        · exact (IntermediateField.adjoin (towerField K t j) _).algebraMap_mem
            ⟨t i, IntermediateField.subset_adjoin K _ (Or.inr ⟨i, hij, rfl⟩)⟩
        · have hieq : i = ⟨j, hj⟩ := Fin.ext (show i.1 = j by omega)
          rw [hieq]
          exact IntermediateField.subset_adjoin (towerField K t j) _ rfl
    exact hle
  · let B : IntermediateField (towerField K t j) E :=
      { (towerField K t (j + 1)).toSubfield with
        algebraMap_mem' := fun x => towerField_mono K t (Nat.le_succ j) x.2 }
    have hle : IntermediateField.adjoin (towerField K t j) ({t ⟨j, hj⟩} : Set E) ≤ B := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin K _ (Or.inr ⟨⟨j, hj⟩, Nat.lt_succ_self j, rfl⟩)
    exact hle

/-- Subgroup of `Σₙ` fixing the first `j` coordinates `i < j`. -/
def permStabSubgroup (n j : ℕ) : Subgroup (SigmaN n) where
  carrier := {σ : SigmaN n | ∀ i : Fin n, i.1 < j → σ i = i}
  mul_mem' {σ τ} hσ hτ i hi := by
    change σ (τ i) = i
    rw [hτ i hi, hσ i hi]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ i hi := by
    change σ.symm i = i
    exact (Equiv.symm_apply_eq σ).mpr (hσ i hi).symm

/-- `permStabSubgroup n j` has cardinality `(n - j)!` for `j ≤ n`. -/
theorem permStabSubgroup_card {n j : ℕ} (hj : j ≤ n) :
    Nat.card (permStabSubgroup n j) = (n - j).factorial := by
  let e : permStabSubgroup n j ≃ Equiv.Perm (Fin (n - j)) :=
    { toFun := fun ⟨σ, hσ⟩ =>
        have hge : ∀ k : Fin (n - j), j ≤ (σ ⟨j + k.1, by omega⟩).1 := by
          intro k
          by_contra hlt
          push Not at hlt
          have hfix := hσ (σ ⟨j + k.1, by omega⟩) hlt
          have hinj := σ.injective hfix
          have hv := congrArg Fin.val hinj
          dsimp at hv; omega
        have hge_inv : ∀ k : Fin (n - j), j ≤ (σ.symm ⟨j + k.1, by omega⟩).1 := by
          intro k
          by_contra hlt
          push Not at hlt
          have hfix := hσ (σ.symm ⟨j + k.1, by omega⟩) hlt
          rw [Equiv.apply_symm_apply] at hfix
          have hv := congrArg Fin.val hfix
          dsimp at hv; omega
        { toFun := fun k => ⟨(σ ⟨j + k.1, by omega⟩).1 - j, by
              have hlt := (σ ⟨j + k.1, by omega⟩).2; have hgk := hge k; omega⟩
          invFun := fun k => ⟨(σ.symm ⟨j + k.1, by omega⟩).1 - j, by
              have hlt := (σ.symm ⟨j + k.1, by omega⟩).2; have hgk := hge_inv k; omega⟩
          left_inv := fun k => by
            ext; dsimp
            have h1 : (⟨j + ((σ ⟨j + k.1, by omega⟩).1 - j), by
                have hlt := (σ ⟨j + k.1, by omega⟩).2; have hgk := hge k; omega⟩ : Fin n) =
                σ ⟨j + k.1, by omega⟩ := Fin.ext (show j + ((σ ⟨j + k.1, by omega⟩).1 - j) = _ by
              have := hge k; omega)
            rw [h1, Equiv.symm_apply_apply]; dsimp; omega
          right_inv := fun k => by
            ext; dsimp
            have h1 : (⟨j + ((σ.symm ⟨j + k.1, by omega⟩).1 - j), by
                have hlt := (σ.symm ⟨j + k.1, by omega⟩).2; have hgk := hge_inv k; omega⟩ : Fin n) =
                σ.symm ⟨j + k.1, by omega⟩ := Fin.ext (show j + ((σ.symm ⟨j + k.1, by omega⟩).1 - j) = _ by
              have := hge_inv k; omega)
            rw [h1, Equiv.apply_symm_apply]; dsimp; omega }
      invFun := fun τ =>
        ⟨{ toFun := fun i => if h : i.1 < j then i else ⟨j + (τ ⟨i.1 - j, by omega⟩).1, by have := (τ ⟨i.1 - j, by omega⟩).2; omega⟩
           invFun := fun i => if h : i.1 < j then i else ⟨j + (τ.symm ⟨i.1 - j, by omega⟩).1, by have := (τ.symm ⟨i.1 - j, by omega⟩).2; omega⟩
           left_inv := fun i => by
             by_cases h : i.1 < j
             · simp [h]
             · simp only [h, ↓reduceDIte]
               have hnot : ¬ (j + (τ ⟨i.1 - j, by omega⟩).1 < j) := by omega
               simp only [hnot, ↓reduceDIte]
               ext; dsimp
               have hidx : (⟨j + (τ ⟨i.1 - j, by omega⟩).1 - j, by have := (τ ⟨i.1 - j, by omega⟩).2; omega⟩ : Fin (n - j)) =
                   τ ⟨i.1 - j, by omega⟩ := Fin.ext (show j + (τ ⟨i.1 - j, by omega⟩).1 - j = _ by omega)
               rw [hidx, Equiv.symm_apply_apply]; dsimp; omega
           right_inv := fun i => by
             by_cases h : i.1 < j
             · simp [h]
             · simp only [h, ↓reduceDIte]
               have hnot : ¬ (j + (τ.symm ⟨i.1 - j, by omega⟩).1 < j) := by omega
               simp only [hnot, ↓reduceDIte]
               ext; dsimp
               have hidx : (⟨j + (τ.symm ⟨i.1 - j, by omega⟩).1 - j, by have := (τ.symm ⟨i.1 - j, by omega⟩).2; omega⟩ : Fin (n - j)) =
                   τ.symm ⟨i.1 - j, by omega⟩ := Fin.ext (show j + (τ.symm ⟨i.1 - j, by omega⟩).1 - j = _ by omega)
               rw [hidx, Equiv.apply_symm_apply]; dsimp; omega },
         fun i hi => by simp [hi]⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        apply Subtype.ext; ext i; dsimp
        by_cases h : i.1 < j
        · simp [h, hσ i h]
        · simp only [h, ↓reduceDIte]
          have hge : j ≤ (σ ⟨j + (i.1 - j), by omega⟩).1 := by
            by_contra hlt; push Not at hlt
            have hv := congrArg Fin.val (σ.injective (hσ (σ ⟨j + (i.1 - j), by omega⟩) hlt))
            dsimp at hv; omega
          have hi_eq : (⟨j + (i.1 - j), by omega⟩ : Fin n) = i := Fin.ext (show j + (i.1 - j) = i.1 by omega)
          rw [hi_eq] at hge ⊢
          omega
      right_inv := fun τ => by
        ext k; dsimp
        have hnot : ¬ (j + k.1 < j) := by omega
        simp only [hnot, ↓reduceDIte]
        have hk : (⟨j + k.1 - j, by omega⟩ : Fin (n - j)) = k := Fin.ext (show j + k.1 - j = k.1 by omega)
        rw [hk]; omega }
  rw [Nat.card_congr e, Nat.card_perm, Nat.card_fin]

/-- Garling's subgroup `G_j ≤ G` fixing `t₁, …, t_j` (`Exercise 19.1`, p. 150). -/
noncomputable def towerStabSubgroup {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (j : ℕ) :
    Subgroup (GarlingAut E) :=
  Subgroup.map (permAutHom ht hgen) (permStabSubgroup n j)

theorem mem_towerStabSubgroup_iff {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) (j : ℕ) (τ : GarlingAut E) :
    τ ∈ towerStabSubgroup ht hgen j ↔
      τ ∈ permAutSubgroup ht hgen ∧ ∀ i : Fin n, i.1 < j → τ (t i) = t i := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨⟨σ, rfl⟩, fun i hi => ?_⟩
    change permAut ht hgen σ (t i) = t i
    rw [permAut_apply_gen, hσ i hi]
  · rintro ⟨⟨σ, rfl⟩, hfix⟩
    refine ⟨σ, fun i hi => ?_, rfl⟩
    have h1 := hfix i hi
    change permAut ht hgen σ (t i) = t i at h1
    rw [permAut_apply_gen] at h1
    exact ht.injective h1

theorem towerStabSubgroup_card {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) {j : ℕ} (hj : j ≤ n) :
    Nat.card (towerStabSubgroup ht hgen j) = (n - j).factorial := by
  let e : permStabSubgroup n j ≃ towerStabSubgroup ht hgen j :=
    Equiv.ofBijective
      (fun x => ⟨permAutHom ht hgen x.1, x.1, x.2, rfl⟩)
      ⟨fun a b hab => Subtype.ext (permAutHom_injective ht hgen (congrArg Subtype.val hab)),
       fun ⟨y, σ, hσ, hy⟩ => ⟨⟨σ, hσ⟩, Subtype.ext hy⟩⟩
  rw [← Nat.card_congr e, permStabSubgroup_card hj]

/-- Prefix factor `f_j = ∏_{i < j} (x - t_i)` in `E[x]` (§19.1, p. 149). -/
noncomputable def towerPrefixPoly {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) (j : ℕ) : R[X] :=
  ∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.1 < j), (Polynomial.X - Polynomial.C (t i))

/-- Suffix factor `g_j = ∏_{j ≤ i} (x - t_i)` in `E[x]` (§19.1, p. 149). -/
noncomputable def towerSuffixPoly {R : Type*} [CommRing R] {n : ℕ} (t : Fin n → R) (j : ℕ) : R[X] :=
  ∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => j ≤ i.1), (Polynomial.X - Polynomial.C (t i))

theorem generalRootsPoly_eq_towerPrefix_mul_suffix {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) (j : ℕ) :
    generalRootsPoly t = towerPrefixPoly t j * towerSuffixPoly t j := by
  unfold generalRootsPoly towerPrefixPoly towerSuffixPoly
  have h := (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
    (fun i => i.1 < j) (fun i => Polynomial.X - Polynomial.C (t i))).symm
  rw [h]
  congr 2
  ext i
  simp [not_lt]

/-- Descent of `g_j` into `M_j[x]` via `Lemma 15.2` (§19.1, p. 149). -/
theorem towerSuffixPoly_coeff_mem_towerField {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) (j : ℕ) (d : ℕ) :
    (towerSuffixPoly t j).coeff d ∈ towerField K t j := by
  let Mj := towerField K t j
  have hf_mem : ∀ k, (generalRootsPoly t).coeff k ∈ Mj.toSubfield := by
    intro k
    rw [← generalRootsPolyOverElemSymm_map K t, Polynomial.coeff_map]
    exact towerField_mono K t (Nat.zero_le j)
      (by rw [towerField_zero]; exact ((generalRootsPolyOverElemSymm K t).coeff k).2)
  have hfj_mem : ∀ k, (towerPrefixPoly t j).coeff k ∈ Mj.toSubfield := by
    suffices ∀ (s : Finset (Fin n)), (∀ i ∈ s, i.1 < j) →
        ∀ k, (∏ i ∈ s, (Polynomial.X - Polynomial.C (t i))).coeff k ∈ Mj.toSubfield by
      exact this _ (fun i hi => (Finset.mem_filter.mp hi).2)
    intro s hs
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro k
      rw [Finset.prod_empty, Polynomial.coeff_one]
      split_ifs
      · exact Mj.toSubfield.one_mem
      · exact Mj.toSubfield.zero_mem
    | insert a s ha ih =>
      intro k
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      refine Mj.toSubfield.sum_mem fun p _ => Mj.toSubfield.mul_mem ?_ (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) p.2)
      rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
      refine Mj.toSubfield.sub_mem ?_ ?_
      · split_ifs
        · exact Mj.toSubfield.one_mem
        · exact Mj.toSubfield.zero_mem
      · split_ifs
        · exact IntermediateField.subset_adjoin K _ (Or.inr ⟨a, hs a (Finset.mem_insert_self a s), rfl⟩)
        · exact Mj.toSubfield.zero_mem
  have hfj_ne0 : towerPrefixPoly t j ≠ 0 :=
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero
  have hmul : generalRootsPoly t = towerSuffixPoly t j * towerPrefixPoly t j := by
    rw [mul_comm, ← generalRootsPoly_eq_towerPrefix_mul_suffix]
  exact lemma_15_2_subfield Mj.toSubfield (towerSuffixPoly t j) (generalRootsPoly t)
    (towerPrefixPoly t j) hf_mem hfj_mem hfj_ne0 hmul d

/-- The descended polynomial `g_j ∈ M_j[x]` (§19.1, p. 149). -/
noncomputable def towerSuffixPolyOver (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) (j : ℕ) : (towerField K t j)[X] :=
  ∑ d ∈ (towerSuffixPoly t j).support,
    Polynomial.monomial d ⟨(towerSuffixPoly t j).coeff d, towerSuffixPoly_coeff_mem_towerField t j d⟩

theorem towerSuffixPolyOver_map (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) (j : ℕ) :
    (towerSuffixPolyOver K t j).map (algebraMap (towerField K t j) E) = towerSuffixPoly t j := by
  apply Polynomial.ext; intro d
  rw [Polynomial.coeff_map, towerSuffixPolyOver, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hd : d ∈ (towerSuffixPoly t j).support
  · rw [Finset.sum_eq_single d (fun b _ hbd => by simp [hbd]) (fun h => absurd hd h)]
    simp
  · rw [Finset.sum_eq_zero (fun b hb => by
      have hbd : b ≠ d := fun h => hd (h ▸ hb)
      simp [hbd]),
      Polynomial.notMem_support_iff.mp hd, map_zero]

theorem towerSuffixPolyOver_monic_and_deg {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} (t : Fin n → E) {j : ℕ} (hj : j ≤ n) :
    (towerSuffixPolyOver K t j).Monic ∧ (towerSuffixPolyOver K t j).natDegree = n - j := by
  have hmonE : (towerSuffixPoly t j).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  have hdegE : (towerSuffixPoly t j).natDegree = n - j := by
    rw [towerSuffixPoly, Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    let e : {i : Fin n // j ≤ i.1} ≃ Fin (n - j) :=
      { toFun := fun ⟨i, hi⟩ => ⟨i.1 - j, by omega⟩
        invFun := fun k => ⟨⟨j + k.1, by omega⟩, by dsimp; omega⟩
        left_inv := fun ⟨i, hi⟩ => Subtype.ext (Fin.ext (by dsimp; omega))
        right_inv := fun k => Fin.ext (by dsimp; omega) }
    have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => j ≤ i.1)).card =
        Fintype.card {i : Fin n // j ≤ i.1} := (Fintype.card_subtype _).symm
    rw [hcard, Fintype.card_congr e, Fintype.card_fin]
  have hinj := (algebraMap (towerField K t j) E).injective
  have hdeg : (towerSuffixPolyOver K t j).natDegree = n - j := by
    rw [← Polynomial.natDegree_map_eq_of_injective hinj, towerSuffixPolyOver_map, hdegE]
  have hmon : (towerSuffixPolyOver K t j).Monic := by
    rw [Polynomial.Monic]
    apply hinj
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, towerSuffixPolyOver_map, map_one]
    exact hmonE.leadingCoeff
  exact ⟨hmon, hdeg⟩

/-- **Exercise 19.1** (§19.1, printed p. 150 / PDF p. 158) + pp. 149–150 tower degrees:
`M_j = φ(G_j)` and `[E : M_j] = (n - j)!` for all `0 ≤ j ≤ n`. -/
theorem exercise_19_1 {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) {j : ℕ} (hj : j ≤ n) :
    (towerField K t j).toSubfield =
      garlingPhi (towerStabSubgroup ht hgen j : Set (GarlingAut E)) ∧
    Module.finrank (towerField K t j) E = (n - j).factorial ∧
    extDegree (towerField K t j) E = ((n - j).factorial : ℕ∞) := by
  classical
  let Mj := towerField K t j
  let Gj := towerStabSubgroup ht hgen j
  let Lj := garlingPhi (Gj : Set (GarlingAut E))
  have _ : Finite Gj := Finite.of_equiv (permStabSubgroup n j)
    (Equiv.ofBijective (fun x => ⟨permAutHom ht hgen x.1, x.1, x.2, rfl⟩)
      ⟨fun a b hab => Subtype.ext (permAutHom_injective ht hgen (congrArg Subtype.val hab)),
       fun ⟨y, σ, hσ, hy⟩ => ⟨⟨σ, hσ⟩, Subtype.ext hy⟩⟩)
  -- `Mj ≤ Lj`:
  have hMj_le : Mj.toSubfield ≤ Lj := by
    have hK : ∀ c : K, algebraMap K E c ∈ Lj := by
      rintro c _ ⟨σ, _, rfl⟩
      exact (permAut ht hgen σ).commutes c
    let Lj_int : IntermediateField K E := Lj.toIntermediateField hK
    have hle : Mj ≤ Lj_int := by
      change towerField K t j ≤ Lj_int
      rw [towerField, IntermediateField.adjoin_le_iff]
      rintro x (⟨k, rfl⟩ | ⟨i, hi, rfl⟩) _ ⟨σ, hσ, rfl⟩
      · exact permAut_elemSymmVal ht hgen σ k
      · change permAut ht hgen σ (t i) = t i
        rw [permAut_apply_gen, hσ i hi]
    exact hle
  -- `E` is a splitting field of `g_j` over `Mj`:
  let gj := towerSuffixPolyOver K t j
  have hsf_gj : IsGarlingSplittingFieldExtension Mj E gj := by
    have hmap := towerSuffixPolyOver_map K t j
    let tailIdx : Fin (n - j) → Fin n := fun k => ⟨j + k.1, by omega⟩
    have hprod_tail : towerSuffixPoly t j = ∏ k : Fin (n - j), (Polynomial.X - Polynomial.C (t (tailIdx k))) := by
      unfold towerSuffixPoly
      refine (Finset.prod_bij (fun (k : Fin (n - j)) _ => tailIdx k) ?_ ?_ ?_ ?_).symm
      · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [tailIdx]; omega⟩
      · intro k₁ _ k₂ _ h; ext; have := congrArg Fin.val h; dsimp [tailIdx] at this; omega
      · intro i hi
        have hij : j ≤ i.1 := (Finset.mem_filter.mp hi).2
        exact ⟨⟨i.1 - j, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp [tailIdx]; omega)⟩
      · intro _ _; rfl
    have hspl : GarlingSplitsOver Mj E gj := by
      refine ⟨n - j, 1, fun k => t (tailIdx k), ?_⟩
      unfold GarlingSplitsExplicit
      rw [hmap, map_one, map_one, one_mul, hprod_tail]
    refine ⟨hspl, fun N hN hNspl => ?_⟩
    rcases hNspl with ⟨m, lam, α, hNexp⟩
    have hmap_eq : towerSuffixPoly t j =
        Polynomial.C (algebraMap Mj E lam) * ∏ l : Fin m, (Polynomial.X - Polynomial.C (α l : E)) := by
      have h1 := congrArg (Polynomial.map N.val.toRingHom) hNexp
      have hcomp : (gj.map (algebraMap Mj N)).map N.val.toRingHom = gj.map (algebraMap Mj E) := by
        rw [Polynomial.map_map]; rfl
      rw [hcomp, hmap] at h1
      simpa [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] using h1
    have hlam0 : algebraMap Mj E lam ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hmap_eq
      exact (towerSuffixPolyOver_monic_and_deg t hj).1.ne_zero
        ((Polynomial.map_eq_zero_iff (algebraMap Mj E).injective).mp (hmap.trans hmap_eq))
    have ht_mem : ∀ i : Fin n, t i ∈ N := by
      intro i
      by_cases hij : i.1 < j
      · exact N.algebraMap_mem ⟨t i, IntermediateField.subset_adjoin K _ (Or.inr ⟨i, hij, rfl⟩)⟩
      · have hroot : (towerSuffixPoly t j).eval (t i) = 0 := by
          rw [towerSuffixPoly, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩) (by simp)
        rw [hmap_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hroot
        have hprod0 := (mul_eq_zero.mp hroot).resolve_left hlam0
        obtain ⟨l, _, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hl
        rw [hl]; exact (α l).2
    apply hN
    have hK_le : IntermediateField.adjoin K (Set.range t) ≤ N.restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ht_mem i
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : IntermediateField K E) := IntermediateField.mem_top
    rw [← hgen] at hx
    exact hK_le hx
  have hmsf : gj.IsSplittingField Mj E := (isGarlingSplittingFieldExtension_iff Mj E gj).mp hsf_gj
  have _ : Polynomial.IsSplittingField Mj E gj := hmsf
  have _ : Module.Finite Mj E := Polynomial.IsSplittingField.finiteDimensional E gj
  have hdvd : Module.finrank Mj E ∣ (n - j).factorial :=
    splittingField_finrank_dvd_factorial (n - j) (towerSuffixPolyOver_monic_and_deg t hj).2 hsf_gj
  have hle_fact : Module.finrank Mj E ≤ (n - j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  -- By `Theorem 11.3`, `[E : Lj] = |Gj| = (n - j)!`:
  have h113 := theorem_11_3 Gj
  have hcard_Gj : Nat.card Gj = (n - j).factorial := towerStabSubgroup_card ht hgen hj
  have hfin_LjE : Module.finrank Lj E = (n - j).factorial := h113.2.2.1.symm.trans hcard_Gj
  let _ : Algebra Mj Lj := (Subfield.inclusion hMj_le).toAlgebra
  have _ : IsScalarTower Mj Lj E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : Module.Finite Mj Lj := Module.Finite.left Mj Lj E
  have _ : Module.Finite Lj E := (isFiniteExtension_iff_moduleFinite Lj E).mp h113.1
  have htower := Module.finrank_mul_finrank Mj Lj E
  have hpos : 0 < Module.finrank Mj Lj := Module.finrank_pos
  have hfin1 : Module.finrank Mj Lj = 1 := by
    rw [hfin_LjE] at htower
    have hfp : 0 < (n - j).factorial := Nat.factorial_pos _
    nlinarith
  have hMj_eq : Mj.toSubfield = Lj := by
    apply le_antisymm hMj_le
    intro x hx
    by_contra hxM
    have hli : LinearIndependent Mj ![((1 : Lj)), ⟨x, hx⟩] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hsum : (c 0 : Mj) • (1 : Lj) + (c 1 : Mj) • (⟨x, hx⟩ : Lj) = 0 := by
        simpa [Fin.sum_univ_two] using hc
      by_cases hc1 : c 1 = 0
      · rw [hc1, zero_smul, add_zero, Algebra.smul_def, mul_one] at hsum
        have hc0 : c 0 = 0 := (algebraMap Mj Lj).injective (by rw [hsum, map_zero])
        intro i; fin_cases i <;> assumption
      · exfalso
        have h1 : (c 1 : E) * x = -(c 0 : E) := by
          have hv := congrArg Subtype.val hsum
          change (c 0 : E) * 1 + (c 1 : E) * x = 0 at hv
          linear_combination hv
        have hc1E : (c 1 : E) ≠ 0 := fun h0 => hc1 (Subtype.ext h0)
        have hx_eq : x = (c 1 : E)⁻¹ * -(c 0 : E) := by
          calc x = (c 1 : E)⁻¹ * ((c 1 : E) * x) := (inv_mul_cancel_left₀ hc1E x).symm
            _ = (c 1 : E)⁻¹ * -(c 0 : E) := by rw [h1]
        apply hxM
        rw [hx_eq]
        exact Mj.toSubfield.mul_mem (Mj.toSubfield.inv_mem (c 1).2) (Mj.toSubfield.neg_mem (c 0).2)
    have hle2 := hli.fintype_card_le_finrank
    simp [hfin1] at hle2
  have hfin_MjE : Module.finrank Mj E = (n - j).factorial := by
    rw [← htower, hfin1, one_mul, hfin_LjE]
  exact ⟨hMj_eq, hfin_MjE, by rw [extDegree_eq_finrank Mj E, hfin_MjE]⟩

/-- Abstract helper for `section_19_1_tower_step`: keeping the base field `F` and intermediate
field `M` completely abstract avoids `whnf` / kernel unfolding of `towerField`. -/
private theorem tower_step_abstract {F M E : Type*} [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    {x : E} {g : F[X]} {d : ℕ}
    (hfin : Module.finrank F M = d)
    (hg_mon : g.Monic) (hg_deg : g.natDegree = d)
    (hroot : Polynomial.aeval x g = 0)
    (hM_eq : Set.range (algebraMap M E) = (IntermediateField.adjoin F ({x} : Set E) : Set E)) :
    minpoly F x = g ∧
    Irreducible g ∧
    LinearIndependent F (fun r : Fin d => x ^ r.1) := by
  have hint : IsIntegral F x := ⟨g, hg_mon, hroot⟩
  let ιM : M →ₐ[F] E := IsScalarTower.toAlgHom F M E
  have hιM_inj : Function.Injective ιM := ιM.injective
  have hrange : ιM.fieldRange = IntermediateField.adjoin F ({x} : Set E) := by
    ext y; exact Set.ext_iff.mp hM_eq y
  let eAdj : M ≃ₐ[F] IntermediateField.adjoin F ({x} : Set E) :=
    (AlgEquiv.ofInjectiveField ιM).trans (IntermediateField.equivOfEq hrange)
  have hmin_deg : (minpoly F x).natDegree = d := by
    have hfr : Module.finrank F (IntermediateField.adjoin F ({x} : Set E)) =
        (minpoly F x).natDegree := IntermediateField.adjoin.finrank hint
    rw [← hfr, ← LinearEquiv.finrank_eq eAdj.toLinearEquiv, hfin]
  have hmin_eq : minpoly F x = g :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hg_mon
      (minpoly.dvd F x hroot) (by omega)).symm
  have hirr : Irreducible g := hmin_eq ▸ minpoly.irreducible hint
  let pb := IntermediateField.adjoin.powerBasis hint
  have hpb_dim : pb.dim = d := by rw [IntermediateField.adjoin.powerBasis_dim hint, hmin_deg]
  have hli : LinearIndependent F (fun r : Fin d => x ^ r.1) := by
    have hli_pb := pb.basis.linearIndependent
    have hli_E : LinearIndependent F
        (fun r : Fin pb.dim => ((pb.basis r : IntermediateField.adjoin F ({x} : Set E)) : E)) :=
      hli_pb.map' (IntermediateField.adjoin F ({x} : Set E)).val.toLinearMap
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hfun : (fun r : Fin d => x ^ r.1) =
        (fun r : Fin pb.dim => ((pb.basis r : IntermediateField.adjoin F ({x} : Set E)) : E)) ∘
          finCongr hpb_dim.symm := by
      funext r
      simp only [Function.comp_apply, PowerBasis.basis_eq_pow, finCongr_apply, Fin.val_cast]
      rw [SubmonoidClass.coe_pow]
      dsimp only [pb]
      rw [IntermediateField.adjoin.powerBasis_gen]
      rfl
    rw [hfun]
    exact hli_E.comp (finCongr hpb_dim.symm) (finCongr hpb_dim.symm).injective
  exact ⟨hmin_eq, hirr, hli⟩

/-- Abstract intermediate-field tower-step helper: keeping `M0, M1 : IntermediateField K E` as
opaque parameters prevents kernel reduction from unfolding `towerField` during `IsScalarTower`
and `Module.finrank_mul_finrank` checks. -/
private theorem tower_step_of_intermediate {K E : Type*} [Field K] [Field E] [Algebra K E]
    (M0 M1 : IntermediateField K E) (hle : M0 ≤ M1)
    {x : E} {g : M0[X]} {d m : ℕ} (hm : 0 < m)
    (h0 : Module.finrank M0 E = d * m) (h1 : Module.finrank M1 E = m)
    (hg_mon : g.Monic) (hg_deg : g.natDegree = d)
    (hroot : Polynomial.aeval x g = 0)
    (hsub_eq : M1.toSubfield = (IntermediateField.adjoin M0 ({x} : Set E)).toSubfield) :
    let _ : Algebra M0 M1 := (IntermediateField.inclusion hle).toAlgebra
    Module.finrank M0 M1 = d ∧
    extDegree M0 M1 = (d : ℕ∞) ∧
    minpoly M0 x = g ∧
    Irreducible g ∧
    LinearIndependent M0 (fun r : Fin d => x ^ r.1) := by
  intro _
  have _ : IsScalarTower M0 M1 E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd : d = 0 := by omega
    rw [hd, zero_mul] at h0
    exact (Nat.ne_of_gt (by
      have _ : Module.Finite M1 E := Module.finite_of_finrank_pos (by omega)
      have _ : Module.Finite M0 M1 := by
        have hint : IsIntegral M0 x := ⟨g, hg_mon, hroot⟩
        have hrange : Set.range (algebraMap M1 E) =
            (IntermediateField.adjoin M0 ({x} : Set E) : Set E) := by
          ext y
          exact ⟨fun ⟨⟨z, hz⟩, hy⟩ => hy ▸ (SetLike.ext_iff.mp hsub_eq z).mp hz,
            fun hy => ⟨⟨y, (SetLike.ext_iff.mp hsub_eq y).mpr hy⟩, rfl⟩⟩
        let ιM : M1 →ₐ[M0] E := IsScalarTower.toAlgHom M0 M1 E
        have hfr : ιM.fieldRange = IntermediateField.adjoin M0 ({x} : Set E) := by
          ext y; exact Set.ext_iff.mp hrange y
        let eAdj : M1 ≃ₐ[M0] IntermediateField.adjoin M0 ({x} : Set E) :=
          (AlgEquiv.ofInjectiveField ιM).trans (IntermediateField.equivOfEq hfr)
        have _ : Module.Finite M0 (IntermediateField.adjoin M0 ({x} : Set E)) :=
          IntermediateField.adjoin.finiteDimensional hint
        exact Module.Finite.equiv eAdj.symm.toLinearEquiv
      have _ : Module.Finite M0 E := Module.Finite.trans M1 E
      exact Module.finrank_pos)) h0
  have _ : Module.Finite M0 E := Module.finite_of_finrank_pos (by rw [h0]; exact Nat.mul_pos hd_pos hm)
  have _ : Module.Finite M0 M1 := Module.Finite.left M0 M1 E
  have _ : Module.Finite M1 E := Module.Finite.right M0 M1 E
  have htower := Module.finrank_mul_finrank M0 M1 E
  rw [h0, h1] at htower
  have hstep : Module.finrank M0 M1 = d := Nat.eq_of_mul_eq_mul_right hm htower
  have hrange_eq : Set.range (algebraMap M1 E) =
      (IntermediateField.adjoin M0 ({x} : Set E) : Set E) := by
    ext y
    exact ⟨fun ⟨⟨z, hz⟩, hy⟩ => hy ▸ (SetLike.ext_iff.mp hsub_eq z).mp hz,
      fun hy => ⟨⟨y, (SetLike.ext_iff.mp hsub_eq y).mpr hy⟩, rfl⟩⟩
  obtain ⟨hmin_eq, hirr, hli⟩ :=
    tower_step_abstract hstep hg_mon hg_deg hroot hrange_eq
  exact ⟨hstep, by rw [extDegree_eq_finrank M0 M1, hstep], hmin_eq, hirr, hli⟩

/-- **§19.1 Prose Tower Step Theorem** (printed p. 149 / PDF p. 157):
For `0 ≤ j < n`, `[M_{j+1} : M_j] = n - j`, `g_j ∈ M_j[x]` is the minimal polynomial of `t_{j+1}`
(0-based `t j`) over `M_j`, `g_j` is irreducible over `M_j`, and `1, t_{j+1}, …, t_{j+1}^{n-j-1}`
is a basis of `M_{j+1}` over `M_j`. -/
theorem section_19_1_tower_step {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
    {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) {j : ℕ} (hj : j < n) :
    let Mj := towerField K t j
    let Mj1 := towerField K t (j + 1)
    let _ : Algebra Mj Mj1 := (IntermediateField.inclusion (towerField_mono K t (show j ≤ j + 1 by omega))).toAlgebra
    Module.finrank Mj Mj1 = n - j ∧
    extDegree Mj Mj1 = ((n - j : ℕ) : ℕ∞) ∧
    minpoly Mj (t ⟨j, hj⟩) = towerSuffixPolyOver K t j ∧
    Irreducible (towerSuffixPolyOver K t j) ∧
    LinearIndependent Mj (fun r : Fin (n - j) => (t ⟨j, hj⟩) ^ r.1) := by
  obtain ⟨_, hfin_j, _⟩ := exercise_19_1 ht hgen (le_of_lt hj)
  obtain ⟨_, hfin_j1, _⟩ := exercise_19_1 ht hgen (show j + 1 ≤ n by omega)
  have hfact : (n - j).factorial = (n - j) * (n - (j + 1)).factorial := by
    have hsub : n - j = (n - (j + 1)) + 1 := by omega
    rw [hsub, Nat.factorial_succ]
  obtain ⟨hgj_mon, hgj_deg⟩ := towerSuffixPolyOver_monic_and_deg (K := K) t (le_of_lt hj)
  have hroot : Polynomial.aeval (t ⟨j, hj⟩) (towerSuffixPolyOver K t j) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, towerSuffixPolyOver_map,
      towerSuffixPoly, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ ⟨j, hj⟩, le_rfl⟩) (by simp)
  exact tower_step_of_intermediate (towerField K t j) (towerField K t (j + 1))
    (towerField_mono K t (show j ≤ j + 1 by omega))
    (Nat.factorial_pos _) (hfin_j.trans hfact) hfin_j1 hgj_mon hgj_deg hroot
    (towerField_succ_eq_adjoin K t hj)

/-- Multi-index type for pp. 149–150 (`0 ≤ i_k ≤ n - k` in 1-based `1 ≤ k ≤ j`, i.e.
`0 ≤ i_k < n - k` in 0-based `k : Fin j`). -/
abbrev GarlingMultiIndex (n j : ℕ) : Type :=
  (k : Fin j) → Fin (n - k.1)

/-- Remark recording p. 149 l. 26's printed slip `0 ≤ i_k < n - k` (empty at `k = n` in 1-based
indexing) vs. the true bound `0 ≤ i_k ≤ n - k` (whose product of ranges is `n!`). -/
theorem section_19_1_p149_strict_bound_typo_remark (n : ℕ) :
    {i : ℕ | 0 ≤ i ∧ i < n - n} = ∅ ∧
    {i : ℕ | 0 ≤ i ∧ i ≤ n - n} = {0} ∧
    Fintype.card (GarlingMultiIndex n n) = n.factorial := by
  refine ⟨by ext i; simp, by ext i; simp, ?_⟩
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Nat.factorial_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
    rw [ih]

/-- Monomial `∏_{k < j} t_k^{i_k}` associated with a multi-index `i : GarlingMultiIndex n j`. -/
noncomputable def multiIndexMonomial {E : Type*} [CommRing E] {n j : ℕ} (hj : j ≤ n)
    (t : Fin n → E) (idx : GarlingMultiIndex n j) : E :=
  ∏ k : Fin j, (t ⟨k.1, lt_of_lt_of_le k.2 hj⟩) ^ (idx k).1

/-- **§19.1 Prose Multi-Index Linear Independence** (printed pp. 149–150 / PDF pp. 157–158):
For `0 ≤ j ≤ n`, the monomials `∏_{k < j} t_k^{i_k}` (`idx : GarlingMultiIndex n j`, i.e.
`0 ≤ i_k ≤ n - k` in 1-based indexing) are linearly independent over `M₀ = K(s₁, …, sₙ)`. -/
theorem section_19_1_multi_index_linearIndependent {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    ∀ (j : ℕ) (hj : j ≤ n),
      LinearIndependent (elemSymmField K t) (multiIndexMonomial hj t) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [Fintype.linearIndependent_iff]
    intro c hc idx
    have h0 : idx = (fun k : Fin 0 => Fin.elim0 k) := funext fun k => Fin.elim0 k
    have hsum : c idx • (1 : E) = 0 := by
      have h1 := hc
      rw [Finset.sum_eq_single idx (fun b _ hb => absurd (funext fun k => Fin.elim0 k) hb)
        (fun h => absurd (Finset.mem_univ idx) h)] at h1
      simpa [multiIndexMonomial] using h1
    rw [Algebra.smul_def, mul_one] at hsum
    exact (algebraMap (elemSymmField K t) E).injective (hsum.trans (map_zero _).symm)
  | succ j ih =>
    intro hj1
    have hj : j < n := Nat.lt_of_succ_le hj1
    have hli_prev := ih (le_of_lt hj)
    have hli_step := (section_19_1_tower_step ht hgen hj).2.2.2.2
    rw [Fintype.linearIndependent_iff]
    intro c hc idx
    -- Group `idx : GarlingMultiIndex n (j + 1)` into `(init : GarlingMultiIndex n j, last : Fin (n - j))`:
    let splitEquiv : GarlingMultiIndex n (j + 1) ≃ GarlingMultiIndex n j × Fin (n - j) :=
      { toFun := fun f => (fun k => f k.castSucc, f (Fin.last j))
        invFun := fun p k =>
          if h : k.1 < j then p.1 ⟨k.1, h⟩
          else (show Fin (n - j) = Fin (n - k.1) from by congr 1; omega) ▸ p.2
        left_inv := fun f => by
          funext k
          by_cases h : k.1 < j
          · simp [h]
          · simp only [h, ↓reduceDIte]
            have hk : k = Fin.last j := Fin.ext (show k.1 = j by omega)
            subst hk; rfl
        right_inv := fun ⟨p1, p2⟩ => by
          ext k
          · simp [k.2]
          · simp }
    have hmon_split : ∀ p : GarlingMultiIndex n j × Fin (n - j),
        multiIndexMonomial hj1 t (splitEquiv.symm p) =
          multiIndexMonomial (le_of_lt hj) t p.1 * (t ⟨j, hj⟩) ^ p.2.1 := by
      rintro ⟨p1, p2⟩
      unfold multiIndexMonomial
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun k _ => ?_
        simp [splitEquiv, k.2]
      · simp [splitEquiv]
    -- Rewrite the sum as a linear combination of `t_j^r` with coefficients in `M_j`:
    have hmem_mon : ∀ p1 : GarlingMultiIndex n j,
        multiIndexMonomial (le_of_lt hj) t p1 ∈ towerField K t j := by
      intro p1
      unfold multiIndexMonomial
      refine (towerField K t j).prod_mem fun k _ => ?_
      have ht_mem : t ⟨k.1, lt_of_lt_of_le k.2 (le_of_lt hj)⟩ ∈ towerField K t j :=
        IntermediateField.subset_adjoin K _ (Or.inr ⟨⟨k.1, lt_of_lt_of_le k.2 (le_of_lt hj)⟩, k.2, rfl⟩)
      exact pow_mem ht_mem (p1 k).1
    let coeffMj : Fin (n - j) → towerField K t j := fun r =>
      ∑ p1 : GarlingMultiIndex n j,
        ⟨((c (splitEquiv.symm (p1, r)) : E) * multiIndexMonomial (le_of_lt hj) t p1),
          (towerField K t j).mul_mem
            (towerField_mono K t (Nat.zero_le j) (by rw [towerField_zero]; exact (c _).2))
            (hmem_mon p1)⟩
    have hsum_r : ∑ r : Fin (n - j), coeffMj r • (t ⟨j, hj⟩) ^ r.1 = 0 := by
      rw [← hc]
      rw [← Equiv.sum_comp splitEquiv.symm, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Algebra.smul_def]
      have hcoe : (algebraMap (towerField K t j) E) (coeffMj r) =
          ∑ p1 : GarlingMultiIndex n j,
            (c (splitEquiv.symm (p1, r)) : E) * multiIndexMonomial (le_of_lt hj) t p1 := by
        simp [coeffMj]
      rw [hcoe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p1 _ => ?_
      rw [Algebra.smul_def, hmon_split (p1, r), mul_assoc]
      rfl
    have hcoeff0 := Fintype.linearIndependent_iff.mp hli_step coeffMj hsum_r (splitEquiv idx).2
    have hsum_p1 : ∑ p1 : GarlingMultiIndex n j,
        c (splitEquiv.symm (p1, (splitEquiv idx).2)) • multiIndexMonomial (le_of_lt hj) t p1 = 0 := by
      have hv := congrArg Subtype.val hcoeff0
      simpa [coeffMj, Algebra.smul_def] using hv
    have hfinal := Fintype.linearIndependent_iff.mp hli_prev _ hsum_p1 (splitEquiv idx).1
    simpa using hfinal

/-- **§19.1 Prose Multi-Index Basis** (printed pp. 149–150 / PDF pp. 157–158):
At `j = n`, the `n!` monomials `∏_{k < n} t_k^{i_k}` (`idx : GarlingMultiIndex n n`, i.e.
`0 ≤ i_k ≤ n - k` in 1-based indexing) form a `K(s₁, …, sₙ)`-basis of `E = K(t₁, …, tₙ)`. -/
theorem section_19_1_multi_index_basis {K E : Type*} [Field K] [Field E] [Algebra K E]
    {n : ℕ} {t : Fin n → E} (ht : IsGarlingAlgIndepTuple K t)
    (hgen : IntermediateField.adjoin K (Set.range t) = ⊤) :
    (∃ B : Module.Basis (GarlingMultiIndex n n) (elemSymmField K t) E,
      ∀ idx : GarlingMultiIndex n n, B idx = multiIndexMonomial le_rfl t idx) ∧
    IsBasis (elemSymmField K t) E (Set.range (multiIndexMonomial le_rfl t)) := by
  have hfin_eq : Module.finrank (elemSymmField K t) E = n.factorial := by
    have h0 := (exercise_19_1 ht hgen (Nat.zero_le n)).2.1
    rw [towerField_zero, Nat.sub_zero] at h0
    exact h0
  have _ : Module.Finite (elemSymmField K t) E :=
    Module.finite_of_finrank_pos (by rw [hfin_eq]; exact Nat.factorial_pos n)
  have hli := section_19_1_multi_index_linearIndependent ht hgen n le_rfl
  have hcard : Fintype.card (GarlingMultiIndex n n) = Module.finrank (elemSymmField K t) E := by
    rw [(section_19_1_p149_strict_bound_typo_remark n).2.2, hfin_eq]
  have hspan : Submodule.span (elemSymmField K t) (Set.range (multiIndexMonomial le_rfl t)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, hcard])
  let B : Module.Basis (GarlingMultiIndex n n) (elemSymmField K t) E :=
    Module.Basis.mk hli (le_of_eq hspan.symm)
  have hB : ∀ idx : GarlingMultiIndex n n, B idx = multiIndexMonomial le_rfl t idx :=
    fun idx => by simp [B, Module.Basis.mk_apply]
  refine ⟨⟨B, hB⟩, ?_, hspan⟩
  rw [isLinearlyIndependent_iff]
  exact (linearIndepOn_id_range_iff hli.injective).mpr hli

/-! #### `Exercise 19.2` (lexicographic order & principal term) and `Theorem 19.4` + `Corollary` (p. 150) -/

/-- Garling's inline prose definition of *follows* / *lexicographic order* on exponent vectors
(`Exercise 19.2`, printed p. 150 / PDF p. 158): `l` *follows* `k` (`lexFollows k l`) iff at the
least index `j` with `k j ≠ l j`, we have `k j < l j`. -/
def lexFollows {n : ℕ} (k l : Fin n →₀ ℕ) : Prop :=
  ∃ j : Fin n, (∀ i : Fin n, i < j → k i = l i) ∧ k j < l j

theorem lexFollows_irrefl {n : ℕ} (k : Fin n →₀ ℕ) : ¬ lexFollows k k := by
  rintro ⟨j, _, hlt⟩
  exact lt_irrefl _ hlt

theorem lexFollows_trans {n : ℕ} {a b c : Fin n →₀ ℕ}
    (hab : lexFollows a b) (hbc : lexFollows b c) : lexFollows a c := by
  rcases hab with ⟨j₁, heq₁, hlt₁⟩
  rcases hbc with ⟨j₂, heq₂, hlt₂⟩
  rcases lt_trichotomy j₁ j₂ with hlt | rfl | hgt
  · refine ⟨j₁, fun i hi => (heq₁ i hi).trans (heq₂ i (lt_trans hi hlt)), ?_⟩
    rwa [← heq₂ j₁ hlt]
  · exact ⟨j₁, fun i hi => (heq₁ i hi).trans (heq₂ i hi), lt_trans hlt₁ hlt₂⟩
  · refine ⟨j₂, fun i hi => (heq₁ i (lt_trans hi hgt)).trans (heq₂ i hi), ?_⟩
    rwa [heq₁ j₂ hgt]

theorem lexFollows_trichotomy {n : ℕ} (k l : Fin n →₀ ℕ) :
    lexFollows k l ∨ k = l ∨ lexFollows l k := by
  by_cases hkl : k = l
  · exact Or.inr (Or.inl hkl)
  · have hex : ∃ j : ℕ, ∃ hj : j < n, k ⟨j, hj⟩ ≠ l ⟨j, hj⟩ := by
      by_contra hall
      push Not at hall
      apply hkl
      ext i
      exact hall i.1 i.2
    classical
    let j := Nat.find hex
    obtain ⟨hj, hne⟩ := Nat.find_spec hex
    have hmin : ∀ i : Fin n, i < ⟨j, hj⟩ → k i = l i := by
      intro i hi
      by_contra hni
      exact Nat.find_min hex hi ⟨i.2, hni⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨⟨j, hj⟩, hmin, hlt⟩
    · exact Or.inr (Or.inr ⟨⟨j, hj⟩, fun i hi => (hmin i hi).symm, hgt⟩)

theorem lexFollows_add_right {n : ℕ} {k l : Fin n →₀ ℕ} (h : lexFollows k l) (m : Fin n →₀ ℕ) :
    lexFollows (k + m) (l + m) := by
  rcases h with ⟨j, heq, hlt⟩
  exact ⟨j, fun i hi => by simp [heq i hi], by simp [hlt]⟩

theorem lexFollows_add_left {n : ℕ} (m : Fin n →₀ ℕ) {k l : Fin n →₀ ℕ} (h : lexFollows k l) :
    lexFollows (m + k) (m + l) := by
  rw [add_comm m k, add_comm m l]
  exact lexFollows_add_right h m

theorem lexFollows_add_le {n : ℕ} {k₁ l₁ k₂ l₂ : Fin n →₀ ℕ}
    (h1 : k₁ = l₁ ∨ lexFollows k₁ l₁) (h2 : k₂ = l₂ ∨ lexFollows k₂ l₂) :
    k₁ + k₂ = l₁ + l₂ ∨ lexFollows (k₁ + k₂) (l₁ + l₂) := by
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl rfl
  · exact Or.inr (lexFollows_add_left k₁ h2)
  · exact Or.inr (lexFollows_add_right h1 k₂)
  · exact Or.inr (lexFollows_trans (lexFollows_add_right h1 k₂) (lexFollows_add_left l₁ h2))

/-- Well-foundedness of `lexFollows` on `Fin n →₀ ℕ` (proved directly by induction on `n`). -/
theorem lexFollows_wf (n : ℕ) : WellFounded (@lexFollows n) := by
  induction n with
  | zero =>
    refine ⟨fun x => Acc.intro x fun y h => ?_⟩
    rcases h with ⟨j, _, _⟩
    exact Fin.elim0 j
  | succ m ih =>
    let split : (Fin (m + 1) →₀ ℕ) → ℕ × (Fin m →₀ ℕ) := fun k =>
      (k 0, Finsupp.equivFunOnFinite.symm (fun i : Fin m => k i.succ))
    have hrel : ∀ k l : Fin (m + 1) →₀ ℕ,
        lexFollows k l → Prod.Lex (· < ·) (@lexFollows m) (split k) (split l) := by
      rintro k l ⟨j, heq, hlt⟩
      refine Fin.cases ?_ ?_ j heq hlt
      · intro _ h0
        exact Prod.Lex.left _ _ h0
      · intro j' heq' hlt'
        have h0 : k 0 = l 0 := heq' 0 (Fin.succ_pos j')
        have hright : lexFollows (split k).2 (split l).2 := by
          refine ⟨j', fun i hi => ?_, ?_⟩
          · change k i.succ = l i.succ
            exact heq' i.succ (Fin.succ_lt_succ_iff.mpr hi)
          · change k j'.succ < l j'.succ
            exact hlt'
        rw [show split k = (k 0, (split k).2) from rfl,
          show split l = (l 0, (split l).2) from rfl, h0]
        exact Prod.Lex.right (l 0) hright
    have hwf_prod : WellFounded (Prod.Lex (· < ·) (@lexFollows m)) :=
      WellFounded.prod_lex Nat.lt_wfRel.wf ih
    exact Subrelation.wf (fun {k l} h => hrel k l h) (InvImage.wf split hwf_prod)

/-- Every non-empty finite set of exponent vectors has a unique `lexFollows`-maximum. -/
theorem exists_max_lexFollows {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (hs : s.Nonempty) :
    ∃ k ∈ s, ∀ l ∈ s, l ≠ k → lexFollows l k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | insert a s ha ih =>
    by_cases hs0 : s.Nonempty
    · obtain ⟨k, hk, hmax⟩ := ih hs0
      rcases lexFollows_trichotomy a k with hak | rfl | hka
      · refine ⟨k, Finset.mem_insert_of_mem hk, fun l hl hlk => ?_⟩
        rcases Finset.mem_insert.mp hl with rfl | hls
        · exact hak
        · exact hmax l hls hlk
      · refine ⟨a, Finset.mem_insert_self a s, fun l hl hla => ?_⟩
        rcases Finset.mem_insert.mp hl with rfl | hls
        · exact (hla rfl).elim
        · exact hmax l hls hla
      · refine ⟨a, Finset.mem_insert_self a s, fun l hl hla => ?_⟩
        rcases Finset.mem_insert.mp hl with rfl | hls
        · exact (hla rfl).elim
        · by_cases hlk : l = k
          · exact hlk ▸ hka
          · exact lexFollows_trans (hmax l hls hlk) hka
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs0]
      exact ⟨a, Finset.mem_singleton_self a, fun l hl hla => (hla (Finset.mem_singleton.mp hl)).elim⟩

/-- Garling's inline prose definition of the *principal term* of `f ∈ R[t₁, …, tₙ]`
(`Exercise 19.2`, printed p. 150 / PDF p. 158): `a t₁^{k₁}⋯tₙ^{kₙ}` is the principal term of `f`
iff `a ≠ 0`, `f.coeff k = a`, and `k` follows every other exponent `l ∈ f.support`. -/
def HasPrincipalTerm {R : Type*} [CommRing R] {n : ℕ}
    (f : MvPolynomial (Fin n) R) (a : R) (k : Fin n →₀ ℕ) : Prop :=
  a ≠ 0 ∧ f.coeff k = a ∧ ∀ l ∈ f.support, l ≠ k → lexFollows l k

theorem exists_principalTerm_of_ne_zero {R : Type*} [CommRing R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hf : f ≠ 0) :
    ∃ (a : R) (k : Fin n →₀ ℕ), HasPrincipalTerm f a k := by
  have hne : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf
  obtain ⟨k, hk, hmax⟩ := exists_max_lexFollows f.support hne
  exact ⟨f.coeff k, k, MvPolynomial.mem_support_iff.mp hk, rfl, hmax⟩

theorem hasPrincipalTerm_unique {R : Type*} [CommRing R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} {a₁ a₂ : R} {k₁ k₂ : Fin n →₀ ℕ}
    (h1 : HasPrincipalTerm f a₁ k₁) (h2 : HasPrincipalTerm f a₂ k₂) :
    a₁ = a₂ ∧ k₁ = k₂ := by
  have hk : k₁ = k₂ := by
    by_contra hne
    have h12 : lexFollows k₁ k₂ := h2.2.2 k₁ (MvPolynomial.mem_support_iff.mpr (h1.2.1.symm ▸ h1.1)) hne
    have h21 : lexFollows k₂ k₁ := h1.2.2 k₂ (MvPolynomial.mem_support_iff.mpr (h2.2.1.symm ▸ h2.1)) (Ne.symm hne)
    exact lexFollows_irrefl k₁ (lexFollows_trans h12 h21)
  subst hk
  exact ⟨h1.2.1.symm.trans h2.2.1, rfl⟩

/-- Multiplicativity of principal terms over an integral domain `R`. -/
theorem hasPrincipalTerm_mul {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f g : MvPolynomial (Fin n) R} {a b : R} {k l : Fin n →₀ ℕ}
    (hf : HasPrincipalTerm f a k) (hg : HasPrincipalTerm g b l) :
    HasPrincipalTerm (f * g) (a * b) (k + l) := by
  classical
  refine ⟨mul_ne_zero hf.1 hg.1, ?_, ?_⟩
  · rw [MvPolynomial.coeff_mul]
    have hmem : (k, l) ∈ Finset.antidiagonal (k + l) := Finset.mem_antidiagonal.mpr rfl
    rw [Finset.sum_eq_single (k, l)]
    · rw [hf.2.1, hg.2.1]
    · rintro ⟨u, v⟩ huv hne
      by_cases hu : u ∈ f.support
      · by_cases hv : v ∈ g.support
        · exfalso
          have hu_le : u = k ∨ lexFollows u k :=
            if h : u = k then Or.inl h else Or.inr (hf.2.2 u hu h)
          have hv_le : v = l ∨ lexFollows v l :=
            if h : v = l then Or.inl h else Or.inr (hg.2.2 v hv h)
          have hsum : u + v = k + l := Finset.mem_antidiagonal.mp huv
          rcases hu_le with rfl | hu_lt
          · rcases hv_le with rfl | hv_lt
            · exact hne rfl
            · have hlt := lexFollows_add_left u hv_lt
              rw [hsum] at hlt
              exact lexFollows_irrefl _ hlt
          · rcases hv_le with rfl | hv_lt
            · have hlt := lexFollows_add_right hu_lt v
              rw [hsum] at hlt
              exact lexFollows_irrefl _ hlt
            · have hlt := lexFollows_trans (lexFollows_add_right hu_lt v) (lexFollows_add_left k hv_lt)
              rw [hsum] at hlt
              exact lexFollows_irrefl _ hlt
        · rw [MvPolynomial.notMem_support_iff.mp hv, mul_zero]
      · rw [MvPolynomial.notMem_support_iff.mp hu, zero_mul]
    · intro h; exact (h hmem).elim
  · intro m hm hne
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hm
    have hex : ∃ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hm (Finset.sum_eq_zero hall)
    obtain ⟨⟨u, v⟩, huv, hnz⟩ := hex
    have hu : u ∈ f.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hnz)
    have hv : v ∈ g.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hnz)
    have hu_le : u = k ∨ lexFollows u k :=
      if h : u = k then Or.inl h else Or.inr (hf.2.2 u hu h)
    have hv_le : v = l ∨ lexFollows v l :=
      if h : v = l then Or.inl h else Or.inr (hg.2.2 v hv h)
    have hsum : u + v = m := Finset.mem_antidiagonal.mp huv
    rcases lexFollows_add_le hu_le hv_le with heq | hlt
    · exact (hne (hsum.symm.trans heq)).elim
    · rwa [hsum] at hlt

theorem hasPrincipalTerm_pow {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} {a : R} {k : Fin n →₀ ℕ}
    (hf : HasPrincipalTerm f a k) (d : ℕ) :
    HasPrincipalTerm (f ^ d) (a ^ d) (d • k) := by
  induction d with
  | zero =>
    simp only [pow_zero, zero_smul]
    refine ⟨one_ne_zero, by simp, fun l hl hne => ?_⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hl
    split_ifs at hl with h
    · exact (hne h.symm).elim
    · exact (hl rfl).elim
  | succ d ih =>
    rw [pow_succ, pow_succ, succ_nsmul]
    exact hasPrincipalTerm_mul ih hf

theorem hasPrincipalTerm_C_mul {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} {a b : R} {k : Fin n →₀ ℕ}
    (ha : a ≠ 0) (hf : HasPrincipalTerm f b k) :
    HasPrincipalTerm (MvPolynomial.C a * f) (a * b) k := by
  have hC : HasPrincipalTerm (MvPolynomial.C a : MvPolynomial (Fin n) R) a 0 := by
    refine ⟨ha, by simp, fun l hl hne => ?_⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hl
    split_ifs at hl with h
    · exact (hne h.symm).elim
    · exact (hl rfl).elim
  simpa using hasPrincipalTerm_mul hC hf

/-- Indicator exponent vector `(1, …, 1, 0, …, 0)` with `1` on coordinates `i ≤ m` and `0` on `i > m`. -/
noncomputable def prefixIndicator {n : ℕ} (m : Fin n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin n => if i ≤ m then 1 else 0)

@[simp]
theorem prefixIndicator_apply {n : ℕ} (m i : Fin n) :
    prefixIndicator m i = if i ≤ m then 1 else 0 := rfl

/-- The principal term of `s_{m+1} = elemSymmPoly R n m` is `1 * t₁ ⋯ t_{m+1}` (`prefixIndicator m`). -/
theorem hasPrincipalTerm_elemSymmPoly {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (m : Fin n) :
    HasPrincipalTerm (elemSymmPoly R n m) 1 (prefixIndicator m) := by
  classical
  have hcoeff : ∀ d : Fin n →₀ ℕ,
      (elemSymmPoly R n m).coeff d =
        if (∀ i : Fin n, d i ≤ 1) ∧ ((Finset.univ : Finset (Fin n)).filter (fun i => d i = 1)).card = m.1 + 1
        then 1 else 0 := by
    intro d
    change (MvPolynomial.esymm (Fin n) R (m.1 + 1)).coeff d = _
    rw [MvPolynomial.esymm, MvPolynomial.coeff_sum]
    have hterm : ∀ S : Finset (Fin n),
        (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) R)).coeff d =
          if d = ∑ i ∈ S, Finsupp.single i 1 then 1 else 0 := by
      intro S
      have hprod : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) R)) =
          MvPolynomial.monomial (∑ i ∈ S, Finsupp.single i 1) (1 : R) := by
        induction S using Finset.induction_on with
        | empty => simp
        | insert a S ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.X,
            MvPolynomial.monomial_mul_monomial, one_mul]
      rw [hprod, MvPolynomial.coeff_monomial]
      simp [eq_comm]
    simp_rw [hterm]
    split_ifs with hcond
    · rcases hcond with ⟨hle1, hcard⟩
      let S₀ := (Finset.univ : Finset (Fin n)).filter (fun i => d i = 1)
      have hdS₀ : d = ∑ i ∈ S₀, Finsupp.single i 1 := by
        ext i
        rw [Finsupp.finsetSum_apply]
        simp only [Finsupp.single_apply, Finset.sum_ite_eq', S₀, Finset.mem_filter,
          Finset.mem_univ, true_and]
        have hi := hle1 i
        split_ifs with h1 <;> omega
      have hS₀_mem : S₀ ∈ (Finset.univ : Finset (Fin n)).powersetCard (m.1 + 1) :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
      rw [Finset.sum_eq_single S₀]
      · simp [hdS₀]
      · intro S _ hSne
        have hnd : d ≠ ∑ i ∈ S, Finsupp.single i 1 := by
          intro hdS
          apply hSne
          ext i
          have hi : d i = if i ∈ S then 1 else 0 := by
            rw [hdS, Finsupp.finsetSum_apply]
            simp [Finsupp.single_apply]
          simp [S₀, hi]
        simp [hnd]
      · intro h; exact (h hS₀_mem).elim
    · refine Finset.sum_eq_zero fun S hS => ?_
      have hnd : d ≠ ∑ i ∈ S, Finsupp.single i 1 := by
        intro hdS
        apply hcond
        have hScard : S.card = m.1 + 1 := (Finset.mem_powersetCard.mp hS).2
        have hval : ∀ i : Fin n, d i = if i ∈ S then 1 else 0 := fun i => by
          rw [hdS, Finsupp.finsetSum_apply]; simp [Finsupp.single_apply]
        refine ⟨fun i => by rw [hval i]; split_ifs <;> omega, ?_⟩
        have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => d i = 1) = S := by
          ext i; simp [hval i]
        rw [hfilt, hScard]
      simp [hnd]
  have hpref_card : ((Finset.univ : Finset (Fin n)).filter (fun i => prefixIndicator m i = 1)).card = m.1 + 1 := by
    have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => prefixIndicator m i = 1) =
        (Finset.univ : Finset (Fin n)).filter (fun i => i ≤ m) := by
      ext i; simp
    rw [hfilt]
    let e : {i : Fin n // i ≤ m} ≃ Fin (m.1 + 1) :=
      { toFun := fun ⟨i, hi⟩ => ⟨i.1, Nat.lt_succ_of_le hi⟩
        invFun := fun k => ⟨⟨k.1, lt_of_lt_of_le k.2 (Nat.succ_le_of_lt m.2)⟩, Nat.le_of_lt_succ k.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
  refine ⟨one_ne_zero, ?_, ?_⟩
  · have hok : (∀ i : Fin n, prefixIndicator m i ≤ 1) ∧
        ((Finset.univ : Finset (Fin n)).filter (fun i => prefixIndicator m i = 1)).card = m.1 + 1 :=
      ⟨fun i => by simp; split_ifs <;> omega, hpref_card⟩
    exact (hcoeff (prefixIndicator m)).trans (ite_eq_left_iff.mpr fun h => (h hok).elim)
  · intro l hl hne
    rw [MvPolynomial.mem_support_iff, hcoeff] at hl
    have hcond : (∀ i : Fin n, l i ≤ 1) ∧
        ((Finset.univ : Finset (Fin n)).filter (fun i => l i = 1)).card = m.1 + 1 := by
      by_contra hc
      simp [hc] at hl
    rcases lexFollows_trichotomy l (prefixIndicator m) with hlt | heq | hgt
    · exact hlt
    · exact (hne heq).elim
    · exfalso
      rcases hgt with ⟨j, heqj, hltj⟩
      -- Since `prefixIndicator m j < l j ≤ 1`, we have `prefixIndicator m j = 0`, so `j > m`,
      -- hence `l i = prefixIndicator m i = 1` for EVERY `i ≤ m`, plus `l j = 1`, giving `card ≥ m + 2`!
      have hlj1 : l j = 1 := by have := hcond.1 j; omega
      have hpj0 : prefixIndicator m j = 0 := by omega
      have hjm : m < j := by
        by_contra hle; push Not at hle
        simp [prefixIndicator_apply, hle] at hpj0
      have hsub : (Finset.univ : Finset (Fin n)).filter (fun i => i ≤ m) ⊂
          (Finset.univ : Finset (Fin n)).filter (fun i => l i = 1) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlj1⟩, by simp [not_le.mpr hjm]⟩
        · intro i hi
          have him : i ≤ m := (Finset.mem_filter.mp hi).2
          have hij : i < j := lt_of_le_of_lt him hjm
          have hli : l i = 1 := by rw [← heqj i hij]; simp [prefixIndicator_apply, him]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli⟩
      have hlt_card := Finset.card_lt_card hsub
      have hcard_le : ((Finset.univ : Finset (Fin n)).filter (fun i => i ≤ m)).card = m.1 + 1 := by
        have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => prefixIndicator m i = 1) =
            (Finset.univ : Finset (Fin n)).filter (fun i => i ≤ m) := by ext i; simp
        rw [← hfilt, hpref_card]
      omega

/-- Garling's `Exercise 19.2(ii)` product `a s₁^{k₁-k₂} ⋯ s_{n-1}^{k_{n-1}-kₙ} sₙ^{kₙ}`. -/
noncomputable def elemSymmMonomial {R : Type*} [CommRing R] {n : ℕ}
    (a : R) (k : Fin n →₀ ℕ) : MvPolynomial (Fin n) R :=
  MvPolynomial.C a *
    ∏ m : Fin n,
      (elemSymmPoly R n m) ^
        (if h : m.1 + 1 < n then k m - k ⟨m.1 + 1, h⟩ else k m)

/-- Corresponding preimage monomial `a x₁^{k₁-k₂} ⋯ x_{n-1}^{k_{n-1}-kₙ} xₙ^{kₙ} ∈ R[x₁, …, xₙ]`. -/
noncomputable def elemSymmMonomialPreimage {R : Type*} [CommRing R] {n : ℕ}
    (a : R) (k : Fin n →₀ ℕ) : MvPolynomial (Fin n) R :=
  MvPolynomial.C a *
    ∏ m : Fin n,
      (MvPolynomial.X m : MvPolynomial (Fin n) R) ^
        (if h : m.1 + 1 < n then k m - k ⟨m.1 + 1, h⟩ else k m)

theorem elemSymmSubst_monomialPreimage {R : Type*} [CommRing R] {n : ℕ}
    (a : R) (k : Fin n →₀ ℕ) :
    elemSymmSubst R n (elemSymmMonomialPreimage a k) = elemSymmMonomial a k := by
  unfold elemSymmSubst elemSymmMonomialPreimage elemSymmMonomial
  rw [map_mul, MvPolynomial.aeval_C, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [map_pow, MvPolynomial.aeval_X]

/-- Principal term of `∏ m : Fin n, s_{m+1}^{d m}` for any exponent vector `d : Fin n →₀ ℕ`. -/
theorem hasPrincipalTerm_prod_elemSymmPoly {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (d : Fin n →₀ ℕ) :
    HasPrincipalTerm (∏ m : Fin n, (elemSymmPoly R n m) ^ (d m)) 1
      (∑ m : Fin n, d m • prefixIndicator m) := by
  classical
  suffices ∀ s : Finset (Fin n),
      HasPrincipalTerm (∏ m ∈ s, (elemSymmPoly R n m) ^ (d m)) 1
        (∑ m ∈ s, d m • prefixIndicator m) from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    refine ⟨one_ne_zero, by simp, fun l hl hne => ?_⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hl
    split_ifs at hl with h
    · exact (hne h.symm).elim
    · exact (hl rfl).elim
  | insert m s hm ih =>
    rw [Finset.prod_insert hm, Finset.sum_insert hm]
    have h1 := hasPrincipalTerm_pow (hasPrincipalTerm_elemSymmPoly (R := R) m) (d m)
    rw [one_pow] at h1
    simpa [one_mul] using hasPrincipalTerm_mul h1 ih

/-- The map `d ↦ ∑ m, d m • prefixIndicator m` is injective on `Fin n →₀ ℕ`. -/
theorem sum_prefixIndicator_injective (n : ℕ) :
    Function.Injective (fun d : Fin n →₀ ℕ => ∑ m : Fin n, d m • prefixIndicator m) := by
  have heval : ∀ (d : Fin n →₀ ℕ) (i : Fin n),
      (∑ m : Fin n, d m • prefixIndicator m) i =
        ∑ m ∈ (Finset.univ : Finset (Fin n)).filter (fun m => i ≤ m), d m := by
    intro d i
    rw [Finsupp.finsetSum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [prefixIndicator_apply]
  intro d₁ d₂ hEq
  ext i
  by_cases hi : i.1 + 1 < n
  · have h1 := congrArg (fun f : Fin n →₀ ℕ => f i) hEq
    have h2 := congrArg (fun f : Fin n →₀ ℕ => f ⟨i.1 + 1, hi⟩) hEq
    rw [heval, heval] at h1 h2
    have hsplit : ∀ d : Fin n →₀ ℕ,
        (∑ m ∈ (Finset.univ : Finset (Fin n)).filter (fun m => i ≤ m), d m) =
          d i + ∑ m ∈ (Finset.univ : Finset (Fin n)).filter (fun m => ⟨i.1 + 1, hi⟩ ≤ m), d m := by
      intro d
      have hset : (Finset.univ : Finset (Fin n)).filter (fun m => i ≤ m) =
          insert i ((Finset.univ : Finset (Fin n)).filter (fun m => ⟨i.1 + 1, hi⟩ ≤ m)) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        change i.1 ≤ m.1 ↔ m.1 = i.1 ∨ i.1 + 1 ≤ m.1
        omega
      rw [hset, Finset.sum_insert]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (i.1 + 1 ≤ i.1)
      omega
    rw [hsplit d₁, hsplit d₂] at h1
    omega
  · have h1 := congrArg (fun f : Fin n →₀ ℕ => f i) hEq
    rw [heval, heval] at h1
    have hset : (Finset.univ : Finset (Fin n)).filter (fun m => i ≤ m) = {i} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      change i.1 ≤ m.1 ↔ m.1 = i.1
      have hm := m.2
      omega
    rw [hset, Finset.sum_singleton, Finset.sum_singleton] at h1
    exact h1

/-- **Exercise 19.2(i)** (over any commutative ring `R`, p. 150):
If `f` is symmetric with principal term `a t₁^{k₁}⋯tₙ^{kₙ}`, then `k₁ ≥ k₂ ≥ ⋯ ≥ kₙ`. -/
theorem exercise_19_2_i {R : Type*} [CommRing R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hsym : IsGarlingSymmetricPoly f)
    {a : R} {k : Fin n →₀ ℕ} (hpt : HasPrincipalTerm f a k) :
    ∀ i j : Fin n, i ≤ j → k j ≤ k i := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · by_contra hgt
    push Not at hgt
    let σ : SigmaN n := Equiv.swap i j
    let l : Fin n →₀ ℕ := Finsupp.mapDomain σ k
    have hl_apply : ∀ m : Fin n, l m = k (σ m) := fun m => by
      change Finsupp.mapDomain σ k m = k (σ m)
      rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]
      rfl
    have hl_coeff : f.coeff l = a := by
      have hren : (MvPolynomial.rename σ f).coeff l = f.coeff k := by
        rw [MvPolynomial.coeff_rename_mapDomain σ σ.injective]
      rw [hsym σ] at hren
      exact hren.trans hpt.2.1
    have hl_mem : l ∈ f.support := MvPolynomial.mem_support_iff.mpr (hl_coeff.symm ▸ hpt.1)
    have hkl : lexFollows k l := by
      refine ⟨i, fun m hm => ?_, ?_⟩
      · have hmi : m ≠ i := ne_of_lt hm
        have hmj : m ≠ j := ne_of_lt (lt_trans hm hlt)
        rw [hl_apply, Equiv.swap_apply_of_ne_of_ne hmi hmj]
      · rw [hl_apply, Equiv.swap_apply_left]
        exact hgt
    have hne : l ≠ k := fun h => lexFollows_irrefl k (h ▸ hkl)
    exact lexFollows_irrefl k (lexFollows_trans hkl (hpt.2.2 l hl_mem hne))

/-- **Exercise 19.2(ii)** (over any integral domain `R`, p. 150):
`a s₁^{k₁ - k₂} ⋯ s_{n-1}^{k_{n-1} - kₙ} sₙ^{kₙ}` has the same principal term `(a, k)` as `f`. -/
theorem exercise_19_2_ii {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hsym : IsGarlingSymmetricPoly f)
    {a : R} {k : Fin n →₀ ℕ} (hpt : HasPrincipalTerm f a k) :
    HasPrincipalTerm (elemSymmMonomial a k) a k := by
  have hanti := exercise_19_2_i hsym hpt
  let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun m : Fin n => if h : m.1 + 1 < n then k m - k ⟨m.1 + 1, h⟩ else k m)
  have hprod := hasPrincipalTerm_C_mul hpt.1 (hasPrincipalTerm_prod_elemSymmPoly (R := R) d)
  rw [mul_one] at hprod
  have hsum_eq : (∑ m : Fin n, d m • prefixIndicator m) = k := by
    ext i
    rw [Finsupp.finsetSum_apply]
    have htele : ∀ r : ℕ, ∀ (hr : i.1 + r < n),
        (∑ m ∈ (Finset.univ : Finset (Fin n)).filter (fun m => i.1 ≤ m.1 ∧ m.1 ≤ i.1 + r), d m) =
          k i - (if h : i.1 + r + 1 < n then k ⟨i.1 + r + 1, h⟩ else 0) := by
      intro r
      induction r with
      | zero =>
        intro hr
        have hset : (Finset.univ : Finset (Fin n)).filter (fun m => i.1 ≤ m.1 ∧ m.1 ≤ i.1 + 0) = {i} := by
          ext m; simp [Fin.ext_iff]; omega
        rw [hset, Finset.sum_singleton]
        change (if h : i.1 + 1 < n then k i - k ⟨i.1 + 1, h⟩ else k i) = _
        split_ifs with h <;> simp
      | succ r ihr =>
        intro hr
        have hprev := ihr (by omega)
        let idx : Fin n := ⟨i.1 + (r + 1), hr⟩
        have hset : (Finset.univ : Finset (Fin n)).filter (fun m => i.1 ≤ m.1 ∧ m.1 ≤ i.1 + (r + 1)) =
            insert idx ((Finset.univ : Finset (Fin n)).filter (fun m => i.1 ≤ m.1 ∧ m.1 ≤ i.1 + r)) := by
          ext m; simp [Fin.ext_iff, idx]; omega
        have hr' : i.1 + r + 1 < n := by omega
        rw [hset, Finset.sum_insert (by simp [idx]), hprev]
        simp only [hr', ↓reduceDIte]
        have hidx_eq : (⟨i.1 + r + 1, hr'⟩ : Fin n) = idx := Fin.ext (show i.1 + r + 1 = i.1 + (r + 1) by omega)
        rw [hidx_eq]
        have hle1 : k idx ≤ k i := hanti i idx (by change i.1 ≤ i.1 + (r + 1); omega)
        have hidx_val : idx.1 = i.1 + (r + 1) := rfl
        change (if h : idx.1 + 1 < n then k idx - k ⟨idx.1 + 1, h⟩ else k idx) +
            (k i - k idx) = k i - (if h : i.1 + (r + 1) + 1 < n then k ⟨i.1 + (r + 1) + 1, h⟩ else 0)
        by_cases hnext : i.1 + (r + 1) + 1 < n
        · have hnext' : idx.1 + 1 < n := by rw [hidx_val]; exact hnext
          simp only [hnext', hnext, ↓reduceDIte]
          have hfin_eq : (⟨idx.1 + 1, hnext'⟩ : Fin n) = ⟨i.1 + (r + 1) + 1, hnext⟩ :=
            Fin.ext (by simp [hidx_val])
          rw [hfin_eq]
          have hle2 : k ⟨i.1 + (r + 1) + 1, hnext⟩ ≤ k idx :=
            hanti idx ⟨i.1 + (r + 1) + 1, hnext⟩ (by change i.1 + (r + 1) ≤ i.1 + (r + 1) + 1; omega)
          omega
        · have hnext' : ¬ (idx.1 + 1 < n) := by rw [hidx_val]; exact hnext
          simp only [hnext', hnext, ↓reduceDIte]
          omega
    have hfilt : (∑ m : Fin n, (d m • prefixIndicator m) i) =
        ∑ m ∈ (Finset.univ : Finset (Fin n)).filter (fun m => i.1 ≤ m.1 ∧ m.1 ≤ i.1 + (n - 1 - i.1)), d m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Finsupp.smul_apply, smul_eq_mul, prefixIndicator_apply, Fin.le_def]
      by_cases him : i.1 ≤ m.1
      · have hle : m.1 ≤ i.1 + (n - 1 - i.1) := by have := m.2; omega
        simp [him, hle]
      · simp [him]
    have hnot_lt : ¬ (i.1 + (n - 1 - i.1) + 1 < n) := by omega
    rw [hfilt, htele (n - 1 - i.1) (by omega)]
    simp [hnot_lt]
  rw [hsum_eq] at hprod
  exact hprod

/-- **Exercise 19.2(iii)** & **Theorem 19.4 (Existence over any integral domain `R`)** (p. 150):
Every symmetric polynomial `f ∈ R[t₁, …, tₙ]` over an integral domain `R` equals `F(s₁, …, sₙ)` for
some `F ∈ R[x₁, …, xₙ]`. -/
theorem exercise_19_2_iii_domain {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hsym : IsGarlingSymmetricPoly f) :
    ∃ F : MvPolynomial (Fin n) R, elemSymmSubst R n F = f := by
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  · obtain ⟨a, k, hpt⟩ := exists_principalTerm_of_ne_zero hf0
    suffices ∀ (k : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) R) (a : R),
        IsGarlingSymmetricPoly f → HasPrincipalTerm f a k →
        ∃ F : MvPolynomial (Fin n) R, elemSymmSubst R n F = f from
      this k f a hsym hpt
    intro k
    induction k using (lexFollows_wf n).induction with
    | h k ih =>
    intro f a hsym hpt
    let h := elemSymmMonomial a k
    let H := elemSymmMonomialPreimage a k
    have hH : elemSymmSubst R n H = h := elemSymmSubst_monomialPreimage a k
    have hsym_h : IsGarlingSymmetricPoly h := hH ▸ isGarlingSymmetricPoly_elemSymmSubst H
    have hpt_h : HasPrincipalTerm h a k := exercise_19_2_ii hsym hpt
    let f' := f - h
    have hsym_f' : IsGarlingSymmetricPoly f' := isGarlingSymmetricPoly_sub hsym hsym_h
    by_cases hf'0 : f' = 0
    · refine ⟨H, ?_⟩
      rw [hH]
      exact (sub_eq_zero.mp hf'0).symm
    · obtain ⟨a', k', hpt'⟩ := exists_principalTerm_of_ne_zero hf'0
      have hk'_lt : lexFollows k' k := by
        have hk'_ne : k' ≠ k := by
          intro hEq
          have hc : f'.coeff k' = 0 := by
            rw [hEq]; simp [f', hpt.2.1, hpt_h.2.1]
          exact hpt'.1 (hpt'.2.1.symm.trans hc)
        have hk'_supp : k' ∈ f.support ∨ k' ∈ h.support := by
          have hmem : k' ∈ (f - h).support := MvPolynomial.mem_support_iff.mpr (hpt'.2.1.symm ▸ hpt'.1)
          by_contra hneither
          push Not at hneither
          have h1 := MvPolynomial.notMem_support_iff.mp hneither.1
          have h2 := MvPolynomial.notMem_support_iff.mp hneither.2
          exact (MvPolynomial.mem_support_iff.mp hmem) (by simp [h1, h2])
        rcases hk'_supp with hmf | hmh
        · exact hpt.2.2 k' hmf hk'_ne
        · exact hpt_h.2.2 k' hmh hk'_ne
      obtain ⟨F', hF'⟩ := ih k' hk'_lt f' a' hsym_f' hpt'
      refine ⟨H + F', ?_⟩
      rw [map_add, hH, hF']
      simp [f']

/-- **Exercise 19.2(iv)** & **Theorem 19.4 (Uniqueness over any integral domain `R`)** (p. 150):
The substitution `F ↦ F(s₁, …, sₙ)` is injective on `R[x₁, …, xₙ]` over every integral domain `R`. -/
theorem elemSymmSubst_injective (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Function.Injective (elemSymmSubst R n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro G hG
  by_contra hG0
  let Φ : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun d => ∑ m : Fin n, d m • prefixIndicator m
  have hΦ_inj : Function.Injective Φ := sum_prefixIndicator_injective n
  have hne : (G.support.image Φ).Nonempty := (MvPolynomial.support_nonempty.mpr hG0).image Φ
  obtain ⟨kmax, hkmax_mem, hkmax⟩ := exists_max_lexFollows (G.support.image Φ) hne
  obtain ⟨d₀, hd₀_mem, hd₀_eq⟩ := Finset.mem_image.mp hkmax_mem
  have hG_expand : elemSymmSubst R n G =
      ∑ d ∈ G.support, MvPolynomial.C (G.coeff d) * ∏ m : Fin n, (elemSymmPoly R n m) ^ (d m) := by
    conv_lhs => rw [G.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.monomial_eq, map_mul, elemSymmSubst, MvPolynomial.aeval_C, map_finsuppProd]
    congr 1
    simp only [map_pow, MvPolynomial.aeval_X]
    exact Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _)
  have hcoeff_kmax : (elemSymmSubst R n G).coeff kmax = G.coeff d₀ := by
    rw [hG_expand, MvPolynomial.coeff_sum, Finset.sum_eq_single d₀]
    · have hpt := hasPrincipalTerm_C_mul (MvPolynomial.mem_support_iff.mp hd₀_mem)
        (hasPrincipalTerm_prod_elemSymmPoly (R := R) d₀)
      rw [mul_one] at hpt
      change HasPrincipalTerm _ _ (Φ d₀) at hpt
      rw [hd₀_eq] at hpt
      exact hpt.2.1
    · intro d hd hd_ne
      have hpt := hasPrincipalTerm_C_mul (MvPolynomial.mem_support_iff.mp hd)
        (hasPrincipalTerm_prod_elemSymmPoly (R := R) d)
      rw [mul_one] at hpt
      by_contra hnz
      have hmem : kmax ∈ (MvPolynomial.C (G.coeff d) * ∏ m : Fin n, (elemSymmPoly R n m) ^ (d m)).support :=
        MvPolynomial.mem_support_iff.mpr hnz
      have hΦ_ne : Φ d ≠ kmax := fun h => hd_ne (hΦ_inj (h.trans hd₀_eq.symm))
      have h1 : lexFollows (Φ d) kmax := hkmax (Φ d) (Finset.mem_image_of_mem Φ hd) hΦ_ne
      have h2 : lexFollows kmax (Φ d) := hpt.2.2 kmax hmem (Ne.symm hΦ_ne)
      exact lexFollows_irrefl kmax (lexFollows_trans h2 h1)
    · intro h; exact (h hd₀_mem).elim
  rw [hG, AddMonoidAlgebra.coeff_zero] at hcoeff_kmax
  exact (MvPolynomial.mem_support_iff.mp hd₀_mem) hcoeff_kmax.symm

/-- **Theorem 19.4 (Integral-domain form, covering both `K` and `ℤ`)** (§19.1, p. 150):
Over any integral domain `R`, every symmetric polynomial `f ∈ R[t₁, …, tₙ]` is uniquely of the form
`g(s₁, …, sₙ)` for `g ∈ R[x₁, …, xₙ]`. -/
theorem theorem_19_4_domain {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f : MvPolynomial (Fin n) R} (hsym : IsGarlingSymmetricPoly f) :
    ∃! g : MvPolynomial (Fin n) R, elemSymmSubst R n g = f := by
  obtain ⟨g, hg⟩ := exercise_19_2_iii_domain hsym
  exact ⟨g, hg, fun g' hg' => elemSymmSubst_injective R n (hg'.trans hg.symm)⟩

/-- **Theorem 19.4** (§19.1, printed p. 150 / PDF p. 158):
*"If `f` is a symmetric polynomial in `K[t₁, …, tₙ]`, there exists a unique `g` in `K[x₁, …, xₙ]`
such that `f(t₁, …, tₙ) = g(s₁, …, sₙ)`."*

Proved literally for all `n : ℕ` and all fields `K`, both directly in `MvPolynomial (Fin n) K` and
evaluated in any extension `E = K(t₁, …, tₙ)` with `t₁, …, tₙ` algebraically independent over `K`. -/
theorem theorem_19_4 {K : Type*} [Field K] {n : ℕ}
    {f : MvPolynomial (Fin n) K} (hsym : IsGarlingSymmetricPoly f) :
    (∃! g : MvPolynomial (Fin n) K, elemSymmSubst K n g = f) ∧
    ∀ {E : Type*} [Field E] [Algebra K E] {t : Fin n → E},
      IsGarlingAlgIndepTuple K t →
      ∃! g : MvPolynomial (Fin n) K,
        evalMvRingHom K t f = evalMvRingHom K (elemSymmVal K t) g := by
  have h1 := theorem_19_4_domain hsym
  refine ⟨h1, fun {E} _ _ {t} ht => ?_⟩
  rcases h1 with ⟨g, hg, huniq⟩
  have hcomp : ∀ q : MvPolynomial (Fin n) K,
      evalMvRingHom K (elemSymmVal K t) q = evalMvRingHom K t (elemSymmSubst K n q) := by
    intro q
    exact AlgHom.congr_fun
      (MvPolynomial.algHom_ext
        (f := MvPolynomial.aeval (elemSymmVal K t))
        (g := (MvPolynomial.aeval t).comp (elemSymmSubst K n))
        fun k => by simp [elemSymmSubst, elemSymmVal, evalMvRingHom]) q
  refine ⟨g, by dsimp only; rw [hcomp g, hg], fun g' hg' => huniq g' ?_⟩
  apply ht
  rw [← hcomp g', ← hg']

/-- **§19.1 Prose `ℤ`-Integrality Remark** (printed p. 150 / PDF p. 158):
*"Note also that if `f` is a symmetric polynomial in `ℤ[t₁, …, tₙ]` then `g ∈ ℤ[x₁, …, xₙ]`."* -/
theorem section_19_1_int_symmetric_remark {n : ℕ}
    {f : MvPolynomial (Fin n) ℤ} (hsym : IsGarlingSymmetricPoly f) :
    (∃! g : MvPolynomial (Fin n) ℤ, elemSymmSubst ℤ n g = f) ∧
    ∀ (K : Type*) [Field K],
      ∀ gK : MvPolynomial (Fin n) K,
        elemSymmSubst K n gK = MvPolynomial.map (Int.castRingHom K) f →
        ∃ gZ : MvPolynomial (Fin n) ℤ,
          elemSymmSubst ℤ n gZ = f ∧ MvPolynomial.map (Int.castRingHom K) gZ = gK := by
  have hZ := theorem_19_4_domain hsym
  refine ⟨hZ, fun K _ gK hgK => ?_⟩
  rcases hZ with ⟨gZ, hgZ, _⟩
  refine ⟨gZ, hgZ, ?_⟩
  apply elemSymmSubst_injective K n
  rw [hgK]
  have hmap : ∀ q : MvPolynomial (Fin n) ℤ,
      elemSymmSubst K n (MvPolynomial.map (Int.castRingHom K) q) =
        MvPolynomial.map (Int.castRingHom K) (elemSymmSubst ℤ n q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp [elemSymmSubst]
    | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
    | mul_X u k hu =>
      rw [map_mul, map_mul, map_mul, map_mul, hu]
      congr 1
      simp only [MvPolynomial.map_X, elemSymmSubst, MvPolynomial.aeval_X]
      change MvPolynomial.esymm (Fin n) K (k.1 + 1) =
        MvPolynomial.map (Int.castRingHom K) (MvPolynomial.esymm (Fin n) ℤ (k.1 + 1))
      exact (MvPolynomial.map_esymm (Fin n) ℤ (k.1 + 1) (Int.castRingHom K)).symm
  rw [hmap gZ, hgZ]

/-- **Corollary** [to **Theorem 19.4**] (§19.1, printed p. 150 / PDF p. 158):
*"Suppose that `h = xⁿ - a₁ x^{n-1} + ⋯ + (-1)ⁿ aₙ` is a monic polynomial in `K[x]`, with roots
`α₁, …, αₙ` in some splitting field extension. If `f` is a symmetric polynomial in `t₁, …, tₙ` then
`f(α₁, …, αₙ) = g(a₁, …, aₙ)` (where `g` is the polynomial of the theorem)."*

Proved literally for all `n : ℕ`, all fields `K`, and all extensions `L : K` in which
`h = ∏_{i : Fin n} (x - α_i)` (roots counted with multiplicity, matching §11.2 / §14.2). -/
theorem corollary_to_theorem_19_4 {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {a : Fin n → K} {α : Fin n → L}
    (hroots : (garlingGenericPoly a).map (algebraMap K L) = generalRootsPoly α)
    {f g : MvPolynomial (Fin n) K} (hg : elemSymmSubst K n g = f) :
    evalMvRingHom K α f = algebraMap K L (evalMvRingHom K a g) := by
  have hs_eq : ∀ k : Fin n, evalMvRingHom K α (elemSymmPoly K n k) = algebraMap K L (a k) := by
    intro k
    have hcoeff := congrArg (fun p : L[X] => p.coeff (n - 1 - k.1)) hroots
    rw [garlingGenericPoly_map, generalRootsPoly_eq_garlingGenericPoly_eval (K := K) α,
      garlingGenericPoly_coeff, garlingGenericPoly_coeff] at hcoeff
    have hunit : (-1 : L) ^ (k.1 + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (mul_left_cancel₀ hunit hcoeff).symm
  have hcomp :
      (MvPolynomial.aeval α).comp (elemSymmSubst K n) =
        (Algebra.ofId K L).comp (MvPolynomial.aeval a) := by
    apply MvPolynomial.algHom_ext
    intro k
    simpa [elemSymmSubst, evalMvRingHom] using hs_eq k
  rw [← hg]
  exact AlgHom.congr_fun hcomp g

/-- **Exercise 19.2** (§19.1, printed p. 150 / PDF p. 158):
Combines all four printed parts `(i)`–`(iv)` over any field `K` and any `n : ℕ`. -/
theorem exercise_19_2 {K : Type*} [Field K] {n : ℕ} :
    (∀ {f : MvPolynomial (Fin n) K} {a : K} {k : Fin n →₀ ℕ},
      IsGarlingSymmetricPoly f → HasPrincipalTerm f a k →
      ∀ i j : Fin n, i ≤ j → k j ≤ k i) ∧
    (∀ {f : MvPolynomial (Fin n) K} {a : K} {k : Fin n →₀ ℕ},
      IsGarlingSymmetricPoly f → HasPrincipalTerm f a k →
      HasPrincipalTerm (elemSymmMonomial a k) a k) ∧
    (∀ {f : MvPolynomial (Fin n) K},
      IsGarlingSymmetricPoly f →
      ∃ F : MvPolynomial (Fin n) K, elemSymmSubst K n F = f) ∧
    (∀ {f : MvPolynomial (Fin n) K},
      IsGarlingSymmetricPoly f →
      ∃! F : MvPolynomial (Fin n) K, elemSymmSubst K n F = f) :=
  ⟨fun hsym hpt => exercise_19_2_i hsym hpt,
   fun hsym hpt => exercise_19_2_ii hsym hpt,
   fun hsym => exercise_19_2_iii_domain hsym,
   fun hsym => theorem_19_4_domain hsym⟩

/-! ## §19.2 The normal basis theorem (printed pp. 150–152 / PDF pp. 158–160) -/

/-- **Theorem 19.5** (§19.2, printed p. 151 / PDF p. 159):
*"Suppose that `R` is an infinite subset of an integral domain `S` and that `f` is a non-zero
element of `S[x₁, …, xₙ]`. Then there exists `(r₁, …, rₙ)` in `Rⁿ` such that `f(r₁, …, rₙ) ≠ 0`."*

Proved literally for all `n : ℕ` (including `n = 0`) by induction on `n`, following Garling p. 151. -/
theorem theorem_19_5 {S : Type*} [CommRing S] [IsDomain S] {R : Set S} (hR : R.Infinite)
    {n : ℕ} {f : MvPolynomial (Fin n) S} (hf : f ≠ 0) :
    ∃ r : Fin n → S, (∀ i : Fin n, r i ∈ R) ∧ MvPolynomial.eval r f ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    have hfC : f = MvPolynomial.C (f.coeff 0) := by
      ext d
      have hd : d = 0 := Finsupp.ext fun i => Fin.elim0 i
      subst hd
      simp
    have hc0 : f.coeff 0 ≠ 0 := fun h0 => hf (by rw [hfC, h0, map_zero])
    rw [hfC, MvPolynomial.eval_C]
    exact hc0
  | succ m ih =>
    let p : (MvPolynomial (Fin m) S)[X] := MvPolynomial.finSuccEquiv S m f
    have hp0 : p ≠ 0 := fun h0 => hf ((MvPolynomial.finSuccEquiv S m).injective (h0.trans (map_zero _).symm))
    have hex_j : ∃ j : ℕ, p.coeff j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hp0 (Polynomial.ext fun j => by rw [hall j, Polynomial.coeff_zero])
    obtain ⟨j, hj⟩ := hex_j
    obtain ⟨r', hr'_mem, hr'_eval⟩ := ih hj
    let q : S[X] := p.map (MvPolynomial.eval r')
    have hq0 : q ≠ 0 := by
      intro h0
      have hc := congrArg (fun g : S[X] => g.coeff j) h0
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
      exact hr'_eval hc
    have hroots_fin : ({x : S | q.eval x = 0} : Set S).Finite := by
      classical
      refine (q.roots.toFinset.finite_toSet).subset fun x hx => ?_
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq0]
      exact hx
    obtain ⟨r0, hr0_R, hr0_nroot⟩ := (hR.sdiff hroots_fin).nonempty
    have hq_eval : q.eval r0 ≠ 0 := hr0_nroot
    refine ⟨Fin.cons r0 r', fun i => Fin.cases hr0_R hr'_mem i, ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval' r' r0 f]
    exact hq_eval

/-- Inline normal-basis generator predicate (§19.2, pp. 151–152): `l ∈ L` generates a *normal basis*
of `L : K` if the Galois orbit `(σ(l))_{σ ∈ Γ(L:K)}` is a `K`-basis of `L`. -/
def IsGarlingNormalBasisGenerator (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (l : L) : Prop :=
  LinearIndependent K (fun σ : GarlingGaloisGroup K L => σ l) ∧
  Submodule.span K (Set.range (fun σ : GarlingGaloisGroup K L => σ l)) = ⊤

/-- Subset form of *normal basis* (§19.2, `Exercise 19.3`, p. 152): `B ⊆ L` is a *normal basis* for
`L : K` if `B` is a `K`-basis of `L` (`IsBasis K L B`) that is the Galois orbit `{σ(l) | σ ∈ Γ(L:K)}`
of some element `l ∈ L`. -/
def IsGarlingNormalBasisSet (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (B : Set L) : Prop :=
  IsBasis K L B ∧ ∃ l : L, B = Set.range (fun σ : GarlingGaloisGroup K L => σ l)

/-- **Theorem 19.6 (The normal basis theorem)** (§19.2, printed p. 151 / PDF p. 159; proof pp. 151–152):
*"Suppose that `K` is an infinite field, and that `L : K` is a Galois extension, with Galois group
`G = {σ₁, …, σₙ}`. Then there exists `l` in `L` such that `(σ₁(l), …, σₙ(l))` is a basis for `L`
over `K`."*

Proved following Garling's pp. 151–152 proof using `Theorem 19.5` and `Chapter11.exercise_11_3`
(itself proved from `Theorem 11.2`). -/
theorem theorem_19_6 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Infinite K] (hgal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) :
    ∃ l : L,
      (∃ B : Module.Basis (Fin n) K L, ∀ j : Fin n, B j = σ j l) ∧
      IsBasis K L (Set.range (fun j : Fin n => σ j l)) ∧
      IsGarlingNormalBasisGenerator K l ∧
      IsGarlingNormalBasisSet K (Set.range (fun τ : GarlingGaloisGroup K L => τ l)) := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
  have hdeg : Module.finrank K L = n := by
    have hcard := (theorem_10_4_algEquiv hgal.1).1 hgal
    rw [← hcard, ← Nat.card_congr σ, Nat.card_fin]
  let b : Module.Basis (Fin n) K L := (Module.finBasis K L).reindex (finCongr hdeg)
  -- Group multiplication table `p i j = σ⁻¹(σ i * σ j)`:
  let p : Fin n → Fin n → Fin n := fun i j => σ.symm (σ i * σ j)
  let M_X : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) L) :=
    Matrix.of fun i j => MvPolynomial.X (p i j)
  let f : MvPolynomial (Fin n) L := M_X.det
  -- Step 1: `f ≠ 0` (evaluate at `x_{σ⁻¹(1)} = 1`, all other variables `0`):
  have hf_ne0 : f ≠ 0 := by
    let e1 : Fin n → L := fun k => if k = σ.symm 1 then 1 else 0
    have heval_f : MvPolynomial.eval e1 f ≠ 0 := by
      rw [show f = M_X.det from rfl, RingHom.map_det]
      let τ : Equiv.Perm (Fin n) :=
        { toFun := fun i => σ.symm (σ i)⁻¹
          invFun := fun i => σ.symm (σ i)⁻¹
          left_inv := fun i => by simp
          right_inv := fun i => by simp }
      have hmat : (MvPolynomial.eval e1).mapMatrix M_X =
          Matrix.of (fun i j : Fin n => if j = τ i then (1 : L) else 0) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M_X, Matrix.of_apply,
          MvPolynomial.eval_X, e1]
        have hiff : p i j = σ.symm 1 ↔ j = τ i := by
          simp only [p, τ, Equiv.apply_eq_iff_eq]
          constructor
          · intro h
            have h' : σ j = (σ i)⁻¹ := eq_inv_of_mul_eq_one_right h
            exact (Equiv.eq_symm_apply σ).mpr h'
          · intro h
            rw [h]
            simp only [Equiv.coe_fn_mk, Equiv.apply_symm_apply, mul_inv_cancel]
        simp [hiff]
      rw [hmat, Matrix.det_apply]
      have hτ_inv : ∀ i : Fin n, τ (τ i) = i := fun i => by simp [τ]
      rw [Finset.sum_eq_single τ]
      · have hprod1 : (∏ i : Fin n, (Matrix.of (fun r c : Fin n => if c = τ r then (1 : L) else 0)) (τ i) i) = 1 :=
          Finset.prod_eq_one fun i _ => by simp [hτ_inv]
        rw [hprod1]
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]
      · intro π _ hπτ
        have hex : ∃ i : Fin n, π i ≠ τ i := by
          by_contra hall; push Not at hall; exact hπτ (Equiv.ext hall)
        obtain ⟨i, hi⟩ := hex
        have hne : i ≠ τ (π i) := fun heq => hi (by simpa [hτ_inv] using congrArg τ heq.symm)
        have hprod0 : (∏ k : Fin n, (Matrix.of (fun r c : Fin n => if c = τ r then (1 : L) else 0)) (π k) k) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hne])
        rw [hprod0, smul_zero]
      · intro h; exact (h (Finset.mem_univ τ)).elim
    intro h0
    rw [h0, map_zero] at heval_f
    exact heval_f rfl
  -- Step 2: Change-of-variables matrix `A i j = σ i (b j)` is invertible by `Exercise 11.3` (`Theorem 11.2`):
  let A : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => σ i (b j)
  have hAdet : A.det ≠ 0 := (exercise_11_3 hgal σ b).1.mp ⟨b, fun _ => rfl⟩
  let Ainv : Matrix (Fin n) (Fin n) L := A⁻¹
  have hAAinv : A * Ainv = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hAdet)
  have hAinvA : Ainv * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hAdet)
  -- Linear substitution `Φ(X i) = ∑ k, A i k * X k` has left inverse `Ψ(X i) = ∑ k, Ainv i k * X k`:
  let Φ : MvPolynomial (Fin n) L →ₐ[L] MvPolynomial (Fin n) L :=
    MvPolynomial.aeval fun i => ∑ k : Fin n, MvPolynomial.C (A i k) * MvPolynomial.X k
  let Ψ : MvPolynomial (Fin n) L →ₐ[L] MvPolynomial (Fin n) L :=
    MvPolynomial.aeval fun i => ∑ k : Fin n, MvPolynomial.C (Ainv i k) * MvPolynomial.X k
  have hΨΦ : Ψ.comp Φ = AlgHom.id L (MvPolynomial (Fin n) L) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Φ, Ψ, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    have hswap :
        (∑ k : Fin n, MvPolynomial.C (A i k) * ∑ j : Fin n, MvPolynomial.C (Ainv k j) * MvPolynomial.X j) =
        ∑ j : Fin n, MvPolynomial.C ((A * Ainv) i j) * MvPolynomial.X j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, mul_assoc]
    rw [hswap, hAAinv]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hΦ_inj : Function.Injective Φ :=
    Function.LeftInverse.injective (g := Ψ) fun q => by
      simpa [AlgHom.comp_apply] using AlgHom.congr_fun hΨΦ q
  let g : MvPolynomial (Fin n) L := Φ f
  have hg_ne0 : g ≠ 0 := fun h0 => hf_ne0 (hΦ_inj (h0.trans (map_zero Φ).symm))
  -- Step 3: Apply `Theorem 19.5` on the infinite subset `R = range (algebraMap K L) ⊆ L`:
  let R : Set L := Set.range (algebraMap K L)
  have hR_inf : R.Infinite := Set.infinite_range_of_injective (algebraMap K L).injective
  obtain ⟨r, hr_mem, hr_eval⟩ := theorem_19_5 hR_inf hg_ne0
  choose c hc using hr_mem
  -- Step 4: Set `l = ∑ k, c k • b k` and evaluate `det(σ_i(σ_j(l)))`:
  let l : L := ∑ k : Fin n, c k • b k
  have hσl : ∀ i : Fin n, σ i l = A.mulVec r i := by
    intro i
    dsimp only [l]
    rw [map_sum]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, hc k, mul_comm]
  have hΦ_eval : ∀ u : MvPolynomial (Fin n) L,
      MvPolynomial.eval r (Φ u) = MvPolynomial.eval (A.mulVec r) u := by
    intro u
    exact AlgHom.congr_fun
      (MvPolynomial.algHom_ext
        (f := (MvPolynomial.aeval r).comp Φ)
        (g := MvPolynomial.aeval (A.mulVec r))
        fun i => by simp [Φ, Matrix.mulVec, dotProduct]) u
  have hdet_l : (Matrix.of (fun i j : Fin n => σ i (σ j l))).det ≠ 0 := by
    have hmat_l : Matrix.of (fun i j : Fin n => σ i (σ j l)) =
        (MvPolynomial.eval (A.mulVec r)).mapMatrix M_X := by
      ext i j
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, M_X,
        MvPolynomial.eval_X]
      have h1 : σ i (σ j l) = (σ i * σ j) l := rfl
      have h2 : σ (p i j) = σ i * σ j := Equiv.apply_symm_apply σ (σ i * σ j)
      rw [h1, ← h2, hσl (p i j)]
    rw [hmat_l, ← RingHom.map_det, ← show f = M_X.det from rfl, ← hΦ_eval f]
    exact hr_eval
  obtain ⟨hB_mod, hB_set⟩ := exercise_11_3 hgal σ (fun j => σ j l)
  have hmod := hB_mod.mpr hdet_l
  have hset := hB_set.mpr hdet_l
  obtain ⟨B, hB⟩ := hmod
  have hrange_eq : Set.range (fun j : Fin n => σ j l) =
      Set.range (fun τ : GarlingGaloisGroup K L => τ l) := by
    ext x
    simp only [Set.mem_range]
    exact ⟨fun ⟨j, hj⟩ => ⟨σ j, hj⟩, fun ⟨τ, hτ⟩ => ⟨σ.symm τ, by simpa using hτ⟩⟩
  have hgen : IsGarlingNormalBasisGenerator K l := by
    refine ⟨?_, ?_⟩
    · have hli_j : LinearIndependent K (fun j : Fin n => σ j l) := by
        have heq : (fun j : Fin n => σ j l) = (B : Fin n → L) := funext fun j => (hB j).symm
        rw [heq]; exact B.linearIndependent
      have hcomp : (fun τ : GarlingGaloisGroup K L => τ l) = (fun j : Fin n => σ j l) ∘ σ.symm := by
        funext τ; simp
      rw [hcomp]
      exact hli_j.comp σ.symm σ.symm.injective
    · rw [← hrange_eq]
      exact hset.2
  refine ⟨l, ⟨B, hB⟩, hset, hgen, ?_, l, rfl⟩
  rwa [← hrange_eq]

/-- Helper for `Exercise 19.3`: for a squarefree `n ≥ 1` and a primitive `n`-th root of unity `ε`
in a field `L : ℚ`, `Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n} = ⊤` inside `ℚ(ε)`. -/
private theorem span_primitiveRoots_eq_top_of_squarefree {L : Type u} [Field L] [Algebra ℚ L] :
    ∀ n : ℕ, 1 ≤ n → Squarefree n →
      ∀ {ε : L},
        IsPrimitiveRoot ε n →
        ∀ y ∈ IntermediateField.adjoin ℚ ({ε} : Set L),
          y ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n} := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn1 hsq ε hε y hy
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      have hε1 : ε = 1 := by simpa using hε.pow_eq_one
      have hbot : IntermediateField.adjoin ℚ ({ε} : Set L) = ⊥ := by
        rw [hε1, eq_bot_iff, IntermediateField.adjoin_le_iff]
        rintro _ rfl; exact (⊥ : IntermediateField ℚ L).one_mem
      rw [hbot] at hy
      rcases IntermediateField.mem_bot.mp hy with ⟨q, rfl⟩
      rw [show algebraMap ℚ L q = q • (1 : L) by simp [Algebra.smul_def]]
      exact Submodule.smul_mem _ q (Submodule.subset_span (IsPrimitiveRoot.one))
    · let p := n.minFac
      have hp : Nat.Prime p := Nat.minFac_prime hn_eq1
      have hpn : p ∣ n := Nat.minFac_dvd n
      rcases hpn with ⟨m, hnm⟩
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hnm; omega
      have hpm : ¬ (p ∣ m) := by
        intro hdiv
        have hp2 : p * p ∣ n := by
          rcases hdiv with ⟨k, rfl⟩
          exact ⟨k, by rw [hnm]; ring⟩
        exact hp.not_isUnit (hsq p hp2)
      have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
      have hsq_m : Squarefree m := hsq.squarefree_of_dvd ⟨p, by rw [hnm, mul_comm]⟩
      have hm_lt : m < n := by
        have hp2 : 2 ≤ p := hp.two_le
        nlinarith
      let α : L := ε ^ m
      let β : L := ε ^ p
      have hα : IsPrimitiveRoot α p := hε.pow (by omega) (by rw [hnm, mul_comm])
      have hβ : IsPrimitiveRoot β m := hε.pow (by omega) hnm
      -- 1. `M := ℚ(β)` is spanned over `ℚ` by primitive `m`-th roots of unity (by IH in the same `L`):
      have hspan_M : ∀ z ∈ IntermediateField.adjoin ℚ ({β} : Set L),
          z ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ m} :=
        ih m hm_lt hm1 hsq_m hβ
      -- 2. Every power `α ^ j` lies in `Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ p}`:
      have hα_geom : ∑ k ∈ Finset.range p, α ^ k = 0 := by
        have h1 : (α - 1) * ∑ k ∈ Finset.range p, α ^ k = α ^ p - 1 := by
          rw [mul_comm]; exact geom_sum_mul α p
        rw [hα.pow_eq_one, sub_self] at h1
        exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (hα.ne_one hp.one_lt))
      have h1_in_Pp : (1 : L) ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ p} := by
        have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
        have hsum0 : (∑ k ∈ Finset.range (p - 1), α ^ (k + 1)) + 1 = 0 := by
          have hsplit := Finset.sum_range_succ' (fun k => α ^ k) (p - 1)
          rw [hp1] at hsplit
          simpa [pow_zero] using hsplit.symm.trans hα_geom
        have h1eq : (1 : L) = - ∑ k ∈ Finset.range (p - 1), α ^ (k + 1) :=
          eq_neg_of_add_eq_zero_right hsum0
        rw [h1eq]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => Submodule.subset_span ?_)
        have hklt : k + 1 < p := by
          have := Finset.mem_range.mp hk; omega
        have hcopk : Nat.Coprime (k + 1) p :=
          (hp.coprime_iff_not_dvd.mpr fun hdiv => by
            have hle := Nat.le_of_dvd (by omega) hdiv; omega).symm
        exact hα.pow_of_coprime (k + 1) hcopk
      have hpow_α : ∀ k : ℕ, α ^ k ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ p} := by
        intro k
        have hmod : α ^ k = α ^ (k % p) := by
          conv_lhs => rw [← Nat.div_add_mod k p]
          rw [pow_add, pow_mul, hα.pow_eq_one, one_pow, one_mul]
        rw [hmod]
        by_cases hr0 : k % p = 0
        · rw [hr0, pow_zero]; exact h1_in_Pp
        · apply Submodule.subset_span
          have hlt : k % p < p := Nat.mod_lt k hp.pos
          have hcopk : Nat.Coprime (k % p) p :=
            (hp.coprime_iff_not_dvd.mpr fun hdiv => by
              have hle := Nat.le_of_dvd (by omega) hdiv; omega).symm
          exact hα.pow_of_coprime (k % p) hcopk
      -- 3. Any product of an element of `span P_p` and an element of `span P_m` lies in `span P_n`:
      have hprim_mul : ∀ {u v : L}, IsPrimitiveRoot u p → IsPrimitiveRoot v m →
          IsPrimitiveRoot (u * v) (p * m) := by
        intro u v hu hv
        refine ⟨?_, ?_⟩
        · rw [mul_pow, pow_mul, hu.pow_eq_one, one_pow, one_mul, mul_comm p m, pow_mul, hv.pow_eq_one, one_pow]
        · intro d hd
          have hd_p : p ∣ d := by
            have h1 : u ^ (d * m) = 1 :=
              calc u ^ (d * m) = u ^ (d * m) * (v ^ m) ^ d := by rw [hv.pow_eq_one, one_pow, mul_one]
                _ = u ^ (d * m) * v ^ (d * m) := by rw [← pow_mul, mul_comm m d]
                _ = ((u * v) ^ d) ^ m := by rw [← mul_pow, pow_mul]
                _ = 1 := by rw [hd, one_pow]
            exact hcop.dvd_of_dvd_mul_right (hu.dvd_of_pow_eq_one _ h1)
          have hd_m : m ∣ d := by
            have h1 : v ^ (d * p) = 1 :=
              calc v ^ (d * p) = (u ^ p) ^ d * v ^ (d * p) := by rw [hu.pow_eq_one, one_pow, one_mul]
                _ = u ^ (d * p) * v ^ (d * p) := by rw [← pow_mul, mul_comm p d]
                _ = ((u * v) ^ d) ^ p := by rw [← mul_pow, pow_mul]
                _ = 1 := by rw [hd, one_pow]
            exact hcop.symm.dvd_of_dvd_mul_right (hv.dvd_of_pow_eq_one _ h1)
          exact hcop.mul_dvd_of_dvd_of_dvd hd_p hd_m
      have hprod_span : ∀ x ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ p},
          ∀ z ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ m},
            x * z ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n} := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem u hu =>
          intro z hz
          induction hz using Submodule.span_induction with
          | mem v hv =>
            apply Submodule.subset_span
            rw [hnm]
            exact hprim_mul hu hv
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add v₁ v₂ _ _ hv₁ hv₂ => rw [mul_add]; exact Submodule.add_mem _ hv₁ hv₂
          | smul q v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ q hv
        | zero => intro z _; rw [zero_mul]; exact Submodule.zero_mem _
        | add u₁ u₂ _ _ hu₁ hu₂ => intro z hz; rw [add_mul]; exact Submodule.add_mem _ (hu₁ z hz) (hu₂ z hz)
        | smul q u _ hu => intro z hz; rw [smul_mul_assoc]; exact Submodule.smul_mem _ q (hu z hz)
      -- 4. Every power `ε ^ r` (`r : ℕ`) equals `α ^ a * β ^ b` for some `a, b : ℕ` (since `Coprime p m`),
      --    hence lies in `Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n}`!
      have hpow_ε : ∀ r : ℕ, ε ^ r ∈ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n} := by
        intro r
        have hbez : ∃ a b : ℕ, ε ^ r = α ^ a * β ^ b := by
          let u : ℤ := Nat.gcdA p m
          let v : ℤ := Nat.gcdB p m
          have huv : (p : ℤ) * u + (m : ℤ) * v = 1 := by
            have h := Nat.gcd_eq_gcd_ab p m
            rw [hcop.gcd_eq_one, Nat.cast_one] at h
            exact h.symm
          have ha_ex : ∃ a : ℕ, (a : ℤ) ≡ (r : ℤ) * v [ZMOD p] :=
            ⟨(((r : ℤ) * v) % (p : ℤ)).toNat, by
              have hp_pos : (0 : ℤ) < p := Nat.cast_pos.mpr hp.pos
              have hnn : 0 ≤ ((r : ℤ) * v) % (p : ℤ) := Int.emod_nonneg _ (ne_of_gt hp_pos)
              rw [Int.toNat_of_nonneg hnn]
              exact Int.mod_modEq _ _⟩
          have hb_ex : ∃ b : ℕ, (b : ℤ) ≡ (r : ℤ) * u [ZMOD m] :=
            ⟨(((r : ℤ) * u) % (m : ℤ)).toNat, by
              have hm_pos : (0 : ℤ) < m := Nat.cast_pos.mpr (by omega)
              have hnn : 0 ≤ ((r : ℤ) * u) % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hm_pos)
              rw [Int.toNat_of_nonneg hnn]
              exact Int.mod_modEq _ _⟩
          obtain ⟨a, ha⟩ := ha_ex
          obtain ⟨b, hb⟩ := hb_ex
          refine ⟨a, b, ?_⟩
          have hcong_p : ((a * m + b * p : ℕ) : ℤ) ≡ (r : ℤ) [ZMOD p] := by
            have h1 : ((a * m + b * p : ℕ) : ℤ) = (a : ℤ) * m + (b : ℤ) * p := by push_cast; ring
            rw [h1]
            have h2 : (a : ℤ) * m + (b : ℤ) * p ≡ ((r : ℤ) * v) * m + 0 [ZMOD p] := by
              refine Int.ModEq.add (ha.mul_right m) ?_
              exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_left (p : ℤ) (b : ℤ))
            have h3 : ((r : ℤ) * v) * m + 0 ≡ (r : ℤ) [ZMOD p] := by
              rw [add_zero]
              have hdiff : ((r : ℤ) * v) * m - r = -(r * u) * p := by linear_combination r * huv
              exact Int.modEq_iff_dvd.mpr ⟨r * u, by linarith⟩
            exact h2.trans h3
          have hcong_m : ((a * m + b * p : ℕ) : ℤ) ≡ (r : ℤ) [ZMOD m] := by
            have h1 : ((a * m + b * p : ℕ) : ℤ) = (a : ℤ) * m + (b : ℤ) * p := by push_cast; ring
            rw [h1]
            have h2 : (a : ℤ) * m + (b : ℤ) * p ≡ 0 + ((r : ℤ) * u) * p [ZMOD m] := by
              refine Int.ModEq.add (Int.modEq_zero_iff_dvd.mpr (dvd_mul_left (m : ℤ) (a : ℤ)))
                (hb.mul_right p)
            have h3 : 0 + ((r : ℤ) * u) * p ≡ (r : ℤ) [ZMOD m] := by
              rw [zero_add]
              have hdiff : ((r : ℤ) * u) * p - r = -(r * v) * m := by linear_combination r * huv
              exact Int.modEq_iff_dvd.mpr ⟨r * v, by linarith⟩
            exact h2.trans h3
          have hdiv_p : (p : ℤ) ∣ ((a * m + b * p : ℕ) : ℤ) - (r : ℤ) :=
            Int.modEq_iff_dvd.mp hcong_p.symm
          have hdiv_m : (m : ℤ) ∣ ((a * m + b * p : ℕ) : ℤ) - (r : ℤ) :=
            Int.modEq_iff_dvd.mp hcong_m.symm
          have hdiv_n : (n : ℤ) ∣ ((a * m + b * p : ℕ) : ℤ) - (r : ℤ) := by
            rw [hnm, Nat.cast_mul]
            exact (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hcop.gcd_eq_one)).mul_dvd hdiv_p hdiv_m
          have hmod_n : (a * m + b * p) ≡ r [MOD n] :=
            Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hdiv_n).symm
          have hpow_eq : ε ^ (a * m + b * p) = ε ^ r := by
            have h1 : ε ^ ((a * m + b * p) % n) = ε ^ (r % n) := congrArg (ε ^ ·) hmod_n
            have hred : ∀ t : ℕ, ε ^ (t % n) = ε ^ t := fun t => by
              conv_rhs => rw [← Nat.div_add_mod t n]
              rw [pow_add, pow_mul, hε.pow_eq_one, one_pow, one_mul]
            rw [hred, hred] at h1
            exact h1
          calc ε ^ r = ε ^ (a * m + b * p) := hpow_eq.symm
            _ = (ε ^ m) ^ a * (ε ^ p) ^ b := by rw [pow_add, mul_comm a m, pow_mul, mul_comm b p, pow_mul]
            _ = α ^ a * β ^ b := rfl
        obtain ⟨a, b, hab⟩ := hbez
        rw [hab]
        have hβb_M : β ^ b ∈ IntermediateField.adjoin ℚ ({β} : Set L) :=
          pow_mem (IntermediateField.mem_adjoin_simple_self ℚ β) b
        exact hprod_span (α ^ a) (hpow_α a) (β ^ b) (hspan_M (β ^ b) hβb_M)
      -- 5. Since `ε` is algebraic over `ℚ`, `ℚ(ε) = ℚ[ε]` is spanned by `{ε ^ r | r : ℕ}`:
      have halg : IsAlgebraic ℚ ε :=
        ⟨Polynomial.X ^ n - 1, (Polynomial.monic_X_pow_sub_C 1 (by omega)).ne_zero, by
          simp [hε.pow_eq_one]⟩
      have hy_alg : y ∈ Algebra.adjoin ℚ ({ε} : Set L) := by
        have hsub : (IntermediateField.adjoin ℚ ({ε} : Set L)).toSubalgebra =
            Algebra.adjoin ℚ ({ε} : Set L) :=
          IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun z hz => by
            rw [Set.mem_singleton_iff.mp hz]; exact halg
        rw [← hsub]; exact hy
      let V : Submodule ℚ L := Submodule.span ℚ (Set.range fun r : ℕ => ε ^ r)
      have hV_le : V ≤ Submodule.span ℚ {ζ : L | IsPrimitiveRoot ζ n} :=
        Submodule.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact hpow_ε r)
      have hV_mul : ∀ a ∈ V, ∀ b ∈ V, a * b ∈ V := by
        intro a ha
        induction ha using Submodule.span_induction with
        | mem u hu =>
          rcases hu with ⟨r₁, rfl⟩
          intro b hb
          induction hb using Submodule.span_induction with
          | mem v hv =>
            rcases hv with ⟨r₂, rfl⟩
            rw [← pow_add]
            exact Submodule.subset_span ⟨r₁ + r₂, rfl⟩
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add v₁ v₂ _ _ hv₁ hv₂ => rw [mul_add]; exact Submodule.add_mem _ hv₁ hv₂
          | smul q v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ q hv
        | zero => intro b _; rw [zero_mul]; exact Submodule.zero_mem _
        | add u₁ u₂ _ _ hu₁ hu₂ => intro b hb; rw [add_mul]; exact Submodule.add_mem _ (hu₁ b hb) (hu₂ b hb)
        | smul q u _ hu => intro b hb; rw [smul_mul_assoc]; exact Submodule.smul_mem _ q (hu b hb)
      have hy_V : y ∈ V := by
        clear hy
        induction hy_alg using Algebra.adjoin_induction with
        | mem x hx =>
          rw [Set.mem_singleton_iff.mp hx]
          exact Submodule.subset_span ⟨1, pow_one ε⟩
        | algebraMap q =>
          rw [show algebraMap ℚ L q = q • (1 : L) by simp [Algebra.smul_def]]
          exact Submodule.smul_mem _ q (Submodule.subset_span ⟨0, pow_zero ε⟩)
        | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
        | mul a b _ _ ha hb => exact hV_mul a ha b hb
      exact hV_le hy_V

/-- **Exercise 19.3** (§19.2, printed p. 152 / PDF p. 160):
*"Show that the primitive `n`th roots of unity over `ℚ` form a normal basis for the splitting field
of `xⁿ - 1` over `ℚ` if and only if `n` has no repeated prime factors."*

Proved **literally for all `n : ℕ`** (including `n = 0`, where `{ε | IsGarlingPrimitiveRoot 0 ε} = ∅`
is not a basis and `Squarefree 0` is `False`, and `n = 1`, where `{1}` is a normal basis of `ℚ:ℚ`
and `Squarefree 1` is `True`), together with the `1 ≤ n` Mathlib `IsPrimitiveRoot` companion! -/
theorem exercise_19_3 {L : Type u} [Field L] [Algebra ℚ L] {n : ℕ}
    (hsf : IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ n - 1)) :
    (IsGarlingNormalBasisSet ℚ {ε : L | Garling.Chapter15.IsGarlingPrimitiveRoot n ε} ↔
      Squarefree n) ∧
    (1 ≤ n →
      (IsGarlingNormalBasisSet ℚ {ε : L | IsPrimitiveRoot ε n} ↔ Squarefree n)) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨?_, fun h => by omega⟩
    have hemp : {ε : L | Garling.Chapter15.IsGarlingPrimitiveRoot 0 ε} = ∅ := by
      ext ε; simp [Garling.Chapter15.IsGarlingPrimitiveRoot]
    rw [hemp]
    refine ⟨fun h => ?_, fun h => absurd h not_squarefree_zero⟩
    have h1 : (1 : L) ∈ (⊤ : Submodule ℚ L) := Submodule.mem_top
    rw [← h.1.2, Submodule.span_empty, Submodule.mem_bot] at h1
    exact (one_ne_zero h1).elim
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have _ : NeZero n := ⟨hn0⟩
    have hset_eq : {ε : L | Garling.Chapter15.IsGarlingPrimitiveRoot n ε} =
        {ε : L | IsPrimitiveRoot ε n} := by
      ext ε
      exact Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hn1 ε
    suffices hmain : IsGarlingNormalBasisSet ℚ {ε : L | IsPrimitiveRoot ε n} ↔ Squarefree n by
      exact ⟨by rwa [hset_eq], fun _ => hmain⟩
    have hcharQ : ¬ (ringChar ℚ ∣ n) := by
      rw [ringChar.eq_zero, zero_dvd_iff]; omega
    obtain ⟨ε₀, hε₀_gar⟩ := Garling.Chapter15.exists_isGarlingPrimitiveRoot_of_splittingField hcharQ hsf
    have hε₀ : IsPrimitiveRoot ε₀ n :=
      (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hn1 ε₀).mp hε₀_gar
    obtain ⟨htop, _, _⟩ :=
      Garling.Chapter15.section_15_1_simple_extension_of_prim_root hcharQ hsf hε₀_gar
    have hsf_cyc : IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic n ℚ) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharQ).1.mpr hsf
    have hirr_cyc : Irreducible (Polynomial.cyclotomic n ℚ) :=
      (Garling.Chapter15.theorem_15_3 hn1).1
    obtain ⟨_, _, _, _, hirr_surj⟩ := Garling.Chapter15.theorem_15_4 hcharQ hsf_cyc
    have hsurj : Function.Surjective (Garling.Chapter15.garlingCyclotomicGalHom hcharQ hsf_cyc) :=
      hirr_surj.mp hirr_cyc
    obtain ⟨hspec_gal, _⟩ := Garling.Chapter15.garlingCyclotomicGalHom_spec_and_injective hcharQ hsf_cyc
    -- The Galois orbit of `ε₀` equals `{ε : L | IsPrimitiveRoot ε n}`:
    have horbit : {ε : L | IsPrimitiveRoot ε n} =
        Set.range (fun σ : GarlingGaloisGroup ℚ L => σ ε₀) := by
      ext ζ
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      constructor
      · intro hζ
        obtain ⟨k, _, rfl⟩ := hε₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
        have hcop : Nat.Coprime k n := (hε₀.pow_iff_coprime (by omega) k).mp hζ
        let u : (ZMod n)ˣ := ZMod.unitOfCoprime k hcop
        obtain ⟨σ, hσ⟩ := hsurj u
        refine ⟨σ, ?_⟩
        have h1 := hspec_gal ε₀ hε₀_gar σ
        rw [hσ] at h1
        change σ ε₀ = ε₀ ^ ((u : ZMod n).val) at h1
        rw [h1]
        have hval : ((u : ZMod n).val) = k % n := by
          change ((k : ZMod n).val) = k % n
          exact ZMod.val_natCast n k
        rw [hval]
        conv_rhs => rw [← Nat.div_add_mod k n]
        rw [pow_add, pow_mul, hε₀.pow_eq_one, one_pow, one_mul]
      · rintro ⟨σ, rfl⟩
        have h1 := hspec_gal ε₀ hε₀_gar σ
        rw [h1]
        have _ : NeZero n := ⟨hn0⟩
        let u := Garling.Chapter15.garlingCyclotomicGalHom hcharQ hsf_cyc σ
        have hcop : Nat.Coprime (u : ZMod n).val n := by
          have hu : IsUnit (((u : ZMod n).val : ℕ) : ZMod n) := by
            rw [ZMod.natCast_zmod_val]; exact u.isUnit
          exact (ZMod.isUnit_iff_coprime _ n).mp hu
        exact hε₀.pow_of_coprime _ hcop
    -- `[L : ℚ] = φ(n)` and `|{ε | IsPrimitiveRoot ε n}| = φ(n)`:
    have hgalQL : IsGarlingGaloisExtension ℚ L :=
      (Garling.Chapter15.section_15_1_roots_group_cyclic hcharQ hsf).1
    have _ : Module.Finite ℚ L := (isFiniteExtension_iff_moduleFinite ℚ L).mp hgalQL.1
    have hfinrank : Module.finrank ℚ L = Nat.totient n := by
      have hcardG := (theorem_10_4_algEquiv hgalQL.1).1 hgalQL
      obtain ⟨_, _, hirr_iso, _, _⟩ := Garling.Chapter15.theorem_15_4 hcharQ hsf_cyc
      obtain ⟨e⟩ := hirr_iso.mp hirr_cyc
      have _ : NeZero n := ⟨hn0⟩
      rw [← hcardG, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    constructor
    · -- `⇒`: if `P` is a normal basis, then `n` is squarefree:
      rintro ⟨⟨hli, _⟩, _⟩
      by_contra hnsq
      have hli_on : LinearIndepOn ℚ id {ε : L | IsPrimitiveRoot ε n} :=
        (isLinearlyIndependent_iff _).mp hli
      -- Pick a prime `p` with `p * p ∣ n`:
      have hex_p : ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ n := by
        by_contra hall
        push Not at hall
        apply hnsq
        intro d hd
        by_contra hnu
        have hd_ne1 : d ≠ 1 := fun h1 => hnu (h1 ▸ isUnit_one)
        have hd_ne0 : d ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hd; exact hn0 (zero_dvd_iff.mp hd)
        let p := d.minFac
        have hp : Nat.Prime p := Nat.minFac_prime hd_ne1
        have hpd : p ∣ d := Nat.minFac_dvd d
        exact hall p hp ((mul_dvd_mul hpd hpd).trans hd)
      obtain ⟨p, hp, hp2_dvd⟩ := hex_p
      rcases hp2_dvd with ⟨k, hnk⟩
      let m := p * k
      have hnm : n = p * m := by dsimp [m]; rw [hnk]; ring
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => hn0 (by rw [hnm, h0, mul_zero])
      let η : L := ε₀ ^ m
      have hη : IsPrimitiveRoot η p := hε₀.pow (by omega) (by rw [hnm, mul_comm])
      let w : Fin p → L := fun j => η ^ j.1 * ε₀
      have hw_prim : ∀ j : Fin p, IsPrimitiveRoot (w j) n := by
        intro j
        have hw_eq : w j = ε₀ ^ (j.1 * m + 1) := by
          dsimp [w, η]; rw [← pow_mul, mul_comm m j.1, pow_succ]
        rw [hw_eq]
        refine hε₀.pow_of_coprime (j.1 * m + 1) ?_
        refine Nat.coprime_of_dvd' fun q hq hq1 hqn => ?_
        have hqm : q ∣ m := by
          rw [hnm] at hqn
          rcases hq.dvd_mul.mp hqn with hqp | hqm
          · have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
            rw [hqeq]; exact ⟨k, rfl⟩
          · exact hqm
        have hqjm : q ∣ j.1 * m := dvd_mul_of_dvd_right hqm j.1
        exact (Nat.dvd_add_right hqjm).mp hq1
      have hw_inj : Function.Injective w := by
        intro j₁ j₂ hEq
        have hε₀_ne0 : ε₀ ≠ 0 := hε₀.ne_zero hn0
        have hη_eq : η ^ j₁.1 = η ^ j₂.1 := mul_right_cancel₀ hε₀_ne0 hEq
        exact Fin.ext (hη.injOn_pow
          (Finset.mem_coe.mpr (Finset.mem_range.mpr j₁.2))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr j₂.2)) hη_eq)
      have hsum_w : ∑ j : Fin p, (1 : ℚ) • w j = 0 := by
        simp only [one_smul, w, ← Finset.sum_mul]
        have hgeom : ∑ j : Fin p, η ^ j.1 = 0 := by
          rw [Fin.sum_univ_eq_sum_range (fun j => η ^ j)]
          have h1 : (η - 1) * ∑ j ∈ Finset.range p, η ^ j = η ^ p - 1 := by
            rw [mul_comm]; exact geom_sum_mul η p
          rw [hη.pow_eq_one, sub_self] at h1
          exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (hη.ne_one hp.one_lt))
        rw [hgeom, zero_mul]
      have hli_w : LinearIndependent ℚ w :=
        (hli_on.comp (fun j => ⟨w j, hw_prim j⟩) (fun a b h => hw_inj (congrArg Subtype.val h)))
      have h10 := Fintype.linearIndependent_iff.mp hli_w (fun _ => (1 : ℚ)) hsum_w ⟨0, hp.pos⟩
      exact one_ne_zero h10
    · -- `⇐`: if `Squarefree n`, then `span ℚ P = ⊤` and `|P| = φ(n) = finrank ℚ L`, so `P` is a normal basis:
      intro hsq
      have hspan : Submodule.span ℚ {ε : L | IsPrimitiveRoot ε n} = ⊤ :=
        eq_top_iff.mpr fun y _ =>
          span_primitiveRoots_eq_top_of_squarefree n hn1 hsq hε₀ y (htop ▸ IntermediateField.mem_top)
      have hfin_P : (primitiveRoots n L : Set L) = {ε : L | IsPrimitiveRoot ε n} := by
        ext ε; simp [mem_primitiveRoots (by omega : 0 < n)]
      have hcard_P : (primitiveRoots n L).card = Module.finrank ℚ L := by
        rw [hε₀.card_primitiveRoots, hfinrank]
      have hli_P : LinearIndepOn ℚ id {ε : L | IsPrimitiveRoot ε n} := by
        rw [← hfin_P] at hspan ⊢
        have hli_sub : LinearIndependent ℚ (fun x : primitiveRoots n L => (x : L)) :=
          linearIndependent_of_top_le_span_of_card_eq_finrank
            (by rw [Subtype.range_coe_subtype]; exact le_of_eq hspan.symm)
            (by rw [Fintype.card_coe, hcard_P])
        exact hli_sub
      exact ⟨⟨(isLinearlyIndependent_iff _).mpr hli_P, hspan⟩, ε₀, horbit⟩

/-!
## §19.3 Constructing regular polygons (printed pp. 152–154 / PDF pp. 160–162)
-/

/-- Helper converting any ring isomorphism between fields equipped with `Algebra ℚ` instances into
a `ℚ`-linear equivalence, avoiding `DivisionRing.toRatAlgebra` vs. `IntermediateField.algebra'`
definitional diamonds. -/
private def ratLinearEquivOfRingEquiv {A B : Type*} [Field A] [Field B]
    [Algebra ℚ A] [Algebra ℚ B] (e : A ≃+* B) : A ≃ₗ[ℚ] B :=
  { e.toAddEquiv with
    map_smul' := fun q x => by
      change e (q • x) = q • e x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ A) q,
        eq_ratCast (algebraMap ℚ B) q, map_ratCast] }

/-- **§19.3 Inline prose definition — *possible* (`n > 2`)** (printed p. 152 / PDF p. 160):
*"given an integer `n > 2`, can we construct a regular polygon with `n` sides of unit length,
using ruler and compasses alone? Let us say that an integer `n` is possible if this can be done."*

Carries `2 < n` explicitly (so `¬ IsPossible 1` and `¬ IsPossible 2`, matching p. 152 and making
`Theorem 19.8` hold literally for all `b : ℕ` including `b = 0`). -/
def IsPossible (n : ℕ) : Prop :=
  2 < n ∧ IsUnitSideRegularPolygonConstructible n

/-- `θ_n = 2π / n` (§19.3, printed p. 152 / PDF p. 160). -/
noncomputable def thetaN (n : ℕ) : ℝ :=
  2 * Real.pi / (n : ℝ)

/-- `x_n = cos θ_n` (§19.3, printed p. 152 / PDF p. 160). -/
noncomputable def xN (n : ℕ) : ℝ :=
  Real.cos (thetaN n)

/-- `y_n = sin θ_n` (§19.3, printed p. 152 / PDF p. 160). -/
noncomputable def yN (n : ℕ) : ℝ :=
  Real.sin (thetaN n)

/-- `ε_n = cos θ_n + i sin θ_n = e^{i θ_n}` (§19.3, printed p. 152 / PDF p. 160). -/
noncomputable def epsN (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (thetaN n : ℂ))

theorem epsN_eq_cos_add_sin_mul_I (n : ℕ) :
    epsN n = (xN n : ℂ) + (yN n : ℂ) * Complex.I := by
  unfold epsN xN yN
  rw [mul_comm Complex.I (thetaN n : ℂ), Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

theorem epsN_re (n : ℕ) : (epsN n).re = xN n := by
  rw [epsN_eq_cos_add_sin_mul_I]; simp

theorem epsN_im (n : ℕ) : (epsN n).im = yN n := by
  rw [epsN_eq_cos_add_sin_mul_I]; simp

/-- §19.3 prose remark (p. 152): *"The complex number `ε_n` is a primitive `n`th root of unity
in `ℂ`."* (Proved for all `n ≠ 0`.) -/
theorem isPrimitiveRoot_epsN {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (epsN n) n ∧ Garling.Chapter15.IsGarlingPrimitiveRoot n (epsN n) := by
  have hprim : IsPrimitiveRoot (epsN n) n := by
    have heq : epsN n = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
      unfold epsN thetaN
      congr 1
      push_cast
      ring
    rw [heq]
    exact Complex.isPrimitiveRoot_exp n hn
  exact ⟨hprim, (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot
    (Nat.pos_of_ne_zero hn) (epsN n)).mpr hprim⟩

/-- Equivalence of `IsPossible n` (for `n > 2`) with constructibility of `(x_n, y_n)` and all four
Chapter 6 regular-polygon formulations (p. 152). -/
theorem isPossible_iff_constructible_point {n : ℕ} (hn : 2 < n) :
    (IsPossible n ↔ IsConstructible (xN n, yN n)) ∧
    (IsPossible n ↔ xN n ∈ constructibleSubfield) ∧
    (IsPossible n ↔ IsUnitCircleRegularPolygonConstructible n) ∧
    (IsPossible n ↔ IsAnyRegularPolygonConstructible n) := by
  obtain ⟨h0A, hAB, hBC, hCD⟩ := regularPolygon_constructible_iff (n := n) (by omega)
  have hA_eq : IsGarlingUnitCircleGeneratorConstructible n ↔ IsConstructible (xN n, yN n) := Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [IsPossible, hn, true_and]
    exact (hBC.symm.trans hAB.symm).trans hA_eq
  · simp only [IsPossible, hn, true_and]
    exact (hBC.symm.trans hAB.symm).trans h0A.symm
  · simp only [IsPossible, hn, true_and]
    exact hBC.symm
  · simp only [IsPossible, hn, true_and]
    exact hCD

/-- Recording why `2 < n` is essential in `IsPossible`: `1` and `2` are not possible (`¬ IsPossible 1`,
`¬ IsPossible 2`), even though `(x_1, y_1) = (1, 0)` and `(x_2, y_2) = (-1, 0)` ARE constructible. -/
theorem isPossible_n1_n2_false :
    ¬ IsPossible 1 ∧ ¬ IsPossible 2 ∧
    IsConstructible (xN 1, yN 1) ∧ IsConstructible (xN 2, yN 2) := by
  refine ⟨fun h => by have := h.1; omega, fun h => by have := h.1; omega, ?_, ?_⟩
  · have h1 : xN 1 = 1 ∧ yN 1 = 0 := by
      unfold xN yN thetaN
      simp [Real.cos_two_pi, Real.sin_two_pi]
    rw [h1.1, h1.2]
    exact isConstructible_P₁
  · have h2 : xN 2 = -1 ∧ yN 2 = 0 := by
      unfold xN yN thetaN
      have hpi : (2 * Real.pi / (2 : ℕ) : ℝ) = Real.pi := by push_cast; ring
      rw [hpi, Real.cos_pi, Real.sin_pi]
      exact ⟨rfl, rfl⟩
    rw [h2.1, h2.2]
    exact isConstructible_neg_one_zero

/-- §19.3 angle constructibility predicate (p. 152): an angle `θ ∈ ℝ` is constructible iff
`(cos θ, sin θ)` is a constructible point. -/
def IsConstructibleAngle (θ : ℝ) : Prop :=
  IsConstructible (Real.cos θ, Real.sin θ)

theorem isConstructibleAngle_iff (θ : ℝ) :
    IsConstructibleAngle θ ↔
      Real.cos θ ∈ constructibleSubfield ∧ Real.sin θ ∈ constructibleSubfield :=
  isConstructible_iff_mem_constructibleSubfield (Real.cos θ) (Real.sin θ)

theorem isConstructibleAngle_zero : IsConstructibleAngle 0 := by
  rw [isConstructibleAngle_iff, Real.cos_zero, Real.sin_zero]
  exact ⟨constructibleSubfield.one_mem, constructibleSubfield.zero_mem⟩

theorem isConstructibleAngle_neg {θ : ℝ} (hθ : IsConstructibleAngle θ) :
    IsConstructibleAngle (-θ) := by
  rw [isConstructibleAngle_iff] at hθ ⊢
  rw [Real.cos_neg, Real.sin_neg]
  exact ⟨hθ.1, constructibleSubfield.neg_mem hθ.2⟩

theorem isConstructibleAngle_add {θ φ : ℝ}
    (hθ : IsConstructibleAngle θ) (hφ : IsConstructibleAngle φ) :
    IsConstructibleAngle (θ + φ) := by
  rw [isConstructibleAngle_iff] at hθ hφ ⊢
  rw [Real.cos_add, Real.sin_add]
  exact ⟨constructibleSubfield.sub_mem (constructibleSubfield.mul_mem hθ.1 hφ.1)
      (constructibleSubfield.mul_mem hθ.2 hφ.2),
    constructibleSubfield.add_mem (constructibleSubfield.mul_mem hθ.2 hφ.1)
      (constructibleSubfield.mul_mem hθ.1 hφ.2)⟩

theorem isConstructibleAngle_sub {θ φ : ℝ}
    (hθ : IsConstructibleAngle θ) (hφ : IsConstructibleAngle φ) :
    IsConstructibleAngle (θ - φ) := by
  rw [sub_eq_add_neg]
  exact isConstructibleAngle_add hθ (isConstructibleAngle_neg hφ)

/-- §19.3 prose statement (p. 152): *"if we can construct angles `θ` and `φ` then we can construct
angles `θ + φ` and `|θ - φ|`."* -/
theorem isConstructibleAngle_abs_sub {θ φ : ℝ}
    (hθ : IsConstructibleAngle θ) (hφ : IsConstructibleAngle φ) :
    IsConstructibleAngle |θ - φ| := by
  rcases abs_cases (θ - φ) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact isConstructibleAngle_sub hθ hφ
  · rw [h]; exact isConstructibleAngle_neg (isConstructibleAngle_sub hθ hφ)

theorem isConstructibleAngle_nsmul {θ : ℝ} (hθ : IsConstructibleAngle θ) (k : ℕ) :
    IsConstructibleAngle ((k : ℝ) * θ) := by
  induction k with
  | zero => simpa using isConstructibleAngle_zero
  | succ m ih =>
    have hEq : (((m + 1 : ℕ) : ℝ) * θ) = (m : ℝ) * θ + θ := by push_cast; ring
    rw [hEq]
    exact isConstructibleAngle_add ih hθ

theorem isConstructibleAngle_zsmul {θ : ℝ} (hθ : IsConstructibleAngle θ) (a : ℤ) :
    IsConstructibleAngle ((a : ℝ) * θ) := by
  rcases Int.eq_nat_or_neg a with ⟨k, rfl | rfl⟩
  · simpa using isConstructibleAngle_nsmul hθ k
  · have hEq : (((-(k : ℤ) : ℤ) : ℝ) * θ) = -((k : ℝ) * θ) := by push_cast; ring
    rw [hEq]
    exact isConstructibleAngle_neg (isConstructibleAngle_nsmul hθ k)

/-- §19.3 prose angle bisection (p. 152): if `θ` is a constructible angle, then `θ / 2` is a
constructible angle. -/
theorem isConstructibleAngle_half {θ : ℝ} (hθ : IsConstructibleAngle θ) :
    IsConstructibleAngle (θ / 2) := by
  rw [isConstructibleAngle_iff] at hθ ⊢
  let K := constructibleSubfield
  have h2K : (2 : ℝ) ∈ K := by exact_mod_cast SubfieldClass.ratCast_mem K (2 : ℚ)
  have hcos_id : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2)
    have h2 : 2 * (θ / 2) = θ := by ring
    rwa [h2] at this
  have hcos_sq : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by linarith
  have hsin_sq : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have hsc := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hmem_sq : ∀ {u s : ℝ}, u ^ 2 = s → s ∈ K → u ∈ K := by
    intro u s hus hsK
    have hs0 : 0 ≤ s := hus ▸ sq_nonneg u
    have hsqrtK : Real.sqrt s ∈ K := sqrt_mem_constructibleSubfield hsK hs0
    have hdiff : (u - Real.sqrt s) * (u + Real.sqrt s) = 0 := by
      have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
      linear_combination hus - hsq
    rcases mul_eq_zero.mp hdiff with h1 | h2
    · have : u = Real.sqrt s := by linarith
      rw [this]; exact hsqrtK
    · have : u = -Real.sqrt s := by linarith
      rw [this]; exact K.neg_mem hsqrtK
  exact ⟨hmem_sq hcos_sq (K.div_mem (K.add_mem K.one_mem hθ.1) h2K),
    hmem_sq hsin_sq (K.div_mem (K.sub_mem K.one_mem hθ.1) h2K)⟩

/-- §19.3 prose result (p. 152): *"if `n` is possible then so is `2n`, for we can certainly bisect
angles."* -/
theorem isPossible_two_mul {n : ℕ} (hn : IsPossible n) : IsPossible (2 * n) := by
  have hn2 : 2 < n := hn.1
  have h2n : 2 < 2 * n := by omega
  rw [((isPossible_iff_constructible_point h2n).1)]
  have hang : IsConstructibleAngle (thetaN n) :=
    ((isPossible_iff_constructible_point hn2).1).mp hn
  have hhalf : thetaN (2 * n) = thetaN n / 2 := by
    unfold thetaN; push_cast; ring
  change IsConstructibleAngle (thetaN (2 * n))
  rw [hhalf]
  exact isConstructibleAngle_half hang

/-- Powers of `2` with `2 ≤ t` (`4, 8, 16, …`) are possible (§19.3, p. 152). -/
theorem isPossible_pow_two {t : ℕ} (ht : 2 ≤ t) : IsPossible (2 ^ t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction k with
  | zero =>
    change IsPossible 4
    rw [(isPossible_iff_constructible_point (by omega : 2 < 4)).1]
    have h4 : thetaN 4 = Real.pi / 2 := by unfold thetaN; push_cast; ring
    unfold xN yN
    rw [h4, Real.cos_pi_div_two, Real.sin_pi_div_two]
    exact isConstructible_zero_one
  | succ m ih =>
    have hpow : 2 ^ (2 + (m + 1)) = 2 * 2 ^ (2 + m) := by ring
    rw [hpow]
    exact isPossible_two_mul ih

/-- §19.3 prose result (p. 152): *"Suppose that `m` and `n` are possible and that `m` and `n` are
relatively prime. ... so that `mn` is possible."* -/
theorem isPossible_mul_of_coprime {m n : ℕ} (hm : IsPossible m) (hn : IsPossible n)
    (hcop : Nat.Coprime m n) : IsPossible (m * n) := by
  have hm2 : 2 < m := hm.1
  have hn2 : 2 < n := hn.1
  have hmn2 : 2 < m * n := by nlinarith
  rw [(isPossible_iff_constructible_point hmn2).1]
  have hang_m : IsConstructibleAngle (thetaN m) :=
    ((isPossible_iff_constructible_point hm2).1).mp hm
  have hang_n : IsConstructibleAngle (thetaN n) :=
    ((isPossible_iff_constructible_point hn2).1).mp hn
  let a : ℤ := Nat.gcdA m n
  let b : ℤ := Nat.gcdB m n
  have hab : (m : ℤ) * a + (n : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have habR : (a : ℝ) * (m : ℝ) + (b : ℝ) * (n : ℝ) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hab
    push_cast at h
    linarith
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htheta : (a : ℝ) * thetaN n + (b : ℝ) * thetaN m = thetaN (m * n) := by
    unfold thetaN
    push_cast
    calc (a : ℝ) * (2 * Real.pi / (n : ℝ)) + (b : ℝ) * (2 * Real.pi / (m : ℝ))
        = ((a : ℝ) * (m : ℝ) + (b : ℝ) * (n : ℝ)) * (2 * Real.pi / ((m : ℝ) * (n : ℝ))) := by
          field_simp [hm_ne, hn_ne]
      _ = 2 * Real.pi / ((m : ℝ) * (n : ℝ)) := by rw [habR, one_mul]
  change IsConstructibleAngle (thetaN (m * n))
  rw [← htheta]
  exact isConstructibleAngle_add
    (isConstructibleAngle_zsmul hang_n a)
    (isConstructibleAngle_zsmul hang_m b)

/-- §19.3 prose result (p. 152): *"if `l` is possible then so are all its divisors"* (with
`2 < d`, matching the `n > 2` domain of *possible*). -/
theorem isPossible_of_dvd {l d : ℕ} (hl : IsPossible l) (hdvd : d ∣ l) (hd2 : 2 < d) :
    IsPossible d := by
  have hl2 : 2 < l := hl.1
  rcases hdvd with ⟨k, rfl⟩
  rw [(isPossible_iff_constructible_point hd2).1]
  have hang_l : IsConstructibleAngle (thetaN (d * k)) :=
    ((isPossible_iff_constructible_point hl2).1).mp hl
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    intro h0; rw [h0, mul_zero] at hl2; omega)
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htheta : thetaN d = (k : ℝ) * thetaN (d * k) := by
    unfold thetaN
    push_cast
    field_simp [hd_ne, hk_ne]
  change IsConstructibleAngle (thetaN d)
  rw [htheta]
  exact isConstructibleAngle_nsmul hang_l k

/-- §19.3 prose examples (p. 152): *"Using the results of Chapter 6 (and its exercises) it should
be clear that `3, 4, 5, 6, 8` and `10` are possible, while `7` and `9` are not."* -/
theorem section_19_3_small_examples :
    IsPossible 3 ∧ IsPossible 4 ∧ IsPossible 5 ∧ IsPossible 6 ∧ IsPossible 8 ∧ IsPossible 10 ∧
    ¬ IsPossible 7 ∧ ¬ IsPossible 9 := by
  have h3 : IsPossible 3 := by
    rw [(isPossible_iff_constructible_point (by omega : 2 < 3)).2.1]
    have hcos : xN 3 = -(1 / 2 : ℝ) := by
      unfold xN thetaN
      have harg : (2 * Real.pi / (3 : ℕ) : ℝ) = 2 * (Real.pi / 3) := by push_cast; ring
      rw [harg, Real.cos_two_mul, Real.cos_pi_div_three]
      norm_num
    rw [hcos]
    exact constructibleSubfield.neg_mem
      (constructibleSubfield.div_mem constructibleSubfield.one_mem
        (by exact_mod_cast SubfieldClass.ratCast_mem constructibleSubfield (2 : ℚ)))
  have h4 : IsPossible 4 := isPossible_pow_two (t := 2) le_rfl
  have h5 : IsPossible 5 := ⟨by omega, Chapter06.exercise_6_3.2.2.1⟩
  have h6 : IsPossible 6 := isPossible_two_mul h3
  have h8 : IsPossible 8 := isPossible_two_mul h4
  have h10 : IsPossible 10 := isPossible_two_mul h5
  have h7 : ¬ IsPossible 7 := fun h => Chapter06.exercise_6_6.2.2.2.1 h.2
  have h9 : ¬ IsPossible 9 := fun h => Chapter06.exercise_6_6.1.2.2.1 h.2
  exact ⟨h3, h4, h5, h6, h8, h10, h7, h9⟩

/-- **Counterexamples to literal unguarded `Theorem 19.7`** (`QUEUE.md` hold, p. 152):
Omitting §19.3's standing `2 < n` allows `r = 0, t = 0` (`n = 1`) and `r = 0, t = 1` (`n = 2`),
where the prime-power condition on `p_i^b` holds vacuously while `¬ IsPossible 1` and
`¬ IsPossible 2`. -/
theorem theorem_19_7_n1_n2_counterexamples :
    (1 = 2 ^ 0 * ∏ i : Fin 0, (Fin.elim0 i) ^ (Fin.elim0 i) ∧
      (∀ i : Fin 0, ∀ b : ℕ, 1 ≤ b → b ≤ Fin.elim0 i → IsPossible ((Fin.elim0 i) ^ b)) ∧
      ¬ IsPossible 1) ∧
    (2 = 2 ^ 1 * ∏ i : Fin 0, (Fin.elim0 i) ^ (Fin.elim0 i) ∧
      (∀ i : Fin 0, ∀ b : ℕ, 1 ≤ b → b ≤ Fin.elim0 i → IsPossible ((Fin.elim0 i) ^ b)) ∧
      ¬ IsPossible 2) := by
  refine ⟨⟨by simp, fun i => Fin.elim0 i, isPossible_n1_n2_false.1⟩,
    ⟨by simp, fun i => Fin.elim0 i, isPossible_n1_n2_false.2.1⟩⟩

/-- **Theorem 19.7 (Repaired with standing `2 < n`)** (§19.3, printed p. 152 / PDF p. 160):
*"Suppose that `n = 2^t p_1^{a_1} ⋯ p_r^{a_r}`, where `p_1, …, p_r` are distinct odd primes
[and `n > 2`]. Then `n` is possible if and only if `p_i^b` is possible for `1 ≤ b ≤ a_i`,
`1 ≤ i ≤ r`."* -/
theorem theorem_19_7_repaired {n t r : ℕ} {p a : Fin r → ℕ}
    (hn2 : 2 < n)
    (hp_prime : ∀ i : Fin r, Nat.Prime (p i))
    (hp_odd : ∀ i : Fin r, Odd (p i))
    (hp_inj : Function.Injective p)
    (hn_eq : n = 2 ^ t * ∏ i : Fin r, (p i) ^ (a i)) :
    IsPossible n ↔ ∀ i : Fin r, ∀ b : ℕ, 1 ≤ b → b ≤ a i → IsPossible ((p i) ^ b) := by
  constructor
  · intro hposs i b hb1 hba
    have hp3 : 3 ≤ p i := by
      have h2 := (hp_prime i).two_le
      have hne2 : p i ≠ 2 := fun h2eq =>
        Nat.not_odd_iff_even.mpr even_two (h2eq ▸ hp_odd i)
      omega
    have hpb2 : 2 < (p i) ^ b := by
      calc 2 < 3 := by omega
        _ ≤ p i := hp3
        _ = (p i) ^ 1 := (pow_one _).symm
        _ ≤ (p i) ^ b := Nat.pow_le_pow_right (by omega) hb1
    have hdvd_pow : (p i) ^ b ∣ (p i) ^ (a i) := Nat.pow_dvd_pow (p i) hba
    have hdvd_prod : (p i) ^ (a i) ∣ ∏ j : Fin r, (p j) ^ (a j) :=
      Finset.dvd_prod_of_mem (fun j => (p j) ^ (a j)) (Finset.mem_univ i)
    have hdvd_n : (p i) ^ b ∣ n := by
      rw [hn_eq]
      exact (hdvd_pow.trans hdvd_prod).trans (dvd_mul_left _ _)
    exact isPossible_of_dvd hposs hdvd_n hpb2
  · intro hall
    -- Show by induction on `S : Finset (Fin r)` that `∏ i ∈ S, (p i) ^ (a i)` is either `1` or possible:
    have hprod_aux : ∀ S : Finset (Fin r),
        (∏ i ∈ S, (p i) ^ (a i)) = 1 ∨ IsPossible (∏ i ∈ S, (p i) ^ (a i)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => left; simp
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        by_cases ha0 : a i = 0
        · rw [ha0, pow_zero, one_mul]; exact ih
        · have ha1 : 1 ≤ a i := Nat.pos_of_ne_zero ha0
          have hi_poss : IsPossible ((p i) ^ (a i)) := hall i (a i) ha1 le_rfl
          rcases ih with hS1 | hSposs
          · right; rw [hS1, mul_one]; exact hi_poss
          · right
            have hcop : Nat.Coprime ((p i) ^ (a i)) (∏ j ∈ S, (p j) ^ (a j)) := by
              refine Nat.Coprime.prod_right fun j hj => ?_
              have hne : p i ≠ p j := fun hEq => hi (hp_inj hEq ▸ hj)
              exact ((Nat.coprime_primes (hp_prime i) (hp_prime j)).mpr hne).pow _ _
            exact isPossible_mul_of_coprime hi_poss hSposs hcop
    -- Multiply by `2^t`:
    have hmul_two_pow : ∀ k m : ℕ, IsPossible m → IsPossible (2 ^ k * m) := by
      intro k
      induction k with
      | zero => intro m hm; simpa using hm
      | succ k ihk =>
        intro m hm
        have hEq : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
        rw [hEq]
        exact isPossible_two_mul (ihk m hm)
    rw [hn_eq]
    rcases hprod_aux Finset.univ with h1 | hMposs
    · rw [h1, mul_one] at hn_eq ⊢
      have ht2 : 2 ≤ t := by
        by_contra hlt
        have ht1 : t = 0 ∨ t = 1 := by omega
        rcases ht1 with rfl | rfl <;> omega
      exact isPossible_pow_two ht2
    · exact hmul_two_pow t _ hMposs

/-- **Theorem 19.7 (Unconditional exact characterization across all `n : ℕ`)** (§19.3, p. 152). -/
theorem theorem_19_7_iff {n t r : ℕ} {p a : Fin r → ℕ}
    (hp_prime : ∀ i : Fin r, Nat.Prime (p i))
    (hp_odd : ∀ i : Fin r, Odd (p i))
    (hp_inj : Function.Injective p)
    (hn_eq : n = 2 ^ t * ∏ i : Fin r, (p i) ^ (a i)) :
    IsPossible n ↔
      2 < n ∧ ∀ i : Fin r, ∀ b : ℕ, 1 ≤ b → b ≤ a i → IsPossible ((p i) ^ b) := by
  constructor
  · intro h; exact ⟨h.1, (theorem_19_7_repaired h.1 hp_prime hp_odd hp_inj hn_eq).mp h⟩
  · rintro ⟨hn2, hall⟩; exact (theorem_19_7_repaired hn2 hp_prime hp_odd hp_inj hn_eq).mpr hall

/-- **§19.3 Prose Complex Quadratic-Step Constructibility** (printed p. 153 / PDF p. 161, inside
`Theorem 19.8`'s proof): if `E ≤ F` are subfields of `ℂ` (`IntermediateField ℚ ℂ`) with `[F : E] = 2`
and every `z ∈ E` has `(z.re, z.im)` constructible, then every `z ∈ F` has `(z.re, z.im)`
constructible. -/
theorem section_19_3_complex_quadratic_step_constructible
    {E F : IntermediateField ℚ ℂ} (hEF : E ≤ F)
    (hE : ∀ z ∈ E, IsConstructible (z.re, z.im))
    (hdeg : let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
            Module.finrank E F = 2) :
    ∀ z ∈ F, IsConstructible (z.re, z.im) := by
  let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have hfin2 : Module.finrank E F = 2 := hdeg
  have _ : Module.Finite E F := Module.finite_of_finrank_pos (by omega)
  let K := constructibleSubfield
  have h2K : (2 : ℝ) ∈ K := by exact_mod_cast SubfieldClass.ratCast_mem K (2 : ℚ)
  have hmem_sq : ∀ {u s : ℝ}, u ^ 2 = s → s ∈ K → u ∈ K := by
    intro u s hus hsK
    have hs0 : 0 ≤ s := hus ▸ sq_nonneg u
    have hsqrtK : Real.sqrt s ∈ K := sqrt_mem_constructibleSubfield hsK hs0
    have hdiff : (u - Real.sqrt s) * (u + Real.sqrt s) = 0 := by
      have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
      linear_combination hus - hsq
    rcases mul_eq_zero.mp hdiff with h1 | h2
    · have : u = Real.sqrt s := by linarith
      rw [this]; exact hsqrtK
    · have : u = -Real.sqrt s := by linarith
      rw [this]; exact K.neg_mem hsqrtK
  intro z hzF
  by_cases hzE : z ∈ E
  · exact hE z hzE
  · -- Since `z ∈ F \ E` and `[F : E] = 2`, `{1, z}` is an `E`-basis of `F`, so `z^2 = a + b z` for `a, b ∈ E`:
    have halgEF : ∀ u : E, ((algebraMap E F u : F) : ℂ) = (u : ℂ) := fun _ => rfl
    let zF : F := ⟨z, hzF⟩
    let w : Fin 2 → F := ![1, zF]
    have hw_li : LinearIndependent E w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hsum : (c 0 : ℂ) + (c 1 : ℂ) * z = 0 := by
        have hval := congrArg Subtype.val hc
        rw [Fin.sum_univ_two] at hval
        simpa [w, zF, Algebra.smul_def, halgEF] using hval
      have hc1 : c 1 = 0 := by
        by_contra hne
        have hneC : (c 1 : ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
        have hz_eq : z = -(c 0 : ℂ) / (c 1 : ℂ) := by
          field_simp [hneC]; linear_combination hsum
        have hz_mem : z ∈ E := by
          rw [hz_eq]
          exact E.div_mem (E.neg_mem (c 0).2) (c 1).2
        exact hzE hz_mem
      have hc0 : c 0 = 0 := by
        have h1 : (c 1 : ℂ) = 0 := congrArg Subtype.val hc1
        rw [h1, zero_mul, add_zero] at hsum
        exact Subtype.ext hsum
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
    have hw_span : Submodule.span E (Set.range w) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hw_li, Fintype.card_fin, hfin2]
    let hB : Module.Basis (Fin 2) E F := Module.Basis.mk hw_li (le_of_eq hw_span.symm)
    have hrepr := hB.sum_repr (zF ^ 2)
    rw [Fin.sum_univ_two] at hrepr
    let aE : E := hB.repr (zF ^ 2) 0
    let bE : E := hB.repr (zF ^ 2) 1
    have hquad : z ^ 2 = (aE : ℂ) + (bE : ℂ) * z := by
      have hval := congrArg Subtype.val hrepr
      have h0 : hB 0 = 1 := by simp [hB, Module.Basis.mk_apply, w]
      have h1 : hB 1 = zF := by simp [hB, Module.Basis.mk_apply, w]
      rw [h0, h1] at hval
      have hval' : (aE : ℂ) * 1 + (bE : ℂ) * z = z ^ 2 := by
        simpa [aE, bE, zF, Algebra.smul_def, halgEF] using hval
      linear_combination -hval'
    -- Complete the square: `v = z - b / 2`, `v^2 = μ := a + b^2 / 4 ∈ E`:
    let v : ℂ := z - (bE : ℂ) / 2
    let μ : ℂ := (aE : ℂ) + (bE : ℂ) ^ 2 / 4
    have hμE : μ ∈ E := by
      have h4E : (4 : ℂ) ∈ E := by exact_mod_cast E.algebraMap_mem (4 : ℚ)
      exact E.add_mem aE.2 (E.div_mem (pow_mem bE.2 2) h4E)
    have hv2 : v ^ 2 = μ := by
      dsimp only [v, μ]
      linear_combination hquad
    have hμ_reK : μ.re ∈ K := ((isConstructible_iff_mem_constructibleSubfield _ _).mp (hE μ hμE)).1
    have hμ_imK : μ.im ∈ K := ((isConstructible_iff_mem_constructibleSubfield _ _).mp (hE μ hμE)).2
    have hb_reK : (bE : ℂ).re ∈ K := ((isConstructible_iff_mem_constructibleSubfield _ _).mp (hE bE.1 bE.2)).1
    have hb_imK : (bE : ℂ).im ∈ K := ((isConstructible_iff_mem_constructibleSubfield _ _).mp (hE bE.1 bE.2)).2
    have hre_eq : v.re ^ 2 - v.im ^ 2 = μ.re := by
      have h := congrArg Complex.re hv2
      simp only [sq, Complex.mul_re] at h
      linarith
    have him_eq : 2 * v.re * v.im = μ.im := by
      have h := congrArg Complex.im hv2
      simp only [sq, Complex.mul_im] at h
      linarith
    let r : ℝ := Real.sqrt (μ.re ^ 2 + μ.im ^ 2)
    have hrK : r ∈ K :=
      sqrt_mem_constructibleSubfield (K.add_mem (K.pow_mem hμ_reK 2) (K.pow_mem hμ_imK 2))
        (by positivity)
    have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
    have hr_sq : r ^ 2 = μ.re ^ 2 + μ.im ^ 2 := Real.sq_sqrt (by positivity)
    have hnorm_sq : (v.re ^ 2 + v.im ^ 2) ^ 2 = r ^ 2 := by
      linear_combination hr_sq.symm + (v.re ^ 2 - v.im ^ 2 + μ.re) * hre_eq +
        (2 * v.re * v.im + μ.im) * him_eq
    have hnorm_eq : v.re ^ 2 + v.im ^ 2 = r := by
      have hnn : 0 ≤ v.re ^ 2 + v.im ^ 2 := by positivity
      nlinarith
    have hvre_sq : v.re ^ 2 = (r + μ.re) / 2 := by linarith
    have hvim_sq : v.im ^ 2 = (r - μ.re) / 2 := by linarith
    have hvreK : v.re ∈ K := hmem_sq hvre_sq (K.div_mem (K.add_mem hrK hμ_reK) h2K)
    have hvimK : v.im ∈ K := hmem_sq hvim_sq (K.div_mem (K.sub_mem hrK hμ_reK) h2K)
    have hz_eq : z = v + (bE : ℂ) / 2 := by dsimp [v]; ring
    have hz_re : z.re = v.re + (bE : ℂ).re / 2 := by
      rw [hz_eq]; simp
    have hz_im : z.im = v.im + (bE : ℂ).im / 2 := by
      rw [hz_eq]; simp
    exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr
      ⟨hz_re ▸ K.add_mem hvreK (K.div_mem hb_reK h2K),
       hz_im ▸ K.add_mem hvimK (K.div_mem hb_imK h2K)⟩

/-- **§19.3 Prose Complex Quadratic-Tower Constructibility** (printed p. 153 / PDF p. 161):
Inducting `section_19_3_complex_quadratic_step_constructible` along any quadratic tower
`ℚ = L_0 ≤ L_1 ≤ ⋯ ≤ L_s ⊆ ℂ` (`[L_{j+1} : L_j] = 2`), every `z ∈ L_s` has `(z.re, z.im)`
constructible. -/
theorem section_19_3_complex_quadratic_tower_constructible {s : ℕ}
    (L : Fin (s + 1) → IntermediateField ℚ ℂ)
    (hL0 : L 0 = ⊥)
    (hmono : ∀ j : Fin s, L j.castSucc ≤ L j.succ)
    (hdeg : ∀ j : Fin s,
      let _ : Algebra (L j.castSucc) (L j.succ) := (IntermediateField.inclusion (hmono j)).toAlgebra
      Module.finrank (L j.castSucc) (L j.succ) = 2) :
    ∀ z ∈ L (Fin.last s), IsConstructible (z.re, z.im) := by
  have hall : ∀ (k : ℕ) (hk : k ≤ s), ∀ z ∈ L ⟨k, Nat.lt_succ_of_le hk⟩,
      IsConstructible (z.re, z.im) := by
    intro k
    induction k with
    | zero =>
      intro _ z hz
      have hz0 : z ∈ (⊥ : IntermediateField ℚ ℂ) := hL0 ▸ hz
      rcases IntermediateField.mem_bot.mp hz0 with ⟨q, rfl⟩
      have hre : (algebraMap ℚ ℂ q).re = (q : ℝ) := by simp
      have him : (algebraMap ℚ ℂ q).im = 0 := by simp
      rw [hre, him]
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr
        ⟨SubfieldClass.ratCast_mem constructibleSubfield q, constructibleSubfield.zero_mem⟩
    | succ k ih =>
      intro hk
      have hlt : k < s := Nat.lt_of_succ_le hk
      exact section_19_3_complex_quadratic_step_constructible (hmono ⟨k, hlt⟩)
        (ih (le_of_lt hlt)) (hdeg ⟨k, hlt⟩)
  exact hall s le_rfl

/-- Abstract tower-degree helper avoiding `DivisionRing.toRatAlgebra` vs. `IntermediateField.algebra'`
definitional diamonds on `ℚ`-subfields. -/
private theorem finrank_rat_of_sub_finrank_equiv {M L N : Type*} [Field M] [Field L] [Field N]
    [Algebra ℚ M] [Algebra M L] [Algebra ℚ L] [IsScalarTower ℚ M L] [Algebra ℚ N]
    (e : M ≃+* N) {a b : ℕ}
    (hML : Module.finrank M L = b) (hQL : Module.finrank ℚ L = a * b) (hb : 0 < b) :
    Module.finrank ℚ N = a := by
  have h := Module.finrank_mul_finrank ℚ M L
  rw [hML, hQL] at h
  have hM : Module.finrank ℚ M = a := Nat.eq_of_mul_eq_mul_right hb h
  rw [← LinearEquiv.finrank_eq (ratLinearEquivOfRingEquiv e), hM]

/-- Helper for `Theorem 19.8 (⇐)`: if `L : ℚ` is a Galois extension with cyclic Galois group of
order `2^k` and `ι : L →ₐ[ℚ] ℂ` is a `ℚ`-embedding, then `(ι z).re, (ι z).im` are constructible
for every `z : L` (implementing Garling's p. 153 subgroup-chain / fixed-field tower proof with
corrected indexing `H_j = ⟨σ^{2^j}⟩`). -/
private theorem complex_constructible_of_cyclic_pow_two_galois
    {L : Type*} [Field L] [Algebra ℚ L] (ι : L →ₐ[ℚ] ℂ)
    (hgal : IsGarlingGaloisExtension ℚ L)
    (hcyc : IsCyclic (GarlingGaloisGroup ℚ L))
    {k : ℕ} (hcard : Nat.card (GarlingGaloisGroup ℚ L) = 2 ^ k) :
    ∀ z : L, IsConstructible ((ι z).re, (ι z).im) := by
  have _ : Module.Finite ℚ L := (isFiniteExtension_iff_moduleFinite ℚ L).mp hgal.1
  have hfinrankL : Module.finrank ℚ L = 2 ^ k := by
    have h := (theorem_10_4_algEquiv hgal.1).1 hgal
    rw [← h, hcard]
  have _ : Finite (GarlingGaloisGroup ℚ L) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨σ, hσ_gen⟩ := hcyc.exists_generator
  have hordσ : orderOf σ = 2 ^ k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ_gen, hcard]
  -- Descending subgroup chain `H j = ⟨σ^{2^j}⟩` (`H 0 = ⊤`, `H (last k) = ⊥`, `|H j| = 2^{k - j}`):
  let H : Fin (k + 1) → Subgroup (GarlingGaloisGroup ℚ L) :=
    fun j => Subgroup.zpowers (σ ^ (2 ^ j.1))
  have hH0 : H 0 = ⊤ := by
    ext τ
    simp only [H, Fin.val_zero, pow_zero, pow_one, Subgroup.mem_top, iff_true]
    exact hσ_gen τ
  have hHk : H (Fin.last k) = ⊥ := by
    have hpow1 : σ ^ (2 ^ k) = 1 := by rw [← hordσ]; exact pow_orderOf_eq_one σ
    ext τ
    simp only [H, Fin.val_last, hpow1, Subgroup.mem_bot, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨m, hm⟩ => by simpa using hm.symm, fun h => ⟨0, by simp [h]⟩⟩
  have hH_anti : ∀ j : Fin k, H j.succ ≤ H j.castSucc := by
    intro j τ hτ
    rcases Subgroup.mem_zpowers_iff.mp hτ with ⟨m, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨2 * m, ?_⟩
    change (σ ^ (2 ^ j.1)) ^ (2 * m) = (σ ^ (2 ^ (j.1 + 1))) ^ m
    rw [zpow_mul, zpow_ofNat, ← pow_mul, ← pow_succ]
  have hH_card : ∀ j : Fin (k + 1), Nat.card (H j) = 2 ^ (k - j.1) := by
    intro j
    change Nat.card (Subgroup.zpowers (σ ^ (2 ^ j.1))) = 2 ^ (k - j.1)
    rw [Nat.card_zpowers, orderOf_pow, hordσ]
    have hdvd : 2 ^ j.1 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (Nat.le_of_lt_succ j.2)
    rw [Nat.gcd_eq_right hdvd, Nat.pow_div (Nat.le_of_lt_succ j.2) (by omega)]
  -- Ascending fixed-field tower `F j = (fixedField (H j)).map ι ⊆ ℂ`:
  let F : Fin (k + 1) → IntermediateField ℚ ℂ :=
    fun j => (IntermediateField.fixedField (H j)).map ι
  have hF_finrank : ∀ j : Fin (k + 1), Module.finrank ℚ (F j) = 2 ^ j.1 := by
    intro j
    let M : IntermediateField ℚ L := IntermediateField.fixedField (H j)
    have hM_fin : Module.finrank M L = 2 ^ (k - j.1) := by
      have h := IntermediateField.finrank_fixedField_eq_card (H j)
      exact h.trans (hH_card j)
    have hpow_mul : Module.finrank ℚ L = 2 ^ j.1 * 2 ^ (k - j.1) := by
      rw [hfinrankL, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ j.2)]
    let e : M ≃+* F j :=
      { toFun := fun x => ⟨ι x.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y => ⟨y.2.choose, y.2.choose_spec.1⟩
        left_inv := fun x => Subtype.ext (ι.injective
          ((⟨x.1, x.2, rfl⟩ : ∃ a ∈ M, ι a = ι x.1).choose_spec.2))
        right_inv := fun y => Subtype.ext y.2.choose_spec.2
        map_mul' := fun x y => Subtype.ext (map_mul ι x.1 y.1)
        map_add' := fun x y => Subtype.ext (map_add ι x.1 y.1) }
    exact @finrank_rat_of_sub_finrank_equiv M L (F j) _ _ _ M.algebra' _ _ _ _
      e (2 ^ j.1) (2 ^ (k - j.1)) hM_fin hpow_mul (by positivity)
  have hF0 : F 0 = ⊥ := by
    have hfr : Module.finrank ℚ (F 0) = 1 := by simpa using hF_finrank 0
    have _ : Module.Finite ℚ (F 0) := Module.finite_of_finrank_pos (by omega)
    rw [eq_bot_iff]
    intro x hx
    by_contra hx_not_bot
    let w : Fin 2 → F 0 := ![1, ⟨x, hx⟩]
    have hw_li : LinearIndependent ℚ w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hval := congrArg Subtype.val hc
      rw [Fin.sum_univ_two] at hval
      have hcoe_smul : ∀ (q : ℚ) (u : F 0), ((q • u : F 0) : ℂ) = (q : ℂ) * (u : ℂ) := by
        intro q u
        rw [Algebra.smul_def, IntermediateField.coe_mul, eq_ratCast (algebraMap ℚ (F 0)) q,
          ← IntermediateField.coe_val, map_ratCast (F 0).val]
      have hsum : (c 0 : ℂ) + (c 1 : ℂ) * x = 0 := by
        simpa [w, hcoe_smul, Rat.smul_def] using hval
      have hc1 : c 1 = 0 := by
        by_contra hne
        have hneC : (c 1 : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hne
        have hx_eq : x = ((-(c 0) / c 1 : ℚ) : ℂ) := by
          push_cast; field_simp [hneC]; linear_combination hsum
        have hx_bot : x ∈ (⊥ : IntermediateField ℚ ℂ) := by
          rw [hx_eq, ← eq_ratCast (algebraMap ℚ ℂ) (-(c 0) / c 1)]
          exact (⊥ : IntermediateField ℚ ℂ).algebraMap_mem _
        exact hx_not_bot hx_bot
      have hc0 : c 0 = 0 := by
        rw [hc1, Rat.cast_zero, zero_mul, add_zero] at hsum
        exact Rat.cast_eq_zero.mp hsum
      intro i; fin_cases i
      · exact hc0
      · exact hc1
    have hle2 : 2 ≤ Module.finrank ℚ (F 0) := by
      simpa using hw_li.fintype_card_le_finrank
    omega
  have hmono : ∀ j : Fin k, F j.castSucc ≤ F j.succ := by
    intro j
    exact IntermediateField.map_mono ι (IntermediateField.fixedField_antitone (hH_anti j))
  have hdeg : ∀ j : Fin k,
      let _ : Algebra (F j.castSucc) (F j.succ) := (IntermediateField.inclusion (hmono j)).toAlgebra
      Module.finrank (F j.castSucc) (F j.succ) = 2 := by
    intro j
    let _ : Algebra (F j.castSucc) (F j.succ) := (IntermediateField.inclusion (hmono j)).toAlgebra
    have _ : IsScalarTower ℚ (F j.castSucc) (F j.succ) :=
      IsScalarTower.of_algebraMap_eq fun q => Subtype.ext (by
        change ((algebraMap ℚ (F j.succ) q : F j.succ) : ℂ) =
          ((algebraMap ℚ (F j.castSucc) q : F j.castSucc) : ℂ)
        rw [eq_ratCast (algebraMap ℚ (F j.succ)) q, eq_ratCast (algebraMap ℚ (F j.castSucc)) q,
          ← IntermediateField.coe_val, ← IntermediateField.coe_val,
          map_ratCast (F j.succ).val, map_ratCast (F j.castSucc).val])
    have htower := Module.finrank_mul_finrank ℚ (F j.castSucc) (F j.succ)
    rw [hF_finrank j.castSucc, hF_finrank j.succ] at htower
    have hpow : 2 ^ j.succ.1 = 2 ^ j.castSucc.1 * 2 := by
      change 2 ^ (j.1 + 1) = 2 ^ j.1 * 2
      rw [pow_succ]
    rw [hpow] at htower
    exact Nat.eq_of_mul_eq_mul_left (by positivity) htower
  have hall := section_19_3_complex_quadratic_tower_constructible F hF0 hmono hdeg
  intro z
  apply hall (ι z)
  refine ⟨z, ?_, rfl⟩
  rw [hHk]
  intro ⟨τ, hτ⟩
  change τ z = z
  rw [Subgroup.mem_bot.mp hτ]
  rfl

/-- **Theorem 19.8** (§19.3, printed p. 153 / PDF p. 161):
*"Suppose that `p` is an odd prime. Then `n = p^b` is possible if and only if `b = 1` and `p` is of
the form `2^k + 1`."*

Proved **literally for every odd prime `p` and every `b : ℕ`** (including `b = 0`, where `p^0 = 1`
is not possible under `IsPossible`'s `2 < n` definition), following Garling's p. 153 proof via
`Chapter06.theorem_6_1`, `Chapter15.theorem_15_3`, `Chapter15.theorem_15_4`, and
`Chapter15.corollary_to_theorem_15_4`. -/
theorem theorem_19_8 {p b : ℕ} (hp : Nat.Prime p) (hp_odd : Odd p) :
    IsPossible (p ^ b) ↔ b = 1 ∧ ∃ k : ℕ, p = 2 ^ k + 1 := by
  have hp_ne2 : p ≠ 2 := by
    intro h2; rw [h2] at hp_odd; exact Nat.not_odd_iff_even.mpr even_two hp_odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  constructor
  · -- `⇒`: use `Theorem 6.1`, adjoining `i`, and `Theorem 15.3`:
    intro hposs
    have hpb2 : 2 < p ^ b := hposs.1
    have hb1 : 1 ≤ b := by
      by_contra h0
      have hb0 : b = 0 := by omega
      rw [hb0, pow_zero] at hpb2; omega
    have hpt : IsConstructible (xN (p ^ b), yN (p ^ b)) :=
      ((isPossible_iff_constructible_point hpb2).1).mp hposs
    obtain ⟨hfin_xy, r, _, hfr_xy⟩ := Chapter06.theorem_6_1 hpt
    -- Embed `ℚ(x_n, y_n) ⊆ ℝ` into `ℂ`:
    let R0 : IntermediateField ℚ ℂ :=
      (ratPointField (xN (p ^ b)) (yN (p ^ b))).map (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    have hR0_fr : Module.finrank ℚ R0 = 2 ^ r := by
      let eR : ratPointField (xN (p ^ b)) (yN (p ^ b)) ≃ₗ[ℚ] R0 :=
        ratLinearEquivOfRingEquiv
          (IntermediateField.equivMap (ratPointField (xN (p ^ b)) (yN (p ^ b)))
            (IsScalarTower.toAlgHom ℚ ℝ ℂ)).toRingEquiv
      rw [← LinearEquiv.finrank_eq eR, hfr_xy]
    have hR0_real : ∀ w ∈ R0, w.im = 0 := by
      rintro _ ⟨u, _, rfl⟩
      exact Complex.ofReal_im u
    have hx_R0 : (xN (p ^ b) : ℂ) ∈ R0 :=
      ⟨xN (p ^ b), IntermediateField.subset_adjoin ℚ _ (Or.inl rfl), rfl⟩
    have hy_R0 : (yN (p ^ b) : ℂ) ∈ R0 :=
      ⟨yN (p ^ b), IntermediateField.subset_adjoin ℚ _ (Or.inr rfl), rfl⟩
    -- Build `R1 = R0 + R0 * i ⊆ ℂ` of degree `2` over `R0`, so `[R1 : ℚ] = 2^{r+1}`:
    let R1 : IntermediateField ℚ ℂ :=
      { carrier := {z : ℂ | ∃ a b : R0, z = a.1 + b.1 * Complex.I}
        mul_mem' := by
          rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
          refine ⟨⟨a₁.1 * a₂.1 - b₁.1 * b₂.1, R0.sub_mem (R0.mul_mem a₁.2 a₂.2) (R0.mul_mem b₁.2 b₂.2)⟩,
            ⟨a₁.1 * b₂.1 + b₁.1 * a₂.1, R0.add_mem (R0.mul_mem a₁.2 b₂.2) (R0.mul_mem b₁.2 a₂.2)⟩, ?_⟩
          ring_nf; rw [Complex.I_sq]; ring
        add_mem' := by
          rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
          refine ⟨⟨a₁.1 + a₂.1, R0.add_mem a₁.2 a₂.2⟩, ⟨b₁.1 + b₂.1, R0.add_mem b₁.2 b₂.2⟩, ?_⟩
          ring
        zero_mem' := ⟨0, 0, by simp⟩
        one_mem' := ⟨1, 0, by simp⟩
        inv_mem' := by
          rintro z ⟨a, b, rfl⟩
          by_cases hz0 : a.1 + b.1 * Complex.I = 0
          · rw [hz0, inv_zero]; exact ⟨0, 0, by simp⟩
          · have hden_ne : a.1 ^ 2 + b.1 ^ 2 ≠ 0 := by
              intro h0
              have ha_re : a.1 = (a.1.re : ℂ) := Complex.ext rfl (hR0_real a.1 a.2)
              have hb_re : b.1 = (b.1.re : ℂ) := Complex.ext rfl (hR0_real b.1 b.2)
              have hre0 : a.1.re ^ 2 + b.1.re ^ 2 = 0 := by
                have := congrArg Complex.re h0
                rw [ha_re, hb_re] at this
                simpa [sq] using this
              have ha0 : a.1.re = 0 := by nlinarith
              have hb0 : b.1.re = 0 := by nlinarith
              apply hz0
              rw [ha_re, hb_re, ha0, hb0]; simp
            have hden_mem : a.1 ^ 2 + b.1 ^ 2 ∈ R0 :=
              R0.add_mem (pow_mem a.2 2) (pow_mem b.2 2)
            refine ⟨⟨a.1 / (a.1 ^ 2 + b.1 ^ 2), R0.div_mem a.2 hden_mem⟩,
              ⟨-b.1 / (a.1 ^ 2 + b.1 ^ 2), R0.div_mem (R0.neg_mem b.2) hden_mem⟩, ?_⟩
            apply inv_eq_of_mul_eq_one_right
            field_simp [hden_ne]
            linear_combination -(b.1 ^ 2) * Complex.I_sq
        algebraMap_mem' := fun q => ⟨⟨algebraMap ℚ ℂ q, R0.algebraMap_mem q⟩, 0, by simp⟩ }
    have hR01 : R0 ≤ R1 := fun w hw => ⟨⟨w, hw⟩, 0, by simp⟩
    have hR1_fr : Module.finrank ℚ R1 = 2 ^ (r + 1) := by
      let _ : Algebra R0 R1 := (IntermediateField.inclusion hR01).toAlgebra
      have halgR01 : ∀ u : R0, ((algebraMap R0 R1 u : R1) : ℂ) = (u : ℂ) := fun _ => rfl
      have _ : IsScalarTower ℚ R0 R1 :=
        IsScalarTower.of_algebraMap_eq fun q => Subtype.ext (by
          change ((algebraMap ℚ R1 q : R1) : ℂ) = ((algebraMap ℚ R0 q : R0) : ℂ)
          rw [eq_ratCast (algebraMap ℚ R1) q, eq_ratCast (algebraMap ℚ R0) q,
            ← IntermediateField.coe_val, ← IntermediateField.coe_val,
            map_ratCast R1.val, map_ratCast R0.val])
      have hI_R1 : Complex.I ∈ R1 := ⟨0, 1, by simp⟩
      let w : Fin 2 → R1 := ![1, ⟨Complex.I, hI_R1⟩]
      have hw_li : LinearIndependent R0 w := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hval := congrArg Subtype.val hc
        rw [Fin.sum_univ_two] at hval
        have hsum : (c 0 : ℂ) + (c 1 : ℂ) * Complex.I = 0 := by
          simpa [w, Algebra.smul_def, halgR01] using hval
        have hre : (c 0 : ℂ).re = 0 := by
          have := congrArg Complex.re hsum
          simp [hR0_real (c 1).1 (c 1).2] at this
          exact this
        have him : (c 1 : ℂ).re = 0 := by
          have := congrArg Complex.im hsum
          simp [hR0_real (c 0).1 (c 0).2] at this
          exact this
        intro i; fin_cases i
        · exact Subtype.ext (Complex.ext hre (hR0_real (c 0).1 (c 0).2))
        · exact Subtype.ext (Complex.ext him (hR0_real (c 1).1 (c 1).2))
      have hw_span : Submodule.span R0 (Set.range w) = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨z, a, b, rfl⟩ _
        have h1 : (⟨a.1 + b.1 * Complex.I, ⟨a, b, rfl⟩⟩ : R1) = a • w 0 + b • w 1 := by
          apply Subtype.ext; simp [w, Algebra.smul_def, halgR01]
        rw [h1]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
      have hB : Module.Basis (Fin 2) R0 R1 := Module.Basis.mk hw_li (le_of_eq hw_span.symm)
      have hR01_fr : Module.finrank R0 R1 = 2 := by rw [Module.finrank_eq_card_basis hB, Fintype.card_fin]
      have htower := Module.finrank_mul_finrank ℚ R0 R1
      rw [hR0_fr, hR01_fr, ← pow_succ] at htower
      exact htower.symm
    -- `ε_n = x_n + i y_n ∈ R1`, so `ℚ(ε_n) ≤ R1` and `[ℚ(ε_n) : ℚ] ∣ 2^{r+1}`:
    let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({epsN (p ^ b)} : Set ℂ)
    have hε_R1 : epsN (p ^ b) ∈ R1 := by
      rw [epsN_eq_cos_add_sin_mul_I]
      exact ⟨⟨xN (p ^ b), hx_R0⟩, ⟨yN (p ^ b), hy_R0⟩, rfl⟩
    have hER1 : E ≤ R1 := IntermediateField.adjoin_le_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]; exact hε_R1
    let _ : Algebra E R1 := (IntermediateField.inclusion hER1).toAlgebra
    have _ : IsScalarTower ℚ E R1 :=
      IsScalarTower.of_algebraMap_eq fun q => Subtype.ext (by
        change ((algebraMap ℚ R1 q : R1) : ℂ) = ((algebraMap ℚ E q : E) : ℂ)
        rw [eq_ratCast (algebraMap ℚ R1) q, eq_ratCast (algebraMap ℚ E) q,
          ← IntermediateField.coe_val, ← IntermediateField.coe_val,
          map_ratCast R1.val, map_ratCast E.val])
    have hE_dvd : Module.finrank ℚ E ∣ 2 ^ (r + 1) := by
      have htower := Module.finrank_mul_finrank ℚ E R1
      rw [hR1_fr] at htower
      exact ⟨Module.finrank E R1, htower.symm⟩
    -- Compute `[ℚ(ε_n) : ℚ] = φ(p^b) = p^{b-1}(p - 1)` using `Chapter15.theorem_15_3`:
    have hε_prim : IsPrimitiveRoot (epsN (p ^ b)) (p ^ b) :=
      (isPrimitiveRoot_epsN (by omega : p ^ b ≠ 0)).1
    have hcyc_irr : Irreducible (Polynomial.cyclotomic (p ^ b) ℚ) :=
      (Garling.Chapter15.theorem_15_3 (by omega : 1 ≤ p ^ b)).1
    have hcyc_mon : (Polynomial.cyclotomic (p ^ b) ℚ).Monic :=
      Polynomial.cyclotomic.monic (p ^ b) ℚ
    have hcyc_root : Polynomial.aeval (epsN (p ^ b)) (Polynomial.cyclotomic (p ^ b) ℚ) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact hε_prim.isRoot_cyclotomic (by omega : 0 < p ^ b)
    have hmin_eq : minpoly ℚ (epsN (p ^ b)) = Polynomial.cyclotomic (p ^ b) ℚ :=
      (minpoly.eq_of_irreducible_of_monic hcyc_irr hcyc_root hcyc_mon).symm
    have hint : IsIntegral ℚ (epsN (p ^ b)) := ⟨_, hcyc_mon, hcyc_root⟩
    have hE_fr : Module.finrank ℚ E = p ^ (b - 1) * (p - 1) := by
      have h1 : Module.finrank ℚ E = (minpoly ℚ (epsN (p ^ b))).natDegree := by
        -- Bridge `E.algebra'` (used by `IntermediateField.adjoin.finrank`) to `DivisionRing.toRatAlgebra`:
        have hraw := IntermediateField.adjoin.finrank hint
        let e : E ≃ₗ[ℚ] ℚ⟮epsN (p ^ b)⟯ :=
          @ratLinearEquivOfRingEquiv E ℚ⟮epsN (p ^ b)⟯ _ _ _ ℚ⟮epsN (p ^ b)⟯.algebra' (RingEquiv.refl E)
        rw [LinearEquiv.finrank_eq e]
        exact hraw
      rw [h1, hmin_eq, Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hp (by omega)]
    rw [hE_fr] at hE_dvd
    have hb_eq1 : b = 1 := by
      by_contra hne1
      have hb2 : 2 ≤ b := by omega
      have hp_dvd : p ∣ 2 ^ (r + 1) := by
        have h1 : p ∣ p ^ (b - 1) := dvd_pow_self p (by omega)
        exact (h1.trans (dvd_mul_right _ _)).trans hE_dvd
      have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd
      have := Nat.le_of_dvd (by omega) hp_dvd2
      omega
    subst hb_eq1
    simp only [Nat.sub_self, pow_zero, one_mul] at hE_dvd
    obtain ⟨k, _, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hE_dvd
    exact ⟨rfl, k, by omega⟩
  · -- `⇐`: `b = 1` and `p = 2^k + 1` prime; apply `Corollary` to `Theorem 15.4` + quadratic tower:
    rintro ⟨rfl, k, hp_eq⟩
    rw [pow_one]
    have hp2 : 2 < p := by omega
    rw [(isPossible_iff_constructible_point hp2).1]
    let L := (Polynomial.cyclotomic p ℚ).SplittingField
    have hsf : IsGarlingSplittingFieldExtension ℚ L (Polynomial.cyclotomic p ℚ) :=
      (isGarlingSplittingFieldExtension_iff ℚ L _).mpr inferInstance
    have hcharQ : ¬ (ringChar ℚ ∣ p) := by
      rw [ringChar.eq_zero, zero_dvd_iff]; exact hp.ne_zero
    have hsf_X : IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ p - 1) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharQ).1.mp hsf
    have hgal : IsGarlingGaloisExtension ℚ L :=
      (Garling.Chapter15.section_15_1_roots_group_cyclic hcharQ hsf_X).1
    have hcyc : IsCyclic (GarlingGaloisGroup ℚ L) :=
      (Garling.Chapter15.corollary_to_theorem_15_4 hp hsf).2.2
    have hcard : Nat.card (GarlingGaloisGroup ℚ L) = 2 ^ k := by
      have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
        (Garling.Chapter15.theorem_15_3 hp.pos).1
      obtain ⟨_, _, hirr_iso, _, _⟩ := Garling.Chapter15.theorem_15_4 hcharQ hsf
      obtain ⟨e⟩ := hirr_iso.mp hirr
      have _ : NeZero p := ⟨hp.ne_zero⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime hp]
      omega
    let ι : L →ₐ[ℚ] ℂ :=
      Polynomial.IsSplittingField.lift L (Polynomial.cyclotomic p ℚ) (IsAlgClosed.splits _)
    obtain ⟨ζ, hζ_gar⟩ := Garling.Chapter15.exists_isGarlingPrimitiveRoot_of_splittingField hcharQ hsf_X
    have hζ : IsPrimitiveRoot ζ p :=
      (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hp.pos ζ).mp hζ_gar
    have hιζ : IsPrimitiveRoot (ι ζ) p := hζ.map_of_injective ι.injective
    have hε : IsPrimitiveRoot (epsN p) p := (isPrimitiveRoot_epsN hp.ne_zero).1
    have _ : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨m, _, hm⟩ := hιζ.eq_pow_of_pow_eq_one hε.pow_eq_one
    have hconst := complex_constructible_of_cyclic_pow_two_galois ι hgal hcyc hcard (ζ ^ m)
    rw [map_pow, hm, epsN_re, epsN_im] at hconst
    exact hconst

/-- **§19.3 Inline prose definition — *Fermat prime*** (printed pp. 153–154 / PDF pp. 161–162):
A prime of the form `2^k + 1` with `1 ≤ k` (excluding `k = 0`, where `2^0 + 1 = 2` is neither odd
nor of the form `2^(2^l) + 1`, matching `Theorem 19.8` and Garling's p. 154 list starting at `3`). -/
def IsFermatPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, 1 ≤ k ∧ p = 2 ^ k + 1

/-- Remark explaining why `1 ≤ k` is built into `IsFermatPrime`: at `k = 0`, `2^0 + 1 = 2` is prime,
yet `0` is not of the form `2^l` (p. 154 l. 1). -/
theorem section_19_3_fermat_prime_k0_remark :
    Nat.Prime (2 ^ 0 + 1) ∧ 2 ^ 0 + 1 = 2 ∧ ¬ IsFermatPrime 2 ∧ ¬ ∃ l : ℕ, 0 = 2 ^ l := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rintro ⟨_, k, hk, hEq⟩
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  · rintro ⟨l, hl⟩
    have hpos : 0 < 2 ^ l := by positivity
    omega

/-- **§19.3 Prose Theorem — Fermat-prime exponent is a power of 2** (printed p. 154 / PDF p. 162):
*"If `2^k + 1` is a Fermat prime, `k` must be of the form `2^l`: for if `k = st`, with `s` odd and
greater than `1`, `2^k + 1 = 2^{st} + 1 = (2^t + 1)(2^{t(s-1)} - 2^{t(s-2)} + ⋯ + 1)`."* -/
theorem section_19_3_fermat_prime_exponent_pow_two {k : ℕ} (hk : 1 ≤ k)
    (hp : Nat.Prime (2 ^ k + 1)) : ∃ l : ℕ, k = 2 ^ l := by
  obtain ⟨l, s, hs_odd, hk_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  by_cases hs1 : s = 1
  · exact ⟨l, by rw [hk_eq, hs1, mul_one]⟩
  · exfalso
    -- Since `s` is odd and `s ≠ 1`, `s ≥ 3`, and `(a + 1) ∣ (a^s + 1)` for `a = 2^(2^l)`:
    have hodd_dvd : ∀ (a m : ℕ), Odd m → (a + 1 : ℕ) ∣ a ^ m + 1 := by
      intro a m hm
      rcases hm with ⟨j, rfl⟩
      induction j with
      | zero => simp
      | succ j ih =>
        have hZ : ((a + 1 : ℕ) : ℤ) ∣ ((a ^ (2 * (j + 1) + 1) + 1 : ℕ) : ℤ) := by
          obtain ⟨q, hq⟩ := ih
          have hqZ : ((a ^ (2 * j + 1) + 1 : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) * (q : ℤ) := by
            exact_mod_cast hq
          refine ⟨(a : ℤ) ^ 2 * q - ((a : ℤ) - 1), ?_⟩
          have hpow : ((a ^ (2 * (j + 1) + 1) + 1 : ℕ) : ℤ) =
              (a : ℤ) ^ 2 * ((a ^ (2 * j + 1) + 1 : ℕ) : ℤ) - ((a : ℤ) ^ 2 - 1) := by
            push_cast; ring
          rw [hpow, hqZ]
          push_cast
          ring
        exact Int.ofNat_dvd.mp hZ
    let a := 2 ^ (2 ^ l)
    have hdvd : a + 1 ∣ 2 ^ k + 1 := by
      have hpow : 2 ^ k = a ^ s := by
        rw [hk_eq, pow_mul]
      rw [hpow]
      exact hodd_dvd a s hs_odd
    have ha_gt1 : 1 < a + 1 := by
      have : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
      have : 2 ≤ a := by
        have h1 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 ^ l) := Nat.pow_le_pow_right (by omega) h1
      omega
    have ha_lt : a + 1 < 2 ^ k + 1 := by
      have hs3 : 2 ≤ s := by
        rcases hs_odd with ⟨j, rfl⟩
        omega
      have hk_gt : 2 ^ l < k := by
        have hpos : 0 < 2 ^ l := by positivity
        nlinarith
      have : 2 ^ (2 ^ l) < 2 ^ k := Nat.pow_lt_pow_right (by omega) hk_gt
      omega
    rcases hp.eq_one_or_self_of_dvd (a + 1) hdvd with h1 | hself <;> omega

theorem isFermatPrime_iff_pow_two_pow (p : ℕ) :
    IsFermatPrime p ↔ Nat.Prime p ∧ ∃ l : ℕ, p = 2 ^ (2 ^ l) + 1 := by
  constructor
  · rintro ⟨hp, k, hk, rfl⟩
    obtain ⟨l, rfl⟩ := section_19_3_fermat_prime_exponent_pow_two hk hp
    exact ⟨hp, l, rfl⟩
  · rintro ⟨hp, l, rfl⟩
    exact ⟨hp, 2 ^ l, Nat.one_le_pow _ _ (by omega), rfl⟩

theorem isFermatPrime_iff_odd_prime (p : ℕ) :
    IsFermatPrime p ↔ Nat.Prime p ∧ Odd p ∧ ∃ k : ℕ, p = 2 ^ k + 1 := by
  constructor
  · rintro ⟨hp, k, hk, rfl⟩
    refine ⟨hp, ?_, k, rfl⟩
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    rcases h2 with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨hp, hodd, k, rfl⟩
    refine ⟨hp, k, ?_, rfl⟩
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hodd
    exact Nat.not_odd_iff_even.mpr even_two hodd

/-- §19.3 prose remark (p. 154): all five known Fermat primes `3, 5, 17, 257, 65537` are Fermat
primes (`l = 0, 1, 2, 3, 4`). Proved purely in-kernel via `norm_num` (zero `native_decide`). -/
theorem section_19_3_known_fermat_primes :
    IsFermatPrime 3 ∧ IsFermatPrime 5 ∧ IsFermatPrime 17 ∧
    IsFermatPrime 257 ∧ IsFermatPrime 65537 := by
  refine ⟨⟨by norm_num, 1, by omega, by norm_num⟩,
    ⟨by norm_num, 2, by omega, by norm_num⟩,
    ⟨by norm_num, 4, by omega, by norm_num⟩,
    ⟨by norm_num, 8, by omega, by norm_num⟩,
    ⟨by norm_num, 16, by omega, by norm_num⟩⟩

/-- Remark documenting p. 154 l. 5's variable slip (`k = 0, 1, 2, 3 and 4` for `l = 0, 1, 2, 3 and 4`). -/
theorem section_19_3_p154_k_for_l_typo_remark :
    (2 ^ 0 + 1 = 2 ∧ 2 ^ 3 + 1 = 9 ∧ ¬ Nat.Prime 9) ∧
    (2 ^ (2 ^ 0) + 1 = 3 ∧ 2 ^ (2 ^ 1) + 1 = 5 ∧ 2 ^ (2 ^ 2) + 1 = 17 ∧
      2 ^ (2 ^ 3) + 1 = 257 ∧ 2 ^ (2 ^ 4) + 1 = 65537) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- **Counterexamples to literal unguarded `Theorem 19.9 (Gauss)`** (`QUEUE.md` hold, p. 154):
Omitting §19.3's standing `2 < n` while allowing `r = 0` (required for `n = 4, 8, …`) and `t ≥ 0`
makes `n = 1 = 2^0` and `n = 2 = 2^1` satisfy the RHS while `¬ IsPossible 1` and `¬ IsPossible 2`. -/
theorem theorem_19_9_n1_n2_counterexamples :
    ((∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ 1 = 2 ^ t * ∏ p ∈ P, p) ∧
      ¬ IsPossible 1) ∧
    ((∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ 2 = 2 ^ t * ∏ p ∈ P, p) ∧
      ¬ IsPossible 2) := by
  exact ⟨⟨⟨0, ∅, by simp, by simp⟩, isPossible_n1_n2_false.1⟩,
    ⟨⟨1, ∅, by simp, by simp⟩, isPossible_n1_n2_false.2.1⟩⟩

/-- **Theorem 19.9 (Gauss) (Repaired with standing `2 < n`)** (§19.3, printed p. 154 / PDF p. 162):
*"It is possible to construct a regular polygon with `n` sides [`n > 2`] if and only if `n` is of
the form `2^t p_1 ⋯ p_r`, where `t ≥ 0` and `p_1, …, p_r` are distinct Fermat primes."*

Proved in both `Finset ℕ` and injective `Fin r → ℕ` distinct-tuple forms. -/
theorem theorem_19_9_repaired {n : ℕ} (hn2 : 2 < n) :
    (IsPossible n ↔
      ∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ n = 2 ^ t * ∏ p ∈ P, p) ∧
    (IsPossible n ↔
      ∃ (t r : ℕ) (p : Fin r → ℕ), Function.Injective p ∧
        (∀ i : Fin r, IsFermatPrime (p i)) ∧ n = 2 ^ t * ∏ i : Fin r, p i) := by
  have hfinset : IsPossible n ↔
      ∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ n = 2 ^ t * ∏ p ∈ P, p := by
    constructor
    · intro hposs
      let P : Finset ℕ := n.primeFactors.erase 2
      let t : ℕ := n.factorization 2
      let e : Fin P.card ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
      let p : Fin P.card → ℕ := fun i => (e i).1
      let a : Fin P.card → ℕ := fun i => n.factorization (p i)
      have hp_mem : ∀ i : Fin P.card, p i ∈ n.primeFactors ∧ p i ≠ 2 := fun i => by
        have h := Finset.mem_erase.mp (e i).2
        exact ⟨h.2, h.1⟩
      have hp_prime : ∀ i : Fin P.card, Nat.Prime (p i) :=
        fun i => Nat.prime_of_mem_primeFactors (hp_mem i).1
      have hp_odd : ∀ i : Fin P.card, Odd (p i) := fun i =>
        (hp_prime i).odd_of_ne_two (hp_mem i).2
      have hp_inj : Function.Injective p := fun i j hEq =>
        e.injective (Subtype.ext hEq)
      have hn_eq : n = 2 ^ t * ∏ i : Fin P.card, (p i) ^ (a i) := by
        have hprod_all : (∏ q ∈ n.primeFactors, q ^ n.factorization q) = n := by
          have h := Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)
          rwa [Finsupp.prod, Nat.support_factorization] at h
        have hsplit : (∏ q ∈ n.primeFactors, q ^ n.factorization q) =
            2 ^ t * ∏ q ∈ P, q ^ n.factorization q := by
          by_cases h2 : 2 ∈ n.primeFactors
          · exact (Finset.mul_prod_erase n.primeFactors (fun q => q ^ n.factorization q) h2).symm
          · have ht0 : t = 0 := Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
              h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, by omega⟩))
            rw [ht0, pow_zero, one_mul, show P = n.primeFactors from Finset.erase_eq_of_notMem h2]
        have hreindex : (∏ q ∈ P, q ^ n.factorization q) = ∏ i : Fin P.card, (p i) ^ (a i) := by
          rw [← Finset.prod_coe_sort P (fun q => q ^ n.factorization q)]
          exact (Equiv.prod_comp e (fun q : P => (q : ℕ) ^ n.factorization (q : ℕ))).symm
        rw [← hreindex, ← hsplit, hprod_all]
      have h197 := (theorem_19_7_repaired hn2 hp_prime hp_odd hp_inj hn_eq).mp hposs
      have ha_eq1 : ∀ i : Fin P.card, a i = 1 ∧ IsFermatPrime (p i) := by
        intro i
        have hai_pos : 1 ≤ a i :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
            rw [Nat.support_factorization]; exact (hp_mem i).1))
        have hposs_i : IsPossible ((p i) ^ (a i)) := h197 i (a i) hai_pos le_rfl
        obtain ⟨ha1, k, hk⟩ := (theorem_19_8 (hp_prime i) (hp_odd i)).mp hposs_i
        exact ⟨ha1, (isFermatPrime_iff_odd_prime (p i)).mpr ⟨hp_prime i, hp_odd i, k, hk⟩⟩
      refine ⟨t, P, ?_, ?_⟩
      · intro q hq
        have h := ha_eq1 (e.symm ⟨q, hq⟩)
        simpa [p] using h.2
      · rw [hn_eq]
        congr 1
        have hreindex1 : (∏ q ∈ P, q) = ∏ i : Fin P.card, p i := by
          rw [← Finset.prod_coe_sort P (fun q => q)]
          exact (Equiv.prod_comp e (fun q : P => (q : ℕ))).symm
        rw [hreindex1]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [(ha_eq1 i).1, pow_one]
    · rintro ⟨t, P, hP, hn_eq⟩
      let e : Fin P.card ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
      let p : Fin P.card → ℕ := fun i => (e i).1
      let a : Fin P.card → ℕ := fun _ => 1
      have hp_ferm : ∀ i : Fin P.card, IsFermatPrime (p i) := fun i => hP (e i).1 (e i).2
      have hp_prime : ∀ i : Fin P.card, Nat.Prime (p i) := fun i => (hp_ferm i).1
      have hp_odd : ∀ i : Fin P.card, Odd (p i) :=
        fun i => ((isFermatPrime_iff_odd_prime (p i)).mp (hp_ferm i)).2.1
      have hp_inj : Function.Injective p := fun i j hEq => e.injective (Subtype.ext hEq)
      have hn_eq' : n = 2 ^ t * ∏ i : Fin P.card, (p i) ^ (a i) := by
        rw [hn_eq]
        congr 1
        rw [← Finset.prod_coe_sort P (fun q => q)]
        simpa [p, a] using (Equiv.prod_comp e (fun q : P => (q : ℕ))).symm
      refine (theorem_19_7_repaired hn2 hp_prime hp_odd hp_inj hn_eq').mpr fun i b hb1 hba => ?_
      have hb_eq1 : b = 1 := by dsimp [a] at hba; omega
      obtain ⟨_, _, k, hk⟩ := (isFermatPrime_iff_odd_prime (p i)).mp (hp_ferm i)
      exact (theorem_19_8 (hp_prime i) (hp_odd i)).mpr ⟨hb_eq1, k, hk⟩
  refine ⟨hfinset, hfinset.trans ⟨?_, ?_⟩⟩
  · rintro ⟨t, P, hP, hn_eq⟩
    let e : Fin P.card ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
    refine ⟨t, P.card, fun i => (e i).1, fun i j h => e.injective (Subtype.ext h),
      fun i => hP (e i).1 (e i).2, ?_⟩
    rw [hn_eq]
    congr 1
    rw [← Finset.prod_coe_sort P (fun q => q)]
    exact (Equiv.prod_comp e (fun q : P => (q : ℕ))).symm
  · rintro ⟨t, r, p, hp_inj, hp_ferm, hn_eq⟩
    refine ⟨t, Finset.univ.image p, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
      exact hp_ferm i
    · rw [hn_eq, Finset.prod_image (fun i _ j _ h => hp_inj h)]

/-- **Theorem 19.9 (Gauss) (Unconditional characterization across all `n : ℕ`)** (§19.3, p. 154). -/
theorem theorem_19_9_iff (n : ℕ) :
    (IsPossible n ↔
      2 < n ∧ ∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ n = 2 ^ t * ∏ p ∈ P, p) ∧
    (IsPossible n ↔
      ∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ (P = ∅ → 2 ≤ t) ∧
        n = 2 ^ t * ∏ p ∈ P, p) := by
  have h1 : IsPossible n ↔
      2 < n ∧ ∃ (t : ℕ) (P : Finset ℕ), (∀ p ∈ P, IsFermatPrime p) ∧ n = 2 ^ t * ∏ p ∈ P, p := by
    constructor
    · intro h; exact ⟨h.1, (theorem_19_9_repaired h.1).1.mp h⟩
    · rintro ⟨hn2, hex⟩; exact (theorem_19_9_repaired hn2).1.mpr hex
  refine ⟨h1, h1.trans ⟨?_, ?_⟩⟩
  · rintro ⟨hn2, t, P, hP, hn_eq⟩
    refine ⟨t, P, hP, ?_, hn_eq⟩
    intro hPemp
    rw [hPemp, Finset.prod_empty, mul_one] at hn_eq
    by_contra hlt
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl <;> omega
  · rintro ⟨t, P, hP, ht_empty, hn_eq⟩
    refine ⟨?_, t, P, hP, hn_eq⟩
    by_cases hPemp : P = ∅
    · have ht2 := ht_empty hPemp
      rw [hn_eq, hPemp, Finset.prod_empty, mul_one]
      calc 2 < 4 := by omega
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht2
    · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hPemp
      have hq3 : 3 ≤ q := by
        obtain ⟨hqp, hqo, _⟩ := (isFermatPrime_iff_odd_prime q).mp (hP q hq)
        have h2 := hqp.two_le
        have hne2 : q ≠ 2 := fun h2eq => Nat.not_odd_iff_even.mpr even_two (h2eq ▸ hqo)
        omega
      have hprod_ge : q ≤ ∏ p ∈ P, p := by
        have hpos : ∀ p ∈ P, 1 ≤ p := fun p hp => (hP p hp).1.pos
        have h1 : 1 ≤ ∏ p ∈ P.erase q, p := Finset.one_le_prod fun p hp =>
          hpos p (Finset.mem_of_mem_erase hp)
        rw [← Finset.mul_prod_erase P (fun p => p) hq]
        nlinarith
      have h2t_ge : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by omega)
      rw [hn_eq]
      nlinarith

end Garling.Chapter19
