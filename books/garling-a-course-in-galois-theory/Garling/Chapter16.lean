import Garling.Chapter12
import Garling.Chapter14
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Chapter 16: Cyclic extensions

Formalization of Chapter 16 (*Cyclic extensions*, printed pp. 123–130 / PDF pp. 131–138)
of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
3-line unnumbered chapter preamble, all four sections (`§16.1`–`§16.4`), all 7 main-text
theorem/corollary items (`Theorem 16.1`, `Theorem 16.2 (Abel's theorem)`, `Theorem 16.3`,
unnumbered `Corollary` [to `Theorem 16.3`], `Theorem 16.4`, `Theorem 16.5`, `Theorem 16.6`),
all 16 numbered exercises (`Exercise 16.1`–`Exercise 16.16`), and all 5 unnumbered inline prose
definitions (*(`K`-valued) character*, *cyclic* extension, *trace* `tr`, *norm* `N`, and
*Kummer extension of exponent `d`*) plus supporting prose derivations in exact source order.

*(Note: Chapter 15 is formalized on a separate parallel lane and is not imported here; all
root-of-unity and cyclotomic prerequisites used in Chapter 16 are established directly inside this
file from Mathlib and Chapters 1–14.)*
-/

namespace Garling.Chapter16

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter08 Garling.Chapter09
open Garling.Chapter10 Garling.Chapter11 Garling.Chapter12
open Garling.Chapter14
open scoped BigOperators Polynomial IntermediateField Classical

universe u v w

/-! ## §16.1 A necessary condition (printed pp. 123–124, PDF pp. 131–132) -/

/-- Self-contained Chapter 16 predicate for a *primitive `n`th root of unity* (`1 ≤ n`, `ω ^ n = 1`,
and `ω ^ k ≠ 1` for `1 ≤ k < n`; cf. Chapter 15 §15.1, proved equivalent to `1 ≤ n ∧ IsPrimitiveRoot ω n`
below without importing `Chapter15`). -/
def IsGarlingPrimitiveRoot {R : Type*} [Monoid R] (ω : R) (n : ℕ) : Prop :=
  1 ≤ n ∧ ω ^ n = 1 ∧ ∀ k : ℕ, 1 ≤ k → k < n → ω ^ k ≠ 1

/-- Equivalence between `IsGarlingPrimitiveRoot ω n` and `1 ≤ n ∧ IsPrimitiveRoot ω n`. -/
theorem isGarlingPrimitiveRoot_iff {R : Type*} [CommMonoid R] (ω : R) (n : ℕ) :
    IsGarlingPrimitiveRoot ω n ↔ 1 ≤ n ∧ IsPrimitiveRoot ω n := by
  constructor
  · rintro ⟨hn, hpow, hmin⟩
    refine ⟨hn, ?_⟩
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨hpow, fun l hl => ?_⟩
    have hmod : ω ^ (l % n) = 1 := by
      have hdiv := Nat.div_add_mod l n
      have h1 : ω ^ (n * (l / n) + l % n) = 1 := by rwa [hdiv]
      rw [pow_add, pow_mul, hpow, one_pow, one_mul] at h1
      exact h1
    rcases Nat.eq_zero_or_pos (l % n) with hr0 | hrpos
    · exact Nat.dvd_of_mod_eq_zero hr0
    · exact (hmin (l % n) hrpos (Nat.mod_lt l hn) hmod).elim
  · rintro ⟨hn, hprim⟩
    refine ⟨hn, hprim.pow_eq_one, fun k hk1 hkn hkpow => ?_⟩
    have hdvd : n ∣ k := hprim.dvd_of_pow_eq_one k hkpow
    exact not_lt_of_ge (Nat.le_of_dvd hk1 hdvd) hkn

/-- If `char K` does not divide `n` (`¬ (ringChar K ∣ n)`), then `1 ≤ n` and `(n : K) ≠ 0`. -/
theorem pos_and_natCast_ne_zero_of_not_ringChar_dvd {K : Type*} [Field K] {n : ℕ}
    (hchar : ¬ (ringChar K ∣ n)) : 1 ≤ n ∧ (n : K) ≠ 0 := by
  have hn0 : n ≠ 0 := fun h => hchar (h ▸ dvd_zero (ringChar K))
  refine ⟨Nat.one_le_iff_ne_zero.mpr hn0, ?_⟩
  intro hcast
  exact hchar ((ringChar.spec K n).mp hcast)

/-- Conversely, if a field `K` contains a primitive `n`th root of unity (`1 ≤ n`), then
`char K` does not divide `n`. -/
theorem not_ringChar_dvd_of_isPrimitiveRoot {K : Type*} [Field K] {n : ℕ} {ω : K}
    (hn : 1 ≤ n) (hω : IsPrimitiveRoot ω n) : ¬ (ringChar K ∣ n) := by
  intro hdvd
  let p := ringChar K
  have _ : CharP K p := ringChar.charP K
  rcases CharP.char_is_prime_or_zero K p with hp | hp0
  · rcases hdvd with ⟨m, hm⟩
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm; omega
      · exact hpos
    have hm_lt : m < n := by
      have hp2 := hp.two_le
      nlinarith
    have hpowp : (ω ^ m - 1) ^ p = 0 := by
      have _ : Fact p.Prime := ⟨hp⟩
      rw [sub_pow_char, one_pow, ← pow_mul, mul_comm, ← hm, hω.pow_eq_one, sub_self]
    have hωm : ω ^ m = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpowp)
    exact not_lt_of_ge (Nat.le_of_dvd hm_pos (hω.dvd_of_pow_eq_one m hωm)) hm_lt
  · change ringChar K = 0 at hp0
    rw [hp0] at hdvd
    have hn0 : n = 0 := zero_dvd_iff.mp hdvd
    omega

/-- Any splitting field extension of a non-zero Garling-separable polynomial `f ∈ K[X]` is a
Garling Galois extension (`IsGarlingGaloisExtension K L`, §10.3 Corollary 3 to Theorem 10.3). -/
theorem isGarlingGalois_of_splittingField {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (hgsep : IsGarlingSeparablePoly f) :
    IsGarlingGaloisExtension K L := by
  have hsp : Polynomial.IsSplittingField K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mp hsf
  have _ : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
  have hnorm : Normal K L := Normal.of_isSplittingField f
  have hsep_roots : ∀ x ∈ (f.rootSet L : Set L), IsSeparable K x := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    have h_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have hdvd : minpoly K x ∣ f := minpoly.dvd K x hx.2
    exact (isGarlingSeparablePoly_iff _).mp hgsep (minpoly K x) (minpoly.irreducible h_int) hdvd
  have hsep_adj : Algebra.IsSeparable K (IntermediateField.adjoin K (f.rootSet L : Set L)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K L).mpr hsep_roots
  have hadj_top : IntermediateField.adjoin K (f.rootSet L : Set L) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp hsp).2
  let e : IntermediateField.adjoin K (f.rootSet L : Set L) ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hadj_top).trans IntermediateField.topEquiv
  have hsepL : Algebra.IsSeparable K L := AlgEquiv.Algebra.isSeparable e
  rw [isGarlingGaloisExtension_iff]
  exact ⟨inferInstance, @IsGalois.mk K _ L _ _ hsepL hnorm⟩

/-- Polynomial `X ^ n - C θ` over a field `K` with `θ ≠ 0` and `¬ (ringChar K ∣ n)` is monic of
degree `n ≥ 1` and separable (`Polynomial.Separable` and `IsGarlingSeparablePoly`). -/
theorem X_pow_sub_C_separable_of_ne_zero {K : Type*} [Field K] {n : ℕ} {θ : K}
    (hθ : θ ≠ 0) (hchar : ¬ (ringChar K ∣ n)) :
    1 ≤ n ∧
    (Polynomial.X ^ n - Polynomial.C θ).Monic ∧
    (Polynomial.X ^ n - Polynomial.C θ).natDegree = n ∧
    (Polynomial.X ^ n - Polynomial.C θ).Separable ∧
    IsGarlingSeparablePoly (Polynomial.X ^ n - Polynomial.C θ) := by
  obtain ⟨hn, hnK⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have hmonic : (Polynomial.X ^ n - Polynomial.C θ).Monic :=
    Polynomial.monic_X_pow_sub_C θ (Nat.ne_of_gt hn)
  have hdeg : (Polynomial.X ^ n - Polynomial.C θ).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  have hsep : (Polynomial.X ^ n - Polynomial.C θ).Separable :=
    Polynomial.separable_X_pow_sub_C θ hnK hθ
  have hgsep : IsGarlingSeparablePoly (Polynomial.X ^ n - Polynomial.C θ) :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly _).mp hsep).2.2
  exact ⟨hn, hmonic, hdeg, hsep, hgsep⟩

/-- Linear factorization `X ^ n - C (β ^ n) = ∏ k : Fin n, (X - C (ω ^ k * β))` in `L[X]`
whenever `1 ≤ n` and `IsPrimitiveRoot ω n`. -/
theorem X_pow_sub_C_pow_eq_prod {L : Type*} [Field L] {n : ℕ} (hn : 1 ≤ n)
    {ω : L} (hω : IsPrimitiveRoot ω n) (β : L) :
    Polynomial.X ^ n - Polynomial.C (β ^ n) =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * β)) := by
  by_cases hβ : β = 0
  · subst hβ
    rw [zero_pow (Nat.ne_of_gt hn)]
    simp [Finset.prod_const]
  · have hmonL : (Polynomial.X ^ n - Polynomial.C (β ^ n)).Monic :=
      Polynomial.monic_X_pow_sub_C (β ^ n) (Nat.ne_of_gt hn)
    have hmonR : (∏ k : Fin n, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * β))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
    have hinj : Function.Injective (fun k : Fin n => ω ^ (k : ℕ) * β) := by
      intro i j hij
      have hpow : ω ^ (i : ℕ) = ω ^ (j : ℕ) := mul_right_cancel₀ hβ hij
      exact Fin.ext (hω.pow_inj i.isLt j.isLt hpow)
    let S : Finset L := Finset.univ.image (fun k : Fin n => ω ^ (k : ℕ) * β)
    have hdvd : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) ∣
        (Polynomial.X ^ n - Polynomial.C (β ^ n)) := by
      refine Finset.prod_dvd_of_coprime
        (fun x _ y _ hxy => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy) ?_
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨k, _, rfl⟩
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, mul_pow, ← pow_mul,
        mul_comm (k : ℕ) n, pow_mul, hω.pow_eq_one, one_pow, one_mul, sub_self]
    have hprodS : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) =
        ∏ k : Fin n, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * β)) :=
      Finset.prod_image fun i _ j _ hij => hinj hij
    rw [hprodS] at hdvd
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonR hmonL hdvd ?_
    rw [Polynomial.natDegree_X_pow_sub_C,
      Polynomial.natDegree_prod _ _ (fun k _ => Polynomial.X_sub_C_ne_zero _)]
    have h1 : ∀ k : Fin n, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * β)).natDegree = 1 :=
      fun k => Polynomial.natDegree_X_sub_C _
    simp_rw [h1]
    simp

/-- **§16.1 Prose Derivation** (printed p. 123 / PDF p. 131):
For `x^n - θ ∈ K[x]` with `θ ≠ 0` and `¬ (char K ∣ n)` and splitting field extension `L : K`,
`x^n - θ` has `n` distinct roots in `L`, `x^n - 1` splits over `L`, `L` contains a primitive `n`th
root of unity `ω`, and for every root `α₁ ∈ L` of `x^n - θ`,
`x^n - θ = ∏_{k < n} (x - ω^k α₁)`. -/
theorem section_16_1_root_factorization {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {θ : K} (hθ : θ ≠ 0) (hchar : ¬ (ringChar K ∣ n))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C θ)) :
    1 ≤ n ∧
    GarlingSplitsOver K L (Polynomial.X ^ n - 1) ∧
    (∃ ω : L, IsPrimitiveRoot ω n) ∧
    (∃ α₁ : L, Polynomial.aeval α₁ (Polynomial.X ^ n - Polynomial.C θ) = 0) ∧
    (∀ (ω α₁ : L), IsPrimitiveRoot ω n →
      Polynomial.aeval α₁ (Polynomial.X ^ n - Polynomial.C θ) = 0 →
      (Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L) =
        ∏ k : Fin n, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * α₁))) := by
  obtain ⟨hn, hmonic, hdeg, hsep, _⟩ := X_pow_sub_C_separable_of_ne_zero hθ hchar
  have hf0 : (Polynomial.X ^ n - Polynomial.C θ : K[X]) ≠ 0 := hmonic.ne_zero
  have hinjKL : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hmap_sep : ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L)).Separable :=
    hsep.map
  have hsplitsL : ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L)).Splits :=
    (garlingSplitsOver_iff_splits K L _).mp hsf.1
  have hroots_card :
      ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L)).roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hmap_sep),
      ← Polynomial.Splits.natDegree_eq_card_roots hsplitsL,
      Polynomial.natDegree_map_eq_of_injective hinjKL, hdeg]
  let Rset := ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L)).roots.toFinset
  have hR_nonempty : Rset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h0 : Rset.card = 0 := by rw [hemp]; rfl
    have h1 : Rset.card = n := hroots_card
    omega
  obtain ⟨α₁, hα₁_mem⟩ := hR_nonempty
  have hα₁_root : Polynomial.aeval α₁ (Polynomial.X ^ n - Polynomial.C θ) = 0 := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hf0),
      Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hα₁_mem
    exact hα₁_mem
  have hα₁_pow : α₁ ^ n = algebraMap K L θ := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hα₁_root
    exact hα₁_root
  have hα₁_ne : α₁ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.ne_of_gt hn)] at hα₁_pow
    exact hθ (hinjKL (hα₁_pow.symm.trans (map_zero _).symm))
  let Uset : Finset L := Rset.image (fun α => α * α₁⁻¹)
  have hU_card : Uset.card = n := by
    rw [Finset.card_image_of_injective _ (mul_left_injective₀ (inv_ne_zero hα₁_ne)), hroots_card]
  have hU_pow : ∀ u ∈ Uset, u ^ n = 1 := by
    intro u hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨α, hα, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hf0),
      Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
      map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hα
    rw [mul_pow, inv_pow, hα, ← hα₁_pow, mul_inv_cancel₀ (pow_ne_zero n hα₁_ne)]
  let Usub : Finset Lˣ := Uset.attach.image (fun x =>
    Units.mk0 x.1 (by
      intro hx0
      have h1 := hU_pow x.1 x.2
      rw [hx0, zero_pow (Nat.ne_of_gt hn)] at h1
      exact zero_ne_one h1))
  have hUsub_card : Usub.card = n := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_attach, hU_card]
    · intro x y hxy
      ext
      exact congrArg Units.val hxy
  have h_mem_rou : ∀ u ∈ Usub, u ∈ rootsOfUnity n L := by
    intro u hu
    rw [mem_rootsOfUnity]
    rw [Finset.mem_image] at hu
    rcases hu with ⟨x, _, rfl⟩
    ext
    exact hU_pow x.1 x.2
  have hdvd_X_pow_sub_one :
      (Polynomial.X ^ n - 1 : L[X]) = ∏ u ∈ Uset, (Polynomial.X - Polynomial.C u) := by
    have hdvd : (∏ u ∈ Uset, (Polynomial.X - Polynomial.C u)) ∣ (Polynomial.X ^ n - 1 : L[X]) := by
      refine Finset.prod_dvd_of_coprime
        (fun x _ y _ hxy => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy) ?_
      intro u hu
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hU_pow u hu, sub_self]
    have hmon1 : (∏ u ∈ Uset, (Polynomial.X - Polynomial.C u)).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun u _ => Polynomial.monic_X_sub_C u
    have hmon2 : (Polynomial.X ^ n - 1 : L[X]).Monic := by
      simpa using Polynomial.monic_X_pow_sub_C (1 : L) (Nat.ne_of_gt hn)
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon1 hmon2 hdvd ?_
    have hdeg2 : (Polynomial.X ^ n - 1 : L[X]).natDegree = n := by
      simpa using (Polynomial.natDegree_X_pow_sub_C (R := L) (n := n) (r := 1))
    rw [hdeg2, Polynomial.natDegree_prod _ _ (fun u _ => Polynomial.X_sub_C_ne_zero u)]
    simp [hU_card]
  have hsplit_one : GarlingSplitsOver K L (Polynomial.X ^ n - 1) := by
    let eFin : Fin n ≃ Uset := (Fintype.equivFinOfCardEq (by simp [hU_card])).symm
    refine ⟨n, 1, fun j => (eFin j).1, ?_⟩
    rw [GarlingSplitsExplicit, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_one, Polynomial.C_1, one_mul, hdvd_X_pow_sub_one,
      ← Finset.prod_attach Uset]
    exact (Equiv.prod_comp eFin (fun x : Uset => Polynomial.X - Polynomial.C x.1)).symm
  have hex_prim : ∃ ω : L, IsPrimitiveRoot ω n := by
    let G : Subgroup Lˣ := rootsOfUnity n L
    have hG_le : ∀ x : G, (x.1 : L) ∈ Uset := by
      intro x
      have hx1 : (x.1 : L) ^ n = 1 := by
        have hx : x.1 ^ n = 1 := (mem_rootsOfUnity n x.1).mp x.2
        exact congrArg Units.val hx
      have hroot : Polynomial.eval (x.1 : L) (Polynomial.X ^ n - 1 : L[X]) = 0 := by
        simp [hx1]
      rw [hdvd_X_pow_sub_one, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hroot
      rcases hroot with ⟨u, hu, hux⟩
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hux
      rwa [hux]
    let injG : G ↪ Uset :=
      ⟨fun x => ⟨(x.1 : L), hG_le x⟩, fun x y hxy => by
        ext; exact congrArg Subtype.val hxy⟩
    let _ : Fintype G := Fintype.ofInjective injG injG.injective
    have hcard_le : Fintype.card G ≤ n := by
      simpa [hU_card] using Fintype.card_le_of_injective injG injG.injective
    let invMap : Usub ↪ G :=
      ⟨fun u => ⟨u.1, h_mem_rou u.1 u.2⟩, fun a b hab => by
        ext; exact congrArg (fun g : G => (g.1 : L)) hab⟩
    have hcard_ge : n ≤ Fintype.card G := by
      simpa [hUsub_card] using Fintype.card_le_of_injective invMap invMap.injective
    have hG_card : Nat.card G = n := by
      rw [Nat.card_eq_fintype_card]
      omega
    obtain ⟨_, ⟨g, _, hordG⟩⟩ := theorem_12_3 L G
    rw [hG_card] at hordG
    have hordL : orderOf ((g.1 : Lˣ) : L) = n := by
      rw [orderOf_units, Subgroup.orderOf_coe] at *
      exact hordG
    refine ⟨((g.1 : Lˣ) : L), ?_⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    exact hordL
  refine ⟨hn, hsplit_one, hex_prim, ⟨α₁, hα₁_root⟩, fun ω β hω hβ => ?_⟩
  have hβpow : β ^ n = algebraMap K L θ := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hβ
    exact hβ
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hβpow]
  exact X_pow_sub_C_pow_eq_prod hn hω β

/-- Helper: `ω ^ a = ω ^ b ↔ a ≡ b [MOD n]` for a primitive `n`th root of unity `ω` (`1 ≤ n`). -/
theorem isPrimitiveRoot_pow_eq_pow_iff_modEq {R : Type*} [CommMonoid R] {ω : R} {n : ℕ}
    (hn : 1 ≤ n) (hω : IsPrimitiveRoot ω n) {a b : ℕ} :
    ω ^ a = ω ^ b ↔ a ≡ b [MOD n] := by
  have hfin : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hω.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hω.eq_orderOf]

/-- **Counterexample to literal `Theorem 16.1` at `θ = 0`** (`QUEUE.md` fidelity hold, Flag 1(a)):
At `K = L = ℚ`, `n = 3`, `θ = 0`, `char ℚ = 0` does not divide `3` and `ℚ : ℚ` is a splitting field
extension for `x³ - 0 = x³`, yet `ℚ` contains **no** primitive `3`rd root of unity. -/
theorem theorem_16_1_zero_counterexample :
    ¬ (ringChar ℚ ∣ 3) ∧
    IsGarlingSplittingFieldExtension ℚ ℚ (Polynomial.X ^ 3 - Polynomial.C (0 : ℚ)) ∧
    ¬ ∃ ω : ℚ, IsPrimitiveRoot ω 3 := by
  have hchar : ¬ (ringChar ℚ ∣ 3) := by
    rw [ringChar.eq_zero]
    simp
  have hsf : IsGarlingSplittingFieldExtension ℚ ℚ (Polynomial.X ^ 3 - Polynomial.C (0 : ℚ)) := by
    refine ⟨⟨3, 1, fun _ => 0, ?_⟩, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
    simp [GarlingSplitsExplicit]
  have hno : ¬ ∃ ω : ℚ, IsPrimitiveRoot ω 3 := by
    rintro ⟨ω, hω⟩
    have hroot : Polynomial.IsRoot (Polynomial.cyclotomic 3 ℚ) ω :=
      hω.isRoot_cyclotomic (by decide)
    rw [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hroot
    have hpos : 0 < (ω + 1 / 2) ^ 2 + 3 / 4 := by positivity
    linarith
  exact ⟨hchar, hsf, hno⟩

/-- **Theorem 16.1** (§16.1, printed p. 123 / PDF p. 131; proof pp. 123–124; `θ ≠ 0` guard made
explicit per `QUEUE.md` Flag 1(a)):
*"Suppose that `x^n - θ ∈ K[x]`, and that `char K` does not divide `n` [with `θ ≠ 0`]. Let `L : K`
be a splitting field extension for `x^n - θ` over `K`. Then `L` contains a primitive `n`th root of
unity, `ω` say. The group `Γ(L : K(ω))` is cyclic, and its order divides `n`. `x^n - θ` is
irreducible over `K(ω)` if and only if `[L : K(ω)] = n`."*

Also constructs Garling's explicit injective group homomorphism `Γ(L : K(ω)) →+ ℤ_n`
(`σ ↦ j(σ) mod n`, correcting p. 124 ll. 3, 5's printed slip `Γ(L : K)` for `Γ(L : K(ω))`). -/
theorem theorem_16_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {θ : K} (hθ : θ ≠ 0) (hchar : ¬ (ringChar K ∣ n))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C θ)) :
    1 ≤ n ∧
    (∃ ω : L, IsPrimitiveRoot ω n) ∧
    (∀ (ω : L), IsPrimitiveRoot ω n →
      let Kω : IntermediateField K L := K⟮ω⟯
      IsGarlingGaloisExtension Kω L ∧
      IsCyclic (GarlingGaloisGroup Kω L) ∧
      Nat.card (GarlingGaloisGroup Kω L) ∣ n ∧
      Module.finrank Kω L = Nat.card (GarlingGaloisGroup Kω L) ∧
      (∃ φ : Additive (GarlingGaloisGroup Kω L) →+ Zn n, Function.Injective φ) ∧
      (Irreducible ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K Kω)) ↔
        Module.finrank Kω L = n) ∧
      (Irreducible ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K Kω)) ↔
        extDegree Kω L = (n : ℕ∞))) := by
  obtain ⟨hn, _, hex_prim, ⟨β, hβ⟩, hfac⟩ := section_16_1_root_factorization hθ hchar hsf
  obtain ⟨_, hmonic, _, _, hgsep⟩ := X_pow_sub_C_separable_of_ne_zero hθ hchar
  have hf0 : (Polynomial.X ^ n - Polynomial.C θ : K[X]) ≠ 0 := hmonic.ne_zero
  have hgalKL : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_splittingField hf0 hsf hgsep
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgalKL |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgalKL |>.2
  have hβ_pow : β ^ n = algebraMap K L θ := by
    have h1 := hβ
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h1
    exact h1
  have hβ_ne : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.ne_of_gt hn)] at hβ_pow
    exact hθ ((algebraMap K L).injective (hβ_pow.symm.trans (map_zero _).symm))
  refine ⟨hn, hex_prim, fun ω hω => ?_⟩
  intro Kω
  have _ : FiniteDimensional Kω L := Module.Finite.right K Kω L
  have _ : IsGalois Kω L := IsGalois.tower_top_of_isGalois K Kω L
  have hgalKωL : IsGarlingGaloisExtension Kω L :=
    (isGarlingGaloisExtension_iff Kω L).mpr ⟨inferInstance, inferInstance⟩
  have hfinrank_eq_card : Module.finrank Kω L = Nat.card (GarlingGaloisGroup Kω L) := by
    rw [IsGalois.card_aut_eq_finrank Kω L]
  have hL_gen : IntermediateField.adjoin Kω ({β} : Set L) = ⊤ := by
    let E : IntermediateField K L :=
      (IntermediateField.adjoin Kω ({β} : Set L)).restrictScalars K
    have hωE : ω ∈ E := by
      change algebraMap Kω L ⟨ω, IntermediateField.mem_adjoin_simple_self K ω⟩ ∈
        IntermediateField.adjoin Kω ({β} : Set L)
      exact (IntermediateField.adjoin Kω ({β} : Set L)).algebraMap_mem _
    have hβE : β ∈ E := IntermediateField.mem_adjoin_simple_self Kω β
    have hsplitE : GarlingSplitsOver K E (Polynomial.X ^ n - Polynomial.C θ) := by
      refine ⟨n, 1, fun k => ⟨ω ^ (k : ℕ) * β, mul_mem (pow_mem hωE _) hβE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmap_comp :
          ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K E)).map (algebraMap E L) =
            (Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K L) := by
        rw [Polynomial.map_map]; rfl
      rw [hmap_comp, hfac ω β hω hβ]
      simp only [map_one, one_mul, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp
    have hE_top : E = ⊤ := by
      by_contra hne
      exact hsf.2 E hne hsplitE
    ext x
    change x ∈ E ↔ True
    simp [hE_top]
  have h_act : ∀ σ : GarlingGaloisGroup Kω L, ∃ j : Fin n, σ β = ω ^ (j : ℕ) * β := by
    intro σ
    have hσβ_root : Polynomial.aeval (σ β) (Polynomial.X ^ n - Polynomial.C θ) = 0 := by
      have h1 : Polynomial.aeval (σ β) ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K Kω)) = 0 := by
        rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, hβ, map_zero]
      rwa [Polynomial.aeval_map_algebraMap] at h1
    have heval := congrArg (Polynomial.eval (σ β)) (hfac ω β hω hβ)
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hσβ_root, Polynomial.eval_prod,
      eq_comm, Finset.prod_eq_zero_iff] at heval
    rcases heval with ⟨j, _, hj⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    exact ⟨j, hj⟩
  let jFun : GarlingGaloisGroup Kω L → Fin n := fun σ => (h_act σ).choose
  have hjFun_spec : ∀ σ : GarlingGaloisGroup Kω L, σ β = ω ^ (jFun σ : ℕ) * β :=
    fun σ => (h_act σ).choose_spec
  have hω_fix : ∀ σ : GarlingGaloisGroup Kω L, σ ω = ω := fun σ =>
    σ.commutes ⟨ω, IntermediateField.mem_adjoin_simple_self K ω⟩
  let φZMod : Additive (GarlingGaloisGroup Kω L) →+ ZMod n :=
    { toFun := fun σ => ((jFun (Additive.toMul σ) : ℕ) : ZMod n)
      map_zero' := by
        have h1 : (1 : GarlingGaloisGroup Kω L) β = ω ^ (0 : ℕ) * β := by simp
        have h2 := hjFun_spec 1
        have hpow : ω ^ (jFun 1 : ℕ) = ω ^ (0 : ℕ) :=
          mul_right_cancel₀ hβ_ne (h2.symm.trans h1)
        have hj0 : (jFun 1 : ℕ) = 0 := hω.pow_inj (jFun 1).isLt hn hpow
        change ((jFun 1 : ℕ) : ZMod n) = 0
        rw [hj0, Nat.cast_zero]
      map_add' := fun σ τ => by
        let σm := Additive.toMul σ
        let τm := Additive.toMul τ
        have hprod : (σm * τm) β = ω ^ ((jFun σm : ℕ) + (jFun τm : ℕ)) * β := by
          calc (σm * τm) β = σm (τm β) := AlgEquiv.mul_apply σm τm β
            _ = σm (ω ^ (jFun τm : ℕ) * β) := by rw [hjFun_spec τm]
            _ = (σm ω) ^ (jFun τm : ℕ) * σm β := by rw [map_mul, map_pow]
            _ = ω ^ (jFun τm : ℕ) * (ω ^ (jFun σm : ℕ) * β) := by rw [hω_fix σm, hjFun_spec σm]
            _ = ω ^ ((jFun σm : ℕ) + (jFun τm : ℕ)) * β := by rw [pow_add]; ring
        have hspec := hjFun_spec (σm * τm)
        have hpow_eq : ω ^ (jFun (σm * τm) : ℕ) = ω ^ ((jFun σm : ℕ) + (jFun τm : ℕ)) :=
          mul_right_cancel₀ hβ_ne (hspec.symm.trans hprod)
        have hdvd : (jFun (σm * τm) : ℕ) ≡ (jFun σm : ℕ) + (jFun τm : ℕ) [MOD n] :=
          (isPrimitiveRoot_pow_eq_pow_iff_modEq hn hω).mp hpow_eq
        change ((jFun (σm * τm) : ℕ) : ZMod n) =
          ((jFun σm : ℕ) : ZMod n) + ((jFun τm : ℕ) : ZMod n)
        rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
        exact hdvd }
  have hφ_inj : Function.Injective φZMod := by
    intro σ₁ σ₂ h12
    let s₁ := Additive.toMul σ₁
    let s₂ := Additive.toMul σ₂
    have hmod : (jFun s₁ : ℕ) ≡ (jFun s₂ : ℕ) [MOD n] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp h12
    have hjeq : (jFun s₁ : ℕ) = (jFun s₂ : ℕ) := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt (jFun s₁).isLt, Nat.mod_eq_of_lt (jFun s₂).isLt] at hmod
      exact hmod
    have hβeq : s₁ β = s₂ β := by
      rw [hjFun_spec s₁, hjFun_spec s₂, hjeq]
    have hs_eq : s₁ = s₂ := by
      let Eeq : IntermediateField Kω L :=
        { (AlgHom.equalizer s₁.toAlgHom s₂.toAlgHom) with
          inv_mem' := fun {a} ha => by
            change s₁ a⁻¹ = s₂ a⁻¹
            rw [map_inv₀, map_inv₀]
            exact congrArg Inv.inv ha }
      have htop : (⊤ : IntermediateField Kω L) ≤ Eeq := by
        rw [← hL_gen, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact hβeq
      ext x
      exact htop IntermediateField.mem_top
    exact Additive.toMul.injective hs_eq
  let φZn : Additive (GarlingGaloisGroup Kω L) →+ Zn n :=
    (znAddEquivZMod n).symm.toAddMonoidHom.comp φZMod
  have hφZn_inj : Function.Injective φZn :=
    (znAddEquivZMod n).symm.injective.comp hφ_inj
  have _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcard_dvd : Nat.card (GarlingGaloisGroup Kω L) ∣ n := by
    let subZ : AddSubgroup (ZMod n) := φZMod.range
    have heq_card : Nat.card (GarlingGaloisGroup Kω L) = Nat.card subZ := by
      have e : Additive (GarlingGaloisGroup Kω L) ≃+ subZ :=
        AddEquiv.ofBijective φZMod.rangeRestrict
          ⟨fun x y hxy => hφ_inj (congrArg Subtype.val hxy), φZMod.rangeRestrict_surjective⟩
      exact (Nat.card_congr Additive.ofMul).trans (Nat.card_congr e.toEquiv)
    rw [heq_card]
    have hd := AddSubgroup.card_dvd_of_le (le_top : subZ ≤ ⊤)
    rw [Nat.card_congr (AddSubgroup.topEquiv.toEquiv), Nat.card_zmod] at hd
    exact hd
  have hcyclic : IsCyclic (GarlingGaloisGroup Kω L) := by
    let subZ : AddSubgroup (ZMod n) := φZMod.range
    have _ : IsAddCyclic subZ := inferInstance
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := subZ)
    obtain ⟨σ₀, hσ₀⟩ := g.2
    refine ⟨⟨Additive.toMul σ₀, fun τ => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg ⟨φZMod (Additive.ofMul τ), ⟨Additive.ofMul τ, rfl⟩⟩
    refine ⟨k, ?_⟩
    apply Additive.ofMul.injective
    apply hφ_inj
    have hk_val : k • g.1 = φZMod (Additive.ofMul τ) := congrArg Subtype.val hk
    rw [← hσ₀, ← map_zsmul φZMod] at hk_val
    simpa using hk_val
  let fKω : Kω[X] := (Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K Kω)
  have hfKω_monic : fKω.Monic := hmonic.map (algebraMap K Kω)
  have hfKω_deg : fKω.natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K Kω).injective,
      Polynomial.natDegree_X_pow_sub_C]
  have hfKω_beta : Polynomial.aeval β fKω = 0 := by
    rwa [Polynomial.aeval_map_algebraMap]
  have hfinrank_adjoin : Module.finrank Kω Kω⟮β⟯ = Module.finrank Kω L := by
    have htop_eq : (Kω⟮β⟯ : IntermediateField Kω L) = ⊤ := hL_gen
    rw [htop_eq]
    exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
  have hβ_int : IsIntegral Kω β := Algebra.IsIntegral.isIntegral β
  have hmin_dvd : minpoly Kω β ∣ fKω := minpoly.dvd Kω β hfKω_beta
  have hfinrank_minpoly : Module.finrank Kω Kω⟮β⟯ = (minpoly Kω β).natDegree :=
    IntermediateField.adjoin.finrank hβ_int
  have hirr_iff : Irreducible fKω ↔ Module.finrank Kω L = n := by
    constructor
    · intro hirr
      have heq : minpoly Kω β = fKω :=
        (minpoly.eq_of_irreducible_of_monic hirr hfKω_beta hfKω_monic).symm
      rw [← hfinrank_adjoin, hfinrank_minpoly, heq, hfKω_deg]
    · intro hdegL
      have hmin_deg : (minpoly Kω β).natDegree = n := by
        rw [← hfinrank_minpoly, hfinrank_adjoin, hdegL]
      have heq : fKω = minpoly Kω β :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic hβ_int) hfKω_monic hmin_dvd (by rw [hfKω_deg, hmin_deg])
      rw [heq]
      exact minpoly.irreducible hβ_int
  have hext_iff : Irreducible fKω ↔ extDegree Kω L = (n : ℕ∞) := by
    rw [hirr_iff, extDegree_eq_finrank Kω L]
    exact ⟨fun h => by rw [h], fun h => Nat.cast_injective h⟩
  exact ⟨hgalKωL, hcyclic, hcard_dvd, hfinrank_eq_card, ⟨φZn, hφZn_inj⟩, hirr_iff, hext_iff⟩

/-- Concrete refutation of printed p. 124 ll. 3, 5's group-name slip (`Γ(L : K)` printed twice for
`Γ(L : K(ω))` in `Theorem 16.1`'s proof): for `x³ - 2 ∈ ℚ[x]`, `Γ_ℚ(x³ - 2) ≅ Σ₃` is **not**
cyclic (non-abelian of order `6`), confirming p. 124 meant `Γ(L : K(ω))`. -/
theorem theorem_16_1_galoisGroup_over_K_not_cyclic_example
    {L : Type u} [Field L] [Algebra ℚ L]
    (hsf : IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ))) :
    ¬ IsCyclic (GarlingGaloisGroup ℚ L) := by
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  let f : ℚ[X] := Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)
  have hf_irr : Irreducible f := (exercise_5_7 (p := 2) (n := 3) Nat.prime_two (by decide)).1
  have hchar : ¬ (ringChar ℚ ∣ 3) := by rw [ringChar.eq_zero]; simp
  obtain ⟨_, hmonic, hdeg, hsep, hgsep⟩ :=
    X_pow_sub_C_separable_of_ne_zero (K := ℚ) (n := 3) (θ := 2) (by norm_num) hchar
  obtain ⟨_, ⟨ω, hω⟩, h161⟩ := theorem_16_1 (by norm_num) hchar hsf
  obtain ⟨_, ⟨β, hβ⟩, _⟩ := (section_16_1_root_factorization (by norm_num) hchar hsf).2.2
  have hgal : IsGarlingGaloisExtension ℚ L :=
    isGarlingGalois_of_splittingField hmonic.ne_zero hsf hgsep
  have _ : FiniteDimensional ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.1
  have _ : IsGalois ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.2
  have hmin_ω3 : minpoly ℚ ω = Polynomial.cyclotomic 3 ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hω (by decide)).symm
  have hdeg_ω : Module.finrank ℚ ℚ⟮ω⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ω),
      hmin_ω3, Polynomial.natDegree_cyclotomic]
    decide
  have hdeg_β : Module.finrank ℚ ℚ⟮β⟯ = 3 := by
    have hm : minpoly ℚ β = f :=
      (minpoly.eq_of_irreducible_of_monic hf_irr hβ hmonic).symm
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β), hm, hdeg]
  have hdvd2 : 2 ∣ Module.finrank ℚ L :=
    hdeg_ω ▸ ⟨Module.finrank ℚ⟮ω⟯ L, (Module.finrank_mul_finrank ℚ ℚ⟮ω⟯ L).symm⟩
  have hdvd3 : 3 ∣ Module.finrank ℚ L :=
    hdeg_β ▸ ⟨Module.finrank ℚ⟮β⟯ L, (Module.finrank_mul_finrank ℚ ℚ⟮β⟯ L).symm⟩
  have hdvd6 : 6 ∣ Module.finrank ℚ L :=
    (by decide : Nat.Coprime 3 2).mul_dvd_of_dvd_of_dvd hdvd3 hdvd2
  obtain ⟨_, _, hcard_dvd3, hfin_eq_card, _, _, _⟩ := h161 ω hω
  have hle3 : Module.finrank ℚ⟮ω⟯ L ≤ 3 :=
    hfin_eq_card ▸ Nat.le_of_dvd (by decide) hcard_dvd3
  have hle6 : Module.finrank ℚ L ≤ 6 := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮ω⟯ L, hdeg_ω]; omega
  have hfinL : Module.finrank ℚ L = 6 :=
    Nat.le_antisymm hle6 (Nat.le_of_dvd Module.finrank_pos hdvd6)
  have hcardG : Nat.card (GarlingGaloisGroup ℚ L) = 6 := by
    change Nat.card (L ≃ₐ[ℚ] L) = 6
    rw [IsGalois.card_aut_eq_finrank ℚ L, hfinL]
  have hinj_perm := theorem_11_6 hsf
  have hsp := (garlingSplitsOver_iff_splits ℚ L f).mp hsf.1
  have hcard_roots : Nat.card (garlingRootSet ℚ L f) = 3 := by
    rw [garlingRootSet_eq_rootSet hmonic.ne_zero, Polynomial.rootSet_def, Finset.coe_sort_coe,
      Nat.card_eq_fintype_card, Fintype.card_coe,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep.map),
      ← Polynomial.Splits.natDegree_eq_card_roots hsp,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective, hdeg]
  have hfin_roots : Finite (garlingRootSet ℚ L f) :=
    Nat.finite_of_card_ne_zero (by rw [hcard_roots]; decide)
  let _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofFinite _
  have hft_roots : Fintype.card (garlingRootSet ℚ L f) = 3 := by
    rwa [← Nat.card_eq_fintype_card]
  let eR : garlingRootSet ℚ L f ≃ Fin 3 := Fintype.equivFinOfCardEq hft_roots
  let ψ : GarlingGaloisGroup ℚ L →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom eR).toMonoidHom.comp (garlingRootPermHom ℚ L f)
  have hψ_inj : Function.Injective ψ := (Equiv.permCongrHom eR).injective.comp hinj_perm
  let _ : Fintype (GarlingGaloisGroup ℚ L) := Fintype.ofFinite _
  have hψ_bij : Function.Bijective ψ := by
    refine (Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, hcardG, Fintype.card_perm, Fintype.card_fin]
    decide
  let eGrp : GarlingGaloisGroup ℚ L ≃* Equiv.Perm (Fin 3) :=
    MulEquiv.ofBijective ψ hψ_bij
  intro hcyc
  have _ : CommGroup (GarlingGaloisGroup ℚ L) := IsCyclic.commGroup
  let c01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let c12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hcomm : c01 * c12 = c12 * c01 := by
    have := mul_comm (eGrp.symm c01) (eGrp.symm c12)
    have h2 := congrArg eGrp this
    simpa [map_mul] using h2
  have hne : (c01 * c12) 0 ≠ (c12 * c01) 0 := by decide
  exact hne (congrArg (fun p : Equiv.Perm (Fin 3) => p 0) hcomm)

/-- **Exercise 16.1** (§16.1, printed p. 124 / PDF p. 132):
*"Show that `x⁶ + 3` is irreducible over `ℚ`, but is not irreducible over `ℚ(ω)`, where `ω` is a
primitive sixth root of unity."* -/
theorem exercise_16_1 :
    Irreducible (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ) : ℚ[X]) ∧
    IsGarlingIrreducible (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ) : ℚ[X]) ∧
    (∃ ω : ℂ, IsPrimitiveRoot ω 6) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L] (ω : L),
      IsPrimitiveRoot ω 6 →
      let Qω : IntermediateField ℚ L := ℚ⟮ω⟯
      ¬ Irreducible ((Polynomial.X ^ 6 + Polynomial.C (3 : ℚ)).map (algebraMap ℚ Qω)) ∧
      ¬ IsGarlingIrreducible ((Polynomial.X ^ 6 + Polynomial.C (3 : ℚ)).map (algebraMap ℚ Qω))) := by
  let fZ : ℤ[X] := Polynomial.X ^ 6 + Polynomial.C 3
  have hfZ_monic : fZ.Monic := Polynomial.monic_X_pow_add_C 3 (by decide)
  have hfZ_deg : fZ.natDegree = 6 := Polynomial.natDegree_X_pow_add_C
  have hfZ_irr : Irreducible fZ := by
    refine Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(3 : ℤ)}) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Ideal.span_singleton_prime (by norm_num)]
      exact Int.prime_three
    · rw [hfZ_monic.leadingCoeff, Ideal.mem_span_singleton]
      norm_num
    · intro k hk
      rw [Polynomial.degree_eq_natDegree hfZ_monic.ne_zero, hfZ_deg, Nat.cast_lt] at hk
      rw [Ideal.mem_span_singleton]
      have hck : fZ.coeff k = if k = 0 then 3 else 0 := by
        simp only [fZ, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        have hk6 : k ≠ 6 := by omega
        simp [hk6]
      rw [hck]
      split_ifs <;> norm_num
    · rw [Polynomial.degree_eq_natDegree hfZ_monic.ne_zero, hfZ_deg]
      decide
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have hc0 : fZ.coeff 0 = 3 := by simp [fZ]
      rw [hc0]; norm_num
    · exact hfZ_monic.isPrimitive
  have hfQ_eq : (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ) : ℚ[X]) =
      fZ.map (algebraMap ℤ ℚ) := by
    simp [fZ, Polynomial.C_ofNat]
  have hfQ_irr : Irreducible (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ) : ℚ[X]) := by
    rw [hfQ_eq]
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfZ_monic.isPrimitive).mp
      hfZ_irr
  have hfQ_girr : IsGarlingIrreducible (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ) : ℚ[X]) :=
    (isGarlingIrreducible_iff _).mpr hfQ_irr
  have hexC : ∃ ω : ℂ, IsPrimitiveRoot ω 6 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 6), Complex.isPrimitiveRoot_exp 6 (by decide)⟩
  refine ⟨hfQ_irr, hfQ_girr, hexC, fun L _ _ ω hω => ?_⟩
  intro Qω
  have hcyc6 : Polynomial.IsRoot (Polynomial.cyclotomic 6 L) ω :=
    hω.isRoot_cyclotomic (by decide)
  have hω_quad : ω ^ 2 - ω + 1 = 0 := by
    have h6 : Polynomial.cyclotomic 6 L = Polynomial.X ^ 2 - Polynomial.X + 1 := by
      rw [← Polynomial.map_cyclotomic_int 6 L]
      have h6Z : Polynomial.cyclotomic 6 ℤ = Polynomial.X ^ 2 - Polynomial.X + 1 := by
        have hmul := Polynomial.prod_cyclotomic_eq_X_pow_sub_one (by decide : 0 < 6) ℤ
        have hdiv : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
        rw [hdiv] at hmul
        simp only [Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ)),
          Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3, 6} : Finset ℕ)),
          Finset.prod_insert (by decide : (3 : ℕ) ∉ ({6} : Finset ℕ)),
          Finset.prod_singleton, Polynomial.cyclotomic_one, Polynomial.cyclotomic_two,
          Polynomial.cyclotomic_three] at hmul
        have hprod123 :
            ((Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) : ℤ[X]) ≠ 0 := by
          intro h0
          have hev := congrArg (Polynomial.eval 2) h0
          norm_num at hev
        apply mul_left_cancel₀ hprod123
        calc ((Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1)) *
              Polynomial.cyclotomic 6 ℤ
            = (Polynomial.X - 1) * ((Polynomial.X + 1) *
                ((Polynomial.X ^ 2 + Polynomial.X + 1) * Polynomial.cyclotomic 6 ℤ)) := by ring
          _ = Polynomial.X ^ 6 - 1 := hmul
          _ = ((Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1)) *
                (Polynomial.X ^ 2 - Polynomial.X + 1) := by ring
      rw [h6Z]; simp
    rw [h6, Polynomial.IsRoot.def] at hcyc6
    simpa using hcyc6
  let ωQ : Qω := ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩
  have hωQ_quad : ωQ ^ 2 - ωQ + 1 = 0 := by
    ext; exact hω_quad
  let γ : Qω := 2 * ωQ - 1
  have hγ_sq : γ ^ 2 = -3 := by
    calc γ ^ 2 = 4 * (ωQ ^ 2 - ωQ + 1) - 3 := by ring
      _ = 4 * 0 - 3 := by rw [hωQ_quad]
      _ = -3 := by ring
  let g₁ : Qω[X] := Polynomial.X ^ 3 - Polynomial.C γ
  let g₂ : Qω[X] := Polynomial.X ^ 3 + Polynomial.C γ
  have hfac_Qω :
      (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ)).map (algebraMap ℚ Qω) = g₁ * g₂ := by
    have hmap :
        (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ)).map (algebraMap ℚ Qω) =
          Polynomial.X ^ 6 + Polynomial.C (3 : Qω) := by
      simp [Polynomial.C_ofNat]
    rw [hmap]
    calc (Polynomial.X ^ 6 + Polynomial.C (3 : Qω) : Qω[X])
        = Polynomial.X ^ 6 - Polynomial.C (-3 : Qω) := by
          simp [sub_neg_eq_add, Polynomial.C_ofNat]
      _ = Polynomial.X ^ 6 - Polynomial.C (γ ^ 2) := by rw [hγ_sq]
      _ = g₁ * g₂ := by
          simp only [g₁, g₂, map_pow]
          ring
  have hg₁_not_unit : ¬ IsUnit g₁ := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    have hdeg1 : g₁.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C
    have hne0 : g₁ ≠ 0 := (Polynomial.monic_X_pow_sub_C γ (by decide)).ne_zero
    rw [Polynomial.degree_eq_natDegree hne0, hdeg1]
    decide
  have hg₂_not_unit : ¬ IsUnit g₂ := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    have hdeg2 : g₂.natDegree = 3 := Polynomial.natDegree_X_pow_add_C
    have hne0 : g₂ ≠ 0 := (Polynomial.monic_X_pow_add_C γ (by decide)).ne_zero
    rw [Polynomial.degree_eq_natDegree hne0, hdeg2]
    decide
  have hnot_irr : ¬ Irreducible ((Polynomial.X ^ 6 + Polynomial.C (3 : ℚ)).map (algebraMap ℚ Qω)) := by
    intro hirr
    rcases hirr.isUnit_or_isUnit hfac_Qω with hu1 | hu2
    · exact hg₁_not_unit hu1
    · exact hg₂_not_unit hu2
  exact ⟨hnot_irr, fun hg => hnot_irr ((isGarlingIrreducible_iff _).mp hg)⟩

/-- **Exercise 16.2** (§16.1, printed p. 124 / PDF p. 132):
*"Show that the Galois group of `x¹⁵ - 2` over `ℚ` can be generated by elements `ρ, σ` and `τ`
satisfying `ρ¹⁵ = σ⁴ = τ² = 1`, `σ⁻¹ρσ = ρ⁷`, `τ⁻¹ρτ = ρ¹⁴`, `τ⁻¹στ = σ`."*

*(OCR warning verified against 220 DPI scan PDF p. 132: `garling1986_pages.txt` l. 4629 corrupts
`σ⁻¹ρσ = ρ⁷` to `a-1 pa= p 1,`!)* -/
theorem exercise_16_2 {L : Type u} [Field L] [Algebra ℚ L]
    (hsf : IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 15 - Polynomial.C (2 : ℚ))) :
    Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 15 - Polynomial.C (2 : ℚ))) = 120 ∧
    ∃ ρ σ τ : GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)),
      Subgroup.closure ({ρ, σ, τ} : Set (GarlingPolyGaloisGroup ℚ L _)) = ⊤ ∧
      orderOf ρ = 15 ∧ orderOf σ = 4 ∧ orderOf τ = 2 ∧
      ρ ^ 15 = 1 ∧ σ ^ 4 = 1 ∧ τ ^ 2 = 1 ∧
      σ⁻¹ * ρ * σ = ρ ^ 7 ∧
      τ⁻¹ * ρ * τ = ρ ^ 14 ∧
      τ⁻¹ * σ * τ = σ := by
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  let f : ℚ[X] := Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)
  have hf_irr : Irreducible f := (exercise_5_7 (p := 2) (n := 15) Nat.prime_two (by decide)).1
  have hchar : ¬ (ringChar ℚ ∣ 15) := by rw [ringChar.eq_zero]; simp
  obtain ⟨_, hmonic, _, _, hgsep⟩ :=
    X_pow_sub_C_separable_of_ne_zero (K := ℚ) (n := 15) (θ := 2) (by norm_num) hchar
  obtain ⟨_, ⟨ω, hω⟩, h161⟩ := theorem_16_1 (by norm_num) hchar hsf
  obtain ⟨_, ⟨β, hβ⟩, hfac⟩ :=
    (section_16_1_root_factorization (by norm_num) hchar hsf).2.2
  have hβ_pow : β ^ 15 = 2 := by
    have h1 := hβ
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat, sub_eq_zero] at h1
    exact h1
  have hβ_ne : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hβ_pow
    norm_num at hβ_pow
  have hgal : IsGarlingGaloisExtension ℚ L :=
    isGarlingGalois_of_splittingField hmonic.ne_zero hsf hgsep
  have _ : FiniteDimensional ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.1
  have _ : IsGalois ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.2
  have hω_int : IsIntegral ℚ ω := Algebra.IsIntegral.isIntegral ω
  have hmin_ω : minpoly ℚ ω = Polynomial.cyclotomic 15 ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hω (by decide)).symm
  have hdeg_Qω : Module.finrank ℚ ℚ⟮ω⟯ = 8 := by
    rw [IntermediateField.adjoin.finrank hω_int, hmin_ω, Polynomial.natDegree_cyclotomic]
    decide
  have hβ_int : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  have hmin_β : minpoly ℚ β = f :=
    (minpoly.eq_of_irreducible_of_monic hf_irr hβ hmonic).symm
  have hdeg_Qβ : Module.finrank ℚ ℚ⟮β⟯ = 15 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin_β, Polynomial.natDegree_X_pow_sub_C]
  have hdvd8 : 8 ∣ Module.finrank ℚ L := by
    rw [← hdeg_Qω]
    exact ⟨Module.finrank ℚ⟮ω⟯ L, (Module.finrank_mul_finrank ℚ ℚ⟮ω⟯ L).symm⟩
  have hdvd15 : 15 ∣ Module.finrank ℚ L := by
    rw [← hdeg_Qβ]
    exact ⟨Module.finrank ℚ⟮β⟯ L, (Module.finrank_mul_finrank ℚ ℚ⟮β⟯ L).symm⟩
  have hdvd120 : 120 ∣ Module.finrank ℚ L := by
    have hcop : Nat.Coprime 15 8 := by decide
    simpa using hcop.mul_dvd_of_dvd_of_dvd hdvd15 hdvd8
  obtain ⟨_, _, hcard_dvd15, hfin_eq_card, _, hirr_Kω, _⟩ := h161 ω hω
  have hle15 : Module.finrank ℚ⟮ω⟯ L ≤ 15 := by
    rw [hfin_eq_card]
    exact Nat.le_of_dvd (by decide) hcard_dvd15
  have hle120 : Module.finrank ℚ L ≤ 120 := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮ω⟯ L, hdeg_Qω]
    omega
  have hfinL : Module.finrank ℚ L = 120 :=
    Nat.le_antisymm hle120 (Nat.le_of_dvd Module.finrank_pos hdvd120)
  have hfin_QωL : Module.finrank ℚ⟮ω⟯ L = 15 := by
    have hmul := Module.finrank_mul_finrank ℚ ℚ⟮ω⟯ L
    rw [hdeg_Qω, hfinL] at hmul
    omega
  have hcardG : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 120 := by
    change Nat.card (L ≃ₐ[ℚ] L) = 120
    rw [IsGalois.card_aut_eq_finrank ℚ L, hfinL]
  have hf_Qω_irr : Irreducible (f.map (algebraMap ℚ ℚ⟮ω⟯)) := hirr_Kω.mpr hfin_QωL
  have _ : FiniteDimensional ℚ⟮ω⟯ L := Module.Finite.right ℚ ℚ⟮ω⟯ L
  have _ : FiniteDimensional ℚ⟮β⟯ L := Module.Finite.right ℚ ℚ⟮β⟯ L
  have hL_over_Qω : IntermediateField.adjoin ℚ⟮ω⟯ ({β} : Set L) = ⊤ := by
    let E : IntermediateField ℚ L :=
      (IntermediateField.adjoin ℚ⟮ω⟯ ({β} : Set L)).restrictScalars ℚ
    have hωE : ω ∈ E :=
      (IntermediateField.adjoin ℚ⟮ω⟯ ({β} : Set L)).algebraMap_mem
        ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩
    have hβE : β ∈ E := IntermediateField.mem_adjoin_simple_self ℚ⟮ω⟯ β
    have hE_top : E = ⊤ := by
      by_contra hne
      refine hsf.2 E hne ⟨15, 1, fun k => ⟨ω ^ (k : ℕ) * β, mul_mem (pow_mem hωE _) hβE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc :
          ((Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)).map (@algebraMap ℚ E _ _ E.algebra')).map
              (algebraMap E L) =
            (Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)).map (algebraMap ℚ L) := by
        rw [Polynomial.map_map]
        congr 1
        exact Subsingleton.elim _ _
      rw [hmc, hfac ω β hω hβ]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have hfin_QβL : Module.finrank ℚ⟮β⟯ L = 8 := by
    have hmul := Module.finrank_mul_finrank ℚ ℚ⟮β⟯ L
    rw [hdeg_Qβ, hfinL] at hmul
    omega
  have hL_over_Qβ : IntermediateField.adjoin ℚ⟮β⟯ ({ω} : Set L) = ⊤ := by
    let E : IntermediateField ℚ L :=
      (IntermediateField.adjoin ℚ⟮β⟯ ({ω} : Set L)).restrictScalars ℚ
    have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self ℚ⟮β⟯ ω
    have hβE : β ∈ E :=
      (IntermediateField.adjoin ℚ⟮β⟯ ({ω} : Set L)).algebraMap_mem
        ⟨β, IntermediateField.mem_adjoin_simple_self ℚ β⟩
    have hE_top : E = ⊤ := by
      by_contra hne
      refine hsf.2 E hne ⟨15, 1, fun k => ⟨ω ^ (k : ℕ) * β, mul_mem (pow_mem hωE _) hβE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc :
          ((Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)).map (@algebraMap ℚ E _ _ E.algebra')).map
              (algebraMap E L) =
            (Polynomial.X ^ 15 - Polynomial.C (2 : ℚ)).map (algebraMap ℚ L) := by
        rw [Polynomial.map_map]
        congr 1
        exact Subsingleton.elim _ _
      rw [hmc, hfac ω β hω hβ]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have aut_ext : ∀ g₁ g₂ : L ≃ₐ[ℚ] L, g₁ ω = g₂ ω → g₁ β = g₂ β → g₁ = g₂ := by
    intro g₁ g₂ h1 h2
    let Eeq : IntermediateField ℚ L :=
      { (AlgHom.equalizer g₁.toAlgHom g₂.toAlgHom) with
        inv_mem' := fun {a} ha => by
          change g₁ a⁻¹ = g₂ a⁻¹
          rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv ha }
    have hω_mem : ω ∈ Eeq := h1
    have hβ_mem : β ∈ Eeq := h2
    have hQω_le : ℚ⟮ω⟯ ≤ Eeq := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hω_mem
    let Eeq' : IntermediateField ℚ⟮ω⟯ L :=
      { Eeq.toSubfield with
        algebraMap_mem' := fun x => hQω_le x.2 }
    have htop' : (⊤ : IntermediateField ℚ⟮ω⟯ L) ≤ Eeq' := by
      rw [← hL_over_Qω, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact hβ_mem
    ext x
    exact htop' IntermediateField.mem_top
  obtain ⟨ρ, hρ_ω, hρ_β⟩ : ∃ ρ : L ≃ₐ[ℚ] L, ρ ω = ω ∧ ρ β = ω * β := by
    let hβ_pb : PowerBasis ℚ⟮ω⟯ (ℚ⟮ω⟯)⟮β⟯ :=
      IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral β)
    have hgen_β : algebraMap (ℚ⟮ω⟯)⟮β⟯ L hβ_pb.gen = β :=
      congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
    have hωβ_root : Polynomial.aeval (ω * β) (minpoly ℚ⟮ω⟯ hβ_pb.gen) = 0 := by
      have hmin_eq : minpoly ℚ⟮ω⟯ hβ_pb.gen = minpoly ℚ⟮ω⟯ β := by
        rw [← minpoly.algebraMap_eq (algebraMap (ℚ⟮ω⟯)⟮β⟯ L).injective, hgen_β]
      have hβ_ev : Polynomial.aeval β (f.map (algebraMap ℚ ℚ⟮ω⟯)) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap ℚ⟮ω⟯ L).comp (algebraMap ℚ ℚ⟮ω⟯) = algebraMap ℚ L :=
          Subsingleton.elim _ _
        rw [hcomp, ← Polynomial.aeval_def]
        exact hβ
      have hm : minpoly ℚ⟮ω⟯ β = f.map (algebraMap ℚ ℚ⟮ω⟯) :=
        (minpoly.eq_of_irreducible_of_monic hf_Qω_irr hβ_ev (hmonic.map _)).symm
      rw [hmin_eq, hm, Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap ℚ⟮ω⟯ L).comp (algebraMap ℚ ℚ⟮ω⟯) = algebraMap ℚ L :=
        Subsingleton.elim _ _
      rw [hcomp, ← Polynomial.aeval_def, map_sub, map_pow, Polynomial.aeval_X,
        Polynomial.aeval_C, map_ofNat, mul_pow, hω.pow_eq_one, one_mul, hβ_pow, sub_self]
    let ρ_hom : (ℚ⟮ω⟯)⟮β⟯ →ₐ[ℚ⟮ω⟯] L := hβ_pb.lift (ω * β) hωβ_root
    have hρ_hom_β : ρ_hom ⟨β, IntermediateField.mem_adjoin_simple_self ℚ⟮ω⟯ β⟩ = ω * β := by
      have hgen : hβ_pb.gen = ⟨β, IntermediateField.mem_adjoin_simple_self ℚ⟮ω⟯ β⟩ :=
        IntermediateField.adjoin.powerBasis_gen _
      rw [← hgen, PowerBasis.lift_gen]
    let toL_Qω : (ℚ⟮ω⟯)⟮β⟯ ≃ₐ[ℚ⟮ω⟯] L :=
      (IntermediateField.equivOfEq hL_over_Qω).trans IntermediateField.topEquiv
    let ρ_end : L →ₐ[ℚ⟮ω⟯] L := ρ_hom.comp toL_Qω.symm.toAlgHom
    have hρ_bij : Function.Bijective ρ_end :=
      ⟨ρ_end.toRingHom.injective,
        LinearMap.surjective_of_injective (f := ρ_end.toLinearMap) ρ_end.toRingHom.injective⟩
    let ρ_Qω : L ≃ₐ[ℚ⟮ω⟯] L := AlgEquiv.ofBijective ρ_end hρ_bij
    refine ⟨ρ_Qω.restrictScalars ℚ,
      ρ_Qω.commutes ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩, ?_⟩
    change ρ_hom (toL_Qω.symm β) = ω * β
    have hsymm_β : toL_Qω.symm β = ⟨β, IntermediateField.mem_adjoin_simple_self ℚ⟮ω⟯ β⟩ := by
      apply toL_Qω.injective
      simp [toL_Qω]
    rw [hsymm_β, hρ_hom_β]
  have mk_Qβ_aut : ∀ (c : ℕ), Nat.Coprime c 15 →
      ∃ ψ : L ≃ₐ[ℚ] L, ψ ω = ω ^ c ∧ ψ β = β := by
    intro c hcop
    have hωc_prim : IsPrimitiveRoot (ω ^ c) 15 := hω.pow_of_coprime c hcop
    have hmin_Qβ : minpoly ℚ⟮β⟯ ω = (Polynomial.cyclotomic 15 ℚ).map (algebraMap ℚ ℚ⟮β⟯) := by
      have hω_int_Qβ : IsIntegral ℚ⟮β⟯ ω := Algebra.IsIntegral.isIntegral ω
      have hdvd : minpoly ℚ⟮β⟯ ω ∣ (Polynomial.cyclotomic 15 ℚ).map (algebraMap ℚ ℚ⟮β⟯) := by
        rw [← hmin_ω]
        refine minpoly.dvd ℚ⟮β⟯ ω ?_
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap ℚ⟮β⟯ L).comp (algebraMap ℚ ℚ⟮β⟯) = algebraMap ℚ L :=
          Subsingleton.elim _ _
        rw [hcomp, ← Polynomial.aeval_def]
        exact minpoly.aeval ℚ ω
      have hdeg_eq : (minpoly ℚ⟮β⟯ ω).natDegree = 8 := by
        rw [← IntermediateField.adjoin.finrank hω_int_Qβ]
        have htop_eq : ((ℚ⟮β⟯)⟮ω⟯ : IntermediateField ℚ⟮β⟯ L) = ⊤ := hL_over_Qβ
        rw [htop_eq, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfin_QβL]
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic hω_int_Qβ)
        ((Polynomial.cyclotomic.monic 15 ℚ).map _)
        hdvd
        (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℚ⟮β⟯).injective,
              Polynomial.natDegree_cyclotomic, hdeg_eq]; decide)).symm
    let pbω : PowerBasis ℚ⟮β⟯ (ℚ⟮β⟯)⟮ω⟯ :=
      IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral ω)
    have hgen_ω : algebraMap (ℚ⟮β⟯)⟮ω⟯ L pbω.gen = ω :=
      congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
    have hωc_root : Polynomial.aeval (ω ^ c) (minpoly ℚ⟮β⟯ pbω.gen) = 0 := by
      have hmin_eq : minpoly ℚ⟮β⟯ pbω.gen = minpoly ℚ⟮β⟯ ω := by
        rw [← minpoly.algebraMap_eq (algebraMap (ℚ⟮β⟯)⟮ω⟯ L).injective, hgen_ω]
      rw [hmin_eq, hmin_Qβ, Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap ℚ⟮β⟯ L).comp (algebraMap ℚ ℚ⟮β⟯) = algebraMap ℚ L :=
        Subsingleton.elim _ _
      rw [hcomp, ← Polynomial.eval_map]
      have hr : Polynomial.IsRoot (Polynomial.cyclotomic 15 L) (ω ^ c) :=
        hωc_prim.isRoot_cyclotomic (by decide)
      rwa [← Polynomial.map_cyclotomic 15 (algebraMap ℚ L)] at hr
    let toL_Qβ : (ℚ⟮β⟯)⟮ω⟯ ≃ₐ[ℚ⟮β⟯] L :=
      (IntermediateField.equivOfEq hL_over_Qβ).trans IntermediateField.topEquiv
    let ψ_hom : (ℚ⟮β⟯)⟮ω⟯ →ₐ[ℚ⟮β⟯] L := pbω.lift (ω ^ c) hωc_root
    let ψ_end : L →ₐ[ℚ⟮β⟯] L := ψ_hom.comp toL_Qβ.symm.toAlgHom
    have hψ_bij : Function.Bijective ψ_end :=
      ⟨ψ_end.toRingHom.injective,
        LinearMap.surjective_of_injective (f := ψ_end.toLinearMap) ψ_end.toRingHom.injective⟩
    let ψ_Qβ : L ≃ₐ[ℚ⟮β⟯] L := AlgEquiv.ofBijective ψ_end hψ_bij
    refine ⟨ψ_Qβ.restrictScalars ℚ, ?_,
      ψ_Qβ.commutes ⟨β, IntermediateField.mem_adjoin_simple_self ℚ β⟩⟩
    change ψ_hom (toL_Qβ.symm ω) = ω ^ c
    have hsymm_ω : toL_Qβ.symm ω = ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ⟮β⟯ ω⟩ := by
      apply toL_Qβ.injective; simp [toL_Qβ]
    have hgen : pbω.gen = ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ⟮β⟯ ω⟩ :=
      IntermediateField.adjoin.powerBasis_gen _
    rw [hsymm_ω, ← hgen, PowerBasis.lift_gen]
  obtain ⟨σ, hσ_ω, hσ_β⟩ := mk_Qβ_aut 13 (by decide)
  obtain ⟨τ, hτ_ω, hτ_β⟩ := mk_Qβ_aut 14 (by decide)
  have hρ_pow_ω : ∀ k : ℕ, (ρ ^ k) ω = ω := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hρ_ω]
  have hρ_pow_β : ∀ k : ℕ, (ρ ^ k) β = ω ^ k * β := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρ_ω, hρ_β, ← mul_assoc, ← pow_succ]
  have hσ_pow_ω : ∀ k : ℕ, (σ ^ k) ω = ω ^ (13 ^ k) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσ_ω, ← pow_mul, ← pow_succ]
  have hσ_pow_β : ∀ k : ℕ, (σ ^ k) β = β := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσ_β]
  have hτ_pow_ω : ∀ k : ℕ, (τ ^ k) ω = ω ^ (14 ^ k) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hτ_ω, ← pow_mul, ← pow_succ]
  have hτ_pow_β : ∀ k : ℕ, (τ ^ k) β = β := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hτ_β]
  have hρ15 : ρ ^ 15 = 1 :=
    aut_ext _ _ (by rw [hρ_pow_ω]; rfl) (by rw [hρ_pow_β, hω.pow_eq_one, one_mul]; rfl)
  have hσ4 : σ ^ 4 = 1 := by
    refine aut_ext _ _ ?_ (by rw [hσ_pow_β]; rfl)
    rw [hσ_pow_ω]
    change ω ^ 28561 = ω
    have hmod : 28561 = 15 * 1904 + 1 := by decide
    rw [hmod, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul, pow_one]
  have hτ2 : τ ^ 2 = 1 := by
    refine aut_ext _ _ ?_ (by rw [hτ_pow_β]; rfl)
    rw [hτ_pow_ω]
    change ω ^ 196 = ω
    have hmod : 196 = 15 * 13 + 1 := by decide
    rw [hmod, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul, pow_one]
  have hrel_σρ : σ⁻¹ * ρ * σ = ρ ^ 7 := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    refine aut_ext _ _ ?_ ?_
    · simp [AlgEquiv.mul_apply, hσ_ω, hρ_ω, hρ_pow_ω]
    · simp only [AlgEquiv.mul_apply, hσ_β, hρ_β, hρ_pow_β, map_mul, map_pow, hσ_ω]
      have h91 : (ω ^ 13) ^ 7 = ω := by
        rw [← pow_mul]
        have hm : 13 * 7 = 15 * 6 + 1 := by decide
        rw [hm, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul, pow_one]
      rw [h91]
  have hrel_τρ : τ⁻¹ * ρ * τ = ρ ^ 14 := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    refine aut_ext _ _ ?_ ?_
    · simp [AlgEquiv.mul_apply, hτ_ω, hρ_ω, hρ_pow_ω]
    · simp only [AlgEquiv.mul_apply, hτ_β, hρ_β, hρ_pow_β, map_mul, map_pow, hτ_ω]
      have h196 : (ω ^ 14) ^ 14 = ω := by
        rw [← pow_mul]
        have hm : 14 * 14 = 15 * 13 + 1 := by decide
        rw [hm, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul, pow_one]
      rw [h196]
  have hrel_τστ : τ⁻¹ * σ * τ = σ := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    refine aut_ext _ _ ?_ ?_
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ_ω, map_pow, hσ_ω, hσ_ω, map_pow, hτ_ω,
        ← pow_mul, ← pow_mul, Nat.mul_comm 13 14]
    · simp [AlgEquiv.mul_apply, hτ_β, hσ_β]
  have hord_ρ : orderOf ρ = 15 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by decide) hρ15 fun p hp hdvd hpow1 => ?_
    have hm : p = 3 ∨ p = 5 := by
      have hle : p ≤ 15 := Nat.le_of_dvd (by decide) hdvd
      interval_cases p <;>
        first
        | exact Or.inl rfl
        | exact Or.inr rfl
        | exact absurd hp (by decide)
        | exact absurd hdvd (by decide)
    rcases hm with rfl | rfl
    · have hb := congrArg (fun g : L ≃ₐ[ℚ] L => g β) hpow1
      simp only [hρ_pow_β, AlgEquiv.one_apply] at hb
      have hw5 : ω ^ 5 = 1 := mul_right_cancel₀ hβ_ne (hb.trans (one_mul β).symm)
      exact absurd (hω.dvd_of_pow_eq_one 5 hw5) (by decide)
    · have hb := congrArg (fun g : L ≃ₐ[ℚ] L => g β) hpow1
      simp only [hρ_pow_β, AlgEquiv.one_apply] at hb
      have hw3 : ω ^ 3 = 1 := mul_right_cancel₀ hβ_ne (hb.trans (one_mul β).symm)
      exact absurd (hω.dvd_of_pow_eq_one 3 hw3) (by decide)
  have hord_σ : orderOf σ = 4 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by decide) hσ4 fun p hp hdvd hpow1 => ?_
    have hp2 : p = 2 := by
      have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hdvd
      interval_cases p <;>
        first
        | rfl
        | exact absurd hp (by decide)
        | exact absurd hdvd (by decide)
    subst hp2
    have hw := congrArg (fun g : L ≃ₐ[ℚ] L => g ω) hpow1
    simp only [hσ_pow_ω, AlgEquiv.one_apply] at hw
    have hmod : 13 ^ 2 ≡ 1 [MOD 15] :=
      (isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) hω).mp (hw.trans (pow_one ω).symm)
    exact absurd hmod (by decide)
  have hord_τ : orderOf τ = 2 := by
    refine orderOf_eq_prime hτ2 fun h1 => ?_
    have hw := congrArg (fun g : L ≃ₐ[ℚ] L => g ω) h1
    simp only [hτ_ω, AlgEquiv.one_apply] at hw
    have hmod : 14 ≡ 1 [MOD 15] :=
      (isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) hω).mp (hw.trans (pow_one ω).symm)
    exact absurd hmod (by decide)
  have hclosure : Subgroup.closure ({ρ, σ, τ} : Set (L ≃ₐ[ℚ] L)) = ⊤ := by
    let H := Subgroup.closure ({ρ, σ, τ} : Set (L ≃ₐ[ℚ] L))
    have hρH : ρ ∈ H := Subgroup.subset_closure (by simp)
    have hσH : σ ∈ H := Subgroup.subset_closure (by simp)
    have hτH : τ ∈ H := Subgroup.subset_closure (by simp)
    let enum120 : Fin 15 × Fin 4 × Fin 2 → H := fun ⟨i, a, b⟩ =>
      ⟨ρ ^ (i : ℕ) * σ ^ (a : ℕ) * τ ^ (b : ℕ),
        mul_mem (mul_mem (pow_mem hρH _) (pow_mem hσH _)) (pow_mem hτH _)⟩
    have henum_inj : Function.Injective enum120 := by
      rintro ⟨i₁, a₁, b₁⟩ ⟨i₂, a₂, b₂⟩ heq
      have hg : ρ ^ (i₁ : ℕ) * σ ^ (a₁ : ℕ) * τ ^ (b₁ : ℕ) =
          ρ ^ (i₂ : ℕ) * σ ^ (a₂ : ℕ) * τ ^ (b₂ : ℕ) := congrArg Subtype.val heq
      have hβ_eq := congrArg (fun g : L ≃ₐ[ℚ] L => g β) hg
      simp only [AlgEquiv.mul_apply, hτ_pow_β, hσ_pow_β, hρ_pow_β] at hβ_eq
      have hpow_i : ω ^ (i₁ : ℕ) = ω ^ (i₂ : ℕ) := mul_right_cancel₀ hβ_ne hβ_eq
      have hi_eq : i₁ = i₂ := Fin.ext (hω.pow_inj i₁.isLt i₂.isLt hpow_i)
      subst hi_eq
      have hg' : σ ^ (a₁ : ℕ) * τ ^ (b₁ : ℕ) = σ ^ (a₂ : ℕ) * τ ^ (b₂ : ℕ) := by
        simpa [mul_assoc] using hg
      have hω_eq := congrArg (fun g : L ≃ₐ[ℚ] L => g ω) hg'
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ_pow_ω, hτ_pow_ω, map_pow, map_pow,
        hσ_pow_ω, hσ_pow_ω, ← pow_mul, ← pow_mul] at hω_eq
      have hmod : 13 ^ (a₁ : ℕ) * 14 ^ (b₁ : ℕ) ≡ 13 ^ (a₂ : ℕ) * 14 ^ (b₂ : ℕ) [MOD 15] :=
        (isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) hω).mp hω_eq
      have hab : a₁ = a₂ ∧ b₁ = b₂ := by
        fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
          first | exact ⟨rfl, rfl⟩ | exact absurd hmod (by decide)
      rw [hab.1, hab.2]
    let _ : Fintype (L ≃ₐ[ℚ] L) := Fintype.ofFinite _
    let _ : Fintype H := Fintype.ofFinite H
    have hH_ge : 120 ≤ Fintype.card H := by
      have h120 : Fintype.card (Fin 15 × Fin 4 × Fin 2) = 120 := by simp
      rw [← h120]
      exact Fintype.card_le_of_injective enum120 henum_inj
    have hG_card : Fintype.card (L ≃ₐ[ℚ] L) = 120 := by
      rw [← Nat.card_eq_fintype_card]; exact hcardG
    have hH_le : Fintype.card H ≤ 120 := by
      rw [← hG_card]
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have hH_eq : Fintype.card H = 120 := le_antisymm hH_le hH_ge
    have hindex1 : H.index = 1 := by
      have hmul := Subgroup.card_mul_index H
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hH_eq, hG_card] at hmul
      omega
    exact Subgroup.index_eq_one.mp hindex1
  exact ⟨hcardG, ρ, σ, τ, hclosure, hord_ρ, hord_σ, hord_τ,
    hρ15, hσ4, hτ2, hrel_σρ, hrel_τρ, hrel_τστ⟩

/-! ### Exercise 16.3: Splitting field of `x⁴ - 5` over `ℚ` (printed p. 124 / PDF p. 132) -/

/-- Explicit carrier Finsets of the `10` subgroups of `DihedralGroup 4` (`D₄` of order `8`):
`0`: `D₄` (`8`, normal); `1`: `⟨r⟩` (`4`, normal); `2`: `⟨r², sr₀⟩` (`4`, normal);
`3`: `⟨r², sr₁⟩` (`4`, normal); `4`: `⟨r²⟩ = Z(D₄)` (`2`, normal);
`5`–`8`: `⟨sr₀⟩, ⟨sr₂⟩, ⟨sr₃⟩, ⟨sr₁⟩` (`2` each, non-normal); `9`: `{1}` (`1`, normal). -/
def d4SubgroupFinset : Fin 10 → Finset (DihedralGroup 4)
  | 0 => Finset.univ
  | 1 => {.r 0, .r 1, .r 2, .r 3}
  | 2 => {.r 0, .r 2, .sr 0, .sr 2}
  | 3 => {.r 0, .r 2, .sr 1, .sr 3}
  | 4 => {.r 0, .r 2}
  | 5 => {.r 0, .sr 0}
  | 6 => {.r 0, .sr 2}
  | 7 => {.r 0, .sr 3}
  | 8 => {.r 0, .sr 1}
  | 9 => {.r 0}

/-- The `10` subgroups of `DihedralGroup 4`. -/
def d4Subgroup (k : Fin 10) : Subgroup (DihedralGroup 4) where
  carrier := (d4SubgroupFinset k : Set (DihedralGroup 4))
  mul_mem' := by
    have hdec : ∀ (k : Fin 10) (a b : DihedralGroup 4),
        a ∈ d4SubgroupFinset k → b ∈ d4SubgroupFinset k → a * b ∈ d4SubgroupFinset k := by decide
    intro a b ha hb
    exact hdec k a b ha hb
  one_mem' := by
    have hdec : ∀ k : Fin 10, (1 : DihedralGroup 4) ∈ d4SubgroupFinset k := by decide
    exact hdec k
  inv_mem' := by
    have hdec : ∀ (k : Fin 10) (a : DihedralGroup 4),
        a ∈ d4SubgroupFinset k → a⁻¹ ∈ d4SubgroupFinset k := by decide
    intro a ha
    exact hdec k a ha

@[simp] theorem mem_d4Subgroup_iff (k : Fin 10) (x : DihedralGroup 4) :
    x ∈ d4Subgroup k ↔ x ∈ d4SubgroupFinset k := Iff.rfl

/-- Complete classification of the `10` subgroups of `DihedralGroup 4`: orders, bijectivity
(exhaustiveness and pairwise distinctness), and normality (`6` normal, `4` non-normal). -/
theorem d4Subgroup_classification :
    (∀ k : Fin 10, Nat.card (d4Subgroup k) = (![8, 4, 4, 4, 2, 2, 2, 2, 2, 1] : Fin 10 → ℕ) k) ∧
    Function.Bijective d4Subgroup ∧
    (∀ k : Fin 10, (d4Subgroup k).Normal ↔ k ∈ ({0, 1, 2, 3, 4, 9} : Set (Fin 10))) := by
  have hcard : ∀ k : Fin 10,
      Nat.card (d4Subgroup k) = (![8, 4, 4, 4, 2, 2, 2, 2, 2, 1] : Fin 10 → ℕ) k := by
    intro k
    let eSub : d4Subgroup k ≃ {x // x ∈ d4SubgroupFinset k} := Equiv.refl _
    rw [Nat.card_congr eSub, Nat.card_eq_fintype_card, Fintype.card_coe]
    fin_cases k <;> decide
  have hinj : Function.Injective d4Subgroup := by
    have hsep : ∀ i j : Fin 10, i ≠ j →
        ∃ x : DihedralGroup 4, ¬ (x ∈ d4SubgroupFinset i ↔ x ∈ d4SubgroupFinset j) := by decide
    intro i j hij
    by_contra hne
    obtain ⟨x, hx⟩ := hsep i j hne
    apply hx
    rw [← mem_d4Subgroup_iff, ← mem_d4Subgroup_iff, hij]
  have hsurj : Function.Surjective d4Subgroup := by
    intro H
    have hr0 : DihedralGroup.r 0 ∈ H := H.one_mem
    by_cases hr13 : DihedralGroup.r 1 ∈ H ∨ DihedralGroup.r 3 ∈ H
    · have hr1 : DihedralGroup.r 1 ∈ H := by
        rcases hr13 with h | h
        · exact h
        · have hinv : (DihedralGroup.r 3 : DihedralGroup 4)⁻¹ = .r 1 := by decide
          rw [← hinv]; exact H.inv_mem h
      have hr2 : DihedralGroup.r 2 ∈ H := by
        have hm : (DihedralGroup.r 1 : DihedralGroup 4) * .r 1 = .r 2 := by decide
        rw [← hm]; exact H.mul_mem hr1 hr1
      have hr3 : DihedralGroup.r 3 ∈ H := by
        have hm : (DihedralGroup.r 2 : DihedralGroup 4) * .r 1 = .r 3 := by decide
        rw [← hm]; exact H.mul_mem hr2 hr1
      by_cases hsr : ∃ k : ZMod 4, DihedralGroup.sr k ∈ H
      · rcases hsr with ⟨k₀, hk₀⟩
        refine ⟨0, ?_⟩
        ext x; rw [mem_d4Subgroup_iff]
        simp only [d4SubgroupFinset, Finset.mem_univ, true_iff]
        rcases x with a | a
        · fin_cases a <;> assumption
        · have hm : DihedralGroup.sr k₀ * DihedralGroup.r (a - k₀) = DihedralGroup.sr a := by
            rw [DihedralGroup.sr_mul_r]; simp
          rw [← hm]
          refine H.mul_mem hk₀ ?_
          generalize a - k₀ = c
          fin_cases c <;> assumption
      · rw [not_exists] at hsr
        have hns0 : DihedralGroup.sr 0 ∉ H := hsr 0
        have hns1 : DihedralGroup.sr 1 ∉ H := hsr 1
        have hns2 : DihedralGroup.sr 2 ∉ H := hsr 2
        have hns3 : DihedralGroup.sr 3 ∉ H := hsr 3
        refine ⟨1, ?_⟩
        ext x; rw [mem_d4Subgroup_iff]
        rcases x with a | a <;> fin_cases a
        all_goals first
          | exact ⟨fun _ => by assumption, fun _ => by decide⟩
          | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
    · rw [not_or] at hr13
      rcases hr13 with ⟨hnr1, hnr3⟩
      by_cases hr2 : DihedralGroup.r 2 ∈ H
      · by_cases hsr02 : DihedralGroup.sr 0 ∈ H ∨ DihedralGroup.sr 2 ∈ H
        · have hs0 : DihedralGroup.sr 0 ∈ H := by
            rcases hsr02 with h | h
            · exact h
            · have hm : (DihedralGroup.sr 2 : DihedralGroup 4) * .r 2 = .sr 0 := by decide
              rw [← hm]; exact H.mul_mem h hr2
          have hs2 : DihedralGroup.sr 2 ∈ H := by
            have hm : (DihedralGroup.sr 0 : DihedralGroup 4) * .r 2 = .sr 2 := by decide
            rw [← hm]; exact H.mul_mem hs0 hr2
          have hns1 : DihedralGroup.sr 1 ∉ H := fun h => hnr1 (by
            have hm : (DihedralGroup.sr 0 : DihedralGroup 4) * .sr 1 = .r 1 := by decide
            rw [← hm]; exact H.mul_mem hs0 h)
          have hns3 : DihedralGroup.sr 3 ∉ H := fun h => hnr3 (by
            have hm : (DihedralGroup.sr 0 : DihedralGroup 4) * .sr 3 = .r 3 := by decide
            rw [← hm]; exact H.mul_mem hs0 h)
          refine ⟨2, ?_⟩
          ext x; rw [mem_d4Subgroup_iff]
          rcases x with a | a <;> fin_cases a
          all_goals first
            | exact ⟨fun _ => by assumption, fun _ => by decide⟩
            | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
        · rw [not_or] at hsr02
          rcases hsr02 with ⟨hns0, hns2⟩
          by_cases hsr13 : DihedralGroup.sr 1 ∈ H ∨ DihedralGroup.sr 3 ∈ H
          · have hs1 : DihedralGroup.sr 1 ∈ H := by
              rcases hsr13 with h | h
              · exact h
              · have hm : (DihedralGroup.sr 3 : DihedralGroup 4) * .r 2 = .sr 1 := by decide
                rw [← hm]; exact H.mul_mem h hr2
            have hs3 : DihedralGroup.sr 3 ∈ H := by
              have hm : (DihedralGroup.sr 1 : DihedralGroup 4) * .r 2 = .sr 3 := by decide
              rw [← hm]; exact H.mul_mem hs1 hr2
            refine ⟨3, ?_⟩
            ext x; rw [mem_d4Subgroup_iff]
            rcases x with a | a <;> fin_cases a
            all_goals first
              | exact ⟨fun _ => by assumption, fun _ => by decide⟩
              | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
          · rw [not_or] at hsr13
            rcases hsr13 with ⟨hns1, hns3⟩
            refine ⟨4, ?_⟩
            ext x; rw [mem_d4Subgroup_iff]
            rcases x with a | a <;> fin_cases a
            all_goals first
              | exact ⟨fun _ => by assumption, fun _ => by decide⟩
              | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
      · have at_most_one_sr : ∀ a b : ZMod 4, a ≠ b →
            DihedralGroup.sr a ∈ H → DihedralGroup.sr b ∉ H := by
          intro a b hab ha hb
          have hm := H.mul_mem ha hb
          rw [DihedralGroup.sr_mul_sr] at hm
          fin_cases a <;> fin_cases b
          all_goals first | exact hab rfl | skip
          all_goals
            change DihedralGroup.r _ ∈ H at hm
            first | exact hnr1 hm | exact hr2 hm | exact hnr3 hm
        by_cases hs0 : DihedralGroup.sr 0 ∈ H
        · have hns1 : DihedralGroup.sr 1 ∉ H := at_most_one_sr 0 1 (by decide) hs0
          have hns2 : DihedralGroup.sr 2 ∉ H := at_most_one_sr 0 2 (by decide) hs0
          have hns3 : DihedralGroup.sr 3 ∉ H := at_most_one_sr 0 3 (by decide) hs0
          refine ⟨5, ?_⟩
          ext x; rw [mem_d4Subgroup_iff]
          rcases x with a | a <;> fin_cases a
          all_goals first
            | exact ⟨fun _ => by assumption, fun _ => by decide⟩
            | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
        · by_cases hs2 : DihedralGroup.sr 2 ∈ H
          · have hns1 : DihedralGroup.sr 1 ∉ H := at_most_one_sr 2 1 (by decide) hs2
            have hns3 : DihedralGroup.sr 3 ∉ H := at_most_one_sr 2 3 (by decide) hs2
            refine ⟨6, ?_⟩
            ext x; rw [mem_d4Subgroup_iff]
            rcases x with a | a <;> fin_cases a
            all_goals first
              | exact ⟨fun _ => by assumption, fun _ => by decide⟩
              | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
          · by_cases hs3 : DihedralGroup.sr 3 ∈ H
            · have hns1 : DihedralGroup.sr 1 ∉ H := at_most_one_sr 3 1 (by decide) hs3
              refine ⟨7, ?_⟩
              ext x; rw [mem_d4Subgroup_iff]
              rcases x with a | a <;> fin_cases a
              all_goals first
                | exact ⟨fun _ => by assumption, fun _ => by decide⟩
                | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
            · by_cases hs1 : DihedralGroup.sr 1 ∈ H
              · refine ⟨8, ?_⟩
                ext x; rw [mem_d4Subgroup_iff]
                rcases x with a | a <;> fin_cases a
                all_goals first
                  | exact ⟨fun _ => by assumption, fun _ => by decide⟩
                  | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
              · refine ⟨9, ?_⟩
                ext x; rw [mem_d4Subgroup_iff]
                rcases x with a | a <;> fin_cases a
                all_goals first
                  | exact ⟨fun _ => by assumption, fun _ => by decide⟩
                  | exact ⟨fun h => absurd h (by decide), fun h => absurd h (by assumption)⟩
  have hnorm_dec : ∀ k : Fin 10,
      (∀ (g : DihedralGroup 4), ∀ h ∈ d4SubgroupFinset k, g * h * g⁻¹ ∈ d4SubgroupFinset k) ↔
        k ∈ ({0, 1, 2, 3, 4, 9} : Set (Fin 10)) := by
    intro k
    fin_cases k <;> simp <;> decide
  have hnorm : ∀ k : Fin 10,
      (d4Subgroup k).Normal ↔ k ∈ ({0, 1, 2, 3, 4, 9} : Set (Fin 10)) := by
    intro k
    rw [← hnorm_dec k]
    constructor
    · intro hN g h hh
      exact hN.conj_mem h hh g
    · intro hc
      exact ⟨fun h hh g => hc g h hh⟩
  exact ⟨hcard, ⟨hinj, hsurj⟩, hnorm⟩

/-- The `10` explicit intermediate fields between `L` and `ℚ` for a splitting field `L : ℚ` of
`x⁴ - 5` with `α⁴ = 5` and `im² = -1` (`Exercise 16.3`, printed p. 124):
`0`: `ℚ`; `1`: `ℚ(i)`; `2`: `ℚ(√5) = ℚ(α²)`; `3`: `ℚ(i√5) = ℚ(iα²)`;
`4`: `ℚ(i, √5) = ℚ(i, α²)`; `5`: `ℚ(⁴√5) = ℚ(α)`; `6`: `ℚ(i⁴√5) = ℚ(iα)`;
`7`: `ℚ((1 + i)⁴√5) = ℚ((1 + i)α)`; `8`: `ℚ((1 - i)⁴√5) = ℚ((1 - i)α)`; `9`: `L`. -/
noncomputable def ex163Field {L : Type u} [Field L] [Algebra ℚ L] (α im : L) :
    Fin 10 → IntermediateField ℚ L
  | 0 => ⊥
  | 1 => ℚ⟮im⟯
  | 2 => ℚ⟮α ^ 2⟯
  | 3 => ℚ⟮im * α ^ 2⟯
  | 4 => IntermediateField.adjoin ℚ ({im, α ^ 2} : Set L)
  | 5 => ℚ⟮α⟯
  | 6 => ℚ⟮im * α⟯
  | 7 => ℚ⟮(1 + im) * α⟯
  | 8 => ℚ⟮(1 - im) * α⟯
  | 9 => ⊤

/-- **Exercise 16.3** (§16.1, printed p. 124 / PDF p. 132; `QUEUE.md` fidelity hold for open-ended
*"What is its Galois group? List ... and determine..."* prompt):
*"Let `L : ℚ` be a splitting field extension for `x⁴ - 5` over `ℚ`. What is its Galois group? List
the fields intermediate between `L` and `ℚ`, and determine which of them are normal over `ℚ`."*

Proves universally for **every** splitting field extension `L : ℚ` of `x⁴ - 5` (together with an
explicit complex witness `ℚ(⁴√5, i) ⊆ ℂ`):
1. `[L : ℚ] = 8` and `Γ(L : ℚ) ≅ D₄` (`DihedralGroup 4`, dihedral group of order `8`);
2. There exist `α, i ∈ L` with `α⁴ = 5` and `i² = -1` such that `ex163Field α i : Fin 10 → IntermediateField ℚ L`
   is **bijective** (listing all `10` pairwise distinct intermediate fields exhaustively), with
   degrees `[1, 2, 2, 2, 4, 4, 4, 4, 4, 8]`;
3. Exactly **`6`** intermediate fields (`ℚ`, `ℚ(i)`, `ℚ(α²)`, `ℚ(iα²)`, `ℚ(i, α²)`, `L`) are normal
   over `ℚ`, and the remaining **`4`** (`ℚ(α)`, `ℚ(iα)`, `ℚ((1 + i)α)`, `ℚ((1 - i)α)`) are non-normal. -/
theorem exercise_16_3 :
    (∃ K₃ : IntermediateField ℚ ℂ,
      IsGarlingSplittingFieldExtension ℚ K₃ (Polynomial.X ^ 4 - Polynomial.C (5 : ℚ)) ∧
      Module.finrank ℚ K₃ = 8) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 - Polynomial.C (5 : ℚ)) →
      Module.finrank ℚ L = 8 ∧
      extDegree ℚ L = 8 ∧
      Nat.card (GarlingGaloisGroup ℚ L) = 8 ∧
      Nonempty (GarlingGaloisGroup ℚ L ≃* DihedralGroup 4) ∧
      ∃ α im : L,
        α ^ 4 = 5 ∧
        im ^ 2 = -1 ∧
        Function.Bijective (ex163Field α im) ∧
        (∀ k : Fin 10,
          Module.finrank ℚ (ex163Field α im k) =
            (![1, 2, 2, 2, 4, 4, 4, 4, 4, 8] : Fin 10 → ℕ) k) ∧
        (∀ k : Fin 10,
          IsGarlingNormal ℚ (ex163Field α im k) ↔
            k ∈ ({0, 1, 2, 3, 4, 9} : Set (Fin 10)))) := by
  let f : ℚ[X] := Polynomial.X ^ 4 - Polynomial.C (5 : ℚ)
  have hf_eq : (Polynomial.X ^ 4 - 5 : ℚ[X]) = f := by simp [f, Polynomial.C_ofNat]
  have hexC : ∃ K₃ : IntermediateField ℚ ℂ,
      IsGarlingSplittingFieldExtension ℚ K₃ f ∧ Module.finrank ℚ K₃ = 8 := by
    obtain ⟨_, _, hsf3, hfin3, _, _⟩ := exercise_7_7
    rw [hf_eq] at hsf3
    exact ⟨_, hsf3, hfin3⟩
  refine ⟨hexC, fun L _ _ hsf => ?_⟩
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  have hchar4 : ¬ (ringChar ℚ ∣ 4) := by rw [ringChar.eq_zero]; simp
  obtain ⟨_, hmonic, _, _, hgsep⟩ :=
    X_pow_sub_C_separable_of_ne_zero (K := ℚ) (n := 4) (θ := 5) (by norm_num) hchar4
  have hgal : IsGarlingGaloisExtension ℚ L :=
    isGarlingGalois_of_splittingField hmonic.ne_zero hsf hgsep
  have _ : FiniteDimensional ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.1
  have _ : IsGalois ℚ L := (isGarlingGaloisExtension_iff ℚ L).mp hgal |>.2
  obtain ⟨K₃, hsfK₃, hfinK₃⟩ := hexC
  obtain ⟨eK₃L⟩ := splitting_field_unique_up_to_algEquiv hsfK₃ hsf
  have hfinL : Module.finrank ℚ L = 8 := by
    rw [← eK₃L.toLinearEquiv.finrank_eq, hfinK₃]
  have hextL : extDegree ℚ L = 8 := by
    rw [extDegree_eq_finrank ℚ L, hfinL]; rfl
  have hcardG : Nat.card (GarlingGaloisGroup ℚ L) = 8 := by
    change Nat.card (L ≃ₐ[ℚ] L) = 8
    rw [IsGalois.card_aut_eq_finrank ℚ L, hfinL]
  obtain ⟨_, ⟨im, him_prim⟩, h161⟩ := theorem_16_1 (by norm_num) hchar4 hsf
  obtain ⟨_, ⟨α, hα_ev⟩, hfac⟩ := (section_16_1_root_factorization (by norm_num) hchar4 hsf).2.2
  have hα4 : α ^ 4 = 5 := by
    have h1 := hα_ev
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat, sub_eq_zero] at h1
    exact h1
  have hα_ne : α ≠ 0 := by
    intro h0; rw [h0, zero_pow (by decide)] at hα4; norm_num at hα4
  have hα2_ne : α ^ 2 ≠ 0 := pow_ne_zero 2 hα_ne
  have him_sq : im ^ 2 = -1 := by
    have h4 : im ^ 4 = 1 := him_prim.pow_eq_one
    have hne2 : im ^ 2 ≠ 1 := fun h2 =>
      absurd (him_prim.dvd_of_pow_eq_one 2 h2) (by decide)
    have hfac4 : (im ^ 2 - 1) * (im ^ 2 + 1) = 0 := by
      calc (im ^ 2 - 1) * (im ^ 2 + 1) = im ^ 4 - 1 := by ring
        _ = 0 := by rw [h4, sub_self]
    rcases mul_eq_zero.mp hfac4 with h1 | h2
    · exact (hne2 (sub_eq_zero.mp h1)).elim
    · exact eq_neg_of_add_eq_zero_left h2
  have him_ne : im ≠ 0 := by
    intro h0; rw [h0, zero_pow (by decide)] at him_sq; norm_num at him_sq
  have hf_irr : Irreducible f := (exercise_5_7 (p := 5) (n := 4) (by decide) (by decide)).1
  have hdeg_im : Module.finrank ℚ ℚ⟮im⟯ = 2 := by
    have hm : minpoly ℚ im = Polynomial.cyclotomic 4 ℚ :=
      (Polynomial.cyclotomic_eq_minpoly_rat him_prim (by decide)).symm
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral im), hm,
      Polynomial.natDegree_cyclotomic]
    decide
  have hdeg_α : Module.finrank ℚ ℚ⟮α⟯ = 4 := by
    have hm : minpoly ℚ α = f :=
      (minpoly.eq_of_irreducible_of_monic hf_irr hα_ev hmonic).symm
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hm,
      Polynomial.natDegree_X_pow_sub_C]
  have hfin_imL : Module.finrank ℚ⟮im⟯ L = 4 := by
    have hmul := Module.finrank_mul_finrank ℚ ℚ⟮im⟯ L
    rw [hdeg_im, hfinL] at hmul; omega
  have hfin_αL : Module.finrank ℚ⟮α⟯ L = 2 := by
    have hmul := Module.finrank_mul_finrank ℚ ℚ⟮α⟯ L
    rw [hdeg_α, hfinL] at hmul; omega
  obtain ⟨_, _, _, _, _, hirr_im, _⟩ := h161 im him_prim
  have hf_im_irr : Irreducible (f.map (algebraMap ℚ ℚ⟮im⟯)) := hirr_im.mpr hfin_imL
  have _ : FiniteDimensional ℚ⟮im⟯ L := Module.Finite.right ℚ ℚ⟮im⟯ L
  have _ : FiniteDimensional ℚ⟮α⟯ L := Module.Finite.right ℚ ℚ⟮α⟯ L
  have hL_over_im : IntermediateField.adjoin ℚ⟮im⟯ ({α} : Set L) = ⊤ := by
    let E : IntermediateField ℚ L :=
      (IntermediateField.adjoin ℚ⟮im⟯ ({α} : Set L)).restrictScalars ℚ
    have himE : im ∈ E :=
      (IntermediateField.adjoin ℚ⟮im⟯ ({α} : Set L)).algebraMap_mem
        ⟨im, IntermediateField.mem_adjoin_simple_self ℚ im⟩
    have hαE : α ∈ E := IntermediateField.mem_adjoin_simple_self ℚ⟮im⟯ α
    have hE_top : E = ⊤ := by
      by_contra hne
      refine hsf.2 E hne ⟨4, 1, fun k => ⟨im ^ (k : ℕ) * α, mul_mem (pow_mem himE _) hαE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc :
          (f.map (@algebraMap ℚ E _ _ E.algebra')).map (algebraMap E L) = f.map (algebraMap ℚ L) := by
        rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
      rw [hmc, hfac im α him_prim hα_ev]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have hL_over_α : IntermediateField.adjoin ℚ⟮α⟯ ({im} : Set L) = ⊤ := by
    let E : IntermediateField ℚ L :=
      (IntermediateField.adjoin ℚ⟮α⟯ ({im} : Set L)).restrictScalars ℚ
    have himE : im ∈ E := IntermediateField.mem_adjoin_simple_self ℚ⟮α⟯ im
    have hαE : α ∈ E :=
      (IntermediateField.adjoin ℚ⟮α⟯ ({im} : Set L)).algebraMap_mem
        ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩
    have hE_top : E = ⊤ := by
      by_contra hne
      refine hsf.2 E hne ⟨4, 1, fun k => ⟨im ^ (k : ℕ) * α, mul_mem (pow_mem himE _) hαE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc :
          (f.map (@algebraMap ℚ E _ _ E.algebra')).map (algebraMap E L) = f.map (algebraMap ℚ L) := by
        rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
      rw [hmc, hfac im α him_prim hα_ev]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have aut_ext : ∀ g₁ g₂ : L ≃ₐ[ℚ] L, g₁ im = g₂ im → g₁ α = g₂ α → g₁ = g₂ := by
    intro g₁ g₂ h1 h2
    let Eeq : IntermediateField ℚ L :=
      { (AlgHom.equalizer g₁.toAlgHom g₂.toAlgHom) with
        inv_mem' := fun {a} ha => by
          change g₁ a⁻¹ = g₂ a⁻¹; rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv ha }
    have hQim_le : ℚ⟮im⟯ ≤ Eeq := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact h1
    let Eeq' : IntermediateField ℚ⟮im⟯ L :=
      { Eeq.toSubfield with algebraMap_mem' := fun x => hQim_le x.2 }
    have htop' : (⊤ : IntermediateField ℚ⟮im⟯ L) ≤ Eeq' := by
      rw [← hL_over_im, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact h2
    ext x; exact htop' IntermediateField.mem_top
  obtain ⟨Φ, hΦ_im, hΦ_α⟩ :
      ∃ Φ : DihedralGroup 4 ≃* (L ≃ₐ[ℚ] L),
        (∀ g : DihedralGroup 4, Φ g im = match g with | .r _ => im | .sr _ => -im) ∧
        (∀ g : DihedralGroup 4, Φ g α = match g with
          | .r k => im ^ k.val * α
          | .sr k => (-im) ^ k.val * α) := by
    obtain ⟨ρ, hρ_im, hρ_α⟩ : ∃ ρ : L ≃ₐ[ℚ] L, ρ im = im ∧ ρ α = im * α := by
      let pb : PowerBasis ℚ⟮im⟯ (ℚ⟮im⟯)⟮α⟯ :=
        IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral α)
      have hgen : algebraMap (ℚ⟮im⟯)⟮α⟯ L pb.gen = α :=
        congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
      have hroot : Polynomial.aeval (im * α) (minpoly ℚ⟮im⟯ pb.gen) = 0 := by
        have hmin_eq : minpoly ℚ⟮im⟯ pb.gen = minpoly ℚ⟮im⟯ α := by
          rw [← minpoly.algebraMap_eq (algebraMap (ℚ⟮im⟯)⟮α⟯ L).injective, hgen]
        have hcomp : (algebraMap ℚ⟮im⟯ L).comp (algebraMap ℚ ℚ⟮im⟯) = algebraMap ℚ L :=
          Subsingleton.elim _ _
        have hα_ev' : Polynomial.aeval α (f.map (algebraMap ℚ ℚ⟮im⟯)) = 0 := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
          exact hα_ev
        have hm : minpoly ℚ⟮im⟯ α = f.map (algebraMap ℚ ℚ⟮im⟯) :=
          (minpoly.eq_of_irreducible_of_monic hf_im_irr hα_ev' (hmonic.map _)).symm
        rw [hmin_eq, hm, Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def,
          map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat, mul_pow,
          him_prim.pow_eq_one, one_mul, hα4, sub_self]
      let toL : (ℚ⟮im⟯)⟮α⟯ ≃ₐ[ℚ⟮im⟯] L :=
        (IntermediateField.equivOfEq hL_over_im).trans IntermediateField.topEquiv
      let hom : L →ₐ[ℚ⟮im⟯] L := (pb.lift (im * α) hroot).comp toL.symm.toAlgHom
      let eqv : L ≃ₐ[ℚ⟮im⟯] L := AlgEquiv.ofBijective hom
        ⟨hom.toRingHom.injective,
          LinearMap.surjective_of_injective (f := hom.toLinearMap) hom.toRingHom.injective⟩
      refine ⟨eqv.restrictScalars ℚ,
        eqv.commutes ⟨im, IntermediateField.mem_adjoin_simple_self ℚ im⟩, ?_⟩
      change (pb.lift (im * α) hroot) (toL.symm α) = im * α
      have hs : toL.symm α = ⟨α, IntermediateField.mem_adjoin_simple_self ℚ⟮im⟯ α⟩ := by
        apply toL.injective; simp [toL]
      have hg : pb.gen = ⟨α, IntermediateField.mem_adjoin_simple_self ℚ⟮im⟯ α⟩ :=
        IntermediateField.adjoin.powerBasis_gen _
      rw [hs, ← hg, PowerBasis.lift_gen]
    obtain ⟨σ, hσ_im, hσ_α⟩ : ∃ σ : L ≃ₐ[ℚ] L, σ im = -im ∧ σ α = α := by
      let pb : PowerBasis ℚ⟮α⟯ (ℚ⟮α⟯)⟮im⟯ :=
        IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral im)
      have hgen : algebraMap (ℚ⟮α⟯)⟮im⟯ L pb.gen = im :=
        congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
      have hmin_im : minpoly ℚ⟮α⟯ im = Polynomial.X ^ 2 + 1 := by
        have him_int : IsIntegral ℚ⟮α⟯ im := Algebra.IsIntegral.isIntegral im
        have hdvd : minpoly ℚ⟮α⟯ im ∣ (Polynomial.X ^ 2 + 1 : ℚ⟮α⟯[X]) := by
          refine minpoly.dvd ℚ⟮α⟯ im ?_
          simp [him_sq]
        have hdeg2 : (minpoly ℚ⟮α⟯ im).natDegree = 2 := by
          rw [← IntermediateField.adjoin.finrank him_int]
          have ht : ((ℚ⟮α⟯)⟮im⟯ : IntermediateField ℚ⟮α⟯ L) = ⊤ := hL_over_α
          rw [ht, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfin_αL]
        have hmon2 : (Polynomial.X ^ 2 + 1 : ℚ⟮α⟯[X]).Monic := by
          simpa using Polynomial.monic_X_pow_add_C (1 : ℚ⟮α⟯) (by decide)
        exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic him_int) hmon2 hdvd
          (by
            have hd : (Polynomial.X ^ 2 + 1 : ℚ⟮α⟯[X]).natDegree = 2 := by
              simp
            omega)).symm
      have hroot : Polynomial.aeval (-im) (minpoly ℚ⟮α⟯ pb.gen) = 0 := by
        have hmin_eq : minpoly ℚ⟮α⟯ pb.gen = minpoly ℚ⟮α⟯ im := by
          rw [← minpoly.algebraMap_eq (algebraMap (ℚ⟮α⟯)⟮im⟯ L).injective, hgen]
        rw [hmin_eq, hmin_im]
        simp [him_sq]
      let toL : (ℚ⟮α⟯)⟮im⟯ ≃ₐ[ℚ⟮α⟯] L :=
        (IntermediateField.equivOfEq hL_over_α).trans IntermediateField.topEquiv
      let hom : L →ₐ[ℚ⟮α⟯] L := (pb.lift (-im) hroot).comp toL.symm.toAlgHom
      let eqv : L ≃ₐ[ℚ⟮α⟯] L := AlgEquiv.ofBijective hom
        ⟨hom.toRingHom.injective,
          LinearMap.surjective_of_injective (f := hom.toLinearMap) hom.toRingHom.injective⟩
      refine ⟨eqv.restrictScalars ℚ, ?_,
        eqv.commutes ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩⟩
      change (pb.lift (-im) hroot) (toL.symm im) = -im
      have hs : toL.symm im = ⟨im, IntermediateField.mem_adjoin_simple_self ℚ⟮α⟯ im⟩ := by
        apply toL.injective; simp [toL]
      have hg : pb.gen = ⟨im, IntermediateField.mem_adjoin_simple_self ℚ⟮α⟯ im⟩ :=
        IntermediateField.adjoin.powerBasis_gen _
      rw [hs, ← hg, PowerBasis.lift_gen]
    have hρ_pow_im : ∀ k : ℕ, (ρ ^ k) im = im := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hρ_im]
    have hρ_pow_α : ∀ k : ℕ, (ρ ^ k) α = im ^ k * α := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρ_im, hρ_α, ← mul_assoc, ← pow_succ]
    let ΦFun : DihedralGroup 4 → (L ≃ₐ[ℚ] L)
      | .r k => ρ ^ k.val
      | .sr k => σ * ρ ^ k.val
    have hΦFun_im : ∀ g : DihedralGroup 4,
        ΦFun g im = match g with | .r _ => im | .sr _ => -im := by
      rintro (k | k)
      · exact hρ_pow_im k.val
      · simp [ΦFun, AlgEquiv.mul_apply, hρ_pow_im, hσ_im]
    have hΦFun_α : ∀ g : DihedralGroup 4,
        ΦFun g α = match g with
          | .r k => im ^ k.val * α
          | .sr k => (-im) ^ k.val * α := by
      rintro (k | k)
      · exact hρ_pow_α k.val
      · simp [ΦFun, AlgEquiv.mul_apply, hρ_pow_α, map_mul, map_pow, hσ_im, hσ_α]
    have hneg_im3 : -im = im ^ 3 := by
      calc -im = (-1) * im := by ring
        _ = im ^ 2 * im := by rw [← him_sq]
        _ = im ^ 3 := by ring
    have hΦ_mul : ∀ g₁ g₂ : DihedralGroup 4, ΦFun (g₁ * g₂) = ΦFun g₁ * ΦFun g₂ := by
      intro g₁ g₂
      refine aut_ext _ _ ?_ ?_
      · rcases g₁ with a | a <;> rcases g₂ with b | b <;>
          simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
            DihedralGroup.sr_mul_sr, AlgEquiv.mul_apply, hΦFun_im]
      · rcases g₁ with a | a <;> rcases g₂ with b | b
        · rw [DihedralGroup.r_mul_r, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            hΦFun_im, hΦFun_α, ← mul_assoc]
          congr 1
          rw [← pow_add, isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · rw [DihedralGroup.r_mul_sr, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            map_neg, hΦFun_im, hΦFun_α, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · rw [DihedralGroup.sr_mul_r, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            hΦFun_im, hΦFun_α, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · rw [DihedralGroup.sr_mul_sr, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            map_neg, hΦFun_im, neg_neg, hΦFun_α, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
    let ΦHom : DihedralGroup 4 →* (L ≃ₐ[ℚ] L) :=
      { toFun := ΦFun
        map_one' := aut_ext _ _ (by simp [ΦFun]) (by simp [ΦFun])
        map_mul' := hΦ_mul }
    have hΦ_inj : Function.Injective ΦHom := by
      intro g₁ g₂ heq
      have h1 : ΦFun g₁ im = ΦFun g₂ im := congrArg (fun g : L ≃ₐ[ℚ] L => g im) heq
      have h2 : ΦFun g₁ α = ΦFun g₂ α := congrArg (fun g : L ≃ₐ[ℚ] L => g α) heq
      have him_ne_neg : im ≠ -im := fun h => him_ne (by linear_combination h / 2)
      rcases g₁ with a | a <;> rcases g₂ with b | b
      · rw [hΦFun_α, hΦFun_α] at h2
        have hp := mul_right_cancel₀ hα_ne h2
        have hv : a.val = b.val := him_prim.pow_inj a.val_lt b.val_lt hp
        exact congrArg DihedralGroup.r (ZMod.val_injective 4 hv)
      · rw [hΦFun_im, hΦFun_im] at h1
        exact (him_ne_neg h1).elim
      · rw [hΦFun_im, hΦFun_im] at h1
        exact (him_ne_neg h1.symm).elim
      · rw [hΦFun_α, hΦFun_α] at h2
        have hp := mul_right_cancel₀ hα_ne h2
        have hneg_prim : IsPrimitiveRoot (-im) 4 := by
          rw [hneg_im3]
          exact him_prim.pow_of_coprime 3 (by decide)
        have hv : a.val = b.val := hneg_prim.pow_inj a.val_lt b.val_lt hp
        exact congrArg DihedralGroup.sr (ZMod.val_injective 4 hv)
    let _ : Fintype (L ≃ₐ[ℚ] L) := Fintype.ofFinite _
    have hΦ_bij : Function.Bijective ΦHom := by
      refine (Fintype.bijective_iff_injective_and_card ΦHom).mpr ⟨hΦ_inj, ?_⟩
      rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcardG]
    exact ⟨MulEquiv.ofBijective ΦHom hΦ_bij, hΦFun_im, hΦFun_α⟩
  obtain ⟨hd4_card, hd4_bij, hd4_norm⟩ := d4Subgroup_classification
  let Hsub : Fin 10 → Subgroup (L ≃ₐ[ℚ] L) := fun k => (d4Subgroup k).map Φ.toMonoidHom
  have hHsub_card : ∀ k : Fin 10,
      Nat.card (Hsub k) = (![8, 4, 4, 4, 2, 2, 2, 2, 2, 1] : Fin 10 → ℕ) k := by
    intro k
    rw [← hd4_card k]
    exact Nat.card_congr (Φ.subgroupMap (d4Subgroup k)).toEquiv.symm
  have hfixed_finrank : ∀ k : Fin 10,
      Module.finrank ℚ (IntermediateField.fixedField (Hsub k)) =
        (![1, 2, 2, 2, 4, 4, 4, 4, 4, 8] : Fin 10 → ℕ) k := by
    intro k
    have hmul := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Hsub k)) L
    rw [IntermediateField.finrank_fixedField_eq_card, hHsub_card k, hfinL] at hmul
    fin_cases k <;> simp at hmul ⊢ <;> omega
  have gt_one_of_moved : ∀ (x : L) (g : L ≃ₐ[ℚ] L), g x ≠ x → 1 < Module.finrank ℚ ℚ⟮x⟯ := by
    intro x g hgx
    have hpos : 0 < Module.finrank ℚ ℚ⟮x⟯ := Module.finrank_pos
    by_contra hle
    have h1 : Module.finrank ℚ ℚ⟮x⟯ = 1 := by omega
    have hbot : (⊥ : IntermediateField ℚ L) = ℚ⟮x⟯ :=
      IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, h1])
    have hx_bot : x ∈ (⊥ : IntermediateField ℚ L) :=
      hbot ▸ IntermediateField.mem_adjoin_simple_self ℚ x
    rw [IntermediateField.mem_bot] at hx_bot
    rcases hx_bot with ⟨q, rfl⟩
    exact hgx (g.commutes q)
  have d4_r2_mem_of_card_ge_four : ∀ D : Subgroup (DihedralGroup 4),
      4 ≤ Nat.card D → DihedralGroup.r 2 ∈ D := by
    intro D hD4
    obtain ⟨k, rfl⟩ := hd4_bij.2 D
    rw [hd4_card k] at hD4
    rw [mem_d4Subgroup_iff]
    fin_cases k <;> simp at hD4 <;> decide
  have finrank_four_of_le_and_r2_moves :
      ∀ (x : L) (k : Fin 10),
        (![1, 2, 2, 2, 4, 4, 4, 4, 4, 8] : Fin 10 → ℕ) k = 4 →
        ℚ⟮x⟯ ≤ IntermediateField.fixedField (Hsub k) →
        Φ (.r 2) x ≠ x →
        ℚ⟮x⟯ = IntermediateField.fixedField (Hsub k) := by
    intro x k hk4 hle hmove
    have hfin_fk : Module.finrank ℚ (IntermediateField.fixedField (Hsub k)) = 4 := by
      rw [hfixed_finrank k, hk4]
    refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
    have hdvd4 : Module.finrank ℚ ℚ⟮x⟯ ∣ 4 := by
      let sub : IntermediateField ℚ⟮x⟯ L :=
        { (IntermediateField.fixedField (Hsub k)).toSubfield with
          algebraMap_mem' := fun y => hle y.2 }
      have hm2 := Module.finrank_mul_finrank ℚ ℚ⟮x⟯ sub
      have hsub_eq : Module.finrank ℚ sub = 4 := hfin_fk
      exact ⟨Module.finrank ℚ⟮x⟯ sub, hsub_eq.symm.trans hm2.symm⟩
    by_contra hne4
    rw [hfin_fk] at hne4
    have h12 : Module.finrank ℚ ℚ⟮x⟯ = 1 ∨ Module.finrank ℚ ℚ⟮x⟯ = 2 := by
      have hle4 : Module.finrank ℚ ℚ⟮x⟯ ≤ 4 := Nat.le_of_dvd (by decide) hdvd4
      have hpos : 0 < Module.finrank ℚ ℚ⟮x⟯ := Module.finrank_pos
      rcases hdvd4 with ⟨c, hc⟩
      interval_cases hfx : Module.finrank ℚ ℚ⟮x⟯
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
      · exact absurd rfl hne4
    have hcard_fix : 4 ≤ Nat.card (IntermediateField.fixingSubgroup ℚ⟮x⟯) := by
      rw [IsGalois.card_fixingSubgroup_eq_finrank]
      have hm := Module.finrank_mul_finrank ℚ ℚ⟮x⟯ L
      rw [hfinL] at hm
      rcases h12 with h1 | h2
      · rw [h1] at hm; omega
      · rw [h2] at hm; omega
    let D : Subgroup (DihedralGroup 4) :=
      (IntermediateField.fixingSubgroup ℚ⟮x⟯).map Φ.symm.toMonoidHom
    have hD_card : Nat.card D = Nat.card (IntermediateField.fixingSubgroup ℚ⟮x⟯) :=
      Nat.card_congr (Φ.symm.subgroupMap (IntermediateField.fixingSubgroup ℚ⟮x⟯)).toEquiv.symm
    have hr2D : DihedralGroup.r 2 ∈ D := d4_r2_mem_of_card_ge_four D (hD_card ▸ hcard_fix)
    rcases hr2D with ⟨g, hg, hΦg⟩
    have hg_eq : g = Φ (.r 2) := by rw [← hΦg, Φ.apply_symm_apply]
    rw [hg_eq] at hg
    exact hmove (hg ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩)
  have h_r1_im : Φ (.r 1) im = im := hΦ_im (.r 1)
  have h_r1_α : Φ (.r 1) α = im * α := by
    rw [hΦ_α (.r 1), ZMod.val_one, pow_one]
  have h_r2_im : Φ (.r 2) im = im := hΦ_im (.r 2)
  have h_r2_α : Φ (.r 2) α = -α := by
    have h := hΦ_α (.r 2)
    have hv2 : (2 : ZMod 4).val = 2 := rfl
    rw [hv2, him_sq] at h
    linear_combination h
  have h_sr0_im : Φ (.sr 0) im = -im := hΦ_im (.sr 0)
  have h_sr0_α : Φ (.sr 0) α = α := by
    rw [hΦ_α (.sr 0), ZMod.val_zero, pow_zero, one_mul]
  have h_sr1_im : Φ (.sr 1) im = -im := hΦ_im (.sr 1)
  have h_sr1_α : Φ (.sr 1) α = -im * α := by
    rw [hΦ_α (.sr 1), ZMod.val_one, pow_one]
  have h_sr2_im : Φ (.sr 2) im = -im := hΦ_im (.sr 2)
  have h_sr2_α : Φ (.sr 2) α = -α := by
    have h := hΦ_α (.sr 2)
    have hv2 : (2 : ZMod 4).val = 2 := rfl
    have hn : (-im) ^ 2 = -1 := by linear_combination him_sq
    rw [hv2, hn] at h
    linear_combination h
  have h_sr3_im : Φ (.sr 3) im = -im := hΦ_im (.sr 3)
  have h_sr3_α : Φ (.sr 3) α = im * α := by
    have h := hΦ_α (.sr 3)
    have hv3 : (3 : ZMod 4).val = 3 := rfl
    have hn : (-im) ^ 3 = im := by
      calc (-im) ^ 3 = -im * im ^ 2 := by ring
        _ = -im * (-1) := by rw [him_sq]
        _ = im := by ring
    rw [hv3, hn] at h
    exact h
  have h_r0_eq1 : Φ (.r 0) = 1 := Φ.map_one
  have hex_eq_fixed : ∀ k : Fin 10,
      ex163Field α im k = IntermediateField.fixedField (Hsub k) := by
    have hk0 : ex163Field α im 0 = IntermediateField.fixedField (Hsub 0) := by
      change (⊥ : IntermediateField ℚ L) = IntermediateField.fixedField (Hsub 0)
      exact IntermediateField.eq_of_le_of_finrank_eq bot_le
        (by rw [IntermediateField.finrank_bot, hfixed_finrank 0]; rfl)
    have hk1 : ex163Field α im 1 = IntermediateField.fixedField (Hsub 1) := by
      change ℚ⟮im⟯ = IntermediateField.fixedField (Hsub 1)
      have hle : ℚ⟮im⟯ ≤ IntermediateField.fixedField (Hsub 1) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        rcases g with a | a
        · exact hΦ_im (.r a)
        · exact absurd hg (by fin_cases a <;> decide)
      exact IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hdeg_im, hfixed_finrank 1]; rfl)
    have hk2 : ex163Field α im 2 = IntermediateField.fixedField (Hsub 2) := by
      change ℚ⟮α ^ 2⟯ = IntermediateField.fixedField (Hsub 2)
      have hle : ℚ⟮α ^ 2⟯ ≤ IntermediateField.fixedField (Hsub 2) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .r 2 ∨ g = .sr 0 ∨ g = .sr 2 := by
          rcases g with a | a <;> fin_cases a <;> first
            | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
            | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))
            | exact absurd hg (by decide)
        rcases hc with rfl | rfl | rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · rw [map_pow, h_r2_α]; ring
        · rw [map_pow, h_sr0_α]
        · rw [map_pow, h_sr2_α]; ring
      have hgt1 : 1 < Module.finrank ℚ ℚ⟮α ^ 2⟯ := by
        refine gt_one_of_moved (α ^ 2) (Φ (.r 1)) ?_
        rw [map_pow, h_r1_α]
        intro heq
        have h1 : (im ^ 2 - 1) * α ^ 2 = 0 := by linear_combination heq
        rw [him_sq] at h1
        exact hα2_ne (by linear_combination -h1 / 2)
      refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
      have hfk : Module.finrank ℚ (IntermediateField.fixedField (Hsub 2)) = 2 := hfixed_finrank 2
      let sub : IntermediateField ℚ⟮α ^ 2⟯ L :=
        { (IntermediateField.fixedField (Hsub 2)).toSubfield with
          algebraMap_mem' := fun y => hle y.2 }
      have hm := Module.finrank_mul_finrank ℚ ℚ⟮α ^ 2⟯ sub
      have hsub_eq : Module.finrank ℚ sub = 2 := hfk
      rw [hsub_eq] at hm
      have hle2 : Module.finrank ℚ ℚ⟮α ^ 2⟯ ≤ 2 :=
        Nat.le_of_dvd (by decide) ⟨Module.finrank ℚ⟮α ^ 2⟯ sub, hm.symm⟩
      rw [hfk]; omega
    have hk3 : ex163Field α im 3 = IntermediateField.fixedField (Hsub 3) := by
      change ℚ⟮im * α ^ 2⟯ = IntermediateField.fixedField (Hsub 3)
      have hle : ℚ⟮im * α ^ 2⟯ ≤ IntermediateField.fixedField (Hsub 3) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .r 2 ∨ g = .sr 1 ∨ g = .sr 3 := by
          rcases g with a | a <;> fin_cases a <;> first
            | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
            | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))
            | exact absurd hg (by decide)
        rcases hc with rfl | rfl | rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · rw [map_mul, map_pow, h_r2_im, h_r2_α]; ring
        · rw [map_mul, map_pow, h_sr1_im, h_sr1_α]
          calc -im * (-im * α) ^ 2 = -im * im ^ 2 * α ^ 2 := by ring
            _ = -im * (-1) * α ^ 2 := by rw [him_sq]
            _ = im * α ^ 2 := by ring
        · rw [map_mul, map_pow, h_sr3_im, h_sr3_α]
          calc -im * (im * α) ^ 2 = -im * im ^ 2 * α ^ 2 := by ring
            _ = -im * (-1) * α ^ 2 := by rw [him_sq]
            _ = im * α ^ 2 := by ring
      have hgt1 : 1 < Module.finrank ℚ ℚ⟮im * α ^ 2⟯ := by
        refine gt_one_of_moved (im * α ^ 2) (Φ (.sr 0)) ?_
        rw [map_mul, map_pow, h_sr0_im, h_sr0_α]
        intro heq
        have h1 : im * α ^ 2 = 0 := by linear_combination -heq / 2
        exact mul_ne_zero him_ne hα2_ne h1
      refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
      have hfk : Module.finrank ℚ (IntermediateField.fixedField (Hsub 3)) = 2 := hfixed_finrank 3
      let sub : IntermediateField ℚ⟮im * α ^ 2⟯ L :=
        { (IntermediateField.fixedField (Hsub 3)).toSubfield with
          algebraMap_mem' := fun y => hle y.2 }
      have hm := Module.finrank_mul_finrank ℚ ℚ⟮im * α ^ 2⟯ sub
      have hsub_eq : Module.finrank ℚ sub = 2 := hfk
      rw [hsub_eq] at hm
      have hle2 : Module.finrank ℚ ℚ⟮im * α ^ 2⟯ ≤ 2 :=
        Nat.le_of_dvd (by decide) ⟨Module.finrank ℚ⟮im * α ^ 2⟯ sub, hm.symm⟩
      rw [hfk]; omega
    have hk4 : ex163Field α im 4 = IntermediateField.fixedField (Hsub 4) := by
      let F4 := IntermediateField.adjoin ℚ ({im, α ^ 2} : Set L)
      change F4 = IntermediateField.fixedField (Hsub 4)
      have hle : F4 ≤ IntermediateField.fixedField (Hsub 4) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro x (rfl | rfl) <;> rw [IntermediateField.mem_fixedField_iff] <;>
          rintro _ ⟨g, hg, rfl⟩ <;> rw [mem_d4Subgroup_iff] at hg
        · have hc : g = .r 0 ∨ g = .r 2 := by
            rcases g with a | a <;> fin_cases a <;>
              first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
          rcases hc with rfl | rfl
          · rw [h_r0_eq1, AlgEquiv.one_apply]
          · exact h_r2_im
        · have hc : g = .r 0 ∨ g = .r 2 := by
            rcases g with a | a <;> fin_cases a <;>
              first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
          rcases hc with rfl | rfl
          · rw [h_r0_eq1, AlgEquiv.one_apply]
          · rw [map_pow, h_r2_α]; ring
      refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
      have hfk : Module.finrank ℚ (IntermediateField.fixedField (Hsub 4)) = 4 := hfixed_finrank 4
      have hQim_le : ℚ⟮im⟯ ≤ F4 := IntermediateField.adjoin_le_adjoin (by simp)
      have hnot_mem : α ^ 2 ∉ ℚ⟮im⟯ := by
        intro hmem
        have hmem1 : α ^ 2 ∈ IntermediateField.fixedField (Hsub 1) := by
          change ex163Field α im 1 = _ at hk1
          rwa [← hk1]
        have hfix : Φ (.r 1) (α ^ 2) = α ^ 2 :=
          hmem1 ⟨Φ (.r 1), ⟨.r 1, by rw [mem_d4Subgroup_iff]; decide, rfl⟩⟩
        rw [map_pow, h_r1_α] at hfix
        have h1 : (im ^ 2 - 1) * α ^ 2 = 0 := by linear_combination hfix
        rw [him_sq] at h1
        exact hα2_ne (by linear_combination -h1 / 2)
      let F4_over_im : IntermediateField ℚ⟮im⟯ L :=
        { F4.toSubfield with algebraMap_mem' := fun x => hQim_le x.2 }
      let fk_over_F4 : IntermediateField F4 L :=
        { (IntermediateField.fixedField (Hsub 4)).toSubfield with
          algebraMap_mem' := fun x => hle x.2 }
      have hm1 := Module.finrank_mul_finrank ℚ ℚ⟮im⟯ F4_over_im
      have hF4_eq : Module.finrank ℚ F4_over_im = Module.finrank ℚ F4 := rfl
      rw [hdeg_im, hF4_eq] at hm1
      have hm2 := Module.finrank_mul_finrank ℚ F4 fk_over_F4
      have hfk_eq : Module.finrank ℚ fk_over_F4 = 4 := hfk
      rw [hfk_eq] at hm2
      have hgt2 : 1 < Module.finrank ℚ⟮im⟯ F4_over_im := by
        have hpos : 0 < Module.finrank ℚ⟮im⟯ F4_over_im := Module.finrank_pos
        by_contra hle1
        have h1 : Module.finrank ℚ⟮im⟯ F4_over_im = 1 := by omega
        have hbot : (⊥ : IntermediateField ℚ⟮im⟯ L) = F4_over_im :=
          IntermediateField.eq_of_le_of_finrank_eq bot_le
            (by rw [IntermediateField.finrank_bot, h1])
        have hmem_F4 : α ^ 2 ∈ F4_over_im :=
          IntermediateField.subset_adjoin ℚ ({im, α ^ 2} : Set L) (by simp)
        rw [← hbot, IntermediateField.mem_bot] at hmem_F4
        rcases hmem_F4 with ⟨y, hy⟩
        exact hnot_mem (hy ▸ y.2)
      have hle4 : Module.finrank ℚ F4 ≤ 4 :=
        Nat.le_of_dvd (by decide) ⟨Module.finrank F4 fk_over_F4, hm2.symm⟩
      rw [hfk]; omega
    have hk5 : ex163Field α im 5 = IntermediateField.fixedField (Hsub 5) := by
      refine finrank_four_of_le_and_r2_moves α 5 rfl ?_ ?_
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .sr 0 := by
          rcases g with a | a <;> fin_cases a <;>
            first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
        rcases hc with rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · exact h_sr0_α
      · rw [h_r2_α]; exact fun h => hα_ne (by linear_combination -h / 2)
    have hk6 : ex163Field α im 6 = IntermediateField.fixedField (Hsub 6) := by
      refine finrank_four_of_le_and_r2_moves (im * α) 6 rfl ?_ ?_
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .sr 2 := by
          rcases g with a | a <;> fin_cases a <;>
            first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
        rcases hc with rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · rw [map_mul, h_sr2_im, h_sr2_α]; ring
      · rw [map_mul, h_r2_im, h_r2_α]
        exact fun h => mul_ne_zero him_ne hα_ne (by linear_combination -h / 2)
    have hk7 : ex163Field α im 7 = IntermediateField.fixedField (Hsub 7) := by
      refine finrank_four_of_le_and_r2_moves ((1 + im) * α) 7 rfl ?_ ?_
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .sr 3 := by
          rcases g with a | a <;> fin_cases a <;>
            first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
        rcases hc with rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · rw [map_mul, map_add, map_one, h_sr3_im, h_sr3_α]
          calc (1 + -im) * (im * α) = (im - im ^ 2) * α := by ring
            _ = (im - (-1)) * α := by rw [him_sq]
            _ = (1 + im) * α := by ring
      · rw [map_mul, map_add, map_one, h_r2_im, h_r2_α]
        have h1im_ne : 1 + im ≠ 0 := by
          intro h0
          have hm1 : im = -1 := by linear_combination h0
          rw [hm1] at him_sq; norm_num at him_sq
        exact fun h => mul_ne_zero h1im_ne hα_ne (by linear_combination -h / 2)
    have hk8 : ex163Field α im 8 = IntermediateField.fixedField (Hsub 8) := by
      refine finrank_four_of_le_and_r2_moves ((1 - im) * α) 8 rfl ?_ ?_
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        rw [mem_d4Subgroup_iff] at hg
        have hc : g = .r 0 ∨ g = .sr 1 := by
          rcases g with a | a <;> fin_cases a <;>
            first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hg (by decide)
        rcases hc with rfl | rfl
        · rw [h_r0_eq1, AlgEquiv.one_apply]
        · rw [map_mul, map_sub, map_one, h_sr1_im, h_sr1_α]
          calc (1 - -im) * (-im * α) = (-im - im ^ 2) * α := by ring
            _ = (-im - (-1)) * α := by rw [him_sq]
            _ = (1 - im) * α := by ring
      · rw [map_mul, map_sub, map_one, h_r2_im, h_r2_α]
        have h1mim_ne : 1 - im ≠ 0 := by
          intro h0
          have hp1 : im = 1 := by linear_combination -h0
          rw [hp1] at him_sq; norm_num at him_sq
        exact fun h => mul_ne_zero h1mim_ne hα_ne (by linear_combination -h / 2)
    have hk9 : ex163Field α im 9 = IntermediateField.fixedField (Hsub 9) := by
      have hbotH : Hsub 9 = ⊥ := by
        ext g
        simp only [Hsub, Subgroup.mem_map, Subgroup.mem_bot, mem_d4Subgroup_iff]
        constructor
        · rintro ⟨d, hd, rfl⟩
          have hd0 : d = .r 0 := by
            rcases d with a | a <;> fin_cases a <;>
              first | rfl | exact absurd hd (by decide)
          rw [hd0]; exact Φ.map_one
        · rintro rfl
          exact ⟨1, by decide, Φ.map_one⟩
      change (⊤ : IntermediateField ℚ L) = IntermediateField.fixedField (Hsub 9)
      rw [hbotH, IntermediateField.fixedField_bot]
    intro k
    fin_cases k
    · exact hk0
    · exact hk1
    · exact hk2
    · exact hk3
    · exact hk4
    · exact hk5
    · exact hk6
    · exact hk7
    · exact hk8
    · exact hk9
  have hex_bij : Function.Bijective (ex163Field α im) := by
    have hinj_ex : Function.Injective (ex163Field α im) := by
      intro k₁ k₂ hk
      rw [hex_eq_fixed k₁, hex_eq_fixed k₂] at hk
      have hfix_eq := congrArg IntermediateField.fixingSubgroup hk
      rw [IntermediateField.fixingSubgroup_fixedField,
        IntermediateField.fixingSubgroup_fixedField] at hfix_eq
      have hd_eq : d4Subgroup k₁ = d4Subgroup k₂ := by
        ext d
        have hm := Subgroup.ext_iff.mp hfix_eq (Φ d)
        simpa [Hsub, Φ.injective.eq_iff] using hm
      exact hd4_bij.1 hd_eq
    have hsurj_ex : Function.Surjective (ex163Field α im) := by
      intro M
      let H := IntermediateField.fixingSubgroup M
      let D := H.comap Φ.toMonoidHom
      obtain ⟨k, hk⟩ := hd4_bij.2 D
      refine ⟨k, ?_⟩
      rw [hex_eq_fixed k]
      have hH_eq : Hsub k = H := by
        ext g
        simp only [Hsub, hk, Subgroup.mem_map, Subgroup.mem_comap]
        exact ⟨fun ⟨d, hd, hgd⟩ => hgd ▸ hd, fun hg => ⟨Φ.symm g, by simpa using hg, Φ.apply_symm_apply g⟩⟩
      rw [hH_eq, IsGalois.fixedField_fixingSubgroup]
    exact ⟨hinj_ex, hsurj_ex⟩
  have hex_finrank : ∀ k : Fin 10,
      Module.finrank ℚ (ex163Field α im k) =
        (![1, 2, 2, 2, 4, 4, 4, 4, 4, 8] : Fin 10 → ℕ) k := by
    intro k
    rw [hex_eq_fixed k, hfixed_finrank k]
  have hex_normal : ∀ k : Fin 10,
      IsGarlingNormal ℚ (ex163Field α im k) ↔ k ∈ ({0, 1, 2, 3, 4, 9} : Set (Fin 10)) := by
    intro k
    rw [isGarlingNormal_iff, ← hd4_norm k, hex_eq_fixed k]
    have hnorm_iff : Normal ℚ (IntermediateField.fixedField (Hsub k)) ↔ (Hsub k).Normal := by
      constructor
      · intro hN
        have hfix := IntermediateField.fixingSubgroup_fixedField (Hsub k)
        rw [← hfix]
        haveI : Normal ℚ (IntermediateField.fixedField (Hsub k)) := hN
        haveI : IsGalois ℚ (IntermediateField.fixedField (Hsub k)) :=
          { to_isSeparable := inferInstance, to_normal := hN }
        exact IsGalois.fixingSubgroup_normal_of_isGalois (IntermediateField.fixedField (Hsub k))
      · intro hHN
        haveI : (Hsub k).Normal := hHN
        exact (IsGalois.of_fixedField_normal_subgroup (Hsub k)).to_normal
    rw [hnorm_iff]
    constructor
    · intro hN
      refine ⟨fun d hd g => ?_⟩
      have hc := hN.conj_mem (Φ d) ⟨d, hd, rfl⟩ (Φ g)
      rw [← map_inv, ← map_mul, ← map_mul] at hc
      rcases hc with ⟨d', hd', heq⟩
      rwa [Φ.injective heq] at hd'
    · intro hN
      refine ⟨fun x hx y => ?_⟩
      rcases hx with ⟨d, hd, rfl⟩
      refine ⟨Φ.symm y * d * (Φ.symm y)⁻¹, hN.conj_mem d hd (Φ.symm y), ?_⟩
      simp [map_mul, map_inv]
  exact ⟨hfinL, hextL, hcardG, ⟨Φ.symm⟩, α, im, hα4, him_sq, hex_bij, hex_finrank, hex_normal⟩

/-! ## §16.2 Abel's theorem (printed pp. 124–125, PDF pp. 132–133) -/

/-- **Sentence 1 of `Theorem 16.2 (Abel's theorem)` — unconditional for all `θ ∈ K` (including `θ = 0`)**
(§16.2, printed p. 124 / PDF p. 132; proof p. 125):
*"Suppose that `q` is a prime, that `x^q - θ ∈ K[x]` and that `char K ≠ q`. Then either `x^q - θ`
is irreducible over `K` or `x^q - θ` has a root in `K`."* -/
theorem theorem_16_2_part1_unconditional {K : Type u} [Field K] {q : ℕ} (hq : Nat.Prime q)
    (θ : K) (hchar : ringChar K ≠ q) :
    Xor' (Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
      (∃ r : K, (Polynomial.X ^ q - Polynomial.C θ).eval r = 0) := by
  let f : K[X] := Polynomial.X ^ q - Polynomial.C θ
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C θ hq.ne_zero
  have hf_deg : f.natDegree = q := Polynomial.natDegree_X_pow_sub_C
  -- Mutual exclusivity: since q ≥ 2, if f has a root r ∈ K then (X - C r) ∣ f with deg 1 < q
  have hnot_both : ¬ (Irreducible f ∧ ∃ r : K, f.eval r = 0) := by
    rintro ⟨hirr, r, hr⟩
    obtain ⟨h, hh⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    have hdeg_f := congrArg Polynomial.natDegree hh
    have hh0 : h ≠ 0 := fun h0 => by rw [h0, mul_zero] at hh; exact hf_monic.ne_zero hh
    rw [hf_deg, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hh0,
      Polynomial.natDegree_X_sub_C] at hdeg_f
    rcases hirr.isUnit_or_isUnit hh with hu1 | hu2
    · rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero r),
        Polynomial.natDegree_X_sub_C] at hu1
      exact absurd hu1 (by decide)
    · rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hh0] at hu2
      have hhq : h.natDegree = 0 := Nat.cast_injective hu2
      have := hq.two_le
      omega
  by_cases hirr : Irreducible f
  · exact Or.inl ⟨hirr, fun hroot => hnot_both ⟨hirr, hroot⟩⟩
  · refine Or.inr ⟨?_, hirr⟩
    by_cases hθ : θ = 0
    · refine ⟨0, ?_⟩
      simp [f, hθ, zero_pow hq.ne_zero]
    · -- Garling's Bézout proof on printed p. 125: let g be a monic irreducible factor of f in K[X] of degree d < q
      have hndvd_char : ¬ (ringChar K ∣ q) := by
        intro hd
        rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp0
        · exact hchar ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
        · rw [hp0] at hd
          exact hq.ne_zero (zero_dvd_iff.mp hd)
      have hf_not_unit : ¬ IsUnit f := by
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hf_monic.ne_zero,
          hf_deg]
        exact Nat.cast_ne_zero.mpr hq.ne_zero
      obtain ⟨p_fac, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hf_not_unit hf_monic.ne_zero
      let g : K[X] := p_fac * Polynomial.C p_fac.leadingCoeff⁻¹
      have hlc_ne : p_fac.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_irr.ne_zero
      have hg_monic : g.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          mul_inv_cancel₀ hlc_ne]
      have hg_irr : Irreducible g :=
        Associated.irreducible ⟨Units.mk0 (Polynomial.C p_fac.leadingCoeff⁻¹)
          (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc_ne))
          (Polynomial.C p_fac.leadingCoeff)
          (by simp [← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne])
          (by simp [← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne]), rfl⟩ hp_irr
      have hg_dvd : g ∣ f := by
        rcases hp_dvd with ⟨c, hc⟩
        exact ⟨Polynomial.C p_fac.leadingCoeff * c, by
          simp only [g]
          rw [mul_assoc, Polynomial.C_mul_C, inv_mul_cancel₀ hlc_ne, Polynomial.C_1, one_mul, ← hc]⟩
      let d := g.natDegree
      have hd_pos : 1 ≤ d := Polynomial.Irreducible.natDegree_pos hg_irr
      have hd_le : d ≤ q := hf_deg ▸ Polynomial.natDegree_le_of_dvd hg_dvd hf_monic.ne_zero
      have hd_lt : d < q := by
        rcases eq_or_lt_of_le hd_le with hd_eq | hlt
        · exfalso
          have heq : f = g :=
            Polynomial.eq_of_monic_of_dvd_of_natDegree_le hg_monic hf_monic hg_dvd
              (by rw [hf_deg, hd_eq])
          exact hirr (heq ▸ hg_irr)
        · exact hlt
      -- Take a splitting field L : K of f (`Theorem 7.3`)
      obtain ⟨L, _, _, hsfL, _⟩ := theorem_7_3_natDegree f
      obtain ⟨_, _, ⟨ω, hω⟩, ⟨γ, hγ⟩, hfacL⟩ :=
        section_16_1_root_factorization hθ hndvd_char hsfL
      have hγ_pow : γ ^ q = algebraMap K L θ := by
        have h1 := hγ
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h1
        exact h1
      -- In L[X], g.map ∣ ∏ k : Fin q, (X - C (ω ^ k * γ)), so (g.eval 0)^q = ((-1)^d * θ)^d ⇒ g₀^q = θ^d
      let gL : L[X] := g.map (algebraMap K L)
      have hgL_monic : gL.Monic := hg_monic.map _
      have hgL_deg : gL.natDegree = d :=
        Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective g
      have hgL_dvd : gL ∣ ∏ k : Fin q, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ) * γ)) := by
        rw [← hfacL ω γ hω hγ]
        exact Polynomial.map_dvd (algebraMap K L) hg_dvd
      -- Every root of gL in L satisfies x^q = θ, and gL splits into linear factors over L!
      have hgL_splits : gL.Splits :=
        Polynomial.Splits.of_dvd
          ((garlingSplitsOver_iff_splits K L f).mp hsfL.1)
          (Polynomial.map_ne_zero hf_monic.ne_zero)
          (Polynomial.map_dvd (algebraMap K L) hg_dvd)
      -- Product of multiset of roots of monic gL: gL = (gL.roots.map (X - C ·)).prod!
      have hgL_prod : gL = (gL.roots.map fun r => Polynomial.X - Polynomial.C r).prod := by
        have hs := Polynomial.eq_prod_roots_of_monic_of_splits_id hgL_monic hgL_splits
        exact hs
      have hroots_pow : ∀ x ∈ gL.roots, x ^ q = algebraMap K L θ := by
        intro x hx
        have hmem_f : x ∈ (f.map (algebraMap K L)).roots :=
          (Polynomial.roots.le_of_dvd (Polynomial.map_ne_zero hf_monic.ne_zero)
            (Polynomial.map_dvd (algebraMap K L) hg_dvd)) hx
        rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero),
          Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hmem_f
        exact hmem_f
      -- Evaluate gL at 0: gL.eval 0 = (-1)^d * gL.roots.prod!
      let g₀ : K := (-1) ^ d * g.eval 0
      have hg₀_L : algebraMap K L g₀ = gL.roots.prod := by
        have hev0 : gL.eval 0 = ((-1 : L) ^ d) * gL.roots.prod := by
          have hcard_r : gL.roots.card = d := by
            rw [← Polynomial.Splits.natDegree_eq_card_roots hgL_splits, hgL_deg]
          conv_lhs => rw [hgL_prod]
          rw [Polynomial.eval_multiset_prod, Multiset.map_map]
          have hfn : ((Polynomial.eval (0 : L)) ∘ fun r : L => Polynomial.X - Polynomial.C r) =
              fun r : L => (-1 : L) * r := by
            ext r; simp
          rw [hfn, Multiset.prod_map_mul, Multiset.map_const, Multiset.prod_replicate,
            Multiset.map_id', hcard_r]
        calc algebraMap K L g₀
            = (-1 : L) ^ d * gL.eval 0 := by
              simp [g₀, gL, Polynomial.eval_map, Polynomial.eval₂_at_zero]
          _ = (-1 : L) ^ d * ((-1 : L) ^ d * gL.roots.prod) := by rw [hev0]
          _ = ((-1 : L) ^ 2) ^ d * gL.roots.prod := by ring
          _ = gL.roots.prod := by norm_num
      have hg₀_pow_L : algebraMap K L (g₀ ^ q) = algebraMap K L (θ ^ d) := by
        rw [map_pow, hg₀_L]
        have hmult_pow : ∀ m : Multiset L,
            (∀ x ∈ m, x ^ q = algebraMap K L θ) → m.prod ^ q = (algebraMap K L θ) ^ m.card := by
          intro m
          induction m using Multiset.induction_on with
          | empty => intro _; simp
          | cons a s ih =>
            intro hall
            rw [Multiset.prod_cons, mul_pow, hall a (Multiset.mem_cons_self a s),
              ih (fun x hx => hall x (Multiset.mem_cons_of_mem hx)),
              Multiset.card_cons, pow_succ']
        rw [hmult_pow gL.roots hroots_pow,
          ← Polynomial.Splits.natDegree_eq_card_roots hgL_splits, hgL_deg, map_pow]
      have hg₀_pow : g₀ ^ q = θ ^ d := (algebraMap K L).injective hg₀_pow_L
      have hg₀_ne : g₀ ≠ 0 := by
        intro h0
        rw [h0, zero_pow hq.ne_zero] at hg₀_pow
        exact pow_ne_zero d hθ hg₀_pow.symm
      -- Bézout identity: gcd(d, q) = 1 ⇒ d * a + q * b = 1 in ℤ
      have hcop : Nat.Coprime d q :=
        (Nat.coprime_of_lt_prime (by omega) hd_lt hq)
      let a : ℤ := Nat.gcdA d q
      let b : ℤ := Nat.gcdB d q
      have hbez : (d : ℤ) * a + (q : ℤ) * b = 1 := by
        have h1 := Nat.gcd_eq_gcd_ab d q
        rw [hcop.gcd_eq_one] at h1
        simpa [a, b] using h1.symm
      let rootK : K := g₀ ^ a * θ ^ b
      refine ⟨rootK, ?_⟩
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero]
      calc rootK ^ q
          = (g₀ ^ a) ^ (q : ℤ) * (θ ^ b) ^ (q : ℤ) := by
            simp [rootK, mul_pow]
        _ = (g₀ ^ (q : ℤ)) ^ a * θ ^ ((q : ℤ) * b) := by
            rw [← zpow_mul, mul_comm a (q : ℤ), zpow_mul, ← zpow_mul, mul_comm b (q : ℤ)]
        _ = (θ ^ (d : ℤ)) ^ a * θ ^ ((q : ℤ) * b) := by
            have hgqZ : g₀ ^ (q : ℤ) = θ ^ (d : ℤ) := by simpa using hg₀_pow
            rw [hgqZ]
        _ = θ ^ ((d : ℤ) * a + (q : ℤ) * b) := by
            rw [← zpow_mul, ← zpow_add₀ hθ]
        _ = θ := by rw [hbez, zpow_one]

/-- **Counterexample to literal Sentence 2 of `Theorem 16.2` at `θ = 0`** (`QUEUE.md` fidelity hold,
Flag 1(b)):
At `K = ℚ`, `q = 3`, `θ = 0`, `3` is prime, `char ℚ = 0 ≠ 3`, `x³ - 0 = x³` has the root `0 ∈ ℚ`
(*"the latter case"*) and **splits over `ℚ`** (`x³ = (x - 0)³`), yet `ℚ` contains **no** primitive
`3`rd root of unity. -/
theorem theorem_16_2_zero_counterexample :
    Nat.Prime 3 ∧
    ringChar ℚ ≠ 3 ∧
    (Polynomial.X ^ 3 - Polynomial.C (0 : ℚ)).eval 0 = 0 ∧
    GarlingSplitsOver ℚ ℚ (Polynomial.X ^ 3 - Polynomial.C (0 : ℚ)) ∧
    ¬ ∃ ω : ℚ, IsPrimitiveRoot ω 3 := by
  refine ⟨by decide, by rw [ringChar.eq_zero]; decide, by simp, ?_,
    theorem_16_1_zero_counterexample.2.2⟩
  refine ⟨3, 1, fun _ => 0, ?_⟩
  simp [GarlingSplitsExplicit]

/-- **Theorem 16.2 (Abel's theorem)** (§16.2, printed p. 124 / PDF p. 132; proof pp. 124–125;
`θ ≠ 0` guard made explicit for Sentence 2 per `QUEUE.md` Flag 1(b)):
*"Suppose that `q` is a prime, that `x^q - θ ∈ K[x]` and that `char K ≠ q` [with `θ ≠ 0`]. Then
either `x^q - θ` is irreducible over `K` or `x^q - θ` has a root in `K`. In the latter case `x^q - θ`
splits over `K` if and only if `K` contains a primitive `q`th root of unity."* -/
theorem theorem_16_2 {K : Type u} [Field K] {q : ℕ} (hq : Nat.Prime q)
    {θ : K} (hθ : θ ≠ 0) (hchar : ringChar K ≠ q) :
    Xor' (Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
      (∃ r : K, (Polynomial.X ^ q - Polynomial.C θ).eval r = 0) ∧
    ((∃ r : K, (Polynomial.X ^ q - Polynomial.C θ).eval r = 0) →
      (GarlingSplitsOver K K (Polynomial.X ^ q - Polynomial.C θ) ↔
        ∃ ω : K, IsPrimitiveRoot ω q)) := by
  have hpart1 := theorem_16_2_part1_unconditional hq θ hchar
  have hndvd_char : ¬ (ringChar K ∣ q) := by
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp0
    · exact hchar ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
    · rw [hp0] at hd
      exact hq.ne_zero (zero_dvd_iff.mp hd)
  refine ⟨hpart1, fun ⟨r, hr⟩ => ?_⟩
  have hr_pow : r ^ q = θ := by
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hr
    exact hr
  constructor
  · intro hsplit
    have hsfK : IsGarlingSplittingFieldExtension K K (Polynomial.X ^ q - Polynomial.C θ) :=
      ⟨hsplit, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
    exact (theorem_16_1 hθ hndvd_char hsfK).2.1
  · rintro ⟨ω, hω⟩
    refine ⟨q, 1, fun k => ω ^ (k : ℕ) * r, ?_⟩
    rw [GarlingSplitsExplicit, Polynomial.map_id, map_one, Polynomial.C_1, one_mul, ← hr_pow]
    exact X_pow_sub_C_pow_eq_prod hq.one_le hω r

/-- Exact unconditional Sentence-2 characterization across **all** `θ ∈ K` (including `θ = 0`):
when `x^q - θ` has a root in `K`, `x^q - θ` splits over `K` iff `θ = 0 ∨ ∃ ω : K, IsPrimitiveRoot ω q`. -/
theorem theorem_16_2_iff {K : Type u} [Field K] {q : ℕ} (hq : Nat.Prime q)
    (θ : K) (hchar : ringChar K ≠ q)
    (hroot : ∃ r : K, (Polynomial.X ^ q - Polynomial.C θ).eval r = 0) :
    GarlingSplitsOver K K (Polynomial.X ^ q - Polynomial.C θ) ↔
      θ = 0 ∨ ∃ ω : K, IsPrimitiveRoot ω q := by
  by_cases hθ : θ = 0
  · subst hθ
    simp only [true_or, iff_true]
    refine ⟨q, 1, fun _ => 0, ?_⟩
    simp [GarlingSplitsExplicit]
  · simp only [hθ, false_or]
    exact (theorem_16_2 hq hθ hchar).2 hroot

/-- **Exercise 16.4 — Repaired Theorem** (§16.2, printed p. 125 / PDF p. 133; `QUEUE.md` fidelity hold,
Flag 2):
For prime `q`, `char K ≠ q`, irreducible `x^q - θ ∈ K[x]`, splitting field `L : K`, primitive `q`th
root of unity `ω ∈ L`, and `j = [K(ω) : K]`:
`j ∣ (q - 1)`, `|Γ_K(x^q - θ)| = q * j`, and `Γ_K(x^q - θ)` is generated by `σ, τ` satisfying
`σ^q = τ^j = 1` (`orderOf σ = q`, `orderOf τ = j`) and `σ^k * τ = τ * σ`, where `k̄ ∈ ℤ_q*`
(`(ZMod q)ˣ`) has **exact multiplicative order `j`** (equivalently `k̄ = ḡ^((q - 1) / j)` for a
generator `ḡ` of `(ZMod q)ˣ`).

*(OCR warning verified against 220 DPI scan PDF p. 133: `garling1986_pages.txt` ll. 4669–4670
corrupts `σ^q = τ^j = 1, σ^k τ = τσ` and `ℤ_q*` to `~ =Tj = 1, rikT =Tri,` and `z:`.)* -/
theorem exercise_16_4_repaired {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {q : ℕ} (hq : Nat.Prime q) (hchar : ringChar K ≠ q) {θ : K}
    (hirr : Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ))
    {ω : L} (hω : IsPrimitiveRoot ω q) {j : ℕ}
    (hj : Module.finrank K K⟮ω⟯ = j) :
    haveI : Fact q.Prime := ⟨hq⟩
    1 ≤ j ∧
    j ∣ (q - 1) ∧
    Nat.card (GarlingPolyGaloisGroup K L (Polynomial.X ^ q - Polynomial.C θ)) = q * j ∧
    ∃ (σ τ : GarlingPolyGaloisGroup K L (Polynomial.X ^ q - Polynomial.C θ))
      (u : (ZMod q)ˣ),
      orderOf u = j ∧
      (∃ g : (ZMod q)ˣ, Subgroup.zpowers g = ⊤ ∧ u = g ^ ((q - 1) / j)) ∧
      Subgroup.closure ({σ, τ} : Set (GarlingPolyGaloisGroup K L _)) = ⊤ ∧
      orderOf σ = q ∧
      orderOf τ = j ∧
      σ ^ q = 1 ∧
      τ ^ j = 1 ∧
      σ ^ ((u : ZMod q).val) * τ = τ * σ := by
  letI : Fact q.Prime := ⟨hq⟩
  let f : K[X] := Polynomial.X ^ q - Polynomial.C θ
  have hθ : θ ≠ 0 := by
    intro h0
    subst h0
    have h0_root : f.eval 0 = 0 := by simp [f, zero_pow hq.ne_zero]
    exact (theorem_16_2_part1_unconditional hq 0 hchar).elim
      (fun h => h.2 ⟨0, h0_root⟩) (fun h => h.2 hirr)
  have hndvd_char : ¬ (ringChar K ∣ q) := by
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp0
    · exact hchar ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
    · rw [hp0] at hd; exact hq.ne_zero (zero_dvd_iff.mp hd)
  obtain ⟨_, hmonic, _, _, hgsep⟩ := X_pow_sub_C_separable_of_ne_zero hθ hndvd_char
  obtain ⟨_, _, _, ⟨β, hβ⟩, hfac⟩ := section_16_1_root_factorization hθ hndvd_char hsf
  have hβ_pow : β ^ q = algebraMap K L θ := by
    have h1 := hβ
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h1
    exact h1
  have hβ_ne : β ≠ 0 := by
    intro h0; rw [h0, zero_pow hq.ne_zero] at hβ_pow
    exact hθ ((algebraMap K L).injective (hβ_pow.symm.trans (map_zero _).symm))
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_splittingField hmonic.ne_zero hsf hgsep
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have _ : FiniteDimensional K K⟮ω⟯ := Module.Finite.left K K⟮ω⟯ L
  have hj_pos : 1 ≤ j := hj ▸ Module.finrank_pos
  -- K⟮ω⟯ / K is Galois (stable under Gal(L/K) since every g(ω) is a qth root of unity, hence a power of ω)
  have hfix_normal : (IntermediateField.fixingSubgroup K⟮ω⟯).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
    -- Suffices to show (g * n * g⁻¹) fixes ω, hence fixes all of K⟮ω⟯!
    have hpow_ginv : (g⁻¹ ω) ^ q = 1 := by
      rw [← map_pow, hω.pow_eq_one, map_one]
    obtain ⟨m, _, hm⟩ := hω.eq_pow_of_pow_eq_one hpow_ginv
    have hginv_mem : g⁻¹ ω ∈ K⟮ω⟯ := by
      rw [hm]; exact pow_mem (IntermediateField.mem_adjoin_simple_self K ω) m
    have hfix_ω : (g * n * g⁻¹) ω = ω := by
      simp only [AlgEquiv.mul_apply]
      rw [hn (g⁻¹ ω) hginv_mem]
      exact g.apply_symm_apply ω
    let Eeq : IntermediateField K L :=
      { (AlgHom.equalizer (g * n * g⁻¹).toAlgHom (1 : L ≃ₐ[K] L).toAlgHom) with
        inv_mem' := fun {a} ha => by
          change (g * n * g⁻¹) a⁻¹ = a⁻¹
          rw [map_inv₀]; exact congrArg Inv.inv ha }
    have hle : K⟮ω⟯ ≤ Eeq := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact hfix_ω
    intro x hx
    exact hle hx
  have _ : Normal K K⟮ω⟯ := by
    have heq_f := IsGalois.fixedField_fixingSubgroup (K := K⟮ω⟯)
    rw [← heq_f]
    exact IsGalois.normal_of_normal_subgroup (IntermediateField.fixingSubgroup K⟮ω⟯)
  have _ : Algebra.IsSeparable K K⟮ω⟯ := Algebra.IsSeparable.tower_bot K K⟮ω⟯ L
  have _ : IsGalois K K⟮ω⟯ := { to_isSeparable := inferInstance, to_normal := inferInstance }
  -- Embed Gal(K⟮ω⟯ / K) injectively into (ZMod q)ˣ
  let ωK : K⟮ω⟯ := ⟨ω, IntermediateField.mem_adjoin_simple_self K ω⟩
  have hωK : IsPrimitiveRoot ωK q := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨by ext; exact hω.pow_eq_one, fun l hl => ?_⟩
    exact hω.dvd_of_pow_eq_one l (congrArg Subtype.val hl)
  have h_aut_pow : ∀ ψ : K⟮ω⟯ ≃ₐ[K] K⟮ω⟯,
      ∃ u : (ZMod q)ˣ, ψ ωK = ωK ^ (u : ZMod q).val := by
    intro ψ
    have hψq : (ψ ωK) ^ q = 1 := by rw [← map_pow, hωK.pow_eq_one, map_one]
    have hψ_prim : IsPrimitiveRoot (ψ ωK) q := by
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨hψq, fun l hl => ?_⟩
      have h1 : ωK ^ l = 1 := ψ.injective (by rw [map_pow, hl, map_one])
      exact hωK.dvd_of_pow_eq_one l h1
    obtain ⟨m, hm_lt, hm_eq⟩ := hωK.eq_pow_of_pow_eq_one hψq
    have hcop : Nat.Coprime m q :=
      (hωK.pow_iff_coprime hq.pos m).mp (hm_eq ▸ hψ_prim)
    let u : (ZMod q)ˣ := ZMod.unitOfCoprime m hcop
    refine ⟨u, ?_⟩
    have hu_val : (u : ZMod q).val = m := by
      change (m : ZMod q).val = m
      exact ZMod.val_natCast_of_lt hm_lt
    rw [hu_val, hm_eq]
  let toUnitsFun : (K⟮ω⟯ ≃ₐ[K] K⟮ω⟯) → (ZMod q)ˣ := fun ψ => (h_aut_pow ψ).choose
  have htoUnits_spec : ∀ ψ : K⟮ω⟯ ≃ₐ[K] K⟮ω⟯,
      ψ ωK = ωK ^ (toUnitsFun ψ : ZMod q).val := fun ψ => (h_aut_pow ψ).choose_spec
  let toUnitsHom : (K⟮ω⟯ ≃ₐ[K] K⟮ω⟯) →* (ZMod q)ˣ :=
    { toFun := toUnitsFun
      map_one' := by
        have h1 := htoUnits_spec 1
        simp only [AlgEquiv.one_apply] at h1
        have hm : (toUnitsFun 1 : ZMod q).val ≡ 1 [MOD q] :=
          (isPrimitiveRoot_pow_eq_pow_iff_modEq hωK).mp (h1.symm.trans (pow_one ωK))
        ext
        rw [← ZMod.natCast_zmod_val (toUnitsFun 1 : ZMod q), Units.val_one,
          ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hm
      map_mul' := fun ψ₁ ψ₂ => by
        have h12 := htoUnits_spec (ψ₁ * ψ₂)
        have hcalc : (ψ₁ * ψ₂) ωK =
            ωK ^ ((toUnitsFun ψ₁ : ZMod q).val * (toUnitsFun ψ₂ : ZMod q).val) := by
          rw [AlgEquiv.mul_apply, htoUnits_spec ψ₂, map_pow, htoUnits_spec ψ₁, ← pow_mul]
        have hm : (toUnitsFun (ψ₁ * ψ₂) : ZMod q).val ≡
            (toUnitsFun ψ₁ : ZMod q).val * (toUnitsFun ψ₂ : ZMod q).val [MOD q] :=
          (isPrimitiveRoot_pow_eq_pow_iff_modEq hωK).mp (h12.symm.trans hcalc)
        ext
        rw [Units.val_mul, ← ZMod.natCast_zmod_val (toUnitsFun (ψ₁ * ψ₂) : ZMod q),
          ← ZMod.natCast_zmod_val (toUnitsFun ψ₁ : ZMod q),
          ← ZMod.natCast_zmod_val (toUnitsFun ψ₂ : ZMod q),
          ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
        exact hm }
  have htoUnits_inj : Function.Injective toUnitsHom := by
    intro ψ₁ ψ₂ heq
    have hω_eq : ψ₁ ωK = ψ₂ ωK := by
      rw [htoUnits_spec ψ₁, htoUnits_spec ψ₂, heq]
    let Eeq : IntermediateField K L :=
      { carrier := {x : L | ∃ hx : x ∈ K⟮ω⟯, ψ₁ ⟨x, hx⟩ = ψ₂ ⟨x, hx⟩}
        add_mem' := by
          rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
          exact ⟨add_mem ha hb, by change ψ₁ (⟨a, ha⟩ + ⟨b, hb⟩) = _; rw [map_add, map_add, ea, eb]⟩
        zero_mem' := ⟨zero_mem _, by change ψ₁ 0 = ψ₂ 0; simp⟩
        neg_mem' := by
          rintro a ⟨ha, ea⟩
          exact ⟨neg_mem ha, by change ψ₁ (-⟨a, ha⟩) = _; rw [map_neg, map_neg, ea]⟩
        mul_mem' := by
          rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
          exact ⟨mul_mem ha hb, by change ψ₁ (⟨a, ha⟩ * ⟨b, hb⟩) = _; rw [map_mul, map_mul, ea, eb]⟩
        one_mem' := ⟨one_mem _, by change ψ₁ 1 = ψ₂ 1; simp⟩
        inv_mem' := by
          rintro a ⟨ha, ea⟩
          exact ⟨inv_mem ha, by change ψ₁ (⟨a, ha⟩)⁻¹ = _; rw [map_inv₀, map_inv₀, ea]⟩
        algebraMap_mem' := fun c => ⟨K⟮ω⟯.algebraMap_mem c, by
          change ψ₁ (algebraMap K K⟮ω⟯ c) = ψ₂ (algebraMap K K⟮ω⟯ c)
          rw [ψ₁.commutes, ψ₂.commutes]⟩ }
    have hle : K⟮ω⟯ ≤ Eeq := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨IntermediateField.mem_adjoin_simple_self K ω, hω_eq⟩
    ext x
    obtain ⟨_, hx⟩ := hle x.2
    exact congrArg Subtype.val hx
  -- Order of Gal(K⟮ω⟯ / K) is j, which divides |(ZMod q)ˣ| = q - 1!
  have hcard_aut_Kω : Nat.card (K⟮ω⟯ ≃ₐ[K] K⟮ω⟯) = j := by
    rw [IsGalois.card_aut_eq_finrank K K⟮ω⟯, hj]
  have hcard_units : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
  have hj_dvd : j ∣ (q - 1) := by
    let imgSub : Subgroup (ZMod q)ˣ := toUnitsHom.range
    have heq_c : Nat.card imgSub = j := by
      have e : (K⟮ω⟯ ≃ₐ[K] K⟮ω⟯) ≃* imgSub :=
        MulEquiv.ofBijective toUnitsHom.rangeRestrict
          ⟨fun a b hab => htoUnits_inj (congrArg Subtype.val hab),
           toUnitsHom.rangeRestrict_surjective⟩
      rw [← hcard_aut_Kω]
      exact Nat.card_congr e.toEquiv.symm
    have hd := Subgroup.card_subgroup_dvd_card imgSub
    rwa [heq_c, hcard_units] at hd
  -- (ZMod q)ˣ is cyclic of order q - 1 (`Theorem 12.3`), so g^((q-1)/j) generates the unique subgroup of order j!
  obtain ⟨_, ⟨gTop, _, hord_gTop⟩⟩ := theorem_12_3 (ZMod q) (⊤ : Subgroup (ZMod q)ˣ)
  let g : (ZMod q)ˣ := gTop.1
  have hg_ord : orderOf g = q - 1 := by
    rw [← Subgroup.orderOf_mk]
    rw [Nat.card_congr (Subgroup.topEquiv.toEquiv), hcard_units] at hord_gTop
    exact hord_gTop
  have hg_gen : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hg_ord, hcard_units]
  -- Pick generator ψ₀ of Gal(K⟮ω⟯ / K) such that toUnitsHom ψ₀ = g ^ ((q - 1) / j)!
  -- Note: toUnitsHom.range has order j inside cyclic group ⟨g⟩ of order q - 1, hence contains g ^ ((q - 1) / j)!
  let m_exp : ℕ := (q - 1) / j
  have hm_mul : m_exp * j = q - 1 := Nat.div_mul_cancel hj_dvd
  let u : (ZMod q)ˣ := g ^ m_exp
  have hu_ord : orderOf u = j := by
    rw [orderOf_pow' g (by
      intro h0
      have hq1_pos : 0 < q - 1 := by have := hq.two_le; omega
      rw [h0, zero_mul] at hm_mul; omega)]
    rw [hg_ord, Nat.gcd_eq_right (⟨j, hm_mul.symm⟩ : m_exp ∣ q - 1)]
    exact Nat.div_div_self hj_dvd (by have := hq.two_le; omega)
  have hu_in_range : u ∈ toUnitsHom.range := by
    -- In cyclic group ⟨g⟩ of order q - 1, every subgroup H of order j satisfies ∀ x ∈ H, x ^ j = 1, hence x = g^(k * m_exp) ∈ ⟨u⟩!
    let H := toUnitsHom.range
    have hH_card : Nat.card H = j := by
      have e : (K⟮ω⟯ ≃ₐ[K] K⟮ω⟯) ≃* H :=
        MulEquiv.ofBijective toUnitsHom.rangeRestrict
          ⟨fun a b hab => htoUnits_inj (congrArg Subtype.val hab),
           toUnitsHom.rangeRestrict_surjective⟩
      rw [← hcard_aut_Kω]
      exact Nat.card_congr e.toEquiv.symm
    have hH_le_u : H ≤ Subgroup.zpowers u := by
      intro x hx
      have hxj : (⟨x, hx⟩ : H) ^ j = 1 := by
        let _ : Fintype H := Fintype.ofFinite H
        rw [← hH_card, Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      have hxj_val : x ^ j = 1 := congrArg Subtype.val hxj
      have hx_top : x ∈ Subgroup.zpowers g := hg_gen.symm ▸ Subgroup.mem_top x
      rw [Subgroup.mem_zpowers_iff] at hx_top ⊢
      rcases hx_top with ⟨z, rfl⟩
      -- (g ^ z) ^ j = 1 ⇒ (q - 1) ∣ z * j ⇒ m_exp ∣ z!
      have hpow1 : g ^ (z * (j : ℤ)) = 1 := by rw [zpow_mul]; exact hxj_val
      have hdvdZ : ((orderOf g : ℕ) : ℤ) ∣ z * (j : ℤ) :=
        orderOf_dvd_iff_zpow_eq_one.mpr hpow1
      rw [hg_ord, ← hm_mul, Nat.cast_mul] at hdvdZ
      have hjZ_ne : (j : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm_dvd_z : (m_exp : ℤ) ∣ z := mul_dvd_mul_iff_right hjZ_ne |>.mp hdvdZ
      rcases hm_dvd_z with ⟨t, rfl⟩
      exact ⟨t, by simp [u, zpow_mul]⟩
    have h_eq_sub : H = Subgroup.zpowers u := by
      let _ : Fintype (ZMod q)ˣ := Fintype.ofFinite _
      apply Subgroup.eq_of_le_of_card_ge hH_le_u
      rw [hH_card, Nat.card_zpowers, hu_ord]
    rw [h_eq_sub]
    exact Subgroup.mem_zpowers u
  obtain ⟨ψ₀, hψ₀_u⟩ := hu_in_range
  have hψ₀_ord : orderOf ψ₀ = j := by
    rw [← orderOf_injective toUnitsHom htoUnits_inj ψ₀, hψ₀_u, hu_ord]
  -- Degree of L / K is q * j since gcd(q, j) = 1
  have hdeg_Kβ : Module.finrank K K⟮β⟯ = q := by
    have hm : minpoly K β = f :=
      (minpoly.eq_of_irreducible_of_monic hirr hβ hmonic).symm
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β), hm,
      Polynomial.natDegree_X_pow_sub_C]
  have hdvd_q : q ∣ Module.finrank K L :=
    hdeg_Kβ ▸ ⟨Module.finrank K⟮β⟯ L, (Module.finrank_mul_finrank K K⟮β⟯ L).symm⟩
  have hdvd_j : j ∣ Module.finrank K L :=
    hj ▸ ⟨Module.finrank K⟮ω⟯ L, (Module.finrank_mul_finrank K K⟮ω⟯ L).symm⟩
  have hcop_qj : Nat.Coprime q j := by
    have hle_j : j ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hj_dvd
    have hlt_j : j < q := by have := hq.two_le; omega
    exact (hq.coprime_iff_not_dvd).mpr fun hd =>
      not_lt_of_ge (Nat.le_of_dvd hj_pos hd) hlt_j
  have hdvd_qj : q * j ∣ Module.finrank K L :=
    hcop_qj.mul_dvd_of_dvd_of_dvd hdvd_q hdvd_j
  obtain ⟨_, _, h161⟩ := theorem_16_1 hθ hndvd_char hsf
  obtain ⟨_, _, hcard_dvd_q, hfin_eq_card, _, hirr_Kω, _⟩ := h161 ω hω
  have hle_q : Module.finrank K⟮ω⟯ L ≤ q :=
    hfin_eq_card ▸ Nat.le_of_dvd hq.pos hcard_dvd_q
  have hle_qj : Module.finrank K L ≤ q * j := by
    rw [← Module.finrank_mul_finrank K K⟮ω⟯ L, hj]; nlinarith
  have hfinL : Module.finrank K L = q * j :=
    Nat.le_antisymm hle_qj (Nat.le_of_dvd Module.finrank_pos hdvd_qj)
  have hfin_KωL : Module.finrank K⟮ω⟯ L = q := by
    have hm := Module.finrank_mul_finrank K K⟮ω⟯ L
    rw [hj, hfinL] at hm; nlinarith
  have hfin_KβL : Module.finrank K⟮β⟯ L = j := by
    have hm := Module.finrank_mul_finrank K K⟮β⟯ L
    rw [hdeg_Kβ, hfinL] at hm; nlinarith
  have hcardG : Nat.card (GarlingPolyGaloisGroup K L f) = q * j := by
    change Nat.card (L ≃ₐ[K] L) = q * j
    rw [IsGalois.card_aut_eq_finrank K L, hfinL]
  have hf_Kω_irr : Irreducible (f.map (algebraMap K K⟮ω⟯)) := hirr_Kω.mpr hfin_KωL
  have _ : FiniteDimensional K⟮ω⟯ L := Module.Finite.right K K⟮ω⟯ L
  have _ : FiniteDimensional K⟮β⟯ L := Module.Finite.right K K⟮β⟯ L
  have hL_over_Kω : IntermediateField.adjoin K⟮ω⟯ ({β} : Set L) = ⊤ := by
    let E : IntermediateField K L :=
      (IntermediateField.adjoin K⟮ω⟯ ({β} : Set L)).restrictScalars K
    have hωE : ω ∈ E :=
      (IntermediateField.adjoin K⟮ω⟯ ({β} : Set L)).algebraMap_mem
        ⟨ω, IntermediateField.mem_adjoin_simple_self K ω⟩
    have hβE : β ∈ E := IntermediateField.mem_adjoin_simple_self K⟮ω⟯ β
    have hsplitE : GarlingSplitsOver K E f := by
      refine ⟨q, 1, fun k => ⟨ω ^ (k : ℕ) * β, mul_mem (pow_mem hωE _) hβE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc : (f.map (algebraMap K E)).map (algebraMap E L) = f.map (algebraMap K L) := by
        rw [Polynomial.map_map]; rfl
      rw [hmc, hfac ω β hω hβ]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    have hE_top : E = ⊤ := by by_contra hne; exact hsf.2 E hne hsplitE
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have hL_over_Kβ : IntermediateField.adjoin K⟮β⟯ ({ω} : Set L) = ⊤ := by
    let E : IntermediateField K L :=
      (IntermediateField.adjoin K⟮β⟯ ({ω} : Set L)).restrictScalars K
    have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self K⟮β⟯ ω
    have hβE : β ∈ E :=
      (IntermediateField.adjoin K⟮β⟯ ({ω} : Set L)).algebraMap_mem
        ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
    have hsplitE : GarlingSplitsOver K E f := by
      refine ⟨q, 1, fun k => ⟨ω ^ (k : ℕ) * β, mul_mem (pow_mem hωE _) hβE⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap E L) (algebraMap E L).injective
      have hmc : (f.map (algebraMap K E)).map (algebraMap E L) = f.map (algebraMap K L) := by
        rw [Polynomial.map_map]; rfl
      rw [hmc, hfac ω β hω hβ]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun k _ => by simp
    have hE_top : E = ⊤ := by by_contra hne; exact hsf.2 E hne hsplitE
    ext x; change x ∈ E ↔ True; simp [hE_top]
  have aut_ext : ∀ g₁ g₂ : L ≃ₐ[K] L, g₁ ω = g₂ ω → g₁ β = g₂ β → g₁ = g₂ := by
    intro g₁ g₂ h1 h2
    let Eeq : IntermediateField K L :=
      { (AlgHom.equalizer g₁.toAlgHom g₂.toAlgHom) with
        inv_mem' := fun {a} ha => by
          change g₁ a⁻¹ = g₂ a⁻¹; rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv ha }
    have hle : K⟮ω⟯ ≤ Eeq := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact h1
    let Eeq' : IntermediateField K⟮ω⟯ L :=
      { Eeq.toSubfield with algebraMap_mem' := fun x => hle x.2 }
    have htop' : (⊤ : IntermediateField K⟮ω⟯ L) ≤ Eeq' := by
      rw [← hL_over_Kω, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact h2
    ext x; exact htop' IntermediateField.mem_top
  -- Construct σ (fixes ω, sends β ↦ ω * β) and τ (fixes β, sends ω ↦ ω ^ u.val)
  obtain ⟨σ, hσ_ω, hσ_β⟩ : ∃ σ : L ≃ₐ[K] L, σ ω = ω ∧ σ β = ω * β := by
    let pb : PowerBasis K⟮ω⟯ (K⟮ω⟯)⟮β⟯ :=
      IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral β)
    have hgen : (pb.gen : L) = β := by rw [IntermediateField.adjoin.powerBasis_gen]; rfl
    have hroot : Polynomial.aeval (ω * β) (minpoly K⟮ω⟯ pb.gen) = 0 := by
      have hmin_eq : minpoly K⟮ω⟯ pb.gen = minpoly K⟮ω⟯ β := by
        rw [← minpoly.algebraMap_eq (algebraMap (K⟮ω⟯)⟮β⟯ L).injective, hgen]
      have hβ_ev : Polynomial.aeval β (f.map (algebraMap K K⟮ω⟯)) = 0 := by
        rwa [Polynomial.aeval_map_algebraMap]
      have hm : minpoly K⟮ω⟯ β = f.map (algebraMap K K⟮ω⟯) :=
        (minpoly.eq_of_irreducible_of_monic hf_Kω_irr hβ_ev (hmonic.map _)).symm
      rw [hmin_eq, hm, Polynomial.aeval_map_algebraMap, map_sub, map_pow, Polynomial.aeval_X,
        Polynomial.aeval_C, mul_pow, hω.pow_eq_one, one_mul, hβ_pow, sub_self]
    let toL : (K⟮ω⟯)⟮β⟯ ≃ₐ[K⟮ω⟯] L :=
      (IntermediateField.equivOfEq hL_over_Kω).trans IntermediateField.topEquiv
    let hom : L →ₐ[K⟮ω⟯] L := (pb.lift (ω * β) hroot).comp toL.symm.toAlgHom
    let eqv : L ≃ₐ[K⟮ω⟯] L := AlgEquiv.ofBijective hom
      ⟨hom.toRingHom.injective,
        LinearMap.surjective_of_injective (f := hom.toLinearMap) hom.toRingHom.injective⟩
    refine ⟨eqv.restrictScalars K,
      eqv.commutes ⟨ω, IntermediateField.mem_adjoin_simple_self K ω⟩, ?_⟩
    change (pb.lift (ω * β) hroot) (toL.symm β) = ω * β
    have hs : toL.symm β = ⟨β, IntermediateField.mem_adjoin_simple_self K⟮ω⟯ β⟩ := by
      apply toL.injective; simp [toL]
    have hg1 : pb.gen = ⟨β, IntermediateField.mem_adjoin_simple_self K⟮ω⟯ β⟩ :=
      IntermediateField.adjoin.powerBasis_gen _
    rw [hs, ← hg1, PowerBasis.lift_gen]
  let kVal : ℕ := (u : ZMod q).val
  obtain ⟨τ, hτ_ω, hτ_β⟩ : ∃ τ : L ≃ₐ[K] L, τ ω = ω ^ kVal ∧ τ β = β := by
    let pb : PowerBasis K⟮β⟯ (K⟮β⟯)⟮ω⟯ :=
      IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral ω)
    have hgen : (pb.gen : L) = ω := by rw [IntermediateField.adjoin.powerBasis_gen]; rfl
    -- minpoly K⟮β⟯ ω = (minpoly K ω).map since both are monic of degree j!
    have hmin_K_deg : (minpoly K ω).natDegree = j := by
      rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ω), hj]
    have hmin_Kβ_eq : minpoly K⟮β⟯ ω = (minpoly K ω).map (algebraMap K K⟮β⟯) := by
      have hω_int_Kβ : IsIntegral K⟮β⟯ ω := Algebra.IsIntegral.isIntegral ω
      have hdvd : minpoly K⟮β⟯ ω ∣ (minpoly K ω).map (algebraMap K K⟮β⟯) :=
        minpoly.dvd K⟮β⟯ ω (by rw [Polynomial.aeval_map_algebraMap, minpoly.aeval])
      have hdeg_eq : (minpoly K⟮β⟯ ω).natDegree = j := by
        rw [← IntermediateField.adjoin.finrank hω_int_Kβ]
        have ht : ((K⟮β⟯)⟮ω⟯ : IntermediateField K⟮β⟯ L) = ⊤ := hL_over_Kβ
        rw [ht, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfin_KβL]
      exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic hω_int_Kβ)
        ((minpoly.monic (Algebra.IsIntegral.isIntegral ω)).map _)
        hdvd
        (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K K⟮β⟯).injective,
              hmin_K_deg, hdeg_eq])
    -- Since ψ₀ ∈ Gal(K⟮ω⟯ / K) sends ωK ↦ ωK ^ kVal, ω ^ kVal is a root of minpoly K ω!
    have hroot_K : Polynomial.aeval (ω ^ kVal) (minpoly K ω) = 0 := by
      have hspec := htoUnits_spec ψ₀
      have h_eq_u : toUnitsFun ψ₀ = u := hψ₀_u
      rw [h_eq_u] at hspec
      have hval_eq : (ψ₀ ωK : L) = ω ^ kVal := by
        simpa [ωK, kVal] using congrArg Subtype.val hspec
      rw [← hval_eq]
      have haev_Kω : Polynomial.aeval (ψ₀ ωK) (minpoly K ωK) = 0 := by
        rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      have hmin_sub : minpoly K ωK = minpoly K ω :=
        minpoly.algebraMap_eq (algebraMap K⟮ω⟯ L).injective ωK
      rw [← hmin_sub]
      simpa using congrArg (algebraMap K⟮ω⟯ L) haev_Kω
    have hroot : Polynomial.aeval (ω ^ kVal) (minpoly K⟮β⟯ pb.gen) = 0 := by
      have hmin_eq : minpoly K⟮β⟯ pb.gen = minpoly K⟮β⟯ ω := by
        rw [← minpoly.algebraMap_eq (algebraMap (K⟮β⟯)⟮ω⟯ L).injective, hgen]
      rw [hmin_eq, hmin_Kβ_eq, Polynomial.aeval_map_algebraMap, hroot_K]
    let toL : (K⟮β⟯)⟮ω⟯ ≃ₐ[K⟮β⟯] L :=
      (IntermediateField.equivOfEq hL_over_Kβ).trans IntermediateField.topEquiv
    let hom : L →ₐ[K⟮β⟯] L := (pb.lift (ω ^ kVal) hroot).comp toL.symm.toAlgHom
    let eqv : L ≃ₐ[K⟮β⟯] L := AlgEquiv.ofBijective hom
      ⟨hom.toRingHom.injective,
        LinearMap.surjective_of_injective (f := hom.toLinearMap) hom.toRingHom.injective⟩
    refine ⟨eqv.restrictScalars K, ?_,
      eqv.commutes ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩⟩
    change (pb.lift (ω ^ kVal) hroot) (toL.symm ω) = ω ^ kVal
    have hs : toL.symm ω = ⟨ω, IntermediateField.mem_adjoin_simple_self K⟮β⟯ ω⟩ := by
      apply toL.injective; simp [toL]
    have hg1 : pb.gen = ⟨ω, IntermediateField.mem_adjoin_simple_self K⟮β⟯ ω⟩ :=
      IntermediateField.adjoin.powerBasis_gen _
    rw [hs, ← hg1, PowerBasis.lift_gen]
  have hσ_pow_ω : ∀ m : ℕ, (σ ^ m) ω = ω := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσ_ω]
  have hσ_pow_β : ∀ m : ℕ, (σ ^ m) β = ω ^ m * β := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hσ_ω, hσ_β, ← mul_assoc, ← pow_succ]
  have hτ_pow_ω : ∀ m : ℕ, (τ ^ m) ω = ω ^ (kVal ^ m) := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hτ_ω, ← pow_mul, mul_comm, pow_succ']
  have hτ_pow_β : ∀ m : ℕ, (τ ^ m) β = β := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hτ_β]
  have hσq : σ ^ q = 1 :=
    aut_ext _ _ (by rw [hσ_pow_ω]; rfl) (by rw [hσ_pow_β, hω.pow_eq_one, one_mul]; rfl)
  -- Helper: kVal ^ m ≡ ((u ^ m : (ZMod q)ˣ) : ZMod q).val [MOD q]
  have hkVal_pow_mod : ∀ m : ℕ, (kVal ^ m : ZMod q) = ((u ^ m : (ZMod q)ˣ) : ZMod q) := by
    intro m
    rw [Nat.cast_pow, Units.val_pow_eq_pow_val]
    simp [kVal]
  have hτj : τ ^ j = 1 := by
    refine aut_ext _ _ ?_ (by rw [hτ_pow_β]; rfl)
    rw [hτ_pow_ω]
    have hpow_u : u ^ j = 1 := by rw [← hu_ord, pow_orderOf_eq_one]
    have hmod : kVal ^ j ≡ 1 [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff, hkVal_pow_mod j, hpow_u, Units.val_one, Nat.cast_one]
    exact (isPrimitiveRoot_pow_eq_pow_iff_modEq hω).mpr hmod |>.trans (pow_one ω)
  have hord_σ : orderOf σ = q := by
    refine orderOf_eq_prime hσq fun h1 => ?_
    have hb := congrArg (fun g : L ≃ₐ[K] L => g β) h1
    simp only [hσ_β, AlgEquiv.one_apply] at hb
    have hw1 : ω = 1 := mul_right_cancel₀ hβ_ne (hb.trans (one_mul β).symm)
    exact absurd (hω.dvd_of_pow_eq_one 1 (by simpa using hw1)) (by have := hq.two_le; omega)
  have hord_τ : orderOf τ = j := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hτj)
    rw [← hu_ord]
    apply orderOf_dvd_of_pow_eq_one
    have hw := congrArg (fun g : L ≃ₐ[K] L => g ω) (pow_orderOf_eq_one τ)
    simp only [hτ_pow_ω, AlgEquiv.one_apply] at hw
    have hmod : kVal ^ orderOf τ ≡ 1 [MOD q] :=
      (isPrimitiveRoot_pow_eq_pow_iff_modEq hω).mp (hw.trans (pow_one ω).symm)
    have hz : ((u ^ orderOf τ : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [← hkVal_pow_mod, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hmod
    exact Units.ext hz
  have hrel : σ ^ kVal * τ = τ * σ := by
    refine aut_ext _ _ ?_ ?_
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ_ω, hσ_pow_ω, hσ_ω, hτ_ω]
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ_β, hσ_pow_β, hσ_β, map_mul, hτ_ω, hτ_β]
  -- Closure {σ, τ} = ⊤ by counting q * j distinct elements σ^a * τ^b
  have hclosure : Subgroup.closure ({σ, τ} : Set (L ≃ₐ[K] L)) = ⊤ := by
    let H := Subgroup.closure ({σ, τ} : Set (L ≃ₐ[K] L))
    have hσH : σ ∈ H := Subgroup.subset_closure (by simp)
    have hτH : τ ∈ H := Subgroup.subset_closure (by simp)
    let enum_qj : Fin q × Fin j → H := fun ⟨a, b⟩ =>
      ⟨σ ^ (a : ℕ) * τ ^ (b : ℕ), mul_mem (pow_mem hσH _) (pow_mem hτH _)⟩
    have henum_inj : Function.Injective enum_qj := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
      have hg_eq : σ ^ (a₁ : ℕ) * τ ^ (b₁ : ℕ) = σ ^ (a₂ : ℕ) * τ ^ (b₂ : ℕ) :=
        congrArg Subtype.val heq
      have hβ_eq := congrArg (fun g : L ≃ₐ[K] L => g β) hg_eq
      simp only [AlgEquiv.mul_apply, hτ_pow_β, hσ_pow_β] at hβ_eq
      have ha_eq : a₁ = a₂ :=
        Fin.ext (hω.pow_inj a₁.isLt a₂.isLt (mul_right_cancel₀ hβ_ne hβ_eq))
      subst ha_eq
      have hτ_eq : τ ^ (b₁ : ℕ) = τ ^ (b₂ : ℕ) := mul_left_cancel hg_eq
      have hb_mod : (b₁ : ℕ) ≡ (b₂ : ℕ) [MOD j] := by
        rw [← hord_τ, ← pow_eq_pow_iff_modEq]
        exact hτ_eq
      have hb_eq : b₁ = b₂ := by
        apply Fin.ext
        rw [Nat.ModEq, Nat.mod_eq_of_lt b₁.isLt, Nat.mod_eq_of_lt b₂.isLt] at hb_mod
        exact hb_mod
      rw [hb_eq]
    let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
    let _ : Fintype H := Fintype.ofFinite H
    have hH_ge : q * j ≤ Fintype.card H := by
      have hqj_card : Fintype.card (Fin q × Fin j) = q * j := by simp
      rw [← hqj_card]
      exact Fintype.card_le_of_injective enum_qj henum_inj
    have hG_card : Fintype.card (L ≃ₐ[K] L) = q * j := by
      rw [← Nat.card_eq_fintype_card]; exact hcardG
    have hindex1 : H.index = 1 := by
      have hmul := Subgroup.card_mul_index H
      have hH_le : Fintype.card H ≤ q * j := by
        rw [← hG_card]
        exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG_card] at hmul
      have hqj_pos : 0 < q * j := Nat.mul_pos hq.pos hj_pos
      nlinarith
    exact Subgroup.index_eq_one.mp hindex1
  exact ⟨hj_pos, hj_dvd, hcardG, σ, τ, u, hu_ord, ⟨g, hg_gen, rfl⟩,
    hclosure, hord_σ, hord_τ, hσq, hτj, hrel⟩

/-- **Exact Characterization of Literal `Exercise 16.4`** (`QUEUE.md` fidelity hold, Flag 2):
Under the hypotheses of `Exercise 16.4`, the literal printed claim (with `k̄` a **generator** of
`ℤ_q*`, i.e. `Subgroup.zpowers u = ⊤` in `(ZMod q)ˣ`) holds **if and only if `j = q - 1`**! -/
theorem exercise_16_4_printed_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {q : ℕ} (hq : Nat.Prime q) (hchar : ringChar K ≠ q) {θ : K}
    (hirr : Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ))
    {ω : L} (hω : IsPrimitiveRoot ω q) {j : ℕ}
    (hj : Module.finrank K K⟮ω⟯ = j) :
    haveI : Fact q.Prime := ⟨hq⟩
    (∃ (σ τ : GarlingPolyGaloisGroup K L (Polynomial.X ^ q - Polynomial.C θ))
      (u : (ZMod q)ˣ),
      Subgroup.zpowers u = ⊤ ∧
      Subgroup.closure ({σ, τ} : Set (GarlingPolyGaloisGroup K L _)) = ⊤ ∧
      σ ^ q = 1 ∧
      τ ^ j = 1 ∧
      σ ^ ((u : ZMod q).val) * τ = τ * σ) ↔ j = q - 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hj_pos, hj_dvd, hcardG, σ₀, τ₀, u₀, hu₀_ord, ⟨g, hg_gen, hu₀_eq⟩,
    hclosure₀, _, _, hσ₀q, hτ₀j, hrel₀⟩ :=
    exercise_16_4_repaired hq hchar hirr hsf hω hj
  constructor
  · rintro ⟨σ, τ, u, hu_gen, hclosure, hσq, hτj, hrel⟩
    -- Conjugating σ by τ m times: τ^m * σ = σ^(k^m) * τ^m!
    let k := (u : ZMod q).val
    have hconj_m : ∀ m : ℕ, τ ^ m * σ = σ ^ (k ^ m) * τ ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hstep : ∀ n : ℕ, τ * σ ^ n = (σ ^ k) ^ n * τ := by
          intro n
          induction n with
          | zero => simp
          | succ n ihn =>
            calc τ * σ ^ (n + 1) = (τ * σ ^ n) * σ := by rw [pow_succ, mul_assoc]
              _ = (σ ^ k) ^ n * (τ * σ) := by rw [ihn, mul_assoc]
              _ = (σ ^ k) ^ n * (σ ^ k * τ) := by rw [← hrel]
              _ = (σ ^ k) ^ (n + 1) * τ := by rw [← mul_assoc, ← pow_succ]
        calc τ ^ (m + 1) * σ
            = τ * (τ ^ m * σ) := by rw [pow_succ', mul_assoc]
          _ = τ * (σ ^ (k ^ m) * τ ^ m) := by rw [ih]
          _ = (τ * σ ^ (k ^ m)) * τ ^ m := by rw [mul_assoc]
          _ = ((σ ^ k) ^ (k ^ m) * τ) * τ ^ m := by rw [hstep]
          _ = σ ^ (k ^ (m + 1)) * τ ^ (m + 1) := by
              rw [← pow_mul, ← pow_succ', mul_assoc, ← pow_succ']
    -- At m = j, τ^j = 1 gives σ = σ^(k^j)!
    have hσ_pow_kj : σ = σ ^ (k ^ j) := by
      have h := hconj_m j
      rwa [hτj, one_mul, mul_one] at h
    -- Could σ = 1? If σ = 1, Subgroup.closure {1, τ} = Subgroup.zpowers τ has card ≤ j < q * j = |G|!
    have hσ_ne1 : σ ≠ 1 := by
      intro hσ1
      subst hσ1
      have hsub_eq : Subgroup.closure ({(1 : GarlingPolyGaloisGroup K L _), τ} : Set _) =
          Subgroup.zpowers τ := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x (rfl | rfl)
          · exact one_mem _
          · exact Subgroup.mem_zpowers τ
        · rw [Subgroup.zpowers_le]
          exact Subgroup.subset_closure (by simp)
      rw [hclosure] at hsub_eq
      have hcard_top : Nat.card (⊤ : Subgroup (GarlingPolyGaloisGroup K L _)) = q * j := by
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
      rw [hsub_eq, Nat.card_zpowers] at hcard_top
      have hord_le : orderOf τ ≤ j :=
        Nat.le_of_dvd hj_pos (orderOf_dvd_of_pow_eq_one hτj)
      have hq2 := hq.two_le
      nlinarith
    -- Since σ ≠ 1 and σ ^ q = 1 with q prime, orderOf σ = q!
    have hord_σ : orderOf σ = q := orderOf_eq_prime hσq hσ_ne1
    have hmod_kj : k ^ j ≡ 1 [MOD q] := by
      rw [← hord_σ, ← pow_eq_pow_iff_modEq, pow_one]
      exact hσ_pow_kj.symm
    -- Hence u ^ j = 1 in (ZMod q)ˣ!
    have huj1 : u ^ j = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have hk_cast : ((k : ZMod q) ^ j) = 1 := by
        rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hmod_kj
      simpa [k] using hk_cast
    -- Since Subgroup.zpowers u = ⊤ in (ZMod q)ˣ, orderOf u = Nat.card (ZMod q)ˣ = q - 1!
    have hu_ord : orderOf u = q - 1 := by
      rw [← Nat.card_zpowers, hu_gen, Nat.card_congr Subgroup.topEquiv.toEquiv,
        Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
    have hq1_dvd_j : (q - 1) ∣ j := hu_ord ▸ orderOf_dvd_of_pow_eq_one huj1
    exact Nat.dvd_antisymm hj_dvd hq1_dvd_j
  · intro hj_eq
    subst hj_eq
    have hdiv1 : (q - 1) / (q - 1) = 1 := Nat.div_self (by have := hq.two_le; omega)
    rw [hdiv1, pow_one] at hu₀_eq
    subst hu₀_eq
    exact ⟨σ₀, τ₀, g, hg_gen, hclosure₀, hσ₀q, hτ₀j, hrel₀⟩

/-- **Concrete Counterexample to Literal `Exercise 16.4`** (`QUEUE.md` fidelity hold, Flag 2):
At `q = 3`, `K = ℚ(ζ₃) ⊆ ℂ` (`ζ₃ = exp(2πi / 3)`), and `θ = 2`:
`q = 3` is prime, `char K = 0 ≠ 3`, `x³ - 2` is irreducible in `K[x]`, `ω = ζ₃ ∈ K` is a primitive
`3`rd root of unity in `K` with `j = [K(ω) : K] = 1 < 2 = q - 1`, and for **every** splitting field
`L : K` of `x³ - 2`, `|Γ_K(x³ - 2)| = 3` while **no** `σ, τ ∈ Γ_K(x³ - 2)` and generator `u` of
`(ZMod 3)ˣ` satisfy `⟨σ, τ⟩ = Γ_K(x³ - 2)`, `σ³ = τ¹ = 1`, and `σ^u * τ = τ * σ`. -/
theorem exercise_16_4_counterexample :
    let ζ₃ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    let K : IntermediateField ℚ ℂ := ℚ⟮ζ₃⟯
    let ωK : K := ⟨ζ₃, IntermediateField.mem_adjoin_simple_self ℚ ζ₃⟩
    Nat.Prime 3 ∧
    ringChar K ≠ 3 ∧
    IsPrimitiveRoot ωK 3 ∧
    Irreducible (Polynomial.X ^ 3 - Polynomial.C (2 : K) : K[X]) ∧
    (∀ (L : Type u) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ 3 - Polynomial.C (2 : K)) →
      let ωL : L := algebraMap K L ωK
      IsPrimitiveRoot ωL 3 ∧
      Module.finrank K K⟮ωL⟯ = 1 ∧
      Nat.card (GarlingPolyGaloisGroup K L (Polynomial.X ^ 3 - Polynomial.C (2 : K))) = 3 ∧
      ¬ ∃ (σ τ : GarlingPolyGaloisGroup K L (Polynomial.X ^ 3 - Polynomial.C (2 : K)))
          (u : (ZMod 3)ˣ),
          Subgroup.zpowers u = ⊤ ∧
          Subgroup.closure ({σ, τ} : Set (GarlingPolyGaloisGroup K L _)) = ⊤ ∧
          σ ^ 3 = 1 ∧
          τ ^ 1 = 1 ∧
          σ ^ ((u : ZMod 3).val) * τ = τ * σ) := by
  intro ζ₃ K ωK
  have hζ₃ : IsPrimitiveRoot ζ₃ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hcharK : ringChar K ≠ 3 := by
    have _ : CharZero K :=
      ⟨fun a b hab => Nat.cast_injective (R := ℂ) (congrArg Subtype.val hab)⟩
    rw [ringChar.eq_zero]; decide
  have hωK : IsPrimitiveRoot ωK 3 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨by ext; exact hζ₃.pow_eq_one, fun l hl => ?_⟩
    exact hζ₃.dvd_of_pow_eq_one l (congrArg Subtype.val hl)
  -- [K : ℚ] = 2 while any root r of X^3 - 2 over ℚ generates degree 3, so X^3 - 2 has no root in K, hence is irreducible over K by Theorem 16.2!
  have hdegK : Module.finrank ℚ K = 2 := by
    have hm : minpoly ℚ ζ₃ = Polynomial.cyclotomic 3 ℚ :=
      (Polynomial.cyclotomic_eq_minpoly_rat hζ₃ (by decide)).symm
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ₃), hm,
      Polynomial.natDegree_cyclotomic]
    decide
  have _ : FiniteDimensional ℚ K :=
    Module.finite_of_finrank_pos (by rw [hdegK]; decide)
  have hfQ_irr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ) : ℚ[X]) :=
    (exercise_5_7 (p := 2) (n := 3) Nat.prime_two (by decide)).1
  have hfK_irr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (2 : K) : K[X]) := by
    have hnoroot : ¬ ∃ r : K, (Polynomial.X ^ 3 - Polynomial.C (2 : K)).eval r = 0 := by
      rintro ⟨r, hr⟩
      have hrQ : Polynomial.aeval (r : ℂ) (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)) = 0 := by
        have h1 : (r : ℂ) ^ 3 - 2 = 0 := by
          have h2 : r ^ 3 - 2 = 0 := by simpa using hr
          exact congrArg Subtype.val h2
        simpa using h1
      have hmin_r : minpoly ℚ (r : ℂ) = Polynomial.X ^ 3 - Polynomial.C (2 : ℚ) :=
        (minpoly.eq_of_irreducible_of_monic hfQ_irr hrQ
          (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide))).symm
      have hdeg_r : Module.finrank ℚ ℚ⟮(r : ℂ)⟯ = 3 := by
        have hr_int : IsIntegral ℚ (r : ℂ) :=
          ⟨Polynomial.X ^ 3 - Polynomial.C 2,
            Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide), hrQ⟩
        rw [IntermediateField.adjoin.finrank hr_int, hmin_r, Polynomial.natDegree_X_pow_sub_C]
      have hle_K : ℚ⟮(r : ℂ)⟯ ≤ K := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact r.2
      let K_over_r : IntermediateField ℚ⟮(r : ℂ)⟯ ℂ :=
        { K.toSubfield with algebraMap_mem' := fun x => hle_K x.2 }
      have hm := Module.finrank_mul_finrank ℚ ℚ⟮(r : ℂ)⟯ K_over_r
      change _ = Module.finrank ℚ K at hm
      rw [hdeg_r, hdegK] at hm
      omega
    rcases theorem_16_2_part1_unconditional (by decide : Nat.Prime 3) (2 : K) hcharK with
      ⟨hi, _⟩ | ⟨hr, _⟩
    · exact hi
    · exact (hnoroot hr).elim
  refine ⟨by decide, hcharK, hωK, hfK_irr, fun L _ _ hsf => ?_⟩
  intro ωL
  have hωL : IsPrimitiveRoot ωL 3 :=
    hωK.map_of_injective (algebraMap K L).injective
  have hj1 : Module.finrank K K⟮ωL⟯ = 1 := by
    have hbot : K⟮ωL⟯ = ⊥ := by
      rw [eq_bot_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.algebraMap_mem _ ωK
    rw [hbot, IntermediateField.finrank_bot]
  obtain ⟨_, _, hcard3, _⟩ :=
    exercise_16_4_repaired (by decide) hcharK hfK_irr hsf hωL hj1
  have hiff := exercise_16_4_printed_iff (by decide) hcharK hfK_irr hsf hωL hj1
  refine ⟨hωL, hj1, by simpa using hcard3, ?_⟩
  intro hex
  have h12 : 1 = 3 - 1 := hiff.mp hex
  omega

/-- **Exercise 16.5** (§16.2, printed p. 125 / PDF p. 133; `QUEUE.md` fidelity hold for open-ended
*"Describe the splitting field..."* prompt):
*"Suppose that `q` is a prime, that `char K = q` and that `θ ∈ K`. Describe the splitting field
for `x^q - θ` over `K`."*

Proves over any field `K` of prime characteristic `q` and any `θ ∈ K` that for **every** splitting
field extension `L : K` of `x^q - θ`:
1. `x^q - θ` has a **unique** root `α ∈ L` (`α^q = θ`), factors in `L[x]` as `(x - α)^q`, generates
   `L = K(α)`, makes `L : K` totally inseparable (`IsGarlingTotallyInseparable K L`), and has
   trivial Galois group `|Γ(L : K)| = 1`;
2. **Case (a) (`∃ c ∈ K, c^q = θ`):** `x^q - θ = (x - c)^q` already splits over `K`, `[L : K] = 1`
   (`L = K`), and `K : K` is a splitting field extension;
3. **Case (b) (`¬ ∃ c ∈ K, c^q = θ`):** `x^q - θ` is **irreducible** in `K[x]`, `[L : K] = q`, and
   `AdjoinRoot (X^q - C θ)` is an explicit splitting field extension of degree `q`. -/
theorem exercise_16_5 {K : Type u} [Field K] {q : ℕ} (hq : Nat.Prime q)
    (hchar : ringChar K = q) (θ : K) :
    (∀ (L : Type v) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ) →
      (∃! α : L, α ^ q = algebraMap K L θ) ∧
      (∀ α : L, α ^ q = algebraMap K L θ →
        (Polynomial.X ^ q - Polynomial.C θ).map (algebraMap K L) =
          (Polynomial.X - Polynomial.C α) ^ q ∧
        K⟮α⟯ = ⊤) ∧
      IsGarlingTotallyInseparable K L ∧
      Nat.card (GarlingGaloisGroup K L) = 1) ∧
    ((∃ c : K, c ^ q = θ) →
      GarlingSplitsOver K K (Polynomial.X ^ q - Polynomial.C θ) ∧
      IsGarlingSplittingFieldExtension K K (Polynomial.X ^ q - Polynomial.C θ) ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ) →
        Module.finrank K L = 1 ∧ extDegree K L = 1) ∧
    ((¬ ∃ c : K, c ^ q = θ) →
      Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]) ∧
      IsGarlingSplittingFieldExtension K (AdjoinRoot (Polynomial.X ^ q - Polynomial.C θ))
        (Polynomial.X ^ q - Polynomial.C θ) ∧
      Module.finrank K (AdjoinRoot (Polynomial.X ^ q - Polynomial.C θ)) = q ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ) →
        Module.finrank K L = q ∧ extDegree K L = q) := by
  have _ : CharP K q := hchar ▸ ringChar.charP K
  have _ : Fact q.Prime := ⟨hq⟩
  let f : K[X] := Polynomial.X ^ q - Polynomial.C θ
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C θ hq.ne_zero
  have hf_deg : f.natDegree = q := Polynomial.natDegree_X_pow_sub_C
  -- Helper: in characteristic q over any K-algebra field L, α^q = θ ⇔ (X - C α)^q = f.map!
  have char_q_fac : ∀ {L : Type*} [Field L] [Algebra K L] (α : L),
      α ^ q = algebraMap K L θ →
      (Polynomial.X ^ q - Polynomial.C θ).map (algebraMap K L) =
        (Polynomial.X - Polynomial.C α) ^ q := by
    intro L _ _ α hα
    have _ : CharP L q := charP_of_injective_algebraMap (algebraMap K L).injective q
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hα,
      sub_pow_char, Polynomial.C_pow]
  -- Part 1: Universal properties of any splitting field L : K of X^q - C θ
  have hpart1 : ∀ (L : Type v) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
      (∃! α : L, α ^ q = algebraMap K L θ) ∧
      (∀ α : L, α ^ q = algebraMap K L θ →
        f.map (algebraMap K L) = (Polynomial.X - Polynomial.C α) ^ q ∧ K⟮α⟯ = ⊤) ∧
      IsGarlingTotallyInseparable K L ∧
      Nat.card (GarlingGaloisGroup K L) = 1 := by
    intro L _ _ hsf
    have _ : CharP L q := charP_of_injective_algebraMap (algebraMap K L).injective q
    have hspL : (f.map (algebraMap K L)).Splits :=
      (garlingSplitsOver_iff_splits K L f).mp hsf.1
    have hcard_r : (f.map (algebraMap K L)).roots.card = q := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots hspL,
        Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hf_deg]
    have hne_r : (f.map (algebraMap K L)).roots ≠ 0 := by
      intro h0; rw [h0] at hcard_r; exact hq.ne_zero hcard_r.symm
    obtain ⟨α, hα_mem⟩ := Multiset.exists_mem_of_ne_zero hne_r
    have hα_pow : α ^ q = algebraMap K L θ := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
        map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hα_mem
      exact hα_mem
    have huniq : ∀ β : L, β ^ q = algebraMap K L θ → β = α := by
      intro β hβ
      have hsub : (β - α) ^ q = 0 := by rw [sub_pow_char, hβ, hα_pow, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsub)
    have hadj_top : ∀ β : L, β ^ q = algebraMap K L θ → K⟮β⟯ = ⊤ := by
      intro β hβ
      have hsplit_sub : GarlingSplitsOver K K⟮β⟯ f := by
        let βK : K⟮β⟯ := ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
        have hβK : βK ^ q = algebraMap K K⟮β⟯ θ := by ext; exact hβ
        refine ⟨q, 1, fun _ => βK, ?_⟩
        rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul, Finset.prod_const,
          Finset.card_fin]
        exact char_q_fac βK hβK
      by_contra hne
      exact hsf.2 K⟮β⟯ hne hsplit_sub
    have hsp_ml : Polynomial.IsSplittingField K L f :=
      (isGarlingSplittingFieldExtension_iff K L hf_monic.ne_zero).mp hsf
    have _ : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
    -- Every element x ∈ L = K(α) satisfies x^q ∈ K since (∑ c_i α^i)^q = ∑ c_i^q θ^i ∈ K!
    have hx_pow_mem : ∀ x : L, x ^ q ∈ Set.range (algebraMap K L) := by
      intro x
      have hx_mem : x ∈ K⟮α⟯ := by rw [hadj_top α hα_pow]; exact IntermediateField.mem_top
      -- Subring {x : L | x ^ q ∈ range (algebraMap K L)} is a Subfield containing K and α!
      let Fpow : IntermediateField K L :=
        { carrier := {y : L | y ^ q ∈ Set.range (algebraMap K L)}
          add_mem' := by
            rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
            exact ⟨ca + cb, by rw [add_pow_char, ← ha, ← hb, ← map_add]⟩
          zero_mem' := ⟨0, by rw [zero_pow hq.ne_zero, map_zero]⟩
          neg_mem' := by
            rintro a ⟨ca, ha⟩
            exact ⟨(-1) ^ q * ca, by rw [neg_eq_neg_one_mul, mul_pow, ← ha, map_mul, map_pow, map_neg, map_one]⟩
          mul_mem' := by
            rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
            exact ⟨ca * cb, by rw [mul_pow, ← ha, ← hb, ← map_mul]⟩
          one_mem' := ⟨1, by rw [one_pow, map_one]⟩
          inv_mem' := by
            rintro a ⟨ca, ha⟩
            exact ⟨ca⁻¹, by rw [inv_pow, ← ha, map_inv₀]⟩
          algebraMap_mem' := fun c => ⟨c ^ q, map_pow _ _ _⟩ }
      have hle_Fpow : K⟮α⟯ ≤ Fpow := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact ⟨θ, hα_pow.symm⟩
      exact hle_Fpow hx_mem
    -- Minimal polynomial over K of any x ∈ L \ K divides X^q - C c = (X - C x)^q, so has unique root x in L, hence is NOT separable!
    have htot_insep : IsGarlingTotallyInseparable K L := by
      refine ⟨(theorem_4_6 K L).1.mp ((isFiniteExtension_iff_moduleFinite K L).mpr inferInstance) |>.1, ?_⟩
      intro x hx_sep
      -- Since x is separable over K and x^q = c ∈ K, minpoly K x divides X^q - C c = (X - C x)^q in L[X];
      -- a separable polynomial dividing (X - C x)^q has natDegree ≤ 1, so x ∈ K!
      obtain ⟨c, hc⟩ := hx_pow_mem x
      have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
      have hdvd_min : minpoly K x ∣ Polynomial.X ^ q - Polynomial.C c := by
        refine minpoly.dvd K x ?_
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]
      have hsep_min : (minpoly K x).Separable :=
        (isGarlingSeparableElement_iff K x).mp hx_sep |>.2
      have hsep_L : ((minpoly K x).map (algebraMap K L)).Separable := hsep_min.map
      have hdvd_L : (minpoly K x).map (algebraMap K L) ∣ (Polynomial.X - Polynomial.C x) ^ q := by
        rw [← char_q_fac x hc.symm]
        exact Polynomial.map_dvd (algebraMap K L) hdvd_min
      -- Irreducible factors in L[X] of (X - C x)^q are all associated to X - C x; since squarefree, natDegree ≤ 1!
      have hsq : Squarefree ((minpoly K x).map (algebraMap K L)) := hsep_L.squarefree
      have hdeg_le1 : (minpoly K x).natDegree ≤ 1 := by
        by_contra hgt1
        have hge2 : 2 ≤ ((minpoly K x).map (algebraMap K L)).natDegree := by
          rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]; omega
        -- Since minpoly K x divides (X - C x)^q and is monic of degree d ≥ 2, by unique factorization in L[X] it equals (X - C x)^d!
        obtain ⟨u_fac, hu_eq⟩ :=
          (dvd_prime_pow (Polynomial.prime_X_sub_C x) q).mp hdvd_L
        rcases u_fac with ⟨k, hk_le, hasc⟩
        have hmon_map : ((minpoly K x).map (algebraMap K L)).Monic :=
          (minpoly.monic hx_int).map _
        have hmon_pow : ((Polynomial.X - Polynomial.C x) ^ k).Monic :=
          (Polynomial.monic_X_sub_C x).pow k
        have heq_pow : (minpoly K x).map (algebraMap K L) = (Polynomial.X - Polynomial.C x) ^ k :=
          Polynomial.eq_of_monic_of_associated hmon_map hmon_pow hasc
        have hk_ge2 : 2 ≤ k := by
          have hd_eq := congrArg Polynomial.natDegree heq_pow
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hd_eq
          omega
        have hdvd2 : (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C x) ∣
            (minpoly K x).map (algebraMap K L) := by
          rw [heq_pow]
          exact ⟨(Polynomial.X - Polynomial.C x) ^ (k - 2), by
            rw [← sq, ← pow_add, Nat.add_sub_of_le hk_ge2]⟩
        have hisunit := hsq (Polynomial.X - Polynomial.C x) hdvd2
        rw [Polynomial.isUnit_iff_degree_eq_zero,
          Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero x),
          Polynomial.natDegree_X_sub_C] at hisunit
        exact absurd hisunit (by decide)
      have hdeg1 : (minpoly K x).natDegree = 1 :=
        le_antisymm hdeg_le1 (minpoly.natDegree_pos hx_int)
      have hfin1 : Module.finrank K K⟮x⟯ = 1 := by
        rw [IntermediateField.adjoin.finrank hx_int, hdeg1]
      have hbot : (⊥ : IntermediateField K L) = K⟮x⟯ :=
        IntermediateField.eq_of_le_of_finrank_eq' bot_le (by rw [IntermediateField.finrank_bot, hfin1])
      have hx_bot : x ∈ (⊥ : IntermediateField K L) :=
        hbot ▸ IntermediateField.mem_adjoin_simple_self K x
      exact IntermediateField.mem_bot.mp hx_bot
    -- Any σ ∈ Γ(L : K) sends α to a root of X^q - θ, hence σ(α) = α by uniqueness, hence σ = 1!
    have hsub_gal : Subsingleton (GarlingGaloisGroup K L) := by
      refine ⟨fun σ₁ σ₂ => ?_⟩
      have h1 : (σ₁ α) ^ q = algebraMap K L θ := by
        rw [← map_pow, hα_pow, σ₁.commutes]
      have h2 : (σ₂ α) ^ q = algebraMap K L θ := by
        rw [← map_pow, hα_pow, σ₂.commutes]
      have heq_α : σ₁ α = σ₂ α := (huniq _ h1).trans (huniq _ h2).symm
      let Eeq : IntermediateField K L :=
        { (AlgHom.equalizer σ₁.toAlgHom σ₂.toAlgHom) with
          inv_mem' := fun {a} ha => by
            change σ₁ a⁻¹ = σ₂ a⁻¹; rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv ha }
      have htop_le : (⊤ : IntermediateField K L) ≤ Eeq := by
        rw [← hadj_top α hα_pow, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact heq_α
      ext x; exact htop_le IntermediateField.mem_top
    have hcard1 : Nat.card (GarlingGaloisGroup K L) = 1 := by
      let _ : Subsingleton (GarlingGaloisGroup K L) := hsub_gal
      exact Nat.card_unique
    exact ⟨⟨α, hα_pow, huniq⟩, fun β hβ => ⟨char_q_fac β hβ, hadj_top β hβ⟩, htot_insep, hcard1⟩
  -- Part 2: Case (a) θ = c^q for some c ∈ K
  have hpart2 : (∃ c : K, c ^ q = θ) →
      GarlingSplitsOver K K f ∧
      IsGarlingSplittingFieldExtension K K f ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L f →
        Module.finrank K L = 1 ∧ extDegree K L = 1 := by
    rintro ⟨c, hc⟩
    have hspK : GarlingSplitsOver K K f := by
      refine ⟨q, 1, fun _ => c, ?_⟩
      rw [GarlingSplitsExplicit, Polynomial.map_id, map_one, Polynomial.C_1, one_mul,
        Finset.prod_const, Finset.card_fin]
      simpa using char_q_fac (L := K) c hc
    have hsfK : IsGarlingSplittingFieldExtension K K f :=
      ⟨hspK, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
    refine ⟨hspK, hsfK, fun L _ _ hsfL => ?_⟩
    obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsfK hsfL
    have hfin1 : Module.finrank K L = 1 := by
      rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
    exact ⟨hfin1, by rw [extDegree_eq_finrank K L, hfin1]; rfl⟩
  -- Part 3: Case (b) θ is NOT a qth power in K ⇒ Irreducible f and [L : K] = q
  have hpart3 : (¬ ∃ c : K, c ^ q = θ) →
      Irreducible f ∧
      IsGarlingSplittingFieldExtension K (AdjoinRoot f) f ∧
      Module.finrank K (AdjoinRoot f) = q ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L f →
        Module.finrank K L = q ∧ extDegree K L = q := by
    intro hno
    -- Irreducibility proof in char q: if g ∣ f in K[X] is monic of degree 1 ≤ d < q, in a splitting field L, g = (X - α)^d, so coeff (d - 1) = -d * α ∈ K with (d : K) ≠ 0 ⇒ α ∈ K!
    obtain ⟨L₀, _, _, hsf₀, _⟩ := theorem_7_3_natDegree f
    obtain ⟨⟨α₀, hα₀, _⟩, hfac₀, _, _⟩ := hpart1 L₀ hsf₀
    have hf_irr : Irreducible f := by
      refine (Monic.irreducible_iff_natDegree hf_monic).mpr ⟨by have := hq.two_le; omega, ?_⟩
      intro g h hg_mon hh_mon hd_pos he_pos hmul
      exfalso
      let d := g.natDegree
      have hd_lt : d < q := by
        have hsum := congrArg Polynomial.natDegree hmul
        rw [hf_deg, Polynomial.natDegree_mul hg_mon.ne_zero hh_mon.ne_zero] at hsum
        omega
      have hd_ge1 : 1 ≤ d := hd_pos
      have hdvd_L₀ : g.map (algebraMap K L₀) ∣ (Polynomial.X - Polynomial.C α₀) ^ q := by
        rw [← (hfac₀ α₀ hα₀).1, hmul, Polynomial.map_mul]
        exact dvd_mul_right _ _
      obtain ⟨k, _, hasc⟩ :=
        (dvd_prime_pow (Polynomial.prime_X_sub_C α₀) q).mp hdvd_L₀
      have heq_pow : g.map (algebraMap K L₀) = (Polynomial.X - Polynomial.C α₀) ^ k :=
        Polynomial.eq_of_monic_of_associated (hg_mon.map _)
          ((Polynomial.monic_X_sub_C α₀).pow k) hasc
      have hk_eq : k = d := by
        have hdeg_eq := congrArg Polynomial.natDegree heq_pow
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L₀).injective,
          Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdeg_eq
        exact hdeg_eq.symm
      subst hk_eq
      -- Inspect coefficient of X^(d - 1) in (X - C α₀)^d: it equals -(d : L₀) * α₀!
      have hcoeff_pow :
          ((Polynomial.X - Polynomial.C α₀) ^ d).coeff (d - 1) = -(d : L₀) * α₀ := by
        -- Prove by induction on d ≥ 1!
        clear heq_pow hasc hdvd_L₀ hd_lt hmul he_pos
        induction d with
        | zero => omega
        | succ m ih =>
          rcases Nat.eq_zero_or_pos m with rfl | hm_pos
          · simp
          · have hsub1 : m + 1 - 1 = m := Nat.add_sub_cancel m 1
            rw [hsub1, pow_succ, sub_eq_add_neg, Polynomial.mul_add, Polynomial.coeff_add,
              Polynomial.mul_X, Polynomial.coeff_X_mul, ← sub_eq_add_neg]
            have h1 := ih hm_pos
            have hmon_m : ((Polynomial.X - Polynomial.C α₀) ^ m).Monic :=
              (Polynomial.monic_X_sub_C α₀).pow m
            have hdeg_m : ((Polynomial.X - Polynomial.C α₀) ^ m).natDegree = m := by
              rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
            have hcm : ((Polynomial.X - Polynomial.C α₀) ^ m).coeff m = 1 := by
              rw [← hdeg_m]; exact hmon_m.leadingCoeff
            have hmulC : ((Polynomial.X - Polynomial.C α₀) ^ m * -Polynomial.C α₀).coeff m = -α₀ := by
              rw [← Polynomial.C_neg, Polynomial.coeff_mul_C, hcm, one_mul]
            have hm_idx : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
            -- Wait: coeff_X_mul is (X * p).coeff (n + 1) = p.coeff n! Let's compute directly with Polynomial.coeff_mul_X!
            have hmulX : ((Polynomial.X - Polynomial.C α₀) ^ m * Polynomial.X).coeff m =
                -(m : L₀) * α₀ := by
              conv_lhs => rw [← hm_idx]
              rw [Polynomial.coeff_mul_X, h1]
            rw [sub_eq_add_neg] at hmulX hmulC ⊢
            -- Recompute cleanly:
            have hclean :
                ((Polynomial.X - Polynomial.C α₀) ^ (m + 1)).coeff m = -(↑(m + 1) : L₀) * α₀ := by
              rw [pow_succ, Polynomial.mul_sub, Polynomial.coeff_sub]
              have hx1 : ((Polynomial.X - Polynomial.C α₀) ^ m * Polynomial.X).coeff m =
                  -(m : L₀) * α₀ := by
                conv_lhs => rw [← hm_idx]
                rw [Polynomial.coeff_mul_X, h1]
              have hc1 : ((Polynomial.X - Polynomial.C α₀) ^ m * Polynomial.C α₀).coeff m = α₀ := by
                rw [Polynomial.coeff_mul_C, hcm, one_mul]
              rw [hx1, hc1, Nat.cast_add, Nat.cast_one]
              ring
            simpa [pow_succ, sub_eq_add_neg, Polynomial.mul_add] using hclean
      have hcoeff_map : (g.map (algebraMap K L₀)).coeff (d - 1) =
          algebraMap K L₀ (g.coeff (d - 1)) := Polynomial.coeff_map _ _
      rw [heq_pow, hcoeff_pow] at hcoeff_map
      have hdK_ne : (d : K) ≠ 0 := by
        intro hd0
        have hq_dvd : q ∣ d := (CharP.cast_eq_zero_iff K q d).mp hd0
        exact not_lt_of_ge (Nat.le_of_dvd hd_ge1 hq_dvd) hd_lt
      let c_cand : K := -(g.coeff (d - 1)) / (d : K)
      have hc_eq_α₀ : algebraMap K L₀ c_cand = α₀ := by
        have hdL_ne : (d : L₀) ≠ 0 := by
          simpa using (map_ne_zero (algebraMap K L₀)).mpr hdK_ne
        simp only [c_cand, map_div₀, map_neg, ← hcoeff_map, map_natCast]
        field_simp
      have hc_pow : c_cand ^ q = θ :=
        (algebraMap K L₀).injective (by rw [map_pow, hc_eq_α₀, hα₀])
      exact hno ⟨c_cand, hc_pow⟩
    -- AdjoinRoot f is a Field when Irreducible f!
    letI : Fact (Irreducible f) := ⟨hf_irr⟩
    let rAdj : AdjoinRoot f := AdjoinRoot.root f
    have hrAdj_pow : rAdj ^ q = algebraMap K (AdjoinRoot f) θ := by
      have hev : Polynomial.aeval rAdj f = 0 := AdjoinRoot.aeval_eq f
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hev
      exact hev
    have hsf_adj : IsGarlingSplittingFieldExtension K (AdjoinRoot f) f := by
      refine ⟨⟨q, 1, fun _ => rAdj, ?_⟩, ?_⟩
      · rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul, Finset.prod_const,
          Finset.card_fin]
        exact char_q_fac rAdj hrAdj_pow
      · intro M hM hspM
        have _ : CharP M q := charP_of_injective_algebraMap (algebraMap K M).injective q
        have hsp_ml := (garlingSplitsOver_iff_splits K M f).mp hspM
        have hcr : (f.map (algebraMap K M)).roots.card = q := by
          rw [← Polynomial.Splits.natDegree_eq_card_roots hsp_ml,
            Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective, hf_deg]
        obtain ⟨βM, hβM⟩ := Multiset.exists_mem_of_ne_zero
          (fun h0 => hq.ne_zero (by rw [h0] at hcr; exact hcr.symm))
        rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero),
          Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hβM
        have hsub0 : ((βM : AdjoinRoot f) - rAdj) ^ q = 0 := by
          have _ : CharP (AdjoinRoot f) q :=
            charP_of_injective_algebraMap (algebraMap K (AdjoinRoot f)).injective q
          rw [sub_pow_char]
          have hb_pow : (βM : AdjoinRoot f) ^ q = algebraMap K (AdjoinRoot f) θ := by
            simpa using congrArg (algebraMap M (AdjoinRoot f)) hβM
          rw [hb_pow, hrAdj_pow, sub_self]
        have hr_in_M : rAdj ∈ M := by
          have heq : (βM : AdjoinRoot f) = rAdj := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsub0)
          exact heq ▸ βM.2
        have htop_M : M = ⊤ := by
          rw [eq_top_iff]
          intro x _
          induction x using AdjoinRoot.induction_on with | ih p =>
          rw [AdjoinRoot.mk_eq_aeval]
          exact Polynomial.aeval_mem_of_mem M hr_in_M p
        exact hM htop_M
    have hfin_adj : Module.finrank K (AdjoinRoot f) = q := by
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf_monic.ne_zero),
        AdjoinRoot.powerBasis_dim, hf_deg]
    refine ⟨hf_irr, hsf_adj, hfin_adj, fun L _ _ hsfL => ?_⟩
    obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf_adj hsfL
    have hfinL : Module.finrank K L = q := by
      rw [← e.toLinearEquiv.finrank_eq, hfin_adj]
    exact ⟨hfinL, by rw [extDegree_eq_finrank K L, hfinL]⟩
  exact ⟨hpart1, hpart2, hpart3⟩

end Garling.Chapter16

