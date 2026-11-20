import Garling.Chapter12
import Garling.Chapter14
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.GroupTheory.Sylow

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
    [Field K] [Field L] [Algebra K L] {f : K[X]} (_hf0 : f ≠ 0)
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
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
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
  have hcommG : ∀ a b : GarlingGaloisGroup ℚ L, a * b = b * a :=
    @mul_comm _ (@IsCyclic.commGroup _ _ hcyc).toCommMagma
  let c01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let c12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hcomm : c01 * c12 = c12 * c01 := by
    have := hcommG (eGrp.symm c01) (eGrp.symm c12)
    have h2 := congrArg eGrp this
    rw [map_mul, map_mul, eGrp.apply_symm_apply, eGrp.apply_symm_apply] at h2
    exact h2
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
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
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
        rw [Polynomial.map_map]; rfl
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
        rw [Polynomial.map_map]; rfl
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
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσ_ω, ← pow_mul, ← pow_succ']
  have hσ_pow_β : ∀ k : ℕ, (σ ^ k) β = β := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσ_β]
  have hτ_pow_ω : ∀ k : ℕ, (τ ^ k) ω = ω ^ (14 ^ k) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hτ_ω, ← pow_mul, ← pow_succ']
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
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hσ_ω, hτ_ω, map_pow, map_pow, hτ_ω, hσ_ω,
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

set_option maxHeartbeats 800000 in
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
  have _ : CharZero L :=
    ⟨fun a b hab => Nat.cast_injective (R := ℚ) ((algebraMap ℚ L).injective (by simpa using hab))⟩
  obtain rfl : ‹Algebra ℚ L› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
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
        rw [Polynomial.map_map]; rfl
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
        rw [Polynomial.map_map]; rfl
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
        · simp only [DihedralGroup.r_mul_r, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            hΦFun_im, ← mul_assoc]
          congr 1
          rw [← pow_add, isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · simp only [DihedralGroup.r_mul_sr, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            map_neg, hΦFun_im, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · simp only [DihedralGroup.sr_mul_r, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            hΦFun_im, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
        · simp only [DihedralGroup.sr_mul_sr, AlgEquiv.mul_apply, hΦFun_α, map_mul, map_pow,
            map_neg, hΦFun_im, neg_neg, ← mul_assoc]
          congr 1
          rw [hneg_im3, ← pow_mul, ← pow_add,
            isPrimitiveRoot_pow_eq_pow_iff_modEq (by decide) him_prim]
          fin_cases a <;> fin_cases b <;> decide
    let ΦHom : DihedralGroup 4 →* (L ≃ₐ[ℚ] L) :=
      { toFun := ΦFun
        map_one' := by
          change ΦFun (.r 0) = 1
          exact aut_ext _ _ (hΦFun_im (.r 0)) (by simpa [ZMod.val_zero] using hΦFun_α (.r 0))
        map_mul' := hΦ_mul }
    have hΦ_inj : Function.Injective ΦHom := by
      intro g₁ g₂ heq
      have h1 : ΦFun g₁ im = ΦFun g₂ im := congrArg (fun g : L ≃ₐ[ℚ] L => g im) heq
      have h2 : ΦFun g₁ α = ΦFun g₂ α := congrArg (fun g : L ≃ₐ[ℚ] L => g α) heq
      have him_ne_neg : im ≠ -im := fun h => him_ne (by linear_combination h / 2)
      rcases g₁ with a | a <;> rcases g₂ with b | b
      · simp only [hΦFun_α] at h2
        have hp := mul_right_cancel₀ hα_ne h2
        have hv : a.val = b.val := him_prim.pow_inj a.val_lt b.val_lt hp
        exact congrArg DihedralGroup.r (ZMod.val_injective 4 hv)
      · simp only [hΦFun_im] at h1
        exact (him_ne_neg h1).elim
      · simp only [hΦFun_im] at h1
        exact (him_ne_neg h1.symm).elim
      · simp only [hΦFun_α] at h2
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
    have hg_eq : g = Φ (.r 2) := by
      change Φ.symm g = .r 2 at hΦg
      rw [← hΦg, Φ.apply_symm_apply]
    rw [hg_eq] at hg
    exact hmove (hg ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩)
  have h_r1_im : Φ (.r 1) im = im := hΦ_im (.r 1)
  have h_r1_α : Φ (.r 1) α = im * α := by
    have h := hΦ_α (.r 1); dsimp only at h
    have hv1 : (1 : ZMod 4).val = 1 := rfl
    rwa [hv1, pow_one] at h
  have h_r2_im : Φ (.r 2) im = im := hΦ_im (.r 2)
  have h_r2_α : Φ (.r 2) α = -α := by
    have h := hΦ_α (.r 2); dsimp only at h
    have hv2 : (2 : ZMod 4).val = 2 := rfl
    rw [hv2, him_sq] at h
    linear_combination h
  have h_sr0_im : Φ (.sr 0) im = -im := hΦ_im (.sr 0)
  have h_sr0_α : Φ (.sr 0) α = α := by
    have h := hΦ_α (.sr 0); dsimp only at h
    rwa [ZMod.val_zero, pow_zero, one_mul] at h
  have h_sr1_im : Φ (.sr 1) im = -im := hΦ_im (.sr 1)
  have h_sr1_α : Φ (.sr 1) α = -im * α := by
    have h := hΦ_α (.sr 1); dsimp only at h
    have hv1 : (1 : ZMod 4).val = 1 := rfl
    rwa [hv1, pow_one] at h
  have h_sr2_im : Φ (.sr 2) im = -im := hΦ_im (.sr 2)
  have h_sr2_α : Φ (.sr 2) α = -α := by
    have h := hΦ_α (.sr 2); dsimp only at h
    have hv2 : (2 : ZMod 4).val = 2 := rfl
    have hn : (-im) ^ 2 = -1 := by linear_combination him_sq
    rw [hv2, hn] at h
    linear_combination h
  have h_sr3_im : Φ (.sr 3) im = -im := hΦ_im (.sr 3)
  have h_sr3_α : Φ (.sr 3) α = im * α := by
    have h := hΦ_α (.sr 3); dsimp only at h
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
        rcases g with a | a
        · exact hΦ_im (.r a)
        · exact absurd hg (by fin_cases a <;> decide)
      exact IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hdeg_im, hfixed_finrank 1]; rfl)
    have hk2 : ex163Field α im 2 = IntermediateField.fixedField (Hsub 2) := by
      change ℚ⟮α ^ 2⟯ = IntermediateField.fixedField (Hsub 2)
      have hle : ℚ⟮α ^ 2⟯ ≤ IntermediateField.fixedField (Hsub 2) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
        rintro x (rfl | rfl) <;>
          rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff] <;>
          rintro _ ⟨g, hg, rfl⟩ <;> dsimp only [MulEquiv.coe_toMonoidHom] <;>
          rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
      have hQim_le : ℚ⟮im⟯ ≤ F4 :=
        IntermediateField.adjoin_le_iff.mpr (by
          rw [Set.singleton_subset_iff]
          exact IntermediateField.subset_adjoin ℚ ({im, α ^ 2} : Set L) (by simp))
      have hnot_mem : α ^ 2 ∉ ℚ⟮im⟯ := by
        intro hmem
        have hmem1 : α ^ 2 ∈ IntermediateField.fixedField (Hsub 1) := by
          change ex163Field α im 1 = _ at hk1
          rwa [← hk1]
        have hfix : Φ (.r 1) (α ^ 2) = α ^ 2 :=
          hmem1 ⟨Φ (.r 1), ⟨.r 1, by rw [SetLike.mem_coe, mem_d4Subgroup_iff]; decide, rfl⟩⟩
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
          SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        rintro _ ⟨g, hg, rfl⟩
        dsimp only [MulEquiv.coe_toMonoidHom]
        rw [SetLike.mem_coe, mem_d4Subgroup_iff] at hg
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
        simp only [Hsub, hk, Subgroup.mem_map]
        exact ⟨fun ⟨d, hd, hgd⟩ => hgd ▸ hd, fun hg =>
          ⟨Φ.symm g, by change Φ (Φ.symm g) ∈ H; simpa using hg, Φ.apply_symm_apply g⟩⟩
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
        have : Normal ℚ (IntermediateField.fixedField (Hsub k)) := hN
        rw [← IntermediateField.restrictNormalHom_ker (IntermediateField.fixedField (Hsub k))]
        exact MonoidHom.normal_ker _
      · intro hHN
        have : (Hsub k).Normal := hHN
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
    Xor (Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
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
      simp [hθ, zero_pow hq.ne_zero]
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
        Associated.irreducible ⟨Units.mk (Polynomial.C p_fac.leadingCoeff⁻¹)
          (Polynomial.C p_fac.leadingCoeff)
          (by simp [← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne])
          (by simp [← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne]), rfl⟩ hp_irr
      have hg_dvd : g ∣ f := by
        rcases hp_dvd with ⟨c, hc⟩
        exact ⟨Polynomial.C p_fac.leadingCoeff * c, by
          simp only [g]
          rw [mul_assoc, ← mul_assoc (Polynomial.C p_fac.leadingCoeff⁻¹),
            ← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne, Polynomial.C_1, one_mul, ← hc]⟩
      let d := g.natDegree
      have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero fun h0 => by
        change g.natDegree = 0 at h0
        exact hg_irr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hg_monic.ne_zero, h0]; rfl))
      have hd_le : d ≤ q := hf_deg ▸ Polynomial.natDegree_le_of_dvd hg_dvd hf_monic.ne_zero
      have hd_lt : d < q := by
        rcases eq_or_lt_of_le hd_le with hd_eq | hlt
        · exfalso
          have hd_eq' : g.natDegree = q := hd_eq
          have heq : f = g :=
            Polynomial.eq_of_monic_of_dvd_of_natDegree_le hg_monic hf_monic hg_dvd
              (by rw [hf_deg, hd_eq'])
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
      have hgL_prod : gL = (gL.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
        hgL_splits.eq_prod_roots_of_monic hgL_monic
      have hroots_pow : ∀ x ∈ gL.roots, x ^ q = algebraMap K L θ := by
        intro x hx
        have hmem_f : x ∈ (f.map (algebraMap K L)).roots :=
          Multiset.mem_of_le (Polynomial.roots.le_of_dvd (Polynomial.map_ne_zero hf_monic.ne_zero)
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
          rw [hfn, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
            Multiset.map_id', hcard_r]
        calc algebraMap K L g₀
            = (-1 : L) ^ d * gL.eval 0 := by
              rw [map_mul, map_pow, map_neg, map_one]
              congr 1
              simp [gL, Polynomial.eval_map, Polynomial.eval₂_at_zero,
                ← Polynomial.coeff_zero_eq_eval_zero]
          _ = (-1 : L) ^ d * ((-1 : L) ^ d * gL.roots.prod) := by rw [hev0]
          _ = gL.roots.prod := by
              rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
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
        (hq.coprime_iff_not_dvd.mpr fun hdvd =>
          not_lt_of_ge (Nat.le_of_dvd hd_pos hdvd) hd_lt).symm
      let a : ℤ := Nat.gcdA d q
      let b : ℤ := Nat.gcdB d q
      have hbez : (d : ℤ) * a + (q : ℤ) * b = 1 := by
        have h1 := Nat.gcd_eq_gcd_ab d q
        rw [hcop.gcd_eq_one] at h1
        simpa [a, b] using h1.symm
      let rootK : K := g₀ ^ a * θ ^ b
      refine ⟨rootK, ?_⟩
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero]
      calc rootK ^ q
          = (g₀ ^ a) ^ (q : ℤ) * (θ ^ b) ^ (q : ℤ) := by
            simp [rootK, mul_pow]
        _ = (g₀ ^ (q : ℤ)) ^ a * θ ^ ((q : ℤ) * b) := by
            rw [← zpow_mul g₀, mul_comm a (q : ℤ), zpow_mul g₀, ← zpow_mul θ, mul_comm b (q : ℤ)]
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
    Xor (Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))
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
    rw [GarlingSplitsExplicit, Algebra.algebraMap_self, Polynomial.map_id, map_one,
      Polynomial.C_1, one_mul, ← hr_pow]
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

set_option maxHeartbeats 800000 in
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
  have : Fact q.Prime := ⟨hq⟩
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
      rw [← hm]; exact pow_mem (IntermediateField.mem_adjoin_simple_self K ω) m
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
  have _ : IsGalois K K⟮ω⟯ := by
    have : (IntermediateField.fixingSubgroup K⟮ω⟯).Normal := hfix_normal
    have heq_f := IsGalois.fixedField_fixingSubgroup (K := K⟮ω⟯)
    rw [← heq_f]
    exact IsGalois.of_fixedField_normal_subgroup (IntermediateField.fixingSubgroup K⟮ω⟯)
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
          (isPrimitiveRoot_pow_eq_pow_iff_modEq hq.one_le hωK).mp (h1.symm.trans (pow_one ωK).symm)
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
          (isPrimitiveRoot_pow_eq_pow_iff_modEq hq.one_le hωK).mp (h12.symm.trans hcalc)
        ext
        rw [Units.val_mul, ← ZMod.natCast_zmod_val (toUnitsFun (ψ₁ * ψ₂) : ZMod q),
          ← ZMod.natCast_zmod_val (toUnitsFun ψ₁ : ZMod q),
          ← ZMod.natCast_zmod_val (toUnitsFun ψ₂ : ZMod q),
          ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
        exact hm }
  have htoUnits_inj : Function.Injective toUnitsHom := by
    intro ψ₁ ψ₂ heq
    change toUnitsFun ψ₁ = toUnitsFun ψ₂ at heq
    have hω_eq : ψ₁ ωK = ψ₂ ωK := by
      rw [htoUnits_spec ψ₁, htoUnits_spec ψ₂, heq]
    let Eeq : IntermediateField K L :=
      { carrier := {x : L | ∃ hx : x ∈ K⟮ω⟯, ψ₁ ⟨x, hx⟩ = ψ₂ ⟨x, hx⟩}
        add_mem' := by
          rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
          refine ⟨add_mem ha hb, ?_⟩
          change ψ₁ (⟨a, ha⟩ + ⟨b, hb⟩) = ψ₂ (⟨a, ha⟩ + ⟨b, hb⟩)
          rw [map_add, map_add, ea, eb]
        zero_mem' := ⟨zero_mem _, by change ψ₁ 0 = ψ₂ 0; simp⟩
        mul_mem' := by
          rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
          refine ⟨mul_mem ha hb, ?_⟩
          change ψ₁ (⟨a, ha⟩ * ⟨b, hb⟩) = ψ₂ (⟨a, ha⟩ * ⟨b, hb⟩)
          rw [map_mul, map_mul, ea, eb]
        one_mem' := ⟨one_mem _, by change ψ₁ 1 = ψ₂ 1; simp⟩
        inv_mem' := by
          rintro a ⟨ha, ea⟩
          refine ⟨inv_mem ha, ?_⟩
          change ψ₁ (⟨a, ha⟩)⁻¹ = ψ₂ (⟨a, ha⟩)⁻¹
          rw [map_inv₀, map_inv₀, ea]
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
    rw [show orderOf g = orderOf gTop from Subgroup.orderOf_coe gTop]
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
    change u ∈ H
    rw [h_eq_sub]
    exact Subgroup.mem_zpowers u
  obtain ⟨ψ₀, hψ₀_u⟩ := hu_in_range
  have hψ₀_ord : orderOf ψ₀ = j := by
    rw [← orderOf_injective toUnitsHom htoUnits_inj ψ₀, hψ₀_u, hu_ord]
  -- Degree of L / K is q * j since gcd(q, j) = 1
  have _ : FiniteDimensional K K⟮β⟯ := Module.Finite.left K K⟮β⟯ L
  have _ : FiniteDimensional K⟮ω⟯ L := Module.Finite.right K K⟮ω⟯ L
  have _ : FiniteDimensional K⟮β⟯ L := Module.Finite.right K K⟮β⟯ L
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
    have hgen : algebraMap (K⟮ω⟯)⟮β⟯ L pb.gen = β :=
      congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
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
    have hgen : algebraMap (K⟮β⟯)⟮ω⟯ L pb.gen = ω :=
      congrArg (algebraMap _ L) (IntermediateField.adjoin.powerBasis_gen _)
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
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic hω_int_Kβ)
        ((minpoly.monic (Algebra.IsIntegral.isIntegral ω)).map _)
        hdvd
        (by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K K⟮β⟯).injective,
              hmin_K_deg, hdeg_eq])).symm
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
        (minpoly.algebraMap_eq (algebraMap K⟮ω⟯ L).injective ωK).symm
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
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hτ_ω, ← pow_mul, mul_comm, ← pow_succ]
  have hτ_pow_β : ∀ m : ℕ, (τ ^ m) β = β := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hτ_β]
  have hσq : σ ^ q = 1 :=
    aut_ext _ _ (by rw [hσ_pow_ω]; rfl) (by rw [hσ_pow_β, hω.pow_eq_one, one_mul]; rfl)
  -- Helper: kVal ^ m ≡ ((u ^ m : (ZMod q)ˣ) : ZMod q).val [MOD q]
  have hkVal_pow_mod : ∀ m : ℕ, (kVal : ZMod q) ^ m = ((u ^ m : (ZMod q)ˣ) : ZMod q) := by
    intro m
    rw [Units.val_pow_eq_pow_val]
    simp [kVal]
  have hτj : τ ^ j = 1 := by
    refine aut_ext _ _ ?_ (by rw [hτ_pow_β]; rfl)
    rw [hτ_pow_ω]
    have hpow_u : u ^ j = 1 := by rw [← hu_ord, pow_orderOf_eq_one]
    have hmod : kVal ^ j ≡ 1 [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hkVal_pow_mod j, hpow_u, Units.val_one, Nat.cast_one]
    exact (isPrimitiveRoot_pow_eq_pow_iff_modEq hq.one_le hω).mpr hmod |>.trans (pow_one ω)
  have hord_σ : orderOf σ = q := by
    refine orderOf_eq_prime hσq fun h1 => ?_
    have hb := congrArg (fun g : L ≃ₐ[K] L => g β) h1
    simp only [hσ_β, AlgEquiv.one_apply] at hb
    have hw1 : ω = 1 := mul_right_cancel₀ hβ_ne (hb.trans (one_mul β).symm)
    have hq1 : q ≤ 1 := Nat.le_of_dvd (by decide) (hω.dvd_of_pow_eq_one 1 (by simpa using hw1))
    have := hq.two_le; omega
  have hord_τ : orderOf τ = j := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hτj)
    rw [← hu_ord]
    apply orderOf_dvd_of_pow_eq_one
    have hw := congrArg (fun g : L ≃ₐ[K] L => g ω) (pow_orderOf_eq_one τ)
    simp only [hτ_pow_ω, AlgEquiv.one_apply] at hw
    have hmod : kVal ^ orderOf τ ≡ 1 [MOD q] :=
      (isPrimitiveRoot_pow_eq_pow_iff_modEq hq.one_le hω).mp (hw.trans (pow_one ω).symm)
    have hz : ((u ^ orderOf τ : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [← hkVal_pow_mod, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hmod
    exact Units.ext hz
  have hrel : σ ^ kVal * τ = τ * σ := by
    refine aut_ext _ _ ?_ ?_
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ_ω, map_pow, hσ_pow_ω, hσ_ω, hτ_ω]
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
        have h1 : (b₁ : ℕ) ≡ (b₂ : ℕ) [MOD orderOf τ] :=
          pow_eq_pow_iff_modEq.mp hτ_eq
        rwa [hord_τ] at h1
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
  have : Fact q.Prime := ⟨hq⟩
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
      have hsub_eq : Subgroup.closure
          ({(1 : GarlingPolyGaloisGroup K L (Polynomial.X ^ q - Polynomial.C θ)), τ} : Set _) =
          Subgroup.zpowers τ := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x (rfl | hx)
          · exact one_mem _
          · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact Subgroup.mem_zpowers τ
        · rw [Subgroup.zpowers_le]
          exact Subgroup.subset_closure (by simp)
      rw [hclosure] at hsub_eq
      have hcard_top : Nat.card (⊤ : Subgroup (GarlingPolyGaloisGroup K L (Polynomial.X ^ q - Polynomial.C θ))) = q * j := by
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
    rw [hu₀_eq] at hrel₀
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
    have hζ₃_int : IsIntegral ℚ ζ₃ :=
      ⟨Polynomial.X ^ 3 - 1, by simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ) (by decide),
        by simp [hζ₃.pow_eq_one]⟩
    rw [IntermediateField.adjoin.finrank hζ₃_int, hm,
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
private theorem char_q_X_pow_sub_C_fac {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {q : ℕ} (hq : Nat.Prime q) (hchar : ringChar K = q) (a : K) (α : L)
    (hα : α ^ q = algebraMap K L a) :
    (Polynomial.X ^ q - Polynomial.C a).map (algebraMap K L) =
      (Polynomial.X - Polynomial.C α) ^ q := by
  have _ : CharP K q := hchar ▸ ringChar.charP K
  have _ : CharP L q := charP_of_injective_algebraMap (algebraMap K L).injective q
  have _ : Fact q.Prime := ⟨hq⟩
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hα,
    sub_pow_char, Polynomial.C_pow]

private theorem exercise_16_5_part1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {q : ℕ} (hq : Nat.Prime q) (hchar : ringChar K = q) (θ : K)
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ)) :
    (∃! α : L, α ^ q = algebraMap K L θ) ∧
    (∀ α : L, α ^ q = algebraMap K L θ →
      (Polynomial.X ^ q - Polynomial.C θ).map (algebraMap K L) =
        (Polynomial.X - Polynomial.C α) ^ q ∧ K⟮α⟯ = ⊤) ∧
    IsGarlingTotallyInseparable K L ∧
    Nat.card (GarlingGaloisGroup K L) = 1 := by
  have _ : CharP K q := hchar ▸ ringChar.charP K
  have _ : CharP L q := charP_of_injective_algebraMap (algebraMap K L).injective q
  have _ : Fact q.Prime := ⟨hq⟩
  let f : K[X] := Polynomial.X ^ q - Polynomial.C θ
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C θ hq.ne_zero
  have hf_deg : f.natDegree = q := Polynomial.natDegree_X_pow_sub_C
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
      exact char_q_X_pow_sub_C_fac hq hchar θ βK hβK
    by_contra hne
    exact hsf.2 K⟮β⟯ hne hsplit_sub
  have hsp_ml : Polynomial.IsSplittingField K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mp hsf
  have _ : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L f
  have hx_pow_mem : ∀ x : L, x ^ q ∈ Set.range (algebraMap K L) := by
    intro x
    have hx_mem : x ∈ K⟮α⟯ := by rw [hadj_top α hα_pow]; exact IntermediateField.mem_top
    let Fpow : IntermediateField K L :=
      { carrier := {y : L | y ^ q ∈ Set.range (algebraMap K L)}
        add_mem' := by
          rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
          exact ⟨ca + cb, by rw [add_pow_char, ← ha, ← hb, ← map_add]⟩
        zero_mem' := ⟨0, by rw [zero_pow hq.ne_zero, map_zero]⟩
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
  have htot_insep : IsGarlingTotallyInseparable K L := by
    refine ⟨(theorem_4_6 K L).1.mp ((isFiniteExtension_iff_moduleFinite K L).mpr inferInstance) |>.1, ?_⟩
    intro x hx_not_mem hx_sep
    obtain ⟨c, hc⟩ := hx_pow_mem x
    have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have hdvd_min : minpoly K x ∣ Polynomial.X ^ q - Polynomial.C c := by
      refine minpoly.dvd K x ?_
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]
    have hsep_min : (minpoly K x).Separable :=
      (isGarlingSeparableElement_iff K x).mp hx_sep
    have hsep_L : ((minpoly K x).map (algebraMap K L)).Separable := hsep_min.map
    have hdvd_L : (minpoly K x).map (algebraMap K L) ∣ (Polynomial.X - Polynomial.C x) ^ q := by
      rw [← char_q_X_pow_sub_C_fac hq hchar c x hc.symm]
      exact Polynomial.map_dvd (algebraMap K L) hdvd_min
    have hsq : Squarefree ((minpoly K x).map (algebraMap K L)) := hsep_L.squarefree
    have hdeg_le1 : (minpoly K x).natDegree ≤ 1 := by
      by_contra hgt1
      have hge2 : 2 ≤ ((minpoly K x).map (algebraMap K L)).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]; omega
      obtain ⟨k, _, hasc⟩ :=
        (dvd_prime_pow (Polynomial.prime_X_sub_C x) q).mp hdvd_L
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
      IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, hfin1])
    have hx_bot : x ∈ (⊥ : IntermediateField K L) :=
      hbot ▸ IntermediateField.mem_adjoin_simple_self K x
    exact hx_not_mem (IntermediateField.mem_bot.mp hx_bot)
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
  exact ⟨⟨α, hα_pow, huniq⟩, fun β hβ => ⟨char_q_X_pow_sub_C_fac hq hchar θ β hβ, hadj_top β hβ⟩,
    htot_insep, hcard1⟩

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
      (∀ [Fact (Irreducible (Polynomial.X ^ q - Polynomial.C θ : K[X]))],
        IsGarlingSplittingFieldExtension K (AdjoinRoot (Polynomial.X ^ q - Polynomial.C θ))
          (Polynomial.X ^ q - Polynomial.C θ) ∧
        Module.finrank K (AdjoinRoot (Polynomial.X ^ q - Polynomial.C θ)) = q) ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ q - Polynomial.C θ) →
        Module.finrank K L = q ∧ extDegree K L = q) := by
  have _ : CharP K q := hchar ▸ ringChar.charP K
  have _ : Fact q.Prime := ⟨hq⟩
  let f : K[X] := Polynomial.X ^ q - Polynomial.C θ
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C θ hq.ne_zero
  have hf_deg : f.natDegree = q := Polynomial.natDegree_X_pow_sub_C
  -- Part 1: Universal properties of any splitting field L : K of X^q - C θ
  have hpart1 : ∀ (L : Type v) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
      (∃! α : L, α ^ q = algebraMap K L θ) ∧
      (∀ α : L, α ^ q = algebraMap K L θ →
        f.map (algebraMap K L) = (Polynomial.X - Polynomial.C α) ^ q ∧ K⟮α⟯ = ⊤) ∧
      IsGarlingTotallyInseparable K L ∧
      Nat.card (GarlingGaloisGroup K L) = 1 :=
    fun L _ _ hsf => exercise_16_5_part1 hq hchar θ hsf
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
      rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul, Finset.prod_const,
        Finset.card_fin]
      exact char_q_X_pow_sub_C_fac hq hchar θ c hc
    have hsfK : IsGarlingSplittingFieldExtension K K f :=
      ⟨hspK, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
    refine ⟨hspK, hsfK, fun L _ _ hsfL => ?_⟩
    obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsfK hsfL
    have _ : FiniteDimensional K L := Module.Finite.equiv e.toLinearEquiv
    have hfin1 : Module.finrank K L = 1 := by
      rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
    exact ⟨hfin1, by rw [extDegree_eq_finrank K L, hfin1]; rfl⟩
  -- Part 3: Case (b) θ is NOT a qth power in K ⇒ Irreducible f and [L : K] = q
  have hpart3 : (¬ ∃ c : K, c ^ q = θ) →
      Irreducible f ∧
      (∀ [Fact (Irreducible f)],
        IsGarlingSplittingFieldExtension K (AdjoinRoot f) f ∧
        Module.finrank K (AdjoinRoot f) = q) ∧
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L f →
        Module.finrank K L = q ∧ extDegree K L = q := by
    intro hno
    obtain ⟨L₀, _, _, hsf₀, _⟩ := theorem_7_3_natDegree f
    obtain ⟨⟨α₀, hα₀, _⟩, hfac₀, _, _⟩ := exercise_16_5_part1 hq hchar θ hsf₀
    have hf_irr : Irreducible f := by
      have hf_not_unit : ¬ IsUnit f := by
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hf_monic.ne_zero,
          hf_deg]
        exact Nat.cast_ne_zero.mpr hq.ne_zero
      refine ⟨hf_not_unit, fun g₀ h₀ hmul₀ => ?_⟩
      by_cases hg0_unit : IsUnit g₀
      · exact Or.inl hg0_unit
      · by_cases hh0_unit : IsUnit h₀
        · exact Or.inr hh0_unit
        · exfalso
          have hg0_ne : g₀ ≠ 0 := fun h => by rw [h, zero_mul] at hmul₀; exact hf_monic.ne_zero hmul₀
          have hh0_ne : h₀ ≠ 0 := fun h => by rw [h, mul_zero] at hmul₀; exact hf_monic.ne_zero hmul₀
          let g : K[X] := g₀ * Polynomial.C g₀.leadingCoeff⁻¹
          have hlc_ne : g₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0_ne
          have hg_mon : g.Monic := by
            rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
              mul_inv_cancel₀ hlc_ne]
          have hg_deg_eq : g.natDegree = g₀.natDegree := by
            rw [Polynomial.natDegree_mul hg0_ne (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc_ne)),
              Polynomial.natDegree_C, add_zero]
          let d := g.natDegree
          have hd_ge1 : 1 ≤ d := by
            rw [Nat.one_le_iff_ne_zero]; intro hd0
            change g.natDegree = 0 at hd0
            apply hg0_unit
            rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hg0_ne, ← hg_deg_eq, hd0]
            rfl
          have hh_ge1 : 1 ≤ h₀.natDegree := by
            rw [Nat.one_le_iff_ne_zero]; intro hh0
            apply hh0_unit
            rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hh0_ne, hh0]
            rfl
          have hd_lt : d < q := by
            have hsum := congrArg Polynomial.natDegree hmul₀
            rw [hf_deg, Polynomial.natDegree_mul hg0_ne hh0_ne, ← hg_deg_eq] at hsum
            omega
          have hg_dvd_f : g ∣ f := ⟨Polynomial.C g₀.leadingCoeff * h₀, by
            simp only [g]
            rw [mul_assoc, ← mul_assoc (Polynomial.C g₀.leadingCoeff⁻¹), ← Polynomial.C_mul,
              inv_mul_cancel₀ hlc_ne, Polynomial.C_1, one_mul, ← hmul₀]⟩
          have hdvd_L₀ : g.map (algebraMap K L₀) ∣ (Polynomial.X - Polynomial.C α₀) ^ q := by
            rw [← (hfac₀ α₀ hα₀).1]
            exact Polynomial.map_dvd (algebraMap K L₀) hg_dvd_f
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
          have hcoeff_pow_gen : ∀ n : ℕ, 1 ≤ n →
              ((Polynomial.X - Polynomial.C α₀) ^ n).coeff (n - 1) = -(n : L₀) * α₀ := by
            intro n
            induction n with
            | zero => intro h; omega
            | succ m ih =>
              intro _
              rcases Nat.eq_zero_or_pos m with rfl | hm_pos
              · simp
              · have hsub1 : m + 1 - 1 = m := Nat.add_sub_cancel m 1
                rw [hsub1]
                have h1 := ih hm_pos
                have hmon_m : ((Polynomial.X - Polynomial.C α₀) ^ m).Monic :=
                  (Polynomial.monic_X_sub_C α₀).pow m
                have hdeg_m : ((Polynomial.X - Polynomial.C α₀) ^ m).natDegree = m := by
                  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
                have hcm : ((Polynomial.X - Polynomial.C α₀) ^ m).coeff m = 1 := by
                  rw [← hmon_m.coeff_natDegree]; congr 1; exact hdeg_m.symm
                have hm_idx : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
                rw [pow_succ, mul_sub, Polynomial.coeff_sub]
                have hx1 : ((Polynomial.X - Polynomial.C α₀) ^ m * Polynomial.X).coeff m =
                    -(m : L₀) * α₀ := by
                  conv_lhs => arg 2; rw [← hm_idx]
                  rw [Polynomial.coeff_mul_X, h1]
                have hc1 : ((Polynomial.X - Polynomial.C α₀) ^ m * Polynomial.C α₀).coeff m = α₀ := by
                  rw [Polynomial.coeff_mul_C, hcm, one_mul]
                rw [hx1, hc1, Nat.cast_add, Nat.cast_one]
                ring
          have hcoeff_pow := hcoeff_pow_gen d hd_ge1
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
    have hadj_fact : ∀ [Fact (Irreducible f)],
        IsGarlingSplittingFieldExtension K (AdjoinRoot f) f ∧
        Module.finrank K (AdjoinRoot f) = q := by
      intro _
      let rAdj : AdjoinRoot f := AdjoinRoot.root f
      have hrAdj_pow : rAdj ^ q = algebraMap K (AdjoinRoot f) θ := by
        have hev : Polynomial.aeval rAdj f = 0 :=
          (AdjoinRoot.aeval_eq f).trans AdjoinRoot.mk_self
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hev
        exact hev
      have hsf_adj : IsGarlingSplittingFieldExtension K (AdjoinRoot f) f := by
        refine ⟨⟨q, 1, fun _ => rAdj, ?_⟩, ?_⟩
        · rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul, Finset.prod_const,
            Finset.card_fin]
          exact char_q_X_pow_sub_C_fac hq hchar θ rAdj hrAdj_pow
        · intro M hM hspM
          have _ : CharP M q := charP_of_injective_algebraMap (algebraMap K M).injective q
          have hsp_ml := (garlingSplitsOver_iff_splits K M f).mp hspM
          have hcr : (f.map (algebraMap K M)).roots.card = q := by
            rw [← Polynomial.Splits.natDegree_eq_card_roots hsp_ml,
              Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective, hf_deg]
          have hne_m : (f.map (algebraMap K M)).roots ≠ 0 := fun h0 =>
            hq.ne_zero (by rw [h0] at hcr; exact hcr.symm)
          obtain ⟨βM, hβM⟩ := Multiset.exists_mem_of_ne_zero hne_m
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
            have hp_mem : ∀ p : K[X], Polynomial.aeval rAdj p ∈ M := by
              intro p
              induction p using Polynomial.induction_on' with
              | add p₁ p₂ hp₁ hp₂ => rw [map_add]; exact add_mem hp₁ hp₂
              | monomial k a =>
                rw [Polynomial.aeval_monomial]
                exact mul_mem (M.algebraMap_mem a) (pow_mem hr_in_M k)
            rw [eq_top_iff]
            intro x _
            induction x using AdjoinRoot.induction_on with | ih p =>
            rw [← AdjoinRoot.aeval_eq]
            exact hp_mem p
          exact hM htop_M
      have hfin_adj : Module.finrank K (AdjoinRoot f) = q := by
        rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf_monic.ne_zero),
          AdjoinRoot.powerBasis_dim, hf_deg]
      exact ⟨hsf_adj, hfin_adj⟩
    refine ⟨hf_irr, fun [_] => hadj_fact, fun L _ _ hsfL => ?_⟩
    have : Fact (Irreducible f) := ⟨hf_irr⟩
    obtain ⟨hsf_adj, hfin_adj⟩ := hadj_fact
    obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf_adj hsfL
    have _ : FiniteDimensional K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf_monic.ne_zero).finite
    have _ : FiniteDimensional K L := Module.Finite.equiv e.toLinearEquiv
    have hfinL : Module.finrank K L = q := by
      rw [← e.toLinearEquiv.finrank_eq, hfin_adj]
    exact ⟨hfinL, by rw [extDegree_eq_finrank K L, hfinL]⟩
  exact ⟨hpart1, hpart2, hpart3⟩

/-! ## §16.3 A sufficient condition (printed pp. 125–128, PDF pp. 133–136) -/

/-- **Inline prose definition** (§16.3, printed p. 125 / PDF p. 133):
*"Suppose that `G` is a group and that `K` is a field. A `(`K`-valued) character` on `G` is a
homomorphism of `G` into the multiplicative group `K*` of non-zero elements of `K`."* -/
abbrev GarlingCharacter (G : Type u) (K : Type v) [Group G] [Field K] : Type (max u v) :=
  G →* Kˣ

/-- Viewing a `K`-valued character on `G` as a `K`-valued function `G → K` inside the `K`-vector
space `G → K` (printed p. 125). -/
def GarlingCharacter.toFunK {G : Type u} {K : Type v} [Group G] [Field K]
    (γ : GarlingCharacter G K) : G → K :=
  fun g => (γ g : K)

/-- Distinct characters determine distinct `K`-valued functions on `G`. -/
theorem GarlingCharacter.toFunK_injective {G : Type u} {K : Type v} [Group G] [Field K] :
    Function.Injective (GarlingCharacter.toFunK (G := G) (K := K)) := by
  intro γ₁ γ₂ h
  ext g
  exact congrFun h g

/-- **Theorem 16.3** (§16.3, printed p. 125 / PDF p. 133; proof p. 126):
*"Suppose that `G` is a group, that `K` is a field and that `S` is a set of `K`-valued characters
on `G`. Then `S` is linearly independent over `K`."*

Proved in both Garling's Chapter 1 subset sense (`IsLinearlyIndependent K (toFunK '' S)`) and
Mathlib's indexed sense (`LinearIndependent K (fun γ : S => γ.1.toFunK)`). -/
theorem theorem_16_3 {G : Type u} {K : Type v} [Group G] [Field K]
    (S : Set (GarlingCharacter G K)) :
    IsLinearlyIndependent K (GarlingCharacter.toFunK '' S) ∧
    LinearIndependent K (fun γ : S => γ.1.toFunK) := by
  let toMH : GarlingCharacter G K → (G →* K) := fun γ => (Units.coeHom K).comp γ
  have htoMH_inj : Function.Injective toMH := by
    intro γ₁ γ₂ h
    ext g
    exact DFunLike.congr_fun h g
  have hLI_all : LinearIndependent K (fun γ : GarlingCharacter G K => γ.toFunK) :=
    (linearIndependent_monoidHom G K).comp toMH htoMH_inj
  have hLI_S : LinearIndependent K (fun γ : S => γ.1.toFunK) :=
    hLI_all.comp Subtype.val Subtype.val_injective
  have hG_LI : IsLinearlyIndependent K (GarlingCharacter.toFunK '' S) := by
    rw [isLinearlyIndependent_iff, LinearIndepOn, linearIndependent_iff']
    intro s c hsum f hf
    let g_idx : (GarlingCharacter.toFunK '' S) → S := fun x =>
      ⟨x.2.choose, x.2.choose_spec.1⟩
    have hg_spec : ∀ x : GarlingCharacter.toFunK '' S, (g_idx x).1.toFunK = x.1 :=
      fun x => x.2.choose_spec.2
    have hg_inj : Function.Injective g_idx := by
      intro x y hxy
      ext1
      rw [← hg_spec x, ← hg_spec y, hxy]
    have hLI_img : LinearIndependent K (fun x : GarlingCharacter.toFunK '' S => x.1) := by
      have hcomp := hLI_S.comp g_idx hg_inj
      convert hcomp using 1
      funext x
      exact (hg_spec x).symm
    exact (linearIndependent_iff'.mp hLI_img) s c hsum f hf
  exact ⟨hG_LI, hLI_S⟩

/-- **§16.3 Prose Bridge** (printed p. 126 / PDF p. 134):
*"If `τ` is an automorphism of a field `K`, then the restriction of `τ` to `K*` is a `K`-valued
character on `K*`."* -/
def garlingAutCharacter {K : Type u} [Field K] (τ : GarlingAut K) : GarlingCharacter Kˣ K :=
  Units.map τ.toRingHom.toMonoidHom

theorem garlingAutCharacter_apply {K : Type u} [Field K] (τ : GarlingAut K) (u : Kˣ) :
    (garlingAutCharacter τ).toFunK u = τ (u : K) := rfl

theorem garlingAutCharacter_injective {K : Type u} [Field K] :
    Function.Injective (garlingAutCharacter (K := K)) := by
  intro τ₁ τ₂ h
  ext x
  by_cases hx : x = 0
  · subst hx; simp
  · have hu := congrArg (fun γ : GarlingCharacter Kˣ K => γ.toFunK (Units.mk0 x hx)) h
    simpa [garlingAutCharacter_apply] using hu

/-- Helper: given finitely many distinct field automorphisms `τ : Fin n → GarlingAut K` and
coefficients `c : Fin n → K` with at least one `c i₀ ≠ 0`, there exists `k ∈ Kˣ` (hence `k ∈ K`,
`k ≠ 0`) such that `∑ i, c i * τ i k ≠ 0`. -/
theorem exists_ne_zero_sum_aut_apply {K : Type u} [Field K] {n : ℕ}
    (τ : Fin n → GarlingAut K) (hτ : Function.Injective τ)
    (c : Fin n → K) (hc : ∃ i : Fin n, c i ≠ 0) :
    ∃ k : K, k ≠ 0 ∧ ∑ i : Fin n, c i * τ i k ≠ 0 := by
  by_contra hno
  push Not at hno
  have hLI_all : LinearIndependent K (fun γ : GarlingCharacter Kˣ K => γ.toFunK) := by
    have h := (theorem_16_3 (Set.univ : Set (GarlingCharacter Kˣ K))).2
    exact h.comp (fun γ => ⟨γ, Set.mem_univ γ⟩) (fun _ _ hxy => congrArg Subtype.val hxy)
  have hLI_τ : LinearIndependent K (fun i : Fin n => (garlingAutCharacter (τ i)).toFunK) :=
    hLI_all.comp (fun i => garlingAutCharacter (τ i)) (garlingAutCharacter_injective.comp hτ)
  have hsum0 : ∑ i : Fin n, c i • (garlingAutCharacter (τ i)).toFunK = 0 := by
    ext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      garlingAutCharacter_apply]
    exact hno (u : K) u.ne_zero
  rcases hc with ⟨i₀, hi₀⟩
  exact hi₀ ((linearIndependent_iff'.mp hLI_τ) Finset.univ c hsum0 i₀ (Finset.mem_univ i₀))

/-- **Empty-list counterexample to unguarded `Corollary` [to Theorem 16.3]** (`QUEUE.md` Flag 5):
For `n = 0`, the empty sum is identically `0` for every `k ∈ K`, confirming that Garling's
`τ₁, ..., τ_n` implicitly assumes a non-empty list `1 ≤ n`. -/
theorem corollary_to_theorem_16_3_empty_counterexample (K : Type u) [Field K]
    (τ : Fin 0 → GarlingAut K) (c : Fin 0 → K) :
    Function.Injective τ ∧ (∀ i : Fin 0, c i ≠ 0) ∧
    ¬ ∃ k : K, ∑ i : Fin 0, c i * τ i k ≠ 0 := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- **Corollary** [to **Theorem 16.3**] (§16.3, printed p. 126 / PDF p. 134; non-empty list guard
`1 ≤ n` made explicit per `QUEUE.md` Flag 5):
*"Suppose that `τ₁, ..., τ_n` are distinct automorphisms of a field `K` and that `k₁, ..., k_n` are
non-zero elements of `K`. Then there exists `k` in `K` such that
`k₁ τ₁(k) + ... + k_n τ_n(k) ≠ 0`."* -/
theorem corollary_to_theorem_16_3 {K : Type u} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (τ : Fin n → GarlingAut K) (hτ : Function.Injective τ)
    (c : Fin n → K) (hc : ∀ i : Fin n, c i ≠ 0) :
    ∃ k : K, ∑ i : Fin n, c i * τ i k ≠ 0 := by
  obtain ⟨k, _, hk⟩ := exists_ne_zero_sum_aut_apply τ hτ c ⟨⟨0, hn⟩, hc ⟨0, hn⟩⟩
  exact ⟨k, hk⟩

/-- Convenience wrapper for distinct `K`-automorphisms `σ : Fin n → (L ≃ₐ[K] L)`. -/
theorem exists_apply_sum_ne_zero_of_algEquiv {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (σ : Fin n → (L ≃ₐ[K] L)) (hσ : Function.Injective σ)
    (c : Fin n → L) (hc : ∃ i : Fin n, c i ≠ 0) :
    ∃ x : L, ∑ i : Fin n, c i * σ i x ≠ 0 := by
  have hinj : Function.Injective (fun i : Fin n => (σ i).toRingEquiv) := by
    intro i j hij
    apply hσ
    ext x
    exact RingEquiv.congr_fun hij x
  obtain ⟨x, _, hx⟩ := exists_ne_zero_sum_aut_apply (fun i => (σ i).toRingEquiv) hinj c hc
  exact ⟨x, hx⟩

/-- **Inline prose definition** (§16.3, printed p. 126 / PDF p. 134):
*"We say that an extension `L : K` is `cyclic` if it is a Galois extension and `Γ(L : K)` is a
cyclic group."*
*(Recall that by §10.3 p. 84, `IsGarlingGaloisExtension K L` already bundles `[FiniteDimensional K L]`
and `[IsGalois K L]`.)* -/
def IsGarlingCyclicExtension (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Prop :=
  IsGarlingGaloisExtension K L ∧ IsCyclic (GarlingGaloisGroup K L)

/-- Helper: an element fixed by every `σ : L ≃ₐ[K] L` in a finite Galois extension `L : K` lies in
the base field `K` (`Set.range (algebraMap K L)`). -/
theorem mem_range_algebraMap_of_forall_gal_fix {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {x : L} (hfix : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ θ : K, algebraMap K L θ = x := by
  have hx_mem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact hfix σ
  have htop_eq : IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ := by
    have h := IsGalois.fixedField_fixingSubgroup (K := (⊥ : IntermediateField K L))
    rwa [IntermediateField.fixingSubgroup_bot] at h
  rw [htop_eq, IntermediateField.mem_bot] at hx_mem
  exact hx_mem

/-- Helper: if `σ` generates `L ≃ₐ[K] L` and `σ x = x`, then every `g : L ≃ₐ[K] L` fixes `x`. -/
theorem forall_gal_fix_of_gen_fix {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    {σ : L ≃ₐ[K] L} (hgen : Subgroup.zpowers σ = ⊤) {x : L} (hσx : σ x = x) :
    ∀ g : L ≃ₐ[K] L, g x = x := by
  let S : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {g : L ≃ₐ[K] L | g x = x}
      mul_mem' := fun {a b} ha hb => by change (a * b) x = x; rw [AlgEquiv.mul_apply, hb, ha]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        change a⁻¹ x = x
        exact a.injective (by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, ha]) }
  have hle : (⊤ : Subgroup (L ≃ₐ[K] L)) ≤ S := by
    rw [← hgen, Subgroup.zpowers_le]
    exact hσx
  intro g
  exact hle (Subgroup.mem_top g)

/-- **Theorem 16.4** (§16.3, printed p. 126 / PDF p. 134; proof pp. 126–127):
*"Suppose that `L : K` is a cyclic extension of degree `n`, that `char K` does not divide `n` and
that `K` contains a primitive `n`th root of unity, `ω` say. Then there exists `θ` in `K` such that
`x^n - θ` is irreducible over `K` and `L : K` is a splitting field extension for `x^n - θ`. If `β`
is a root of `x^n - θ` in `L`, then `L = K(β)`."*

Proved literally for all `n` (including `n = 1`) following Garling's proof via the Corollary to
Theorem 16.3. -/
theorem theorem_16_4 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hcyc : IsGarlingCyclicExtension K L) (hdeg : Module.finrank K L = n)
    (hchar : ¬ (ringChar K ∣ n)) {ω : K} (hω : IsPrimitiveRoot ω n) :
    ∃ θ : K,
      Irreducible (Polynomial.X ^ n - Polynomial.C θ : K[X]) ∧
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C θ) ∧
      ∀ β : L, Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C θ) = 0 →
        K⟮β⟯ = ⊤ := by
  obtain ⟨hn, _⟩ := pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hcyc.1 |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hcyc.1 |>.2
  have _ : IsCyclic (L ≃ₐ[K] L) := hcyc.2
  have hcardG : Nat.card (L ≃ₐ[K] L) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  obtain ⟨σ, hσ_gen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hσ_zpow : Subgroup.zpowers σ = ⊤ := by
    ext g; simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]; exact hσ_gen g
  have hσ_ord : orderOf σ = n := by
    rw [← Nat.card_zpowers, hσ_zpow, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
  have hσ_pow_inj : Function.Injective (fun k : Fin n => σ ^ (k : ℕ)) := by
    intro a b hab
    have hmod : (a : ℕ) ≡ (b : ℕ) [MOD n] := by
      have h1 := pow_eq_pow_iff_modEq.mp hab
      rwa [hσ_ord] at h1
    rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  let ωL : L := algebraMap K L ω
  have hωL : IsPrimitiveRoot ωL n := hω.map_of_injective (algebraMap K L).injective
  have hωL_ne : ωL ≠ 0 := hωL.ne_zero (Nat.ne_of_gt hn)
  have hσ_ωL : σ ωL = ωL := σ.commutes ω
  -- Apply Corollary to Theorem 16.3 to {1, σ, ..., σ^{n-1}} with coefficients 1, ωL, ..., ωL^{n-1}
  obtain ⟨α, hβ_ne⟩ := exists_apply_sum_ne_zero_of_algEquiv
    (fun k : Fin n => σ ^ (k : ℕ)) hσ_pow_inj
    (fun k : Fin n => ωL ^ (k : ℕ))
    ⟨⟨0, hn⟩, by simp⟩
  let β : L := ∑ k : Fin n, ωL ^ (k : ℕ) * (σ ^ (k : ℕ)) α
  change β ≠ 0 at hβ_ne
  -- Compute ωL * σ(β) = β by cyclic shift on Fin n
  have hωL_mul_σβ : ωL * σ β = β := by
    have h1 : ωL * σ β = ∑ k : Fin n, ωL ^ ((k : ℕ) + 1) * (σ ^ ((k : ℕ) + 1)) α := by
      simp only [β, map_sum, map_mul, map_pow, hσ_ωL, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← pow_succ' ωL, ← AlgEquiv.mul_apply, ← pow_succ']
    rw [h1]
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let shift : Fin n ≃ Fin n := Equiv.addRight (1 : Fin n)
    rw [← Equiv.sum_comp shift.symm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk_eq : (shift.symm k : ℕ) + 1 = if (k : ℕ) = 0 then n else (k : ℕ) := by
      have hsymm : shift.symm k = k - 1 := by simp [shift, sub_eq_add_neg]
      rw [hsymm]
      rcases eq_or_lt_of_le hn with rfl | hgt1
      · simp
      · have h1val : (1 : Fin n).val = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt hgt1
        have hsub_val : ((k - 1 : Fin n) : ℕ) = (n - 1 + (k : ℕ)) % n := by
          have h0 : ((k - 1 : Fin n) : ℕ) = (n - (1 : Fin n).val + (k : ℕ)) % n := by
            rw [Fin.sub_def]
          rw [h0, h1val]
        rw [hsub_val]
        have hlt : (k : ℕ) < n := k.isLt
        split_ifs with hk0
        · rw [hk0, add_zero, Nat.mod_eq_of_lt (by omega)]; omega
        · have hadd : n - 1 + (k : ℕ) = n + ((k : ℕ) - 1) := by omega
          rw [hadd, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hk_eq]
    split_ifs with hk0
    · rw [hk0, pow_zero, pow_zero, hωL.pow_eq_one,
        show σ ^ n = 1 from hσ_ord ▸ pow_orderOf_eq_one σ]
    · rfl
  have hσβ : σ β = ωL⁻¹ * β := by
    apply mul_left_cancel₀ hωL_ne
    rw [hωL_mul_σβ, ← mul_assoc, mul_inv_cancel₀ hωL_ne, one_mul]
  have hσ_pow_β : ∀ m : ℕ, (σ ^ m) β = (ωL⁻¹) ^ m * β := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, map_inv₀, hσ_ωL, hσβ,
        ← mul_assoc, ← pow_succ]
  have hσ_βn : σ (β ^ n) = β ^ n := by
    rw [map_pow, hσβ, mul_pow, inv_pow, hωL.pow_eq_one, inv_one, one_mul]
  obtain ⟨θ, hθ_eq⟩ :=
    mem_range_algebraMap_of_forall_gal_fix (forall_gal_fix_of_gen_fix hσ_zpow hσ_βn)
  -- Show K⟮β⟯ = ⊤ by exhibiting n distinct roots of minpoly K β in L
  have hβ_int : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hmin_dvd : minpoly K β ∣ Polynomial.X ^ n - Polynomial.C θ := by
    refine minpoly.dvd K β ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hθ_eq, sub_self]
  have hωL_inv : IsPrimitiveRoot ωL⁻¹ n := hωL.inv
  have hroots_inj : Function.Injective (fun k : Fin n => (σ ^ (k : ℕ)) β) := by
    intro a b hab
    dsimp only at hab
    rw [hσ_pow_β, hσ_pow_β] at hab
    exact Fin.ext (hωL_inv.pow_inj a.isLt b.isLt (mul_right_cancel₀ hβ_ne hab))
  have hmin_deg_ge : n ≤ (minpoly K β).natDegree := by
    let S : Finset L := Finset.univ.image (fun k : Fin n => (σ ^ (k : ℕ)) β)
    have hS_sub : S ⊆ ((minpoly K β).map (algebraMap K L)).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨k, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hβ_int)),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have hcard_le : S.card ≤ ((minpoly K β).map (algebraMap K L)).roots.card :=
      (Finset.card_le_card hS_sub).trans (Multiset.toFinset_card_le _)
    have hroots_le_deg : ((minpoly K β).map (algebraMap K L)).roots.card ≤ (minpoly K β).natDegree := by
      have h := Polynomial.card_roots' ((minpoly K β).map (algebraMap K L))
      rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective] at h
    have hS_card : S.card = n := by
      rw [Finset.card_image_of_injective _ hroots_inj, Finset.card_fin]
    omega
  have hmin_eq : minpoly K β = Polynomial.X ^ n - Polynomial.C θ :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hβ_int)
      (Polynomial.monic_X_pow_sub_C θ (Nat.ne_of_gt hn))
      hmin_dvd
      (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hmin_deg_ge)).symm
  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C θ : K[X]) :=
    hmin_eq ▸ minpoly.irreducible hβ_int
  have hKβ_top : K⟮β⟯ = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.adjoin.finrank hβ_int, hmin_eq, Polynomial.natDegree_X_pow_sub_C,
      LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hdeg]
  have hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C θ) := by
    refine ⟨⟨n, 1, fun k => ωL ^ (k : ℕ) * β, ?_⟩, ?_⟩
    · rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul,
        Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hθ_eq]
      exact X_pow_sub_C_pow_eq_prod hn hωL β
    · intro M hM hspM
      have hsp_ml := (garlingSplitsOver_iff_splits K M _).mp hspM
      have hcr : ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K M)).roots.card = n := by
        rw [← Polynomial.Splits.natDegree_eq_card_roots hsp_ml,
          Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective,
          Polynomial.natDegree_X_pow_sub_C]
      have hne_r : ((Polynomial.X ^ n - Polynomial.C θ).map (algebraMap K M)).roots ≠ 0 := by
        intro h0; rw [h0, Multiset.card_zero] at hcr; omega
      obtain ⟨γM, hγM⟩ := Multiset.exists_mem_of_ne_zero hne_r
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Polynomial.monic_X_pow_sub_C θ (Nat.ne_of_gt hn)).ne_zero),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
        map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hγM
      have hγL_pow : (γM : L) ^ n = β ^ n := by
        rw [← hθ_eq]
        simpa using congrArg (algebraMap M L) hγM
      have hratio_pow : ((γM : L) * β⁻¹) ^ n = 1 := by
        rw [mul_pow, inv_pow, hγL_pow, mul_inv_cancel₀ (pow_ne_zero n hβ_ne)]
      have : NeZero n := ⟨Nat.ne_of_gt hn⟩
      obtain ⟨k, _, hk⟩ := hωL.eq_pow_of_pow_eq_one hratio_pow
      have hβ_eq : β = (ωL ^ k)⁻¹ * (γM : L) := by
        have h1 : (γM : L) = ωL ^ k * β := by
          rw [hk, mul_assoc, inv_mul_cancel₀ hβ_ne, mul_one]
        rw [h1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hωL_ne), one_mul]
      have hβ_mem_M : β ∈ M := by
        rw [hβ_eq]
        exact mul_mem (inv_mem (pow_mem (M.algebraMap_mem ω) k)) γM.2
      have htop_le : (⊤ : IntermediateField K L) ≤ M := by
        rw [← hKβ_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact hβ_mem_M
      exact hM (le_antisymm le_top htop_le)
  refine ⟨θ, hirr, hsf, fun γ hγ => ?_⟩
  have hγ_int : IsIntegral K γ := Algebra.IsIntegral.isIntegral γ
  have hmin_γ : minpoly K γ = Polynomial.X ^ n - Polynomial.C θ :=
    (minpoly.eq_of_irreducible_of_monic hirr hγ (Polynomial.monic_X_pow_sub_C θ (Nat.ne_of_gt hn))).symm
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.adjoin.finrank hγ_int, hmin_γ, Polynomial.natDegree_X_pow_sub_C,
    LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hdeg]

/-- Helper: value of `k - 1` in `Fin n` (for `n ≥ 1`). -/
private theorem fin_sub_one_val {n : ℕ} [NeZero n] (k : Fin n) :
    ((k - 1 : Fin n) : ℕ) = if (k : ℕ) = 0 then n - 1 else (k : ℕ) - 1 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases eq_or_lt_of_le hn with rfl | hgt1
  · simp
  · have h1val : (1 : Fin n).val = 1 := by
      change 1 % n = 1
      exact Nat.mod_eq_of_lt hgt1
    have hsub_val : ((k - 1 : Fin n) : ℕ) = (n - 1 + (k : ℕ)) % n := by
      have h0 : ((k - 1 : Fin n) : ℕ) = (n - (1 : Fin n).val + (k : ℕ)) % n := by
        rw [Fin.sub_def]
      rw [h0, h1val]
    rw [hsub_val]
    have hlt : (k : ℕ) < n := k.isLt
    split_ifs with hk0
    · rw [hk0, add_zero, Nat.mod_eq_of_lt (by omega)]
    · have hadd : n - 1 + (k : ℕ) = n + ((k : ℕ) - 1) := by omega
      rw [hadd, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- Helper: if `L : K` is finite, `L` is algebraically closed, and `char K ∤ [L : K]`, then `L : K`
is a Garling Galois extension (`IsGarlingGaloisExtension K L`). -/
theorem isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L]
    (hchar : ¬ (ringChar K ∣ Module.finrank K L)) :
    IsGarlingGaloisExtension K L := by
  have hnorm : Normal K L :=
    { toIsAlgebraic := Algebra.IsAlgebraic.of_finite K L
      splits' := fun x => IsAlgClosed.splits _ }
  have hsep : Algebra.IsSeparable K L := by
    refine ⟨fun x => ?_⟩
    have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have hpos : 1 ≤ (minpoly K x).natDegree := minpoly.natDegree_pos hx_int
    have hdeg_dvd : (minpoly K x).natDegree ∣ Module.finrank K L := by
      have hm := Module.finrank_mul_finrank K K⟮x⟯ L
      rw [IntermediateField.adjoin.finrank hx_int] at hm
      exact ⟨Module.finrank K⟮x⟯ L, hm.symm⟩
    have hndvd_deg : ¬ (ringChar K ∣ (minpoly K x).natDegree) :=
      fun hd => hchar (hd.trans hdeg_dvd)
    have hcast_ne : ((minpoly K x).natDegree : K) ≠ 0 :=
      (pos_and_natCast_ne_zero_of_not_ringChar_dvd hndvd_deg).2
    have hderiv_ne : (minpoly K x).derivative ≠ 0 := by
      intro hd0
      have hc := congrArg (fun p : K[X] => p.coeff ((minpoly K x).natDegree - 1)) hd0
      rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
      have hsub : (minpoly K x).natDegree - 1 + 1 = (minpoly K x).natDegree :=
        Nat.sub_add_cancel hpos
      rw [hsub, (minpoly.monic hx_int).coeff_natDegree, one_mul] at hc
      have hcast_eq : (((minpoly K x).natDegree - 1 : ℕ) : K) + 1 = ((minpoly K x).natDegree : K) := by
        calc (((minpoly K x).natDegree - 1 : ℕ) : K) + 1
            = (((minpoly K x).natDegree - 1 : ℕ) : K) + ((1 : ℕ) : K) := by simp
          _ = (((minpoly K x).natDegree - 1 + 1 : ℕ) : K) := (Nat.cast_add _ 1).symm
          _ = ((minpoly K x).natDegree : K) := by rw [hsub]
      rw [hcast_eq] at hc
      exact hcast_ne hc
    rcases (minpoly.irreducible hx_int).isCoprime_or_dvd (minpoly K x).derivative with hcop | hdvd
    · exact hcop
    · exfalso
      have hle := Polynomial.natDegree_le_of_dvd hdvd hderiv_ne
      have hlt := Polynomial.natDegree_derivative_lt (by omega : (minpoly K x).natDegree ≠ 0)
      omega
  rw [isGarlingGaloisExtension_iff]
  exact ⟨inferInstance, @IsGalois.mk K _ L _ _ hsep hnorm⟩

/-- Helper: an algebraically closed field `L` with `¬ (char L ∣ n)` contains a primitive `n`th root
of unity. -/
theorem exists_isPrimitiveRoot_of_isAlgClosed {L : Type u} [Field L] [IsAlgClosed L]
    {n : ℕ} (hchar : ¬ (ringChar L ∣ n)) :
    ∃ ω : L, IsPrimitiveRoot ω n := by
  have hsp : GarlingSplitsOver L L (Polynomial.X ^ n - Polynomial.C (1 : L)) :=
    (garlingSplitsOver_iff_splits L L _).mpr (IsAlgClosed.splits _)
  have hsf : IsGarlingSplittingFieldExtension L L (Polynomial.X ^ n - Polynomial.C (1 : L)) :=
    ⟨hsp, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
  exact (section_16_1_root_factorization one_ne_zero hchar hsf).2.2.1

/-- Helper: if a field `K` contains a primitive `m`th root of unity (`1 ≤ m`), then the `m`th
cyclotomic polynomial `Φ_m` (`Polynomial.cyclotomic m K`) splits over `K`. -/
theorem garlingSplitsOver_cyclotomic_of_isPrimitiveRoot {K : Type u} [Field K]
    {m : ℕ} (hm : 1 ≤ m) {ω : K} (hω : IsPrimitiveRoot ω m) :
    GarlingSplitsOver K K (Polynomial.cyclotomic m K) := by
  rw [garlingSplitsOver_iff_splits, Algebra.algebraMap_self, Polynomial.map_id]
  have hfac : (Polynomial.X ^ m - 1 : K[X]) =
      ∏ k : Fin m, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ))) := by
    simpa [one_pow] using X_pow_sub_C_pow_eq_prod hm hω (1 : K)
  have hsp_all : (Polynomial.X ^ m - 1 : K[X]).Splits := by
    rw [hfac]
    have hsp_s : ∀ s : Finset (Fin m),
        (∏ k ∈ s, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ)))).Splits := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Polynomial.Splits.one]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact (Polynomial.Splits.X_sub_C _).mul ih
    exact hsp_s Finset.univ
  have hdvd : Polynomial.cyclotomic m K ∣ Polynomial.X ^ m - 1 := by
    rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hm K]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self m (Nat.ne_of_gt hm))
  have hne : (Polynomial.X ^ m - 1 : K[X]) ≠ 0 := by
    simpa using (Polynomial.monic_X_pow_sub_C (1 : K) (Nat.ne_of_gt hm)).ne_zero
  exact Polynomial.Splits.of_dvd hsp_all hne hdvd

/-- **Exercise 16.6 (i)** (§16.3, printed p. 127 / PDF p. 135):
Under `[L : K] = p` prime, `p ≠ char K`, `L` algebraically closed, and `p > 2`, both `Φ_p` and
`Φ_{p²}` split over `K` (and `K` contains primitive `p`th and `p²`th roots of unity). -/
theorem exercise_16_6_i {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L] {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hdeg : Module.finrank K L = p) (hchar : ringChar K ≠ p) :
    (∃ ω : K, IsPrimitiveRoot ω p) ∧
    (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2)) ∧
    GarlingSplitsOver K K (Polynomial.cyclotomic p K) ∧
    GarlingSplitsOver K K (Polynomial.cyclotomic (p ^ 2) K) := by
  have hcharL : ringChar L = ringChar K :=
    (ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)))
  have hndvd_p : ¬ (ringChar K ∣ p) := by
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
    · exact hchar ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
    · rw [h0] at hd; exact hp.ne_zero (zero_dvd_iff.mp hd)
  have hndvd_p2 : ¬ (ringChar L ∣ p ^ 2) := by
    rw [hcharL]
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
    · exact hndvd_p (hq.dvd_of_dvd_pow hd)
    · rw [h0] at hd; exact (pow_ne_zero 2 hp.ne_zero) (zero_dvd_iff.mp hd)
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank (hdeg.symm ▸ hndvd_p)
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  obtain ⟨ζL, hζL⟩ := exists_isPrimitiveRoot_of_isAlgClosed (L := L) hndvd_p2
  have hζL_ne : ζL ≠ 0 := hζL.ne_zero (pow_ne_zero 2 hp.ne_zero)
  let ωL : L := ζL ^ p
  have hωL : IsPrimitiveRoot ωL p := by
    have hdiv : p ^ 2 / p = p := by rw [sq, Nat.mul_div_cancel _ hp.pos]
    exact hdiv ▸ hζL.pow_of_dvd hp.ne_zero (dvd_pow_self p (by decide : 2 ≠ 0))
  -- Step 1: ωL ∈ K since deg(minpoly K ωL) ≤ deg(Φ_p) = p - 1 < p and divides [L : K] = p
  have hωL_in_K : ∃ ω : K, algebraMap K L ω = ωL := by
    have hωL_int : IsIntegral K ωL := Algebra.IsIntegral.isIntegral ωL
    have hdvd_cyc : minpoly K ωL ∣ Polynomial.cyclotomic p K := by
      refine minpoly.dvd K ωL ?_
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hωL.isRoot_cyclotomic hp.pos
    have hle_deg : (minpoly K ωL).natDegree ≤ p - 1 := by
      have h1 := Polynomial.natDegree_le_of_dvd hdvd_cyc (Polynomial.cyclotomic_ne_zero p K)
      rwa [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at h1
    have hdvd_p : Module.finrank K K⟮ωL⟯ ∣ p := by
      rw [← hdeg]
      exact ⟨Module.finrank K⟮ωL⟯ L, (Module.finrank_mul_finrank K K⟮ωL⟯ L).symm⟩
    have hfin1 : Module.finrank K K⟮ωL⟯ = 1 := by
      rw [IntermediateField.adjoin.finrank hωL_int] at hdvd_p ⊢
      rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hp_eq
      · exact h1
      · omega
    have hbot : (⊥ : IntermediateField K L) = K⟮ωL⟯ :=
      IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, hfin1])
    exact IntermediateField.mem_bot.mp (hbot ▸ IntermediateField.mem_adjoin_simple_self K ωL)
  obtain ⟨ωK, hωK_eq⟩ := hωL_in_K
  have hωK : IsPrimitiveRoot ωK p := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨(algebraMap K L).injective (by rw [map_pow, hωK_eq, hωL.pow_eq_one, map_one]),
      fun l hl => hωL.dvd_of_pow_eq_one l (by rw [← hωK_eq, ← map_pow, hl, map_one])⟩
  -- Step 2: ζL ∈ K using η ∈ L with η^p = ζL and odd-prime cancellation p ∣ p(p-1)/2
  have hζL_in_K : ∃ ζ : K, algebraMap K L ζ = ζL := by
    by_contra hnotK
    have hζ_not_bot : ζL ∉ (⊥ : IntermediateField K L) := fun h =>
      hnotK (IntermediateField.mem_bot.mp h)
    have hfin_gt1 : 1 < Module.finrank K K⟮ζL⟯ := by
      have hpos : 0 < Module.finrank K K⟮ζL⟯ := Module.finrank_pos
      by_contra hle
      have h1 : Module.finrank K K⟮ζL⟯ = 1 := by omega
      have hbot : (⊥ : IntermediateField K L) = K⟮ζL⟯ :=
        IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, h1])
      exact hζ_not_bot (hbot ▸ IntermediateField.mem_adjoin_simple_self K ζL)
    have hdvd_p : Module.finrank K K⟮ζL⟯ ∣ p := by
      rw [← hdeg]
      exact ⟨Module.finrank K⟮ζL⟯ L, (Module.finrank_mul_finrank K K⟮ζL⟯ L).symm⟩
    have hfin_eq_p : Module.finrank K K⟮ζL⟯ = p := by
      rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hp_eq
      · omega
      · exact hp_eq
    have hKζ_top : K⟮ζL⟯ = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hfin_eq_p, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hdeg])
    have hcardG : Nat.card (L ≃ₐ[K] L) = p := by
      rw [IsGalois.card_aut_eq_finrank K L, hdeg]
    have : Fact p.Prime := ⟨hp⟩
    have hcycG : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hcardG
    obtain ⟨σ, hσ_gen⟩ := hcycG.exists_generator
    have hσ_zpow : Subgroup.zpowers σ = ⊤ := by
      ext g; simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_top, iff_true]; exact hσ_gen g
    have hσ_ord : orderOf σ = p := by
      rw [← Nat.card_zpowers, hσ_zpow, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
    have hσp : σ ^ p = 1 := hσ_ord ▸ pow_orderOf_eq_one σ
    have hσζ_ne : σ ζL ≠ ζL := by
      intro hfix
      exact hnotK (mem_range_algebraMap_of_forall_gal_fix (forall_gal_fix_of_gen_fix hσ_zpow hfix))
    have hratio_p : (σ ζL * ζL⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, ← map_pow]
      change σ ωL * ωL⁻¹ = 1
      rw [← hωK_eq, σ.commutes, hωK_eq, mul_inv_cancel₀ (hωL.ne_zero hp.ne_zero)]
    obtain ⟨r, _, hr⟩ := hωL.eq_pow_of_pow_eq_one hratio_p
    have hσζ : σ ζL = ωL ^ r * ζL := by
      rw [hr, mul_assoc, inv_mul_cancel₀ hζL_ne, mul_one]
    have hωr_ne1 : ωL ^ r ≠ 1 := by
      intro h1; rw [h1, one_mul] at hσζ; exact hσζ_ne hσζ
    -- Take η ∈ L with η^p = ζL (exists since L is algebraically closed)
    have hdeg_η : (Polynomial.X ^ p - Polynomial.C ζL : L[X]).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.monic_X_pow_sub_C ζL hp.ne_zero).ne_zero,
        Polynomial.natDegree_X_pow_sub_C]
      exact Nat.cast_ne_zero.mpr hp.ne_zero
    obtain ⟨η, hη_root⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C ζL) hdeg_η
    have hη_pow : η ^ p = ζL := by
      simpa [Polynomial.IsRoot.def, sub_eq_zero] using hη_root
    have hη_ne : η ≠ 0 := by
      intro h0; rw [h0, zero_pow hp.ne_zero] at hη_pow; exact hζL_ne hη_pow.symm
    let u : L := σ η * η⁻¹
    have hu_p : u ^ p = ωL ^ r := by
      rw [mul_pow, inv_pow, ← map_pow, hη_pow, ← hr]
    have hu_p2 : u ^ (p ^ 2) = 1 := by
      rw [sq, pow_mul, hu_p, ← pow_mul, mul_comm, pow_mul, hωL.pow_eq_one, one_pow]
    obtain ⟨a, _, ha⟩ := hζL.eq_pow_of_pow_eq_one hu_p2
    let c : L := ωL ^ (r * a)
    have hσc : σ c = c := by
      have hcK : c = algebraMap K L (ωK ^ (r * a)) := by simp [c, ← hωK_eq]
      rw [hcK, σ.commutes]
    have hcp : c ^ p = 1 := by
      change (ωL ^ (r * a)) ^ p = 1
      rw [← pow_mul, mul_comm (r * a) p, pow_mul, hωL.pow_eq_one, one_pow]
    have hσu : σ u = c * u := by
      rw [← ha, map_pow, hσζ, mul_pow, ← pow_mul, ha]
    have hση : σ η = u * η := by
      simp only [u, mul_assoc, inv_mul_cancel₀ hη_ne, mul_one]
    have hσ_pow_η : ∀ k : ℕ, (σ ^ k) η = c ^ (k * (k - 1) / 2) * u ^ k * η := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_mul, map_pow σ c, map_pow σ u,
          hσc, hσu, hση, mul_pow]
        have htri : k * (k - 1) / 2 + k = (k + 1) * k / 2 := by
          rcases k with _ | m
          · rfl
          · have heven : 2 ∣ (m + 1) * m := by
              rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
              · exact ⟨(t + t + 1) * t, by ring⟩
              · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
            rcases heven with ⟨q, hq⟩
            have h1 : (m + 1) * (m + 1 - 1) = 2 * q := by simpa using hq
            have h2 : (m + 1 + 1) * (m + 1) = 2 * (q + (m + 1)) := by linarith
            rw [h1, h2, Nat.mul_div_right _ (by decide), Nat.mul_div_right _ (by decide)]
        calc c ^ (k * (k - 1) / 2) * (c ^ k * u ^ k) * (u * η)
            = c ^ (k * (k - 1) / 2 + k) * (u ^ k * u) * η := by rw [pow_add]; ring
          _ = c ^ ((k + 1) * k / 2) * u ^ (k + 1) * η := by rw [htri, ← pow_succ]
          _ = c ^ ((k + 1) * (k + 1 - 1) / 2) * u ^ (k + 1) * η := by simp
    have hη_fix := hσ_pow_η p
    rw [hσp, AlgEquiv.one_apply, hu_p] at hη_fix
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    rcases hp_odd with ⟨t, ht⟩
    have hdiv_tri : p * (p - 1) / 2 = p * t := by
      have hp1 : p - 1 = 2 * t := by omega
      rw [hp1, show p * (2 * t) = 2 * (p * t) by ring, Nat.mul_div_right _ (by decide)]
    rw [hdiv_tri, pow_mul, hcp, one_pow, one_mul] at hη_fix
    have hωr_eq1 : ωL ^ r = 1 :=
      mul_right_cancel₀ hη_ne (hη_fix.symm.trans (one_mul η).symm)
    exact hωr_ne1 hωr_eq1
  obtain ⟨ζK, hζK_eq⟩ := hζL_in_K
  have hζK : IsPrimitiveRoot ζK (p ^ 2) := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨(algebraMap K L).injective (by rw [map_pow, hζK_eq, hζL.pow_eq_one, map_one]),
      fun l hl => hζL.dvd_of_pow_eq_one l (by rw [← hζK_eq, ← map_pow, hl, map_one])⟩
  exact ⟨⟨ωK, hωK⟩, ⟨ζK, hζK⟩,
    garlingSplitsOver_cyclotomic_of_isPrimitiveRoot hp.one_le hωK,
    garlingSplitsOver_cyclotomic_of_isPrimitiveRoot (by have := hp.one_le; nlinarith) hζK⟩

/-- **Exercise 16.6 (ii)** (§16.3, printed p. 127 / PDF p. 135):
There exists `θ ∈ K` such that `x^p - θ` is irreducible over `K` and `L : K` is a splitting field
extension for `x^p - θ`. -/
theorem exercise_16_6_ii {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L] {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hdeg : Module.finrank K L = p) (hchar : ringChar K ≠ p) :
    ∃ θ : K,
      Irreducible (Polynomial.X ^ p - Polynomial.C θ : K[X]) ∧
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ p - Polynomial.C θ) := by
  have hndvd_p : ¬ (ringChar K ∣ p) := by
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
    · exact hchar ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
    · rw [h0] at hd; exact hp.ne_zero (zero_dvd_iff.mp hd)
  obtain ⟨⟨ωK, hωK⟩, _, _, _⟩ := exercise_16_6_i hp hp2 hdeg hchar
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank (hdeg.symm ▸ hndvd_p)
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hcardG : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsGarlingCyclicExtension K L := ⟨hgal, isCyclic_of_prime_card hcardG⟩
  obtain ⟨θ, hirr, hsf, _⟩ := theorem_16_4 hcyc hdeg hndvd_p hωK
  exact ⟨θ, hirr, hsf⟩

/-- **Exercise 16.6 (iii)** (§16.3, printed p. 127 / PDF p. 135):
For any `θ ∈ K` with `x^p - θ` irreducible over `K` (under `[L : K] = p` prime, `IsAlgClosed L`),
`f = x^{p²} - θ` has no roots in `K` and factors as `f = ∏ j : Fin p, f_j` where each `f_j ∈ K[x]`
is monic and irreducible of degree `p`. -/
theorem exercise_16_6_iii {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L] {p : ℕ} (hp : Nat.Prime p)
    (hdeg : Module.finrank K L = p) {θ : K}
    (hirr : Irreducible (Polynomial.X ^ p - Polynomial.C θ : K[X])) :
    (¬ ∃ c : K, (Polynomial.X ^ (p ^ 2) - Polynomial.C θ).eval c = 0) ∧
    ∃ fs : Fin p → K[X],
      (Polynomial.X ^ (p ^ 2) - Polynomial.C θ : K[X]) = ∏ j : Fin p, fs j ∧
      ∀ j : Fin p, (fs j).Monic ∧ Irreducible (fs j) ∧ (fs j).natDegree = p := by
  let f : K[X] := Polynomial.X ^ (p ^ 2) - Polynomial.C θ
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C θ (pow_ne_zero 2 hp.ne_zero)
  have hf_deg : f.natDegree = p ^ 2 := Polynomial.natDegree_X_pow_sub_C
  have hnoroot : ¬ ∃ c : K, f.eval c = 0 := by
    rintro ⟨c, hc⟩
    have hc_pow : (c ^ p) ^ p = θ := by
      rw [← pow_mul, ← sq]
      simpa [f, sub_eq_zero] using hc
    have hroot_p : (Polynomial.X ^ p - Polynomial.C θ).eval (c ^ p) = 0 := by
      simp [hc_pow]
    obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot_p
    rcases hirr.isUnit_or_isUnit hq_fac with hu1 | hu2
    · rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
        Polynomial.natDegree_X_sub_C] at hu1
      exact absurd hu1 (by decide)
    · have hq0 : q_fac ≠ 0 := fun h => by
        rw [h, mul_zero] at hq_fac
        exact (Polynomial.monic_X_pow_sub_C θ hp.ne_zero).ne_zero hq_fac
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
      have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
      have hdeg_eq := congrArg Polynomial.natDegree hq_fac
      rw [Polynomial.natDegree_X_pow_sub_C,
        Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
        Polynomial.natDegree_X_sub_C, hqd] at hdeg_eq
      have := hp.two_le; omega
  -- Every irreducible factor of f in K[X] has degree p!
  have hirr_deg_p : ∀ g : K[X], g.Monic → Irreducible g → g ∣ f → g.natDegree = p := by
    intro g hg_mon hg_irr hg_dvd
    have hg_pos : 1 ≤ g.natDegree := Nat.pos_of_ne_zero fun h0 =>
      hg_irr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hg_mon.ne_zero, h0]; rfl))
    have hdeg_map : (g.map (algebraMap K L)).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.map_ne_zero hg_mon.ne_zero),
        Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]
      exact Nat.cast_ne_zero.mpr (by omega)
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_root (g.map (algebraMap K L)) hdeg_map
    have hγ_aev : Polynomial.aeval γ g = 0 := by
      rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hmin_eq : minpoly K γ = g :=
      (minpoly.eq_of_irreducible_of_monic hg_irr hγ_aev hg_mon).symm
    have hdvd_p : g.natDegree ∣ p := by
      have hm := Module.finrank_mul_finrank K K⟮γ⟯ L
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral γ), hmin_eq, hdeg] at hm
      exact ⟨Module.finrank K⟮γ⟯ L, hm.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hp_eq
    · exfalso
      have hlin : g = Polynomial.X + Polynomial.C (g.coeff 0) := by
        ext k
        rcases k with _ | _ | m
        · simp
        · simp [show g.coeff 1 = 1 from h1 ▸ hg_mon.coeff_natDegree]
        · have hgt : g.natDegree < m + 2 := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, Polynomial.coeff_add,
            Polynomial.coeff_X, Polynomial.coeff_C]
          simp
      have hroot_g : g.eval (-g.coeff 0) = 0 := by rw [hlin]; simp
      have hroot_f : f.eval (-g.coeff 0) = 0 := by
        rcases hg_dvd with ⟨h, hh⟩
        rw [hh, Polynomial.eval_mul, hroot_g, zero_mul]
      exact hnoroot ⟨-g.coeff 0, hroot_f⟩
    · exact hp_eq
  -- Factor f into monic irreducibles by strong induction on degree of monic divisors of f
  have hfac_div : ∀ (m : ℕ) (h : K[X]), h.Monic → h ∣ f → h.natDegree = m * p →
      ∃ fs : Fin m → K[X], h = ∏ j : Fin m, fs j ∧
        ∀ j : Fin m, (fs j).Monic ∧ Irreducible (fs j) ∧ (fs j).natDegree = p := by
    intro m
    induction m with
    | zero =>
      intro h hh_mon _ hh_deg
      rw [zero_mul] at hh_deg
      refine ⟨fun j => j.elim0, ?_, fun j => j.elim0⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty]
      exact Polynomial.eq_one_of_monic_natDegree_zero hh_mon hh_deg
    | succ m ih =>
      intro h hh_mon hh_dvd hh_deg
      have hh_not_unit : ¬ IsUnit h := by
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hh_mon.ne_zero,
          hh_deg]
        exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero m) hp.ne_zero)
      obtain ⟨q_fac, hq_irr, hq_dvd⟩ :=
        WfDvdMonoid.exists_irreducible_factor hh_not_unit hh_mon.ne_zero
      have hlc_ne : q_fac.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_irr.ne_zero
      let g : K[X] := q_fac * Polynomial.C q_fac.leadingCoeff⁻¹
      have hg_mon : g.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          mul_inv_cancel₀ hlc_ne]
      have hg_irr : Irreducible g :=
        Associated.irreducible ⟨Units.mk (Polynomial.C q_fac.leadingCoeff⁻¹)
          (Polynomial.C q_fac.leadingCoeff)
          (by simp [← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne])
          (by simp [← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne]), rfl⟩ hq_irr
      have hg_dvd_h : g ∣ h := by
        rcases hq_dvd with ⟨c, hc⟩
        exact ⟨Polynomial.C q_fac.leadingCoeff * c, by
          simp only [g]
          rw [mul_assoc, ← mul_assoc (Polynomial.C q_fac.leadingCoeff⁻¹), ← Polynomial.C_mul,
            inv_mul_cancel₀ hlc_ne, Polynomial.C_1, one_mul, ← hc]⟩
      have hg_deg : g.natDegree = p := hirr_deg_p g hg_mon hg_irr (hg_dvd_h.trans hh_dvd)
      rcases hg_dvd_h with ⟨h', hh'⟩
      have hh'_ne : h' ≠ 0 := fun h0 => by rw [h0, mul_zero] at hh'; exact hh_mon.ne_zero hh'
      have hh'_mon : h'.Monic := by
        have hlc := congrArg Polynomial.leadingCoeff hh'
        rw [hh_mon.leadingCoeff, Polynomial.leadingCoeff_mul, hg_mon.leadingCoeff, one_mul] at hlc
        exact hlc.symm
      have hh'_deg : h'.natDegree = m * p := by
        have hd := congrArg Polynomial.natDegree hh'
        rw [hh_deg, Polynomial.natDegree_mul hg_mon.ne_zero hh'_ne, hg_deg, Nat.succ_mul] at hd
        omega
      obtain ⟨fs', hfs'_eq, hfs'_spec⟩ := ih h' hh'_mon (dvd_trans ⟨g, by rw [hh', mul_comm]⟩ hh_dvd) hh'_deg
      refine ⟨Fin.cons g fs', ?_, ?_⟩
      · rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [← hfs'_eq, ← hh']
      · intro j
        refine Fin.cases ?_ ?_ j
        · simpa using ⟨hg_mon, hg_irr, hg_deg⟩
        · intro k; simpa using hfs'_spec k
  obtain ⟨fs, hfs_eq, hfs_spec⟩ := hfac_div p f hf_monic (dvd_refl f) (by rw [hf_deg, sq])
  exact ⟨hnoroot, fs, hfs_eq, hfs_spec⟩

/-- **Exercise 16.6 (iv)** (§16.3, printed p. 127 / PDF p. 135; see `QUEUE.md` Flags 6–7):
1. For *any* `p` roots `α₁, ..., α_p ∈ L` of `f₁` (where `f₁ ∣ x^{p²} - θ` and `θ ≠ 0`),
   `α₁ ... α_p = ω * β` where `ω^{p²} = 1` (`ω` is a `p²`th root of unity) and `β^p = θ`.
2. Taking the `p` roots of monic degree-`p` `f₁` (`f₁.map = ∏ (X - C (α i))`) gives
   `ω * β = α₁ ... α_p = -f₁(0) ∈ K`; since `Φ_{p²}` splits over `K` by `(i)`, `ω ∈ Kˣ`, whence
   `β ∈ K` with `β^p = θ`, contradicting `(ii)` (`Irreducible (x^p - θ)`). -/
theorem exercise_16_6_iv {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L] {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hdeg : Module.finrank K L = p) (hchar : ringChar K ≠ p) {θ : K}
    (hirr : Irreducible (Polynomial.X ^ p - Polynomial.C θ : K[X]))
    {f₁ : K[X]} (hf₁_mon : f₁.Monic) (hf₁_deg : f₁.natDegree = p)
    (hf₁_dvd : f₁ ∣ Polynomial.X ^ (p ^ 2) - Polynomial.C θ) :
    (∀ α : Fin p → L, (∀ i : Fin p, Polynomial.aeval (α i) f₁ = 0) →
      ∃ (ω β : L), ω ^ (p ^ 2) = 1 ∧ β ^ p = algebraMap K L θ ∧
        ∏ i : Fin p, α i = ω * β) ∧
    False := by
  have hθ_ne : θ ≠ 0 := by
    intro h0; subst h0
    have hroot : (Polynomial.X ^ p - Polynomial.C (0 : K)).eval 0 = 0 := by
      simp [zero_pow hp.ne_zero]
    exact (theorem_16_2_part1_unconditional hp (0 : K) hchar).elim
      (fun h => h.2 ⟨0, hroot⟩) (fun h => h.2 hirr)
  have hpart_prod : ∀ α : Fin p → L, (∀ i : Fin p, Polynomial.aeval (α i) f₁ = 0) →
      ∃ (ω β : L), ω ^ (p ^ 2) = 1 ∧ β ^ p = algebraMap K L θ ∧
        ∏ i : Fin p, α i = ω * β := by
    intro α hα
    have hα_pow : ∀ i : Fin p, (α i) ^ (p ^ 2) = algebraMap K L θ := by
      intro i
      rcases hf₁_dvd with ⟨h, hh⟩
      have hev : Polynomial.aeval (α i) (Polynomial.X ^ (p ^ 2) - Polynomial.C θ) = 0 := by
        rw [hh, map_mul, hα i, zero_mul]
      simpa [sub_eq_zero] using hev
    let i₀ : Fin p := ⟨0, hp.pos⟩
    have hα₀_ne : α i₀ ≠ 0 := by
      intro h0
      have h1 := hα_pow i₀
      rw [h0, zero_pow (pow_ne_zero 2 hp.ne_zero)] at h1
      exact hθ_ne ((algebraMap K L).injective (h1.symm.trans (map_zero _).symm))
    let ωi : Fin p → L := fun i => α i * (α i₀)⁻¹
    let ω : L := ∏ i : Fin p, ωi i
    let β : L := (α i₀) ^ p
    refine ⟨ω, β, ?_, ?_, ?_⟩
    · simp only [ω]
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      simp only [ωi, mul_pow, inv_pow, hα_pow i, hα_pow i₀,
        mul_inv_cancel₀ ((map_ne_zero (algebraMap K L)).mpr hθ_ne)]
    · simp only [β, ← pow_mul, ← sq, hα_pow i₀]
    · calc ∏ i : Fin p, α i
          = ∏ i : Fin p, (ωi i * α i₀) :=
            Finset.prod_congr rfl fun i _ => by
              simp only [ωi, mul_assoc, inv_mul_cancel₀ hα₀_ne, mul_one]
        _ = (∏ i : Fin p, ωi i) * (∏ _ : Fin p, α i₀) := Finset.prod_mul_distrib
        _ = ω * β := by simp [ω, β, Finset.prod_const]
  refine ⟨hpart_prod, ?_⟩
  -- Derive the contradiction using the p roots of monic f₁ over algebraically closed L
  have hf₁L_splits : (f₁.map (algebraMap K L)).Splits := IsAlgClosed.splits _
  have hf₁L_mon : (f₁.map (algebraMap K L)).Monic := hf₁_mon.map _
  have hcard_r : (f₁.map (algebraMap K L)).roots.card = p := by
    rw [← Polynomial.Splits.natDegree_eq_card_roots hf₁L_splits,
      Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hf₁_deg]
  let rs := (f₁.map (algebraMap K L)).roots
  have hprod_eq_eval : rs.prod = (-1 : L) ^ p * algebraMap K L (f₁.eval 0) := by
    have hev0 := hf₁L_splits.eval_eq_prod_roots_of_monic hf₁L_mon 0
    have hmap_ev : (f₁.map (algebraMap K L)).eval 0 = algebraMap K L (f₁.eval 0) := by
      simp [Polynomial.eval_map, Polynomial.eval₂_at_zero, ← Polynomial.coeff_zero_eq_eval_zero]
    rw [hmap_ev] at hev0
    have hprod_neg : (rs.map (fun r => (0 : L) - r)).prod = (-1 : L) ^ p * rs.prod := by
      have hfn : (fun r : L => (0 : L) - r) = fun r : L => (-1 : L) * r := by ext r; ring
      rw [hfn, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
        Multiset.map_id', hcard_r]
    rw [hprod_neg] at hev0
    calc rs.prod = (-1 : L) ^ p * ((-1 : L) ^ p * rs.prod) := by
          rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
      _ = (-1 : L) ^ p * algebraMap K L (f₁.eval 0) := by rw [← hev0]
  -- Extract Fin p indexing of the multiset rs
  obtain ⟨l, hl⟩ := Quotient.exists_rep rs
  have hl_len : l.length = p := by
    have h1 := congrArg Multiset.card hl
    change l.length = rs.card at h1
    rw [h1, hcard_r]
  let α : Fin p → L := fun i => l.get (i.cast hl_len.symm)
  have hα_roots : ∀ i : Fin p, Polynomial.aeval (α i) f₁ = 0 := by
    intro i
    have hmem : α i ∈ rs := by
      rw [← hl]; exact Multiset.mem_coe.mpr (List.get_mem l _)
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf₁_mon.ne_zero),
      Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hmem
    exact hmem
  have hα_prod : (∏ i : Fin p, α i) = rs.prod := by
    rw [← hl]
    change (∏ i : Fin p, l.get (i.cast hl_len.symm)) = (l : Multiset L).prod
    rw [Multiset.prod_coe]
    have h1 : (∏ i : Fin p, l.get (i.cast hl_len.symm)) = (∏ i : Fin l.length, l.get i) :=
      Fintype.prod_equiv (finCongr hl_len.symm) _ _ fun _ => rfl
    have hlist_prod : ∀ l' : List L, (∏ i : Fin l'.length, l'.get i) = l'.prod := by
      intro l'
      induction l' with
      | nil => simp
      | cons a t ih =>
        change (∏ i : Fin (t.length + 1), (a :: t).get i) = a * t.prod
        rw [Fin.prod_univ_succ]
        exact congrArg (a * ·) ih
    rw [h1, hlist_prod]
  obtain ⟨ω, β, hω_pow, hβ_pow, hprod_ωβ⟩ := hpart_prod α hα_roots
  obtain ⟨_, ⟨ζK, hζK⟩, _, _⟩ := exercise_16_6_i hp hp2 hdeg hchar
  have hζL : IsPrimitiveRoot (algebraMap K L ζK) (p ^ 2) :=
    hζK.map_of_injective (algebraMap K L).injective
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain ⟨k, _, hk⟩ := hζL.eq_pow_of_pow_eq_one hω_pow
  let ωK : K := ζK ^ k
  have hωK_eq : algebraMap K L ωK = ω := by simp [ωK, hk]
  have hωK_ne : ωK ≠ 0 := by
    intro h0
    have h1 : ω = 0 := by rw [← hωK_eq, h0, map_zero]
    rw [h1, zero_pow (pow_ne_zero 2 hp.ne_zero)] at hω_pow
    exact zero_ne_one hω_pow
  let βK : K := ωK⁻¹ * ((-1 : K) ^ p * f₁.eval 0)
  have hβK_eq : algebraMap K L βK = β := by
    have hω_ne : ω ≠ 0 := by
      rw [← hωK_eq]; exact (map_ne_zero (algebraMap K L)).mpr hωK_ne
    apply mul_left_cancel₀ hω_ne
    rw [← hprod_ωβ, hα_prod, hprod_eq_eval]
    simp only [βK, map_mul, map_inv₀, map_pow, map_neg, map_one, hωK_eq, ← mul_assoc,
      mul_inv_cancel₀ hω_ne, one_mul]
  have hβK_pow : βK ^ p = θ :=
    (algebraMap K L).injective (by rw [map_pow, hβK_eq, hβ_pow])
  have hroot_K : (Polynomial.X ^ p - Polynomial.C θ).eval βK = 0 := by simp [hβK_pow]
  exact (theorem_16_2_part1_unconditional hp θ hchar).elim
    (fun h => h.2 ⟨βK, hroot_K⟩) (fun h => h.2 hirr)

/-- **Exercise 16.6** (§16.3, printed p. 127 / PDF p. 135):
Bundles all four parts `(i)`–`(iv)` and the resulting impossibility `False` whenever
`[L : K] = p > 2` is an odd prime with `p ≠ char K` and `L` algebraically closed. -/
theorem exercise_16_6 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L] {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hdeg : Module.finrank K L = p) (hchar : ringChar K ≠ p) :
    False := by
  obtain ⟨θ, hirr, _⟩ := exercise_16_6_ii hp hp2 hdeg hchar
  obtain ⟨_, fs, hfs_eq, hfs_spec⟩ := exercise_16_6_iii hp hdeg hirr
  let i₀ : Fin p := ⟨0, hp.pos⟩
  obtain ⟨hmon, _, hdeg1⟩ := hfs_spec i₀
  have hdvd : fs i₀ ∣ Polynomial.X ^ (p ^ 2) - Polynomial.C θ := by
    rw [hfs_eq]
    exact Finset.dvd_prod_of_mem fs (Finset.mem_univ i₀)
  exact (exercise_16_6_iv hp hp2 hdeg hchar hirr hmon hdeg1 hdvd).2

/-- **Exercise 16.7 (Part 1 — Existence of `M`)** (§16.3, printed p. 127 / PDF p. 135):
Suppose `[L : K] = 4`, `char K ≠ 2`, and `L` is algebraically closed. Then there exists an
intermediate field `M` between `K` and `L` such that `[L : M] = 2` and `Φ₄` splits over `M`. -/
theorem exercise_16_7_exists_M {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L]
    (hdeg : Module.finrank K L = 4) (hchar : ringChar K ≠ 2) :
    ∃ M : IntermediateField K L,
      Module.finrank M L = 2 ∧
      GarlingSplitsOver M M (Polynomial.cyclotomic 4 M) := by
  have hcharL : ringChar L = ringChar K :=
    ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K))
  have hndvd4 : ¬ (ringChar K ∣ 4) := by
    intro hd
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
    · have h2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow (show ringChar K ∣ 2 ^ 2 by exact hd)
      exact hchar ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · rw [h0] at hd; exact absurd (zero_dvd_iff.mp hd) (by decide)
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank (hdeg.symm ▸ hndvd4)
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  obtain ⟨im, him⟩ := exists_isPrimitiveRoot_of_isAlgClosed (L := L) (n := 4) (hcharL.symm ▸ hndvd4)
  have him_sq : im ^ 2 = -1 := by
    have h4 : im ^ 4 = 1 := him.pow_eq_one
    have hne2 : im ^ 2 ≠ 1 := fun h2 =>
      absurd (Nat.le_of_dvd (by decide) (him.dvd_of_pow_eq_one 2 h2)) (by decide)
    have hfac : (im ^ 2 - 1) * (im ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hne2
    · linear_combination h2
  by_cases him_in_K : im ∈ (⊥ : IntermediateField K L)
  · -- Case 1: i ∈ K; take M = fixedField H for a subgroup H ≤ Gal(L/K) of order 2
    have hcardG : Nat.card (L ≃ₐ[K] L) = 4 := by
      rw [IsGalois.card_aut_eq_finrank K L, hdeg]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨H, hH_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := L ≃ₐ[K] L) 2 (n := 1)
      (by rw [pow_one, hcardG]; decide)
    let M : IntermediateField K L := IntermediateField.fixedField H
    refine ⟨M, ?_, ?_⟩
    · rw [IntermediateField.finrank_fixedField_eq_card, hH_card, pow_one]
    · let imM : M := ⟨im, (bot_le : (⊥ : IntermediateField K L) ≤ M) him_in_K⟩
      have himM : IsPrimitiveRoot imM 4 := by
        rw [IsPrimitiveRoot.iff_def]
        refine ⟨by ext; exact him.pow_eq_one,
          fun l hl => him.dvd_of_pow_eq_one l (congrArg Subtype.val hl)⟩
      exact garlingSplitsOver_cyclotomic_of_isPrimitiveRoot (by decide) himM
  · -- Case 2: i ∉ K; take M = K⟮im⟯, which has [M : K] = 2 hence [L : M] = 2
    let M : IntermediateField K L := K⟮im⟯
    have him_int : IsIntegral K im := Algebra.IsIntegral.isIntegral im
    have hdvd_x2 : minpoly K im ∣ (Polynomial.X ^ 2 + 1 : K[X]) := by
      refine minpoly.dvd K im ?_
      simp [him_sq]
    have hdeg_le2 : (minpoly K im).natDegree ≤ 2 := by
      have hne : (Polynomial.X ^ 2 + 1 : K[X]) ≠ 0 := by
        simpa using (Polynomial.monic_X_pow_add_C (1 : K) (by decide)).ne_zero
      have h1 := Polynomial.natDegree_le_of_dvd hdvd_x2 hne
      simpa using h1
    have hdeg_gt1 : 1 < Module.finrank K M := by
      have hpos : 0 < Module.finrank K M := Module.finrank_pos
      by_contra hle
      have h1 : Module.finrank K M = 1 := by omega
      have hbot : (⊥ : IntermediateField K L) = M :=
        IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, h1])
      exact him_in_K (hbot ▸ IntermediateField.mem_adjoin_simple_self K im)
    have hfinM : Module.finrank K M = 2 := by
      have hle : Module.finrank K M ≤ 2 := by
        rw [IntermediateField.adjoin.finrank him_int]; exact hdeg_le2
      omega
    have hfinML : Module.finrank M L = 2 := by
      have hm := Module.finrank_mul_finrank K M L
      rw [hfinM, hdeg] at hm; omega
    let imM : M := ⟨im, IntermediateField.mem_adjoin_simple_self K im⟩
    have himM : IsPrimitiveRoot imM 4 := by
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨by ext; exact him.pow_eq_one,
        fun l hl => him.dvd_of_pow_eq_one l (congrArg Subtype.val hl)⟩
    exact ⟨M, hfinML, garlingSplitsOver_cyclotomic_of_isPrimitiveRoot (by decide) himM⟩

/-- **Exercise 16.7 (Part 2 — Degree-2 contradiction when `Φ₄` splits over `M`)** (§16.3, p. 127):
If `[L : M] = 2`, `char M ≠ 2`, `L` is algebraically closed, and `Φ₄` splits over `M`, then `False`.
*(Reused directly in both `Exercise 16.7` and `Exercise 16.8`!)* -/
theorem exercise_16_7_contradiction {M : Type u} {L : Type v} [Field M] [Field L] [Algebra M L]
    [FiniteDimensional M L] [IsAlgClosed L]
    (hdeg : Module.finrank M L = 2) (hchar : ringChar M ≠ 2)
    (hsplit4 : GarlingSplitsOver M M (Polynomial.cyclotomic 4 M)) :
    False := by
  have h2M_ne : (2 : M) ≠ 0 := by
    intro h20
    have hd : ringChar M ∣ 2 := (ringChar.spec M 2).mp h20
    rcases CharP.char_is_prime_or_zero M (ringChar M) with hp | h0
    · exact hchar ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    · rw [h0] at hd; exact absurd (zero_dvd_iff.mp hd) (by decide)
  have hndvd2 : ¬ (ringChar M ∣ 2) := fun hd => h2M_ne ((ringChar.spec M 2).mpr hd)
  -- Extract i ∈ M with i^2 = -1 from splitting of Φ₄ = X^2 + 1 over M
  have hΦ4_eq : Polynomial.cyclotomic 4 M = Polynomial.X ^ 2 + 1 := by
    have hmul := Polynomial.prod_cyclotomic_eq_X_pow_sub_one (by decide : 0 < 4) M
    have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
    rw [hdiv] at hmul
    simp only [Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
      Finset.prod_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)),
      Finset.prod_singleton, Polynomial.cyclotomic_one, Polynomial.cyclotomic_two] at hmul
    have h12_ne : ((Polynomial.X - 1) * (Polynomial.X + 1) : M[X]) ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero 1) (by simpa using Polynomial.X_sub_C_ne_zero (-1 : M))
    apply mul_left_cancel₀ h12_ne
    calc ((Polynomial.X - 1) * (Polynomial.X + 1)) * Polynomial.cyclotomic 4 M
        = (Polynomial.X - 1) * ((Polynomial.X + 1) * Polynomial.cyclotomic 4 M) := by ring
      _ = Polynomial.X ^ 4 - 1 := hmul
      _ = ((Polynomial.X - 1) * (Polynomial.X + 1)) * (Polynomial.X ^ 2 + 1) := by ring
  have hsp_ml : (Polynomial.X ^ 2 + 1 : M[X]).Splits := by
    rw [← hΦ4_eq]
    have h := (garlingSplitsOver_iff_splits M M _).mp hsplit4
    rwa [Algebra.algebraMap_self, Polynomial.map_id] at h
  have hne_r : (Polynomial.X ^ 2 + 1 : M[X]).roots ≠ 0 := by
    intro h0
    have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
    rw [h0, Multiset.card_zero] at hc
    have hd : (Polynomial.X ^ 2 + 1 : M[X]).natDegree = 2 := by simp
    omega
  obtain ⟨imM, himM⟩ := Multiset.exists_mem_of_ne_zero hne_r
  have himM_sq : imM ^ 2 = -1 := by
    have hne : (Polynomial.X ^ 2 + 1 : M[X]) ≠ 0 := by
      simpa using (Polynomial.monic_X_pow_add_C (1 : M) (by decide)).ne_zero
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def] at himM
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at himM
    linear_combination himM
  -- L : M is cyclic of degree 2 and -1 ∈ M is a primitive 2nd root of unity
  have hgal : IsGarlingGaloisExtension M L :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank (hdeg.symm ▸ hndvd2)
  have _ : IsGalois M L := (isGarlingGaloisExtension_iff M L).mp hgal |>.2
  have hcardG : Nat.card (L ≃ₐ[M] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank M L, hdeg]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsGarlingCyclicExtension M L := ⟨hgal, isCyclic_of_prime_card hcardG⟩
  have hm1_prim : IsPrimitiveRoot (-1 : M) 2 := by
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨by ring, fun l hl => ?_⟩
    by_contra hndvd
    have hodd : l % 2 = 1 := by omega
    have hpow : (-1 : M) ^ (l % 2) = 1 := by
      have hdiv := Nat.div_add_mod l 2
      have h1 : (-1 : M) ^ (2 * (l / 2) + l % 2) = 1 := hdiv.symm ▸ hl
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul] at h1
      exact h1
    rw [hodd, pow_one] at hpow
    exact h2M_ne (by linear_combination -hpow)
  obtain ⟨θ, hirr, hsf, hgen⟩ := theorem_16_4 hcyc hdeg hndvd2 hm1_prim
  -- Let β ∈ L satisfy β^2 = θ, and α ∈ L satisfy α^2 = β; write α = a + b * β with a, b ∈ M
  have hdeg_β : (Polynomial.X ^ 2 - Polynomial.C (algebraMap M L θ) : L[X]).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (Polynomial.monic_X_pow_sub_C _ (by decide)).ne_zero,
      Polynomial.natDegree_X_pow_sub_C]
    decide
  obtain ⟨β, hβ_r⟩ := IsAlgClosed.exists_root _ hdeg_β
  have hβ_pow : β ^ 2 = algebraMap M L θ := by simpa [Polynomial.IsRoot.def, sub_eq_zero] using hβ_r
  have hβ_aev : Polynomial.aeval β (Polynomial.X ^ 2 - Polynomial.C θ) = 0 := by
    simp [hβ_pow]
  have hMβ_top : M⟮β⟯ = ⊤ := hgen β hβ_aev
  have hdeg_α : (Polynomial.X ^ 2 - Polynomial.C β : L[X]).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (Polynomial.monic_X_pow_sub_C _ (by decide)).ne_zero,
      Polynomial.natDegree_X_pow_sub_C]
    decide
  obtain ⟨α, hα_r⟩ := IsAlgClosed.exists_root _ hdeg_α
  have hα_pow : α ^ 2 = β := by simpa [Polynomial.IsRoot.def, sub_eq_zero] using hα_r
  -- Express α in basis {1, β} of L = M(β) via PowerBasis
  let pb : PowerBasis M M⟮β⟯ := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral β)
  have hmin_β : minpoly M β = Polynomial.X ^ 2 - Polynomial.C θ :=
    (minpoly.eq_of_irreducible_of_monic hirr hβ_aev (Polynomial.monic_X_pow_sub_C θ (by decide))).symm
  have hpb_dim : pb.dim = 2 := by
    rw [IntermediateField.adjoin.powerBasis_dim, hmin_β, Polynomial.natDegree_X_pow_sub_C]
  have hα_mem : α ∈ M⟮β⟯ := hMβ_top.symm ▸ IntermediateField.mem_top
  let c := pb.basis.repr ⟨α, hα_mem⟩
  let a : M := c ⟨0, by omega⟩
  let b : M := c ⟨1, by omega⟩
  have hα_lin : α = algebraMap M L a + algebraMap M L b * β := by
    have hsum := pb.basis.sum_repr ⟨α, hα_mem⟩
    have hval := congrArg Subtype.val hsum
    rw [AddSubmonoidClass.coe_finsetSum] at hval
    have hterm : ∀ i : Fin pb.dim,
        (((pb.basis.repr ⟨α, hα_mem⟩) i • pb.basis i : M⟮β⟯) : L) =
          algebraMap M L (c i) * (pb.gen : L) ^ (i : ℕ) := by
      intro i
      rw [PowerBasis.coe_basis, Algebra.smul_def]
      simp [c]
    simp only [hterm] at hval
    have hgen_eq : (pb.gen : L) = β := by rw [IntermediateField.adjoin.powerBasis_gen]; rfl
    rw [← hval]
    have hsum2 : (∑ i : Fin pb.dim, algebraMap M L (c i) * (pb.gen : L) ^ (i : ℕ)) =
        ∑ i : Fin 2, algebraMap M L (c (i.cast hpb_dim.symm)) * (pb.gen : L) ^ (i : ℕ) :=
      Fintype.sum_equiv (finCongr hpb_dim) _ _ fun _ => rfl
    rw [hsum2, Fin.sum_univ_two, hgen_eq]
    simp [a, b]
    rfl
  -- (a + b β)^2 = β ⇒ (a^2 + b^2 θ) + (2ab - 1) β = 0
  have hβ_not_M : β ∉ Set.range (algebraMap M L) := by
    rintro ⟨r, hr⟩
    have hroot : (Polynomial.X ^ 2 - Polynomial.C θ).eval r = 0 := by
      have hr2 : r ^ 2 = θ := (algebraMap M L).injective (by rw [map_pow, hr, hβ_pow])
      simp [hr2]
    exact (theorem_16_2_part1_unconditional Nat.prime_two θ hchar).elim
      (fun h => h.2 ⟨r, hroot⟩) (fun h => h.2 hirr)
  have hsq_eq : algebraMap M L (a ^ 2 + b ^ 2 * θ) + algebraMap M L (2 * a * b - 1) * β = 0 := by
    have h1 : (algebraMap M L a + algebraMap M L b * β) ^ 2 = β := hα_lin ▸ hα_pow
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
    linear_combination h1 - algebraMap M L b ^ 2 * hβ_pow
  have hcoeff1 : 2 * a * b - 1 = 0 := by
    by_contra hne
    have hneL : algebraMap M L (2 * a * b - 1) ≠ 0 := (map_ne_zero (algebraMap M L)).mpr hne
    have hβ_eq : β = algebraMap M L (-(a ^ 2 + b ^ 2 * θ) / (2 * a * b - 1)) := by
      simp only [map_div₀, map_neg]
      apply mul_left_cancel₀ hneL
      rw [mul_div_cancel₀ _ hneL]
      linear_combination hsq_eq
    exact hβ_not_M ⟨_, hβ_eq.symm⟩
  have hcoeff0 : a ^ 2 + b ^ 2 * θ = 0 := by
    rw [hcoeff1, map_zero, zero_mul, add_zero] at hsq_eq
    exact (algebraMap M L).injective (hsq_eq.trans (map_zero _).symm)
  have hb_ne : b ≠ 0 := by
    intro hb0; rw [hb0, mul_zero, zero_sub] at hcoeff1
    exact neg_ne_zero.mpr one_ne_zero hcoeff1
  let r : M := imM * (a / b)
  have hr_sq : r ^ 2 = θ := by
    have h1 : b ^ 2 * (r ^ 2 - θ) = 0 := by
      calc b ^ 2 * ((imM * (a / b)) ^ 2 - θ)
          = imM ^ 2 * a ^ 2 - b ^ 2 * θ := by field_simp
        _ = (-1) * a ^ 2 - b ^ 2 * θ := by rw [himM_sq]
        _ = -(a ^ 2 + b ^ 2 * θ) := by ring
        _ = 0 := by rw [hcoeff0, neg_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hb_ne))
  have hroot_θ : (Polynomial.X ^ 2 - Polynomial.C θ).eval r = 0 := by simp [hr_sq]
  exact (theorem_16_2_part1_unconditional Nat.prime_two θ hchar).elim
    (fun h => h.2 ⟨r, hroot_θ⟩) (fun h => h.2 hirr)

/-- **Exercise 16.7** (§16.3, printed p. 127 / PDF p. 135):
*"Suppose that `[L : K] = 4`, that `char K ≠ 2` and that `L` is algebraically closed. Show that
there exists an intermediate field `M` such that `[L : M] = 2` and such that `Φ₄` splits over `M`.
Show that this leads to a contradiction."* -/
theorem exercise_16_7 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L]
    (hdeg : Module.finrank K L = 4) (hchar : ringChar K ≠ 2) :
    False := by
  obtain ⟨M, hML, hsp4⟩ := exercise_16_7_exists_M hdeg hchar
  have _ : FiniteDimensional M L := Module.Finite.right K M L
  have hcharM : ringChar M ≠ 2 := by
    have hEq : ringChar M = ringChar K :=
      ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K M).injective (ringChar K))
    rwa [hEq]
  exact exercise_16_7_contradiction hML hcharM hsp4

/-- **Exercise 16.8** (§16.3, printed p. 127 / PDF p. 135):
*"Suppose that `char K = 0`, that `1 < [L : K] < ∞` and that `L` is algebraically closed. Show that
`[L : K] = 2` and that `L : K` is a splitting field extension for `x² + 1`."* -/
theorem exercise_16_8 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAlgClosed L]
    (hchar : ringChar K = 0) (hdeg_gt1 : 1 < Module.finrank K L) :
    Module.finrank K L = 2 ∧
    extDegree K L = 2 ∧
    IsGarlingSplittingFieldExtension K L (Polynomial.X ^ 2 + 1) := by
  have hndvd : ¬ (ringChar K ∣ Module.finrank K L) := by
    rw [hchar, zero_dvd_iff]; omega
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank hndvd
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hcardG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L :=
    IsGalois.card_aut_eq_finrank K L
  -- No odd prime p divides |Gal(L/K)| (by Cauchy/Sylow + Exercise 16.6)
  have hno_odd : ∀ p : ℕ, Nat.Prime p → 2 < p → ¬ (p ∣ Module.finrank K L) := by
    intro p hp hp2 hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨H, hH_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := L ≃ₐ[K] L) p (n := 1)
      (by rwa [pow_one, hcardG])
    let M := IntermediateField.fixedField H
    have _ : FiniteDimensional M L := Module.Finite.right K M L
    have hML : Module.finrank M L = p := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH_card, pow_one]
    have hcharM : ringChar M ≠ p := by
      have hEq : ringChar M = ringChar K :=
        ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K M).injective (ringChar K))
      rw [hEq, hchar]; exact hp.ne_zero.symm
    exact exercise_16_6 hp hp2 hML hcharM
  -- 4 does not divide |Gal(L/K)| (by Sylow + Exercise 16.7)
  have hno_4 : ¬ (4 ∣ Module.finrank K L) := by
    intro hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨H, hH_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := L ≃ₐ[K] L) 2 (n := 2)
      (by rwa [hcardG])
    let M := IntermediateField.fixedField H
    have _ : FiniteDimensional M L := Module.Finite.right K M L
    have hML : Module.finrank M L = 4 := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH_card]; norm_num
    have hcharM : ringChar M ≠ 2 := by
      have hEq : ringChar M = ringChar K :=
        ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K M).injective (ringChar K))
      rw [hEq, hchar]; decide
    exact exercise_16_7 hML hcharM
  -- Deduce [L : K] = 2
  have hfin2 : Module.finrank K L = 2 := by
    let n := Module.finrank K L
    have hn_gt1 : 1 < n := hdeg_gt1
    have h2_dvd : 2 ∣ n := by
      let p := n.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      rcases eq_or_lt_of_le hp.two_le with hp2 | hp_gt2
      · exact hp2 ▸ hpdvd
      · exact absurd hpdvd (hno_odd p hp hp_gt2)
    rcases h2_dvd with ⟨m, hm⟩
    change Module.finrank K L = 2 * m at hm
    have hm1 : m = 1 := by
      by_contra hne1
      have hm_gt1 : 1 < m := by omega
      let p := m.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have hpdvd_m : p ∣ m := Nat.minFac_dvd m
      rcases eq_or_lt_of_le hp.two_le with hp2 | hp_gt2
      · rw [← hp2] at hpdvd_m
        rcases hpdvd_m with ⟨k, rfl⟩
        exact hno_4 ⟨k, by rw [hm]; ring⟩
      · exact hno_odd p hp hp_gt2 (hpdvd_m.trans ⟨2, by rw [hm, mul_comm]⟩)
    rw [hm, hm1, mul_one]
  -- Show L : K is a splitting field extension for x^2 + 1
  have hcharL : ringChar L = 0 := by
    rw [ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)), hchar]
  obtain ⟨im, him⟩ := exists_isPrimitiveRoot_of_isAlgClosed (L := L) (n := 4)
    (by rw [hcharL]; simp)
  have him_sq : im ^ 2 = -1 := by
    have h4 : im ^ 4 = 1 := him.pow_eq_one
    have hne2 : im ^ 2 ≠ 1 := fun h2 =>
      absurd (Nat.le_of_dvd (by decide) (him.dvd_of_pow_eq_one 2 h2)) (by decide)
    have hfac : (im ^ 2 - 1) * (im ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hne2
    · linear_combination h2
  have him_not_K : im ∉ (⊥ : IntermediateField K L) := by
    intro hmem
    rcases IntermediateField.mem_bot.mp hmem with ⟨imK, himK_eq⟩
    have himK : IsPrimitiveRoot imK 4 := by
      rw [IsPrimitiveRoot.iff_def]
      refine ⟨(algebraMap K L).injective (by rw [map_pow, himK_eq, him.pow_eq_one, map_one]),
        fun l hl => him.dvd_of_pow_eq_one l (by rw [← himK_eq, ← map_pow, hl, map_one])⟩
    exact exercise_16_7_contradiction hfin2 (by rw [hchar]; decide)
      (garlingSplitsOver_cyclotomic_of_isPrimitiveRoot (by decide) himK)
  have hKim_top : K⟮im⟯ = ⊤ := by
    have hgt1 : 1 < Module.finrank K K⟮im⟯ := by
      have hpos : 0 < Module.finrank K K⟮im⟯ := Module.finrank_pos
      by_contra hle
      have h1 : Module.finrank K K⟮im⟯ = 1 := by omega
      have hbot : (⊥ : IntermediateField K L) = K⟮im⟯ :=
        IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, h1])
      exact him_not_K (hbot ▸ IntermediateField.mem_adjoin_simple_self K im)
    have hle2 : Module.finrank K K⟮im⟯ ≤ 2 := by
      have hm := Module.finrank_mul_finrank K K⟮im⟯ L
      have hpos2 : 0 < Module.finrank K⟮im⟯ L := Module.finrank_pos
      rw [hfin2] at hm; nlinarith
    exact IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfin2]; omega)
  have hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ 2 + 1) := by
    refine ⟨⟨2, 1, ![im, -im], ?_⟩, ?_⟩
    · rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_one]
      have hsub : (Polynomial.X - Polynomial.C im) * (Polynomial.X - Polynomial.C (-im)) =
          Polynomial.X ^ 2 - Polynomial.C (im ^ 2) := by
        rw [Polynomial.C_neg, map_pow]; ring
      rw [hsub, him_sq, map_neg, map_one, sub_neg_eq_add]
    · intro M hM hspM
      have hsp_ml := (garlingSplitsOver_iff_splits K M _).mp hspM
      have hne_r : ((Polynomial.X ^ 2 + 1 : K[X]).map (algebraMap K M)).roots ≠ 0 := by
        intro h0
        have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
        rw [h0, Multiset.card_zero, Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective] at hc
        have hd : (Polynomial.X ^ 2 + 1 : K[X]).natDegree = 2 := by simp
        omega
      obtain ⟨rM, hrM⟩ := Multiset.exists_mem_of_ne_zero hne_r
      have hne2 : (Polynomial.X ^ 2 + 1 : K[X]) ≠ 0 := by
        simpa using (Polynomial.monic_X_pow_add_C (1 : K) (by decide)).ne_zero
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne2), Polynomial.IsRoot.def,
        Polynomial.eval_map, ← Polynomial.aeval_def] at hrM
      have hrL_sq : (rM : L) ^ 2 = -1 := by
        have h1 : rM ^ 2 + 1 = 0 := by simpa using hrM
        have h2 := congrArg (algebraMap M L) h1
        simp only [map_add, map_pow, map_one, map_zero] at h2
        change (rM : L) ^ 2 + 1 = 0 at h2
        linear_combination h2
      have hfac : ((rM : L) - im) * ((rM : L) + im) = 0 := by linear_combination hrL_sq - him_sq
      have him_M : im ∈ M := by
        rcases mul_eq_zero.mp hfac with h1 | h2
        · have heq : (rM : L) = im := sub_eq_zero.mp h1
          exact heq ▸ rM.2
        · have heq : im = -(rM : L) := by linear_combination h2
          exact heq ▸ neg_mem rM.2
      have htop_le : (⊤ : IntermediateField K L) ≤ M := by
        rw [← hKim_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact him_M
      exact hM (le_antisymm le_top htop_le)
  exact ⟨hfin2, by rw [extDegree_eq_finrank K L, hfin2]; rfl, hsf⟩

/-- **Characteristic-`0` counterexample to unguarded `Exercise 16.9`** (`QUEUE.md` Flag 5):
When `p = 0` (`K = ℚ`, `char ℚ = 0`), `x^0 - x - α = 1 - x - α` has root `1 - α` (1 root, not `0`
roots) and cannot have a cyclic extension of degree `0`, confirming `Exercise 16.9` implicitly
assumes prime `p > 0` (matching the preceding prose sentence on p. 127 and §3.9 Theorem 3.16). -/
theorem exercise_16_9_char_zero_counterexample :
    ringChar ℚ = 0 ∧
    (Polynomial.X ^ 0 - Polynomial.X - Polynomial.C (0 : ℚ)).eval 1 = 0 ∧
    ¬ ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L),
      Module.finrank ℚ L = 0 := by
  refine ⟨ringChar.eq_zero, by simp, ?_⟩
  rintro ⟨L, _, _, _, h0⟩
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  omega

/-- Helper: in characteristic `p` (prime), every natural cast `(j : R)` satisfies `(j : R) ^ p = j`. -/
theorem natCast_pow_char {R : Type*} [CommRing R] {p : ℕ} (hp : Nat.Prime p) [CharP R p]
    (j : ℕ) : (j : R) ^ p = (j : R) := by
  have : Fact p.Prime := ⟨hp⟩
  induction j with
  | zero => simp [zero_pow hp.ne_zero]
  | succ j ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]

/-- **Exercise 16.9** (§16.3, printed p. 127 / PDF p. 135; prime `p` made explicit per `QUEUE.md`
Flag 5):
*"Suppose that `char K = p` [prime], that `f = x^p - x - α ∈ K[x]` and that `L : K` is a splitting
field extension for `f`. Show that if `β` is a root of `f` then the roots of `f` are
`β, β + 1, ..., β + p - 1`. Show that either `f` splits over `K` or `f` is irreducible over `K`
and `L : K` is cyclic of degree `p`."* -/
theorem exercise_16_9 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar K = p) (α : K)
    (hsf : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ p - Polynomial.X - Polynomial.C α)) :
    let f : K[X] := Polynomial.X ^ p - Polynomial.X - Polynomial.C α
    (∀ β : L, Polynomial.aeval β f = 0 →
      Function.Injective (fun j : Fin p => β + (j : L)) ∧
      (∀ j : Fin p, Polynomial.aeval (β + (j : L)) f = 0) ∧
      f.map (algebraMap K L) = ∏ j : Fin p, (Polynomial.X - Polynomial.C (β + (j : L))) ∧
      (f.map (algebraMap K L)).roots.toFinset = Finset.univ.image (fun j : Fin p => β + (j : L))) ∧
    Xor (GarlingSplitsOver K K f)
      (Irreducible f ∧ IsGarlingCyclicExtension K L ∧ Module.finrank K L = p ∧ extDegree K L = p) := by
  intro f
  have _ : CharP K p := hchar ▸ ringChar.charP K
  have _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : Fact p.Prime := ⟨hp⟩
  have hf_deg : f.natDegree = p := by
    have h1 : (Polynomial.X ^ p - Polynomial.X : K[X]).natDegree = p := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow p
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp.one_lt
    rw [show f = (Polynomial.X ^ p - Polynomial.X) - Polynomial.C α from rfl,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact h1
    · rw [Polynomial.natDegree_C, h1]; exact hp.pos
  have hf_monic : f.Monic := by
    have h1 : (Polynomial.X ^ p - Polynomial.X : K[X]).Monic := by
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow p) ?_
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast hp.one_lt
    refine h1.sub_of_left ?_
    rw [Polynomial.degree_eq_natDegree h1.ne_zero]
    have hd1 : (Polynomial.X ^ p - Polynomial.X : K[X]).natDegree = p := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow p
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp.one_lt
    rw [hd1]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hp.pos)
  have hf_deriv : f.derivative = -1 := by
    simp [f, Polynomial.derivative_X_pow, CharP.cast_eq_zero]
  have hf_sep : f.Separable := by
    rw [Polynomial.Separable, hf_deriv]
    exact isCoprime_one_right.neg_right
  have hf_gsep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_splittingField hf_monic.ne_zero hsf hf_gsep
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  -- Part 1: Root characterization
  have hpart1 : ∀ β : L, Polynomial.aeval β f = 0 →
      Function.Injective (fun j : Fin p => β + (j : L)) ∧
      (∀ j : Fin p, Polynomial.aeval (β + (j : L)) f = 0) ∧
      f.map (algebraMap K L) = ∏ j : Fin p, (Polynomial.X - Polynomial.C (β + (j : L))) ∧
      (f.map (algebraMap K L)).roots.toFinset = Finset.univ.image (fun j : Fin p => β + (j : L)) := by
    intro β hβ
    have hβ_eq : β ^ p - β = algebraMap K L α := by
      simpa [f, sub_eq_zero] using hβ
    have hinj : Function.Injective (fun j : Fin p => β + (j : L)) := by
      intro a b hab
      have hcast : ((a : ℕ) : L) = ((b : ℕ) : L) := add_left_cancel hab
      rcases le_total (a : ℕ) (b : ℕ) with hle | hle
      · have hsub0 : (((b : ℕ) - (a : ℕ) : ℕ) : L) = 0 := by
          rw [Nat.cast_sub hle, hcast, sub_self]
        have hdvd : p ∣ (b : ℕ) - (a : ℕ) := (CharP.cast_eq_zero_iff L p _).mp hsub0
        have hlt : (b : ℕ) - (a : ℕ) < p := by omega
        have h0 : (b : ℕ) - (a : ℕ) = 0 := by
          by_contra hne
          exact not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) hlt
        exact Fin.ext (by omega)
      · have hsub0 : (((a : ℕ) - (b : ℕ) : ℕ) : L) = 0 := by
          rw [Nat.cast_sub hle, hcast, sub_self]
        have hdvd : p ∣ (a : ℕ) - (b : ℕ) := (CharP.cast_eq_zero_iff L p _).mp hsub0
        have hlt : (a : ℕ) - (b : ℕ) < p := by omega
        have h0 : (a : ℕ) - (b : ℕ) = 0 := by
          by_contra hne
          exact not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) hlt
        exact Fin.ext (by omega)
    have hroots : ∀ j : Fin p, Polynomial.aeval (β + (j : L)) f = 0 := by
      intro j
      simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [add_pow_char, natCast_pow_char hp (j : ℕ)]
      linear_combination hβ_eq
    have hfac : f.map (algebraMap K L) = ∏ j : Fin p, (Polynomial.X - Polynomial.C (β + (j : L))) := by
      let S : Finset L := Finset.univ.image (fun j : Fin p => β + (j : L))
      have hdvd : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) ∣ f.map (algebraMap K L) := by
        refine Finset.prod_dvd_of_coprime
          (fun x _ y _ hxy => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy) ?_
        intro x hx
        rw [Finset.mem_image] at hx
        rcases hx with ⟨j, _, rfl⟩
        rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map,
          ← Polynomial.aeval_def]
        exact hroots j
      have hprodS : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) =
          ∏ j : Fin p, (Polynomial.X - Polynomial.C (β + (j : L))) :=
        Finset.prod_image fun a _ b _ hab => hinj hab
      rw [hprodS] at hdvd
      have hmonR : (∏ j : Fin p, (Polynomial.X - Polynomial.C (β + (j : L)))).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
      exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonR (hf_monic.map _) hdvd (by
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hf_deg,
          Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero _)]
        simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one, le_refl])
    have hfinset : (f.map (algebraMap K L)).roots.toFinset =
        Finset.univ.image (fun j : Fin p => β + (j : L)) := by
      ext x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero),
        Polynomial.IsRoot.def, hfac, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
      simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero, Finset.mem_image, eq_comm]
    exact ⟨hinj, hroots, hfac, hfinset⟩
  -- Part 2: Dichotomy (splits over K) ⊻ (irreducible & cyclic of degree p)
  have hnot_both : ¬ (GarlingSplitsOver K K f ∧ Irreducible f) := by
    rintro ⟨hspK, hirr⟩
    have hsp_ml := (garlingSplitsOver_iff_splits K K f).mp hspK
    rw [Algebra.algebraMap_self, Polynomial.map_id] at hsp_ml
    have hne_r : f.roots ≠ 0 := by
      intro h0
      have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
      rw [h0, Multiset.card_zero, hf_deg] at hc; exact hp.ne_zero hc
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne_r
    rw [Polynomial.mem_roots hf_monic.ne_zero, Polynomial.IsRoot.def] at hr
    obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    rcases hirr.isUnit_or_isUnit hq_fac with hu1 | hu2
    · rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero r),
        Polynomial.natDegree_X_sub_C] at hu1
      exact absurd hu1 (by decide)
    · have hq0 : q_fac ≠ 0 := fun h => by rw [h, mul_zero] at hq_fac; exact hf_monic.ne_zero hq_fac
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
      have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
      have hd := congrArg Polynomial.natDegree hq_fac
      rw [hf_deg, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0,
        Polynomial.natDegree_X_sub_C, hqd] at hd
      have := hp.two_le; omega
  refine ⟨hpart1, ?_⟩
  by_cases hspK : GarlingSplitsOver K K f
  · exact Or.inl ⟨hspK, fun h => hnot_both ⟨hspK, h.1⟩⟩
  · refine Or.inr ⟨?_, hspK⟩
    -- Pick a root β ∈ L of f
    have hspL := (garlingSplitsOver_iff_splits K L f).mp hsf.1
    have hne_r : (f.map (algebraMap K L)).roots ≠ 0 := by
      intro h0
      have hc := Polynomial.Splits.natDegree_eq_card_roots hspL
      rw [h0, Multiset.card_zero, Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
        hf_deg] at hc
      exact hp.ne_zero hc
    obtain ⟨β, hβ_mem⟩ := Multiset.exists_mem_of_ne_zero hne_r
    have hβ : Polynomial.aeval β f = 0 := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hβ_mem
      exact hβ_mem
    obtain ⟨hinj_r, hroots_r, hfac_r, _⟩ := hpart1 β hβ
    -- Show L = K⟮β⟯
    have hKβ_top : K⟮β⟯ = ⊤ := by
      by_contra hne
      refine hsf.2 K⟮β⟯ hne ⟨p, 1, fun j => ⟨β + (j : L), add_mem (IntermediateField.mem_adjoin_simple_self K β) (natCast_mem K⟮β⟯ (j : ℕ))⟩, ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap K⟮β⟯ L) (algebraMap K⟮β⟯ L).injective
      have hmc : (f.map (algebraMap K K⟮β⟯)).map (algebraMap K⟮β⟯ L) = f.map (algebraMap K L) := by
        rw [Polynomial.map_map]; rfl
      rw [hmc, hfac_r]
      simp only [map_one, one_mul, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun j _ => by simp
    -- Show β ∉ K (else f splits over K!)
    have hβ_not_K : β ∉ Set.range (algebraMap K L) := by
      rintro ⟨c, hc⟩
      apply hspK
      refine ⟨p, 1, fun j => c + (j : K), ?_⟩
      unfold GarlingSplitsExplicit
      apply Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective
      rw [Algebra.algebraMap_self, Polynomial.map_id, map_one, Polynomial.C_1, one_mul, hfac_r,
        Polynomial.map_prod]
      exact Finset.prod_congr rfl fun j _ => by simp [hc]
    have hfin_gt1 : 1 < Module.finrank K L := by
      have hpos : 0 < Module.finrank K L := Module.finrank_pos
      by_contra hle
      have h1 : Module.finrank K L = 1 := by omega
      have hbot : (⊥ : IntermediateField K L) = ⊤ :=
        IntermediateField.eq_of_le_of_finrank_eq bot_le
          (by rw [IntermediateField.finrank_bot, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, h1])
      exact hβ_not_K (IntermediateField.mem_bot.mp (hbot.symm ▸ IntermediateField.mem_top))
    -- Embed Additive (Gal(L/K)) injectively into ZMod p via σ(β) = β + c(σ)
    have hact : ∀ σ : L ≃ₐ[K] L, ∃ j : Fin p, σ β = β + (j : L) := by
      intro σ
      have hσβ : Polynomial.aeval (σ β) f = 0 := by
        rw [Polynomial.aeval_algHom_apply, hβ, map_zero]
      have hev := congrArg (Polynomial.eval (σ β)) hfac_r
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, hσβ, Polynomial.eval_prod, eq_comm,
        Finset.prod_eq_zero_iff] at hev
      rcases hev with ⟨j, _, hj⟩
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
      exact ⟨j, hj⟩
    let cFun : (L ≃ₐ[K] L) → Fin p := fun σ => (hact σ).choose
    have hcFun_spec : ∀ σ : L ≃ₐ[K] L, σ β = β + (cFun σ : L) := fun σ => (hact σ).choose_spec
    let φ : (L ≃ₐ[K] L) →* Multiplicative (ZMod p) :=
      { toFun := fun σ => Multiplicative.ofAdd ((cFun σ : ℕ) : ZMod p)
        map_one' := by
          have h1 := hcFun_spec 1
          simp only [AlgEquiv.one_apply] at h1
          have h0 : cFun 1 = ⟨0, hp.pos⟩ := hinj_r (by simpa using h1.symm)
          simp [h0]
        map_mul' := fun g₁ g₂ => by
          apply congrArg Multiplicative.ofAdd
          have h12 : (g₁ * g₂) β = β + ((cFun g₁ : ℕ) + (cFun g₂ : ℕ) : L) := by
            rw [AlgEquiv.mul_apply, hcFun_spec g₂, map_add, map_natCast, hcFun_spec g₁,
              add_assoc]
          have h12' := hcFun_spec (g₁ * g₂)
          have hcast_eq : ((cFun (g₁ * g₂) : ℕ) : L) = (((cFun g₁ : ℕ) + (cFun g₂ : ℕ) : ℕ) : L) := by
            have := add_left_cancel (h12'.symm.trans h12)
            simpa [Nat.cast_add] using this
          have hmod : (cFun (g₁ * g₂) : ℕ) ≡ (cFun g₁ : ℕ) + (cFun g₂ : ℕ) [MOD p] := by
            rcases le_total (cFun (g₁ * g₂) : ℕ) ((cFun g₁ : ℕ) + (cFun g₂ : ℕ)) with hle | hle
            · have h0 : ((((cFun g₁ : ℕ) + (cFun g₂ : ℕ)) - (cFun (g₁ * g₂) : ℕ) : ℕ) : L) = 0 := by
                rw [Nat.cast_sub hle, hcast_eq, sub_self]
              exact (Nat.modEq_iff_dvd' hle).mpr ((CharP.cast_eq_zero_iff L p _).mp h0)
            · have h0 : (((cFun (g₁ * g₂) : ℕ) - ((cFun g₁ : ℕ) + (cFun g₂ : ℕ)) : ℕ) : L) = 0 := by
                rw [Nat.cast_sub hle, hcast_eq, sub_self]
              exact ((Nat.modEq_iff_dvd' hle).mpr ((CharP.cast_eq_zero_iff L p _).mp h0)).symm
          change ((cFun (g₁ * g₂) : ℕ) : ZMod p) = ((cFun g₁ : ℕ) : ZMod p) + ((cFun g₂ : ℕ) : ZMod p)
          rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
          exact hmod }
    have hφ_inj : Function.Injective φ := by
      intro a b hab
      have hmod : (cFun a : ℕ) ≡ (cFun b : ℕ) [MOD p] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp (Multiplicative.ofAdd.injective hab)
      rw [Nat.ModEq, Nat.mod_eq_of_lt (cFun _).isLt, Nat.mod_eq_of_lt (cFun _).isLt] at hmod
      have hc_eq : cFun a = cFun b := Fin.ext hmod
      have hβ_eq : a β = b β := by
        rw [hcFun_spec, hcFun_spec, hc_eq]
      let Eeq : IntermediateField K L :=
        { (AlgHom.equalizer a.toAlgHom b.toAlgHom) with
          inv_mem' := fun {x} hx => by
            change a x⁻¹ = b x⁻¹
            rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv hx }
      have htop_le : (⊤ : IntermediateField K L) ≤ Eeq := by
        rw [← hKβ_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact hβ_eq
      ext x; exact htop_le IntermediateField.mem_top
    have hdvd_p : Nat.card (L ≃ₐ[K] L) ∣ p := by
      let H : Subgroup (Multiplicative (ZMod p)) := φ.range
      have hcardH : Nat.card H = Nat.card (L ≃ₐ[K] L) := by
        let e : (L ≃ₐ[K] L) ≃* H :=
          MulEquiv.ofBijective φ.rangeRestrict
            ⟨fun x y hxy => hφ_inj (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
        exact Nat.card_congr e.toEquiv.symm
      have hd := H.card_subgroup_dvd_card
      have hcz : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
      rwa [hcardH, Nat.card_congr Multiplicative.toAdd, hcz] at hd
    have hcardG : Nat.card (L ≃ₐ[K] L) = p := by
      rw [IsGalois.card_aut_eq_finrank K L] at hdvd_p ⊢
      rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hp_eq
      · omega
      · exact hp_eq
    have hfinL : Module.finrank K L = p := by
      rwa [IsGalois.card_aut_eq_finrank K L] at hcardG
    have hβ_int : IsIntegral K β := Algebra.IsIntegral.isIntegral β
    have hmin_eq : minpoly K β = f := by
      have hdeg_min : (minpoly K β).natDegree = p := by
        rw [← IntermediateField.adjoin.finrank hβ_int, hKβ_top,
          LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfinL]
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ_int) hf_monic
        (minpoly.dvd K β hβ) (by rw [hf_deg, hdeg_min])).symm
    have hirr : Irreducible f := hmin_eq ▸ minpoly.irreducible hβ_int
    have hcyc : IsGarlingCyclicExtension K L :=
      ⟨hgal, isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank K L, hfinL])⟩
    exact ⟨hirr, hcyc, hfinL, by rw [extDegree_eq_finrank K L, hfinL]⟩

/-- Raw Galois trace sum `∑_{σ ∈ Γ(L : K)} σ(x)` valued in `L` (for finite Galois group `Γ(L : K)`). -/
noncomputable def garlingTraceL {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (x : L) : L :=
  letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  ∑ σ : L ≃ₐ[K] L, σ x

theorem garlingTraceL_eq_sum {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Fintype (L ≃ₐ[K] L)] (x : L) :
    garlingTraceL (K := K) x = ∑ σ : L ≃ₐ[K] L, σ x := by
  unfold garlingTraceL
  convert rfl

theorem garlingTraceL_gal_fix {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (x : L) :
    τ (garlingTraceL (K := K) x) = garlingTraceL (K := K) x := by
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  rw [garlingTraceL_eq_sum, map_sum]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : L ≃ₐ[K] L => σ x)

theorem garlingTraceL_apply_gal {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (x : L) :
    garlingTraceL (K := K) (τ x) = garlingTraceL (K := K) x := by
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  rw [garlingTraceL_eq_sum, garlingTraceL_eq_sum]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : L ≃ₐ[K] L => σ x)

/-- **Inline prose definition of Trace** (`Exercise 16.10`, §16.3, printed pp. 127–128 / PDF pp.
135–136):
For a Garling Galois extension `L : K` with Galois group `G = Γ(L : K)`, the trace
`tr : L →ₗ[K] K` is the unique `K`-linear mapping satisfying
`algebraMap K L (tr x) = ∑_{σ ∈ G} σ(x)` for all `x ∈ L`. -/
noncomputable def garlingTrace (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) : L →ₗ[K] K :=
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hmem : ∀ x : L, ∃ k : K, algebraMap K L k = garlingTraceL (K := K) x :=
    fun x => mem_range_algebraMap_of_forall_gal_fix fun τ => garlingTraceL_gal_fix τ x
  { toFun := fun x => (hmem x).choose
    map_add' := fun x y => (algebraMap K L).injective (by
      let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
      rw [map_add, (hmem (x + y)).choose_spec, (hmem x).choose_spec, (hmem y).choose_spec,
        garlingTraceL_eq_sum, garlingTraceL_eq_sum, garlingTraceL_eq_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun σ _ => map_add σ x y)
    map_smul' := fun c x => (algebraMap K L).injective (by
      let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
      simp only [RingHom.id_apply, smul_eq_mul, map_mul, Algebra.smul_def]
      rw [(hmem _).choose_spec, (hmem x).choose_spec, garlingTraceL_eq_sum, garlingTraceL_eq_sum,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, σ.commutes]) }

theorem garlingTrace_spec {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) [Fintype (L ≃ₐ[K] L)] (x : L) :
    algebraMap K L (garlingTrace K L hgal x) = ∑ σ : L ≃ₐ[K] L, σ x := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  unfold garlingTrace
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [(mem_range_algebraMap_of_forall_gal_fix fun τ => garlingTraceL_gal_fix τ x).choose_spec,
    garlingTraceL_eq_sum]

theorem garlingTrace_apply_gal {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) (τ : L ≃ₐ[K] L) (x : L) :
    garlingTrace K L hgal (τ x) = garlingTrace K L hgal x := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  apply (algebraMap K L).injective
  rw [garlingTrace_spec, garlingTrace_spec]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : L ≃ₐ[K] L => σ x)

/-- **Exercise 16.10** (§16.3, printed pp. 127–128 / PDF pp. 135–136; `QUEUE.md` Flags 6–7):
*"Suppose that `L : K` is a Galois extension with Galois group `G`. If `x ∈ L`, let
`tr(x) = ∑_{σ ∈ G} σ(x)`. Show that `tr` is a `K`-linear mapping of `L` onto `K`. The mapping `tr`
is the `trace`. What is the effect of `tr` on `K` if `char K ∣ |G|`?"*

Proves:
1. `garlingTrace K L hgal : L →ₗ[K] K` satisfies `tr(x) = ∑_{σ ∈ G} σ(x)` and is **surjective**
   onto `K` (via the Corollary to Theorem 16.3);
2. For all `k ∈ K`, `tr(k) = |G| · k`;
3. When `char K ∣ |G|` (and indeed iff `char K ∣ |G|`), `tr|_K = 0` (`tr` vanishes identically on `K`). -/
theorem exercise_16_10 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) :
    (∀ [Fintype (GarlingGaloisGroup K L)] (x : L),
      algebraMap K L (garlingTrace K L hgal x) = ∑ σ : GarlingGaloisGroup K L, σ x) ∧
    Function.Surjective (garlingTrace K L hgal) ∧
    (∀ k : K, garlingTrace K L hgal (algebraMap K L k) =
      (Nat.card (GarlingGaloisGroup K L) : K) * k) ∧
    (ringChar K ∣ Nat.card (GarlingGaloisGroup K L) ↔
      ∀ k : K, garlingTrace K L hgal (algebraMap K L k) = 0) := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have hsurj : Function.Surjective (garlingTrace K L hgal) := by
    let eFin : Fin (Fintype.card (L ≃ₐ[K] L)) ≃ (L ≃ₐ[K] L) := (Fintype.equivFin _).symm
    have hpos : 0 < Fintype.card (L ≃ₐ[K] L) := Fintype.card_pos
    obtain ⟨x₀, hx₀⟩ := exists_apply_sum_ne_zero_of_algEquiv
      (fun i => eFin i) eFin.injective (fun _ => (1 : L)) ⟨⟨0, hpos⟩, one_ne_zero⟩
    have htr0_ne : garlingTrace K L hgal x₀ ≠ 0 := by
      intro h0
      apply hx₀
      have h1 : algebraMap K L (garlingTrace K L hgal x₀) = 0 := by rw [h0, map_zero]
      rw [garlingTrace_spec] at h1
      simpa [one_mul, Equiv.sum_comp eFin (fun σ : L ≃ₐ[K] L => σ x₀)] using h1
    intro c
    refine ⟨(c * (garlingTrace K L hgal x₀)⁻¹) • x₀, ?_⟩
    rw [LinearMap.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ htr0_ne, mul_one]
  have honK : ∀ k : K, garlingTrace K L hgal (algebraMap K L k) =
      (Nat.card (GarlingGaloisGroup K L) : K) * k := by
    intro k
    apply (algebraMap K L).injective
    rw [garlingTrace_spec, map_mul, map_natCast]
    have hsum : (∑ σ : L ≃ₐ[K] L, σ (algebraMap K L k)) =
        (Fintype.card (L ≃ₐ[K] L) : L) * algebraMap K L k := by
      simp [AlgEquiv.commutes]
    rw [hsum, Nat.card_eq_fintype_card]
  have hchar_iff : ringChar K ∣ Nat.card (GarlingGaloisGroup K L) ↔
      ∀ k : K, garlingTrace K L hgal (algebraMap K L k) = 0 := by
    constructor
    · intro hdvd k
      rw [honK, (ringChar.spec K _).mpr hdvd, zero_mul]
    · intro hall
      have h1 := hall 1
      rw [honK, mul_one] at h1
      exact (ringChar.spec K _).mp h1
  exact ⟨fun [_] x => garlingTrace_spec hgal x, hsurj, honK, hchar_iff⟩

/-- **Exercise 16.11** (§16.3, printed p. 128 / PDF p. 136):
*"Suppose that `char K = p`, that `L : K` is a cyclic extension of degree `p` and that `τ` generates
`Γ(L : K)`. Let `z` be an element of `L` with `tr(z) = 1`, and let
`y = (p - 1)z + (p - 2)τ(z) + ... + 2τ^{p-3}(z) + τ^{p-2}(z)`.
Show that `τ(y) - y = 1`, and that `α = y^p - y ∈ K`. Show that `f = x^p - x - α` is irreducible
over `K`, that `L : K` is a splitting field extension for `f` and that `L = K(y)`."* -/
theorem exercise_16_11 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hchar : ringChar K = p) (hcyc : IsGarlingCyclicExtension K L)
    (hdeg : Module.finrank K L = p) {τ : GarlingGaloisGroup K L}
    (hgen : Subgroup.zpowers τ = ⊤) {z : L} (hz : garlingTrace K L hcyc.1 z = 1) :
    let y : L := ∑ j : Fin p, ((p - 1 - (j : ℕ) : ℕ) : L) * (τ ^ (j : ℕ)) z
    Nat.Prime p ∧
    τ y - y = 1 ∧
    ∃ α : K,
      algebraMap K L α = y ^ p - y ∧
      Irreducible (Polynomial.X ^ p - Polynomial.X - Polynomial.C α : K[X]) ∧
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ p - Polynomial.X - Polynomial.C α) ∧
      K⟮y⟯ = ⊤ := by
  intro y
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hcyc.1 |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hcyc.1 |>.2
  have hp_pos : 0 < p := hdeg ▸ Module.finrank_pos
  have hp : Nat.Prime p := by
    have _ : CharP K p := hchar ▸ ringChar.charP K
    rcases CharP.char_is_prime_or_zero K p with hp | h0
    · exact hp
    · omega
  have _ : CharP K p := hchar ▸ ringChar.charP K
  have _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : Fact p.Prime := ⟨hp⟩
  have hcardG : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  have hτ_ord : orderOf τ = p := by
    rw [← Nat.card_zpowers, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
  have hτ_pow_bij : Function.Bijective (fun k : Fin p => τ ^ (k : ℕ)) := by
    let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardG]⟩
    intro a b hab
    have hmod : (a : ℕ) ≡ (b : ℕ) [MOD p] := by
      have h1 := pow_eq_pow_iff_modEq.mp hab
      rwa [hτ_ord] at h1
    rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  have htr_z : ∑ k : Fin p, (τ ^ (k : ℕ)) z = 1 := by
    let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
    have h1 := garlingTrace_spec hcyc.1 z
    rw [hz, map_one] at h1
    rw [h1]
    exact Equiv.sum_comp (Equiv.ofBijective _ hτ_pow_bij) (fun σ : L ≃ₐ[K] L => σ z)
  -- Show τ(y) - y = ∑ k, τ^k(z) = 1
  have hτy : τ y - y = 1 := by
    have h1 : τ y = ∑ j : Fin p, ((p - 1 - (j : ℕ) : ℕ) : L) * (τ ^ ((j : ℕ) + 1)) z := by
      simp only [y, map_sum, map_mul, map_natCast]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← AlgEquiv.mul_apply, ← pow_succ']
    rw [h1]
    let shift : Fin p ≃ Fin p := Equiv.addRight (1 : Fin p)
    rw [← Equiv.sum_comp shift.symm, ← Finset.sum_sub_distrib, ← htr_z]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsymm : shift.symm k = k - 1 := by simp [shift, sub_eq_add_neg]
    rw [hsymm, fin_sub_one_val k]
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
    · have hkz : k = 0 := Fin.ext hk0
      subst hkz
      simp only [Fin.val_zero, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_mul, zero_sub,
        Nat.sub_zero, pow_zero, AlgEquiv.one_apply]
      have hpm1 : ((p - 1 : ℕ) : L) = -1 := by
        have hsum : ((p - 1 : ℕ) : L) + 1 = 0 := by
          calc ((p - 1 : ℕ) : L) + 1 = ((p - 1 : ℕ) : L) + ((1 : ℕ) : L) := by simp
            _ = (((p - 1) + 1 : ℕ) : L) := (Nat.cast_add (p - 1) 1).symm
            _ = (p : L) := by rw [Nat.sub_add_cancel hp.one_le]
            _ = 0 := CharP.cast_eq_zero L p
        linear_combination hsum
      rw [hpm1]; ring
    · simp only [Nat.ne_of_gt hkpos, ↓reduceIte]
      rw [Nat.sub_add_cancel hkpos]
      have hdiff : ((p - 1 - ((k : ℕ) - 1) : ℕ) : L) - ((p - 1 - (k : ℕ) : ℕ) : L) = 1 := by
        have hlt : (k : ℕ) < p := k.isLt
        have heq : p - 1 - ((k : ℕ) - 1) = (p - 1 - (k : ℕ)) + 1 := by omega
        rw [heq, Nat.cast_add, Nat.cast_one]; ring
      rw [← sub_mul, hdiff, one_mul]
  -- Show α = y^p - y is fixed by τ, hence lies in K
  have hτ_ypy : τ (y ^ p - y) = y ^ p - y := by
    have hτy_eq : τ y = y + 1 := by linear_combination hτy
    rw [map_sub, map_pow, hτy_eq, add_pow_char, one_pow]
    ring
  obtain ⟨α, hα_eq⟩ :=
    mem_range_algebraMap_of_forall_gal_fix (forall_gal_fix_of_gen_fix hgen hτ_ypy)
  let f : K[X] := Polynomial.X ^ p - Polynomial.X - Polynomial.C α
  have hy_root : Polynomial.aeval y f = 0 := by
    simp [f, hα_eq]
  have hy_not_K : y ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    have hfix : τ y = y := by rw [← hc, τ.commutes]
    rw [hfix, sub_self] at hτy
    exact zero_ne_one hτy
  have hKy_top : K⟮y⟯ = ⊤ := by
    have hgt1 : 1 < Module.finrank K K⟮y⟯ := by
      have hpos : 0 < Module.finrank K K⟮y⟯ := Module.finrank_pos
      by_contra hle
      have h1 : Module.finrank K K⟮y⟯ = 1 := by omega
      have hbot : (⊥ : IntermediateField K L) = K⟮y⟯ :=
        IntermediateField.eq_of_le_of_finrank_eq bot_le (by rw [IntermediateField.finrank_bot, h1])
      exact hy_not_K (IntermediateField.mem_bot.mp (hbot ▸ IntermediateField.mem_adjoin_simple_self K y))
    have hdvd_p : Module.finrank K K⟮y⟯ ∣ p := by
      rw [← hdeg]
      exact ⟨Module.finrank K⟮y⟯ L, (Module.finrank_mul_finrank K K⟮y⟯ L).symm⟩
    have hfin_p : Module.finrank K K⟮y⟯ = p := by
      rcases hp.eq_one_or_self_of_dvd _ hdvd_p with h1 | hp_eq
      · omega
      · exact hp_eq
    exact IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [hfin_p, LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hdeg])
  -- Show f splits over L (as ∏ (X - (y + j))) and L : K is its splitting field extension
  have hf_deg : f.natDegree = p := by
    have h1 : (Polynomial.X ^ p - Polynomial.X : K[X]).natDegree = p := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow p
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp.one_lt
    rw [show f = (Polynomial.X ^ p - Polynomial.X) - Polynomial.C α from rfl,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact h1
    · rw [Polynomial.natDegree_C, h1]; exact hp.pos
  have hf_monic : f.Monic := by
    have h1 : (Polynomial.X ^ p - Polynomial.X : K[X]).Monic := by
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow p) ?_
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]; exact_mod_cast hp.one_lt
    refine h1.sub_of_left ?_
    rw [Polynomial.degree_eq_natDegree h1.ne_zero]
    have hd1 : (Polynomial.X ^ p - Polynomial.X : K[X]).natDegree = p := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow p
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp.one_lt
    rw [hd1]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hp.pos)
  have hfacL : f.map (algebraMap K L) = ∏ j : Fin p, (Polynomial.X - Polynomial.C (y + (j : L))) := by
    have hinj : Function.Injective (fun j : Fin p => y + (j : L)) := by
      intro a b hab
      have hcast : ((a : ℕ) : L) = ((b : ℕ) : L) := add_left_cancel hab
      rcases le_total (a : ℕ) (b : ℕ) with hle | hle
      · have hdvd : p ∣ (b : ℕ) - (a : ℕ) :=
          (CharP.cast_eq_zero_iff L p _).mp (by rw [Nat.cast_sub hle, hcast, sub_self])
        have h0 : (b : ℕ) - (a : ℕ) = 0 := by
          by_contra hne; exact not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (by omega)
        exact Fin.ext (by omega)
      · have hdvd : p ∣ (a : ℕ) - (b : ℕ) :=
          (CharP.cast_eq_zero_iff L p _).mp (by rw [Nat.cast_sub hle, hcast, sub_self])
        have h0 : (a : ℕ) - (b : ℕ) = 0 := by
          by_contra hne; exact not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (by omega)
        exact Fin.ext (by omega)
    let S : Finset L := Finset.univ.image (fun j : Fin p => y + (j : L))
    have hdvd : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) ∣ f.map (algebraMap K L) := by
      refine Finset.prod_dvd_of_coprime
        (fun x _ y' _ hxy => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy) ?_
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨j, _, rfl⟩
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [add_pow_char, natCast_pow_char hp (j : ℕ)]
      linear_combination hα_eq.symm
    rw [Finset.prod_image fun a _ b _ hab => hinj hab] at hdvd
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _)
      (hf_monic.map _) hdvd (by
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective, hf_deg,
          Polynomial.natDegree_prod _ _ (fun j _ => Polynomial.X_sub_C_ne_zero _)]
        simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one, le_refl])
  have hsf : IsGarlingSplittingFieldExtension K L f := by
    refine ⟨⟨p, 1, fun j => y + (j : L), ?_⟩, ?_⟩
    · rw [GarlingSplitsExplicit, map_one, Polynomial.C_1, one_mul]; exact hfacL
    · intro M hM hspM
      have hsp_ml := (garlingSplitsOver_iff_splits K M f).mp hspM
      have hne_r : (f.map (algebraMap K M)).roots ≠ 0 := by
        intro h0
        have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
        rw [h0, Multiset.card_zero, Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective,
          hf_deg] at hc
        exact hp.ne_zero hc
      obtain ⟨rM, hrM⟩ := Multiset.exists_mem_of_ne_zero hne_r
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf_monic.ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map, ← Polynomial.aeval_def] at hrM
      have hrL : Polynomial.aeval (rM : L) f = 0 := by
        change Polynomial.aeval (M.val rM) f = 0
        rw [Polynomial.aeval_algHom_apply, hrM, map_zero]
      have hev := congrArg (Polynomial.eval (rM : L)) hfacL
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, hrL, Polynomial.eval_prod, eq_comm,
        Finset.prod_eq_zero_iff] at hev
      rcases hev with ⟨j, _, hj⟩
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
      have hy_in_M : y ∈ M := by
        have hy_eq : y = (rM : L) - (j : L) := by linear_combination -hj
        rw [hy_eq]
        exact sub_mem rM.2 (natCast_mem M (j : ℕ))
      have htop_le : (⊤ : IntermediateField K L) ≤ M := by
        rw [← hKy_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hy_in_M
      exact hM (le_antisymm le_top htop_le)
  have hnot_spK : ¬ GarlingSplitsOver K K f := by
    intro hspK
    have hsp_ml := (garlingSplitsOver_iff_splits K K f).mp hspK
    rw [Algebra.algebraMap_self, Polynomial.map_id] at hsp_ml
    have hne_r : f.roots ≠ 0 := by
      intro h0
      have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
      rw [h0, Multiset.card_zero, hf_deg] at hc; exact hp.ne_zero hc
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hne_r
    rw [Polynomial.mem_roots hf_monic.ne_zero, Polynomial.IsRoot.def] at hc
    have hev := congrArg (Polynomial.eval (algebraMap K L c)) hfacL
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hc, map_zero, Polynomial.eval_prod, eq_comm,
      Finset.prod_eq_zero_iff] at hev
    rcases hev with ⟨j, _, hj⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    exact hy_not_K ⟨c - (j : K), by rw [map_sub, map_natCast]; linear_combination hj⟩
  have hirr : Irreducible f := by
    rcases (exercise_16_9 hp hchar α hsf).2 with ⟨hsp, _⟩ | ⟨hi, _⟩
    · exact (hnot_spK hsp).elim
    · exact hi.1
  exact ⟨hp, hτy, α, hα_eq, hirr, hsf, hKy_top⟩

/-- Raw Galois norm product `∏_{σ ∈ Γ(L : K)} σ(x)` valued in `L`. -/
noncomputable def garlingNormL {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (x : L) : L :=
  letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  ∏ σ : L ≃ₐ[K] L, σ x

theorem garlingNormL_eq_prod {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Fintype (L ≃ₐ[K] L)] (x : L) :
    garlingNormL (K := K) x = ∏ σ : L ≃ₐ[K] L, σ x := by
  unfold garlingNormL
  convert rfl

theorem garlingNormL_gal_fix {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Finite (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (x : L) :
    τ (garlingNormL (K := K) x) = garlingNormL (K := K) x := by
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  rw [garlingNormL_eq_prod, map_prod]
  exact Equiv.prod_comp (Equiv.mulLeft τ) (fun σ : L ≃ₐ[K] L => σ x)

/-- **Inline prose definition of Norm** (`Exercise 16.12`, §16.3, printed p. 128 / PDF p. 136):
For a Garling Galois extension `L : K` with Galois group `G = Γ(L : K)`, the norm
`N : L →* K` is the unique multiplicative monoid homomorphism satisfying
`algebraMap K L (N x) = ∏_{σ ∈ G} σ(x)` for all `x ∈ L`. -/
noncomputable def garlingNorm (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) : L →* K :=
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hmem : ∀ x : L, ∃ k : K, algebraMap K L k = garlingNormL (K := K) x :=
    fun x => mem_range_algebraMap_of_forall_gal_fix fun τ => garlingNormL_gal_fix τ x
  { toFun := fun x => (hmem x).choose
    map_one' := (algebraMap K L).injective (by
      let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
      rw [(hmem 1).choose_spec, map_one, garlingNormL_eq_prod]
      simp)
    map_mul' := fun x y => (algebraMap K L).injective (by
      let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
      rw [map_mul, (hmem (x * y)).choose_spec, (hmem x).choose_spec, (hmem y).choose_spec,
        garlingNormL_eq_prod, garlingNormL_eq_prod, garlingNormL_eq_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun σ _ => map_mul σ x y) }

theorem garlingNorm_spec {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) [Fintype (L ≃ₐ[K] L)] (x : L) :
    algebraMap K L (garlingNorm K L hgal x) = ∏ σ : L ≃ₐ[K] L, σ x := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  unfold garlingNorm
  dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [(mem_range_algebraMap_of_forall_gal_fix fun τ => garlingNormL_gal_fix τ x).choose_spec,
    garlingNormL_eq_prod]

theorem garlingNorm_apply_gal {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) (τ : L ≃ₐ[K] L) (x : L) :
    garlingNorm K L hgal (τ x) = garlingNorm K L hgal x := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  apply (algebraMap K L).injective
  rw [garlingNorm_spec, garlingNorm_spec]
  exact Equiv.prod_comp (Equiv.mulRight τ) (fun σ : L ≃ₐ[K] L => σ x)

theorem garlingNorm_zero {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) :
    garlingNorm K L hgal 0 = 0 := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  apply (algebraMap K L).injective
  rw [garlingNorm_spec, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ (1 : L ≃ₐ[K] L)) (by simp)

theorem garlingNorm_div {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) {x y : L} (hy : y ≠ 0) :
    garlingNorm K L hgal (x / y) = garlingNorm K L hgal x / garlingNorm K L hgal y := by
  have hyN : garlingNorm K L hgal y ≠ 0 := by
    intro h0
    have h1 := map_mul (garlingNorm K L hgal) y y⁻¹
    rw [mul_inv_cancel₀ hy, map_one, h0, zero_mul] at h1
    exact one_ne_zero h1
  apply mul_right_cancel₀ hyN
  rw [← map_mul, div_mul_cancel₀ _ hy, div_mul_cancel₀ _ hyN]

/-- **Exercise 16.12** (§16.3, printed p. 128 / PDF p. 136; exact integer quotient `((n / r : ℕ) : K)`
per `QUEUE.md` Flag 4):
*"Suppose that `L : K` is a Galois extension of degree `n` with Galois group `G`. If `x ∈ L`, let
`tr(x) = ∑_{σ ∈ G} σ(x)`, `N(x) = ∏_{σ ∈ G} σ(x)`. The mapping `N` is the `norm`. Suppose that
`α ∈ L` has minimal polynomial `x^r - a₁ x^{r-1} + ... + (-1)^r a_r` Show that
`tr(α) = (n/r) a₁` and `N(α) = a_r^{n/r}`."* -/
theorem exercise_16_12 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hgal : IsGarlingGaloisExtension K L) (hdeg : Module.finrank K L = n) (α : L) :
    let m : K[X] := minpoly K α
    let r : ℕ := m.natDegree
    let a₁ : K := -(m.coeff (r - 1))
    let a_r : K := (-1) ^ r * m.coeff 0
    1 ≤ r ∧
    r ∣ n ∧
    garlingTrace K L hgal α = ((n / r : ℕ) : K) * a₁ ∧
    garlingNorm K L hgal α = a_r ^ (n / r) := by
  intro m r a₁ a_r
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have hα_int : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hr_pos : 1 ≤ r := minpoly.natDegree_pos hα_int
  have hfin_Kα : Module.finrank K K⟮α⟯ = r := IntermediateField.adjoin.finrank hα_int
  have hmul_deg : r * Module.finrank K⟮α⟯ L = n := by
    rw [← hfin_Kα, Module.finrank_mul_finrank K K⟮α⟯ L, hdeg]
  have hr_dvd : r ∣ n := ⟨Module.finrank K⟮α⟯ L, hmul_deg.symm⟩
  have hq_eq : Module.finrank K⟮α⟯ L = n / r := by
    rw [← hmul_deg, Nat.mul_div_cancel_left _ hr_pos]
  -- Let H = fixingSubgroup K⟮α⟯; |H| = n / r and orbit {σ α | σ ∈ G} has cardinality r
  let H : Subgroup (L ≃ₐ[K] L) := IntermediateField.fixingSubgroup K⟮α⟯
  have hH_card : Nat.card H = n / r := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank, hq_eq]
  let orbit : Finset L := Finset.univ.image (fun σ : L ≃ₐ[K] L => σ α)
  -- Every fiber {σ | σ α = x} for x ∈ orbit has cardinality |H| = n / r
  have hfiber_card : ∀ x ∈ orbit,
      (Finset.univ.filter fun σ : L ≃ₐ[K] L => σ α = x).card = n / r := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨σ₀, _, rfl⟩
    let _ : Fintype H := Fintype.ofFinite H
    have hbij : Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ α = σ₀ α) =
        Finset.univ.image (fun h : H => σ₀ * h.1) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hσ
        have hmemH : σ₀⁻¹ * σ ∈ H := by
          rw [IntermediateField.mem_fixingSubgroup_iff]
          let Eeq : IntermediateField K L :=
            { (AlgHom.equalizer (σ₀⁻¹ * σ).toAlgHom (1 : L ≃ₐ[K] L).toAlgHom) with
              inv_mem' := fun {y} hy => by
                change (σ₀⁻¹ * σ) y⁻¹ = y⁻¹; rw [map_inv₀]; exact congrArg Inv.inv hy }
          have hle : K⟮α⟯ ≤ Eeq := by
            rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
            change (σ₀⁻¹ * σ) α = α
            rw [AlgEquiv.mul_apply, hσ, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
          intro y hy; exact hle hy
        exact ⟨⟨σ₀⁻¹ * σ, hmemH⟩, by simp⟩
      · rintro ⟨h, rfl⟩
        rw [AlgEquiv.mul_apply]
        have hhα : h.1 α = α :=
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp h.2 α
            (IntermediateField.mem_adjoin_simple_self K α)
        rw [hhα]
    rw [hbij, Finset.card_image_of_injective _ fun a b hab =>
      Subtype.ext (mul_left_cancel hab), Finset.card_univ, ← Nat.card_eq_fintype_card, hH_card]
  -- Count |G| = ∑_{x ∈ orbit} |fiber x| = orbit.card * (n / r) ⇒ orbit.card = r
  have horbit_card : orbit.card = r := by
    have hcardG : (Finset.univ : Finset (L ≃ₐ[K] L)).card = n := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L, hdeg]
    have hsum_card : (Finset.univ : Finset (L ≃ₐ[K] L)).card =
        ∑ x ∈ orbit, (Finset.univ.filter fun σ : L ≃ₐ[K] L => σ α = x).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext σ
        simp [orbit]
      · intro x _ y _ hxy
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro σ h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hxy (h1.2.symm.trans h2.2)
    rw [hcardG, Finset.sum_congr rfl hfiber_card, Finset.sum_const, smul_eq_mul] at hsum_card
    have hq_pos : 0 < n / r := by rw [← hq_eq]; exact Module.finrank_pos
    have hmul_eq : orbit.card * (n / r) = r * (n / r) := by
      rw [← hsum_card, Nat.mul_div_cancel' hr_dvd]
    exact Nat.eq_of_mul_eq_mul_right hq_pos hmul_eq
  -- Identify m.map (algebraMap K L) = ∏ x ∈ orbit, (X - C x)
  have hm_fac : m.map (algebraMap K L) = ∏ x ∈ orbit, (Polynomial.X - Polynomial.C x) := by
    have hdvd : (∏ x ∈ orbit, (Polynomial.X - Polynomial.C x)) ∣ m.map (algebraMap K L) := by
      refine Finset.prod_dvd_of_coprime
        (fun x _ y _ hxy => Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy) ?_
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨σ, _, rfl⟩
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (Polynomial.monic_prod_of_monic _ _ fun x _ => Polynomial.monic_X_sub_C x)
      ((minpoly.monic hα_int).map _) hdvd (by
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
          Polynomial.natDegree_prod _ _ (fun x _ => Polynomial.X_sub_C_ne_zero x)]
        simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
          horbit_card]
        exact le_rfl)
  -- Vieta identities on ∏ x ∈ orbit, (X - C x): sum of roots = a₁, product of roots = a_r
  have hvieta_sum : ∀ (s : Finset L), 1 ≤ s.card →
      (∏ x ∈ s, (Polynomial.X - Polynomial.C x)).coeff (s.card - 1) = - ∑ x ∈ s, x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a s ha ih =>
      intro _
      rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, Finset.sum_insert ha,
        Nat.add_sub_cancel]
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · simp
      · have hs1 : 1 ≤ s.card := Finset.card_pos.mpr hne
        have hih := ih hs1
        let P : L[X] := ∏ x ∈ s, (Polynomial.X - Polynomial.C x)
        have hP_mon : P.Monic :=
          Polynomial.monic_prod_of_monic _ _ fun x _ => Polynomial.monic_X_sub_C x
        have hP_deg : P.natDegree = s.card := by
          rw [Polynomial.natDegree_prod _ _ (fun x _ => Polynomial.X_sub_C_ne_zero x)]
          simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        have hP_top : P.coeff s.card = 1 := by
          rw [← hP_mon.coeff_natDegree]; congr 1; exact hP_deg.symm
        rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hP_top, mul_one]
        have hidx : s.card - 1 + 1 = s.card := Nat.sub_add_cancel hs1
        have hXP : (Polynomial.X * P).coeff s.card = P.coeff (s.card - 1) := by
          conv_lhs => arg 2; rw [← hidx]
          exact Polynomial.coeff_X_mul P (s.card - 1)
        rw [hXP, hih]
        ring
  have horbit_sum : ∑ x ∈ orbit, x = algebraMap K L a₁ := by
    have h1 := congrArg (fun p : L[X] => p.coeff (r - 1)) hm_fac
    rw [Polynomial.coeff_map] at h1
    have h2 := hvieta_sum orbit (horbit_card.symm ▸ hr_pos)
    rw [horbit_card] at h2
    rw [h2] at h1
    simp only [a₁, map_neg]
    linear_combination h1
  have horbit_prod : ∏ x ∈ orbit, x = algebraMap K L a_r := by
    have h1 := congrArg (Polynomial.eval (0 : L)) hm_fac
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.eval_prod] at h1
    have h2 : (∏ x ∈ orbit, (Polynomial.X - Polynomial.C x).eval (0 : L)) =
        (-1 : L) ^ r * ∏ x ∈ orbit, x := by
      calc (∏ x ∈ orbit, (Polynomial.X - Polynomial.C x).eval (0 : L))
          = ∏ x ∈ orbit, ((-1 : L) * x) := Finset.prod_congr rfl fun x _ => by simp
        _ = (∏ _ ∈ orbit, (-1 : L)) * ∏ x ∈ orbit, x := Finset.prod_mul_distrib
        _ = (-1 : L) ^ r * ∏ x ∈ orbit, x := by rw [Finset.prod_const, horbit_card]
    rw [h2] at h1
    simp only [a_r, map_mul, map_pow, map_neg, map_one]
    calc ∏ x ∈ orbit, x
        = (-1 : L) ^ r * ((-1 : L) ^ r * ∏ x ∈ orbit, x) := by
          rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
      _ = (-1 : L) ^ r * algebraMap K L (m.coeff 0) := by rw [← h1]
  -- Sum and product over G via fiberwise partition over orbit
  have htr : garlingTrace K L hgal α = ((n / r : ℕ) : K) * a₁ := by
    apply (algebraMap K L).injective
    rw [garlingTrace_spec, map_mul, map_natCast, ← horbit_sum]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (L ≃ₐ[K] L))) (t := orbit) (g := fun σ => σ α)
      (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)) (fun σ => σ α)
    rw [← hfib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hconst : (∑ σ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ α = x), σ α) =
        ∑ _ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ α = x), x :=
      Finset.sum_congr rfl fun σ hσ => (Finset.mem_filter.mp hσ).2
    rw [hconst, Finset.sum_const, hfiber_card x hx, nsmul_eq_mul]
  have hnorm : garlingNorm K L hgal α = a_r ^ (n / r) := by
    apply (algebraMap K L).injective
    rw [garlingNorm_spec, map_pow, ← horbit_prod]
    have hfib := Finset.prod_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (L ≃ₐ[K] L))) (t := orbit) (g := fun σ => σ α)
      (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)) (fun σ => σ α)
    rw [← hfib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hconst : (∏ σ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ α = x), σ α) =
        ∏ _ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ α = x), x :=
      Finset.prod_congr rfl fun σ hσ => (Finset.mem_filter.mp hσ).2
    rw [hconst, Finset.prod_const, hfiber_card x hx]
  exact ⟨hr_pos, hr_dvd, htr, hnorm⟩

/-- **Field-division counterexample for `Exercise 16.12` in positive characteristic** (`QUEUE.md`
Flag 4):
Over `K = ZMod 2`, `f = X^2 + X + 1` is irreducible; in `L = AdjoinRoot f` (`n = r = 2`), the root
`α` has `a₁ = 1` and `tr(α) = 1 = ((2 / 2 : ℕ) : ZMod 2) * 1`, whereas field division
`((2 : ZMod 2) / (2 : ZMod 2)) * 1 = 0 ≠ 1`. -/
theorem exercise_16_12_field_division_counterexample :
    ((2 / 2 : ℕ) : ZMod 2) * (1 : ZMod 2) = 1 ∧
    ((2 : ZMod 2) / (2 : ZMod 2)) * (1 : ZMod 2) = 0 ∧
    ((2 / 2 : ℕ) : ZMod 2) * (1 : ZMod 2) ≠ ((2 : ZMod 2) / (2 : ZMod 2)) * (1 : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hdiv : ((2 / 2 : ℕ) : ZMod 2) = 1 := by norm_num
  rw [h2, div_zero, zero_mul, hdiv, one_mul]
  exact ⟨rfl, rfl, one_ne_zero⟩

/-- Recursive cocycle sequence `c₀ = α`, `c_{k+1} = α * τ(c_k)` from `Exercise 16.13 (ii)`
(printed p. 128 / PDF p. 136). -/
def hilbert90Coeff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (α : L) : ℕ → L
  | 0 => α
  | k + 1 => α * τ (hilbert90Coeff τ α k)

theorem hilbert90Coeff_eq_prod {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) (α : L) (k : ℕ) :
    hilbert90Coeff τ α k = ∏ j ∈ Finset.range (k + 1), (τ ^ j) α := by
  induction k with
  | zero => simp [hilbert90Coeff]
  | succ k ih =>
    rw [hilbert90Coeff, ih, map_prod]
    conv_rhs => rw [Finset.prod_range_succ']
    rw [pow_zero, AlgEquiv.one_apply, mul_comm α]
    exact congrArg (· * α) (Finset.prod_congr rfl fun j _ => by
      rw [← AlgEquiv.mul_apply, ← pow_succ'])

/-- **Counterexample to unguarded `Exercise 16.13 (i)` at `β = 0` under Lean total division**
(`QUEUE.md` Flag 4):
In any Galois extension `L : K`, `β = 0` and `α = 0 / τ(0) = 0` satisfy `α = β / τ(β)` under total
division `0 / 0 = 0`, yet `N(0) = 0 ≠ 1`. -/
theorem exercise_16_13_i_zero_counterexample {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (hgal : IsGarlingGaloisExtension K L)
    (τ : GarlingGaloisGroup K L) :
    (0 : L) = (0 : L) / τ 0 ∧ garlingNorm K L hgal 0 ≠ 1 := by
  rw [map_zero, div_zero, garlingNorm_zero]
  exact ⟨rfl, zero_ne_one⟩

/-- **Exercise 16.13 (i)** (§16.3, printed p. 128 / PDF p. 136; implicit `β ≠ 0` made explicit per
`QUEUE.md` Flag 4):
If `α = β / τ(β)` with `β ≠ 0`, then `N(α) = 1`. -/
theorem exercise_16_13_i {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) (τ : GarlingGaloisGroup K L)
    {α β : L} (hβ : β ≠ 0) (hα : α = β / τ β) :
    garlingNorm K L hgal α = 1 := by
  have hτβ_ne : τ β ≠ 0 := (map_ne_zero τ).mpr hβ
  have hNβ_ne : garlingNorm K L hgal β ≠ 0 := by
    intro h0
    have h1 := map_mul (garlingNorm K L hgal) β β⁻¹
    rw [mul_inv_cancel₀ hβ, map_one, h0, zero_mul] at h1
    exact one_ne_zero h1
  rw [hα, garlingNorm_div hgal hτβ_ne, garlingNorm_apply_gal hgal τ β, div_self hNβ_ne]

/-- **Exercise 16.13 (ii) — Hilbert's Theorem 90** (§16.3, printed p. 128 / PDF p. 136):
*"Suppose that `L : K` is a Galois extension of degree `n` with cyclic Galois group generated by
`τ`, say. (ii) Suppose that `N(α) = 1`. Let `c₀ = α, c₁ = ατ(c₀), c₂ = ατ(c₁), ...,
c_{n-1} = ατ(c_{n-2})`. Show that there exists `γ` in `L` such that
`β = c₀γ + c₁τ(γ) + ... + c_{n-1}τ^{n-1}(γ) ≠ 0`. Show that `α = β/τ(β)`."*

*(OCR warning verified against 200 DPI scan PDF p. 136: `garling1986_pages.txt` ll. 4784–4785
corrupts Greek `γ` to `y` four times.)* -/
theorem exercise_16_13_ii {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hgal : IsGarlingGaloisExtension K L) (hdeg : Module.finrank K L = n)
    {τ : GarlingGaloisGroup K L} (hgen : Subgroup.zpowers τ = ⊤)
    {α : L} (hN : garlingNorm K L hgal α = 1) :
    ∃ γ : L,
      let β : L := ∑ k : Fin n, hilbert90Coeff τ α (k : ℕ) * (τ ^ (k : ℕ)) γ
      β ≠ 0 ∧ α = β / τ β := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have hn : 1 ≤ n := hdeg ▸ Module.finrank_pos
  have hcardG : Nat.card (L ≃ₐ[K] L) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  have hτ_ord : orderOf τ = n := by
    rw [← Nat.card_zpowers, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
  have hτ_pow_inj : Function.Injective (fun k : Fin n => τ ^ (k : ℕ)) := by
    intro a b hab
    have hmod : (a : ℕ) ≡ (b : ℕ) [MOD n] := by
      have h1 := pow_eq_pow_iff_modEq.mp hab
      rwa [hτ_ord] at h1
    rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  have hτ_pow_bij : Function.Bijective (fun k : Fin n => τ ^ (k : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hτ_pow_inj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardG]⟩
  have hα_ne : α ≠ 0 := by
    intro h0; rw [h0, garlingNorm_zero] at hN; exact zero_ne_one hN
  -- Show c_{n-1} = N(α) = 1
  have hc_last : hilbert90Coeff τ α (n - 1) = 1 := by
    rw [hilbert90Coeff_eq_prod, Nat.sub_add_cancel hn]
    have hprod_fin : (∏ j ∈ Finset.range n, (τ ^ j) α) = ∏ k : Fin n, (τ ^ (k : ℕ)) α :=
      (Fin.prod_univ_eq_prod_range (fun j => (τ ^ j) α) n).symm
    rw [hprod_fin]
    change (∏ i : Fin n, (Equiv.ofBijective _ hτ_pow_bij i) α) = 1
    rw [Equiv.prod_comp (Equiv.ofBijective _ hτ_pow_bij) (fun σ : L ≃ₐ[K] L => σ α),
      ← garlingNorm_spec hgal α, hN, map_one]
  -- Apply Corollary to Theorem 16.3 to get γ with β ≠ 0
  obtain ⟨γ, hβ_ne⟩ := exists_apply_sum_ne_zero_of_algEquiv
    (fun k : Fin n => τ ^ (k : ℕ)) hτ_pow_inj
    (fun k : Fin n => hilbert90Coeff τ α (k : ℕ))
    ⟨⟨0, hn⟩, by simpa [hilbert90Coeff] using hα_ne⟩
  refine ⟨γ, hβ_ne, ?_⟩
  let β : L := ∑ k : Fin n, hilbert90Coeff τ α (k : ℕ) * (τ ^ (k : ℕ)) γ
  change β ≠ 0 at hβ_ne
  -- Compute α * τ(β) = β by cyclic shift on Fin n
  have hα_mul_τβ : α * τ β = β := by
    have h1 : α * τ β =
        ∑ k : Fin n, (α * τ (hilbert90Coeff τ α (k : ℕ))) * (τ ^ ((k : ℕ) + 1)) γ := by
      simp only [β, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← AlgEquiv.mul_apply, ← pow_succ']
    rw [h1]
    have : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let shift : Fin n ≃ Fin n := Equiv.addRight (1 : Fin n)
    rw [← Equiv.sum_comp shift.symm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsymm : shift.symm k = k - 1 := by simp [shift, sub_eq_add_neg]
    rw [hsymm, fin_sub_one_val k]
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
    · have hkz : k = 0 := Fin.ext hk0
      subst hkz
      simp only [Fin.val_zero, ↓reduceIte, hc_last, map_one, mul_one, Nat.sub_add_cancel hn,
        show τ ^ n = 1 from hτ_ord ▸ pow_orderOf_eq_one τ]
      simp [hilbert90Coeff]
    · simp only [Nat.ne_of_gt hkpos, ↓reduceIte]
      rw [Nat.sub_add_cancel hkpos]
      change (hilbert90Coeff τ α (((k : ℕ) - 1) + 1)) * (τ ^ (k : ℕ)) γ =
        hilbert90Coeff τ α (k : ℕ) * (τ ^ (k : ℕ)) γ
      rw [Nat.sub_add_cancel hkpos]
  have hτβ_ne : τ β ≠ 0 := (map_ne_zero τ).mpr hβ_ne
  exact (eq_div_iff hτβ_ne).mpr hα_mul_τβ

/-- **Exercise 16.13 (Hilbert's theorem 90)** — bundled `(i)` + `(ii)` (§16.3, printed p. 128 /
PDF p. 136; `β ≠ 0` guard in `(i)` made explicit per `QUEUE.md` Flag 4). -/
theorem exercise_16_13 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hgal : IsGarlingGaloisExtension K L) (hdeg : Module.finrank K L = n)
    {τ : GarlingGaloisGroup K L} (hgen : Subgroup.zpowers τ = ⊤) (α : L) :
    garlingNorm K L hgal α = 1 ↔ ∃ β : L, β ≠ 0 ∧ α = β / τ β := by
  constructor
  · intro hN
    obtain ⟨γ, hβ_ne, hα_eq⟩ := exercise_16_13_ii hgal hdeg hgen hN
    exact ⟨_, hβ_ne, hα_eq⟩
  · rintro ⟨β, hβ_ne, hα_eq⟩
    exact exercise_16_13_i hgal τ hβ_ne hα_eq

/-- **Exercise 16.14 (Additive Hilbert's Theorem 90 — Repaired `τ(β)` form)** (§16.3, printed p. 128
/ PDF p. 136; repairs printed typo `σβ` for `τ(β)` per `QUEUE.md` Flag 3):
*"Suppose that `L : K` is a Galois extension of degree `n` with cyclic Galois group generated by
`τ`, say, and that `α ∈ L`. Show that `tr(α) = 0` if and only if there exists `β` in `L` such that
`α = β - τ(β)`."* -/
theorem exercise_16_14_repaired {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hgal : IsGarlingGaloisExtension K L) (hdeg : Module.finrank K L = n)
    {τ : GarlingGaloisGroup K L} (hgen : Subgroup.zpowers τ = ⊤) (α : L) :
    garlingTrace K L hgal α = 0 ↔ ∃ β : L, α = β - τ β := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  constructor
  · intro htr0
    have hn : 1 ≤ n := hdeg ▸ Module.finrank_pos
    have hcardG : Nat.card (L ≃ₐ[K] L) = n := by
      rw [IsGalois.card_aut_eq_finrank K L, hdeg]
    have hτ_ord : orderOf τ = n := by
      rw [← Nat.card_zpowers, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
    have hτ_pow_bij : Function.Bijective (fun k : Fin n => τ ^ (k : ℕ)) := by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by
        rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardG]⟩
      intro a b hab
      have hmod : (a : ℕ) ≡ (b : ℕ) [MOD n] := by
        have h1 := pow_eq_pow_iff_modEq.mp hab
        rwa [hτ_ord] at h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
      exact Fin.ext hmod
    -- Pick z ∈ L with tr(z) = 1 via Exercise 16.10
    obtain ⟨z, hz⟩ := (exercise_16_10 hgal).2.1 1
    have htr_z : ∑ k : Fin n, (τ ^ (k : ℕ)) z = 1 := by
      have h1 := garlingTrace_spec hgal z
      rw [hz, map_one] at h1
      rw [h1]
      exact Equiv.sum_comp (Equiv.ofBijective _ hτ_pow_bij) (fun σ : L ≃ₐ[K] L => σ z)
    let s : ℕ → L := fun k => ∑ i ∈ Finset.range (k + 1), (τ ^ i) α
    have hs_succ : ∀ k : ℕ, s (k + 1) = α + τ (s k) := by
      intro k
      simp only [s]
      conv_lhs => rw [Finset.sum_range_succ']
      rw [pow_zero, AlgEquiv.one_apply, map_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← AlgEquiv.mul_apply, ← pow_succ']
    have hs_last : s (n - 1) = 0 := by
      simp only [s, Nat.sub_add_cancel hn]
      have hsum_fin : (∑ i ∈ Finset.range n, (τ ^ i) α) = ∑ k : Fin n, (τ ^ (k : ℕ)) α :=
        (Fin.sum_univ_eq_sum_range (fun i => (τ ^ i) α) n).symm
      rw [hsum_fin]
      change (∑ i : Fin n, (Equiv.ofBijective _ hτ_pow_bij i) α) = 0
      rw [Equiv.sum_comp (Equiv.ofBijective _ hτ_pow_bij) (fun σ : L ≃ₐ[K] L => σ α),
        ← garlingTrace_spec hgal α, htr0, map_zero]
    let β : L := ∑ k : Fin n, s (k : ℕ) * (τ ^ (k : ℕ)) z
    refine ⟨β, ?_⟩
    have hτβ : τ β = ∑ k : Fin n, τ (s (k : ℕ)) * (τ ^ ((k : ℕ) + 1)) z := by
      simp only [β, map_sum, map_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← AlgEquiv.mul_apply, ← pow_succ']
    have hβ_sub : β - τ β = ∑ k : Fin n, α * (τ ^ (k : ℕ)) z := by
      rw [hτβ]
      have : NeZero n := ⟨Nat.ne_of_gt hn⟩
      let shift : Fin n ≃ Fin n := Equiv.addRight (1 : Fin n)
      rw [← Equiv.sum_comp shift.symm (fun k : Fin n => τ (s (k : ℕ)) * (τ ^ ((k : ℕ) + 1)) z),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsymm : shift.symm k = k - 1 := by simp [shift, sub_eq_add_neg]
      rw [hsymm, fin_sub_one_val k]
      rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
      · have hkz : k = 0 := Fin.ext hk0
        subst hkz
        simp only [Fin.val_zero, ↓reduceIte, hs_last, map_zero, zero_mul, sub_zero]
        simp [s]
      · simp only [Nat.ne_of_gt hkpos, ↓reduceIte]
        rw [Nat.sub_add_cancel hkpos, ← sub_mul]
        have hdiff : s (k : ℕ) - τ (s ((k : ℕ) - 1)) = α := by
          have hstep := hs_succ ((k : ℕ) - 1)
          rw [Nat.sub_add_cancel hkpos] at hstep
          linear_combination hstep
        rw [hdiff]
    rw [hβ_sub, ← Finset.mul_sum, htr_z, mul_one]
  · rintro ⟨β, rfl⟩
    rw [map_sub, garlingTrace_apply_gal hgal τ β, sub_self]

/-- **Counterexample to non-generator `σ` in literal `Exercise 16.14`** (`QUEUE.md` Flag 3):
In `ℂ : ℝ` (cyclic Galois extension of degree `2` generated by complex conjugation), `tr(i) = 0`,
yet for the non-generator `σ = 1 ∈ Γ(ℂ : ℝ)` there is **no** `β ∈ ℂ` with `i = β - σ(β) = 0`. -/
theorem exercise_16_14_unbound_sigma_counterexample :
    IsGarlingGaloisExtension ℝ ℂ ∧
    Module.finrank ℝ ℂ = 2 ∧
    ∀ hgal : IsGarlingGaloisExtension ℝ ℂ,
      garlingTrace ℝ ℂ hgal Complex.I = 0 ∧
      ¬ ∃ β : ℂ, Complex.I = β - (1 : GarlingGaloisGroup ℝ ℂ) β := by
  have hgal : IsGarlingGaloisExtension ℝ ℂ :=
    isGarlingGalois_of_isAlgClosed_of_not_char_dvd_finrank
      (by rw [ringChar.eq_zero, Complex.finrank_real_complex]; simp)
  refine ⟨hgal, Complex.finrank_real_complex, fun hgal' => ?_⟩
  have htrI : garlingTrace ℝ ℂ hgal' Complex.I = 0 := by
    have hconj : Complex.conjAe Complex.I = -Complex.I := by simp
    have heq := garlingTrace_apply_gal hgal' Complex.conjAe Complex.I
    rw [hconj, map_neg] at heq
    linarith
  refine ⟨htrI, ?_⟩
  rintro ⟨β, hβ⟩
  simp only [AlgEquiv.one_apply, sub_self] at hβ
  exact Complex.I_ne_zero hβ

/-! ## §16.4 Kummer extensions (printed pp. 128–130 / PDF pp. 136–138) -/

/-- Helper: for `1 ≤ d`, `x^d - 1` has `d` distinct roots in `K` iff `char K ∤ d` and `K` contains
a primitive `d`th root of unity. -/
theorem has_d_distinct_roots_X_pow_sub_one_iff {K : Type u} [Field K] {d : ℕ} (hd : 1 ≤ d) :
    (Polynomial.X ^ d - 1 : K[X]).roots.toFinset.card = d ↔
      (¬ (ringChar K ∣ d) ∧ ∃ ω : K, IsPrimitiveRoot ω d) := by
  have hXd_ne : (Polynomial.X ^ d - 1 : K[X]) ≠ 0 := by
    simpa [Polynomial.C_1] using (Polynomial.monic_X_pow_sub_C (1 : K) (Nat.ne_of_gt hd)).ne_zero
  constructor
  · intro hcard
    have hndvd : ¬ (ringChar K ∣ d) := by
      intro hdvd
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
      · have _ : CharP K (ringChar K) := ringChar.charP K
        have : Fact (ringChar K).Prime := ⟨hp⟩
        rcases hdvd with ⟨m, hm⟩
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · rw [mul_zero] at hm; omega
          · exact hpos
        have hm_lt : m < d := by have hp2 := hp.two_le; nlinarith
        have hXm_ne : (Polynomial.X ^ m - 1 : K[X]) ≠ 0 := by
          simpa [Polynomial.C_1] using
            (Polynomial.monic_X_pow_sub_C (1 : K) (Nat.ne_of_gt hm_pos)).ne_zero
        have hsub : (Polynomial.X ^ d - 1 : K[X]).roots.toFinset ⊆
            (Polynomial.X ^ m - 1 : K[X]).roots.toFinset := by
          intro r hr
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hXd_ne, Polynomial.IsRoot.def] at hr
          have hr_pow : r ^ d = 1 := by simpa [sub_eq_zero] using hr
          have hpow : (r ^ m - 1) ^ (ringChar K) = 0 := by
            have h1 : ((r ^ m - 1) + 1) ^ (ringChar K) = (r ^ m - 1) ^ (ringChar K) + 1 := by
              rw [add_pow_char, one_pow]
            have h2 : ((r ^ m - 1) + 1) ^ (ringChar K) = 1 := by
              rw [sub_add_cancel, ← pow_mul, mul_comm, ← hm, hr_pow]
            linear_combination h2 - h1
          have hrm : r ^ m = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hXm_ne, Polynomial.IsRoot.def]
          simp [hrm]
        have hle1 : d ≤ (Polynomial.X ^ m - 1 : K[X]).roots.toFinset.card :=
          hcard ▸ Finset.card_le_card hsub
        have hle2 : (Polynomial.X ^ m - 1 : K[X]).roots.toFinset.card ≤
            (Polynomial.X ^ m - 1 : K[X]).roots.card := Multiset.toFinset_card_le _
        have hle3 : (Polynomial.X ^ m - 1 : K[X]).roots.card ≤ m := by
          have h := Polynomial.card_roots' (Polynomial.X ^ m - 1 : K[X])
          have hdegm : (Polynomial.X ^ m - 1 : K[X]).natDegree = m := by
            simpa [Polynomial.C_1] using (Polynomial.natDegree_X_pow_sub_C (n := m) (r := (1 : K)))
          rwa [hdegm] at h
        omega
      · rw [h0] at hdvd
        have := zero_dvd_iff.mp hdvd
        omega
    refine ⟨hndvd, ?_⟩
    -- The d-th roots of unity in K form a finite subgroup U ≤ Kˣ of order d, hence cyclic
    let U : Subgroup Kˣ :=
      { carrier := { u : Kˣ | u ^ d = 1 }
        mul_mem' := fun {a b} ha hb => show (a * b) ^ d = 1 by rw [mul_pow, ha, hb, mul_one]
        one_mem' := one_pow d
        inv_mem' := fun {a} ha => show a⁻¹ ^ d = 1 by rw [inv_pow, ha, inv_one] }
    let eU : U ≃ (Polynomial.X ^ d - 1 : K[X]).roots.toFinset :=
      { toFun := fun u => ⟨(u.1 : K), by
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hXd_ne, Polynomial.IsRoot.def]
          have h1 : (u.1 : K) ^ d = 1 := by
            rw [← Units.val_pow_eq_pow_val, u.2, Units.val_one]
          simp [h1]⟩
        invFun := fun r =>
          have hr_pow : (r.1 : K) ^ d = 1 := by
            have h := r.2
            rw [Multiset.mem_toFinset, Polynomial.mem_roots hXd_ne, Polynomial.IsRoot.def] at h
            simpa [sub_eq_zero] using h
          have hr_ne : (r.1 : K) ≠ 0 := fun h0 => by
            rw [h0, zero_pow (Nat.ne_of_gt hd)] at hr_pow; exact zero_ne_one hr_pow
          ⟨Units.mk0 r.1 hr_ne, by ext; simpa using hr_pow⟩
        left_inv := fun u => Subtype.ext (Units.ext rfl)
        right_inv := fun r => Subtype.ext rfl }
    have _ : Finite U := Finite.of_equiv _ eU.symm
    have hcardU : Nat.card U = d := by
      rw [Nat.card_congr eU, Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
    have hcycU : IsCyclic U :=
      isCyclic_of_injective_ringHom ((Units.coeHom K).comp U.subtype)
        (Units.val_injective.comp Subtype.val_injective)
    obtain ⟨u, hu_gen⟩ := hcycU.exists_generator
    have hu_zpow : Subgroup.zpowers u = ⊤ :=
      eq_top_iff.mpr fun x _ => hu_gen x
    have hu_ord : orderOf u = d := by
      rw [← Nat.card_zpowers, hu_zpow, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardU]
    refine ⟨(u.1 : K), ?_⟩
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨by rw [← Units.val_pow_eq_pow_val, u.2, Units.val_one], fun l hl => ?_⟩
    have hul : u ^ l = 1 := Subtype.ext (Units.ext (by simpa using hl))
    rw [← hu_ord]
    exact orderOf_dvd_of_pow_eq_one hul
  · rintro ⟨_, ω, hω⟩
    have hfac : (Polynomial.X ^ d - 1 : K[X]) = ∏ k : Fin d, (Polynomial.X - Polynomial.C (ω ^ (k : ℕ))) := by
      have h := X_pow_sub_C_pow_eq_prod hd hω (1 : K)
      simpa [one_pow, Polynomial.C_1, mul_one] using h
    have hset : (Polynomial.X ^ d - 1 : K[X]).roots.toFinset =
        Finset.univ.image (fun k : Fin d => ω ^ (k : ℕ)) := by
      ext x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hXd_ne, Polynomial.IsRoot.def, hfac,
        Polynomial.eval_prod, Finset.prod_eq_zero_iff]
      simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero, Finset.mem_image, eq_comm]
    rw [hset, Finset.card_image_of_injective _ fun a b hab => Fin.ext (hω.pow_inj a.isLt b.isLt hab),
      Finset.card_fin]

/-- **Theorem 16.5** (§16.4, printed pp. 128–129 / PDF pp. 136–137):
*"Suppose that `L : K` is a Galois extension, that `Γ(L : K)` is an abelian group of exponent `d`
and that `x^d - 1` has `d` distinct roots in `K`. Then there exist `θ₁, ..., θ_r` in `K` such that
`L : K` is a splitting field extension for `(x^d - θ₁)...(x^d - θ_r)`."* -/
theorem theorem_16_5 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {d : ℕ} (hgal : IsGarlingGaloisExtension K L)
    (hcomm : ∀ σ τ : GarlingGaloisGroup K L, σ * τ = τ * σ)
    (hexp : ∀ [Finite (GarlingGaloisGroup K L)], garlingExponent (GarlingGaloisGroup K L) = d)
    (hroots : (Polynomial.X ^ d - 1 : K[X]).roots.toFinset.card = d) :
    ∃ (r : ℕ) (θ : Fin r → K),
      1 ≤ r ∧
      IsGarlingSplittingFieldExtension K L (∏ j : Fin r, (Polynomial.X ^ d - Polynomial.C (θ j))) := by
  have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  have hexp_eq : garlingExponent (L ≃ₐ[K] L) = d := hexp
  have hexp_props := garlingExponent_and_elemOrder_properties (L ≃ₐ[K] L)
  have hd_pos : 1 ≤ d := hexp_eq ▸ hexp_props.1
  have hpow_d : ∀ σ : L ≃ₐ[K] L, σ ^ d = 1 := hexp_eq ▸ hexp_props.2.1
  obtain ⟨hndvd_d, ω, hω⟩ := (has_d_distinct_roots_X_pow_sub_one_iff hd_pos).mp hroots
  have hωL : IsPrimitiveRoot (algebraMap K L ω) d :=
    hω.map_of_injective (algebraMap K L).injective
  have hωL_ne : algebraMap K L ω ≠ 0 := hωL.ne_zero (Nat.ne_of_gt hd_pos)
  -- Decompose abelian G = Γ(L : K) via Theorem 12.2
  let addCommInst : AddCommGroup (Additive (L ≃ₐ[K] L)) :=
    { (inferInstance : AddGroup (Additive (L ≃ₐ[K] L))) with
      add_comm := fun a b => hcomm (Additive.toMul a) (Additive.toMul b) }
  obtain ⟨s, e, he_gt1, _, ⟨eG⟩, _, _, _, _⟩ := @theorem_12_2 (Additive (L ≃ₐ[K] L)) addCommInst _
  rcases Nat.eq_zero_or_pos s with rfl | hs_pos
  · -- Trivial Galois group: L = K, take r = 1, θ = fun _ => 1
    have hcardG : Nat.card (L ≃ₐ[K] L) = 1 := by
      have hsub : Subsingleton (L ≃ₐ[K] L) :=
        ⟨fun a b => Additive.ofMul.injective (eG.injective (funext fun j => j.elim0))⟩
      exact Nat.card_unique
    have hfin1 : Module.finrank K L = 1 := by
      rw [← IsGalois.card_aut_eq_finrank K L, hcardG]
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq bot_le
        (by rw [IntermediateField.finrank_bot,
          LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfin1])
    refine ⟨1, fun _ => 1, le_rfl, ?_, fun M hM _ => hM (le_antisymm le_top (hbot_top ▸ bot_le))⟩
    rw [Fin.prod_univ_one]
    refine ⟨d, 1, fun k => (algebraMap K L ω) ^ (k : ℕ), ?_⟩
    simp only [GarlingSplitsExplicit, map_one, one_mul,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    have h := X_pow_sub_C_pow_eq_prod hd_pos hωL (1 : L)
    simpa [one_pow, Polynomial.C_1, mul_one] using h
  · -- Nontrivial decomposition: apply Theorem 16.4 to each cyclic quotient M_j = fixedField (ker π_j)
    have hcomp : ∀ j : Fin s,
        ∃ (θj : K) (βj : L),
          βj ≠ 0 ∧
          βj ^ d = algebraMap K L θj ∧
          ∀ (E : IntermediateField K L), βj ∈ E →
            ∀ σ ∈ E.fixingSubgroup, eG (Additive.ofMul σ) j = 0 := by
      intro j
      have _ : NeZero (e j) := ⟨by have := he_gt1 j; omega⟩
      -- Map G →* Multiplicative (ZMod (e j)) via the j-th coordinate of eG and znAddEquivZMod
      let π : (L ≃ₐ[K] L) →* Multiplicative (ZMod (e j)) :=
        { toFun := fun σ => Multiplicative.ofAdd (znAddEquivZMod (e j) (eG (Additive.ofMul σ) j))
          map_one' := by
            change Multiplicative.ofAdd (znAddEquivZMod (e j) (eG 0 j)) = Multiplicative.ofAdd 0
            rw [map_zero, Pi.zero_apply, map_zero]
          map_mul' := fun σ τ => by
            apply congrArg Multiplicative.ofAdd
            change (znAddEquivZMod (e j)) (eG (Additive.ofMul σ + Additive.ofMul τ) j) = _
            rw [map_add, Pi.add_apply, map_add]
            rfl }
      have hπ_surj : Function.Surjective π := by
        intro y
        let z : Zn (e j) := (znAddEquivZMod (e j)).symm (Multiplicative.toAdd y)
        refine ⟨Additive.toMul (eG.symm (Pi.single j z)), ?_⟩
        change Multiplicative.ofAdd (znAddEquivZMod (e j) (eG (eG.symm (Pi.single j z)) j)) = y
        rw [eG.apply_symm_apply, Pi.single_eq_same, AddEquiv.apply_symm_apply]
        rfl
      -- Show e j ∣ d
      have hej_dvd_d : e j ∣ d := by
        obtain ⟨σ₁, hσ₁⟩ := hπ_surj (Multiplicative.ofAdd (1 : ZMod (e j)))
        have h1 : π (σ₁ ^ d) = 1 := by rw [hpow_d σ₁, map_one]
        rw [map_pow, hσ₁] at h1
        change d • (1 : ZMod (e j)) = 0 at h1
        rw [nsmul_eq_mul, mul_one] at h1
        exact (ZMod.natCast_eq_zero_iff d (e j)).mp h1
      -- Fixed field M_j of H_j = ker π is cyclic Galois over K of degree e j
      let H : Subgroup (L ≃ₐ[K] L) := π.ker
      have _ : H.Normal := MonoidHom.normal_ker π
      let M : IntermediateField K L := IntermediateField.fixedField H
      have _ : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
      have hgalM : IsGarlingGaloisExtension K M :=
        (isGarlingGaloisExtension_iff K M).mpr ⟨inferInstance, inferInstance⟩
      let eAut : (M ≃ₐ[K] M) ≃* Multiplicative (ZMod (e j)) :=
        (IsGalois.normalAutEquivQuotient H).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj)
      have hcycZM : IsCyclic (Multiplicative (ZMod (e j))) := by
        refine ⟨Multiplicative.ofAdd (1 : ZMod (e j)), fun x => ?_⟩
        refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
        change (Multiplicative.ofAdd (1 : ZMod (e j))) ^ ((Multiplicative.toAdd x).val : ℤ) = x
        rw [zpow_natCast]
        change ((Multiplicative.toAdd x).val : ℕ) • (1 : ZMod (e j)) = Multiplicative.toAdd x
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      have hcycM : IsGarlingCyclicExtension K M := by
        refine ⟨hgalM, ?_⟩
        obtain ⟨g, hg⟩ := hcycZM.exists_generator
        refine ⟨eAut.symm g, fun x => ?_⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (eAut x))
        exact ⟨k, by change (eAut.symm g) ^ k = x; rw [← map_zpow, hk, eAut.symm_apply_apply]⟩
      have hfinM : Module.finrank K M = e j := by
        rw [← IsGalois.card_aut_eq_finrank K M, Nat.card_congr eAut.toEquiv,
          Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
      have hndvd_ej : ¬ (ringChar K ∣ e j) := fun hd => hndvd_d (hd.trans hej_dvd_d)
      -- Primitive (e j)-th root of unity in K: ω ^ (d / e j)
      have hωj : IsPrimitiveRoot (ω ^ (d / e j)) (e j) := by
        rw [IsPrimitiveRoot.iff_def]
        refine ⟨by rw [← pow_mul, Nat.div_mul_cancel hej_dvd_d, hω.pow_eq_one], fun l hl => ?_⟩
        rw [← pow_mul] at hl
        have hd_dvd : d ∣ (d / e j) * l := hω.dvd_of_pow_eq_one _ hl
        have hq_pos : 0 < d / e j := Nat.div_pos (Nat.le_of_dvd hd_pos hej_dvd_d) (by have := he_gt1 j; omega)
        have hmul : (d / e j) * e j ∣ (d / e j) * l := by rwa [Nat.div_mul_cancel hej_dvd_d]
        exact (mul_dvd_mul_iff_left (Nat.ne_of_gt hq_pos)).mp hmul
      -- Apply Theorem 16.4 to M : K
      obtain ⟨ψ, hirr_ψ, hsf_ψ, _⟩ := theorem_16_4 hcycM hfinM hndvd_ej hωj
      have hsp_ψ := (garlingSplitsOver_iff_splits K M _).mp hsf_ψ.1
      have hne_r : ((Polynomial.X ^ (e j) - Polynomial.C ψ).map (algebraMap K M)).roots ≠ 0 := by
        intro h0
        have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ψ
        rw [h0, Multiset.card_zero,
          Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective,
          Polynomial.natDegree_X_pow_sub_C] at hc
        have := he_gt1 j; omega
      obtain ⟨βM, hβM⟩ := Multiset.exists_mem_of_ne_zero hne_r
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero
          (Polynomial.monic_X_pow_sub_C ψ (by have := he_gt1 j; omega)).ne_zero),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hβM
      let βL : L := (βM : L)
      have hβL_aev : Polynomial.aeval βL (Polynomial.X ^ (e j) - Polynomial.C ψ) = 0 := by
        change Polynomial.aeval (M.val βM) _ = 0
        rw [Polynomial.aeval_algHom_apply, hβM, map_zero]
      have hβL_pow : βL ^ (e j) = algebraMap K L ψ := by
        simpa [sub_eq_zero] using hβL_aev
      have hψ_ne : ψ ≠ 0 := by
        intro h0; subst h0
        have hroot : (Polynomial.X ^ (e j) - Polynomial.C (0 : K)).eval 0 = 0 := by
          simp [zero_pow (by have := he_gt1 j; omega : e j ≠ 0)]
        obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
        rcases hirr_ψ.isUnit_or_isUnit hq_fac with hu1 | hu2
        · rw [Polynomial.isUnit_iff_degree_eq_zero,
            Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
            Polynomial.natDegree_X_sub_C] at hu1
          exact absurd hu1 (by decide)
        · have hq0 : q_fac ≠ 0 := fun h => by
            rw [h, mul_zero] at hq_fac
            exact (Polynomial.monic_X_pow_sub_C (0 : K) (by have := he_gt1 j; omega)).ne_zero hq_fac
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
          have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
          have hdeg := congrArg Polynomial.natDegree hq_fac
          rw [Polynomial.natDegree_X_pow_sub_C,
            Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
            Polynomial.natDegree_X_sub_C, hqd] at hdeg
          have := he_gt1 j; omega
      have hβL_ne : βL ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by have := he_gt1 j; omega)] at hβL_pow
        exact hψ_ne ((algebraMap K L).injective (hβL_pow.symm.trans (map_zero _).symm))
      have hKβ_eq_M : K⟮βL⟯ = M := by
        have hle : K⟮βL⟯ ≤ M := by
          rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
          exact βM.2
        have hmin_eq : minpoly K βL = Polynomial.X ^ (e j) - Polynomial.C ψ :=
          (minpoly.eq_of_irreducible_of_monic hirr_ψ hβL_aev
            (Polynomial.monic_X_pow_sub_C ψ (by have := he_gt1 j; omega))).symm
        refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
        rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral βL), hmin_eq,
          Polynomial.natDegree_X_pow_sub_C, hfinM]
      refine ⟨ψ ^ (d / e j), βL, hβL_ne, ?_, ?_⟩
      · rw [map_pow, ← hβL_pow, ← pow_mul, Nat.mul_div_cancel' hej_dvd_d]
      · intro E hβE σ hσE
        have hM_le_E : M ≤ E := by
          rw [← hKβ_eq_M, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
          exact hβE
        have hσH : σ ∈ H := by
          rw [← IntermediateField.fixingSubgroup_fixedField H,
            IntermediateField.mem_fixingSubgroup_iff]
          intro x hx
          exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσE x (hM_le_E hx)
        have hπ0 : π σ = 1 := hσH
        exact (znAddEquivZMod (e j)).injective
          ((Multiplicative.ofAdd.injective hπ0).trans (map_zero _).symm)
    let θ : Fin s → K := fun j => (hcomp j).choose
    let β : Fin s → L := fun j => (hcomp j).choose_spec.choose
    have hβ_ne : ∀ j : Fin s, β j ≠ 0 := fun j => (hcomp j).choose_spec.choose_spec.1
    have hβ_pow : ∀ j : Fin s, (β j) ^ d = algebraMap K L (θ j) :=
      fun j => (hcomp j).choose_spec.choose_spec.2.1
    have hβ_fix : ∀ j : Fin s, ∀ (E : IntermediateField K L), β j ∈ E →
        ∀ σ ∈ E.fixingSubgroup, eG (Additive.ofMul σ) j = 0 :=
      fun j => (hcomp j).choose_spec.choose_spec.2.2
    let f : K[X] := ∏ j : Fin s, (Polynomial.X ^ d - Polynomial.C (θ j))
    have hf_monic : f.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_pow_sub_C (θ j) (Nat.ne_of_gt hd_pos)
    refine ⟨s, θ, hs_pos, ?_, ?_⟩
    · -- f splits over L because each X^d - θ_j = ∏_k (X - ω^k β_j) splits over L
      rw [garlingSplitsOver_iff_splits]
      rw [Polynomial.map_prod]
      refine Polynomial.Splits.prod fun j _ => ?_
      have hfac_j : (Polynomial.X ^ d - Polynomial.C (θ j)).map (algebraMap K L) =
          ∏ k : Fin d, (Polynomial.X - Polynomial.C ((algebraMap K L ω) ^ (k : ℕ) * β j)) := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hβ_pow j]
        exact X_pow_sub_C_pow_eq_prod hd_pos hωL (β j)
      rw [hfac_j]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    · -- No proper intermediate field E splits f
      intro E hE hspE
      have hsp_ml := (garlingSplitsOver_iff_splits K E f).mp hspE
      have hβ_mem_E : ∀ j : Fin s, β j ∈ E := by
        intro j
        have hdvd_j : (Polynomial.X ^ d - Polynomial.C (θ j)) ∣ f :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
        have hsp_j : ((Polynomial.X ^ d - Polynomial.C (θ j)).map (algebraMap K E)).Splits :=
          hsp_ml.of_dvd (Polynomial.map_ne_zero hf_monic.ne_zero) (Polynomial.map_dvd _ hdvd_j)
        have hne_r : ((Polynomial.X ^ d - Polynomial.C (θ j)).map (algebraMap K E)).roots ≠ 0 := by
          intro h0
          have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_j
          rw [h0, Multiset.card_zero,
            Polynomial.natDegree_map_eq_of_injective (algebraMap K E).injective,
            Polynomial.natDegree_X_pow_sub_C] at hc
          omega
        obtain ⟨γE, hγE⟩ := Multiset.exists_mem_of_ne_zero hne_r
        rw [Polynomial.mem_roots (Polynomial.map_ne_zero
            (Polynomial.monic_X_pow_sub_C (θ j) (Nat.ne_of_gt hd_pos)).ne_zero),
          Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hγE
        have hγL_pow : (γE : L) ^ d = (β j) ^ d := by
          rw [hβ_pow j]
          simpa using congrArg (algebraMap E L) hγE
        have hratio_pow : ((γE : L) * (β j)⁻¹) ^ d = 1 := by
          rw [mul_pow, inv_pow, hγL_pow, mul_inv_cancel₀ (pow_ne_zero d (hβ_ne j))]
        have : NeZero d := ⟨Nat.ne_of_gt hd_pos⟩
        obtain ⟨k, _, hk⟩ := hωL.eq_pow_of_pow_eq_one hratio_pow
        have hβ_eq : β j = ((algebraMap K L ω) ^ k)⁻¹ * (γE : L) := by
          have h1 : (γE : L) = (algebraMap K L ω) ^ k * β j := by
            rw [hk, mul_assoc, inv_mul_cancel₀ (hβ_ne j), mul_one]
          rw [h1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hωL_ne), one_mul]
        rw [hβ_eq]
        exact mul_mem (inv_mem (pow_mem (E.algebraMap_mem ω) k)) γE.2
      have hfix_bot : E.fixingSubgroup = ⊥ := by
        rw [eq_bot_iff]
        intro σ hσ
        rw [Subgroup.mem_bot]
        apply Additive.ofMul.injective
        apply eG.injective
        ext j
        rw [hβ_fix j E (hβ_mem_E j) σ hσ]
        change 0 = eG 0 j
        rw [map_zero, Pi.zero_apply]
      have hE_top : E = ⊤ := by
        rw [← IsGalois.fixedField_fixingSubgroup E, hfix_bot, IntermediateField.fixedField_bot]
      exact hE hE_top

/-- **Inline prose definition of Kummer extension of exponent `d`** (§16.4, printed p. 129 / PDF p.
137; `1 ≤ d` made explicit per `QUEUE.md` Flag 5):
*"An extension `L : K` is called a `Kummer extension of exponent d` if it is a splitting field
extension of a polynomial of the form `(x^d - θ₁)...(x^d - θ_r)` (where `θ₁, ..., θ_r` are in `K`)
and if `x^d - 1` has `d` distinct roots in `K`."* -/
def IsGarlingKummerExtension (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (d : ℕ) : Prop :=
  1 ≤ d ∧
  (Polynomial.X ^ d - 1 : K[X]).roots.toFinset.card = d ∧
  ∃ (r : ℕ) (θ : Fin r → K),
    IsGarlingSplittingFieldExtension K L (∏ j : Fin r, (Polynomial.X ^ d - Polynomial.C (θ j)))

/-- **Zero-exponent Mathlib roots trap for `IsGarlingKummerExtension` / `Theorem 16.6`**
(`QUEUE.md` Flag 5):
At `d = 0`, `X ^ 0 - 1 = 0 : ℚ[X]` evaluates to `0` at every element of `ℚ` (infinitely many
roots), yet Mathlib's junk value `(0 : ℚ[X]).roots = 0` gives
`(X ^ 0 - 1 : ℚ[X]).roots.toFinset.card = 0 = d`, confirming `1 ≤ d` must be stated explicitly. -/
theorem theorem_16_6_zero_exponent_mathlib_trap :
    (Polynomial.X ^ 0 - 1 : ℚ[X]) = 0 ∧
    (Polynomial.X ^ 0 - 1 : ℚ[X]).roots.toFinset.card = 0 ∧
    ∀ x : ℚ, (Polynomial.X ^ 0 - 1 : ℚ[X]).eval x = 0 := by
  refine ⟨by simp, by simp, fun x => by simp⟩

/-- **Theorem 16.6** (§16.4, printed pp. 129–130 / PDF pp. 137–138):
*"Suppose that `L : K` is a Kummer extension of exponent `d`. Then `Γ(L : K)` is abelian, and its
exponent divides `d`."* -/
theorem theorem_16_6 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {d : ℕ} (hkum : IsGarlingKummerExtension K L d) :
    IsGarlingGaloisExtension K L ∧
    (∀ σ τ : GarlingGaloisGroup K L, σ * τ = τ * σ) ∧
    ∀ [Finite (GarlingGaloisGroup K L)], garlingExponent (GarlingGaloisGroup K L) ∣ d := by
  rcases hkum with ⟨hd_pos, hroots, r, θ, hsf⟩
  obtain ⟨hndvd_d, ω, hω⟩ := (has_d_distinct_roots_X_pow_sub_one_iff hd_pos).mp hroots
  have hωL : IsPrimitiveRoot (algebraMap K L ω) d :=
    hω.map_of_injective (algebraMap K L).injective
  have hd_cast_ne : (d : K) ≠ 0 :=
    (pos_and_natCast_ne_zero_of_not_ringChar_dvd hndvd_d).2
  let f : K[X] := ∏ j : Fin r, (Polynomial.X ^ d - Polynomial.C (θ j))
  -- Step 1: Deduplicate nonzero θ_j to obtain a separable polynomial f₁ with the same splitting fields
  let S : Finset K := (Finset.univ.image θ).erase 0
  let f₁ : K[X] := ∏ a ∈ S, (Polynomial.X ^ d - Polynomial.C a)
  have hf₁_monic : f₁.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_pow_sub_C a (Nat.ne_of_gt hd_pos)
  have hf_monic : f.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_pow_sub_C (θ j) (Nat.ne_of_gt hd_pos)
  have hXd_sep : ∀ a : K, a ≠ 0 → (Polynomial.X ^ d - Polynomial.C a : K[X]).Separable := by
    intro a ha
    rw [Polynomial.Separable]
    refine ⟨Polynomial.C (-a⁻¹), Polynomial.C (a⁻¹ * (d : K)⁻¹) * Polynomial.X, ?_⟩
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
    have hX : Polynomial.X * ((d : K[X]) * Polynomial.X ^ (d - 1)) =
        Polynomial.C (d : K) * Polynomial.X ^ d := by
      rw [Polynomial.C_eq_natCast]
      calc Polynomial.X * ((d : K[X]) * Polynomial.X ^ (d - 1))
          = (d : K[X]) * (Polynomial.X ^ (d - 1) * Polynomial.X) := by ring
        _ = (d : K[X]) * Polynomial.X ^ (d - 1 + 1) := by rw [← pow_succ]
        _ = (d : K[X]) * Polynomial.X ^ d := by rw [Nat.sub_add_cancel hd_pos]
    calc Polynomial.C (-a⁻¹) * (Polynomial.X ^ d - Polynomial.C a) +
          Polynomial.C (a⁻¹ * (d : K)⁻¹) * Polynomial.X * ((d : K[X]) * Polynomial.X ^ (d - 1))
        = Polynomial.C (-a⁻¹) * Polynomial.X ^ d - Polynomial.C (-a⁻¹ * a) +
          Polynomial.C (a⁻¹ * (d : K)⁻¹) * (Polynomial.X * ((d : K[X]) * Polynomial.X ^ (d - 1))) := by
            rw [show Polynomial.C (-a⁻¹ * a) = Polynomial.C (-a⁻¹) * Polynomial.C a from Polynomial.C_mul]
            ring
      _ = Polynomial.C (-a⁻¹) * Polynomial.X ^ d - Polynomial.C (-a⁻¹ * a) +
          Polynomial.C (a⁻¹ * (d : K)⁻¹ * (d : K)) * Polynomial.X ^ d := by
            rw [hX, ← mul_assoc, ← Polynomial.C_mul]
      _ = Polynomial.C (-a⁻¹ + a⁻¹ * (d : K)⁻¹ * (d : K)) * Polynomial.X ^ d -
          Polynomial.C (-a⁻¹ * a) := by rw [Polynomial.C_add]; ring
      _ = 1 := by
            rw [mul_assoc a⁻¹, inv_mul_cancel₀ hd_cast_ne, mul_one, neg_add_cancel,
              Polynomial.C_0, zero_mul, zero_sub, neg_mul, inv_mul_cancel₀ ha, map_neg,
              Polynomial.C_1, neg_neg]
  have hf₁_sep : f₁.Separable := by
    have hgen : ∀ T : Finset K, (∀ a ∈ T, a ≠ 0) →
        (∏ a ∈ T, (Polynomial.X ^ d - Polynomial.C a : K[X])).Separable := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; simp [Polynomial.separable_one]
      | insert a T haT ih =>
        intro hne
        rw [Finset.prod_insert haT]
        refine Polynomial.Separable.mul (hXd_sep a (hne a (Finset.mem_insert_self a T)))
          (ih fun b hb => hne b (Finset.mem_insert_of_mem hb)) ?_
        refine IsCoprime.prod_right fun b hb => ?_
        have hab : b - a ≠ 0 := sub_ne_zero.mpr fun h => haT (h ▸ hb)
        refine ⟨Polynomial.C (b - a)⁻¹, Polynomial.C (-(b - a)⁻¹), ?_⟩
        calc Polynomial.C (b - a)⁻¹ * (Polynomial.X ^ d - Polynomial.C a) +
              Polynomial.C (-(b - a)⁻¹) * (Polynomial.X ^ d - Polynomial.C b)
            = Polynomial.C ((b - a)⁻¹ * (b - a)) := by
              simp only [map_neg, map_sub, map_mul]; ring
          _ = 1 := by rw [inv_mul_cancel₀ hab, Polynomial.C_1]
    exact hgen S fun a ha => (Finset.mem_erase.mp ha).1
  have hsp_iff : ∀ M : IntermediateField K L, GarlingSplitsOver K M f ↔ GarlingSplitsOver K M f₁ := by
    intro M
    rw [garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits]
    constructor
    · intro hsp
      rw [Polynomial.map_prod]
      refine Polynomial.Splits.prod fun a ha => ?_
      have ha_img := (Finset.mem_erase.mp ha).2
      rw [Finset.mem_image] at ha_img
      rcases ha_img with ⟨j, _, rfl⟩
      exact hsp.of_dvd (Polynomial.map_ne_zero hf_monic.ne_zero)
        (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
    · intro hsp₁
      rw [Polynomial.map_prod]
      refine Polynomial.Splits.prod fun j _ => ?_
      by_cases hθ0 : θ j = 0
      · rw [hθ0, Polynomial.C_0, sub_zero, Polynomial.map_pow, Polynomial.map_X]
        exact Polynomial.Splits.pow Polynomial.Splits.X d
      · have hmemS : θ j ∈ S := Finset.mem_erase.mpr ⟨hθ0, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
        exact hsp₁.of_dvd (Polynomial.map_ne_zero hf₁_monic.ne_zero)
          (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ hmemS))
  have hsf₁ : IsGarlingSplittingFieldExtension K L f₁ := by
    have hsp_top : GarlingSplitsOver K (⊤ : IntermediateField K L) f₁ :=
      (hsp_iff ⊤).mp (by
        have h1 := hsf.1
        rw [garlingSplitsOver_iff_splits] at h1 ⊢
        have hmap : f.map (algebraMap K (⊤ : IntermediateField K L)) =
            (f.map (algebraMap K L)).map IntermediateField.topEquiv.symm.toRingHom := by
          rw [Polynomial.map_map]; congr 1
        rw [hmap]
        exact h1.map _)
    have hsp_L : GarlingSplitsOver K L f₁ := by
      rw [garlingSplitsOver_iff_splits] at hsp_top ⊢
      have hmap : f₁.map (algebraMap K L) =
          (f₁.map (algebraMap K (⊤ : IntermediateField K L))).map IntermediateField.topEquiv.toRingHom := by
        rw [Polynomial.map_map]; congr 1
      rw [hmap]
      exact hsp_top.map _
    exact ⟨hsp_L, fun M hM hspM => hsf.2 M hM ((hsp_iff M).mpr hspM)⟩
  have hgal : IsGarlingGaloisExtension K L :=
    isGarlingGalois_of_splittingField hf₁_monic.ne_zero hsf₁
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f₁).mp hf₁_sep).2.2
  -- Step 2: Action of Γ(L : K) on every root β of f multiplies by a power of ω (Garling pp. 129–130)
  have hact : ∀ (σ : L ≃ₐ[K] L) (β : garlingRootSet K L f),
      ∃ n : ℕ, σ β.1 = (algebraMap K L ω) ^ n * β.1 := by
    intro σ β
    by_cases hβ0 : β.1 = 0
    · exact ⟨0, by rw [hβ0, map_zero, mul_zero]⟩
    · have hβ_ev : Polynomial.aeval β.1 f = 0 := β.2
      simp only [f, map_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, map_sub,
        map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hβ_ev
      rcases hβ_ev with ⟨j, hβ_pow⟩
      have hσ_pow : (σ β.1) ^ d = β.1 ^ d := by
        rw [← map_pow, hβ_pow, σ.commutes]
      have hratio : (σ β.1 * β.1⁻¹) ^ d = 1 := by
        rw [mul_pow, inv_pow, hσ_pow, mul_inv_cancel₀ (pow_ne_zero d hβ0)]
      have : NeZero d := ⟨Nat.ne_of_gt hd_pos⟩
      obtain ⟨n, _, hn⟩ := hωL.eq_pow_of_pow_eq_one hratio
      refine ⟨n, ?_⟩
      rw [hn, mul_assoc, inv_mul_cancel₀ hβ0, mul_one]
  have hinj := theorem_11_6 hsf
  have hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
    intro σ τ
    apply hinj
    ext β
    change (σ * τ) β.1 = (τ * σ) β.1
    obtain ⟨n₁, hn₁⟩ := hact σ β
    obtain ⟨n₂, hn₂⟩ := hact τ β
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn₂, hn₁, map_mul, map_mul, map_pow, map_pow,
      σ.commutes, τ.commutes, hn₁, hn₂]
    ring
  have hpow_d : ∀ σ : L ≃ₐ[K] L, σ ^ d = 1 := by
    intro σ
    apply hinj
    ext β
    change (σ ^ d) β.1 = (1 : L ≃ₐ[K] L) β.1
    obtain ⟨n, hn⟩ := hact σ β
    have hpow_k : ∀ k : ℕ, (σ ^ k) β.1 = ((algebraMap K L ω) ^ n) ^ k * β.1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, map_pow, σ.commutes, hn,
          ← mul_assoc, ← pow_succ]
    rw [hpow_k d, ← pow_mul, mul_comm n d, pow_mul, hωL.pow_eq_one, one_pow, one_mul,
      AlgEquiv.one_apply]
  refine ⟨hgal, hcomm, fun [_] => ?_⟩
  exact (garlingExponent_and_elemOrder_properties (L ≃ₐ[K] L)).2.2.2.1 d |>.mp hpow_d

/-- **Exercise 16.15** (§16.4, printed p. 130 / PDF p. 138):
*"Suppose that `K` is a field which contains a primitive `n`th root of unity and that `x^n - a` and
`x^n - b` are irreducible over `K`. Show that if `b = a^r c^n` for some `r` which is prime to `n`
and some `c` in `K`, then `x^n - a` and `x^n - b` have the same splitting field extension over
`K`."* -/
theorem exercise_16_15 {K : Type u} [Field K] {n r : ℕ} {ω a b c : K}
    (hω : IsPrimitiveRoot ω n)
    (hirr_a : Irreducible (Polynomial.X ^ n - Polynomial.C a : K[X]))
    (hirr_b : Irreducible (Polynomial.X ^ n - Polynomial.C b : K[X]))
    (hcop : Nat.Coprime r n) (hb : b = a ^ r * c ^ n) :
    ∀ (L : Type v) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C a) ↔
      IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C b) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exfalso
      have hconst : (Polynomial.X ^ 0 - Polynomial.C a : K[X]) = Polynomial.C (1 - a) := by
        simp [Polynomial.C_sub]
      rw [hconst] at hirr_a
      by_cases h0 : 1 - a = 0
      · rw [h0, map_zero] at hirr_a; exact hirr_a.ne_zero rfl
      · exact hirr_a.not_isUnit (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr h0))
    · exact hpos
  -- Core one-way lemma for n ≥ 2: if b = a^r * c^n (with both X^n - a, X^n - b irreducible), then
  -- any splitting field of X^n - a is also a splitting field of X^n - b.
  have hfwd : ∀ (a' b' c' : K) (r' : ℕ),
      2 ≤ n →
      Irreducible (Polynomial.X ^ n - Polynomial.C a' : K[X]) →
      Irreducible (Polynomial.X ^ n - Polynomial.C b' : K[X]) →
      b' = a' ^ r' * c' ^ n →
      ∀ (L : Type v) [Field L] [Algebra K L],
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C a') →
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C b') := by
    intro a' b' c' r' hn2 hirr_a' hirr_b' hb' L _ _ hsf_a'
    have hωL : IsPrimitiveRoot (algebraMap K L ω) n :=
      hω.map_of_injective (algebraMap K L).injective
    have hωL_ne : algebraMap K L ω ≠ 0 := hωL.ne_zero (by omega)
    have hne_zero_of_irr : ∀ u : K, Irreducible (Polynomial.X ^ n - Polynomial.C u : K[X]) → u ≠ 0 := by
      intro u hu h0; subst h0
      have hroot : (Polynomial.X ^ n - Polynomial.C (0 : K)).eval 0 = 0 := by
        simp [zero_pow (by omega : n ≠ 0)]
      obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      rcases hu.isUnit_or_isUnit hq_fac with hu1 | hu2
      · rw [Polynomial.isUnit_iff_degree_eq_zero,
          Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
          Polynomial.natDegree_X_sub_C] at hu1
        exact absurd hu1 (by decide)
      · have hq0 : q_fac ≠ 0 := fun h => by
          rw [h, mul_zero] at hq_fac
          exact (Polynomial.monic_X_pow_sub_C (0 : K) (by omega)).ne_zero hq_fac
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
        have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
        have hdeg := congrArg Polynomial.natDegree hq_fac
        rw [Polynomial.natDegree_X_pow_sub_C,
          Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
          Polynomial.natDegree_X_sub_C, hqd] at hdeg
        omega
    have ha'_ne : a' ≠ 0 := hne_zero_of_irr a' hirr_a'
    have hb'_ne : b' ≠ 0 := hne_zero_of_irr b' hirr_b'
    -- Pick a root α ∈ L of X^n - a'
    have hsp_a' := (garlingSplitsOver_iff_splits K L _).mp hsf_a'.1
    have hne_r : ((Polynomial.X ^ n - Polynomial.C a').map (algebraMap K L)).roots ≠ 0 := by
      intro h0
      have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_a'
      rw [h0, Multiset.card_zero,
        Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
        Polynomial.natDegree_X_pow_sub_C] at hc
      omega
    obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hne_r
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Polynomial.monic_X_pow_sub_C a' (by omega)).ne_zero),
      Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hα
    have hα_pow : α ^ n = algebraMap K L a' := by simpa [sub_eq_zero] using hα
    have hα_ne : α ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by omega)] at hα_pow
      exact ha'_ne ((algebraMap K L).injective (hα_pow.symm.trans (map_zero _).symm))
    -- L = K⟮α⟯ and [L : K] = n
    have hKα_top : K⟮α⟯ = ⊤ := by
      by_contra hne
      refine hsf_a'.2 K⟮α⟯ hne ?_
      rw [garlingSplitsOver_iff_splits]
      have hω_Kα : IsPrimitiveRoot (algebraMap K K⟮α⟯ ω) n :=
        hω.map_of_injective (algebraMap K K⟮α⟯).injective
      have hfac := X_pow_sub_C_pow_eq_prod hn hω_Kα (⟨α, IntermediateField.mem_adjoin_simple_self K α⟩ : K⟮α⟯)
      have hpow_Kα : (⟨α, IntermediateField.mem_adjoin_simple_self K α⟩ : K⟮α⟯) ^ n =
          algebraMap K K⟮α⟯ a' := Subtype.ext (by simpa using hα_pow)
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hpow_Kα, hfac]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    have hα_int : IsIntegral K α := ⟨Polynomial.X ^ n - Polynomial.C a',
      Polynomial.monic_X_pow_sub_C a' (by omega), hα⟩
    have hmin_α : minpoly K α = Polynomial.X ^ n - Polynomial.C a' :=
      (minpoly.eq_of_irreducible_of_monic hirr_a' hα (Polynomial.monic_X_pow_sub_C a' (by omega))).symm
    have hfinL : Module.finrank K L = n := by
      rw [← LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, ← hKα_top,
        IntermediateField.adjoin.finrank hα_int, hmin_α, Polynomial.natDegree_X_pow_sub_C]
    -- Construct root β = α^r' * c' ∈ L of X^n - b'
    let β : L := α ^ r' * algebraMap K L c'
    have hβ_pow : β ^ n = algebraMap K L b' := by
      show (α ^ r' * algebraMap K L c') ^ n = algebraMap K L b'
      rw [mul_pow, ← pow_mul, mul_comm r' n, pow_mul, hα_pow, ← map_pow, ← map_pow, ← map_mul, hb']
    have hβ_aev : Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C b') = 0 := by
      simp [hβ_pow]
    have hβ_ne : β ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by omega)] at hβ_pow
      exact hb'_ne ((algebraMap K L).injective (hβ_pow.symm.trans (map_zero _).symm))
    have hβ_int : IsIntegral K β := ⟨Polynomial.X ^ n - Polynomial.C b',
      Polynomial.monic_X_pow_sub_C b' (by omega), hβ_aev⟩
    have hmin_β : minpoly K β = Polynomial.X ^ n - Polynomial.C b' :=
      (minpoly.eq_of_irreducible_of_monic hirr_b' hβ_aev (Polynomial.monic_X_pow_sub_C b' (by omega))).symm
    have _ : FiniteDimensional K L := by
      have : FiniteDimensional K K⟮α⟯ := IntermediateField.adjoin.finiteDimensional hα_int
      exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv.symm.trans
        (IntermediateField.equivOfEq hKα_top.symm)).symm.toLinearEquiv
    have hKβ_top : K⟮β⟯ = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq le_top (by
        rw [IntermediateField.adjoin.finrank hβ_int, hmin_β, Polynomial.natDegree_X_pow_sub_C,
          LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, hfinL])
    refine ⟨?_, ?_⟩
    · rw [garlingSplitsOver_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, ← hβ_pow, X_pow_sub_C_pow_eq_prod hn hωL β]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    · intro M hM hspM
      have hsp_ml := (garlingSplitsOver_iff_splits K M _).mp hspM
      have hne_rM : ((Polynomial.X ^ n - Polynomial.C b').map (algebraMap K M)).roots ≠ 0 := by
        intro h0
        have hc := Polynomial.Splits.natDegree_eq_card_roots hsp_ml
        rw [h0, Multiset.card_zero,
          Polynomial.natDegree_map_eq_of_injective (algebraMap K M).injective,
          Polynomial.natDegree_X_pow_sub_C] at hc
        omega
      obtain ⟨γM, hγM⟩ := Multiset.exists_mem_of_ne_zero hne_rM
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Polynomial.monic_X_pow_sub_C b' (by omega)).ne_zero),
        Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
        map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hγM
      have hγL_pow : (γM : L) ^ n = β ^ n := by
        rw [hβ_pow]; simpa using congrArg (algebraMap M L) hγM
      have hratio : ((γM : L) * β⁻¹) ^ n = 1 := by
        rw [mul_pow, inv_pow, hγL_pow, mul_inv_cancel₀ (pow_ne_zero n hβ_ne)]
      have : NeZero n := ⟨by omega⟩
      obtain ⟨k, _, hk⟩ := hωL.eq_pow_of_pow_eq_one hratio
      have hβ_mem_M : β ∈ M := by
        have hβ_eq : β = ((algebraMap K L ω) ^ k)⁻¹ * (γM : L) := by
          have h1 : (γM : L) = (algebraMap K L ω) ^ k * β := by
            rw [hk, mul_assoc, inv_mul_cancel₀ hβ_ne, mul_one]
          rw [h1, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hωL_ne), one_mul]
        rw [hβ_eq]
        exact mul_mem (inv_mem (pow_mem (M.algebraMap_mem ω) k)) γM.2
      have htop_le : (⊤ : IntermediateField K L) ≤ M := by
        rw [← hKβ_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hβ_mem_M
      exact hM (le_antisymm le_top htop_le)
  intro L _ _
  rcases eq_or_lt_of_le hn with rfl | hn2
  · -- n = 1: both X - a and X - b split over every intermediate field, so both hold iff ⊥ = ⊤
    have hsf_lin : ∀ u : K,
        IsGarlingSplittingFieldExtension K L (Polynomial.X ^ 1 - Polynomial.C u) ↔
          (⊥ : IntermediateField K L) = ⊤ := by
      intro u
      have hsp_all : ∀ M : IntermediateField K L, GarlingSplitsOver K M (Polynomial.X ^ 1 - Polynomial.C u) := by
        intro M
        rw [garlingSplitsOver_iff_splits, pow_one, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        exact Polynomial.Splits.X_sub_C _
      constructor
      · intro hsf
        by_contra hne
        exact hsf.2 ⊥ hne (hsp_all ⊥)
      · intro hbot
        refine ⟨?_, fun M hM _ => hM (le_antisymm le_top (hbot ▸ bot_le))⟩
        rw [garlingSplitsOver_iff_splits, pow_one, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        exact Polynomial.Splits.X_sub_C _
    rw [hsf_lin a, hsf_lin b]
  · -- n ≥ 2: invert r mod n via ZMod.unitOfCoprime to get a = b^s * d^n
    constructor
    · exact hfwd a b c r hn2 hirr_a hirr_b hb L
    · have : NeZero n := ⟨by omega⟩
      let u : (ZMod n)ˣ := ZMod.unitOfCoprime r hcop
      let s : ℕ := ((u⁻¹ : (ZMod n)ˣ) : ZMod n).val
      have hrs_mod : r * s ≡ 1 [MOD n] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        have h1 : (r : ZMod n) * (s : ZMod n) = 1 := by
          change (u : ZMod n) * (((u⁻¹ : (ZMod n)ˣ) : ZMod n).val : ZMod n) = 1
          rw [ZMod.natCast_zmod_val, Units.mul_inv]
        simpa using h1
      have hrs_pos : 1 ≤ r * s := by
        by_contra h0
        have hzero : r * s = 0 := by omega
        rw [hzero, Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt hn2] at hrs_mod
        omega
      have hdvd_rs : n ∣ r * s - 1 := (Nat.modEq_iff_dvd' hrs_pos).mp hrs_mod.symm
      rcases hdvd_rs with ⟨t, ht⟩
      have hrs_eq : r * s = 1 + n * t := by omega
      have ha_ne : a ≠ 0 := by
        intro h0; subst h0
        have hroot : (Polynomial.X ^ n - Polynomial.C (0 : K)).eval 0 = 0 := by
          simp [zero_pow (by omega : n ≠ 0)]
        obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
        rcases hirr_a.isUnit_or_isUnit hq_fac with hu1 | hu2
        · rw [Polynomial.isUnit_iff_degree_eq_zero,
            Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
            Polynomial.natDegree_X_sub_C] at hu1
          exact absurd hu1 (by decide)
        · have hq0 : q_fac ≠ 0 := fun h => by
            rw [h, mul_zero] at hq_fac
            exact (Polynomial.monic_X_pow_sub_C (0 : K) (by omega)).ne_zero hq_fac
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
          have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
          have hdeg := congrArg Polynomial.natDegree hq_fac
          rw [Polynomial.natDegree_X_pow_sub_C,
            Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
            Polynomial.natDegree_X_sub_C, hqd] at hdeg
          omega
      have hb_ne : b ≠ 0 := by
        intro h0; subst h0
        have hroot : (Polynomial.X ^ n - Polynomial.C (0 : K)).eval 0 = 0 := by
          simp [zero_pow (by omega : n ≠ 0)]
        obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
        rcases hirr_b.isUnit_or_isUnit hq_fac with hu1 | hu2
        · rw [Polynomial.isUnit_iff_degree_eq_zero,
            Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
            Polynomial.natDegree_X_sub_C] at hu1
          exact absurd hu1 (by decide)
        · have hq0 : q_fac ≠ 0 := fun h => by
            rw [h, mul_zero] at hq_fac
            exact (Polynomial.monic_X_pow_sub_C (0 : K) (by omega)).ne_zero hq_fac
          rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
          have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
          have hdeg := congrArg Polynomial.natDegree hq_fac
          rw [Polynomial.natDegree_X_pow_sub_C,
            Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
            Polynomial.natDegree_X_sub_C, hqd] at hdeg
          omega
      have hc_ne : c ≠ 0 := by
        intro h0; rw [h0, zero_pow (by omega), mul_zero] at hb; exact hb_ne hb
      let dK : K := (a ^ t * c ^ s)⁻¹
      have ha_eq : a = b ^ s * dK ^ n := by
        have hdenom_ne : a ^ t * c ^ s ≠ 0 := mul_ne_zero (pow_ne_zero t ha_ne) (pow_ne_zero s hc_ne)
        have hbs : b ^ s = a * (a ^ t * c ^ s) ^ n := by
          rw [hb, mul_pow, ← pow_mul, hrs_eq, pow_add, pow_one, mul_pow, ← pow_mul, ← pow_mul,
            mul_comm t n, mul_comm n s]
          ring
        simp only [dK, inv_pow, hbs, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hdenom_ne), mul_one]
      exact hfwd b a dK s hn2 hirr_b hirr_a ha_eq L

/-- **Edge-case counterexample to requiring positive `r ≥ 1` in `Exercise 16.16` at `n = 1`**
(`QUEUE.md` Flag 5):
Over `K = ℚ`, `1` is a primitive `1`st root of unity, `x - 0` and `x - 1` are irreducible with the
same splitting field `ℚ : ℚ`, yet there is **no** positive `r ≥ 1` and `c ∈ ℚ` with
`1 = 0 ^ r * c ^ 1` (whereas `r = 0`, which satisfies `Nat.Coprime 0 1`, gives `1 = 0 ^ 0 * 1 ^ 1`). -/
theorem exercise_16_16_n1_pos_r_counterexample :
    IsPrimitiveRoot (1 : ℚ) 1 ∧
    Irreducible (Polynomial.X ^ 1 - Polynomial.C (0 : ℚ)) ∧
    Irreducible (Polynomial.X ^ 1 - Polynomial.C (1 : ℚ)) ∧
    ¬ ∃ (r : ℕ) (c : ℚ), 1 ≤ r ∧ (1 : ℚ) = (0 : ℚ) ^ r * c ^ 1 := by
  refine ⟨IsPrimitiveRoot.one, ?_, ?_, ?_⟩
  · simpa using Polynomial.irreducible_X_sub_C (0 : ℚ)
  · simpa using Polynomial.irreducible_X_sub_C (1 : ℚ)
  · rintro ⟨r, c, hr, heq⟩
    rw [zero_pow (by omega), zero_mul] at heq
    exact one_ne_zero heq

/-- **Exercise 16.16** (§16.4, printed p. 130 / PDF p. 138; unconditional for all `n` with `r : ℕ`,
`Nat.Coprime r n` — see `exercise_16_16_pos_r` for `1 ≤ r < n` when `2 ≤ n` and
`exercise_16_16_n1_pos_r_counterexample` for the `n = 1, a = 0` boundary per `QUEUE.md` Flag 5):
*"Suppose `K` is a field which contains a primitive `n`th root of unity, and that `x^n - a` and
`x^n - b` are irreducible polynomials over `K` with the same splitting field extension `L : K`. Let
`α` be a root of `x^n - a` in `L`, `β` a root of `x^n - b`. By considering the action of `Γ(L : K)`
on `α` and `β`, show that there exists `r`, prime to `n`, such that `β α^{-r} ∈ K`. Show that
`b = a^r c^n` for some `c` in `K`."* -/
theorem exercise_16_16 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {ω a b : K} (hω : IsPrimitiveRoot ω n)
    (hirr_a : Irreducible (Polynomial.X ^ n - Polynomial.C a : K[X]))
    (hirr_b : Irreducible (Polynomial.X ^ n - Polynomial.C b : K[X]))
    (hsf_a : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C a))
    (hsf_b : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C b))
    {α β : L} (hα : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C a) = 0)
    (hβ : Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C b) = 0) :
    ∃ (r : ℕ) (c : K),
      Nat.Coprime r n ∧
      algebraMap K L c = β * (α ^ r)⁻¹ ∧
      b = a ^ r * c ^ n := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exfalso
      have hconst : (Polynomial.X ^ 0 - Polynomial.C a : K[X]) = Polynomial.C (1 - a) := by
        simp [Polynomial.C_sub]
      rw [hconst] at hirr_a
      by_cases h0 : 1 - a = 0
      · rw [h0, map_zero] at hirr_a; exact hirr_a.ne_zero rfl
      · exact hirr_a.not_isUnit (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr h0))
    · exact hpos
  rcases eq_or_lt_of_le hn with rfl | hn2
  · -- n = 1: r = 0, c = b works unconditionally (even when a = 0)
    have hβ_eq : β = algebraMap K L b := by simpa [sub_eq_zero] using hβ
    refine ⟨0, b, (Nat.coprime_zero_left 1).mpr rfl, ?_, by simp⟩
    simp [hβ_eq]
  · -- n ≥ 2: Galois action of Γ(L : K) on α and β
    have hndvd : ¬ (ringChar K ∣ n) := not_ringChar_dvd_of_isPrimitiveRoot hn hω
    have hn_cast_ne : (n : K) ≠ 0 := (pos_and_natCast_ne_zero_of_not_ringChar_dvd hndvd).2
    have hne_zero_of_irr : ∀ u : K, Irreducible (Polynomial.X ^ n - Polynomial.C u : K[X]) → u ≠ 0 := by
      intro u hu h0; subst h0
      have hroot : (Polynomial.X ^ n - Polynomial.C (0 : K)).eval 0 = 0 := by
        simp [zero_pow (by omega : n ≠ 0)]
      obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      rcases hu.isUnit_or_isUnit hq_fac with hu1 | hu2
      · rw [Polynomial.isUnit_iff_degree_eq_zero,
          Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
          Polynomial.natDegree_X_sub_C] at hu1
        exact absurd hu1 (by decide)
      · have hq0 : q_fac ≠ 0 := fun h => by
          rw [h, mul_zero] at hq_fac
          exact (Polynomial.monic_X_pow_sub_C (0 : K) (by omega)).ne_zero hq_fac
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
        have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
        have hdeg := congrArg Polynomial.natDegree hq_fac
        rw [Polynomial.natDegree_X_pow_sub_C,
          Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
          Polynomial.natDegree_X_sub_C, hqd] at hdeg
        omega
    have ha_ne : a ≠ 0 := hne_zero_of_irr a hirr_a
    have hb_ne : b ≠ 0 := hne_zero_of_irr b hirr_b
    have hα_pow : α ^ n = algebraMap K L a := by simpa [sub_eq_zero] using hα
    have hβ_pow : β ^ n = algebraMap K L b := by simpa [sub_eq_zero] using hβ
    have hα_ne : α ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by omega)] at hα_pow
      exact ha_ne ((algebraMap K L).injective (hα_pow.symm.trans (map_zero _).symm))
    have hβ_ne : β ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by omega)] at hβ_pow
      exact hb_ne ((algebraMap K L).injective (hβ_pow.symm.trans (map_zero _).symm))
    have hωL : IsPrimitiveRoot (algebraMap K L ω) n :=
      hω.map_of_injective (algebraMap K L).injective
    have hωL_ne : algebraMap K L ω ≠ 0 := hωL.ne_zero (by omega)
    -- Show L : K is Galois of degree n, with K⟮α⟯ = ⊤ and K⟮β⟯ = ⊤
    have hkum : IsGarlingKummerExtension K L n :=
      ⟨hn, (has_d_distinct_roots_X_pow_sub_one_iff hn).mpr ⟨hndvd, ω, hω⟩,
        1, fun _ => a, by simpa [Fin.prod_univ_one] using hsf_a⟩
    have hgal : IsGarlingGaloisExtension K L := (theorem_16_6 hkum).1
    have _ : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
    have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
    have hKα_top : K⟮α⟯ = ⊤ := by
      by_contra hne
      refine hsf_a.2 K⟮α⟯ hne ?_
      rw [garlingSplitsOver_iff_splits]
      have hω_Kα : IsPrimitiveRoot (algebraMap K K⟮α⟯ ω) n :=
        hω.map_of_injective (algebraMap K K⟮α⟯).injective
      have hpow_Kα : (⟨α, IntermediateField.mem_adjoin_simple_self K α⟩ : K⟮α⟯) ^ n =
          algebraMap K K⟮α⟯ a := Subtype.ext (by simpa using hα_pow)
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hpow_Kα,
        X_pow_sub_C_pow_eq_prod hn hω_Kα _]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    have hKβ_top : K⟮β⟯ = ⊤ := by
      by_contra hne
      refine hsf_b.2 K⟮β⟯ hne ?_
      rw [garlingSplitsOver_iff_splits]
      have hω_Kβ : IsPrimitiveRoot (algebraMap K K⟮β⟯ ω) n :=
        hω.map_of_injective (algebraMap K K⟮β⟯).injective
      have hpow_Kβ : (⟨β, IntermediateField.mem_adjoin_simple_self K β⟩ : K⟮β⟯) ^ n =
          algebraMap K K⟮β⟯ b := Subtype.ext (by simpa using hβ_pow)
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hpow_Kβ,
        X_pow_sub_C_pow_eq_prod hn hω_Kβ _]
      exact Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _
    have hfinL : Module.finrank K L = n := by
      have hmin_α : minpoly K α = Polynomial.X ^ n - Polynomial.C a :=
        (minpoly.eq_of_irreducible_of_monic hirr_a hα (Polynomial.monic_X_pow_sub_C a (by omega))).symm
      rw [← LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv, ← hKα_top,
        IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin_α,
        Polynomial.natDegree_X_pow_sub_C]
    have hcardG : Nat.card (L ≃ₐ[K] L) = n := by
      rw [IsGalois.card_aut_eq_finrank K L, hfinL]
    -- Define isomorphism φ : Γ(L : K) ≃* Multiplicative (ZMod n) via σ(α) = ω^{k(σ)} α
    have : NeZero n := ⟨by omega⟩
    have hact_α : ∀ σ : L ≃ₐ[K] L, ∃ k : ℕ, k < n ∧ σ α = (algebraMap K L ω) ^ k * α := by
      intro σ
      have hratio : (σ α * α⁻¹) ^ n = 1 := by
        rw [mul_pow, inv_pow, ← map_pow, hα_pow, σ.commutes,
          mul_inv_cancel₀ ((map_ne_zero (algebraMap K L)).mpr ha_ne)]
      obtain ⟨k, hk_lt, hk⟩ := hωL.eq_pow_of_pow_eq_one hratio
      exact ⟨k, hk_lt, by rw [hk, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]⟩
    let kα : (L ≃ₐ[K] L) → ℕ := fun σ => (hact_α σ).choose
    have hkα_lt : ∀ σ, kα σ < n := fun σ => (hact_α σ).choose_spec.1
    have hkα_spec : ∀ σ, σ α = (algebraMap K L ω) ^ (kα σ) * α := fun σ => (hact_α σ).choose_spec.2
    let φ : (L ≃ₐ[K] L) →* Multiplicative (ZMod n) :=
      { toFun := fun σ => Multiplicative.ofAdd ((kα σ : ZMod n))
        map_one' := by
          have h1 := hkα_spec 1
          rw [AlgEquiv.one_apply] at h1
          have hpow1 : (algebraMap K L ω) ^ kα 1 = 1 :=
            mul_right_cancel₀ hα_ne (h1.symm.trans (one_mul α).symm)
          have hk0 : kα 1 = 0 := by
            have hd := hωL.dvd_of_pow_eq_one _ hpow1
            by_contra hne
            exact not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) (hkα_lt 1)
          simp [hk0]
        map_mul' := fun σ₁ σ₂ => by
          apply congrArg Multiplicative.ofAdd
          have h12 : (σ₁ * σ₂) α = (algebraMap K L ω) ^ (kα σ₁ + kα σ₂) * α := by
            rw [AlgEquiv.mul_apply, hkα_spec σ₂, map_mul, map_pow, σ₁.commutes, hkα_spec σ₁,
              ← mul_assoc, mul_comm ((algebraMap K L ω) ^ kα σ₂), ← pow_add]
          have hpow_eq : (algebraMap K L ω) ^ kα (σ₁ * σ₂) =
              (algebraMap K L ω) ^ (kα σ₁ + kα σ₂) :=
            mul_right_cancel₀ hα_ne ((hkα_spec (σ₁ * σ₂)).symm.trans h12)
          have hmod : kα (σ₁ * σ₂) ≡ kα σ₁ + kα σ₂ [MOD n] := by
            rcases le_total (kα (σ₁ * σ₂)) (kα σ₁ + kα σ₂) with hle | hle
            · have hdiff : (algebraMap K L ω) ^ (kα σ₁ + kα σ₂ - kα (σ₁ * σ₂)) = 1 := by
                apply mul_left_cancel₀ (pow_ne_zero (kα (σ₁ * σ₂)) hωL_ne)
                rw [← pow_add, Nat.add_sub_of_le hle, mul_one, hpow_eq]
              exact (Nat.modEq_iff_dvd' hle).mpr (hωL.dvd_of_pow_eq_one _ hdiff)
            · have hdiff : (algebraMap K L ω) ^ (kα (σ₁ * σ₂) - (kα σ₁ + kα σ₂)) = 1 := by
                apply mul_left_cancel₀ (pow_ne_zero (kα σ₁ + kα σ₂) hωL_ne)
                rw [← pow_add, Nat.add_sub_of_le hle, mul_one, hpow_eq.symm]
              exact ((Nat.modEq_iff_dvd' hle).mpr (hωL.dvd_of_pow_eq_one _ hdiff)).symm
          change ((kα (σ₁ * σ₂) : ℕ) : ZMod n) = ((kα σ₁ : ℕ) : ZMod n) + ((kα σ₂ : ℕ) : ZMod n)
          rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
          exact hmod }
    have hφ_inj : Function.Injective φ := by
      intro σ₁ σ₂ hEq
      have hmod : kα σ₁ ≡ kα σ₂ [MOD n] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp (Multiplicative.ofAdd.injective hEq)
      rw [Nat.ModEq, Nat.mod_eq_of_lt (hkα_lt σ₁), Nat.mod_eq_of_lt (hkα_lt σ₂)] at hmod
      have hα_eq : σ₁ α = σ₂ α := by rw [hkα_spec σ₁, hkα_spec σ₂, hmod]
      let Eeq : IntermediateField K L :=
        { (AlgHom.equalizer σ₁.toAlgHom σ₂.toAlgHom) with
          inv_mem' := fun {x} hx => by
            change σ₁ x⁻¹ = σ₂ x⁻¹; rw [map_inv₀, map_inv₀]; exact congrArg Inv.inv hx }
      have htop_le : (⊤ : IntermediateField K L) ≤ Eeq := by
        rw [← hKα_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hα_eq
      ext x; exact htop_le IntermediateField.mem_top
    have hφ_bij : Function.Bijective φ := by
      let _ : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hφ_inj, ?_⟩
      rw [← Nat.card_eq_fintype_card, hcardG, ← Nat.card_eq_fintype_card,
        Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
    let eφ : (L ≃ₐ[K] L) ≃* Multiplicative (ZMod n) := MulEquiv.ofBijective φ hφ_bij
    -- Generator τ = eφ⁻¹(1) satisfies τ(α) = ω * α and generates Γ(L : K)
    let τ : L ≃ₐ[K] L := eφ.symm (Multiplicative.ofAdd (1 : ZMod n))
    have hτ_α : τ α = algebraMap K L ω * α := by
      have h1 : (kα τ : ZMod n) = 1 := Multiplicative.ofAdd.injective (eφ.apply_symm_apply _)
      have hmod : kα τ ≡ 1 [MOD n] := (ZMod.natCast_eq_natCast_iff (kα τ) 1 n).mp (by simpa using h1)
      rw [Nat.ModEq, Nat.mod_eq_of_lt (hkα_lt τ), Nat.mod_eq_of_lt hn2] at hmod
      rw [hkα_spec τ, hmod, pow_one]
    have hτ_gen : Subgroup.zpowers τ = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨((Multiplicative.toAdd (eφ σ)).val : ℤ), ?_⟩
      apply eφ.injective
      rw [map_zpow, eφ.apply_symm_apply, zpow_natCast]
      change ((Multiplicative.toAdd (eφ σ)).val : ℕ) • (1 : ZMod n) = Multiplicative.toAdd (eφ σ)
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    have hτ_ord : orderOf τ = n := by
      rw [← Nat.card_zpowers, hτ_gen, Nat.card_congr Subgroup.topEquiv.toEquiv, hcardG]
    -- Action of τ on β: τ(β) = ω^r * β with r < n
    have hratio_β : (τ β * β⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, hβ_pow, τ.commutes,
        mul_inv_cancel₀ ((map_ne_zero (algebraMap K L)).mpr hb_ne)]
    obtain ⟨r, hr_lt, hr_eq⟩ := hωL.eq_pow_of_pow_eq_one hratio_β
    have hτ_β : τ β = (algebraMap K L ω) ^ r * β := by
      rw [hr_eq, mul_assoc, inv_mul_cancel₀ hβ_ne, mul_one]
    -- Show Nat.Coprime r n using K⟮β⟯ = ⊤
    have hcop : Nat.Coprime r n := by
      let g := Nat.gcd r n
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right r (by omega)
      have hg_dvd_r : g ∣ r := Nat.gcd_dvd_left r n
      have hg_dvd_n : g ∣ n := Nat.gcd_dvd_right r n
      let m := n / g
      have hrm_dvd : n ∣ r * m := by
        rcases hg_dvd_r with ⟨r', hr'⟩
        refine ⟨r', ?_⟩
        calc r * m = (g * r') * (n / g) := by rw [hr']
          _ = (g * (n / g)) * r' := by ring
          _ = n * r' := by rw [Nat.mul_div_cancel' hg_dvd_n]
      have hτm_β : (τ ^ m) β = β := by
        have hpow_k : ∀ k : ℕ, (τ ^ k) β = ((algebraMap K L ω) ^ r) ^ k * β := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, map_pow, τ.commutes, hτ_β,
              ← mul_assoc, ← pow_succ]
        rw [hpow_k m, ← pow_mul]
        rcases hrm_dvd with ⟨q, hq⟩
        rw [hq, pow_mul, hωL.pow_eq_one, one_pow, one_mul]
      have hτm_eq1 : τ ^ m = 1 := by
        let Eeq : IntermediateField K L :=
          { (AlgHom.equalizer (τ ^ m).toAlgHom (1 : L ≃ₐ[K] L).toAlgHom) with
            inv_mem' := fun {x} hx => by
              change (τ ^ m) x⁻¹ = x⁻¹; rw [map_inv₀]; exact congrArg Inv.inv hx }
        have htop_le : (⊤ : IntermediateField K L) ≤ Eeq := by
          rw [← hKβ_top, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hτm_β
        ext x; exact htop_le IntermediateField.mem_top
      have hn_dvd_m : n ∣ m := hτ_ord ▸ orderOf_dvd_of_pow_eq_one hτm_eq1
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hg_dvd_n) hg_pos
      have hn_le_m : n ≤ m := Nat.le_of_dvd hm_pos hn_dvd_m
      have hg_eq1 : g = 1 := by
        have hgm : g * m = n := Nat.mul_div_cancel' hg_dvd_n
        nlinarith
      exact hg_eq1
    -- Show β * (α ^ r)⁻¹ is fixed by τ, hence equals algebraMap K L c for some c ∈ K
    have hfix : τ (β * (α ^ r)⁻¹) = β * (α ^ r)⁻¹ := by
      rw [map_mul, map_inv₀, map_pow, hτ_β, hτ_α, mul_pow, mul_inv]
      calc (algebraMap K L ω) ^ r * β * (((algebraMap K L ω) ^ r)⁻¹ * (α ^ r)⁻¹)
          = ((algebraMap K L ω) ^ r * ((algebraMap K L ω) ^ r)⁻¹) * (β * (α ^ r)⁻¹) := by ring
        _ = β * (α ^ r)⁻¹ := by rw [mul_inv_cancel₀ (pow_ne_zero r hωL_ne), one_mul]
    obtain ⟨c, hc⟩ :=
      mem_range_algebraMap_of_forall_gal_fix (forall_gal_fix_of_gen_fix hτ_gen hfix)
    refine ⟨r, c, hcop, hc, ?_⟩
    apply (algebraMap K L).injective
    rw [map_mul, map_pow, map_pow, hc, mul_pow, inv_pow, ← pow_mul, mul_comm r n, pow_mul,
      hα_pow, hβ_pow, ← map_pow]
    have ha_r_ne : algebraMap K L (a ^ r) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr (pow_ne_zero r ha_ne)
    rw [mul_comm (algebraMap K L b), ← mul_assoc, mul_inv_cancel₀ ha_r_ne, one_mul]

/-- Positive-`r` companion to **`Exercise 16.16`** for `2 ≤ n` (§16.4, printed p. 130 / PDF p. 138):
whenever `2 ≤ n`, `r` can be chosen with `1 ≤ r`, `r < n`, and `Nat.Coprime r n`. -/
theorem exercise_16_16_pos_r {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hn2 : 2 ≤ n) {ω a b : K} (hω : IsPrimitiveRoot ω n)
    (hirr_a : Irreducible (Polynomial.X ^ n - Polynomial.C a : K[X]))
    (hirr_b : Irreducible (Polynomial.X ^ n - Polynomial.C b : K[X]))
    (hsf_a : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C a))
    (hsf_b : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ n - Polynomial.C b))
    {α β : L} (hα : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C a) = 0)
    (hβ : Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C b) = 0) :
    ∃ (r : ℕ) (c : K),
      1 ≤ r ∧ r < n ∧ Nat.Coprime r n ∧
      algebraMap K L c = β * (α ^ r)⁻¹ ∧
      b = a ^ r * c ^ n := by
  obtain ⟨r₀, c₀, hcop₀, hc₀, hb₀⟩ := exercise_16_16 hω hirr_a hirr_b hsf_a hsf_b hα hβ
  let r := r₀ % n
  let q := r₀ / n
  have hr_lt : r < n := Nat.mod_lt r₀ (by omega)
  have hr0_eq : r₀ = r + n * q := by
    simpa [r, q, add_comm] using (Nat.div_add_mod r₀ n).symm
  have hcop : Nat.Coprime r n := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hdvd1 : Nat.gcd r n ∣ r₀ := by
      rw [hr0_eq]
      exact dvd_add (Nat.gcd_dvd_left r n) (dvd_mul_of_dvd_left (Nat.gcd_dvd_right r n) q)
    have hdvd2 : Nat.gcd r n ∣ Nat.gcd r₀ n := Nat.dvd_gcd hdvd1 (Nat.gcd_dvd_right r n)
    rw [hcop₀.gcd_eq_one] at hdvd2
    exact Nat.eq_one_of_dvd_one hdvd2
  have hr_pos : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    rw [hr0, Nat.coprime_zero_left] at hcop
    omega
  have ha_ne : a ≠ 0 := by
    intro h0; subst h0
    have hroot : (Polynomial.X ^ n - Polynomial.C (0 : K)).eval 0 = 0 := by
      simp [zero_pow (by omega : n ≠ 0)]
    obtain ⟨q_fac, hq_fac⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    rcases hirr_a.isUnit_or_isUnit hq_fac with hu1 | hu2
    · rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree (Polynomial.X_sub_C_ne_zero _),
        Polynomial.natDegree_X_sub_C] at hu1
      exact absurd hu1 (by decide)
    · have hq0 : q_fac ≠ 0 := fun h => by
        rw [h, mul_zero] at hq_fac
        exact (Polynomial.monic_X_pow_sub_C (0 : K) (by omega)).ne_zero hq_fac
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0] at hu2
      have hqd : q_fac.natDegree = 0 := Nat.cast_injective hu2
      have hdeg := congrArg Polynomial.natDegree hq_fac
      rw [Polynomial.natDegree_X_pow_sub_C,
        Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq0,
        Polynomial.natDegree_X_sub_C, hqd] at hdeg
      omega
  have hα_pow : α ^ n = algebraMap K L a := by simpa [sub_eq_zero] using hα
  let c : K := a ^ q * c₀
  refine ⟨r, c, hr_pos, hr_lt, hcop, ?_, ?_⟩
  · have hα_nq : α ^ (n * q) = algebraMap K L (a ^ q) := by
      rw [pow_mul, hα_pow, map_pow]
    have hα_nq_ne : algebraMap K L (a ^ q) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr (pow_ne_zero q ha_ne)
    rw [show c = a ^ q * c₀ from rfl, map_mul, hc₀, hr0_eq, pow_add, mul_inv, hα_nq]
    calc algebraMap K L (a ^ q) * (β * ((α ^ r)⁻¹ * (algebraMap K L (a ^ q))⁻¹))
        = (algebraMap K L (a ^ q) * (algebraMap K L (a ^ q))⁻¹) * (β * (α ^ r)⁻¹) := by ring
      _ = β * (α ^ r)⁻¹ := by rw [mul_inv_cancel₀ hα_nq_ne, one_mul]
  · simp only [c, mul_pow, ← pow_mul, mul_comm q n]
    rw [hb₀, hr0_eq, pow_add]
    ring

end Garling.Chapter16

