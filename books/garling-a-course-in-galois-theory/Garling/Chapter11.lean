import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter06
import Garling.Chapter07
import Garling.Chapter08
import Garling.Chapter09
import Garling.Chapter10
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.Aut
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chapter 11: Automorphisms and fixed fields

Formalization of Chapter 11 (*Automorphisms and fixed fields*, printed pp. 91–100 / PDF pp. 99–108)
of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
4-paragraph unnumbered chapter preamble, all five sections (`§11.1`–`§11.5`), all 10 main-text
theorem/corollary items (`Theorem 11.1`–`Theorem 11.9` + `Corollary` [to `Theorem 11.1`]), all 12
numbered exercises (`Exercise 11.1`–`Exercise 11.12`), and all unnumbered prose definitions,
auxiliary lemmas, and worked examples in exact source order.
-/

namespace Garling.Chapter11

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter08 Garling.Chapter09 Garling.Chapter10
open scoped BigOperators Polynomial IntermediateField Matrix

universe u v w

/-! ## Chapter 11 Preamble: `Aut L`, Fixed Field `φ(A)`, and Galois Group `Γ(L:K)` / `γ(K)` (p. 91) -/

/-- Garling's prose definition of `Aut L` (Chapter 11 preamble, printed p. 91 / PDF p. 99):
*"If `L` is a field, we denote by `Aut L` the set of all automorphisms of `L`. `Aut L` is a group
under the usual law of composition."* -/
abbrev GarlingAut (L : Type u) [Field L] : Type u := L ≃+* L

/-- Exact bijection between `GarlingAut L` (`L ≃+* L`) and Chapter 4's field-automorphism subtype
`{τ : L →+* L | IsFieldAutomorphism τ}` (§4.5, p. 48). -/
noncomputable def garlingAutEquivIsFieldAutomorphism (L : Type u) [Field L] :
    GarlingAut L ≃ {τ : L →+* L | IsFieldAutomorphism τ} where
  toFun σ := ⟨σ.toRingHom, σ.injective, σ.surjective⟩
  invFun τ := RingEquiv.ofBijective τ.1 ⟨τ.2.1, τ.2.2⟩
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl

/-- Garling's prose definition of the *fixed field* `φ(A)` of a subset `A ⊆ Aut L`
(Chapter 11 preamble, printed p. 91 / PDF p. 99):
`φ(A) = {k ∈ L : σ(k) = k for each σ in A}`, equipped as a subfield of `L`. -/
def garlingPhi {L : Type u} [Field L] (A : Set (GarlingAut L)) : Subfield L where
  carrier := {k : L | ∀ σ ∈ A, σ k = k}
  mul_mem' {a b} ha hb σ hσ := by rw [map_mul, ha σ hσ, hb σ hσ]
  one_mem' σ _ := map_one σ
  add_mem' {a b} ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  zero_mem' σ _ := map_zero σ
  neg_mem' {a} ha σ hσ := by rw [map_neg, ha σ hσ]
  inv_mem' {a} ha σ hσ := by rw [map_inv₀, ha σ hσ]

@[simp]
theorem mem_garlingPhi_iff {L : Type u} [Field L] {A : Set (GarlingAut L)} {k : L} :
    k ∈ garlingPhi A ↔ ∀ σ ∈ A, σ k = k := Iff.rfl

/-- Garling's prose definition of the *Galois group* `γ(K) = Γ(L:K)` of an extension `L : K`
when `K` is a subfield of `L` (Chapter 11 preamble, printed p. 91 / PDF p. 99):
`Γ(L:K) = {σ ∈ Aut L : σ(k) = k for all k in K}`, equipped as a subgroup of `Aut L`. -/
def garlingGamma {L : Type u} [Field L] (K : Subfield L) : Subgroup (GarlingAut L) where
  carrier := {σ : GarlingAut L | ∀ k ∈ K, σ k = k}
  mul_mem' {σ τ} hσ hτ k hk := by
    change σ (τ k) = k
    rw [hτ k hk, hσ k hk]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ k hk := by
    have h := congrArg σ.symm (hσ k hk)
    simpa using h.symm

@[simp]
theorem mem_garlingGamma_iff {L : Type u} [Field L] {K : Subfield L} {σ : GarlingAut L} :
    σ ∈ garlingGamma K ↔ ∀ k ∈ K, σ k = k := Iff.rfl

/-- The Galois group `Γ(L:K)` as a subgroup of `Aut L` for an arbitrary `[Algebra K L]` extension
(identifying `K` with `(algebraMap K L).fieldRange : Subfield L` per §4.2, p. 40). -/
def garlingGaloisSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Subgroup (GarlingAut L) :=
  garlingGamma (algebraMap K L).fieldRange

@[simp]
theorem mem_garlingGaloisSubgroup_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {σ : GarlingAut L} :
    σ ∈ garlingGaloisSubgroup K L ↔ ∀ k : K, σ (algebraMap K L k) = algebraMap K L k := by
  simp only [garlingGaloisSubgroup, mem_garlingGamma_iff, RingHom.mem_fieldRange,
    forall_exists_index, forall_apply_eq_imp_iff]

/-- Bundled `K`-algebra automorphism group `Γ(L:K) = (L ≃ₐ[K] L)` for an extension `L : K`. -/
abbrev GarlingGaloisGroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Type v :=
  L ≃ₐ[K] L

/-- Canonical group isomorphism between `GarlingGaloisGroup K L` (`L ≃ₐ[K] L`) and the subgroup
`garlingGaloisSubgroup K L ≤ GarlingAut L`. -/
def garlingGaloisGroupMulEquiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    GarlingGaloisGroup K L ≃* garlingGaloisSubgroup K L where
  toFun σ := ⟨σ.toRingEquiv, mem_garlingGaloisSubgroup_iff.mpr fun k => σ.commutes k⟩
  invFun τ := AlgEquiv.ofRingEquiv (f := τ.1) (mem_garlingGaloisSubgroup_iff.mp τ.2)
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ₁ σ₂ := by ext x; rfl

/-- Specialization of `garlingGaloisGroupMulEquiv` to a subfield `K : Subfield L`:
`GarlingGaloisGroup K L ≃* garlingGamma K`. -/
def garlingGaloisGroupSubfieldMulEquiv {L : Type u} [Field L] (K : Subfield L) :
    GarlingGaloisGroup K L ≃* garlingGamma K where
  toFun σ := ⟨σ.toRingEquiv, fun k hk => σ.commutes ⟨k, hk⟩⟩
  invFun τ := AlgEquiv.ofRingEquiv (f := τ.1) (fun k => τ.2 k.1 k.2)
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ₁ σ₂ := by ext x; rfl

/-! ## §11.1 Fixed fields and Galois groups (printed pp. 91–94, PDF pp. 99–102) -/

/-- Inclusion-reversal of `φ` noted in the polarity discussion and proof of `Theorem 11.1`
(§11.1, printed pp. 91–92): if `A₁ ⊆ A₂ ⊆ Aut L`, then `φ(A₁) ≥ φ(A₂)`. -/
theorem garlingPhi_anti {L : Type u} [Field L] {A₁ A₂ : Set (GarlingAut L)} (h : A₁ ⊆ A₂) :
    garlingPhi A₂ ≤ garlingPhi A₁ :=
  fun _ hk σ hσ => hk σ (h hσ)

/-- Inclusion-reversal of `γ` noted in the polarity discussion and proof of `Theorem 11.1`
(§11.1, printed pp. 91–92): if `K₁ ≤ K₂` are subfields of `L`, then `γ(K₁) ≥ γ(K₂)`. -/
theorem garlingGamma_anti {L : Type u} [Field L] {K₁ K₂ : Subfield L} (h : K₁ ≤ K₂) :
    garlingGamma K₂ ≤ garlingGamma K₁ :=
  fun _ hσ k hk => hσ k (h hk)

/-- **Theorem 11.1** (§11.1, printed p. 91 / PDF p. 99; proof p. 92 / PDF p. 100):
*"Suppose that `L : K` is an extension, and that `A` is an [sic] subset of `Aut L`.
(i) `γφ(A) ⊇ A`;
(ii) `φγ(K) ⊇ K`;
(iii) `φγφ(A) = φ(A)`;
(iv) `γφγ(K) = γ(K)`."* -/
theorem theorem_11_1 {L : Type u} [Field L] (K : Subfield L) (A : Set (GarlingAut L)) :
    (A ⊆ (garlingGamma (garlingPhi A) : Set (GarlingAut L))) ∧
    (K ≤ garlingPhi (garlingGamma K : Set (GarlingAut L))) ∧
    (garlingPhi (garlingGamma (garlingPhi A) : Set (GarlingAut L)) = garlingPhi A) ∧
    (garlingGamma (garlingPhi (garlingGamma K : Set (GarlingAut L))) = garlingGamma K) := by
  have hi : ∀ B : Set (GarlingAut L), B ⊆ (garlingGamma (garlingPhi B) : Set (GarlingAut L)) :=
    fun _ σ hσ k hk => hk σ hσ
  have hii : ∀ F : Subfield L, F ≤ garlingPhi (garlingGamma F : Set (GarlingAut L)) :=
    fun _ k hk σ hσ => hσ k hk
  refine ⟨hi A, hii K, ?_, ?_⟩
  · exact le_antisymm (garlingPhi_anti (hi A)) (hii (garlingPhi A))
  · exact le_antisymm (garlingGamma_anti (hii K)) (hi (garlingGamma K : Set (GarlingAut L)))

/-- `[Algebra K L]` companion to **Theorem 11.1** (§11.1, p. 91), identifying `K` with its embedded
subfield `(algebraMap K L).fieldRange ≤ L`. -/
theorem theorem_11_1_algebra (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : Set (GarlingAut L)) :
    (A ⊆ (garlingGamma (garlingPhi A) : Set (GarlingAut L))) ∧
    ((algebraMap K L).fieldRange ≤ garlingPhi (garlingGaloisSubgroup K L : Set (GarlingAut L))) ∧
    (garlingPhi (garlingGamma (garlingPhi A) : Set (GarlingAut L)) = garlingPhi A) ∧
    (garlingGamma (garlingPhi (garlingGaloisSubgroup K L : Set (GarlingAut L))) =
      garlingGaloisSubgroup K L) :=
  theorem_11_1 (algebraMap K L).fieldRange A

/-- **Corollary** [to Theorem 11.1] (§11.1, printed p. 92 / PDF p. 100):
*"If `A` is a subset of `Aut L`, and `⟨A⟩` is the subgroup of `Aut L` generated by `A`, then
`φ(A) = φ(⟨A⟩)`."*

Proved directly from `Theorem 11.1 (i)` and `(iii)` following Garling's 2-line deduction on p. 92:
`A ⊆ ⟨A⟩ ⊆ γφ(A)` gives `φ(A) ≥ φ(⟨A⟩) ≥ φγφ(A) = φ(A)`. -/
theorem corollary_to_theorem_11_1 {L : Type u} [Field L] (A : Set (GarlingAut L)) :
    garlingPhi A = garlingPhi (Subgroup.closure A : Set (GarlingAut L)) := by
  have h1 := theorem_11_1 (⊥ : Subfield L) A
  have hcl_le : Subgroup.closure A ≤ garlingGamma (garlingPhi A) :=
    (Subgroup.closure_le (garlingGamma (garlingPhi A))).mpr h1.1
  apply le_antisymm
  · rw [← h1.2.2.1]
    exact garlingPhi_anti hcl_le
  · exact garlingPhi_anti Subgroup.subset_closure

/-- Garling's prose definition of the *trajectory* `T(λ) = {σ(λ)}_{σ ∈ G} ∈ L^G`
(§11.1, printed p. 92 / PDF p. 100):
for a subgroup `G ≤ Aut L` and `λ ∈ L`, `T(λ)` is the family `σ ↦ σ(λ)` in the function space
`FunSpace G L` (`G → L`). -/
def garlingTrajectory {L : Type u} [Field L] (G : Subgroup (GarlingAut L)) (lam : L) :
    FunSpace G L :=
  fun σ => σ.1 lam

@[simp]
theorem garlingTrajectory_apply {L : Type u} [Field L] (G : Subgroup (GarlingAut L))
    (lam : L) (σ : G) :
    garlingTrajectory G lam σ = σ.1 lam := rfl

/-- Evaluating a trajectory at `1 ∈ G` recovers `λ`, so `λ ↦ T(λ)` is injective. -/
theorem garlingTrajectory_injective {L : Type u} [Field L] (G : Subgroup (GarlingAut L)) :
    Function.Injective (garlingTrajectory G) := by
  intro a b hab
  have h1 := congrFun hab ⟨1, G.one_mem⟩
  simpa [garlingTrajectory] using h1

/-- **Theorem 11.2** (§11.1, printed p. 92 / PDF p. 100; proof pp. 92–93 / PDF pp. 100–101):
*"Suppose that `G` is a subgroup of `Aut L`, that `K` is the fixed field of `G` and that `B` is a
subset of `L`. Then the following are equivalent:
(i) `B` is linearly independent over `K`;
(ii) `{T(β) : β ∈ B}` is linearly independent over `K`;
(iii) `{T(β) : β ∈ B}` is linearly independent over `L`."*

Proved directly via Garling's minimal-length `L`-linear dependence elimination argument on p. 93
using Chapter 1's subset `IsLinearlyIndependent`. -/
theorem theorem_11_2 {L : Type u} [Field L] (G : Subgroup (GarlingAut L)) (B : Set L) :
    let K : Subfield L := garlingPhi (G : Set (GarlingAut L))
    let TB : Set (FunSpace G L) := garlingTrajectory G '' B
    (IsLinearlyIndependent K B ↔ IsLinearlyIndependent K TB) ∧
    (IsLinearlyIndependent K TB ↔ IsLinearlyIndependent L TB) := by
  intro K TB
  have h3_imp_2 : IsLinearlyIndependent L TB → IsLinearlyIndependent K TB := by
    intro h3 ⟨n, v, c, hv_inj, hvTB, ⟨i₀, hc₀⟩, hsum⟩
    refine h3 ⟨n, v, fun i => (c i : L), hv_inj, hvTB, ⟨i₀, ?_⟩, ?_⟩
    · exact fun h0 => hc₀ (Subtype.ext h0)
    · ext σ
      have hσ := congrFun hsum σ
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hσ ⊢
      exact hσ
  have h2_imp_1 : IsLinearlyIndependent K TB → IsLinearlyIndependent K B := by
    intro h2 ⟨n, β, c, hβ_inj, hβB, hnz, hsum⟩
    refine h2 ⟨n, fun i => garlingTrajectory G (β i), c, ?_, ?_, hnz, ?_⟩
    · exact (garlingTrajectory_injective G).comp hβ_inj
    · exact fun i => ⟨β i, hβB i, rfl⟩
    · ext σ
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, garlingTrajectory_apply]
      have hfix : ∀ i, σ.1 (c i : L) = (c i : L) := fun i => (c i).2 σ.1 σ.2
      have hlin : (∑ i : Fin n, (c i : L) * σ.1 (β i)) =
          σ.1 (∑ i : Fin n, (c i : L) * β i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, hfix i]
      have hsumL : (∑ i : Fin n, (c i : L) * β i) = 0 := hsum
      simpa [Subfield.smul_def] using (hlin.trans (by rw [hsumL, map_zero]))
  have h1_imp_3 : IsLinearlyIndependent K B → IsLinearlyIndependent L TB := by
    intro h1 hdep3
    classical
    have hex : ∃ r : ℕ, ∃ (β : Fin r → L) (lam : Fin r → L),
        0 < r ∧ Function.Injective β ∧ (∀ i, β i ∈ B) ∧ (∀ i, lam i ≠ 0) ∧
        ∑ i : Fin r, lam i • garlingTrajectory G (β i) = 0 := by
      rcases hdep3 with ⟨n, v, c, hv_inj, hvTB, ⟨i₀, hc₀⟩, hsum⟩
      let S : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
      have hS_nonempty : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc₀⟩⟩
      let e : Fin S.card ≃ S := S.equivFin.symm
      have hb_ex : ∀ j : Fin S.card, ∃ b ∈ B, garlingTrajectory G b = v (e j).1 :=
        fun j => hvTB (e j).1
      choose β hβB hβv using hb_ex
      refine ⟨S.card, β, fun j => c (e j).1, Finset.card_pos.mpr hS_nonempty, ?_, hβB, ?_, ?_⟩
      · intro j₁ j₂ hj
        have hv_eq : v (e j₁).1 = v (e j₂).1 := by rw [← hβv j₁, ← hβv j₂, hj]
        exact e.injective (Subtype.ext (hv_inj hv_eq))
      · intro j
        exact (Finset.mem_filter.mp (e j).2).2
      · have hsum_S : (∑ i ∈ S, c i • v i) = 0 := by
          rw [← hsum]
          refine Finset.sum_subset (Finset.subset_univ S) ?_
          intro i _ hiS
          have hci : c i = 0 := by
            by_contra hne
            exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
          rw [hci, zero_smul]
        calc (∑ j : Fin S.card, c (e j).1 • garlingTrajectory G (β j))
            = ∑ j : Fin S.card, c (e j).1 • v (e j).1 := by
              refine Finset.sum_congr rfl fun j _ => by rw [hβv j]
          _ = ∑ x : S, c x.1 • v x.1 := Equiv.sum_comp e (fun x : S => c x.1 • v x.1)
          _ = ∑ i ∈ S, c i • v i := S.sum_coe_sort (fun i => c i • v i)
          _ = 0 := hsum_S
    have hspec : ∃ (β : Fin (Nat.find hex) → L) (lam : Fin (Nat.find hex) → L),
        0 < Nat.find hex ∧ Function.Injective β ∧ (∀ i, β i ∈ B) ∧ (∀ i, lam i ≠ 0) ∧
        ∑ i, lam i • garlingTrajectory G (β i) = 0 := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex, ¬ ∃ (β : Fin k → L) (lam : Fin k → L),
        0 < k ∧ Function.Injective β ∧ (∀ i, β i ∈ B) ∧ (∀ i, lam i ≠ 0) ∧
        ∑ i, lam i • garlingTrajectory G (β i) = 0 := fun k hk => Nat.find_min hex hk
    generalize Nat.find hex = r at hspec hmin
    obtain ⟨β, lam, hr_pos, hβ_inj, hβB, hlam_nz, hsum⟩ := hspec
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr_pos)
    have hstar : ∀ σ : G, ∑ i : Fin (m + 1), lam i * σ.1 (β i) = 0 := by
      intro σ
      have h := congrFun hsum σ
      simpa [Finset.sum_apply, Pi.smul_apply, garlingTrajectory_apply] using h
    have hstar2 : ∀ τ σ : G, ∑ i : Fin (m + 1), τ.1 (lam i) * σ.1 (β i) = 0 := by
      intro τ σ
      have h := hstar (τ⁻¹ * σ)
      have hτ := congrArg τ.1 h
      rw [map_sum, map_zero] at hτ
      rw [← hτ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]
      congr 1
      exact (τ.1.apply_symm_apply (σ.1 (β i))).symm
    let lastIdx : Fin (m + 1) := Fin.last m
    have hcomb : ∀ τ : G,
        ∑ j : Fin m,
          (τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx) •
            garlingTrajectory G (β j.castSucc) = 0 := by
      intro τ
      ext σ
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, garlingTrajectory_apply,
        smul_eq_mul]
      have h1' := congrArg (fun x => τ.1 (lam lastIdx) * x) (hstar σ)
      have h2' := congrArg (fun x => lam lastIdx * x) (hstar2 τ σ)
      simp only [Finset.mul_sum, mul_zero] at h1' h2'
      rw [Fin.sum_univ_castSucc] at h1' h2'
      have hdiff :
          (∑ j : Fin m, τ.1 (lam lastIdx) * (lam j.castSucc * σ.1 (β j.castSucc)) +
            τ.1 (lam lastIdx) * (lam lastIdx * σ.1 (β lastIdx))) -
          (∑ j : Fin m, lam lastIdx * (τ.1 (lam j.castSucc) * σ.1 (β j.castSucc)) +
            lam lastIdx * (τ.1 (lam lastIdx) * σ.1 (β lastIdx))) = 0 := by
        rw [h1', h2', sub_self]
      rw [← hdiff]
      have hring :
          (∑ j : Fin m,
            (τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx) *
              σ.1 (β j.castSucc)) =
          (∑ j : Fin m, τ.1 (lam lastIdx) * (lam j.castSucc * σ.1 (β j.castSucc))) -
          (∑ j : Fin m, lam lastIdx * (τ.1 (lam j.castSucc) * σ.1 (β j.castSucc))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hring]
      ring
    have hcoeff_zero : ∀ (τ : G) (j : Fin m),
        τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx = 0 := by
      intro τ j₀
      by_contra hne
      let S' : Finset (Fin m) := Finset.univ.filter
        (fun j => τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx ≠ 0)
      have hS'_ne : S'.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
      let e' : Fin S'.card ≃ S' := S'.equivFin.symm
      have hcard_lt : S'.card < m + 1 := by
        have hle : S'.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
        rw [Finset.card_fin] at hle
        omega
      refine hmin S'.card hcard_lt ⟨fun k => β (e' k).1.castSucc,
        fun k => τ.1 (lam lastIdx) * lam (e' k).1.castSucc -
          τ.1 (lam (e' k).1.castSucc) * lam lastIdx,
        Finset.card_pos.mpr hS'_ne, ?_, fun k => hβB _, ?_, ?_⟩
      · intro k₁ k₂ hk
        exact e'.injective (Subtype.ext (Fin.castSucc_injective m (hβ_inj hk)))
      · intro k
        exact (Finset.mem_filter.mp (e' k).2).2
      · have hsum_S' :
            (∑ j ∈ S',
              (τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx) •
                garlingTrajectory G (β j.castSucc)) = 0 := by
          rw [← hcomb τ]
          refine Finset.sum_subset (Finset.subset_univ S') ?_
          intro j _ hjS'
          have hz : τ.1 (lam lastIdx) * lam j.castSucc -
              τ.1 (lam j.castSucc) * lam lastIdx = 0 := by
            by_contra hnz'
            exact hjS' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz'⟩)
          rw [hz, zero_smul]
        calc _ = ∑ x : S',
              (τ.1 (lam lastIdx) * lam x.1.castSucc - τ.1 (lam x.1.castSucc) * lam lastIdx) •
                garlingTrajectory G (β x.1.castSucc) :=
              Equiv.sum_comp e' _
          _ = _ := S'.sum_coe_sort (fun j : Fin m =>
              (τ.1 (lam lastIdx) * lam j.castSucc - τ.1 (lam j.castSucc) * lam lastIdx) •
                garlingTrajectory G (β j.castSucc))
          _ = 0 := hsum_S'
    have hk_mem : ∀ j : Fin m, (lam lastIdx)⁻¹ * lam j.castSucc ∈ K := by
      intro j τ hτ
      have hcz : τ (lam lastIdx) * lam j.castSucc = τ (lam j.castSucc) * lam lastIdx :=
        sub_eq_zero.mp (hcoeff_zero ⟨τ, hτ⟩ j)
      have hlr_ne : lam lastIdx ≠ 0 := hlam_nz lastIdx
      have hτlr_ne : τ (lam lastIdx) ≠ 0 :=
        fun h0 => hlr_ne (τ.injective (h0.trans (map_zero τ).symm))
      rw [map_mul, map_inv₀]
      field_simp [hlr_ne, hτlr_ne]
      linear_combination -hcz
    let cK : Fin (m + 1) → K :=
      Fin.snoc (fun j => ⟨(lam lastIdx)⁻¹ * lam j.castSucc, hk_mem j⟩) 1
    refine (h1 ⟨m + 1, β, cK, hβ_inj, hβB, ⟨lastIdx, ?_⟩, ?_⟩).elim
    · simp [cK, lastIdx]
    · have h1G : ∑ i : Fin (m + 1), lam i * β i = 0 := hstar ⟨1, G.one_mem⟩
      have hmul := congrArg (fun x => (lam lastIdx)⁻¹ * x) h1G
      simp only [Finset.mul_sum, mul_zero] at hmul
      rw [Fin.sum_univ_castSucc] at hmul ⊢
      change (∑ j : Fin m, (cK j.castSucc : L) * β j.castSucc) + (cK lastIdx : L) * β lastIdx = 0
      simp only [cK, lastIdx, Fin.snoc_castSucc, Fin.snoc_last, OneMemClass.coe_one, one_mul]
      rw [← hmul]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [lastIdx]
        ring
      · dsimp only [lastIdx]
        rw [inv_mul_cancel_left₀ (hlam_nz (Fin.last m))]
  exact ⟨⟨fun h1 => h3_imp_2 (h1_imp_3 h1), h2_imp_1⟩,
    ⟨fun h2 => h1_imp_3 (h2_imp_1 h2), h3_imp_2⟩⟩

/-- Mathlib `LinearIndepOn` companion to **Theorem 11.2** (§11.1, p. 92). -/
theorem theorem_11_2_linearIndepOn {L : Type u} [Field L] (G : Subgroup (GarlingAut L))
    (B : Set L) :
    let K : Subfield L := garlingPhi (G : Set (GarlingAut L))
    let TB : Set (FunSpace G L) := garlingTrajectory G '' B
    (LinearIndepOn K id B ↔ LinearIndepOn K id TB) ∧
    (LinearIndepOn K id TB ↔ LinearIndepOn L id TB) := by
  intro K TB
  rw [← isLinearlyIndependent_iff, ← isLinearlyIndependent_iff, ← isLinearlyIndependent_iff]
  exact theorem_11_2 G B

/-- **Theorem 11.3** (§11.1, printed p. 93 / PDF p. 101; proof pp. 93–94 / PDF pp. 101–102):
*"Suppose that `G` is a finite subgroup of `Aut L`. Then `|G| = [L : φ(G)]`, `G = γφ(G)` and
`L : φ(G)` is a Galois extension."*

Proved directly following Garling's deduction on pp. 93–94 from `Theorem 11.2` (bounding `|B| ≤ |G|`
in `L^G`), `Chapter 2` (`exists_basis`), `Theorem 10.4` (`|γφ(G)| ≤ [L : K]`), and `Theorem 11.1 (i)`
(`G ≤ γφ(G)`). -/
theorem theorem_11_3 {L : Type u} [Field L] (G : Subgroup (GarlingAut L)) [Finite G] :
    let K : Subfield L := garlingPhi (G : Set (GarlingAut L))
    IsFiniteExtension K L ∧
    setOrder G = extDegree K L ∧
    Nat.card G = Module.finrank K L ∧
    G = garlingGamma K ∧
    IsGarlingGaloisExtension K L := by
  classical
  intro K
  let _ : Fintype G := Fintype.ofFinite G
  have hLG_dim : Module.finrank L (FunSpace G L) = Fintype.card G := Module.finrank_pi L
  have hli_bound : ∀ s : Finset L, LinearIndepOn K id (s : Set L) → s.card ≤ Fintype.card G := by
    intro s hs
    have hTB : LinearIndepOn L id (garlingTrajectory G '' (s : Set L)) := by
      have h112 := theorem_11_2_linearIndepOn G (s : Set L)
      exact h112.2.mp (h112.1.mp hs)
    have hfin_map : (s.image (garlingTrajectory G) : Set (FunSpace G L)) =
        garlingTrajectory G '' (s : Set L) := Finset.coe_image
    rw [← hfin_map] at hTB
    have hcard_eq : (s.image (garlingTrajectory G)).card = s.card :=
      Finset.card_image_of_injective s (garlingTrajectory_injective G)
    have hle := hTB.finset_card_le_finrank
    rwa [hcard_eq, hLG_dim] at hle
  obtain ⟨B, hB⟩ := exists_basis K L
  have hB_fin : B.Finite := by
    by_contra hB_inf
    obtain ⟨s, hsB, hscard⟩ := Set.Infinite.exists_subset_card_eq hB_inf (Fintype.card G + 1)
    have hs_li : LinearIndepOn K id (s : Set L) :=
      (isLinearlyIndependent_iff _).mp (hB.1.mono hsB)
    have hle := hli_bound s hs_li
    omega
  have hmod_KL : Module.Finite K L := by
    rw [Module.finite_def]
    exact ⟨hB_fin.toFinset, by simpa [Spans] using hB.2⟩
  have hfin : IsFiniteExtension K L := (isFiniteExtension_iff_moduleFinite K L).mpr hmod_KL
  have hdeg_le : Module.finrank K L ≤ Fintype.card G := by
    let b := Module.finBasis K L
    have hs_li : LinearIndepOn K id ((Finset.univ.image b : Finset L) : Set L) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact b.linearIndependent.linearIndepOn_id
    have hcard := hli_bound (Finset.univ.image b) hs_li
    rw [Finset.card_image_of_injective _ b.injective, Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard
  have hG_le_gamma : G ≤ garlingGamma K := (theorem_11_1 K (G : Set (GarlingAut L))).1
  have h104 := theorem_10_4_algEquiv (K := K) (L := L) hfin
  have hgamma_card_eq : Nat.card (garlingGamma K) = Nat.card (GarlingGaloisGroup K L) :=
    (Nat.card_congr (garlingGaloisGroupSubfieldMulEquiv K).toEquiv).symm
  have hgamma_le_deg : Nat.card (garlingGamma K) ≤ Module.finrank K L := by
    rw [hgamma_card_eq]
    by_cases hgal : IsGarlingGaloisExtension K L
    · exact le_of_eq (h104.1 hgal)
    · exact le_of_lt (h104.2 hgal)
  have hgamma_fin : Finite (garlingGamma K) := by
    have _ : Finite (GarlingGaloisGroup K L) := Finite.of_fintype (L ≃ₐ[K] L)
    exact Equiv.finite_iff (garlingGaloisGroupSubfieldMulEquiv K).symm.toEquiv |>.mpr inferInstance
  have hG_le_gamma_card : Fintype.card G ≤ Nat.card (garlingGamma K) := by
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_le_of_le hG_le_gamma
  have heq_deg : Module.finrank K L = Fintype.card G :=
    le_antisymm hdeg_le (hG_le_gamma_card.trans hgamma_le_deg)
  have heq_gamma_card : Nat.card (garlingGamma K) = Fintype.card G :=
    le_antisymm (hgamma_le_deg.trans (le_of_eq heq_deg)) hG_le_gamma_card
  have hgal : IsGarlingGaloisExtension K L := by
    by_contra hngal
    have hlt := h104.2 hngal
    rw [← hgamma_card_eq, heq_gamma_card, heq_deg] at hlt
    exact lt_irrefl _ hlt
  have hG_eq_gamma : G = garlingGamma K := by
    let _ : Fintype (garlingGamma K) := Fintype.ofFinite (garlingGamma K)
    apply Subgroup.eq_of_le_of_card_ge hG_le_gamma
    have hc1 : Nat.card (garlingGamma K) = Fintype.card (garlingGamma K) :=
      Nat.card_eq_fintype_card
    have hc2 : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
    omega
  have hset_eq : setOrder G = extDegree K L := by
    rw [extDegree_eq_finrank K L, heq_deg]
    simp [setOrder, ENat.card_eq_coe_fintype_card]
  exact ⟨hfin, hset_eq, by rw [Nat.card_eq_fintype_card, heq_deg], hG_eq_gamma, hgal⟩

/-- Set-finiteness wrapper for **Theorem 11.3** (§11.1, p. 93). -/
theorem theorem_11_3_set_finite {L : Type u} [Field L] (G : Subgroup (GarlingAut L))
    (hG : (G : Set (GarlingAut L)).Finite) :
    let K : Subfield L := garlingPhi (G : Set (GarlingAut L))
    IsFiniteExtension K L ∧
    setOrder G = extDegree K L ∧
    Nat.card G = Module.finrank K L ∧
    G = garlingGamma K ∧
    IsGarlingGaloisExtension K L := by
  have _ : Finite G := hG.to_subtype
  exact theorem_11_3 G

/-- Every finite extension `L : K` has a finite Galois group `γ(K)` (`Theorem 10.4`). -/
theorem finite_garlingGamma_of_isFiniteExtension {L : Type u} [Field L] (K : Subfield L)
    (hfin : IsFiniteExtension K L) :
    Finite (garlingGamma K) := by
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have _ : Finite (GarlingGaloisGroup K L) := Finite.of_fintype (L ≃ₐ[K] L)
  exact Equiv.finite_iff (garlingGaloisGroupSubfieldMulEquiv K).symm.toEquiv |>.mpr inferInstance

/-- **Theorem 11.4** (§11.1, printed p. 94 / PDF p. 102):
*"Suppose that `L : K` is finite. If `L : K` is a Galois extension, then `|γ(K)| = [L : K]`, and
`K = φγ(K)`. Otherwise, `|γ(K)| < [L : K]` and `K` is a proper subfield of `φγ(K)`."*

Proved directly from `Theorem 10.4` and `Theorem 11.3` following Garling's 6-line proof on p. 94. -/
theorem theorem_11_4 {L : Type u} [Field L] (K : Subfield L) (hfin : IsFiniteExtension K L) :
    let G := garlingGamma K
    let K₀ := garlingPhi (G : Set (GarlingAut L))
    (IsGarlingGaloisExtension K L →
      setOrder G = extDegree K L ∧ Nat.card G = Module.finrank K L ∧ K = K₀) ∧
    (¬ IsGarlingGaloisExtension K L →
      setOrder G < extDegree K L ∧ Nat.card G < Module.finrank K L ∧ K < K₀) := by
  intro G K₀
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have _ : Finite G := finite_garlingGamma_of_isFiniteExtension K hfin
  have h113 := theorem_11_3 G
  have _ : Module.Finite K₀ L := (isFiniteExtension_iff_moduleFinite K₀ L).mp h113.1
  have h104 := theorem_10_4_algEquiv (K := K) (L := L) hfin
  have hcard_eq : Nat.card G = Nat.card (GarlingGaloisGroup K L) :=
    (Nat.card_congr (garlingGaloisGroupSubfieldMulEquiv K).toEquiv).symm
  have hK_le : K ≤ K₀ := (theorem_11_1 K ∅).2.1
  let K₀_int : IntermediateField K L :=
    { K₀ with algebraMap_mem' := fun k => hK_le k.2 }
  have hK₀_deg_eq : Module.finrank K₀_int L = Module.finrank K₀ L := rfl
  have _ : Module.Finite K₀_int L := h113.1 |> (isFiniteExtension_iff_moduleFinite K₀ L).mp
  have _ : Module.Finite K K₀_int := FiniteDimensional.left K K₀_int L
  have htower : Module.finrank K K₀_int * Module.finrank K₀_int L = Module.finrank K L :=
    Module.finrank_mul_finrank K K₀_int L
  have hdeg_pos : 0 < Module.finrank K₀ L := Module.finrank_pos
  have hset_G : setOrder G = (Nat.card G : ℕ∞) := by
    let _ : Fintype G := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card]
    simp [setOrder, ENat.card_eq_coe_fintype_card]
  constructor
  · intro hgal
    have hcard_deg : Nat.card G = Module.finrank K L := hcard_eq.trans (h104.1 hgal)
    have hset_deg : setOrder G = extDegree K L := by
      rw [hset_G, extDegree_eq_finrank K L, hcard_deg]
    have hK₀_deg : Module.finrank K₀_int L = Module.finrank K L :=
      hK₀_deg_eq.trans (h113.2.2.1.symm.trans hcard_deg)
    have hfin1 : Module.finrank K K₀_int = 1 := by
      nlinarith
    have hbot : K₀_int = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin1
    have hKK₀ : K = K₀ := by
      apply le_antisymm hK_le
      intro x hx
      have hx_bot : x ∈ (⊥ : IntermediateField K L) := by
        change x ∈ K₀_int at hx
        rwa [hbot] at hx
      rw [IntermediateField.mem_bot] at hx_bot
      obtain ⟨k, hk⟩ := hx_bot
      rw [← hk]
      exact k.2
    exact ⟨hset_deg, hcard_deg, hKK₀⟩
  · intro hngal
    have hcard_lt : Nat.card G < Module.finrank K L := by
      rw [hcard_eq]
      exact h104.2 hngal
    have hset_lt : setOrder G < extDegree K L := by
      rw [hset_G, extDegree_eq_finrank K L]
      exact Nat.cast_lt.mpr hcard_lt
    have hne : K ≠ K₀ := by
      intro heq
      have hbot : K₀_int = ⊥ := by
        ext x
        change x ∈ K₀ ↔ x ∈ (⊥ : IntermediateField K L)
        rw [← heq, IntermediateField.mem_bot]
        exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ k.2⟩
      have hfin1 : Module.finrank K K₀_int = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
      have hcard_eq_deg : Nat.card G = Module.finrank K₀_int L := h113.2.2.1.trans hK₀_deg_eq.symm
      rw [hfin1, one_mul] at htower
      omega
    exact ⟨hset_lt, hcard_lt, lt_of_le_of_ne hK_le hne⟩

/-- `[Algebra K L]` companion to **Theorem 11.4** (§11.1, p. 94), comparing `(algebraMap K L).fieldRange`
with `φ(Γ(L:K))`. -/
theorem theorem_11_4_algebra (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    let G := garlingGaloisSubgroup K L
    let K_sub := (algebraMap K L).fieldRange
    let K₀ := garlingPhi (G : Set (GarlingAut L))
    (IsGarlingGaloisExtension K L →
      setOrder (GarlingGaloisGroup K L) = extDegree K L ∧
      Nat.card (GarlingGaloisGroup K L) = Module.finrank K L ∧ K_sub = K₀) ∧
    (¬ IsGarlingGaloisExtension K L →
      setOrder (GarlingGaloisGroup K L) < extDegree K L ∧
      Nat.card (GarlingGaloisGroup K L) < Module.finrank K L ∧ K_sub < K₀) := by
  intro G K_sub K₀
  let eK : K ≃+* K_sub := RingEquiv.ofBijective (algebraMap K L).rangeRestrict
    ⟨fun a b hab => (algebraMap K L).injective (congrArg Subtype.val hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩
  have heK_smul : ∀ (c : K) (x : L), (eK c) • x = c • x := fun c x => by
    change (algebraMap K L c) * x = c • x
    rw [Algebra.smul_def]
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  let b1 := Module.finBasis K L
  let b2 : Module.Basis (Fin (Module.finrank K L)) K_sub L := b1.mapCoeffs eK heK_smul
  have hmod_sub : Module.Finite K_sub L := Module.Finite.of_basis b2
  have hfin_sub : IsFiniteExtension K_sub L :=
    (isFiniteExtension_iff_moduleFinite K_sub L).mpr hmod_sub
  have hdeg_eq : Module.finrank K_sub L = Module.finrank K L := by
    rw [Module.finrank_eq_card_basis b2, Fintype.card_fin]
  have eAlg : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K_sub] L) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := fun y => by
            obtain ⟨k, hk⟩ := y.2
            change σ y.1 = y.1
            rw [← hk]
            exact σ.commutes k }
      invFun := fun τ =>
        { τ.toRingEquiv with
          commutes' := fun k => τ.commutes ⟨algebraMap K L k, ⟨k, rfl⟩⟩ }
      left_inv := fun σ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl }
  have hcard_alg : Nat.card (L ≃ₐ[K] L) = Nat.card (L ≃ₐ[K_sub] L) := Nat.card_congr eAlg
  have hgal_iff : IsGarlingGaloisExtension K L ↔ IsGarlingGaloisExtension K_sub L := by
    have h1 := theorem_10_4_algEquiv hfin
    have h2 := theorem_10_4_algEquiv hfin_sub
    constructor
    · intro hg
      by_contra hng
      have hc1 := h1.1 hg
      have hc2 := h2.2 hng
      omega
    · intro hg
      by_contra hng
      have hc1 := h1.2 hng
      have hc2 := h2.1 hg
      omega
  have h114 := theorem_11_4 K_sub hfin_sub
  have hext_eq : extDegree K_sub L = extDegree K L := by
    rw [extDegree_eq_finrank K_sub L, extDegree_eq_finrank K L, hdeg_eq]
  have hcard_G : Nat.card (GarlingGaloisGroup K L) = Nat.card G :=
    Nat.card_congr (garlingGaloisGroupMulEquiv K L).toEquiv
  have hset_G : setOrder (GarlingGaloisGroup K L) = setOrder G :=
    ENat.card_congr (garlingGaloisGroupMulEquiv K L).toEquiv
  constructor
  · intro hgal
    obtain ⟨hs, hc, hk⟩ := h114.1 (hgal_iff.mp hgal)
    exact ⟨hset_G.trans (hs.trans hext_eq), hcard_G.trans (hc.trans hdeg_eq), hk⟩
  · intro hngal
    obtain ⟨hs, hc, hk⟩ := h114.2 (fun h => hngal (hgal_iff.mpr h))
    exact ⟨by rwa [hset_G, ← hext_eq], by rwa [hcard_G, ← hdeg_eq], hk⟩

/-! ### §11.1 Exercises 11.1–11.4 (printed p. 94, PDF p. 102) -/

/-- **Exercise 11.1** (§11.1, printed p. 94 / PDF p. 102):
*"Suppose that `L : K` is a Galois extension with Galois group `G`, and that `α ∈ L`. Show that
`L = K(α)` if and only if the images of `α` under `G` are all distinct."* -/
theorem exercise_11_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) (α : L) :
    IntermediateField.adjoin K ({α} : Set L) = ⊤ ↔
      Function.Injective (fun σ : GarlingGaloisGroup K L => σ α) := by
  have ⟨hfd, hgalM⟩ := (isGarlingGaloisExtension_iff K L).mp hgal
  let M : IntermediateField K L := IntermediateField.adjoin K ({α} : Set L)
  have hgal_ML : IsGarlingGaloisExtension M L := by
    rw [isGarlingGaloisExtension_iff]
    exact ⟨FiniteDimensional.right K M L, IsGalois.tower_top_of_isGalois K M L⟩
  have hcard_H : Nat.card (GarlingGaloisGroup M L) = Module.finrank M L :=
    (theorem_10_4_algEquiv hgal_ML.1).1 hgal_ML
  have hH_subsingleton_iff : Subsingleton (GarlingGaloisGroup M L) ↔
      Function.Injective (fun σ : GarlingGaloisGroup K L => σ α) := by
    constructor
    · intro hsub σ₁ σ₂ hα
      have hα' : σ₁ α = σ₂ α := hα
      have hfix : ∀ x ∈ M, (σ₁⁻¹ * σ₂) x = x := by
        let H₀ : Subgroup (GarlingGaloisGroup K L) :=
          { carrier := {τ | τ α = α}
            mul_mem' := fun {a b} ha hb => by change a (b α) = α; rw [hb, ha]
            one_mem' := rfl
            inv_mem' := fun {a} ha => by
              change a.symm α = α
              have h := congrArg a.symm ha
              simpa using h.symm }
        have hmem_H₀ : σ₁⁻¹ * σ₂ ∈ H₀ := by
          change σ₁.symm (σ₂ α) = α
          rw [← hα', σ₁.symm_apply_apply]
        have hM_le : M ≤ IntermediateField.fixedField H₀ := by
          rw [IntermediateField.adjoin_le_iff]
          intro x hx
          rw [Set.mem_singleton_iff.mp hx]
          exact (IntermediateField.mem_fixedField_iff H₀ α).mpr fun τ hτ => hτ
        intro x hx
        exact (IntermediateField.mem_fixedField_iff H₀ x).mp (hM_le hx) (σ₁⁻¹ * σ₂) hmem_H₀
      let τM : GarlingGaloisGroup M L :=
        { (σ₁⁻¹ * σ₂).toRingEquiv with commutes' := fun x => hfix x.1 x.2 }
      have hτM_one : τM = 1 := Subsingleton.elim τM 1
      apply inv_mul_eq_one.mp
      ext x
      exact congrFun (congrArg DFunLike.coe hτM_one) x
    · intro hinj
      refine ⟨fun τ₁ τ₂ => ?_⟩
      let σ₁ : GarlingGaloisGroup K L :=
        { τ₁.toRingEquiv with
          commutes' := fun k => by
            change τ₁ (algebraMap M L (algebraMap K M k)) = _
            rw [τ₁.commutes]
            rfl }
      let σ₂ : GarlingGaloisGroup K L :=
        { τ₂.toRingEquiv with
          commutes' := fun k => by
            change τ₂ (algebraMap M L (algebraMap K M k)) = _
            rw [τ₂.commutes]
            rfl }
      have hα_mem : α ∈ M := IntermediateField.mem_adjoin_simple_self K α
      have h1 : σ₁ α = α := τ₁.commutes ⟨α, hα_mem⟩
      have h2 : σ₂ α = α := τ₂.commutes ⟨α, hα_mem⟩
      have hσ : σ₁ = σ₂ := hinj (h1.trans h2.symm)
      ext x
      exact congrFun (congrArg DFunLike.coe hσ) x
  rw [← hH_subsingleton_iff]
  constructor
  · intro htop
    have hfin1 : Module.finrank M L = 1 := by
      have hmul := Module.finrank_mul_finrank K M L
      have hKM : Module.finrank K M = Module.finrank K L := by
        change Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = Module.finrank K L
        rw [htop]
        exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq
      have hpos : 0 < Module.finrank K L := Module.finrank_pos
      nlinarith
    have hcard1 : Nat.card (GarlingGaloisGroup M L) = 1 := hcard_H.trans hfin1
    exact (Nat.card_eq_one_iff_unique.mp hcard1).1
  · intro hsub
    have hcard1 : Nat.card (GarlingGaloisGroup M L) = 1 := Nat.card_unique
    have hfin1 : Module.finrank M L = 1 := hcard_H.symm.trans hcard1
    have hKM : Module.finrank K M.toSubmodule = Module.finrank K L := by
      have hmul := Module.finrank_mul_finrank K M L
      rw [hfin1, mul_one] at hmul
      exact hmul
    have hsub_top : M.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hKM
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    change x ∈ M.toSubmodule
    rw [hsub_top]
    exact Submodule.mem_top

/-- Orbit-cardinality companion to **Exercise 11.1** (§11.1, p. 94): `L = K(α)` iff the Galois orbit
`{σ(α) : σ ∈ G}` has cardinality `|G|`. -/
theorem exercise_11_1_ncard {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) (α : L) :
    IntermediateField.adjoin K ({α} : Set L) = ⊤ ↔
      (Set.range (fun σ : GarlingGaloisGroup K L => σ α)).ncard =
        Nat.card (GarlingGaloisGroup K L) := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
  let _ : Fintype (GarlingGaloisGroup K L) := Fintype.ofFinite _
  rw [exercise_11_1 hgal α, Nat.card_eq_fintype_card]
  have hrange : (Set.range (fun σ : GarlingGaloisGroup K L => σ α)) =
      ((Finset.univ.image (fun σ : GarlingGaloisGroup K L => σ α) : Finset L) : Set L) := by
    simp
  rw [hrange, Set.ncard_coe_finset]
  have hcard_univ : Fintype.card (GarlingGaloisGroup K L) =
      (Finset.univ : Finset (GarlingGaloisGroup K L)).card := (Finset.card_univ).symm
  rw [hcard_univ, Finset.card_image_iff]
  simp [Set.InjOn, Function.Injective]

/-- Subfield companion to **Exercise 11.1** (§11.1, p. 94) using `garlingGamma K` and Chapter 4's
`garlingFieldGenSubfield K {α}`. -/
theorem exercise_11_1_subfield {L : Type u} [Field L] (K : Subfield L)
    (hgal : IsGarlingGaloisExtension K L) (α : L) :
    garlingFieldGenSubfield K ({α} : Set L) = ⊤ ↔
      Function.Injective (fun σ : garlingGamma K => σ.1 α) := by
  rw [garlingFieldGenSubfield_eq_adjoin]
  have htop_iff : (IntermediateField.adjoin K ({α} : Set L)).toSubfield = ⊤ ↔
      IntermediateField.adjoin K ({α} : Set L) = ⊤ :=
    ⟨fun h => by ext x; exact Set.ext_iff.mp (congrArg SetLike.coe h) x,
     fun h => by rw [h]; rfl⟩
  rw [htop_iff, exercise_11_1 hgal α]
  let e := garlingGaloisGroupSubfieldMulEquiv K
  constructor
  · intro hinj a b hab
    exact e.symm.injective (hinj hab)
  · intro hinj a b hab
    exact e.injective (hinj hab)

/-- Inline prose definition in `Exercise 11.2` (§11.1, printed p. 94 / PDF p. 102):
`End_K(L)` is *"the `K`-linear space of `K`-linear mappings of `L` into itself"*. -/
abbrev GarlingEnd (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Type v :=
  L →ₗ[K] L

/-- Dedekind's linear independence of field automorphisms over `L` (supporting `Exercise 11.2`
for arbitrary, possibly infinite extensions `L : K`). -/
theorem linearIndependent_aut_over_top {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] :
    LinearIndependent L (fun σ : GarlingGaloisGroup K L => (σ : L → L)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum σ₀ hσ₀
  by_contra hc₀
  have hex : ∃ r : ℕ, ∃ (σ : Fin r → GarlingGaloisGroup K L) (lam : Fin r → L),
      0 < r ∧ Function.Injective σ ∧ (∀ i, lam i ≠ 0) ∧
      ∀ x : L, ∑ i : Fin r, lam i * σ i x = 0 := by
    let S : Finset (GarlingGaloisGroup K L) := s.filter (fun σ => c σ ≠ 0)
    have hS_ne : S.Nonempty := ⟨σ₀, Finset.mem_filter.mpr ⟨hσ₀, hc₀⟩⟩
    let e : Fin S.card ≃ S := S.equivFin.symm
    refine ⟨S.card, fun i => (e i).1, fun i => c (e i).1, Finset.card_pos.mpr hS_ne,
      fun i j h => e.injective (Subtype.ext h),
      fun i => (Finset.mem_filter.mp (e i).2).2, ?_⟩
    intro x
    have hx := congrFun hsum x
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hx
    have hsum_S : (∑ σ ∈ S, c σ * σ x) = 0 := by
      rw [← hx]
      refine Finset.sum_subset (Finset.filter_subset _ s) fun σ hσs hσS => ?_
      have hz : c σ = 0 := by
        by_contra hnz
        exact hσS (Finset.mem_filter.mpr ⟨hσs, hnz⟩)
      rw [hz, zero_mul]
    calc (∑ i : Fin S.card, c (e i).1 * (e i).1 x)
        = ∑ u : S, c u.1 * u.1 x := Equiv.sum_comp e (fun u : S => c u.1 * u.1 x)
      _ = ∑ σ ∈ S, c σ * σ x := S.sum_coe_sort (fun σ => c σ * σ x)
      _ = 0 := hsum_S
  have hspec : ∃ (σ : Fin (Nat.find hex) → GarlingGaloisGroup K L) (lam : Fin (Nat.find hex) → L),
      0 < Nat.find hex ∧ Function.Injective σ ∧ (∀ i, lam i ≠ 0) ∧
      ∀ x : L, ∑ i, lam i * σ i x = 0 := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ¬ ∃ (σ : Fin k → GarlingGaloisGroup K L) (lam : Fin k → L),
      0 < k ∧ Function.Injective σ ∧ (∀ i, lam i ≠ 0) ∧
      ∀ x : L, ∑ i, lam i * σ i x = 0 := fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = r at hspec hmin
  obtain ⟨σ, lam, hr_pos, hσ_inj, hlam_nz, hrel⟩ := hspec
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr_pos)
  cases m with
  | zero =>
    have h1 := hrel 1
    rw [Fin.sum_univ_one] at h1
    simp only [map_one, mul_one] at h1
    exact hlam_nz 0 h1
  | succ m' =>
    have h0_ne_last : (0 : Fin (m' + 2)) ≠ Fin.last (m' + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have hne01 : σ 0 ≠ σ (Fin.last (m' + 1)) :=
      fun h => h0_ne_last (hσ_inj h)
    have hex_y : ∃ y : L, σ 0 y ≠ σ (Fin.last (m' + 1)) y := by
      by_contra hall
      push Not at hall
      exact hne01 (AlgEquiv.ext hall)
    obtain ⟨y, hy⟩ := hex_y
    let lastIdx : Fin (m' + 2) := Fin.last (m' + 1)
    have hcomb : ∀ x : L,
        ∑ j : Fin (m' + 1),
          (lam j.castSucc * (σ j.castSucc y - σ lastIdx y)) * σ j.castSucc x = 0 := by
      intro x
      have h1 := hrel (y * x)
      have h2 := congrArg (fun z => σ lastIdx y * z) (hrel x)
      simp only [Finset.mul_sum, mul_zero] at h2
      rw [Fin.sum_univ_castSucc] at h1 h2
      have hdiff :
          (∑ j : Fin (m' + 1), lam j.castSucc * σ j.castSucc (y * x) +
            lam lastIdx * σ lastIdx (y * x)) -
          (∑ j : Fin (m' + 1), σ lastIdx y * (lam j.castSucc * σ j.castSucc x) +
            σ lastIdx y * (lam lastIdx * σ lastIdx x)) = 0 := by
        rw [h1, h2, sub_self]
      rw [← hdiff]
      simp only [map_mul]
      have hsub :
          (∑ j : Fin (m' + 1),
            (lam j.castSucc * (σ j.castSucc y - σ lastIdx y)) * σ j.castSucc x) =
          (∑ j : Fin (m' + 1), lam j.castSucc * (σ j.castSucc y * σ j.castSucc x)) -
          (∑ j : Fin (m' + 1), σ lastIdx y * (lam j.castSucc * σ j.castSucc x)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hsub]
      ring
    let coeff : Fin (m' + 1) → L := fun j => lam j.castSucc * (σ j.castSucc y - σ lastIdx y)
    have hc0 : coeff 0 ≠ 0 := mul_ne_zero (hlam_nz 0) (sub_ne_zero.mpr hy)
    let S' : Finset (Fin (m' + 1)) := Finset.univ.filter (fun j => coeff j ≠ 0)
    have hS'_ne : S'.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0⟩⟩
    let e' : Fin S'.card ≃ S' := S'.equivFin.symm
    have hlt : S'.card < m' + 2 := by
      have hle : S'.card ≤ (Finset.univ : Finset (Fin (m' + 1))).card := Finset.card_filter_le _ _
      rw [Finset.card_fin] at hle
      omega
    refine hmin S'.card hlt ⟨fun k => σ (e' k).1.castSucc, fun k => coeff (e' k).1,
      Finset.card_pos.mpr hS'_ne,
      fun k₁ k₂ hk => e'.injective (Subtype.ext (Fin.castSucc_injective _ (hσ_inj hk))),
      fun k => (Finset.mem_filter.mp (e' k).2).2, ?_⟩
    intro x
    have hsum_S' : (∑ j ∈ S', coeff j * σ j.castSucc x) = 0 := by
      rw [← hcomb x]
      refine Finset.sum_subset (Finset.subset_univ S') fun j _ hjS' => ?_
      have hz : coeff j = 0 := by
        by_contra hnz
        exact hjS' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩)
      rw [hz, zero_mul]
    calc (∑ k : Fin S'.card, coeff (e' k).1 * σ (e' k).1.castSucc x)
        = ∑ u : S', coeff u.1 * σ u.1.castSucc x :=
            Equiv.sum_comp e' (fun u : S' => coeff u.1 * σ u.1.castSucc x)
      _ = ∑ j ∈ S', coeff j * σ j.castSucc x :=
            S'.sum_coe_sort (fun j : Fin (m' + 1) => coeff j * σ j.castSucc x)
      _ = 0 := hsum_S'

/-- **Exercise 11.2** (§11.1, printed p. 94 / PDF p. 102):
*"Suppose that `L : K` is an extension. If `σ ∈ Γ(L:K)`, `σ ∈ End_K(L)`, the `K`-linear space of
`K`-linear mappings of `L` into itself. Show that `Γ(L:K)` is a linearly independent subset of
`End_K(L)`."* -/
theorem exercise_11_2 (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    IsLinearlyIndependent K
      (Set.range (fun σ : GarlingGaloisGroup K L => (σ.toLinearMap : GarlingEnd K L))) ∧
    LinearIndependent K
      (fun σ : GarlingGaloisGroup K L => (σ.toLinearMap : GarlingEnd K L)) := by
  have hli_K : LinearIndependent K
      (fun σ : GarlingGaloisGroup K L => (σ.toLinearMap : GarlingEnd K L)) := by
    rw [linearIndependent_iff']
    intro s c hsum σ₀ hσ₀
    have hsum_L : (∑ σ ∈ s, (algebraMap K L (c σ)) • (σ : L → L)) = 0 := by
      ext x
      have hx := LinearMap.congr_fun hsum x
      simp only [LinearMap.sum_apply, LinearMap.zero_apply, Finset.sum_apply, Pi.zero_apply] at hx ⊢
      rw [← hx]
      refine Finset.sum_congr rfl fun σ _ => ?_
      change algebraMap K L (c σ) * σ x = (c σ • σ.toLinearMap) x
      simp [Algebra.smul_def]
    have h0 := linearIndependent_iff'.mp (linearIndependent_aut_over_top (K := K) (L := L))
      s (fun σ => algebraMap K L (c σ)) hsum_L σ₀ hσ₀
    exact (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp h0
  refine ⟨?_, hli_K⟩
  rw [isLinearlyIndependent_iff]
  exact hli_K.linearIndepOn_id

/-- **Exercise 11.3** (§11.1, printed p. 94 / PDF p. 102):
*"Suppose that `L : K` is a Galois extension with Galois group `G = {σ₁, …, σ_n}`. Show that
`(β₁, …, β_n)` is a basis for `L` over `K` if and only if `det(σ_i(β_j)) ≠ 0`."*
*(OCR warning verified against 160 DPI scan p. 94 / PDF p. 102: `garling1986_pages.txt` drops
subscript `j` in `det(σ_i(β_j)) ≠ 0`.)*

Proved directly from `Theorem 11.2` and `Theorem 11.4` by identifying the columns of `(σ_i(β_j))`
with the trajectories `T(β_j) ∈ L^G` over `K = φ(G)`. -/
theorem exercise_11_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) (β : Fin n → L) :
    ((∃ B : Module.Basis (Fin n) K L, ∀ j : Fin n, B j = β j) ↔
      (Matrix.of (fun i j : Fin n => σ i (β j))).det ≠ 0) ∧
    (IsBasis K L (Set.range β) ↔
      (Matrix.of (fun i j : Fin n => σ i (β j))).det ≠ 0) := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
  have _ : Nonempty (Fin n) := ⟨σ.symm 1⟩
  have hdeg : Module.finrank K L = n := by
    have hcard := (theorem_10_4_algEquiv hgal.1).1 hgal
    rw [← hcard, ← Nat.card_congr σ, Nat.card_fin]
  let G : Subgroup (GarlingAut L) := garlingGaloisSubgroup K L
  let K_sub : Subfield L := (algebraMap K L).fieldRange
  have hK₀_eq : garlingPhi (G : Set (GarlingAut L)) = K_sub :=
    ((theorem_11_4_algebra K L hgal.1).1 hgal).2.2.symm
  let eG : Fin n ≃ G := σ.trans (garlingGaloisGroupMulEquiv K L).toEquiv
  let fK : K →+* garlingPhi (G : Set (GarlingAut L)) :=
    { toFun := fun k => ⟨algebraMap K L k, hK₀_eq.symm ▸ ⟨k, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  let eK : K ≃+* garlingPhi (G : Set (GarlingAut L)) :=
    RingEquiv.ofBijective fK
      ⟨fun a b hab => (algebraMap K L).injective (congrArg Subtype.val hab),
       fun y => by
         have hy : y.1 ∈ K_sub := hK₀_eq ▸ y.2
         obtain ⟨k, hk⟩ := hy
         exact ⟨k, Subtype.ext hk⟩⟩
  let Mf : Fin n → Fin n → L := fun i j => σ i (β j)
  let M : Matrix (Fin n) (Fin n) L := Matrix.of Mf
  have hdet_iff_col : M.det ≠ 0 ↔ LinearIndependent L (fun j : Fin n => fun i : Fin n => Mf i j) := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    constructor
    · intro hu
      have hinj : Function.Injective M.mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr hu
      rw [linearIndependent_iff']
      intro s c hsum j₀ hj₀
      have hvec : M.mulVec (fun j => if j ∈ s then c j else 0) = 0 := by
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M, Matrix.of_apply]
        have hi := congrFun hsum i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
        have hsum_ite :
            (∑ j : Fin n, Mf i j * (if j ∈ s then c j else 0)) = ∑ j ∈ s, c j * Mf i j := by
          trans ∑ j : Fin n, (if j ∈ s then c j * Mf i j else 0)
          · refine Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> ring
          · rw [← Finset.sum_filter]
            have hfs : Finset.univ.filter (fun j => j ∈ s) = s := by ext j; simp
            rw [hfs]
        exact hsum_ite.trans hi
      have hz := congrFun (hinj (hvec.trans (Matrix.mulVec_zero M).symm)) j₀
      simpa [hj₀] using hz
    · intro hli
      rw [← Matrix.mulVec_injective_iff_isUnit]
      intro u v huv
      have hsub : M.mulVec (u - v) = 0 := by
        rw [Matrix.mulVec_sub, huv, sub_self]
      have hsum : (∑ j : Fin n, (u j - v j) • (fun i : Fin n => Mf i j)) = 0 := by
        ext i
        have hi := congrFun hsub i
        simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply, M, Matrix.of_apply] at hi
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        simpa [mul_comm] using hi
      ext j
      exact sub_eq_zero.mp
        (linearIndependent_iff'.mp hli Finset.univ (u - v) hsum j (Finset.mem_univ j))
  have hcol_iff_li_K : LinearIndependent L (fun j : Fin n => fun i : Fin n => Mf i j) ↔
      LinearIndependent K β := by
    let eFun : (G → L) ≃ₗ[L] (Fin n → L) := LinearEquiv.piCongrLeft' L (fun _ => L) eG.symm
    have hmap : (eFun.toLinearMap ∘ fun j : Fin n => garlingTrajectory G (β j)) =
        (fun j : Fin n => fun i : Fin n => Mf i j) := by
      ext j i
      change ((garlingGaloisGroupMulEquiv K L (σ i)).1) (β j) = σ i (β j)
      rfl
    rw [← hmap, LinearMap.linearIndependent_iff eFun.toLinearMap eFun.ker]
    have htraj_iff : LinearIndependent L (fun j : Fin n => garlingTrajectory G (β j)) ↔
        LinearIndependent (garlingPhi (G : Set (GarlingAut L))) β := by
      constructor
      · intro hli
        have hinj : Function.Injective β :=
          fun j₁ j₂ h => hli.injective (congrArg (garlingTrajectory G) h)
        have hon_L : LinearIndepOn L id (garlingTrajectory G '' Set.range β) := by
          rw [← Set.range_comp]
          exact hli.linearIndepOn_id
        have hon_K := (theorem_11_2_linearIndepOn G (Set.range β)).1.mpr
          ((theorem_11_2_linearIndepOn G (Set.range β)).2.mpr hon_L)
        exact (linearIndepOn_id_range_iff hinj).mp hon_K
      · intro hli
        have hinj : Function.Injective β := hli.injective
        have hon_K : LinearIndepOn (garlingPhi (G : Set (GarlingAut L))) id (Set.range β) :=
          hli.linearIndepOn_id
        have hon_L := (theorem_11_2_linearIndepOn G (Set.range β)).2.mp
          ((theorem_11_2_linearIndepOn G (Set.range β)).1.mp hon_K)
        rw [← Set.range_comp] at hon_L
        exact (linearIndepOn_id_range_iff ((garlingTrajectory_injective G).comp hinj)).mp hon_L
    rw [htraj_iff]
    constructor
    · intro hli
      rw [linearIndependent_iff'] at hli ⊢
      intro s c hsum j₀ hj₀
      have hsum' : ∑ j ∈ s, (eK (c j)) • β j = 0 := by
        have h1 : (∑ j ∈ s, (eK (c j)) • β j) = ∑ j ∈ s, (c j) • β j :=
          Finset.sum_congr rfl fun j _ => by
            simp only [Algebra.smul_def]
            rfl
        exact h1.trans hsum
      exact eK.injective (by simpa using hli s (fun j => eK (c j)) hsum' j₀ hj₀)
    · intro hli
      rw [linearIndependent_iff'] at hli ⊢
      intro s c hsum j₀ hj₀
      have hsum' : ∑ j ∈ s, (eK.symm (c j)) • β j = 0 := by
        have h1 : (∑ j ∈ s, (eK.symm (c j)) • β j) = ∑ j ∈ s, (c j) • β j :=
          Finset.sum_congr rfl fun j _ => by
            simp only [Algebra.smul_def]
            have heq : (eK (eK.symm (c j)) : L) = (c j : L) :=
              congrArg Subtype.val (eK.apply_symm_apply (c j))
            exact congrArg (· * β j) heq
        exact h1.trans hsum
      have hz := hli s (fun j => eK.symm (c j)) hsum' j₀ hj₀
      exact eK.symm.injective (hz.trans (map_zero eK.symm).symm)
  have hbasis_iff_li : (∃ B : Module.Basis (Fin n) K L, ∀ j : Fin n, B j = β j) ↔
      LinearIndependent K β := by
    constructor
    · rintro ⟨B, hB⟩
      have heq : (B : Fin n → L) = β := funext hB
      exact heq ▸ B.linearIndependent
    · intro hli
      let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdeg])
      exact ⟨B, fun j => by simp [B]⟩
  have hisBasis_iff_li : IsBasis K L (Set.range β) ↔ LinearIndependent K β := by
    constructor
    · rintro ⟨hli_set, hspan⟩
      have hspan_top : Submodule.span K (Set.range β) = ⊤ := hspan
      let S₀ : Finset L := Finset.univ.image β
      have hS₀_coe : (S₀ : Set L) = Set.range β := by simp [S₀]
      obtain ⟨B_sub, _, hB_sub_le, hB_sub⟩ :=
        theorem_1_1 S₀.finite_toSet (by rwa [Spans, hS₀_coe]) (Set.empty_subset _)
          (empty_isLinearlyIndependent K)
      have hB_fin : B_sub.Finite := S₀.finite_toSet.subset hB_sub_le
      have hb_card : hB_fin.toFinset.card = n := by
        have hdim := extDegree_eq_setOrder_basis hB_sub
        rw [extDegree_eq_finrank K L, hdeg] at hdim
        have hso : setOrder B_sub = (hB_fin.toFinset.card : ℕ∞) := by
          let _ : Fintype B_sub := hB_fin.fintype
          rw [Set.Finite.card_toFinset hB_fin]
          simp [setOrder, ENat.card_eq_coe_fintype_card]
        exact Nat.cast_injective (hso.symm.trans hdim.symm)
      have hle : n ≤ S₀.card := by
        rw [← hb_card]
        refine Finset.card_le_card fun x hx => ?_
        have hxS₀ : x ∈ (S₀ : Set L) := hB_sub_le (hB_fin.mem_toFinset.mp hx)
        exact Finset.mem_coe.mp hxS₀
      have hinj : Function.Injective β := by
        have hcard_eq : S₀.card = (Finset.univ : Finset (Fin n)).card :=
          le_antisymm Finset.card_image_le (by simpa using hle)
        exact fun a b hab =>
          (Finset.card_image_iff.mp hcard_eq) (Finset.mem_univ a) (Finset.mem_univ b) hab
      exact (linearIndepOn_id_range_iff hinj).mp ((isLinearlyIndependent_iff _).mp hli_set)
    · intro hli
      obtain ⟨B, hB⟩ := hbasis_iff_li.mpr hli
      have heq : (B : Fin n → L) = β := funext hB
      rw [← heq]
      exact ⟨(isLinearlyIndependent_iff _).mpr B.linearIndependent.linearIndepOn_id, B.span_eq⟩
  exact ⟨hbasis_iff_li.trans (hcol_iff_li_K.symm.trans hdet_iff_col.symm),
    hisBasis_iff_li.trans (hcol_iff_li_K.symm.trans hdet_iff_col.symm)⟩

/-- Companion to **Exercise 11.3** (§11.1, p. 94) allowing any surjective enumeration
`G = {σ₁, …, σ_n}` (`Set.range σ = Set.univ`, without assuming `σ` is repetition-free): both sides
of the equivalence remain false if `σ` repeats an element. -/
theorem exercise_11_3_surjective_enum {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n → GarlingGaloisGroup K L) (hσ : Set.range σ = Set.univ) (β : Fin n → L) :
    (∃ B : Module.Basis (Fin n) K L, ∀ j : Fin n, B j = β j) ↔
      (Matrix.of (fun i j : Fin n => σ i (β j))).det ≠ 0 := by
  classical
  by_cases hinj : Function.Injective σ
  · let e : Fin n ≃ GarlingGaloisGroup K L :=
      Equiv.ofBijective σ ⟨hinj, Set.range_eq_univ.mp hσ⟩
    exact (exercise_11_3 hgal e β).1
  · have hnot_inj : ∃ i₁ i₂ : Fin n, σ i₁ = σ i₂ ∧ i₁ ≠ i₂ := by
      simpa [Function.Injective] using hinj
    obtain ⟨i₁, i₂, heq, hne⟩ := hnot_inj
    have hdet_zero : (Matrix.of (fun i j : Fin n => σ i (β j))).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext j; simp [heq])
    have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
    have hcard_G : Nat.card (GarlingGaloisGroup K L) = Module.finrank K L :=
      (theorem_10_4_algEquiv hgal.1).1 hgal
    let _ : Fintype (GarlingGaloisGroup K L) := Fintype.ofFinite _
    have hsurj : Function.Surjective σ := Set.range_eq_univ.mp hσ
    have hcard_lt : Fintype.card (GarlingGaloisGroup K L) < n := by
      have hle : Fintype.card (GarlingGaloisGroup K L) ≤ n := by
        simpa using Fintype.card_le_of_surjective σ hsurj
      rcases lt_or_eq_of_le hle with hlt | heq_card
      · exact hlt
      · exfalso
        have hbij : Function.Bijective σ :=
          (Fintype.bijective_iff_surjective_and_card σ).mpr ⟨hsurj, by simpa using heq_card.symm⟩
        exact hinj hbij.1
    have hn_gt_deg : Module.finrank K L < n := by
      rw [← hcard_G, Nat.card_eq_fintype_card]
      exact hcard_lt
    refine ⟨fun ⟨B, _⟩ => ?_, fun h => (h hdet_zero).elim⟩
    have hdeg_eq : Module.finrank K L = n := by
      rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
    omega

/-- **Exercise 11.4** (subfield form, §11.1, printed p. 94 / PDF p. 102):
*"Suppose that `char K = 0` and that `L : K` is a finite extension; let `β₁, …, β_n` be a basis for
`L` over `K`. Suppose that `H` is a subgroup of `Γ(L:K)`; let `γ_j = ∑_{σ ∈ H} σβ_j`, for
`1 ≤ j ≤ n`. Show that `K(γ₁, …, γ_n)` is the fixed field for `H`."* -/
theorem exercise_11_4_subfield {L : Type u} [Field L] (K : Subfield L)
    (hchar : ringChar K = 0) (hfin : IsFiniteExtension K L) {n : ℕ}
    (β : Module.Basis (Fin n) K L) (H : Subgroup (GarlingAut L)) (hH : H ≤ garlingGamma K) :
    ∃ (_ : Fintype H),
      let γ : Fin n → L := fun j => ∑ σ : H, σ.1 (β j)
      garlingFieldGenSubfield K (Set.range γ) = garlingPhi (H : Set (GarlingAut L)) := by
  classical
  have hG_fin : Finite (garlingGamma K) := finite_garlingGamma_of_isFiniteExtension K hfin
  have hH_fin : Finite H :=
    ((Set.toFinite (garlingGamma K : Set (GarlingAut L))).subset hH).to_subtype
  let hft : Fintype H := Fintype.ofFinite H
  refine ⟨hft, ?_⟩
  intro γ
  have hcp0 : CharP K 0 := hchar ▸ ringChar.charP K
  have _ : CharZero K := CharP.charP_to_charZero K
  have _ : CharZero L := charZero_of_injective_ringHom K.subtype.injective
  rw [garlingFieldGenSubfield_eq_adjoin]
  let F : Subfield L := (IntermediateField.adjoin K (Set.range γ)).toSubfield
  change F = garlingPhi (H : Set (GarlingAut L))
  apply le_antisymm
  · have hK_le : K ≤ garlingPhi (H : Set (GarlingAut L)) :=
      (theorem_11_1 K ∅).2.1.trans (garlingPhi_anti hH)
    have hadj_le : IntermediateField.adjoin K (Set.range γ) ≤
        { garlingPhi (H : Set (GarlingAut L)) with
          algebraMap_mem' := fun k => hK_le k.2 } := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩ τ hτ
      dsimp only [γ]
      rw [map_sum]
      let mulLeftEquiv : H ≃ H := Equiv.mulLeft ⟨τ, hτ⟩
      calc (∑ σ : H, τ (σ.1 (β j)))
          = ∑ σ : H, (mulLeftEquiv σ).1 (β j) := rfl
        _ = ∑ σ : H, σ.1 (β j) := Equiv.sum_comp mulLeftEquiv (fun σ : H => σ.1 (β j))
    exact hadj_le
  · intro x hx
    have hx_repr : x = ∑ j : Fin n, (β.repr x j : L) * β j := by
      have h := β.sum_repr x
      simpa [Subfield.smul_def] using h.symm
    have hsum_H : (∑ σ : H, σ.1 x) = (Fintype.card H : L) * x := by
      have hfix : ∀ σ : H, σ.1 x = x := fun σ => hx σ.1 σ.2
      simp [hfix]
    have hsum_rhs : (∑ σ : H, σ.1 x) = ∑ j : Fin n, (β.repr x j : L) * γ j := by
      calc (∑ σ : H, σ.1 x)
          = ∑ σ : H, σ.1 (∑ j : Fin n, (β.repr x j : L) * β j) := by
              refine Finset.sum_congr rfl fun σ _ => congrArg σ.1 hx_repr
        _ = ∑ σ : H, ∑ j : Fin n, (β.repr x j : L) * σ.1 (β j) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              rw [map_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [map_mul, hH σ.2 (β.repr x j).1 (β.repr x j).2]
        _ = ∑ j : Fin n, ∑ σ : H, (β.repr x j : L) * σ.1 (β j) := Finset.sum_comm
        _ = ∑ j : Fin n, (β.repr x j : L) * γ j := by
              refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    have hcard_pos : 0 < Fintype.card H := Fintype.card_pos
    have hcard_ne : (Fintype.card H : L) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
    have hx_eq : x = (Fintype.card H : L)⁻¹ * ∑ j : Fin n, (β.repr x j : L) * γ j := by
      apply mul_left_cancel₀ hcard_ne
      rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul, ← hsum_H, hsum_rhs]
    rw [hx_eq]
    refine F.mul_mem (F.inv_mem (natCast_mem F (Fintype.card H))) ?_
    refine F.sum_mem fun j _ => F.mul_mem ?_ ?_
    · exact (IntermediateField.adjoin K (Set.range γ)).algebraMap_mem (β.repr x j)
    · exact IntermediateField.subset_adjoin K (Set.range γ) ⟨j, rfl⟩

/-- `[Algebra K L]` companion to **Exercise 11.4** (§11.1, printed p. 94 / PDF p. 102):
for `H : Subgroup (GarlingGaloisGroup K L)` over a characteristic-`0` finite extension `L : K`
with `K`-basis `β : Module.Basis (Fin n) K L`, `K(γ₁, …, γ_n) = IntermediateField.fixedField H`. -/
theorem exercise_11_4 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hchar : ringChar K = 0) (hfin : IsFiniteExtension K L) {n : ℕ}
    (β : Module.Basis (Fin n) K L) (H : Subgroup (GarlingGaloisGroup K L)) :
    ∃ (_ : Fintype H),
      let γ : Fin n → L := fun j => ∑ σ : H, σ.1 (β j)
      IntermediateField.adjoin K (Set.range γ) = IntermediateField.fixedField H := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  let hft : Fintype H := Fintype.ofFinite H
  refine ⟨hft, ?_⟩
  intro γ
  have hcp0 : CharP K 0 := hchar ▸ ringChar.charP K
  have _ : CharZero K := CharP.charP_to_charZero K
  have _ : CharZero L := charZero_of_injective_ringHom (algebraMap K L).injective
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    refine (IntermediateField.mem_fixedField_iff H (γ j)).mpr fun τ hτ => ?_
    dsimp only [γ]
    rw [map_sum]
    let mulLeftEquiv : H ≃ H := Equiv.mulLeft ⟨τ, hτ⟩
    calc (∑ σ : H, τ (σ.1 (β j)))
        = ∑ σ : H, (mulLeftEquiv σ).1 (β j) := rfl
      _ = ∑ σ : H, σ.1 (β j) := Equiv.sum_comp mulLeftEquiv (fun σ : H => σ.1 (β j))
  · intro x hx
    have hx' := (IntermediateField.mem_fixedField_iff H x).mp hx
    have hx_repr : x = ∑ j : Fin n, algebraMap K L (β.repr x j) * β j := by
      have h := β.sum_repr x
      simpa [Algebra.smul_def] using h.symm
    have hsum_H : (∑ σ : H, σ.1 x) = (Fintype.card H : L) * x := by
      have hfix : ∀ σ : H, σ.1 x = x := fun σ => hx' σ.1 σ.2
      simp [hfix]
    have hsum_rhs : (∑ σ : H, σ.1 x) = ∑ j : Fin n, algebraMap K L (β.repr x j) * γ j := by
      calc (∑ σ : H, σ.1 x)
          = ∑ σ : H, σ.1 (∑ j : Fin n, algebraMap K L (β.repr x j) * β j) := by
              refine Finset.sum_congr rfl fun σ _ => congrArg σ.1 hx_repr
        _ = ∑ σ : H, ∑ j : Fin n, algebraMap K L (β.repr x j) * σ.1 (β j) := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              rw [map_sum]
              refine Finset.sum_congr rfl fun j _ => by rw [map_mul, σ.1.commutes]
        _ = ∑ j : Fin n, ∑ σ : H, algebraMap K L (β.repr x j) * σ.1 (β j) := Finset.sum_comm
        _ = ∑ j : Fin n, algebraMap K L (β.repr x j) * γ j := by
              refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    have hcard_pos : 0 < Fintype.card H := Fintype.card_pos
    have hcard_ne : (Fintype.card H : L) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
    have hx_eq : x = (Fintype.card H : L)⁻¹ * ∑ j : Fin n, algebraMap K L (β.repr x j) * γ j := by
      apply mul_left_cancel₀ hcard_ne
      rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul, ← hsum_H, hsum_rhs]
    rw [hx_eq]
    let E := IntermediateField.adjoin K (Set.range γ)
    exact E.mul_mem (E.inv_mem (natCast_mem E (Fintype.card H)))
      (E.sum_mem fun j _ => E.mul_mem (E.algebraMap_mem (β.repr x j))
        (IntermediateField.subset_adjoin K (Set.range γ) ⟨j, rfl⟩))

/-! ## §11.2 The Galois group of a polynomial (printed pp. 94–96, PDF pp. 102–104) -/

/-- Garling's prose definition of the *Galois group* `Γ_K(f)` / `Γ(f)` of a polynomial `f ∈ K[x]`
relative to a splitting field extension `L : K` (§11.2, printed pp. 94–95 / PDF pp. 102–103):
*"Suppose that `f ∈ K[x]` and that `L : K` is a splitting field extension for `f` over `K`. Then we
call `Γ(L:K)` the Galois group of `f`; we denote it by `Γ_K(f)` (or `Γ(f)`, when it is clear what
`K` is)."* -/
abbrev GarlingPolyGaloisGroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (_f : K[X]) : Type v :=
  GarlingGaloisGroup K L

/-- Subgroup-of-`Aut L` form of `Γ_K(f)` (§11.2, pp. 94–95). -/
abbrev garlingPolyGaloisSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (_f : K[X]) : Subgroup (GarlingAut L) :=
  garlingGaloisSubgroup K L

/-- Independence of `Γ_K(f)` from the choice of splitting field up to group isomorphism
(§11.2, printed p. 95, ll. 1–3: *"By Corollary 1 to Theorem 7.5, `Γ_K(f)` depends on `f` and `K`,
but not on any particular choice of splitting field"*), holding for all `f ∈ K[X]` (including
`f = 0`). -/
theorem garlingPolyGaloisGroup_independent_of_splittingField
    {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂] {f : K[X]}
    (hsf₁ : IsGarlingSplittingFieldExtension K L₁ f)
    (hsf₂ : IsGarlingSplittingFieldExtension K L₂ f) :
    Nonempty (GarlingPolyGaloisGroup K L₁ f ≃* GarlingPolyGaloisGroup K L₂ f) := by
  obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf₁ hsf₂
  exact ⟨{
    toFun := fun σ => e.symm.trans (σ.trans e)
    invFun := fun τ => e.trans (τ.trans e.symm)
    left_inv := fun σ => by ext x; simp
    right_inv := fun τ => by ext x; simp
    map_mul' := fun σ₁ σ₂ => by ext x; simp [AlgEquiv.mul_apply]
  }⟩

/-- **Counterexample to the literal `"otherwise"` branch of `Theorem 11.5` at `f = 0` over an
imperfect field** (`BRIEF.md` Flag 4; see `QUEUE.md`):
On `K = FractionRing (ZMod 2)[X]` (`ℤ₂(α)` from §10.6, p. 89), `L = K` is a splitting field
extension for `f = 0` (`IsGarlingSplittingFieldExtension K K 0`), and `0` is **not** separable
under §10.1's literal definition `IsGarlingSeparablePoly` (`x² - α` is an inseparable irreducible
divisor of `0`), yet `|Γ(0)| = 1 = [K : K]` and `(algebraMap K K).fieldRange = φ(Γ(0))`, refuting
`|Γ(f)| < [L : K]` and strict subfield inclusion at `f = 0`. -/
theorem theorem_11_5_zero_imperfect_counterexample :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let K := FractionRing (ZMod 2)[X]
    IsGarlingSplittingFieldExtension K K (0 : K[X]) ∧
    ¬ IsGarlingSeparablePoly (0 : K[X]) ∧
    Nat.card (GarlingPolyGaloisGroup K K (0 : K[X])) = Module.finrank K K ∧
    (algebraMap K K).fieldRange =
      garlingPhi (garlingPolyGaloisSubgroup K K (0 : K[X]) : Set (GarlingAut K)) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K
  have hex := section_10_6_inseparable_example.{0} Nat.prime_two
  have hnot_sep0 : ¬ IsGarlingSeparablePoly (0 : K[X]) := by
    intro h0
    exact hex.2.2.2.1 ((isGarlingSeparablePoly_zero_iff K).mp h0 _)
  have hsf0 : IsGarlingSplittingFieldExtension K K (0 : K[X]) :=
    (isGarlingSplittingFieldExtension_zero_iff K K).mpr
      (Subsingleton.elim (⊥ : IntermediateField K K) ⊤)
  have hsub : Subsingleton (GarlingPolyGaloisGroup K K (0 : K[X])) :=
    ⟨fun σ₁ σ₂ => by
      ext x
      exact (σ₁.commutes x).trans (σ₂.commutes x).symm⟩
  have hcard : Nat.card (GarlingPolyGaloisGroup K K (0 : K[X])) = Module.finrank K K := by
    rw [Nat.card_unique, Module.finrank_self]
  have hphi : (algebraMap K K).fieldRange =
      garlingPhi (garlingPolyGaloisSubgroup K K (0 : K[X]) : Set (GarlingAut K)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ σ hσ
      exact mem_garlingGaloisSubgroup_iff.mp hσ y
    · intro _
      exact ⟨x, rfl⟩
  exact ⟨hsf0, hnot_sep0, hcard, hphi⟩

/-- Helper equivalence: for `f ≠ 0` and a splitting field extension `L : K` of `f`, `L : K` is
separable iff `f` is separable (`IsGarlingSeparablePoly f`). -/
theorem isGarlingSeparableExtension_iff_poly_of_splittingField
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) (hsf : IsGarlingSplittingFieldExtension K L f) :
    IsGarlingSeparableExtension K L ↔ IsGarlingSeparablePoly f := by
  constructor
  · intro hsepL g hg_irr hg_dvd
    obtain ⟨q, hfq⟩ := hg_dvd
    have hq0 : q ≠ 0 := fun h0 => hf0 (by rw [hfq, h0, mul_zero])
    have hsplits_g : GarlingSplitsOver K L g :=
      ((garlingSplitsOver_mul_iff hg_irr.ne_zero hq0).mp (hfq ▸ hsf.1)).1
    have hg_pos : 0 < g.natDegree := hg_irr.natDegree_pos
    obtain ⟨m, c, α, hexp⟩ := hsplits_g
    have hm_eq : m = g.natDegree := (garlingSplitsExplicit_props hg_irr.ne_zero hexp).2.2.1
    have hm_pos : 0 < m := hm_eq ▸ hg_pos
    let α₀ : L := α ⟨0, hm_pos⟩
    have hα₀_root : Polynomial.aeval α₀ g = 0 := by
      have hmem : α₀ ∈ g.rootSet L :=
        (garlingSplitsExplicit_props hg_irr.ne_zero hexp).2.2.2 ▸ ⟨⟨0, hm_pos⟩, rfl⟩
      exact (Polynomial.mem_rootSet.mp hmem).2
    have hα₀_alg : IsGarlingAlgebraic K α₀ := ⟨g, hg_irr.ne_zero, hα₀_root⟩
    have hint : IsIntegral K α₀ := (isGarlingAlgebraic_iff_isIntegral K α₀).mp hα₀_alg
    have hass : Associated (minpoly K α₀) g :=
      (minpoly.irreducible hint).associated_of_dvd hg_irr (minpoly.dvd K α₀ hα₀_root)
    have hmin_sep : (minpoly K α₀).Separable :=
      (isGarlingSeparableElement_iff K α₀).mp (hsepL α₀)
    exact (isGarlingSeparableIrreducible_iff_separable hg_irr).mpr (hass.separable hmin_sep)
  · exact fun hsep_f => corollary_3_to_theorem_10_3 hsep_f hsf

/-- **Theorem 11.5** (§11.2, printed p. 95 / PDF p. 103; see `QUEUE.md` on `f = 0`):
*"Suppose that `f ∈ K[x]` and that `L : K` is a splitting field extension for `f`. If `f` is
separable then `|Γ(f)| = [L : K]` and `K = φ(Γ(f))`; otherwise `|Γ(f)| < [L : K]` and `K` is a
proper subfield of `φ(Γ(f))`."*
*(OCR warning verified against 160 DPI scan p. 95 / PDF p. 103: `garling1986_pages.txt` corrupts
`[L : K]` to `[L : ~]`.)* -/
theorem theorem_11_5 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) (hsf : IsGarlingSplittingFieldExtension K L f) :
    let K_sub := (algebraMap K L).fieldRange
    let K₀ := garlingPhi (garlingPolyGaloisSubgroup K L f : Set (GarlingAut L))
    (IsGarlingSeparablePoly f →
      setOrder (GarlingPolyGaloisGroup K L f) = extDegree K L ∧
      Nat.card (GarlingPolyGaloisGroup K L f) = Module.finrank K L ∧ K_sub = K₀) ∧
    (¬ IsGarlingSeparablePoly f →
      setOrder (GarlingPolyGaloisGroup K L f) < extDegree K L ∧
      Nat.card (GarlingPolyGaloisGroup K L f) < Module.finrank K L ∧ K_sub < K₀) := by
  intro K_sub K₀
  have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨f, hsf⟩
  have h114 := theorem_11_4_algebra K L hfin
  have hgal_iff : IsGarlingGaloisExtension K L ↔ IsGarlingSeparablePoly f := by
    unfold IsGarlingGaloisExtension
    rw [← isGarlingSeparableExtension_iff_poly_of_splittingField hf0 hsf]
    exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨hfin, hnorm, hs⟩⟩
  exact ⟨fun hsep => h114.1 (hgal_iff.mpr hsep),
    fun hnsep => h114.2 (fun hg => hnsep (hgal_iff.mp hg))⟩

/-- Subfield form of **Theorem 11.5** (§11.2, p. 95) for `K : Subfield L` and `f ≠ 0`. -/
theorem theorem_11_5_subfield {L : Type u} [Field L] (K : Subfield L)
    {f : K[X]} (hf0 : f ≠ 0) (hsf : IsGarlingSplittingFieldExtension K L f) :
    let G := garlingGamma K
    let K₀ := garlingPhi (G : Set (GarlingAut L))
    (IsGarlingSeparablePoly f →
      setOrder G = extDegree K L ∧ Nat.card G = Module.finrank K L ∧ K = K₀) ∧
    (¬ IsGarlingSeparablePoly f →
      setOrder G < extDegree K L ∧ Nat.card G < Module.finrank K L ∧ K < K₀) := by
  intro G K₀
  have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨f, hsf⟩
  have h114 := theorem_11_4 K hfin
  have hgal_iff : IsGarlingGaloisExtension K L ↔ IsGarlingSeparablePoly f := by
    unfold IsGarlingGaloisExtension
    rw [← isGarlingSeparableExtension_iff_poly_of_splittingField hf0 hsf]
    exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨hfin, hnorm, hs⟩⟩
  exact ⟨fun hsep => h114.1 (hgal_iff.mpr hsep),
    fun hnsep => h114.2 (fun hg => hnsep (hgal_iff.mp hg))⟩

/-- Unconditional characterization for **Theorem 11.5** across **all** `f ∈ K[X]` (including
`f = 0`), replacing `IsGarlingSeparablePoly f` by `f = 0 ∨ IsGarlingSeparablePoly f` (which
coincides with `IsGarlingSeparablePoly f` whenever `f ≠ 0` or `K` is perfect). -/
theorem theorem_11_5_unconditional {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f) :
    let K_sub := (algebraMap K L).fieldRange
    let K₀ := garlingPhi (garlingPolyGaloisSubgroup K L f : Set (GarlingAut L))
    ((f = 0 ∨ IsGarlingSeparablePoly f) →
      setOrder (GarlingPolyGaloisGroup K L f) = extDegree K L ∧
      Nat.card (GarlingPolyGaloisGroup K L f) = Module.finrank K L ∧ K_sub = K₀) ∧
    (¬ (f = 0 ∨ IsGarlingSeparablePoly f) →
      setOrder (GarlingPolyGaloisGroup K L f) < extDegree K L ∧
      Nat.card (GarlingPolyGaloisGroup K L f) < Module.finrank K L ∧ K_sub < K₀) := by
  by_cases hf0 : f = 0
  · subst hf0
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
      (isGarlingSplittingFieldExtension_zero_iff K L).mp hsf
    have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨0, hsf⟩
    have hsep : IsGarlingSeparableExtension K L :=
      corollary_2_to_theorem_10_3 hfin Fin.elim0
        (by rw [Set.range_eq_empty, IntermediateField.adjoin_empty, hbot_top])
        (fun i => Fin.elim0 i)
    have hgal : IsGarlingGaloisExtension K L := ⟨hfin, hnorm, hsep⟩
    have h114 := (theorem_11_4_algebra K L hgal.1).1 hgal
    exact ⟨fun _ => h114, fun hn => (hn (Or.inl rfl)).elim⟩
  · have h115 := theorem_11_5 hf0 hsf
    exact ⟨fun h => h115.1 (h.resolve_left hf0),
      fun hn => h115.2 (fun hs => hn (Or.inr hs))⟩

/-- Over any perfect field `K` (`IsGarlingPerfectField K`, e.g. `char K = 0`), **Theorem 11.5**
holds literally for **every** `f ∈ K[X]` including `f = 0`. -/
theorem theorem_11_5_perfect {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hperf : IsGarlingPerfectField K) {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f) :
    let K_sub := (algebraMap K L).fieldRange
    let K₀ := garlingPhi (garlingPolyGaloisSubgroup K L f : Set (GarlingAut L))
    setOrder (GarlingPolyGaloisGroup K L f) = extDegree K L ∧
    Nat.card (GarlingPolyGaloisGroup K L f) = Module.finrank K L ∧ K_sub = K₀ :=
  (theorem_11_5_unconditional hsf).1 (Or.inr (hperf f))

/-- Literal set `R = {α ∈ L : f(α) = 0}` of roots of `f ∈ K[X]` in `L` (§11.2, printed p. 95),
avoiding `Polynomial.rootSet`'s junk value `∅` at `f = 0`. -/
def garlingRootSet (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (f : K[X]) :
    Set L :=
  {α : L | Polynomial.aeval α f = 0}

@[simp]
theorem mem_garlingRootSet_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {α : L} :
    α ∈ garlingRootSet K L f ↔ Polynomial.aeval α f = 0 := Iff.rfl

/-- For `f ≠ 0`, `garlingRootSet K L f` coincides with Mathlib's `f.rootSet L`. -/
theorem garlingRootSet_eq_rootSet {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) :
    garlingRootSet K L f = f.rootSet L := by
  ext α
  rw [mem_garlingRootSet_iff, Polynomial.mem_rootSet_of_ne hf0]

/-- Permutation `σ|_R ∈ Σ_R` induced by `σ ∈ Γ_K(f)` on the root set `R = garlingRootSet K L f`
(§11.2, `Theorem 11.6`, printed p. 95). -/
def garlingRootPerm (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (f : K[X])
    (σ : GarlingPolyGaloisGroup K L f) : Equiv.Perm (garlingRootSet K L f) where
  toFun α := ⟨σ α.1, by
    have h : σ (Polynomial.aeval α.1 f) = Polynomial.aeval (σ α.1) f :=
      (Polynomial.aeval_algHom_apply σ.toAlgHom α.1 f).symm
    exact h.symm.trans (by rw [α.2, map_zero])⟩
  invFun α := ⟨σ.symm α.1, by
    have h : σ.symm (Polynomial.aeval α.1 f) = Polynomial.aeval (σ.symm α.1) f :=
      (Polynomial.aeval_algHom_apply σ.symm.toAlgHom α.1 f).symm
    exact h.symm.trans (by rw [α.2, map_zero])⟩
  left_inv α := Subtype.ext (σ.symm_apply_apply α.1)
  right_inv α := Subtype.ext (σ.apply_symm_apply α.1)

/-- Group homomorphism `σ ↦ σ|_R` from `Γ_K(f)` into `Σ_R = Equiv.Perm (garlingRootSet K L f)`
(§11.2, `Theorem 11.6`, printed p. 95). -/
def garlingRootPermHom (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (f : K[X]) :
    GarlingPolyGaloisGroup K L f →* Equiv.Perm (garlingRootSet K L f) where
  toFun := garlingRootPerm K L f
  map_one' := by ext α; rfl
  map_mul' σ₁ σ₂ := by ext α; rfl

@[simp]
theorem garlingRootPermHom_apply {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (σ : GarlingPolyGaloisGroup K L f) (α : garlingRootSet K L f) :
    (garlingRootPermHom K L f σ α : L) = σ α.1 := rfl

/-- **Theorem 11.6** (§11.2, printed p. 95 / PDF p. 103):
*"Suppose that `f ∈ K[x]` and that `L : K` is a splitting field extension for `f` over `K`. Let `R`
denote the set of roots of `f` in `L`. Each `σ` in `Γ(f)` defines a permutation of `R`, so that we
have a mapping from `Γ(f)` into the group `Σ_R` of permutations of `R`. This mapping is a group
homomorphism, and is one–one."*

Holds literally for **every** `f ∈ K[x]` (including `f = 0` and constants `n = 0`). -/
theorem theorem_11_6 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsf : IsGarlingSplittingFieldExtension K L f) :
    Function.Injective (garlingRootPermHom K L f) := by
  intro σ τ hστ
  by_cases hf0 : f = 0
  · subst hf0
    ext x
    have hx : x ∈ garlingRootSet K L 0 := by simp [garlingRootSet]
    exact congrArg Subtype.val (Equiv.congr_fun hστ ⟨x, hx⟩)
  · obtain ⟨n, c, α, hexp⟩ := hsf.1
    have hroots : Set.range α = garlingRootSet K L f := by
      rw [garlingRootSet_eq_rootSet hf0]
      exact (garlingSplitsExplicit_props hf0 hexp).2.2.2
    have hadj_top : IntermediateField.adjoin K (garlingRootSet K L f) = ⊤ := by
      rw [← hroots]
      have h71 : IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K (Set.range α)) f :=
        theorem_7_1 hf0 hexp
      by_contra hne
      exact hsf.2 (IntermediateField.adjoin K (Set.range α)) hne h71.1
    let F_eq : IntermediateField K L :=
      { (AlgHom.equalizer σ.toAlgHom τ.toAlgHom) with
        inv_mem' := fun {a} ha => by
          change σ a⁻¹ = τ a⁻¹
          rw [map_inv₀, map_inv₀]
          exact congrArg Inv.inv ha }
    have htop_le : (⊤ : IntermediateField K L) ≤ F_eq := by
      rw [← hadj_top, IntermediateField.adjoin_le_iff]
      intro r hr
      exact congrArg Subtype.val (Equiv.congr_fun hστ ⟨r, hr⟩)
    ext x
    exact htop_le (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K L))

/-- Garling's prose definition that a group `G` *acts transitively* on `X`
(§11.2, printed p. 95 / PDF p. 103): for any `α, β ∈ X`, there exists `σ ∈ G` sending `α` to `β`. -/
def GarlingActsTransitively (G : Type*) (X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ α β : X, ∃ σ : G, σ • α = β

theorem garlingActsTransitively_iff_isPretransitive (G : Type*) (X : Type*)
    [Group G] [MulAction G X] :
    GarlingActsTransitively G X ↔ MulAction.IsPretransitive G X :=
  ⟨fun h => ⟨h⟩, fun h => h.exists_smul_eq⟩

/-- Subgroup action of `H ≤ Equiv.Perm X` on `X` is transitive iff `∀ x y : X, ∃ σ ∈ H, σ x = y`. -/
def SubgroupActsTransitively {X : Type*} (H : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x y : X, ∃ σ ∈ H, σ x = y

/-- §11.2 prose observation (printed p. 95 / PDF p. 103): by `Corollary 2` to `Theorem 7.5`, if
`f ∈ K[x]` is irreducible and `L : K` is a splitting field extension for `f`, then `Γ(f)` acts
transitively on the roots of `f` in `L`. -/
theorem irreducible_imp_galoisGroup_actsTransitively
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hirr : Irreducible f) (hsf : IsGarlingSplittingFieldExtension K L f) :
    SubgroupActsTransitively (garlingRootPermHom K L f).range := by
  intro α β
  obtain ⟨σ, hσ⟩ := corollary_2_to_theorem_7_5_algEquiv hirr hsf α.2 β.2
  exact ⟨garlingRootPermHom K L f σ, ⟨σ, rfl⟩, Subtype.ext hσ⟩

/-- §11.2 unnumbered post-proof prose converse (printed p. 95 / PDF p. 103; `BRIEF.md` Flag 4):
*"Conversely, suppose that `f` is a monic polynomial of degree `n` in `K[x]` which has `n` distinct
roots in a splitting field `L`, and that `Γ(f)` acts transitively on the roots of `f` ... it follows
that `f` is irreducible."* (`1 ≤ n` makes explicit `Let α be a root of f`; at `n = 0`, `f = 1` is a
unit.) -/
theorem irreducible_of_monic_distinct_roots_transitive
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hn : 1 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (_hsf : IsGarlingSplittingFieldExtension K L f)
    (hdist : (garlingRootSet K L f).ncard = n)
    (htrans : SubgroupActsTransitively (garlingRootPermHom K L f).range) :
    Irreducible f := by
  classical
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hnonempty : (garlingRootSet K L f).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty.mp hemp, Set.ncard_empty] at hdist
    omega
  obtain ⟨α, hα⟩ := hnonempty
  have hα_alg : IsGarlingAlgebraic K α := ⟨f, hf0, hα⟩
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα_alg
  let m : K[X] := minpoly K α
  have hm_monic : m.Monic := minpoly.monic hint
  have hm_irr : Irreducible m := minpoly.irreducible hint
  have hm_dvd : m ∣ f := minpoly.dvd K α hα
  have hall_roots : garlingRootSet K L f ⊆ (m.map (algebraMap K L)).roots.toFinset := by
    intro β hβ
    obtain ⟨_, ⟨σ, rfl⟩, hσα⟩ := htrans ⟨α, hα⟩ ⟨β, hβ⟩
    have hβ_eq : σ α = β := congrArg Subtype.val hσα
    have hm_β : Polynomial.aeval β m = 0 := by
      rw [← hβ_eq]
      have h : σ (Polynomial.aeval α m) = Polynomial.aeval (σ α) m :=
        (Polynomial.aeval_algHom_apply σ.toAlgHom α m).symm
      exact h.symm.trans (by rw [minpoly.aeval K α, map_zero])
    rw [Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots (Polynomial.map_monic_ne_zero hm_monic),
      Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hm_β
  have hm_fin_card : n ≤ (m.map (algebraMap K L)).roots.toFinset.card := by
    rw [← hdist, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hall_roots (Finset.finite_toSet _)
  have hm_deg_ge : n ≤ m.natDegree := by
    have h1 : (m.map (algebraMap K L)).roots.toFinset.card ≤
        (m.map (algebraMap K L)).roots.card := Multiset.toFinset_card_le _
    have h2 : (m.map (algebraMap K L)).roots.card ≤ (m.map (algebraMap K L)).natDegree :=
      Polynomial.card_roots' _
    rw [hm_monic.natDegree_map] at h2
    omega
  obtain ⟨q, hfq⟩ := hm_dvd
  have hq0 : q ≠ 0 := fun h0 => hf0 (by rw [hfq, h0, mul_zero])
  have hdeg_sum : n = m.natDegree + q.natDegree := by
    rw [← hdeg, hfq, Polynomial.natDegree_mul hm_monic.ne_zero hq0]
  have hq_deg0 : q.natDegree = 0 := by omega
  have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
  have hqlc : q.coeff 0 = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hfq
    rw [hmonic.leadingCoeff, Polynomial.leadingCoeff_mul, hm_monic.leadingCoeff, one_mul,
      Polynomial.leadingCoeff, hq_deg0] at hlc
    exact hlc.symm
  have hmf : f = m := by rw [hfq, hqc, hqlc, map_one, mul_one]
  exact hmf ▸ hm_irr

/-- Degenerate `n = 0` (`f = 1`) witness for §11.2's unnumbered prose converse (`BRIEF.md` Flag 4):
`f = 1 ∈ ℚ[X]` is monic of degree `0`, has `0` distinct roots in its splitting field `ℚ`, and
vacuously has a transitive Galois action on `∅`, yet is a unit (`¬ Irreducible`). -/
theorem monic_zero_deg_not_irreducible_counterexample :
    let f : ℚ[X] := 1
    f.Monic ∧ f.natDegree = 0 ∧ IsGarlingSplittingFieldExtension ℚ ℚ f ∧
    (garlingRootSet ℚ ℚ f).ncard = 0 ∧
    SubgroupActsTransitively (garlingRootPermHom ℚ ℚ f).range ∧
    ¬ Irreducible f := by
  refine ⟨Polynomial.monic_one, Polynomial.natDegree_one, ?_, ?_, ?_, not_irreducible_one⟩
  · refine ⟨⟨0, 1, Fin.elim0, ?_⟩, fun M hne _ => hne (Subsingleton.elim M ⊤)⟩
    dsimp [GarlingSplitsExplicit]
    simp
  · have hemp : garlingRootSet ℚ ℚ (1 : ℚ[X]) = ∅ := by
      ext x
      simp [garlingRootSet]
    rw [hemp, Set.ncard_empty]
  · intro α
    exact ((by simp [garlingRootSet] : α.1 ∉ garlingRootSet ℚ ℚ (1 : ℚ[X])) α.2).elim

/-! ### §11.2 Exercises 11.5–11.7 (printed pp. 95–96, PDF pp. 103–104) -/

/-- Conjugacy relation `g H₁ g⁻¹ = H₂` on subgroups of a group `G` (`Exercise 11.5`). -/
def IsConjugateSubgroup {G : Type*} [Group G] (H₁ H₂ : Subgroup G) : Prop :=
  ∃ g : G, H₁.map (MulAut.conj g).toMonoidHom = H₂

theorem isConjugateSubgroup_refl {G : Type*} [Group G] (H : Subgroup G) :
    IsConjugateSubgroup H H :=
  ⟨1, by ext x; simp⟩

theorem isConjugateSubgroup_symm {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (h : IsConjugateSubgroup H₁ H₂) : IsConjugateSubgroup H₂ H₁ := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩

theorem isConjugateSubgroup_trans {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G}
    (h₁₂ : IsConjugateSubgroup H₁ H₂) (h₂₃ : IsConjugateSubgroup H₂ H₃) :
    IsConjugateSubgroup H₁ H₃ := by
  obtain ⟨g₁, rfl⟩ := h₁₂
  obtain ⟨g₂, rfl⟩ := h₂₃
  refine ⟨g₂ * g₁, ?_⟩
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g₁ * y * g₁⁻¹, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩

theorem isConjugateSubgroup_natCard_eq {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (h : IsConjugateSubgroup H₁ H₂) : Nat.card H₁ = Nat.card H₂ := by
  obtain ⟨g, rfl⟩ := h
  exact (Nat.card_congr ((MulAut.conj g).subgroupMap H₁).toEquiv)

theorem isConjugateSubgroup_actsTransitively_iff {X : Type*}
    {H₁ H₂ : Subgroup (Equiv.Perm X)} (h : IsConjugateSubgroup H₁ H₂) :
    SubgroupActsTransitively H₁ ↔ SubgroupActsTransitively H₂ := by
  suffices ∀ {A B : Subgroup (Equiv.Perm X)},
      IsConjugateSubgroup A B → SubgroupActsTransitively A → SubgroupActsTransitively B from
    ⟨this h, this (isConjugateSubgroup_symm h)⟩
  rintro A _ ⟨g, rfl⟩ htr x y
  obtain ⟨σ, hσA, hσxy⟩ := htr (g.symm x) (g.symm y)
  refine ⟨g * σ * g⁻¹, Subgroup.mem_map.mpr ⟨σ, hσA, rfl⟩, ?_⟩
  change g (σ (g.symm x)) = y
  rw [hσxy, g.apply_symm_apply]

/-- Orbit-stabilizer divisibility and fixed-point-free criterion for a transitive subgroup
`H ≤ Equiv.Perm X` on a finite non-empty set `X`. -/
theorem card_dvd_and_fixedPointFree_of_transitive {X : Type*} [Fintype X] [Nonempty X]
    {H : Subgroup (Equiv.Perm X)} (htr : SubgroupActsTransitively H) :
    Fintype.card X ∣ Nat.card H ∧
    (Nat.card H = Fintype.card X → ∀ σ ∈ H, ∀ x : X, σ x = x → σ = 1) := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  have hstab : ∀ x₀ : X,
      ∃ S : Subgroup H,
        (∀ h : H, h ∈ S ↔ h.1 x₀ = x₀) ∧ S.index = Fintype.card X := by
    intro x₀
    let S : Subgroup H :=
      { carrier := {h : H | h.1 x₀ = x₀}
        mul_mem' := fun {a b} ha hb => by change a.1 (b.1 x₀) = x₀; rw [hb, ha]
        one_mem' := rfl
        inv_mem' := fun {a} ha => by
          change a.1.symm x₀ = x₀
          have h' := congrArg a.1.symm ha
          simpa using h'.symm }
    let φ : H ⧸ S → X := Quotient.lift (fun h : H => h.1 x₀) fun a b hab => by
      have hmem : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
      have heq : a.1.symm (b.1 x₀) = x₀ := hmem
      have h' := congrArg a.1 heq
      simpa using h'.symm
    have hφ_bij : Function.Bijective φ := by
      refine ⟨fun q₁ q₂ hq => ?_, fun y => ?_⟩
      · refine Quotient.inductionOn₂ q₁ q₂ (fun a b hab => ?_) hq
        refine (QuotientGroup.eq (s := S)).mpr ?_
        change a.1.symm (b.1 x₀) = x₀
        have hab' : a.1 x₀ = b.1 x₀ := hab
        rw [← hab', a.1.symm_apply_apply]
      · obtain ⟨σ, hσH, hσy⟩ := htr x₀ y
        exact ⟨QuotientGroup.mk ⟨σ, hσH⟩, hσy⟩
    have hidx : S.index = Fintype.card X := by
      rw [Subgroup.index, Nat.card_congr (Equiv.ofBijective φ hφ_bij), Nat.card_eq_fintype_card]
    exact ⟨S, fun _ => Iff.rfl, hidx⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨S₀, _, hidx₀⟩ := hstab x₀
  have hdvd : Fintype.card X ∣ Nat.card H := by
    rw [← hidx₀, ← S₀.card_mul_index]
    exact dvd_mul_left _ _
  refine ⟨hdvd, fun hcard σ hσ x hx => ?_⟩
  obtain ⟨Sx, hSx_mem, hidx_x⟩ := hstab x
  have hmul := Sx.card_mul_index
  rw [hidx_x, hcard] at hmul
  have hpos : 0 < Fintype.card X := Fintype.card_pos
  have hcard1 : Nat.card Sx = 1 := by nlinarith
  have hsub : Subsingleton Sx := (Nat.card_eq_one_iff_unique.mp hcard1).1
  have hmem : (⟨σ, hσ⟩ : H) ∈ Sx := (hSx_mem _).mpr hx
  have heq1 : (⟨⟨σ, hσ⟩, hmem⟩ : Sx) = 1 := @Subsingleton.elim _ hsub _ 1
  exact congrArg (fun u : Sx => u.1.1) heq1

/-- Canonical permutation action of `DihedralGroup n` on `ZMod n`:
`r i ↦ (x ↦ x - i)` and `sr i ↦ (x ↦ i - x)`. -/
def dihedralZModPerm (n : ℕ) : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun
    | DihedralGroup.r i =>
        { toFun := fun x => x - i
          invFun := fun x => x + i
          left_inv := fun x => sub_add_cancel x i
          right_inv := fun x => add_sub_cancel_right x i }
    | DihedralGroup.sr i =>
        { toFun := fun x => i - x
          invFun := fun x => i - x
          left_inv := fun x => sub_sub_cancel i x
          right_inv := fun x => sub_sub_cancel i x }
  map_one' := by
    ext x
    change x - 0 = x
    exact sub_zero x
  map_mul' := by
    rintro (i | i) (j | j) <;> ext x <;> simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring

@[simp]
theorem dihedralZModPerm_r (n : ℕ) (i x : ZMod n) :
    dihedralZModPerm n (DihedralGroup.r i) x = x - i :=
  rfl

@[simp]
theorem dihedralZModPerm_sr (n : ℕ) (i x : ZMod n) :
    dihedralZModPerm n (DihedralGroup.sr i) x = i - x :=
  rfl

theorem dihedralZModPerm_injective {n : ℕ} [NeZero n] (hn2 : (2 : ZMod n) ≠ 0) :
    Function.Injective (dihedralZModPerm n) := by
  rintro (i | i) (j | j) hij
  · have e0 := Equiv.congr_fun hij 0
    simp only [dihedralZModPerm_r, zero_sub, neg_inj] at e0
    rw [e0]
  · exfalso
    have e0 := Equiv.congr_fun hij 0
    have e1 := Equiv.congr_fun hij 1
    simp only [dihedralZModPerm_r, dihedralZModPerm_sr, zero_sub] at e0 e1
    have h2 : (2 : ZMod n) = 0 := by linear_combination e1 - e0
    exact hn2 h2
  · exfalso
    have e0 := Equiv.congr_fun hij 0
    have e1 := Equiv.congr_fun hij 1
    simp only [dihedralZModPerm_r, dihedralZModPerm_sr, zero_sub] at e0 e1
    have h2 : (2 : ZMod n) = 0 := by linear_combination e0 - e1
    exact hn2 h2
  · have e0 := Equiv.congr_fun hij 0
    simp only [dihedralZModPerm_sr, sub_zero] at e0
    rw [e0]

/-- For `n + 1`, `ZMod (n + 1)` is definitionally `Fin (n + 1)`, giving a canonical injective
action `DihedralGroup (n + 1) →* Equiv.Perm (Fin (n + 1))` whenever `(2 : ZMod (n + 1)) ≠ 0`. -/
abbrev dihedralFinPermHom (n : ℕ) : DihedralGroup (n + 1) →* Equiv.Perm (Fin (n + 1)) :=
  dihedralZModPerm (n + 1)

theorem dihedralFinPermHom_injective {n : ℕ} (hn2 : (2 : ZMod (n + 1)) ≠ 0) :
    Function.Injective (dihedralFinPermHom n) :=
  dihedralZModPerm_injective hn2

theorem dihedralFinPermHom_range_actsTransitively (n : ℕ) :
    SubgroupActsTransitively (dihedralFinPermHom n).range := by
  intro x y
  let zx : ZMod (n + 1) := x
  let zy : ZMod (n + 1) := y
  refine ⟨dihedralFinPermHom n (DihedralGroup.r (zx - zy)), ⟨_, rfl⟩, ?_⟩
  change dihedralZModPerm (n + 1) (DihedralGroup.r (zx - zy)) zx = zy
  rw [dihedralZModPerm_r]
  ring

/-! #### `Σ₃` Transitive Subgroups (`Exercise 11.5`, part 1) -/

/-- The `2` transitive subgroups of `Σ₃`: `A₃` (order `3`) and `Σ₃` (order `6`). -/
def s3TransitiveModel : Fin 2 → Subgroup (Equiv.Perm (Fin 3))
  | 0 => alternatingGroup (Fin 3)
  | 1 => ⊤

theorem exercise_11_5_s3 :
    (Nat.card (s3TransitiveModel 0) = 3 ∧ Nat.card (s3TransitiveModel 1) = 6) ∧
    (∀ i : Fin 2, SubgroupActsTransitively (s3TransitiveModel i)) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 3)),
      SubgroupActsTransitively H ↔ H = alternatingGroup (Fin 3) ∨ H = ⊤) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 3)),
      SubgroupActsTransitively H → ∃! i : Fin 2, IsConjugateSubgroup (s3TransitiveModel i) H) := by
  have hcardA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcardS3 : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) = 6 := by
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have hrot_even : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hrot_all : ∀ a b : Fin 3,
      a = b ∨ finRotate 3 a = b ∨ (finRotate 3 * finRotate 3) a = b := by decide
  have htrA3 : SubgroupActsTransitively (alternatingGroup (Fin 3)) := by
    intro x y
    rcases hrot_all x y with rfl | h1 | h2
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · exact ⟨finRotate 3, hrot_even, h1⟩
    · exact ⟨finRotate 3 * finRotate 3, Subgroup.mul_mem _ hrot_even hrot_even, h2⟩
  have htrS3 : SubgroupActsTransitively (⊤ : Subgroup (Equiv.Perm (Fin 3))) :=
    fun x y => by
      obtain ⟨σ, _, hσ⟩ := htrA3 x y
      exact ⟨σ, Subgroup.mem_top σ, hσ⟩
  have hiff : ∀ H : Subgroup (Equiv.Perm (Fin 3)),
      SubgroupActsTransitively H ↔ H = alternatingGroup (Fin 3) ∨ H = ⊤ := by
    intro H
    refine ⟨fun htr => ?_, ?_⟩
    · have hdvd3 : 3 ∣ Nat.card H := (card_dvd_and_fixedPointFree_of_transitive htr).1
      have hdvd6 : Nat.card H ∣ 6 := by
        have hd := H.card_subgroup_dvd_card
        rwa [Nat.card_perm, Nat.card_fin] at hd
      have hpos : 0 < Nat.card H := Nat.card_pos
      have hle6 : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hdvd6
      have hc_cases : Nat.card H = 3 ∨ Nat.card H = 6 := by omega
      have hfac3 : (3 : ℕ).factorial = 6 := rfl
      rcases hc_cases with hc3 | hc6
      · left
        have hidx : H.index = 2 := by
          have hm := H.card_mul_index
          rw [Nat.card_perm, Nat.card_fin, hfac3, hc3] at hm
          omega
        exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
      · right
        have hidx : H.index = 1 := by
          have hm := H.card_mul_index
          rw [Nat.card_perm, Nat.card_fin, hfac3, hc6] at hm
          omega
        exact Subgroup.index_eq_one.mp hidx
    · rintro (rfl | rfl)
      · exact htrA3
      · exact htrS3
  refine ⟨⟨hcardA3, hcardS3⟩, ?_, hiff, ?_⟩
  · intro i
    fin_cases i
    · exact htrA3
    · exact htrS3
  · intro H htr
    rcases (hiff H).mp htr with rfl | rfl
    · refine ⟨0, isConjugateSubgroup_refl _, fun j hj => ?_⟩
      fin_cases j
      · rfl
      · exfalso
        have hc := isConjugateSubgroup_natCard_eq hj
        dsimp [s3TransitiveModel] at hc
        omega
    · refine ⟨1, isConjugateSubgroup_refl _, fun j hj => ?_⟩
      fin_cases j
      · exfalso
        have hc := isConjugateSubgroup_natCard_eq hj
        dsimp [s3TransitiveModel] at hc
        omega
      · rfl

/-! #### `Σ₄` Transitive Subgroups (`Exercise 11.5`, part 2) & Sylow-`2` `D₄` Lemma -/

/-- Explicit `4`-element `Finset` of `V₄ = {1, (0 1)(2 3), (0 2)(1 3), (0 3)(1 2)}` in `Σ₄`. -/
def s4V4Finset : Finset (Equiv.Perm (Fin 4)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3,
   Equiv.swap 0 2 * Equiv.swap 1 3,
   Equiv.swap 0 3 * Equiv.swap 1 2}

theorem mem_s4V4Finset_iff (σ : Equiv.Perm (Fin 4)) :
    σ ∈ s4V4Finset ↔ Equiv.Perm.sign σ = 1 ∧ σ * σ = 1 := by
  revert σ
  decide

/-- Klein four-subgroup `V₄ = {σ ∈ A₄ : σ² = 1}` of `Σ₄` (order `4`, normal). -/
def s4V4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {σ : Equiv.Perm (Fin 4) | σ ∈ s4V4Finset}
  mul_mem' := by
    have hmul : ∀ a ∈ s4V4Finset, ∀ b ∈ s4V4Finset, a * b ∈ s4V4Finset := by decide
    intro a b ha hb
    exact hmul a ha b hb
  one_mem' := by decide
  inv_mem' := by
    have hinv : ∀ a ∈ s4V4Finset, a⁻¹ ∈ s4V4Finset := by decide
    intro a ha
    exact hinv a ha

instance : DecidablePred (· ∈ s4V4) :=
  fun σ => inferInstanceAs (Decidable (σ ∈ s4V4Finset))

/-- Cyclic subgroup `C₄ = ⟨(0 1 2 3)⟩` of `Σ₄` (order `4`). -/
def s4C4 : Subgroup (Equiv.Perm (Fin 4)) :=
  Subgroup.zpowers (finRotate 4)

/-- Dihedral subgroup `D₄ ≤ Σ₄` (order `8`, image of `DihedralGroup 4`). -/
def s4D4 : Subgroup (Equiv.Perm (Fin 4)) :=
  (dihedralFinPermHom 3).range

/-- Explicit isomorphism `DihedralGroup 4 ≃* s4D4`. -/
noncomputable def dihedral4MulEquivS4D4 : DihedralGroup 4 ≃* s4D4 :=
  MulEquiv.ofBijective (dihedralFinPermHom 3).rangeRestrict
    ⟨fun a b hab => dihedralFinPermHom_injective (by decide) (congrArg Subtype.val hab),
     (dihedralFinPermHom 3).rangeRestrict_surjective⟩

theorem natCard_s4D4 : Nat.card s4D4 = 8 := by
  rw [← Nat.card_congr dihedral4MulEquivS4D4.toEquiv, DihedralGroup.nat_card]

/-- Helper turning a `p`-subgroup `P ≤ G` with `¬ p ∣ P.index` into a `Sylow p G` with
definitional underlying subgroup `P`. -/
def mkSylowOfNotDvdIndex {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) {k : ℕ} (hcard : Nat.card P = p ^ k) (hndvd : ¬ p ∣ P.index) :
    Sylow p G :=
  (IsPGroup.of_card hcard).toSylow hndvd

@[simp]
theorem coe_mkSylowOfNotDvdIndex {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) {k : ℕ} (hcard : Nat.card P = p ^ k) (hndvd : ¬ p ∣ P.index) :
    (mkSylowOfNotDvdIndex P hcard hndvd : Subgroup G) = P :=
  rfl

/-- **Key Sylow-`2` lemma for `Σ₄`:** Every subgroup `H ≤ Equiv.Perm (Fin 4)` of order `8` is
conjugate in `Σ₄` to `s4D4` and isomorphic as a group to `DihedralGroup 4` (`D₄`). -/
theorem s4_subgroup_card_eight_conj_d4 (H : Subgroup (Equiv.Perm (Fin 4)))
    (hcard : Nat.card H = 8) :
    IsConjugateSubgroup s4D4 H ∧ Nonempty (H ≃* DihedralGroup 4) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd_of_eight : ∀ K : Subgroup (Equiv.Perm (Fin 4)), Nat.card K = 8 → ¬ 2 ∣ K.index := by
    intro K hKc
    have hm := K.card_mul_index
    have hf4 : (4 : ℕ).factorial = 24 := rfl
    rw [Nat.card_perm, Nat.card_fin, hf4, hKc] at hm
    omega
  let P_D4 : Sylow 2 (Equiv.Perm (Fin 4)) :=
    mkSylowOfNotDvdIndex s4D4 (natCard_s4D4.trans (by decide : 8 = 2 ^ 3))
      (hndvd_of_eight s4D4 natCard_s4D4)
  let P_H : Sylow 2 (Equiv.Perm (Fin 4)) :=
    mkSylowOfNotDvdIndex H (hcard.trans (by decide : 8 = 2 ^ 3))
      (hndvd_of_eight H hcard)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 4)) P_D4 P_H
  have hconj : IsConjugateSubgroup s4D4 H := by
    rw [Sylow.ext_iff, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.pointwise_smul_def] at hg
    exact ⟨g, hg⟩
  have hiso : Nonempty (H ≃* DihedralGroup 4) := by
    obtain ⟨g, rfl⟩ := hconj
    exact ⟨((MulAut.conj g).subgroupMap s4D4).symm.trans dihedral4MulEquivS4D4.symm⟩
  exact ⟨hconj, hiso⟩

/-- The `5` conjugacy-class model transitive subgroups of `Σ₄`:
`V₄` (`4`), `C₄` (`4`), `D₄` (`8`), `A₄` (`12`), and `Σ₄` (`24`). -/
def s4TransitiveModel : Fin 5 → Subgroup (Equiv.Perm (Fin 4))
  | 0 => s4V4
  | 1 => s4C4
  | 2 => s4D4
  | 3 => alternatingGroup (Fin 4)
  | 4 => ⊤

theorem exercise_11_5_s4 :
    (∀ i : Fin 5, Nat.card (s4TransitiveModel i) = (![4, 4, 8, 12, 24] : Fin 5 → ℕ) i) ∧
    (∀ i : Fin 5, SubgroupActsTransitively (s4TransitiveModel i)) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 4)),
      SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s4TransitiveModel i) H) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 4)),
      SubgroupActsTransitively H → ∃! i : Fin 5, IsConjugateSubgroup (s4TransitiveModel i) H) := by
  have hmemV4_dec : ∀ τ : Equiv.Perm (Fin 4),
      τ * τ = 1 → (τ = 1 ∨ ∀ x : Fin 4, τ x ≠ x) → τ ∈ s4V4Finset := by decide
  have hall_V4 : ∀ a b : Fin 4, ∃ σ ∈ s4V4Finset, σ a = b := by decide
  have hc0 : Nat.card s4V4 = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hc1 : Nat.card s4C4 = 4 := by
    unfold s4C4
    rw [Nat.card_zpowers]
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, fun m hm hpos => ?_⟩
    interval_cases m <;> decide
  have hc2 : Nat.card s4D4 = 8 := natCard_s4D4
  have hc3 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hc4 : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 4))) = 24 := by
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have hcards : ∀ i : Fin 5, Nat.card (s4TransitiveModel i) = (![4, 4, 8, 12, 24] : Fin 5 → ℕ) i := by
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
  have htr0 : SubgroupActsTransitively s4V4 := by
    intro x y
    obtain ⟨σ, hσ, hxy⟩ := hall_V4 x y
    exact ⟨σ, hσ, hxy⟩
  have htr1 : SubgroupActsTransitively s4C4 := by
    intro x y
    let r := finRotate 4
    have hall : ∀ a b : Fin 4,
        a = b ∨ r a = b ∨ (r * r) a = b ∨ (r * r * r) a = b := by decide
    rcases hall x y with rfl | h1 | h2 | h3
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · exact ⟨r, Subgroup.mem_zpowers r, h1⟩
    · exact ⟨r * r, Subgroup.mul_mem _ (Subgroup.mem_zpowers r) (Subgroup.mem_zpowers r), h2⟩
    · exact ⟨r * r * r, Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_zpowers r) (Subgroup.mem_zpowers r))
        (Subgroup.mem_zpowers r), h3⟩
  have htr2 : SubgroupActsTransitively s4D4 := dihedralFinPermHom_range_actsTransitively 3
  have htr3 : SubgroupActsTransitively (alternatingGroup (Fin 4)) := by
    intro x y
    obtain ⟨σ, hσ, hxy⟩ := htr0 x y
    exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr ((mem_s4V4Finset_iff σ).mp hσ).1, hxy⟩
  have htr4 : SubgroupActsTransitively (⊤ : Subgroup (Equiv.Perm (Fin 4))) :=
    fun x y => ⟨Equiv.swap x y, Subgroup.mem_top _, Equiv.swap_apply_left x y⟩
  have htrs : ∀ i : Fin 5, SubgroupActsTransitively (s4TransitiveModel i) := by
    intro i
    fin_cases i
    · exact htr0
    · exact htr1
    · exact htr2
    · exact htr3
    · exact htr4
  have hiff : ∀ H : Subgroup (Equiv.Perm (Fin 4)),
      SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s4TransitiveModel i) H := by
    intro H
    refine ⟨fun htr => ?_, ?_⟩
    · obtain ⟨hdvd4, hfpf⟩ := card_dvd_and_fixedPointFree_of_transitive htr
      rw [Fintype.card_fin] at hdvd4 hfpf
      have hdvd24 : Nat.card H ∣ 24 := by
        have hd := H.card_subgroup_dvd_card
        rwa [Nat.card_perm, Nat.card_fin] at hd
      have hpos : 0 < Nat.card H := Nat.card_pos
      have hle24 : Nat.card H ≤ 24 := Nat.le_of_dvd (by decide) hdvd24
      have hc_cases : Nat.card H = 4 ∨ Nat.card H = 8 ∨ Nat.card H = 12 ∨ Nat.card H = 24 := by
        rcases hdvd4 with ⟨k, hk⟩
        have hk_le : k ≤ 6 := by omega
        have hk_pos : 1 ≤ k := by omega
        interval_cases k
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hk))
        · exfalso; rw [hk] at hdvd24; norm_num at hdvd24
        · exfalso; rw [hk] at hdvd24; norm_num at hdvd24
        · exact Or.inr (Or.inr (Or.inr hk))
      have hf4 : (4 : ℕ).factorial = 24 := rfl
      rcases hc_cases with hc_4 | hc_8 | hc_12 | hc_24
      · classical
        by_cases hexp2 : ∀ σ ∈ H, σ * σ = 1
        · refine ⟨0, 1, ?_⟩
          have hle_V4 : H ≤ s4V4 := by
            intro σ hσ
            have hsq : σ * σ = 1 := hexp2 σ hσ
            have hfpf_σ : ∀ x : Fin 4, σ x = x → σ = 1 := hfpf hc_4 σ hσ
            refine hmemV4_dec σ hsq ?_
            by_cases h1 : σ = 1
            · exact Or.inl h1
            · exact Or.inr fun x hx => h1 (hfpf_σ x hx)
          have heq : H = s4V4 := Subgroup.eq_of_le_of_card_ge hle_V4 (by rw [hc0, hc_4])
          dsimp [s4TransitiveModel]
          rw [heq]
          ext x
          simp
        · push Not at hexp2
          obtain ⟨σ, hσH, hσ2⟩ := hexp2
          let _ : Fintype H := Fintype.ofFinite H
          have hσ4 : σ ^ 4 = 1 := by
            have hpow : (⟨σ, hσH⟩ : H) ^ Fintype.card H = 1 := pow_card_eq_one
            rw [← Nat.card_eq_fintype_card, hc_4] at hpow
            exact congrArg Subtype.val hpow
          have hord4 : orderOf (⟨σ, hσH⟩ : H) = 4 := by
            have hdvd : orderOf (⟨σ, hσH⟩ : H) ∣ 4 := by
              have hdvd0 := orderOf_dvd_natCard (⟨σ, hσH⟩ : H)
              rwa [hc_4] at hdvd0
            have hpos_o : 0 < orderOf (⟨σ, hσH⟩ : H) := orderOf_pos _
            have hle_o : orderOf (⟨σ, hσH⟩ : H) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
            interval_cases ho : orderOf (⟨σ, hσH⟩ : H)
            · exfalso
              have h1 := orderOf_eq_one_iff.mp ho
              have hσ1 : σ = 1 := congrArg Subtype.val h1
              exact hσ2 (by rw [hσ1, mul_one])
            · exfalso
              have hsq : (⟨σ, hσH⟩ : H) ^ 2 = 1 := ho ▸ pow_orderOf_eq_one _
              have hσ_sq : σ * σ = 1 := by simpa [sq] using congrArg Subtype.val hsq
              exact hσ2 hσ_sq
            · exfalso; norm_num at hdvd
            · rfl
          have hzpow_H : Subgroup.zpowers (⟨σ, hσH⟩ : H) = ⊤ := by
            apply Subgroup.eq_of_le_of_card_ge le_top
            rw [Subgroup.card_top, hc_4, Nat.card_zpowers, hord4]
          have hH_eq : H = Subgroup.zpowers σ := by
            apply le_antisymm
            · intro x hx
              have hmem_top : (⟨x, hx⟩ : H) ∈ Subgroup.zpowers (⟨σ, hσH⟩ : H) :=
                hzpow_H.symm ▸ Subgroup.mem_top _
              obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem_top
              exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
            · rw [Subgroup.zpowers_le]
              exact hσH
          -- Construct the conjugating permutation `g` via the orbit map `i ↦ (σ ^ i) 0`.
          let orb : Fin 4 → Fin 4 := fun i => (σ ^ i.val) 0
          have horb_surj : Function.Surjective orb := by
            intro y
            obtain ⟨τ, hτH, hτy⟩ := htr 0 y
            rw [hH_eq] at hτH
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτH
            let r : ℕ := (k % 4).toNat
            have hk_eq : k = (4 : ℤ) * (k / 4) + (r : ℤ) := by omega
            have hlt : r < 4 := by omega
            have hmod : σ ^ k = σ ^ r := by
              rw [hk_eq, zpow_add, zpow_mul, zpow_ofNat, hσ4, one_zpow, one_mul, zpow_natCast]
            refine ⟨⟨r, hlt⟩, ?_⟩
            dsimp [orb]
            rw [← hmod, hτy]
          let g : Equiv.Perm (Fin 4) :=
            Equiv.ofBijective orb ⟨Finite.injective_iff_surjective.mpr horb_surj, horb_surj⟩
          have hg_step : ∀ i : Fin 4, g (finRotate 4 i) = σ (g i) := by
            intro i
            change orb (finRotate 4 i) = σ (orb i)
            fin_cases i
            · change (σ ^ 1) 0 = σ ((σ ^ 0) 0); simp
            · change (σ ^ 2) 0 = σ ((σ ^ 1) 0); simp [pow_succ']
            · change (σ ^ 3) 0 = σ ((σ ^ 2) 0); simp [pow_succ']
            · change (σ ^ 0) 0 = σ ((σ ^ 3) 0)
              have h4 : (σ ^ 4) 0 = 0 := by rw [hσ4]; rfl
              simpa [pow_succ'] using h4.symm
          have hg : g * finRotate 4 * g⁻¹ = σ :=
            Equiv.ext fun x => by
              change g (finRotate 4 (g.symm x)) = σ x
              rw [hg_step, g.apply_symm_apply]
          refine ⟨1, g, ?_⟩
          rw [hH_eq]
          dsimp [s4TransitiveModel, s4C4]
          rw [MonoidHom.map_zpowers]
          congr 1
      · exact ⟨2, (s4_subgroup_card_eight_conj_d4 H hc_8).1⟩
      · refine ⟨3, 1, ?_⟩
        have hidx : H.index = 2 := by
          have hm := H.card_mul_index
          rw [Nat.card_perm, Nat.card_fin, hf4, hc_12] at hm
          omega
        have heq := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
        rw [heq]
        ext x; simp [s4TransitiveModel]
      · refine ⟨4, 1, ?_⟩
        have hidx : H.index = 1 := by
          have hm := H.card_mul_index
          rw [Nat.card_perm, Nat.card_fin, hf4, hc_24] at hm
          omega
        rw [Subgroup.index_eq_one.mp hidx]
        ext x; simp [s4TransitiveModel]
    · rintro ⟨i, hconj⟩
      exact (isConjugateSubgroup_actsTransitively_iff hconj).mp (htrs i)
  refine ⟨hcards, htrs, hiff, fun H htr => ?_⟩
  obtain ⟨i, hi⟩ := (hiff H).mp htr
  refine ⟨i, hi, fun j hj => ?_⟩
  have hci : (![4, 4, 8, 12, 24] : Fin 5 → ℕ) i = Nat.card H :=
    (hcards i).symm.trans (isConjugateSubgroup_natCard_eq hi)
  have hcj : (![4, 4, 8, 12, 24] : Fin 5 → ℕ) j = Nat.card H :=
    (hcards j).symm.trans (isConjugateSubgroup_natCard_eq hj)
  have hcard_ij : (![4, 4, 8, 12, 24] : Fin 5 → ℕ) j = (![4, 4, 8, 12, 24] : Fin 5 → ℕ) i :=
    hcj.trans hci.symm
  have hV4_not_C4 : ¬ IsConjugateSubgroup s4V4 s4C4 := by
    rintro ⟨g, hg⟩
    have hr_mem : finRotate 4 ∈ s4C4 := Subgroup.mem_zpowers _
    rw [← hg] at hr_mem
    obtain ⟨v, hv, hgv⟩ := Subgroup.mem_map.mp hr_mem
    have hv_sq : v * v = 1 := ((mem_s4V4Finset_iff v).mp hv).2
    have hr_sq : finRotate 4 * finRotate 4 = 1 := by
      rw [← hgv]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc (g * v * g⁻¹) * (g * v * g⁻¹)
          = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv_sq]; group
    have hr_ne : finRotate 4 * finRotate 4 ≠ 1 := by decide
    exact hr_ne hr_sq
  fin_cases i <;> fin_cases j <;> dsimp [s4TransitiveModel] at hi hj hcard_ij ⊢
  all_goals try (exfalso; norm_num at hcard_ij)
  · exfalso
    exact hV4_not_C4 (isConjugateSubgroup_trans hi (isConjugateSubgroup_symm hj))
  · exfalso
    exact hV4_not_C4 (isConjugateSubgroup_trans hj (isConjugateSubgroup_symm hi))

/-! #### `Σ₅` Transitive Subgroups (`Exercise 11.5`, part 3) -/

/-- Translation `x ↦ x + 1` on `ZMod 5` (definitionally `Equiv.Perm (Fin 5)`). -/
def s5ShiftPerm : Equiv.Perm (Fin 5) :=
  Equiv.addRight (1 : ZMod 5)

/-- Cyclic subgroup `C₅ ≤ Σ₅` (order `5`). -/
def s5C5 : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.zpowers s5ShiftPerm

/-- Dihedral subgroup `D₅ ≤ Σ₅` (order `10`, image of `DihedralGroup 5`). -/
def s5D5 : Subgroup (Equiv.Perm (Fin 5)) :=
  (dihedralFinPermHom 4).range

/-- Affine / Frobenius group `F₂₀ = AGL₁(ℤ₅)` as permutations of `ZMod 5 = Fin 5`:
elements are pairs `(a, b) ∈ (ZMod 5)ˣ × ZMod 5` acting by `x ↦ a * x + b`. -/
def agl1ZMod5Perm (u : (ZMod 5)ˣ × ZMod 5) : Equiv.Perm (ZMod 5) where
  toFun x := (u.1 : ZMod 5) * x + u.2
  invFun y := ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (y - u.2)
  left_inv x := by
    have hu : ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (u.1 : ZMod 5) = 1 := Units.inv_mul u.1
    calc ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * ((u.1 : ZMod 5) * x + u.2 - u.2)
        = (((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (u.1 : ZMod 5)) * x := by ring
      _ = x := by rw [hu, one_mul]
  right_inv y := by
    have hu : (u.1 : ZMod 5) * ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 1 := Units.mul_inv u.1
    calc (u.1 : ZMod 5) * (((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (y - u.2)) + u.2
        = ((u.1 : ZMod 5) * ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5)) * (y - u.2) + u.2 := by ring
      _ = y := by rw [hu, one_mul, sub_add_cancel]

@[simp]
theorem agl1ZMod5Perm_apply (u : (ZMod 5)ˣ × ZMod 5) (x : ZMod 5) :
    agl1ZMod5Perm u x = (u.1 : ZMod 5) * x + u.2 :=
  rfl

@[simp]
theorem agl1ZMod5Perm_symm_apply (u : (ZMod 5)ˣ × ZMod 5) (y : ZMod 5) :
    (agl1ZMod5Perm u).symm y = ((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (y - u.2) :=
  rfl

/-- Frobenius subgroup `F₂₀ ≤ Σ₅` (`{x ↦ a * x + b : a ∈ ℤ₅ˣ, b ∈ ℤ₅}`, order `20`). -/
abbrev agl1Fin5Perm (u : (ZMod 5)ˣ × ZMod 5) : Equiv.Perm (Fin 5) :=
  agl1ZMod5Perm u

def s5F20 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := Set.range agl1Fin5Perm
  mul_mem' := by
    rintro _ _ ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
    refine ⟨(u₁.1 * u₂.1, (u₁.1 : ZMod 5) * u₂.2 + u₁.2), Equiv.ext fun x : ZMod 5 => ?_⟩
    change agl1ZMod5Perm _ x = agl1ZMod5Perm u₁ (agl1ZMod5Perm u₂ x)
    simp only [agl1ZMod5Perm_apply, Units.val_mul]
    ring
  one_mem' := by
    refine ⟨(1, 0), Equiv.ext fun x : ZMod 5 => ?_⟩
    change agl1ZMod5Perm (1, 0) x = x
    simp
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    refine ⟨(u.1⁻¹, -(((u.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * u.2)), Equiv.ext fun y : ZMod 5 => ?_⟩
    change agl1ZMod5Perm _ y = (agl1ZMod5Perm u).symm y
    simp only [agl1ZMod5Perm_apply, agl1ZMod5Perm_symm_apply]
    ring

/-- The `5` conjugacy-class model transitive subgroups of `Σ₅`:
`C₅` (`5`), `D₅` (`10`), `F₂₀` (`20`), `A₅` (`60`), and `Σ₅` (`120`). -/
def s5TransitiveModel : Fin 5 → Subgroup (Equiv.Perm (Fin 5))
  | 0 => s5C5
  | 1 => s5D5
  | 2 => s5F20
  | 3 => alternatingGroup (Fin 5)
  | 4 => ⊤

theorem exercise_11_5_s5 :
    (∀ i : Fin 5, Nat.card (s5TransitiveModel i) = (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i) ∧
    (∀ i : Fin 5, SubgroupActsTransitively (s5TransitiveModel i)) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 5)),
      SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) H) ∧
    (∀ H : Subgroup (Equiv.Perm (Fin 5)),
      SubgroupActsTransitively H → ∃! i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) H) := by
  have hs5Shift_even : s5ShiftPerm ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hs5Shift_ne1 : s5ShiftPerm ≠ 1 := by decide
  have hs5Shift_ord : orderOf s5ShiftPerm = 5 := by
    rw [orderOf_eq_iff (by decide)]
    refine ⟨by decide, fun m hm hpos => ?_⟩
    interval_cases m <;> decide
  have hs5Shift_all : ∀ a b : Fin 5,
      a = b ∨ s5ShiftPerm a = b ∨ (s5ShiftPerm ^ 2) a = b ∨
      (s5ShiftPerm ^ 3) a = b ∨ (s5ShiftPerm ^ 4) a = b := by decide
  have hc_units5_fin : Fintype.card (ZMod 5)ˣ = 4 := by decide
  have hz_units5 : ∀ z : ZMod 5, IsUnit z → z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 := by decide
  have h2_ne0 : (2 : ZMod 5) ≠ 0 := by decide
  have h4_eq_m1 : (4 : ZMod 5) = ((-1 : (ZMod 5)ˣ) : ZMod 5) := by decide
  have h2_pow3 : (3 : ZMod 5) = (2 : ZMod 5) ^ 3 := by decide
  have h2_pow2 : (4 : ZMod 5) = (2 : ZMod 5) ^ 2 := by decide
  have h2_pow9 : (2 : ZMod 5) = ((2 : ZMod 5) ^ 3) ^ 3 := by decide
  have _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc_units5 : Nat.card (ZMod 5)ˣ = 4 :=
    (Nat.card_eq_fintype_card (α := (ZMod 5)ˣ)).trans hc_units5_fin
  have hc0 : Nat.card s5C5 = 5 := by
    unfold s5C5
    rw [Nat.card_zpowers, hs5Shift_ord]
  have hd5Equiv : DihedralGroup 5 ≃* s5D5 :=
    MulEquiv.ofBijective (dihedralFinPermHom 4).rangeRestrict
      ⟨fun a b hab => dihedralFinPermHom_injective (by decide) (congrArg Subtype.val hab),
       (dihedralFinPermHom 4).rangeRestrict_surjective⟩
  have hc1 : Nat.card s5D5 = 10 := by
    rw [← Nat.card_congr hd5Equiv.toEquiv, DihedralGroup.nat_card]
  let f20Map : (ZMod 5)ˣ × ZMod 5 → s5F20 := fun u => ⟨agl1Fin5Perm u, ⟨u, rfl⟩⟩
  have hf20_bij : Function.Bijective f20Map := by
    refine ⟨fun u₁ u₂ hu => ?_, fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩
    have hp : agl1ZMod5Perm u₁ = agl1ZMod5Perm u₂ := congrArg Subtype.val hu
    have h0 := Equiv.congr_fun hp (0 : ZMod 5)
    have h1 := Equiv.congr_fun hp (1 : ZMod 5)
    simp only [agl1ZMod5Perm_apply, mul_zero, zero_add, mul_one] at h0 h1
    have ha : (u₁.1 : ZMod 5) = (u₂.1 : ZMod 5) := by linear_combination h1 - h0
    exact Prod.ext (Units.ext ha) h0
  have hc2 : Nat.card s5F20 = 20 := by
    rw [← Nat.card_congr (Equiv.ofBijective f20Map hf20_bij), Nat.card_prod,
      hc_units5, Nat.card_zmod 5]
  have hc3 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hc4 : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 5))) = 120 := by
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have hcards : ∀ i : Fin 5,
      Nat.card (s5TransitiveModel i) = (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i := by
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
  have hC5_le_D5 : s5C5 ≤ s5D5 := by
    rw [s5C5, Subgroup.zpowers_le]
    refine ⟨DihedralGroup.r (-1), Equiv.ext fun z : ZMod 5 => ?_⟩
    change dihedralZModPerm 5 (DihedralGroup.r (-1)) z = z + 1
    simp [dihedralZModPerm_r]
  have hD5_le_F20 : s5D5 ≤ s5F20 := by
    rintro _ ⟨d, rfl⟩
    cases d with
    | r i =>
      refine ⟨(1, -i), Equiv.ext fun x : ZMod 5 => ?_⟩
      change agl1ZMod5Perm (1, -i) x = dihedralZModPerm 5 (DihedralGroup.r i) x
      simp; ring
    | sr i =>
      refine ⟨(-1, i), Equiv.ext fun x : ZMod 5 => ?_⟩
      change agl1ZMod5Perm (-1, i) x = dihedralZModPerm 5 (DihedralGroup.sr i) x
      simp; ring
  have hC5_le_A5 : s5C5 ≤ alternatingGroup (Fin 5) := by
    rw [s5C5, Subgroup.zpowers_le]
    exact hs5Shift_even
  have htr0 : SubgroupActsTransitively s5C5 := by
    intro x y
    rcases hs5Shift_all x y with rfl | h1 | h2 | h3 | h4
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · exact ⟨s5ShiftPerm, Subgroup.mem_zpowers _, h1⟩
    · exact ⟨s5ShiftPerm ^ 2, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2, h2⟩
    · exact ⟨s5ShiftPerm ^ 3, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3, h3⟩
    · exact ⟨s5ShiftPerm ^ 4, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 4, h4⟩
  have htrs : ∀ i : Fin 5, SubgroupActsTransitively (s5TransitiveModel i) := by
    intro i
    fin_cases i
    · exact htr0
    · exact fun x y => by
        obtain ⟨σ, hσ, hxy⟩ := htr0 x y
        exact ⟨σ, hC5_le_D5 hσ, hxy⟩
    · exact fun x y => by
        obtain ⟨σ, hσ, hxy⟩ := htr0 x y
        exact ⟨σ, hD5_le_F20 (hC5_le_D5 hσ), hxy⟩
    · exact fun x y => by
        obtain ⟨σ, hσ, hxy⟩ := htr0 x y
        exact ⟨σ, hC5_le_A5 hσ, hxy⟩
    · exact fun x y => ⟨Equiv.swap x y, Subgroup.mem_top _, Equiv.swap_apply_left x y⟩
  let toZ : Fin 5 → ZMod 5 := fun z => z
  have hs_zpow_apply : ∀ (m : ℤ) (z : Fin 5),
      toZ ((s5ShiftPerm ^ m) z) = toZ z + (m : ZMod 5) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      intro z
      change toZ z = toZ z + ((0 : ℤ) : ZMod 5)
      simp
    | succ n ih =>
      intro z
      have hmul : (s5ShiftPerm ^ ((n : ℤ) + 1)) z =
          (s5ShiftPerm ^ (n : ℤ)) (s5ShiftPerm z) := by
        rw [zpow_add_one]
        rfl
      rw [hmul, ih (s5ShiftPerm z)]
      have h1 : toZ (s5ShiftPerm z) = toZ z + 1 := rfl
      rw [h1]
      push_cast; ring
    | pred n ih =>
      intro z
      have hmul : (s5ShiftPerm ^ (-(n : ℤ) - 1)) z =
          (s5ShiftPerm ^ (-(n : ℤ))) (s5ShiftPerm⁻¹ z) := by
        rw [zpow_sub_one]
        rfl
      rw [hmul, ih (s5ShiftPerm⁻¹ z)]
      have hm1 : toZ (s5ShiftPerm⁻¹ z) = toZ z + -1 := rfl
      rw [hm1]
      push_cast; ring
  -- Normalizer of `s5C5` in `Σ₅` equals `s5F20` (order `20`, index `6`).
  have hnorm_C5 : Subgroup.normalizer (s5C5 : Set (Equiv.Perm (Fin 5))) = s5F20 := by
    apply le_antisymm
    · intro g hg
      have hs_mem : s5ShiftPerm ∈ s5C5 := Subgroup.mem_zpowers _
      have hconj_mem : g * s5ShiftPerm * g⁻¹ ∈ s5C5 := (hg s5ShiftPerm).mp hs_mem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem
      let gZ : Equiv.Perm (ZMod 5) := g
      let aZ : ZMod 5 := (k : ZMod 5)
      have hstep : ∀ x : ZMod 5, gZ (x + 1) = gZ x + aZ := by
        intro x
        have heval : toZ ((g * s5ShiftPerm * g⁻¹) (g x)) = toZ ((s5ShiftPerm ^ k) (g x)) :=
          congrArg toZ (congrFun (congrArg DFunLike.coe hk.symm) (g x))
        rw [hs_zpow_apply k (g x)] at heval
        have hlhs : toZ ((g * s5ShiftPerm * g⁻¹) (g x)) = gZ (x + 1) := by
          change gZ (s5ShiftPerm (gZ.symm (gZ x))) = gZ (x + 1)
          rw [gZ.symm_apply_apply]
          rfl
        exact hlhs.symm.trans heval
      have ha_ne0 : aZ ≠ 0 := by
        intro ha0
        have h01 := hstep 0
        rw [zero_add, ha0, add_zero] at h01
        exact zero_ne_one (gZ.injective h01.symm)
      let u_unit : (ZMod 5)ˣ := Units.mk0 aZ ha_ne0
      refine ⟨(u_unit, gZ 0), Equiv.ext fun x : ZMod 5 => ?_⟩
      change aZ * x + gZ 0 = gZ x
      have hnat : ∀ n : ℕ, gZ (n : ZMod 5) = aZ * (n : ZMod 5) + gZ 0 := by
        intro n
        induction n with
        | zero => simp
        | succ m ih =>
          push_cast
          rw [hstep, ih]
          ring
      have hx_nat : (x.val : ZMod 5) = x := ZMod.natCast_zmod_val x
      rw [← hx_nat, hnat x.val]
    · rintro g ⟨u, rfl⟩ h
      have hsub : ∀ v : (ZMod 5)ˣ × ZMod 5,
          agl1Fin5Perm v * s5ShiftPerm * (agl1Fin5Perm v)⁻¹ ∈ s5C5 := by
        intro v
        refine Subgroup.mem_zpowers_iff.mpr ⟨(v.1 : ZMod 5).val, Equiv.ext fun z : Fin 5 => ?_⟩
        have hlhs := hs_zpow_apply ((v.1 : ZMod 5).val : ℤ) z
        rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hlhs
        refine hlhs.trans ?_
        change toZ z + (v.1 : ZMod 5) = agl1ZMod5Perm v ((agl1ZMod5Perm v).symm (toZ z) + 1)
        simp only [agl1ZMod5Perm_apply, agl1ZMod5Perm_symm_apply]
        have hv : (v.1 : ZMod 5) * ((v.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) = 1 := Units.mul_inv v.1
        calc toZ z + (v.1 : ZMod 5)
            = ((v.1 : ZMod 5) * ((v.1⁻¹ : (ZMod 5)ˣ) : ZMod 5)) * (toZ z - v.2) +
                (v.1 : ZMod 5) + v.2 := by rw [hv]; ring
          _ = (v.1 : ZMod 5) * (((v.1⁻¹ : (ZMod 5)ˣ) : ZMod 5) * (toZ z - v.2) + 1) +
                v.2 := by ring
      have hmap_le : s5C5.map (MulAut.conj (agl1Fin5Perm u)).toMonoidHom ≤ s5C5 := by
        rw [s5C5, MonoidHom.map_zpowers, Subgroup.zpowers_le]
        exact hsub u
      have hmap_inv_le : s5C5.map (MulAut.conj (agl1Fin5Perm u)⁻¹).toMonoidHom ≤ s5C5 := by
        obtain ⟨u', hu'⟩ := s5F20.inv_mem ⟨u, rfl⟩
        change agl1Fin5Perm u' = (agl1Fin5Perm u)⁻¹ at hu'
        rw [← hu', s5C5, MonoidHom.map_zpowers, Subgroup.zpowers_le]
        exact hsub u'
      constructor
      · intro hh
        exact hmap_le ⟨h, hh, rfl⟩
      · intro hconj
        have hh : (agl1Fin5Perm u)⁻¹ * (agl1Fin5Perm u * h * (agl1Fin5Perm u)⁻¹) *
            ((agl1Fin5Perm u)⁻¹)⁻¹ ∈ s5C5 := hmap_inv_le ⟨_, hconj, rfl⟩
        have heq : (agl1Fin5Perm u)⁻¹ * (agl1Fin5Perm u * h * (agl1Fin5Perm u)⁻¹) *
            ((agl1Fin5Perm u)⁻¹)⁻¹ = h := by group
        rwa [heq] at hh
  -- Subgroups between `s5C5` and `s5F20` are `s5C5`, `s5D5`, `s5F20`.
  have hbetween_F20 : ∀ K : Subgroup (Equiv.Perm (Fin 5)),
      s5C5 ≤ K → K ≤ s5F20 → K = s5C5 ∨ K = s5D5 ∨ K = s5F20 := by
    intro K hCK hKF
    let linHom : s5F20 →* (ZMod 5)ˣ :=
      { toFun := fun g => (hf20_bij.surjective g).choose.1
        map_one' := by
          have h1 : f20Map (1, 0) = 1 :=
            Subtype.ext (Equiv.ext fun z : ZMod 5 => by change agl1ZMod5Perm (1, 0) z = z; simp)
          have heq := hf20_bij.injective ((hf20_bij.surjective 1).choose_spec.trans h1.symm)
          exact congrArg Prod.fst heq
        map_mul' := fun g₁ g₂ => by
          let u₁ := (hf20_bij.surjective g₁).choose
          let u₂ := (hf20_bij.surjective g₂).choose
          have hu₁ : f20Map u₁ = g₁ := (hf20_bij.surjective g₁).choose_spec
          have hu₂ : f20Map u₂ = g₂ := (hf20_bij.surjective g₂).choose_spec
          let u₁₂ : (ZMod 5)ˣ × ZMod 5 := (u₁.1 * u₂.1, (u₁.1 : ZMod 5) * u₂.2 + u₁.2)
          have hu₁₂ : f20Map u₁₂ = g₁ * g₂ := by
            apply Subtype.ext
            rw [← hu₁, ← hu₂]
            exact Equiv.ext fun z : ZMod 5 => by
              change agl1ZMod5Perm u₁₂ z = agl1ZMod5Perm u₁ (agl1ZMod5Perm u₂ z)
              simp only [agl1ZMod5Perm_apply, Units.val_mul, u₁₂]; ring
          have heq := hf20_bij.injective ((hf20_bij.surjective (g₁ * g₂)).choose_spec.trans hu₁₂.symm)
          exact congrArg Prod.fst heq }
    have htrans_mem : ∀ b : ZMod 5, f20Map (1, b) ∈ s5C5.subgroupOf s5F20 := by
      intro b
      change (f20Map (1, b)).1 ∈ s5C5
      refine Subgroup.mem_zpowers_iff.mpr ⟨b.val, Equiv.ext fun z : Fin 5 => ?_⟩
      have hlhs := hs_zpow_apply (b.val : ℤ) z
      rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hlhs
      refine hlhs.trans ?_
      change toZ z + b = agl1ZMod5Perm (1, b) (toZ z)
      simp
    let K' : Subgroup s5F20 := K.subgroupOf s5F20
    let U : Subgroup (ZMod 5)ˣ := K'.map linHom
    have hker_le_K' : linHom.ker ≤ K' := by
      intro g hg
      let u := (hf20_bij.surjective g).choose
      have hu : f20Map u = g := (hf20_bij.surjective g).choose_spec
      have hu1 : u.1 = 1 := hg
      have hg_eq : g = f20Map (1, u.2) := by
        rw [← hu]
        congr 1
        exact Prod.ext hu1 rfl
      rw [hg_eq]
      exact hCK (htrans_mem u.2)
    have hK'_eq_comap : K' = U.comap linHom := by
      apply le_antisymm
      · intro g hg
        exact ⟨g, hg, rfl⟩
      · rintro g ⟨k, hk, hlin_eq⟩
        have hdiff : k⁻¹ * g ∈ linHom.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hlin_eq, inv_mul_cancel]
        have hmem := K'.mul_mem hk (hker_le_K' hdiff)
        simpa using hmem
    have hu_vals : ∀ a : (ZMod 5)ˣ,
        (a : ZMod 5) = 1 ∨ (a : ZMod 5) = 2 ∨ (a : ZMod 5) = 3 ∨ (a : ZMod 5) = 4 :=
      fun a => hz_units5 (a : ZMod 5) a.isUnit
    -- Every subgroup `U ≤ (ZMod 5)ˣ` is `⊥`, `{1, -1}`, or `⊤`.
    have hU_cases : U = ⊥ ∨ (∀ a : (ZMod 5)ˣ, a ∈ U ↔ a = 1 ∨ a = -1) ∨ U = ⊤ := by
      classical
      let u2 : (ZMod 5)ˣ := Units.mk0 2 h2_ne0
      have hu2_3 : (3 : ZMod 5) = ((u2 ^ 3 : (ZMod 5)ˣ) : ZMod 5) := by
        simpa [u2] using h2_pow3
      have hu2_2 : (4 : ZMod 5) = ((u2 ^ 2 : (ZMod 5)ˣ) : ZMod 5) := by
        simpa [u2] using h2_pow2
      have hu2_9 : u2 = (u2 ^ 3) ^ 3 := Units.ext (by simpa [u2] using h2_pow9)
      by_cases h2 : u2 ∈ U
      · right; right
        rw [eq_top_iff]
        intro a _
        rcases hu_vals a with h1 | h2' | h3' | h4'
        · have heq : a = 1 := Units.ext h1; rw [heq]; exact U.one_mem
        · have heq : a = u2 := Units.ext h2'; rw [heq]; exact h2
        · have heq : a = u2 ^ 3 := Units.ext (h3'.trans hu2_3)
          rw [heq]; exact U.pow_mem h2 3
        · have heq : a = u2 ^ 2 := Units.ext (h4'.trans hu2_2)
          rw [heq]; exact U.pow_mem h2 2
      · by_cases h3 : u2 ^ 3 ∈ U
        · exfalso
          exact h2 (hu2_9 ▸ U.pow_mem h3 3)
        · by_cases hm1 : (-1 : (ZMod 5)ˣ) ∈ U
          · right; left
            intro a
            refine ⟨fun ha => ?_, ?_⟩
            · rcases hu_vals a with h1 | h2' | h3' | h4'
              · exact Or.inl (Units.ext h1)
              · exfalso; exact h2 ((Units.ext h2' : a = u2) ▸ ha)
              · exfalso; exact h3 ((Units.ext (h3'.trans hu2_3) : a = u2 ^ 3) ▸ ha)
              · exact Or.inr (Units.ext (h4'.trans h4_eq_m1))
            · rintro (rfl | rfl)
              · exact U.one_mem
              · exact hm1
          · left
            rw [eq_bot_iff]
            intro a ha
            rcases hu_vals a with h1 | h2' | h3' | h4'
            · exact Units.ext h1
            · exfalso; exact h2 ((Units.ext h2' : a = u2) ▸ ha)
            · exfalso; exact h3 ((Units.ext (h3'.trans hu2_3) : a = u2 ^ 3) ▸ ha)
            · exfalso; exact hm1 ((Units.ext (h4'.trans h4_eq_m1) : a = -1) ▸ ha)
    have hsub_eq : ∀ M : Subgroup (Equiv.Perm (Fin 5)),
        M ≤ s5F20 → K' = M.subgroupOf s5F20 → K = M := by
      intro M hMF hKM
      ext x
      constructor
      · intro hx
        have hxF : x ∈ s5F20 := hKF hx
        have hxK' : (⟨x, hxF⟩ : s5F20) ∈ K' := hx
        rw [hKM] at hxK'
        exact hxK'
      · intro hx
        have hxF : x ∈ s5F20 := hMF hx
        have hxM' : (⟨x, hxF⟩ : s5F20) ∈ M.subgroupOf s5F20 := hx
        rw [← hKM] at hxM'
        exact hxM'
    rcases hU_cases with hU_bot | hU_pm1 | hU_top
    · left
      refine hsub_eq s5C5 (hC5_le_D5.trans hD5_le_F20) ?_
      apply le_antisymm
      · rw [hK'_eq_comap, hU_bot]
        intro g hg
        let u := (hf20_bij.surjective g).choose
        have hu : f20Map u = g := (hf20_bij.surjective g).choose_spec
        have hu1 : u.1 = 1 := hg
        have hg_eq : g = f20Map (1, u.2) := by
          rw [← hu]; congr 1; exact Prod.ext hu1 rfl
        rw [hg_eq]
        exact htrans_mem u.2
      · intro g hg
        exact hCK hg
    · right; left
      refine hsub_eq s5D5 hD5_le_F20 ?_
      ext g
      rw [hK'_eq_comap, Subgroup.mem_comap, hU_pm1]
      let u := (hf20_bij.surjective g).choose
      have hu : f20Map u = g := (hf20_bij.surjective g).choose_spec
      change (u.1 = 1 ∨ u.1 = -1) ↔ g.1 ∈ s5D5
      constructor
      · rintro (hu1 | hum1)
        · have hg_eq : g = f20Map (1, u.2) := by
            rw [← hu]; congr 1; exact Prod.ext hu1 rfl
          rw [hg_eq]
          exact hC5_le_D5 (htrans_mem u.2)
        · refine ⟨DihedralGroup.sr u.2, ?_⟩
          have hgval : g.1 = agl1ZMod5Perm u := congrArg Subtype.val hu.symm
          rw [hgval]
          exact Equiv.ext fun z : ZMod 5 => by
            change dihedralZModPerm 5 (DihedralGroup.sr u.2) z = agl1ZMod5Perm u z
            simp [hum1]; ring
      · rintro ⟨d, hd⟩
        cases d with
        | r i =>
          have h1 : f20Map (1, -i) = g :=
            Subtype.ext ((Equiv.ext fun z : ZMod 5 => by
              change agl1ZMod5Perm (1, -i) z = dihedralZModPerm 5 (DihedralGroup.r i) z
              simp; ring).trans hd)
          have heq := hf20_bij.injective (hu.trans h1.symm)
          exact Or.inl (congrArg Prod.fst heq)
        | sr i =>
          have h1 : f20Map (-1, i) = g :=
            Subtype.ext ((Equiv.ext fun z : ZMod 5 => by
              change agl1ZMod5Perm (-1, i) z = dihedralZModPerm 5 (DihedralGroup.sr i) z
              simp; ring).trans hd)
          have heq := hf20_bij.injective (hu.trans h1.symm)
          exact Or.inr (congrArg Prod.fst heq)
    · right; right
      refine hsub_eq s5F20 le_rfl ?_
      rw [hK'_eq_comap, hU_top]
      ext g
      simp
  -- Helper showing `¬ 5 ∣ P.index` whenever `Nat.card G ∣ 120` and `Nat.card P = 5`.
  have hndvd5_of_card5 : ∀ {G : Type} [Group G], Nat.card G ∣ 120 →
      ∀ P : Subgroup G, Nat.card P = 5 → ¬ 5 ∣ P.index := by
    rintro G _ hdvd P hPc ⟨m, hm⟩
    have hmul := P.card_mul_index
    rw [hPc, hm] at hmul
    have hd25 : 25 ∣ 120 := dvd_trans ⟨m, by linarith⟩ hdvd
    norm_num at hd25
  -- Helper showing any `Q : Sylow 5 G` has `Nat.card Q.toSubgroup = 5` when `5 ∣ Nat.card G` and `Nat.card G ∣ 120`.
  have sylow5_card : ∀ {G : Type} [Group G] [Finite G],
      5 ∣ Nat.card G → Nat.card G ∣ 120 → ∀ Q : Sylow 5 G, Nat.card Q.toSubgroup = 5 := by
    intro G _ _ h5 h120 Q
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hnot5 : ¬ 5 ∣ Q.toSubgroup.index := Q.not_dvd_index
    have hk_ne0 : k ≠ 0 := by
      rintro rfl
      have hm := Q.toSubgroup.card_mul_index
      rw [hk, pow_zero, one_mul] at hm
      exact hnot5 (hm ▸ h5)
    have hd_pow : 5 ^ k ∣ 120 :=
      dvd_trans (hk ▸ Q.toSubgroup.card_subgroup_dvd_card) h120
    have hle_pow : 5 ^ k ≤ 120 := Nat.le_of_dvd (by decide) hd_pow
    have hk_lt3 : k < 3 := by
      by_contra hge
      have h125 : 125 ≤ 5 ^ k :=
        calc 125 = 5 ^ 3 := by decide
          _ ≤ 5 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · simpa using hk
    · exfalso; norm_num at hd_pow
  have hdvd_S5 : Nat.card (Equiv.Perm (Fin 5)) ∣ 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hiff : ∀ H : Subgroup (Equiv.Perm (Fin 5)),
      SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) H := by
    intro H
    refine ⟨fun htr => ?_, ?_⟩
    · have hdvd5 : 5 ∣ Nat.card H := by
        simpa [Fintype.card_fin] using (card_dvd_and_fixedPointFree_of_transitive htr).1
      have hdvd120 : Nat.card H ∣ 120 := dvd_trans H.card_subgroup_dvd_card hdvd_S5
      obtain ⟨P₀⟩ : Nonempty (Sylow 5 H) := Sylow.nonempty
      have hP₀_card : Nat.card P₀.toSubgroup = 5 := sylow5_card hdvd5 hdvd120 P₀
      let P₀_map : Subgroup (Equiv.Perm (Fin 5)) := P₀.toSubgroup.map H.subtype
      have hP₀_map_card : Nat.card P₀_map = 5 := by
        have heq := Nat.card_congr (P₀.toSubgroup.equivMapOfInjective H.subtype H.subtype_injective).toEquiv
        exact heq.symm.trans hP₀_card
      let S_C5 : Sylow 5 (Equiv.Perm (Fin 5)) :=
        mkSylowOfNotDvdIndex s5C5 (hc0.trans (pow_one 5).symm)
          (hndvd5_of_card5 hdvd_S5 s5C5 hc0)
      let S_P0 : Sylow 5 (Equiv.Perm (Fin 5)) :=
        mkSylowOfNotDvdIndex P₀_map (hP₀_map_card.trans (pow_one 5).symm)
          (hndvd5_of_card5 hdvd_S5 P₀_map hP₀_map_card)
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5)) S_P0 S_C5
      let H' : Subgroup (Equiv.Perm (Fin 5)) := H.map (MulAut.conj g).toMonoidHom
      have hHH' : IsConjugateSubgroup H' H := isConjugateSubgroup_symm ⟨g, rfl⟩
      have hC5_le_H' : s5C5 ≤ H' := by
        have hg_sub := hg
        rw [Sylow.ext_iff, Sylow.smul_def, Sylow.pointwise_smul_def,
          Subgroup.pointwise_smul_def] at hg_sub
        change P₀_map.map (MulAut.conj g).toMonoidHom = s5C5 at hg_sub
        rw [← hg_sub]
        rintro _ ⟨x, ⟨y, _, rfl⟩, rfl⟩
        exact ⟨y.1, y.2, rfl⟩
      have hdvd5_H' : 5 ∣ Nat.card H' := isConjugateSubgroup_natCard_eq ⟨g, rfl⟩ ▸ hdvd5
      have hdvd120_H' : Nat.card H' ∣ 120 := isConjugateSubgroup_natCard_eq ⟨g, rfl⟩ ▸ hdvd120
      let embSylow : Sylow 5 H' → Sylow 5 (Equiv.Perm (Fin 5)) := fun Q =>
        let hmapc : Nat.card (Q.toSubgroup.map H'.subtype) = 5 :=
          (Nat.card_congr (Q.toSubgroup.equivMapOfInjective H'.subtype H'.subtype_injective).toEquiv).symm.trans
            (sylow5_card hdvd5_H' hdvd120_H' Q)
        mkSylowOfNotDvdIndex (Q.toSubgroup.map H'.subtype) (hmapc.trans (pow_one 5).symm)
          (hndvd5_of_card5 hdvd_S5 _ hmapc)
      have hemb_inj : Function.Injective embSylow := by
        intro Q₁ Q₂ hQ
        have hsub : Q₁.toSubgroup.map H'.subtype = Q₂.toSubgroup.map H'.subtype :=
          congrArg Sylow.toSubgroup hQ
        apply Sylow.ext
        ext x
        constructor
        · intro hx
          have hm : (x : Equiv.Perm (Fin 5)) ∈ Q₂.toSubgroup.map H'.subtype :=
            hsub ▸ ⟨x, hx, rfl⟩
          obtain ⟨y, hy, hyx⟩ := hm
          exact (H'.subtype_injective hyx) ▸ hy
        · intro hx
          have hm : (x : Equiv.Perm (Fin 5)) ∈ Q₁.toSubgroup.map H'.subtype :=
            hsub.symm ▸ ⟨x, hx, rfl⟩
          obtain ⟨y, hy, hyx⟩ := hm
          exact (H'.subtype_injective hyx) ▸ hy
      have hn5_S5 : Nat.card (Sylow 5 (Equiv.Perm (Fin 5))) = 6 := by
        rw [S_C5.card_eq_index_normalizer]
        change (Subgroup.normalizer (s5C5 : Set (Equiv.Perm (Fin 5)))).index = 6
        rw [hnorm_C5]
        have hm := s5F20.card_mul_index
        have hf5 : (5 : ℕ).factorial = 120 := rfl
        rw [Nat.card_perm, Nat.card_fin, hf5, hc2] at hm
        omega
      let _ : Finite (Sylow 5 (Equiv.Perm (Fin 5))) :=
        Nat.finite_of_card_ne_zero (by rw [hn5_S5]; decide)
      let _ : Finite (Sylow 5 H') := Finite.of_injective embSylow hemb_inj
      have hn5_le : Nat.card (Sylow 5 H') ≤ 6 := by
        rw [← hn5_S5]
        exact Nat.card_le_card_of_injective embSylow hemb_inj
      have hn5_pos : 0 < Nat.card (Sylow 5 H') := Nat.card_pos
      have hn5_mod : Nat.card (Sylow 5 H') % 5 = 1 := card_sylow_modEq_one 5 H'
      have hn5_cases : Nat.card (Sylow 5 H') = 1 ∨ Nat.card (Sylow 5 H') = 6 := by omega
      rcases hn5_cases with hn1 | hn6
      · -- `n_5(H') = 1`: `s5C5` is the unique Sylow `5`-subgroup of `H'`, so `H' ≤ N(s5C5) = s5F20`.
        have hsub_syl : Subsingleton (Sylow 5 H') := (Nat.card_eq_one_iff_unique.mp hn1).1
        have hc_sub : Nat.card (s5C5.subgroupOf H') = 5 :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC5_le_H').toEquiv).trans hc0
        let P_C5' : Sylow 5 H' :=
          mkSylowOfNotDvdIndex (s5C5.subgroupOf H') (hc_sub.trans (pow_one 5).symm)
            (hndvd5_of_card5 hdvd120_H' _ hc_sub)
        have hconj_sub : ∀ k ∈ H', ∀ y ∈ s5C5, k * y * k⁻¹ ∈ s5C5 := by
          intro k hk y hy
          have hk_smul : (⟨k, hk⟩ : H') • P_C5' = P_C5' := @Subsingleton.elim _ hsub_syl _ _
          rw [Sylow.ext_iff, Sylow.smul_def, Sylow.pointwise_smul_def,
            Subgroup.pointwise_smul_def] at hk_smul
          change (s5C5.subgroupOf H').map (MulAut.conj ⟨k, hk⟩).toMonoidHom =
              s5C5.subgroupOf H' at hk_smul
          have hmem : (⟨k * y * k⁻¹,
              H'.mul_mem (H'.mul_mem hk (hC5_le_H' hy)) (H'.inv_mem hk)⟩ : H') ∈
              (s5C5.subgroupOf H').map (MulAut.conj ⟨k, hk⟩).toMonoidHom :=
            ⟨⟨y, hC5_le_H' hy⟩, hy, rfl⟩
          rw [hk_smul] at hmem
          exact hmem
        have hH'_le_norm : H' ≤ Subgroup.normalizer (s5C5 : Set (Equiv.Perm (Fin 5))) := by
          intro k hk x
          refine ⟨fun hx => hconj_sub k hk x hx, fun hx => ?_⟩
          have hinv := hconj_sub k⁻¹ (H'.inv_mem hk) (k * x * k⁻¹) hx
          simpa [mul_assoc] using hinv
        rw [hnorm_C5] at hH'_le_norm
        rcases hbetween_F20 H' hC5_le_H' hH'_le_norm with heq | heq | heq
        · refine ⟨0, ?_⟩; dsimp [s5TransitiveModel]; rwa [← heq]
        · refine ⟨1, ?_⟩; dsimp [s5TransitiveModel]; rwa [← heq]
        · refine ⟨2, ?_⟩; dsimp [s5TransitiveModel]; rwa [← heq]
      · -- `n_5(H') = 6`: `embSylow` is bijective, so every `5`-cycle lies in `H'`, forcing `A₅ ≤ H'`.
        let _ : Fintype (Sylow 5 H') := Fintype.ofFinite _
        let _ : Fintype (Sylow 5 (Equiv.Perm (Fin 5))) := Fintype.ofFinite _
        have hemb_surj : Function.Surjective embSylow := by
          refine ((Fintype.bijective_iff_injective_and_card embSylow).mpr ⟨hemb_inj, ?_⟩).2
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hn6, hn5_S5]
        have hall_conj_mem : ∀ u : Equiv.Perm (Fin 5), u * s5ShiftPerm * u⁻¹ ∈ H' := by
          intro u
          obtain ⟨Q, hQ⟩ := hemb_surj (u • S_C5)
          rw [Sylow.ext_iff, Sylow.smul_def, Sylow.pointwise_smul_def,
            Subgroup.pointwise_smul_def] at hQ
          change Q.toSubgroup.map H'.subtype =
              s5C5.map (MulAut.conj u).toMonoidHom at hQ
          have hmem : u * s5ShiftPerm * u⁻¹ ∈ s5C5.map (MulAut.conj u).toMonoidHom :=
            ⟨s5ShiftPerm, Subgroup.mem_zpowers _, rfl⟩
          rw [← hQ] at hmem
          obtain ⟨q, _, hq⟩ := hmem
          exact hq ▸ q.2
        let genSet : Set (alternatingGroup (Fin 5)) :=
          {a | ∃ u : Equiv.Perm (Fin 5), u * s5ShiftPerm * u⁻¹ = a.1}
        let N : Subgroup (alternatingGroup (Fin 5)) := Subgroup.closure genSet
        have hN_norm : N.Normal := by
          refine ⟨fun n hn b => ?_⟩
          refine Subgroup.closure_induction
            (fun a ha => ?_)
            (by simp)
            (fun x y _ _ hx hy => by
              have heq : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
              rw [heq]; exact N.mul_mem hx hy)
            (fun x _ hx => by
              have heq : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
              rw [heq]; exact N.inv_mem hx) hn
          obtain ⟨u, hu⟩ := ha
          refine Subgroup.subset_closure ⟨b.1 * u, ?_⟩
          change (b.1 * u) * s5ShiftPerm * (b.1 * u)⁻¹ = b.1 * a.1 * b.1⁻¹
          rw [← hu]
          group
        have hN_ne_bot : N ≠ ⊥ := by
          intro hbot
          let sA : alternatingGroup (Fin 5) := ⟨s5ShiftPerm, hC5_le_A5 (Subgroup.mem_zpowers _)⟩
          have hsA_mem : sA ∈ N := Subgroup.subset_closure ⟨1, by simp [sA]⟩
          rw [hbot, Subgroup.mem_bot] at hsA_mem
          have hs_eq1 : s5ShiftPerm = 1 := congrArg Subtype.val hsA_mem
          exact hs5Shift_ne1 hs_eq1
        have hN_top : N = ⊤ :=
          (IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN_norm).resolve_left hN_ne_bot
        have hA5_le_H' : alternatingGroup (Fin 5) ≤ H' := by
          have hN_le : N ≤ H'.subgroupOf (alternatingGroup (Fin 5)) := by
            rw [Subgroup.closure_le]
            rintro a ⟨u, hu⟩
            change a.1 ∈ H'
            rw [← hu]
            exact hall_conj_mem u
          intro x hx
          have hmem_top : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ N := hN_top.symm ▸ Subgroup.mem_top _
          exact hN_le hmem_top
        have hidx_dvd : H'.index ∣ (alternatingGroup (Fin 5)).index :=
          Subgroup.index_dvd_of_le hA5_le_H'
        rw [alternatingGroup.index_eq_two] at hidx_dvd
        have hidx_pos : 0 < H'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have hidx_le : H'.index ≤ 2 := Nat.le_of_dvd (by decide) hidx_dvd
        interval_cases hidx_val : H'.index
        · refine ⟨4, ?_⟩
          have htop : H' = ⊤ := Subgroup.index_eq_one.mp hidx_val
          dsimp [s5TransitiveModel]
          rwa [← htop]
        · refine ⟨3, ?_⟩
          have heqA5 : H' = alternatingGroup (Fin 5) :=
            Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx_val
          dsimp [s5TransitiveModel]
          rwa [← heqA5]
    · rintro ⟨i, hconj⟩
      exact (isConjugateSubgroup_actsTransitively_iff hconj).mp (htrs i)
  refine ⟨hcards, htrs, hiff, fun H htr => ?_⟩
  obtain ⟨i, hi⟩ := (hiff H).mp htr
  refine ⟨i, hi, fun j hj => ?_⟩
  have hci : (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i = Nat.card H :=
    (hcards i).symm.trans (isConjugateSubgroup_natCard_eq hi)
  have hcj : (![5, 10, 20, 60, 120] : Fin 5 → ℕ) j = Nat.card H :=
    (hcards j).symm.trans (isConjugateSubgroup_natCard_eq hj)
  have hcard_ij : (![5, 10, 20, 60, 120] : Fin 5 → ℕ) j = (![5, 10, 20, 60, 120] : Fin 5 → ℕ) i :=
    hcj.trans hci.symm
  fin_cases i <;> fin_cases j <;> dsimp at hcard_ij ⊢
  all_goals (exfalso; norm_num at hcard_ij)

/-- **Exercise 11.5** (§11.2, printed p. 95 / PDF p. 103; see `QUEUE.md` on `"Describe..."` prompt):
*"Describe the transitive subgroups of `Σ₃`, `Σ₄` and `Σ₅`."*

Bundles the complete conjugacy-class classifications for `Σ₃` (`A₃, Σ₃`), `Σ₄` (`V₄, C₄, D₄, A₄, Σ₄`),
and `Σ₅` (`C₅, D₅, F₂₀, A₅, Σ₅`). -/
theorem exercise_11_5 :
    ((∀ H : Subgroup (Equiv.Perm (Fin 3)),
        SubgroupActsTransitively H ↔ H = alternatingGroup (Fin 3) ∨ H = ⊤) ∧
      ∀ H : Subgroup (Equiv.Perm (Fin 3)),
        SubgroupActsTransitively H → ∃! i : Fin 2, IsConjugateSubgroup (s3TransitiveModel i) H) ∧
    ((∀ H : Subgroup (Equiv.Perm (Fin 4)),
        SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s4TransitiveModel i) H) ∧
      ∀ H : Subgroup (Equiv.Perm (Fin 4)),
        SubgroupActsTransitively H → ∃! i : Fin 5, IsConjugateSubgroup (s4TransitiveModel i) H) ∧
    ((∀ H : Subgroup (Equiv.Perm (Fin 5)),
        SubgroupActsTransitively H ↔ ∃ i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) H) ∧
      ∀ H : Subgroup (Equiv.Perm (Fin 5)),
        SubgroupActsTransitively H → ∃! i : Fin 5, IsConjugateSubgroup (s5TransitiveModel i) H) :=
  ⟨⟨exercise_11_5_s3.2.2.1, exercise_11_5_s3.2.2.2⟩,
   ⟨exercise_11_5_s4.2.2.1, exercise_11_5_s4.2.2.2⟩,
   ⟨exercise_11_5_s5.2.2.1, exercise_11_5_s5.2.2.2⟩⟩

/-! #### Shared Helpers for Exercises 11.6 & 11.7 -/

/-- Any finite group `G` of cardinality `n` possessing an element `g` of order `n` is isomorphic
to `Multiplicative (ZMod n)` (`C_n`). -/
theorem mulEquivMultiplicativeZModOfOrderOfEqNatCard {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (g : G) (hord : orderOf g = n) (hcard : Nat.card G = n) :
    Nonempty (G ≃* Multiplicative (ZMod n)) := by
  classical
  have hn_pos : 0 < n := NeZero.pos n
  let _ : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne n)
  let _ : Fintype G := Fintype.ofFinite G
  have hgn : g ^ n = 1 := hord ▸ pow_orderOf_eq_one g
  let φ : Multiplicative (ZMod n) →* G :=
    { toFun := fun x => g ^ (Multiplicative.toAdd x).val
      map_one' := by
        change g ^ (0 : ZMod n).val = 1
        rw [ZMod.val_zero, pow_zero]
      map_mul' := fun x y => by
        let a : ZMod n := Multiplicative.toAdd x
        let b : ZMod n := Multiplicative.toAdd y
        change g ^ (a + b).val = g ^ a.val * g ^ b.val
        rw [ZMod.val_add, ← pow_add]
        have hdiv : a.val + b.val = n * ((a.val + b.val) / n) + (a.val + b.val) % n :=
          (Nat.div_add_mod (a.val + b.val) n).symm
        conv_rhs => rw [hdiv, pow_add, pow_mul, hgn, one_pow, one_mul] }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    let a : ZMod n := Multiplicative.toAdd x
    let b : ZMod n := Multiplicative.toAdd y
    have ha : a.val < n := ZMod.val_lt a
    have hb : b.val < n := ZMod.val_lt b
    have hpow : g ^ a.val = g ^ b.val := hxy
    have hval_eq : a.val = b.val := by
      rcases le_total a.val b.val with hle | hle
      · by_contra hne
        have hlt_sub : b.val - a.val < n := by omega
        have hpos_sub : 0 < b.val - a.val := by omega
        have hpow_sub : g ^ (b.val - a.val) = 1 := by
          have heq : g ^ a.val * g ^ (b.val - a.val) = g ^ a.val * 1 := by
            rw [← pow_add, Nat.add_sub_of_le hle, ← hpow, mul_one]
          exact mul_left_cancel heq
        have hord_le : orderOf g ≤ b.val - a.val := orderOf_le_of_pow_eq_one hpos_sub hpow_sub
        omega
      · by_contra hne
        have hlt_sub : a.val - b.val < n := by omega
        have hpos_sub : 0 < a.val - b.val := by omega
        have hpow_sub : g ^ (a.val - b.val) = 1 := by
          have heq : g ^ b.val * g ^ (a.val - b.val) = g ^ b.val * 1 := by
            rw [← pow_add, Nat.add_sub_of_le hle, hpow, mul_one]
          exact mul_left_cancel heq
        have hord_le : orderOf g ≤ a.val - b.val := orderOf_le_of_pow_eq_one hpos_sub hpow_sub
        omega
    exact Multiplicative.toAdd.injective (ZMod.val_injective n hval_eq)
  have hφ_bij : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, ?_⟩
    rw [Fintype.card_multiplicative, ZMod.card, ← Nat.card_eq_fintype_card, hcard]
  exact ⟨(MulEquiv.ofBijective φ hφ_bij).symm⟩

/-- Every group of cardinality `2` is isomorphic to `Multiplicative (ZMod 2)` (`C₂`). -/
theorem mulEquivZMod2OfNatCardTwo {G : Type*} [Group G] (hcard : Nat.card G = 2) :
    Nonempty (G ≃* Multiplicative (ZMod 2)) := by
  classical
  let _ : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let _ : Fintype G := Fintype.ofFinite G
  have hfcard : Fintype.card G = 2 := Nat.card_eq_fintype_card.symm.trans hcard
  have _ : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg1⟩ := exists_ne (1 : G)
  have hdvd : orderOf g ∣ 2 := by
    have hd := orderOf_dvd_natCard g
    rwa [hcard] at hd
  have hpos : 0 < orderOf g := orderOf_pos g
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hord2 : orderOf g = 2 := by
    interval_cases ho : orderOf g
    · exfalso; exact hg1 (orderOf_eq_one_iff.mp ho)
    · rfl
  exact mulEquivMultiplicativeZModOfOrderOfEqNatCard g hord2 hcard

/-- `X ^ 4 - C c` is separable over any field `K` in which `4 ≠ 0` and `c ≠ 0`. -/
theorem separable_X_pow_four_sub_C {K : Type*} [Field K] {c : K}
    (h4 : (4 : K) ≠ 0) (hc : c ≠ 0) :
    (Polynomial.X ^ 4 - Polynomial.C c : K[X]).Separable := by
  refine ⟨-Polynomial.C c⁻¹, Polynomial.C (c⁻¹ * (4 : K)⁻¹) * Polynomial.X, ?_⟩
  have hderiv : Polynomial.derivative (Polynomial.X ^ 4 - Polynomial.C c : K[X]) =
      Polynomial.C (4 : K) * Polynomial.X ^ 3 := by
    simp [map_ofNat]
    norm_num
  rw [hderiv]
  calc -Polynomial.C c⁻¹ * (Polynomial.X ^ 4 - Polynomial.C c) +
        Polynomial.C (c⁻¹ * (4 : K)⁻¹) * Polynomial.X * (Polynomial.C (4 : K) * Polynomial.X ^ 3)
      = Polynomial.C (c⁻¹ * c) +
          Polynomial.C (c⁻¹ * ((4 : K)⁻¹ * (4 : K)) - c⁻¹) * Polynomial.X ^ 4 := by
        simp only [Polynomial.C_mul, Polynomial.C_sub]
        ring
    _ = 1 := by
        rw [inv_mul_cancel₀ hc, inv_mul_cancel₀ h4, mul_one, sub_self, map_zero, zero_mul,
          add_zero, map_one]

/-- In any splitting field `L` of a separable polynomial `f ∈ K[X]`, `garlingRootSet K L f` has
cardinality `f.natDegree`. -/
theorem ncard_garlingRootSet_eq_natDegree_of_separable
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hsep : f.Separable) (hsf : IsGarlingSplittingFieldExtension K L f) :
    (garlingRootSet K L f).ncard = f.natDegree := by
  classical
  have hsplit_inst : Polynomial.IsSplittingField K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mp hsf
  let fL : L[X] := f.map (algebraMap K L)
  have hfL_sep : fL.Separable := hsep.map
  have hfL_ne0 : fL ≠ 0 := hfL_sep.ne_zero
  have hfL_splits : fL.Splits := hsplit_inst.splits
  have hset_eq : garlingRootSet K L f = (fL.roots.toFinset : Set L) := by
    ext α
    change Polynomial.aeval α f = 0 ↔ α ∈ (fL.roots.toFinset : Set L)
    simp only [Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots hfL_ne0, Polynomial.IsRoot.def, fL, Polynomial.eval_map_algebraMap]
  rw [hset_eq, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hfL_sep),
    ← hfL_splits.natDegree_eq_card_roots, Polynomial.natDegree_map]

/-- If a separable quartic `f ∈ K[X]` (`f.natDegree = 4`) over a perfect field `K` has a splitting
field `E` of degree `8`, then **every** splitting field `L` of `f` over `K` has `[L : K] = 8` and
`GarlingPolyGaloisGroup K L f ≃* DihedralGroup 4` (`D₄`). -/
theorem quartic_galoisGroup_d4_of_splittingField_finrank_eight
    {K : Type*} {E : Type*} [Field K] [PerfectField K] [Field E] [Algebra K E]
    {f : K[X]} (hsep : f.Separable) (hdeg : f.natDegree = 4)
    (hsfE : IsGarlingSplittingFieldExtension K E f) (hfinE : Module.finrank K E = 8)
    (L : Type*) [Field L] [Algebra K L] (hsfL : IsGarlingSplittingFieldExtension K L f) :
    Module.finrank K L = 8 ∧
    Nat.card (GarlingPolyGaloisGroup K L f) = 8 ∧
    Nonempty (GarlingPolyGaloisGroup K L f ≃* DihedralGroup 4) := by
  obtain ⟨eLE⟩ := splitting_field_unique_up_to_algEquiv hsfL hsfE
  have hfinL : Module.finrank K L = 8 := eLE.toLinearEquiv.finrank_eq.trans hfinE
  have hperf : IsGarlingPerfectField K :=
    (isGarlingPerfectField_iff_perfectField K).mpr inferInstance
  have hcardG : Nat.card (GarlingPolyGaloisGroup K L f) = 8 :=
    (theorem_11_5_perfect hperf hsfL).2.1.trans hfinL
  have hncard_roots : (garlingRootSet K L f).ncard = 4 :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsfL).trans hdeg
  have hfin_roots : (garlingRootSet K L f).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncard_roots]; decide)
  let _ : Fintype (garlingRootSet K L f) := hfin_roots.fintype
  have hfcard_roots : Fintype.card (garlingRootSet K L f) = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hncard_roots]
  let eRoots : garlingRootSet K L f ≃ Fin 4 := Fintype.equivFinOfCardEq hfcard_roots
  let ψ : GarlingPolyGaloisGroup K L f →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom eRoots).toMonoidHom.comp (garlingRootPermHom K L f)
  have hψ_inj : Function.Injective ψ :=
    (Equiv.permCongrHom eRoots).injective.comp (theorem_11_6 hsfL)
  let eRange : GarlingPolyGaloisGroup K L f ≃* ψ.range :=
    MulEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b hab => hψ_inj (congrArg Subtype.val hab), ψ.rangeRestrict_surjective⟩
  have hrange_card : Nat.card ψ.range = 8 :=
    (Nat.card_congr eRange.symm.toEquiv).trans hcardG
  obtain ⟨hisoD4⟩ := (s4_subgroup_card_eight_conj_d4 ψ.range hrange_card).2
  exact ⟨hfinL, hcardG, ⟨eRange.trans hisoD4⟩⟩

/-- If `f ∈ K[X]` (`f ≠ 0`) over a perfect field `K` splits into `4` linear factors over
`AdjoinRoot q` where `q ∈ K[X]` is monic of degree `2` with no roots in `K`, and `AdjoinRoot.root q`
is one of the roots of `f`, then `AdjoinRoot q` is a splitting field of `f` of degree `2`, and
**every** splitting field `L` of `f` over `K` has `[L : K] = 2` and
`GarlingPolyGaloisGroup K L f ≃* Multiplicative (ZMod 2)` (`C₂`). -/
theorem quartic_galoisGroup_c2_of_quad_adjoinRoot
    {K : Type u} [Field K] [PerfectField K] {f q : K[X]} (hf0 : f ≠ 0)
    (hq_mon : q.Monic) (hq_deg : q.natDegree = 2) (hq_noroots : ∀ z : K, q.eval z ≠ 0)
    (β : Fin 4 → AdjoinRoot q)
    (hfac : f.map (algebraMap K (AdjoinRoot q)) =
      ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β i)))
    (hi₀ : ∃ i₀ : Fin 4, β i₀ = AdjoinRoot.root q) :
    Irreducible q ∧
    (∃ (E : Type u) (_ : Field E) (_ : Algebra K E),
      IsGarlingSplittingFieldExtension K E f ∧ Module.finrank K E = 2) ∧
    ∀ (L : Type v) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
      Module.finrank K L = 2 ∧
      Nat.card (GarlingPolyGaloisGroup K L f) = 2 ∧
      Nonempty (GarlingPolyGaloisGroup K L f ≃* Multiplicative (ZMod 2)) := by
  have hq_irr : Irreducible q := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hau, hbu⟩
      have ha0 : a ≠ 0 := fun h0 => hq_mon.ne_zero (by rw [hab, h0, zero_mul])
      have hb0 : b ≠ 0 := fun h0 => hq_mon.ne_zero (by rw [hab, h0, mul_zero])
      have had : 1 ≤ a.natDegree := Nat.pos_of_ne_zero fun hd0 =>
        hau (Polynomial.isUnit_iff.mpr ⟨a.coeff 0,
          isUnit_iff_ne_zero.mpr fun hc0 => ha0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by simp [hc0])),
          (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩)
      have hbd : 1 ≤ b.natDegree := Nat.pos_of_ne_zero fun hd0 =>
        hbu (Polynomial.isUnit_iff.mpr ⟨b.coeff 0,
          isUnit_iff_ne_zero.mpr fun hc0 => hb0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by simp [hc0])),
          (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩)
      have hsum : a.natDegree + b.natDegree = 2 := by
        rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hq_deg]
      have ha1 : a.natDegree = 1 := by omega
      obtain ⟨z, hz⟩ := Polynomial.exists_root_of_degree_eq_one
        ((Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr ha1)
      have hqz : q.eval z = 0 := by rw [hab, Polynomial.eval_mul, hz.eq_zero, zero_mul]
      exact hq_noroots z hqz
  have _ : Fact (Irreducible q) := ⟨hq_irr⟩
  let E : Type u := AdjoinRoot q
  have hfinE : Module.finrank K E = 2 :=
    (PowerBasis.finrank (AdjoinRoot.powerBasis hq_mon.ne_zero)).trans hq_deg
  have hsfE : IsGarlingSplittingFieldExtension K E f := by
    rw [isGarlingSplittingFieldExtension_iff]
    refine ⟨?_, ?_⟩
    · rw [hfac]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (β i)
    · obtain ⟨i₀, hi₀_eq⟩ := hi₀
      have hroot_mem : AdjoinRoot.root q ∈ f.rootSet E := by
        rw [Polynomial.mem_rootSet_of_ne hf0, Polynomial.aeval_def, ← Polynomial.eval_map, hfac,
          Polynomial.eval_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        rw [hi₀_eq, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
      rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top (f := q)]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hroot_mem)
  refine ⟨hq_irr, ⟨E, inferInstance, inferInstance, hsfE, hfinE⟩, fun L _ _ hsfL => ?_⟩
  obtain ⟨eLE⟩ := splitting_field_unique_up_to_algEquiv hsfL hsfE
  have hfinL : Module.finrank K L = 2 := eLE.toLinearEquiv.finrank_eq.trans hfinE
  have hperf : IsGarlingPerfectField K :=
    (isGarlingPerfectField_iff_perfectField K).mpr inferInstance
  have hcardG : Nat.card (GarlingPolyGaloisGroup K L f) = 2 :=
    (theorem_11_5_perfect hperf hsfL).2.1.trans hfinL
  exact ⟨hfinL, hcardG, mulEquivZMod2OfNatCardTwo hcardG⟩

/-- Concrete degree-`8` splitting field `ℚ(2^(1/4), i) ⊆ ℂ` for **both** `X ^ 4 - 2` and `X ^ 4 + 2`
over `ℚ` (`Exercises 11.6 (a)` and `11.7 (a)`). -/
theorem rat_splittingField_X_pow_four_pm_two :
    ∃ E : IntermediateField ℚ ℂ,
      Module.finrank ℚ E = 8 ∧
      IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 - 2) ∧
      IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 + 2) := by
  open scoped IntermediateField in
  let r2R : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)
  let r2 : ℂ := r2R
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({r2, Complex.I} : Set ℂ)
  obtain ⟨hr2R_pow, _, hr2R_min, _⟩ :=
    real_rpow_inv_nat_minpoly_of_prime Nat.prime_two (by decide : 1 ≤ 4)
  have hr2R_eq : ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ)) = r2R := by simp [r2R]
  rw [hr2R_eq] at hr2R_pow hr2R_min
  have hr2_coe : (IsScalarTower.toAlgHom ℚ ℝ ℂ) r2R = r2 := rfl
  have hr2_pow : r2 ^ 4 = 2 := by
    change ((r2R : ℂ) ^ 4) = 2
    rw [← Complex.ofReal_pow, hr2R_pow]
    norm_num
  have hr2_ne0 : r2 ≠ 0 := fun h0 => by rw [h0] at hr2_pow; norm_num at hr2_pow
  have hr2_min : minpoly ℚ r2 = Polynomial.X ^ 4 - 2 := by
    rw [← hr2_coe, minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective r2R,
      hr2R_min]
    norm_num
    rw [map_ofNat]
  have hr2_int : IsIntegral ℚ r2 :=
    ⟨Polynomial.X ^ 4 - Polynomial.C 2, Polynomial.monic_X_pow_sub_C 2 (by decide), by simp [hr2_pow]⟩
  have hfin_r2 : Module.finrank ℚ ℚ⟮r2⟯ = 4 := by
    rw [IntermediateField.adjoin.finrank hr2_int, hr2_min, ← map_ofNat Polynomial.C 2,
      Polynomial.natDegree_X_pow_sub_C]
  have hI_not : Complex.I ∉ ℚ⟮r2⟯ := by
    intro hmem
    let φ : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
    have hle : ℚ⟮r2⟯ ≤ φ.fieldRange := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨r2R, rfl⟩
    obtain ⟨x, hx⟩ := hle hmem
    have him := congrArg Complex.im hx
    change ((x : ℝ) : ℂ).im = Complex.I.im at him
    rw [Complex.ofReal_im, Complex.I_im] at him
    norm_num at him
  let Ka : IntermediateField ℚ ℂ := ℚ⟮r2⟯
  let Eab : IntermediateField Ka ℂ := Ka⟮Complex.I⟯
  have hI_eval : Polynomial.aeval Complex.I (Polynomial.X ^ 2 + 1 : Ka[X]) = 0 := by
    rw [map_add, map_pow, Polynomial.aeval_X, map_one, Complex.I_sq]; ring
  have hI_int : IsIntegral Ka Complex.I :=
    ⟨Polynomial.X ^ 2 + 1, by monicity!, by rwa [← Polynomial.aeval_def]⟩
  have hfin_I : Module.finrank Ka Eab = 2 := by
    change Module.finrank Ka Ka⟮Complex.I⟯ = 2
    rw [IntermediateField.adjoin.finrank hI_int]
    have hdvd : minpoly Ka Complex.I ∣ (Polynomial.X ^ 2 + 1 : Ka[X]) :=
      minpoly.dvd Ka Complex.I hI_eval
    have hdeg_le : (minpoly Ka Complex.I).natDegree ≤ 2 := by
      have hp_deg : (Polynomial.X ^ 2 + 1 : Ka[X]).natDegree = 2 := by compute_degree!
      have hp_mon : (Polynomial.X ^ 2 + 1 : Ka[X]).Monic := by monicity!
      exact (Polynomial.natDegree_le_of_dvd hdvd hp_mon.ne_zero).trans_eq hp_deg
    have hdeg_pos : 0 < (minpoly Ka Complex.I).natDegree := minpoly.natDegree_pos hI_int
    have hdeg_ne1 : (minpoly Ka Complex.I).natDegree ≠ 1 := by
      intro hd1
      have hmon := minpoly.monic hI_int
      have heq : minpoly Ka Complex.I =
          Polynomial.X + Polynomial.C ((minpoly Ka Complex.I).coeff 0) := by
        ext k
        rcases k with _ | _ | k
        · simp
        · have hc1 : (minpoly Ka Complex.I).coeff 1 = 1 := by
            rw [← hd1, ← Polynomial.leadingCoeff, hmon.leadingCoeff]
          simp [hc1]
        · have hc0 : (minpoly Ka Complex.I).coeff (k + 2) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [hc0, Polynomial.coeff_X]
      have haev := minpoly.aeval Ka Complex.I
      rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haev
      change Complex.I + (((minpoly Ka Complex.I).coeff 0 : Ka) : ℂ) = 0 at haev
      have hI_eq : Complex.I = -(((minpoly Ka Complex.I).coeff 0 : Ka) : ℂ) := by
        linear_combination haev
      exact hI_not (hI_eq ▸ neg_mem ((minpoly Ka Complex.I).coeff 0).2)
    omega
  have hrestrict_eq : Eab.restrictScalars ℚ = E := by
    apply le_antisymm
    · intro z hz
      have hKa_le : Ka ≤ E := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      let E_over_Ka : IntermediateField Ka ℂ :=
        { E.toSubfield with algebraMap_mem' := fun x => hKa_le x.2 }
      have hb_mem : Complex.I ∈ E_over_Ka :=
        IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hb_mem) hz
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Eab.algebraMap_mem ⟨r2, IntermediateField.mem_adjoin_simple_self ℚ r2⟩
      · exact IntermediateField.mem_adjoin_simple_self Ka Complex.I
  have hfinE : Module.finrank ℚ E = 8 := by
    have hmul : Module.finrank ℚ Ka * Module.finrank Ka Eab =
        Module.finrank ℚ (Eab.restrictScalars ℚ) := Module.finrank_mul_finrank ℚ Ka Eab
    rw [hfin_r2, hfin_I, hrestrict_eq] at hmul
    exact hmul.symm
  -- 1. Splitting field for `X ^ 4 - 2`: roots `![r2, -r2, i*r2, -i*r2]`.
  let α : Fin 4 → ℂ := ![r2, -r2, Complex.I * r2, -(Complex.I * r2)]
  have hexp_sub : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 - 2) 4 1 α := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 4 - 2 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 4 - 2 := by simp
    rw [hmap]
    simp only [map_one, one_mul, α, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
    calc (Polynomial.X ^ 4 - 2 : ℂ[X])
        = Polynomial.X ^ 4 - Polynomial.C (r2 ^ 4) := by rw [hr2_pow, map_ofNat]
      _ = (Polynomial.X ^ 2 - Polynomial.C (r2 ^ 2)) *
            (Polynomial.X ^ 2 + Polynomial.C (r2 ^ 2)) := by simp only [map_pow]; ring
      _ = ((Polynomial.X - Polynomial.C r2) * (Polynomial.X + Polynomial.C r2)) *
            ((Polynomial.X - Polynomial.C (Complex.I * r2)) *
             (Polynomial.X + Polynomial.C (Complex.I * r2))) := by
          have hq1 : (Polynomial.X - Polynomial.C r2) * (Polynomial.X + Polynomial.C r2) =
              (Polynomial.X ^ 2 - Polynomial.C (r2 ^ 2) : ℂ[X]) := by simp only [map_pow]; ring
          have hq2 : (Polynomial.X - Polynomial.C (Complex.I * r2)) *
              (Polynomial.X + Polynomial.C (Complex.I * r2)) =
              (Polynomial.X ^ 2 + Polynomial.C (r2 ^ 2) : ℂ[X]) := by
            calc (Polynomial.X - Polynomial.C (Complex.I * r2)) *
                  (Polynomial.X + Polynomial.C (Complex.I * r2))
                = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2 * r2 ^ 2) := by
                  simp only [map_mul, map_pow]; ring
              _ = Polynomial.X ^ 2 + Polynomial.C (r2 ^ 2) := by
                  rw [Complex.I_sq, neg_one_mul, map_neg]; ring
          rw [hq1, hq2]
      _ = _ := by ring
  have hadj_sub : E = IntermediateField.adjoin ℚ (Set.range α) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      have hr2_mem : r2 ∈ IntermediateField.adjoin ℚ (Set.range α) :=
        IntermediateField.subset_adjoin ℚ (Set.range α) ⟨0, by simp [α]⟩
      rcases hz with rfl | rfl
      · exact hr2_mem
      · have hir2_mem : Complex.I * r2 ∈ IntermediateField.adjoin ℚ (Set.range α) :=
          IntermediateField.subset_adjoin ℚ (Set.range α) ⟨2, by simp [α]⟩
        have hdiv : (Complex.I * r2) / r2 = Complex.I := mul_div_cancel_right₀ Complex.I hr2_ne0
        exact hdiv ▸ div_mem hir2_mem hr2_mem
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hr2E : r2 ∈ E := IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      have hIE : Complex.I ∈ E := IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      fin_cases i
      · exact hr2E
      · exact neg_mem hr2E
      · exact mul_mem hIE hr2E
      · exact neg_mem (mul_mem hIE hr2E)
  have hf_sub_mon : (Polynomial.X ^ 4 - 2 : ℚ[X]).Monic := by
    rw [← map_ofNat Polynomial.C 2]
    exact Polynomial.monic_X_pow_sub_C 2 (by decide)
  have hsf_sub : IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 - 2) :=
    hadj_sub.symm ▸ theorem_7_1 hf_sub_mon.ne_zero hexp_sub
  -- 2. Splitting field for `X ^ 4 + 2`: `β₀ = r2 ^ 3 * (1 + i) / 2` satisfies `β₀ ^ 4 = -2`.
  let β₀ : ℂ := r2 ^ 3 * (1 + Complex.I) / 2
  have hβ₀_pow : β₀ ^ 4 = -2 := by
    have h1I_4 : (1 + Complex.I) ^ 4 = -4 := by
      calc (1 + Complex.I) ^ 4 = ((1 + Complex.I) ^ 2) ^ 2 := by ring
        _ = (2 * Complex.I) ^ 2 := by
            have hsq : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
              calc (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
                _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
            rw [hsq]
        _ = 4 * Complex.I ^ 2 := by ring
        _ = -4 := by rw [Complex.I_sq]; ring
    calc β₀ ^ 4 = (r2 ^ 4) ^ 3 * (1 + Complex.I) ^ 4 / 16 := by dsimp [β₀]; ring
      _ = 2 ^ 3 * (-4) / 16 := by rw [hr2_pow, h1I_4]
      _ = -2 := by norm_num
  have hβ₀_ne0 : β₀ ≠ 0 := fun h0 => by rw [h0] at hβ₀_pow; norm_num at hβ₀_pow
  let β : Fin 4 → ℂ := ![β₀, -β₀, Complex.I * β₀, -(Complex.I * β₀)]
  have hexp_add : GarlingSplitsExplicit ℚ ℂ (Polynomial.X ^ 4 + 2) 4 1 β := by
    unfold GarlingSplitsExplicit
    have hmap : (Polynomial.X ^ 4 + 2 : ℚ[X]).map (algebraMap ℚ ℂ) = Polynomial.X ^ 4 + 2 := by simp
    rw [hmap]
    simp only [map_one, one_mul, β, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
    calc (Polynomial.X ^ 4 + 2 : ℂ[X])
        = Polynomial.X ^ 4 - Polynomial.C (β₀ ^ 4) := by
          rw [hβ₀_pow, map_neg, map_ofNat, sub_neg_eq_add]
      _ = (Polynomial.X ^ 2 - Polynomial.C (β₀ ^ 2)) *
            (Polynomial.X ^ 2 + Polynomial.C (β₀ ^ 2)) := by simp only [map_pow]; ring
      _ = ((Polynomial.X - Polynomial.C β₀) * (Polynomial.X + Polynomial.C β₀)) *
            ((Polynomial.X - Polynomial.C (Complex.I * β₀)) *
             (Polynomial.X + Polynomial.C (Complex.I * β₀))) := by
          have hq1 : (Polynomial.X - Polynomial.C β₀) * (Polynomial.X + Polynomial.C β₀) =
              (Polynomial.X ^ 2 - Polynomial.C (β₀ ^ 2) : ℂ[X]) := by simp only [map_pow]; ring
          have hq2 : (Polynomial.X - Polynomial.C (Complex.I * β₀)) *
              (Polynomial.X + Polynomial.C (Complex.I * β₀)) =
              (Polynomial.X ^ 2 + Polynomial.C (β₀ ^ 2) : ℂ[X]) := by
            calc (Polynomial.X - Polynomial.C (Complex.I * β₀)) *
                  (Polynomial.X + Polynomial.C (Complex.I * β₀))
                = Polynomial.X ^ 2 - Polynomial.C (Complex.I ^ 2 * β₀ ^ 2) := by
                  simp only [map_mul, map_pow]; ring
              _ = Polynomial.X ^ 2 + Polynomial.C (β₀ ^ 2) := by
                  rw [Complex.I_sq, neg_one_mul, map_neg]; ring
          rw [hq1, hq2]
      _ = _ := by ring
  have hadj_add : E = IntermediateField.adjoin ℚ (Set.range β) := by
    let F := IntermediateField.adjoin ℚ (Set.range β)
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      have hβ₀_mem : β₀ ∈ F := IntermediateField.subset_adjoin ℚ (Set.range β) ⟨0, by simp [β]⟩
      have hiβ₀_mem : Complex.I * β₀ ∈ F :=
        IntermediateField.subset_adjoin ℚ (Set.range β) ⟨2, by simp [β]⟩
      have hI_mem : Complex.I ∈ F :=
        (mul_div_cancel_right₀ Complex.I hβ₀_ne0) ▸ div_mem hiβ₀_mem hβ₀_mem
      rcases hz with rfl | rfl
      · have hr2_cube : β₀ * (1 - Complex.I) = r2 ^ 3 := by
          calc β₀ * (1 - Complex.I)
              = r2 ^ 3 * (1 - Complex.I ^ 2) / 2 := by dsimp [β₀]; ring
            _ = r2 ^ 3 := by rw [Complex.I_sq]; ring
        have hr2_cube_mem : r2 ^ 3 ∈ F :=
          hr2_cube ▸ mul_mem hβ₀_mem (sub_mem F.one_mem hI_mem)
        have hr2_eq : (2 : ℂ) / r2 ^ 3 = r2 := by
          rw [← hr2_pow, pow_succ, mul_div_cancel_left₀ r2 (pow_ne_zero 3 hr2_ne0)]
        have h2_mem : (2 : ℂ) ∈ F := by simp
        exact hr2_eq ▸ div_mem h2_mem hr2_cube_mem
      · exact hI_mem
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hr2E : r2 ∈ E := IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      have hIE : Complex.I ∈ E := IntermediateField.subset_adjoin ℚ ({r2, Complex.I} : Set ℂ) (by simp)
      have h2E : (2 : ℂ) ∈ E := by simp
      have hβ₀E : β₀ ∈ E :=
        div_mem (mul_mem (pow_mem hr2E 3) (add_mem E.one_mem hIE)) h2E
      fin_cases i
      · exact hβ₀E
      · exact neg_mem hβ₀E
      · exact mul_mem hIE hβ₀E
      · exact neg_mem (mul_mem hIE hβ₀E)
  have hf_add_mon : (Polynomial.X ^ 4 + 2 : ℚ[X]).Monic := by
    rw [← map_ofNat Polynomial.C 2]
    exact Polynomial.monic_X_pow_add_C 2 (by decide)
  have hsf_add : IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 + 2) :=
    hadj_add.symm ▸ theorem_7_1 hf_add_mon.ne_zero hexp_add
  exact ⟨E, hfinE, hsf_sub, hsf_add⟩

local instance instFactPrime3 : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance instFactPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance instFactPrime7 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **Exercise 11.6** (§11.2, printed p. 95 / PDF p. 103; see `QUEUE.md` on `"Find..."` prompt):
*"Find the Galois group of `x⁴ - 2` over (a) `ℚ`, (b) `ℤ₃`, and (c) `ℤ₇`."*
- **(a) Over `ℚ`:** `Γ_ℚ(x⁴ - 2) ≅ D₄` (`DihedralGroup 4`, order `8`, splitting field `ℚ(2^(1/4), i)`).
- **(b) Over `ℤ₃`:** `x⁴ - 2 = (x² + x + 2)(x² + 2x + 2)`, splitting field of degree `2`,
  `Γ_{ℤ₃}(x⁴ - 2) ≅ C₂` (`Multiplicative (ZMod 2)`, order `2`).
- **(c) Over `ℤ₇`:** `x⁴ - 2 = (x - 2)(x - 5)(x² - 3)`, splitting field of degree `2`,
  `Γ_{ℤ₇}(x⁴ - 2) ≅ C₂` (`Multiplicative (ZMod 2)`, order `2`). -/
theorem exercise_11_6 :
    -- (a) Over `ℚ`: concrete degree-`8` splitting field + universal `D₄` isomorphism
    ((∃ E : IntermediateField ℚ ℂ,
        IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 - 2) ∧ Module.finrank ℚ E = 8) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 - 2) →
        Module.finrank ℚ L = 8 ∧
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2)) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2) ≃* DihedralGroup 4)) ∧
    -- (b) Over `ℤ₃`: concrete degree-`2` splitting field + universal `C₂` isomorphism
    ((∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 3) E),
        IsGarlingSplittingFieldExtension (ZMod 3) E (Polynomial.X ^ 4 - 2) ∧
        Module.finrank (ZMod 3) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 3) L],
        IsGarlingSplittingFieldExtension (ZMod 3) L (Polynomial.X ^ 4 - 2) →
        Module.finrank (ZMod 3) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 - 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 - 2) ≃*
          Multiplicative (ZMod 2))) ∧
    -- (c) Over `ℤ₇`: concrete degree-`2` splitting field + universal `C₂` isomorphism
    ((∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 7) E),
        IsGarlingSplittingFieldExtension (ZMod 7) E (Polynomial.X ^ 4 - 2) ∧
        Module.finrank (ZMod 7) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 7) L],
        IsGarlingSplittingFieldExtension (ZMod 7) L (Polynomial.X ^ 4 - 2) →
        Module.finrank (ZMod 7) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 7) L (Polynomial.X ^ 4 - 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 7) L (Polynomial.X ^ 4 - 2) ≃*
          Multiplicative (ZMod 2))) := by
  have hq3_noroots_dec : ∀ z : ZMod 3, z ^ 2 + z + 2 ≠ 0 := by decide
  have hq7_noroots_dec : ∀ z : ZMod 7, z ^ 2 - 3 ≠ 0 := by decide
  -- Part (a): over `ℚ`
  have ha : (∃ E : IntermediateField ℚ ℂ,
        IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 - 2) ∧ Module.finrank ℚ E = 8) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 - 2) →
        Module.finrank ℚ L = 8 ∧
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2)) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2) ≃* DihedralGroup 4) := by
    obtain ⟨E, hfinE, hsfE, _⟩ := rat_splittingField_X_pow_four_pm_two
    have hsep : (Polynomial.X ^ 4 - 2 : ℚ[X]).Separable := by
      rw [← map_ofNat Polynomial.C 2]
      exact separable_X_pow_four_sub_C (K := ℚ) (c := 2) (by norm_num) (by norm_num)
    have hdeg : (Polynomial.X ^ 4 - 2 : ℚ[X]).natDegree = 4 := by
      rw [← map_ofNat Polynomial.C 2]
      exact Polynomial.natDegree_X_pow_sub_C
    exact ⟨⟨E, hsfE, hfinE⟩,
      quartic_galoisGroup_d4_of_splittingField_finrank_eight hsep hdeg hsfE hfinE⟩
  -- Part (b): over `ZMod 3`, `q = X^2 + X + 2`, roots `α, 2α + 2, 2α, α + 1`.
  have hb : (∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 3) E),
        IsGarlingSplittingFieldExtension (ZMod 3) E (Polynomial.X ^ 4 - 2) ∧
        Module.finrank (ZMod 3) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 3) L],
        IsGarlingSplittingFieldExtension (ZMod 3) L (Polynomial.X ^ 4 - 2) →
        Module.finrank (ZMod 3) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 - 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 - 2) ≃*
          Multiplicative (ZMod 2)) := by
    let f3 : (ZMod 3)[X] := Polynomial.X ^ 4 - 2
    let q3 : (ZMod 3)[X] := Polynomial.X ^ 2 + Polynomial.X + 2
    have hf3_ne0 : f3 ≠ 0 := by
      change (Polynomial.X ^ 4 - Polynomial.C 2 : (ZMod 3)[X]) ≠ 0
      exact (Polynomial.monic_X_pow_sub_C (2 : ZMod 3) (by decide)).ne_zero
    have hq3_mon : q3.Monic := by dsimp [q3]; monicity!
    have hq3_deg : q3.natDegree = 2 := by dsimp [q3]; compute_degree!
    have hq3_noroots : ∀ z : ZMod 3, q3.eval z ≠ 0 := by
      intro z
      simpa [q3] using hq3_noroots_dec z
    let α : AdjoinRoot q3 := AdjoinRoot.root q3
    have hα_sq : α ^ 2 = -α - 2 := by
      have hr : α ^ 2 + α + 2 = 0 := by
        simpa [q3, α] using AdjoinRoot.eval₂_root q3
      linear_combination hr
    let β3 : Fin 4 → AdjoinRoot q3 := ![α, 2 * α + 2, 2 * α, α + 1]
    have hfac3 : f3.map (algebraMap (ZMod 3) (AdjoinRoot q3)) =
        ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β3 i)) := by
      have hmap : f3.map (algebraMap (ZMod 3) (AdjoinRoot q3)) =
          Polynomial.X ^ 4 - Polynomial.C 2 := by simp [f3, map_ofNat]
      rw [hmap]
      simp only [β3, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one]
      have hchar3 : (3 : AdjoinRoot q3) = 0 := by
        rw [← map_ofNat (algebraMap (ZMod 3) (AdjoinRoot q3)) 3,
          show (3 : ZMod 3) = 0 by decide, map_zero]
      have hp1 : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (2 * α + 2)) =
          Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 2 := by
        calc (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (2 * α + 2))
            = Polynomial.X ^ 2 + Polynomial.C (1 - (3 : AdjoinRoot q3) * (α + 1)) * Polynomial.X +
                Polynomial.C (2 * (α ^ 2 + α + 2) + 2 - 2 * (3 : AdjoinRoot q3)) := by
              simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
          _ = Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 2 := by
              have hr : α ^ 2 + α + 2 = 0 := by linear_combination hα_sq
              rw [hchar3, hr]; simp
      have hp2 : (Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (α + 1)) =
          Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2 := by
        calc (Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (α + 1))
            = Polynomial.X ^ 2 + Polynomial.C (2 - (3 : AdjoinRoot q3) * (α + 1)) * Polynomial.X +
                Polynomial.C (2 * (α ^ 2 + α + 2) + 2 - 2 * (3 : AdjoinRoot q3)) := by
              simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
          _ = Polynomial.X ^ 2 + Polynomial.X * Polynomial.C 2 + Polynomial.C 2 := by
              have hr : α ^ 2 + α + 2 = 0 := by linear_combination hα_sq
              rw [hchar3, hr]; simp
          _ = Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2 := by ring
      calc (Polynomial.X ^ 4 - Polynomial.C 2 : (AdjoinRoot q3)[X])
          = (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 2) *
              (Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2) -
              Polynomial.C (3 : AdjoinRoot q3) *
                (Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 +
                 Polynomial.C 2 * Polynomial.X + Polynomial.C 2) := by
            simp only [map_ofNat]; ring
        _ = (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 2) *
              (Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2) := by
            rw [hchar3]; simp
        _ = ((Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (2 * α + 2))) *
              ((Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (α + 1))) := by
            rw [hp1, hp2]
        _ = _ := by ring
    have hres := quartic_galoisGroup_c2_of_quad_adjoinRoot hf3_ne0 hq3_mon hq3_deg hq3_noroots
      β3 hfac3 ⟨0, rfl⟩
    exact ⟨hres.2.1, hres.2.2⟩
  -- Part (c): over `ZMod 7`, `q = X^2 - 3`, roots `2, -2, α, -α`.
  have hc : (∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 7) E),
        IsGarlingSplittingFieldExtension (ZMod 7) E (Polynomial.X ^ 4 - 2) ∧
        Module.finrank (ZMod 7) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 7) L],
        IsGarlingSplittingFieldExtension (ZMod 7) L (Polynomial.X ^ 4 - 2) →
        Module.finrank (ZMod 7) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 7) L (Polynomial.X ^ 4 - 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 7) L (Polynomial.X ^ 4 - 2) ≃*
          Multiplicative (ZMod 2)) := by
    let f7 : (ZMod 7)[X] := Polynomial.X ^ 4 - 2
    let q7 : (ZMod 7)[X] := Polynomial.X ^ 2 - 3
    have hf7_ne0 : f7 ≠ 0 := by
      change (Polynomial.X ^ 4 - Polynomial.C 2 : (ZMod 7)[X]) ≠ 0
      exact (Polynomial.monic_X_pow_sub_C (2 : ZMod 7) (by decide)).ne_zero
    have hq7_mon : q7.Monic := by
      change (Polynomial.X ^ 2 - Polynomial.C 3 : (ZMod 7)[X]).Monic
      exact Polynomial.monic_X_pow_sub_C (3 : ZMod 7) (by decide)
    have hq7_deg : q7.natDegree = 2 := by
      change (Polynomial.X ^ 2 - Polynomial.C 3 : (ZMod 7)[X]).natDegree = 2
      exact Polynomial.natDegree_X_pow_sub_C
    have hq7_noroots : ∀ z : ZMod 7, q7.eval z ≠ 0 := by
      intro z
      simpa [q7] using hq7_noroots_dec z
    let α : AdjoinRoot q7 := AdjoinRoot.root q7
    have hα_sq : α ^ 2 = 3 := by
      have hr : α ^ 2 - 3 = 0 := by simpa [q7, α] using AdjoinRoot.eval₂_root q7
      linear_combination hr
    let β7 : Fin 4 → AdjoinRoot q7 := ![2, -2, α, -α]
    have hfac7 : f7.map (algebraMap (ZMod 7) (AdjoinRoot q7)) =
        ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β7 i)) := by
      have hmap : f7.map (algebraMap (ZMod 7) (AdjoinRoot q7)) =
          Polynomial.X ^ 4 - Polynomial.C 2 := by simp [f7, map_ofNat]
      rw [hmap]
      simp only [β7, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add]
      have hchar7 : (7 : AdjoinRoot q7) = 0 := by
        rw [← map_ofNat (algebraMap (ZMod 7) (AdjoinRoot q7)) 7,
          show (7 : ZMod 7) = 0 by decide, map_zero]
      have hpα : (Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α) =
          Polynomial.X ^ 2 - Polynomial.C 3 := by
        calc (Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α)
            = Polynomial.X ^ 2 - Polynomial.C (α ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 - Polynomial.C 3 := by rw [hα_sq]
      calc (Polynomial.X ^ 4 - Polynomial.C 2 : (AdjoinRoot q7)[X])
          = (Polynomial.X - Polynomial.C 2) * (Polynomial.X + Polynomial.C 2) *
              (Polynomial.X ^ 2 - Polynomial.C 3) +
              Polynomial.C (7 : AdjoinRoot q7) * (Polynomial.X ^ 2 - Polynomial.C 2) := by
            simp only [map_ofNat]; ring
        _ = (Polynomial.X - Polynomial.C 2) * (Polynomial.X + Polynomial.C 2) *
              (Polynomial.X ^ 2 - Polynomial.C 3) := by rw [hchar7]; simp
        _ = (Polynomial.X - Polynomial.C 2) * (Polynomial.X + Polynomial.C 2) *
              ((Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α)) := by rw [hpα]
        _ = _ := by ring
    have hres := quartic_galoisGroup_c2_of_quad_adjoinRoot hf7_ne0 hq7_mon hq7_deg hq7_noroots
      β7 hfac7 ⟨2, rfl⟩
    exact ⟨hres.2.1, hres.2.2⟩
  exact ⟨ha, hb, hc⟩

/-- **Exercise 11.7** (§11.2, printed p. 96 / PDF p. 104; see `QUEUE.md` on `"Find..."` prompt):
*"Find the Galois group of `x⁴ + 2` over (a) `ℚ`, (b) `ℤ₃`, and (c) `ℤ₅`."*
- **(a) Over `ℚ`:** `Γ_ℚ(x⁴ + 2) ≅ D₄` (`DihedralGroup 4`, order `8`, splitting field `ℚ(2^(1/4), i)`).
- **(b) Over `ℤ₃`:** `x⁴ + 2 = x⁴ - 1 = (x - 1)(x + 1)(x² + 1)`, splitting field of degree `2`,
  `Γ_{ℤ₃}(x⁴ + 2) ≅ C₂` (`Multiplicative (ZMod 2)`, order `2`).
- **(c) Over `ℤ₅`:** `x⁴ + 2` is irreducible of degree `4` over `ℤ₅`, splitting field of degree `4`,
  `Γ_{ℤ₅}(x⁴ + 2) ≅ C₄` (`Multiplicative (ZMod 4)`, order `4`). -/
theorem exercise_11_7 :
    -- (a) Over `ℚ`: concrete degree-`8` splitting field + universal `D₄` isomorphism
    ((∃ E : IntermediateField ℚ ℂ,
        IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 + 2) ∧ Module.finrank ℚ E = 8) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 + 2) →
        Module.finrank ℚ L = 8 ∧
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 2)) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 2) ≃* DihedralGroup 4)) ∧
    -- (b) Over `ℤ₃`: concrete degree-`2` splitting field + universal `C₂` isomorphism
    ((∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 3) E),
        IsGarlingSplittingFieldExtension (ZMod 3) E (Polynomial.X ^ 4 + 2) ∧
        Module.finrank (ZMod 3) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 3) L],
        IsGarlingSplittingFieldExtension (ZMod 3) L (Polynomial.X ^ 4 + 2) →
        Module.finrank (ZMod 3) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 + 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 + 2) ≃*
          Multiplicative (ZMod 2))) ∧
    -- (c) Over `ℤ₅`: irreducibility + concrete degree-`4` splitting field + universal `C₄` isomorphism
    (Irreducible (Polynomial.X ^ 4 + 2 : (ZMod 5)[X]) ∧
      (∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 5) E),
        IsGarlingSplittingFieldExtension (ZMod 5) E (Polynomial.X ^ 4 + 2) ∧
        Module.finrank (ZMod 5) E = 4) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 5) L],
        IsGarlingSplittingFieldExtension (ZMod 5) L (Polynomial.X ^ 4 + 2) →
        Module.finrank (ZMod 5) L = 4 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 5) L (Polynomial.X ^ 4 + 2)) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 5) L (Polynomial.X ^ 4 + 2) ≃*
          Multiplicative (ZMod 4))) := by
  have hno_quad5 : ¬ ∃ a b c d : ZMod 5,
      a + c = 0 ∧ b + d + a * c = 0 ∧ a * d + b * c = 0 ∧ b * d = 2 := by decide
  have hq3_noroots_dec : ∀ z : ZMod 3, z ^ 2 + 1 ≠ 0 := by decide
  have hf5_noroots_dec : ∀ z : ZMod 5, z ^ 4 + 2 ≠ 0 := by decide
  -- Part (a): over `ℚ`
  have ha : (∃ E : IntermediateField ℚ ℂ,
        IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 4 + 2) ∧ Module.finrank ℚ E = 8) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 + 2) →
        Module.finrank ℚ L = 8 ∧
        Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 2)) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 2) ≃* DihedralGroup 4) := by
    obtain ⟨E, hfinE, _, hsfE⟩ := rat_splittingField_X_pow_four_pm_two
    have hsep : (Polynomial.X ^ 4 + 2 : ℚ[X]).Separable := by
      have heq : (Polynomial.X ^ 4 + 2 : ℚ[X]) = Polynomial.X ^ 4 - Polynomial.C (-2) := by
        rw [map_neg, map_ofNat, sub_neg_eq_add]
      rw [heq]
      exact separable_X_pow_four_sub_C (K := ℚ) (c := -2) (by norm_num) (by norm_num)
    have hdeg : (Polynomial.X ^ 4 + 2 : ℚ[X]).natDegree = 4 := by
      rw [← map_ofNat Polynomial.C 2]
      exact Polynomial.natDegree_X_pow_add_C
    exact ⟨⟨E, hsfE, hfinE⟩,
      quartic_galoisGroup_d4_of_splittingField_finrank_eight hsep hdeg hsfE hfinE⟩
  -- Part (b): over `ZMod 3`, `X^4 + 2 = X^4 - 1 = (X - 1)(X + 1)(X^2 + 1)`.
  have hb : (∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 3) E),
        IsGarlingSplittingFieldExtension (ZMod 3) E (Polynomial.X ^ 4 + 2) ∧
        Module.finrank (ZMod 3) E = 2) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 3) L],
        IsGarlingSplittingFieldExtension (ZMod 3) L (Polynomial.X ^ 4 + 2) →
        Module.finrank (ZMod 3) L = 2 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 + 2)) = 2 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 3) L (Polynomial.X ^ 4 + 2) ≃*
          Multiplicative (ZMod 2)) := by
    let f3 : (ZMod 3)[X] := Polynomial.X ^ 4 + 2
    let q3 : (ZMod 3)[X] := Polynomial.X ^ 2 + 1
    have hf3_ne0 : f3 ≠ 0 := by
      change (Polynomial.X ^ 4 + Polynomial.C 2 : (ZMod 3)[X]) ≠ 0
      exact (Polynomial.monic_X_pow_add_C (2 : ZMod 3) (by decide)).ne_zero
    have hq3_mon : q3.Monic := by
      change (Polynomial.X ^ 2 + Polynomial.C 1 : (ZMod 3)[X]).Monic
      exact Polynomial.monic_X_pow_add_C (1 : ZMod 3) (by decide)
    have hq3_deg : q3.natDegree = 2 := by
      change (Polynomial.X ^ 2 + Polynomial.C 1 : (ZMod 3)[X]).natDegree = 2
      exact Polynomial.natDegree_X_pow_add_C
    have hq3_noroots : ∀ z : ZMod 3, q3.eval z ≠ 0 := by
      intro z
      simpa [q3] using hq3_noroots_dec z
    let α : AdjoinRoot q3 := AdjoinRoot.root q3
    have hα_sq : α ^ 2 = -1 := by
      have hr : α ^ 2 + 1 = 0 := by simpa [q3, α] using AdjoinRoot.eval₂_root q3
      linear_combination hr
    let β3 : Fin 4 → AdjoinRoot q3 := ![1, -1, α, -α]
    have hfac3 : f3.map (algebraMap (ZMod 3) (AdjoinRoot q3)) =
        ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β3 i)) := by
      have hmap : f3.map (algebraMap (ZMod 3) (AdjoinRoot q3)) =
          Polynomial.X ^ 4 + Polynomial.C 2 := by simp [f3, map_ofNat]
      rw [hmap]
      simp only [β3, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, map_neg, sub_neg_eq_add, map_one]
      have hchar3 : (3 : AdjoinRoot q3) = 0 := by
        rw [← map_ofNat (algebraMap (ZMod 3) (AdjoinRoot q3)) 3,
          show (3 : ZMod 3) = 0 by decide, map_zero]
      have hpα : (Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α) =
          Polynomial.X ^ 2 + 1 := by
        calc (Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α)
            = Polynomial.X ^ 2 - Polynomial.C (α ^ 2) := by simp only [map_pow]; ring
          _ = Polynomial.X ^ 2 + 1 := by rw [hα_sq, map_neg, map_one, sub_neg_eq_add]
      calc (Polynomial.X ^ 4 + Polynomial.C 2 : (AdjoinRoot q3)[X])
          = (Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + 1) +
              Polynomial.C (3 : AdjoinRoot q3) := by
            simp only [map_ofNat]; ring
        _ = (Polynomial.X - 1) * (Polynomial.X + 1) * (Polynomial.X ^ 2 + 1) := by
            rw [hchar3, map_zero, add_zero]
        _ = (Polynomial.X - 1) * (Polynomial.X + 1) *
              ((Polynomial.X - Polynomial.C α) * (Polynomial.X + Polynomial.C α)) := by rw [hpα]
        _ = _ := by ring
    have hres := quartic_galoisGroup_c2_of_quad_adjoinRoot hf3_ne0 hq3_mon hq3_deg hq3_noroots
      β3 hfac3 ⟨2, rfl⟩
    exact ⟨hres.2.1, hres.2.2⟩
  -- Part (c): over `ZMod 5`, `f5 = X^4 + 2` is irreducible of degree `4`, `Γ ≃* C₄`.
  have hc : Irreducible (Polynomial.X ^ 4 + 2 : (ZMod 5)[X]) ∧
      (∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 5) E),
        IsGarlingSplittingFieldExtension (ZMod 5) E (Polynomial.X ^ 4 + 2) ∧
        Module.finrank (ZMod 5) E = 4) ∧
      ∀ (L : Type u) [Field L] [Algebra (ZMod 5) L],
        IsGarlingSplittingFieldExtension (ZMod 5) L (Polynomial.X ^ 4 + 2) →
        Module.finrank (ZMod 5) L = 4 ∧
        Nat.card (GarlingPolyGaloisGroup (ZMod 5) L (Polynomial.X ^ 4 + 2)) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup (ZMod 5) L (Polynomial.X ^ 4 + 2) ≃*
          Multiplicative (ZMod 4)) := by
    let f5 : (ZMod 5)[X] := Polynomial.X ^ 4 + 2
    have hf5_mon : f5.Monic := by
      change (Polynomial.X ^ 4 + Polynomial.C 2 : (ZMod 5)[X]).Monic
      exact Polynomial.monic_X_pow_add_C (2 : ZMod 5) (by decide)
    have hf5_deg : f5.natDegree = 4 := by
      change (Polynomial.X ^ 4 + Polynomial.C 2 : (ZMod 5)[X]).natDegree = 4
      exact Polynomial.natDegree_X_pow_add_C
    have hf5_noroots : ∀ z : ZMod 5, f5.eval z ≠ 0 := by
      intro z
      simpa [f5] using hf5_noroots_dec z
    have hf5_irr : Irreducible f5 := by
      refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
      · have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        omega
      · by_contra hboth
        push Not at hboth
        rcases hboth with ⟨hgu, hhu⟩
        have hg0 : g ≠ 0 := fun h0 => hf5_mon.ne_zero (by rw [hgh, h0, zero_mul])
        have hh0 : h ≠ 0 := fun h0 => hf5_mon.ne_zero (by rw [hgh, h0, mul_zero])
        have hgd : 1 ≤ g.natDegree := Nat.pos_of_ne_zero fun hd0 =>
          hgu (Polynomial.isUnit_iff.mpr ⟨g.coeff 0,
            isUnit_iff_ne_zero.mpr fun hc0 => hg0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by simp [hc0])),
            (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩)
        have hhd : 1 ≤ h.natDegree := Nat.pos_of_ne_zero fun hd0 =>
          hhu (Polynomial.isUnit_iff.mpr ⟨h.coeff 0,
            isUnit_iff_ne_zero.mpr fun hc0 => hh0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by simp [hc0])),
            (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩)
        have hsum : g.natDegree + h.natDegree = 4 := by
          rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hf5_deg]
        have hcases : g.natDegree = 1 ∨ h.natDegree = 1 ∨ (g.natDegree = 2 ∧ h.natDegree = 2) := by
          omega
        rcases hcases with hg1 | hh1 | ⟨hg2, hh2⟩
        · obtain ⟨z, hz⟩ := Polynomial.exists_root_of_degree_eq_one
            ((Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr hg1)
          exact hf5_noroots z (by rw [hgh, Polynomial.eval_mul, hz.eq_zero, zero_mul])
        · obtain ⟨z, hz⟩ := Polynomial.exists_root_of_degree_eq_one
            ((Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr hh1)
          exact hf5_noroots z (by rw [hgh, Polynomial.eval_mul, hz.eq_zero, mul_zero])
        · -- Normalize `g, h` to monic quadratics `g₁, h₁` with `g₁ * h₁ = f5`.
          have hglc_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
          let g₁ : (ZMod 5)[X] := Polynomial.C g.leadingCoeff⁻¹ * g
          let h₁ : (ZMod 5)[X] := Polynomial.C g.leadingCoeff * h
          have hg₁h₁ : g₁ * h₁ = f5 := by
            calc g₁ * h₁ = Polynomial.C (g.leadingCoeff⁻¹ * g.leadingCoeff) * (g * h) := by
                  simp only [g₁, h₁, Polynomial.C_mul]; ring
              _ = f5 := by rw [inv_mul_cancel₀ hglc_ne, map_one, one_mul, hgh]
          have hg₁_deg : g₁.natDegree = 2 := by
            dsimp [g₁]
            rw [Polynomial.natDegree_C_mul (inv_ne_zero hglc_ne), hg2]
          have hh₁_deg : h₁.natDegree = 2 := by
            dsimp [h₁]
            rw [Polynomial.natDegree_C_mul hglc_ne, hh2]
          have hg₁_mon : g₁.Monic := by
            rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
              inv_mul_cancel₀ hglc_ne]
          have hh₁_mon : h₁.Monic := by
            have hlc : (g₁ * h₁).leadingCoeff = 1 := hg₁h₁ ▸ hf5_mon
            rw [Polynomial.leadingCoeff_mul, hg₁_mon.leadingCoeff, one_mul] at hlc
            exact hlc
          have quad_expand : ∀ p : (ZMod 5)[X], p.Monic → p.natDegree = 2 →
              p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
                Polynomial.C (p.coeff 0) := by
            intro p hp_mon hp_deg
            ext k
            rcases k with _ | _ | _ | k
            · simp
            · simp
            · have hp2 : p.coeff 2 = 1 := by
                rw [← hp_deg, ← Polynomial.leadingCoeff, hp_mon.leadingCoeff]
              simp [hp2]
            · have hp_zero : p.coeff (k + 3) = 0 :=
                Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
              simp [hp_zero]
          have hg₁_eq := quad_expand g₁ hg₁_mon hg₁_deg
          have hh₁_eq := quad_expand h₁ hh₁_mon hh₁_deg
          let a := g₁.coeff 1; let b := g₁.coeff 0
          let c := h₁.coeff 1; let d := h₁.coeff 0
          have hprod : Polynomial.X ^ 4 + Polynomial.C (a + c) * Polynomial.X ^ 3 +
              Polynomial.C (b + d + a * c) * Polynomial.X ^ 2 +
              Polynomial.C (a * d + b * c) * Polynomial.X + Polynomial.C (b * d) =
              Polynomial.X ^ 4 + Polynomial.C (2 : ZMod 5) := by
            calc _ = (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b) *
                    (Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) := by
                  simp only [map_add, map_mul]; ring
              _ = g₁ * h₁ := by rw [← hg₁_eq, ← hh₁_eq]
              _ = f5 := hg₁h₁
              _ = Polynomial.X ^ 4 + Polynomial.C (2 : ZMod 5) := by simp [f5, map_ofNat]
          have hc3_eq : a + c = 0 := by
            have h := congrArg (fun p => p.coeff 3) hprod
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_X, Polynomial.coeff_C] at h
            simpa using h
          have hc2_eq : b + d + a * c = 0 := by
            have h := congrArg (fun p => p.coeff 2) hprod
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_X, Polynomial.coeff_C] at h
            simpa using h
          have hc1_eq : a * d + b * c = 0 := by
            have h := congrArg (fun p => p.coeff 1) hprod
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_X, Polynomial.coeff_C] at h
            simpa using h
          have hc0_eq : b * d = 2 := by
            have h := congrArg (fun p => p.coeff 0) hprod
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_X, Polynomial.coeff_C] at h
            simpa using h
          exact hno_quad5 ⟨a, b, c, d, hc3_eq, hc2_eq, hc1_eq, hc0_eq⟩
    have _ : Fact (Irreducible f5) := ⟨hf5_irr⟩
    let E := AdjoinRoot f5
    let α : E := AdjoinRoot.root f5
    have hfinE : Module.finrank (ZMod 5) E = 4 :=
      (PowerBasis.finrank (AdjoinRoot.powerBasis hf5_mon.ne_zero)).trans hf5_deg
    have hα_pow : α ^ 4 = -2 := by
      have hr : α ^ 4 + 2 = 0 := by simpa [f5, α] using AdjoinRoot.eval₂_root f5
      linear_combination hr
    have hchar5 : (5 : E) = 0 := by
      rw [← map_ofNat (algebraMap (ZMod 5) E) 5, show (5 : ZMod 5) = 0 by decide, map_zero]
    let β5 : Fin 4 → E := ![α, 2 * α, 3 * α, 4 * α]
    have hfac5 : f5.map (algebraMap (ZMod 5) E) =
        ∏ i : Fin 4, (Polynomial.X - Polynomial.C (β5 i)) := by
      have hmap : f5.map (algebraMap (ZMod 5) E) = Polynomial.X ^ 4 + Polynomial.C 2 := by
        simp [f5, map_ofNat]
      rw [hmap]
      simp only [β5, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one]
      have hp14 : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (4 * α)) =
          Polynomial.X ^ 2 - Polynomial.C (α ^ 2) := by
        calc (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (4 * α))
            = Polynomial.X ^ 2 - Polynomial.C ((5 : E) * α) * Polynomial.X +
                Polynomial.C (((5 : E) - 1) * α ^ 2) := by
              simp only [map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
          _ = Polynomial.X ^ 2 - Polynomial.C (α ^ 2) := by
              rw [hchar5]; simp [sub_eq_add_neg]
      have hp23 : (Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (3 * α)) =
          Polynomial.X ^ 2 + Polynomial.C (α ^ 2) := by
        calc (Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (3 * α))
            = Polynomial.X ^ 2 - Polynomial.C ((5 : E) * α) * Polynomial.X +
                Polynomial.C (((5 : E) + 1) * α ^ 2) := by
              simp only [map_add, map_mul, map_pow, map_one, map_ofNat]; ring
          _ = Polynomial.X ^ 2 + Polynomial.C (α ^ 2) := by
              rw [hchar5]; simp
      calc (Polynomial.X ^ 4 + Polynomial.C 2 : E[X])
          = Polynomial.X ^ 4 - Polynomial.C (α ^ 4) := by
            rw [hα_pow, map_neg, sub_neg_eq_add]
        _ = (Polynomial.X ^ 2 - Polynomial.C (α ^ 2)) *
              (Polynomial.X ^ 2 + Polynomial.C (α ^ 2)) := by simp only [map_pow]; ring
        _ = ((Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (4 * α))) *
              ((Polynomial.X - Polynomial.C (2 * α)) * (Polynomial.X - Polynomial.C (3 * α))) := by
            rw [hp14, hp23]
        _ = _ := by ring
    have hsfE : IsGarlingSplittingFieldExtension (ZMod 5) E f5 := by
      rw [isGarlingSplittingFieldExtension_iff]
      refine ⟨?_, ?_⟩
      · rw [hfac5]
        exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (β5 i)
      · have hroot_mem : α ∈ f5.rootSet E := by
          rw [Polynomial.mem_rootSet_of_ne hf5_mon.ne_zero, Polynomial.aeval_def,
            ← Polynomial.eval_map, hfac5, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) (by simp [β5])
        rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top (f := f5)]
        exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hroot_mem)
    -- Exhibit `σ_alg : E ≃ₐ[ZMod 5] E` sending `α ↦ 2 * α` of order `4`.
    have h2α_root : Polynomial.eval₂ (Algebra.ofId (ZMod 5) E).toRingHom (2 * α) f5 = 0 := by
      change Polynomial.aeval (2 * α) f5 = 0
      simp only [f5, map_add, map_pow, Polynomial.aeval_X, map_ofNat]
      calc (2 * α) ^ 4 + 2 = (3 * (5 : E) + 1) * α ^ 4 + 2 := by ring
        _ = α ^ 4 + 2 := by rw [hchar5]; ring
        _ = 0 := by rw [hα_pow]; ring
    have h3α_root : Polynomial.eval₂ (Algebra.ofId (ZMod 5) E).toRingHom (3 * α) f5 = 0 := by
      change Polynomial.aeval (3 * α) f5 = 0
      simp only [f5, map_add, map_pow, Polynomial.aeval_X, map_ofNat]
      calc (3 * α) ^ 4 + 2 = (16 * (5 : E) + 1) * α ^ 4 + 2 := by ring
        _ = α ^ 4 + 2 := by rw [hchar5]; ring
        _ = 0 := by rw [hα_pow]; ring
    let σ_hom : E →ₐ[ZMod 5] E := AdjoinRoot.liftAlgHom f5 (Algebra.ofId (ZMod 5) E) (2 * α) h2α_root
    let τ_hom : E →ₐ[ZMod 5] E := AdjoinRoot.liftAlgHom f5 (Algebra.ofId (ZMod 5) E) (3 * α) h3α_root
    have h6_eq_1 : (6 : E) = 1 := by
      calc (6 : E) = (5 : E) + 1 := by norm_num
        _ = 1 := by rw [hchar5, zero_add]
    have hστ : τ_hom.comp σ_hom = AlgHom.id (ZMod 5) E := by
      apply AdjoinRoot.algHom_ext
      change τ_hom (σ_hom α) = α
      have h1 : σ_hom α = 2 * α := AdjoinRoot.liftAlgHom_root _ _ _ _
      have h2 : τ_hom α = 3 * α := AdjoinRoot.liftAlgHom_root _ _ _ _
      rw [h1, map_mul, map_ofNat, h2, ← mul_assoc]
      norm_num
      rw [h6_eq_1, one_mul]
    have hτστ : σ_hom.comp τ_hom = AlgHom.id (ZMod 5) E := by
      apply AdjoinRoot.algHom_ext
      change σ_hom (τ_hom α) = α
      have h1 : σ_hom α = 2 * α := AdjoinRoot.liftAlgHom_root _ _ _ _
      have h2 : τ_hom α = 3 * α := AdjoinRoot.liftAlgHom_root _ _ _ _
      rw [h2, map_mul, map_ofNat, h1, ← mul_assoc]
      norm_num
      rw [h6_eq_1, one_mul]
    let σ_alg : E ≃ₐ[ZMod 5] E := AlgEquiv.ofAlgHom σ_hom τ_hom hτστ hστ
    have hperf5 : IsGarlingPerfectField (ZMod 5) :=
      (isGarlingPerfectField_iff_perfectField (ZMod 5)).mpr inferInstance
    have hcardGE : Nat.card (GarlingPolyGaloisGroup (ZMod 5) E f5) = 4 :=
      (theorem_11_5_perfect hperf5 hsfE).2.1.trans hfinE
    have hcardAlg : Nat.card (E ≃ₐ[ZMod 5] E) = 4 := hcardGE
    let _ : Finite (E ≃ₐ[ZMod 5] E) := Nat.finite_of_card_ne_zero (by rw [hcardAlg]; decide)
    have hα_ne0 : α ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by decide : (4 : ℕ) ≠ 0)] at hα_pow
      have h2_0 : (2 : E) = 0 := by linear_combination hα_pow
      have h1_0 : (1 : E) = 0 := by linear_combination hchar5 - 2 * h2_0
      exact one_ne_zero h1_0
    have hσ_apply : σ_alg α = 2 * α :=
      AdjoinRoot.liftAlgHom_root f5 (Algebra.ofId (ZMod 5) E) (2 * α) h2α_root
    have hσ_sq_ne1 : σ_alg ^ 2 ≠ 1 := by
      intro hsq1
      have heval : (σ_alg ^ 2) α = α := by rw [hsq1]; rfl
      have hlhs : (σ_alg ^ 2) α = 4 * α := by
        rw [sq, AlgEquiv.mul_apply, hσ_apply, map_mul, map_ofNat, hσ_apply]
        ring
      rw [hlhs] at heval
      have h3α : (3 : E) * α = 0 := by linear_combination heval
      have hα0 : α = 0 := by
        calc α = 1 * α := (one_mul α).symm
          _ = ((6 : E) - (5 : E)) * α := by norm_num
          _ = 2 * ((3 : E) * α) - (5 : E) * α := by ring
          _ = 0 := by rw [h3α, hchar5]; ring
      exact hα_ne0 hα0
    have hord_σ : orderOf σ_alg = 4 := by
      have hdvd : orderOf σ_alg ∣ 4 := by
        have hd0 := orderOf_dvd_natCard σ_alg
        rwa [hcardAlg] at hd0
      have hpos : 0 < orderOf σ_alg := orderOf_pos σ_alg
      have hle : orderOf σ_alg ≤ 4 := Nat.le_of_dvd (by decide) hdvd
      interval_cases ho : orderOf σ_alg
      · exfalso
        have h1 := orderOf_eq_one_iff.mp ho
        exact hσ_sq_ne1 (by rw [h1, one_pow])
      · exfalso
        exact hσ_sq_ne1 (ho ▸ pow_orderOf_eq_one σ_alg)
      · exfalso; norm_num at hdvd
      · rfl
    obtain ⟨eGE⟩ := mulEquivMultiplicativeZModOfOrderOfEqNatCard σ_alg hord_σ hcardAlg
    refine ⟨hf5_irr, ⟨E, inferInstance, inferInstance, hsfE, hfinE⟩, fun L _ _ hsfL => ?_⟩
    obtain ⟨eLE⟩ := splitting_field_unique_up_to_algEquiv hsfL hsfE
    have hfinL : Module.finrank (ZMod 5) L = 4 := eLE.toLinearEquiv.finrank_eq.trans hfinE
    have hcardGL : Nat.card (GarlingPolyGaloisGroup (ZMod 5) L f5) = 4 :=
      (theorem_11_5_perfect hperf5 hsfL).2.1.trans hfinL
    obtain ⟨eGL_GE⟩ := garlingPolyGaloisGroup_independent_of_splittingField hsfL hsfE
    exact ⟨hfinL, hcardGL, ⟨eGL_GE.trans eGE⟩⟩
  exact ⟨ha, hb, hc⟩

/-! ## §11.3 An example (printed pp. 96–97, PDF pp. 104–105) -/

/-- **§11.3 Unnumbered Prose Lemma** (printed p. 96 / PDF p. 104):
*"First we need a lemma: if `p` is prime and `G` is a transitive subgroup of `Σ_X` (where
`|X| = p`) which contains a transposition, then `G = Σ_X`."*

Proved directly via Garling's p. 96 equivalence relation `x ~ y ↔ x = y ∨ (x y) ∈ G`,
equal equivalence-class sizes under transitivity of `G`, primality of `|X|`, and generation of
`Equiv.Perm X` by transpositions (`Equiv.Perm.closure_isSwap`). -/
theorem transitive_subgroup_eq_top_of_prime_of_exists_swap
    {X : Type*} [Fintype X] [DecidableEq X] (hp : Nat.Prime (Fintype.card X))
    {G : Subgroup (Equiv.Perm X)} (htr : SubgroupActsTransitively G)
    (hswap : ∃ a b : X, a ≠ b ∧ Equiv.swap a b ∈ G) :
    G = ⊤ := by
  obtain ⟨a₀, b₀, hab₀, hswap₀⟩ := hswap
  let rel : X → X → Prop := fun x y => x = y ∨ Equiv.swap x y ∈ G
  have hrel_refl : ∀ x : X, rel x x := fun _ => Or.inl rfl
  have hrel_symm : ∀ {x y : X}, rel x y → rel y x := by
    intro x y hxy
    rcases hxy with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr (Equiv.swap_comm x y ▸ hs)
  have hrel_trans : ∀ {x y z : X}, rel x y → rel y z → rel x z := by
    intro x y z hxy hyz
    rcases hxy with rfl | hs_xy
    · exact hyz
    · rcases hyz with rfl | hs_yz
      · exact Or.inr hs_xy
      · by_cases hxz : x = z
        · exact Or.inl hxz
        · by_cases hxy_ne : x = y
          · subst hxy_ne; exact Or.inr hs_yz
          · by_cases hyz_ne : y = z
            · subst hyz_ne; exact Or.inr hs_xy
            · -- Garling's identity `(x y)(y z)(x y) = (x z)` for distinct `x, y, z`.
              have hconj_swap :
                  Equiv.swap x y * Equiv.swap y z * Equiv.swap x y = Equiv.swap x z := by
                ext w
                change Equiv.swap x y (Equiv.swap y z (Equiv.swap x y w)) = Equiv.swap x z w
                by_cases hwx : w = x
                · subst hwx
                  rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left,
                    Equiv.swap_apply_of_ne_of_ne (Ne.symm hxz) (Ne.symm hyz_ne)]
                · by_cases hwy : w = y
                  · subst hwy
                    rw [Equiv.swap_apply_right,
                      Equiv.swap_apply_of_ne_of_ne hxy_ne hxz,
                      Equiv.swap_apply_left,
                      Equiv.swap_apply_of_ne_of_ne (Ne.symm hxy_ne) hyz_ne]
                  · by_cases hwz : w = z
                    · subst hwz
                      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hxz) (Ne.symm hyz_ne),
                        Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right]
                    · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy,
                        Equiv.swap_apply_of_ne_of_ne hwy hwz,
                        Equiv.swap_apply_of_ne_of_ne hwx hwy,
                        Equiv.swap_apply_of_ne_of_ne hwx hwz]
              exact Or.inr (hconj_swap ▸ G.mul_mem (G.mul_mem hs_xy hs_yz) hs_xy)
  have hrel_smul : ∀ σ ∈ G, ∀ x y : X, rel x y → rel (σ x) (σ y) := by
    intro σ hσ x y hxy
    rcases hxy with rfl | hs
    · exact Or.inl rfl
    · right
      have hconj : σ * Equiv.swap x y * σ⁻¹ = Equiv.swap (σ x) (σ y) := by
        ext w
        change σ (Equiv.swap x y (σ.symm w)) = Equiv.swap (σ x) (σ y) w
        by_cases hwx : w = σ x
        · subst hwx
          rw [σ.symm_apply_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
        · by_cases hwy : w = σ y
          · subst hwy
            rw [σ.symm_apply_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
          · have h1 : σ.symm w ≠ x := fun h => hwx (by rw [← h, σ.apply_symm_apply])
            have h2 : σ.symm w ≠ y := fun h => hwy (by rw [← h, σ.apply_symm_apply])
            rw [Equiv.swap_apply_of_ne_of_ne h1 h2, σ.apply_symm_apply,
              Equiv.swap_apply_of_ne_of_ne hwx hwy]
      exact hconj ▸ G.mul_mem (G.mul_mem hσ hs) (G.inv_mem hσ)
  let s : Setoid X := ⟨rel, ⟨hrel_refl, hrel_symm, hrel_trans⟩⟩
  classical
  let cls : X → Finset X := fun x => Finset.univ.filter (fun y => rel x y)
  have hcls_card_eq : ∀ x : X, (cls x).card = (cls a₀).card := by
    intro x
    obtain ⟨σ, hσG, hσx⟩ := htr a₀ x
    symm
    refine Finset.card_bij (fun y _ => σ y) (fun y hy => ?_) (fun y₁ _ y₂ _ h => σ.injective h)
      (fun z hz => ?_)
    · rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, hσx ▸ hrel_smul σ hσG a₀ y hy.2⟩
    · rw [Finset.mem_filter] at hz
      refine ⟨σ⁻¹ z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, σ.apply_symm_apply z⟩
      have himg := hrel_smul σ⁻¹ (G.inv_mem hσG) x z hz.2
      have hinvx : σ⁻¹ x = a₀ := by rw [← hσx]; exact σ.symm_apply_apply a₀
      rwa [hinvx] at himg
  -- Partition `X` into equivalence classes of `s`, each of size `(cls a₀).card`.
  have hdvd_card : (cls a₀).card ∣ Fintype.card X := by
    let π : X → Quotient s := Quotient.mk s
    have hfiber_card : ∀ q : Quotient s, Nat.card {y : X // π y = q} = (cls a₀).card := by
      refine Quotient.ind fun x => ?_
      have heq_set : ({y : X | π y = π x} : Set X) = (cls x : Set X) := by
        ext y
        change (π y = π x) ↔ y ∈ (cls x : Set X)
        simp only [Finset.mem_coe, cls, Finset.mem_filter, Finset.mem_univ,
          true_and, π, Quotient.eq]
        exact ⟨fun h => hrel_symm h, fun h => hrel_symm h⟩
      calc Nat.card {y : X // π y = π x}
          = Nat.card ({y : X | π y = π x} : Set X) := rfl
        _ = (cls x).card := by rw [heq_set, Nat.card_coe_set_eq, Set.ncard_coe_finset]
        _ = (cls a₀).card := hcls_card_eq x
    have hsum : Fintype.card X = Nat.card (Quotient s) * (cls a₀).card := by
      rw [← Nat.card_eq_fintype_card,
        ← Nat.card_congr (Equiv.sigmaFiberEquiv π)]
      let _ : Fintype (Quotient s) := Fintype.ofFinite (Quotient s)
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sigma]
      have hfib_fin : ∀ q : Quotient s, Fintype.card {y : X // π y = q} = (cls a₀).card :=
        fun q => (Nat.card_eq_fintype_card (α := {y : X // π y = q})).symm.trans (hfiber_card q)
      simp [hfib_fin]
    exact ⟨Nat.card (Quotient s), by linarith⟩
  have hcard_ge2 : 2 ≤ (cls a₀).card := by
    have ha_mem : a₀ ∈ cls a₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
    have hb_mem : b₀ ∈ cls a₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hswap₀⟩
    exact Finset.one_lt_card.mpr ⟨a₀, ha_mem, b₀, hb_mem, hab₀⟩
  have hcard_all : (cls a₀).card = Fintype.card X := by
    rcases hp.eq_one_or_self_of_dvd (cls a₀).card hdvd_card with h1 | hself
    · omega
    · exact hself
  have hcls_univ : cls a₀ = Finset.univ := Finset.eq_univ_of_card (cls a₀) hcard_all
  have hall_rel : ∀ x y : X, rel x y := by
    intro x y
    have hx : rel a₀ x := (Finset.mem_filter.mp (hcls_univ ▸ Finset.mem_univ x)).2
    have hy : rel a₀ y := (Finset.mem_filter.mp (hcls_univ ▸ Finset.mem_univ y)).2
    exact hrel_trans (hrel_symm hx) hy
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  rcases hall_rel x y with heq | hmem
  · exact (hxy heq).elim
  · exact hmem

/-- `IsSwap` wrapper for **§11.3's prose lemma**: a transitive subgroup of `Equiv.Perm X` (with
`(Fintype.card X).Prime`) containing at least one transposition (`Equiv.Perm.IsSwap`) is `⊤`. -/
theorem transitive_subgroup_eq_top_of_prime_of_exists_isSwap
    {X : Type*} [Fintype X] [DecidableEq X] (hp : Nat.Prime (Fintype.card X))
    {G : Subgroup (Equiv.Perm X)} (htr : SubgroupActsTransitively G)
    (hswap : ∃ τ ∈ G, τ.IsSwap) :
    G = ⊤ := by
  obtain ⟨τ, hτG, a, b, hab, rfl⟩ := hswap
  exact transitive_subgroup_eq_top_of_prime_of_exists_swap hp htr ⟨a, b, hab, hτG⟩

/-- Explicit complex conjugation `z ↦ ⟨z.re, -z.im⟩` as a `ℚ`-algebra automorphism `ℂ ≃ₐ[ℚ] ℂ`. -/
def complexConjAlgEquiv : ℂ ≃ₐ[ℚ] ℂ where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := Complex.ext rfl (neg_neg z.im)
  right_inv z := Complex.ext rfl (neg_neg z.im)
  map_mul' x y := Complex.ext (by simp only [Complex.mul_re]; ring)
    (by simp only [Complex.mul_im]; ring)
  map_add' x y := Complex.ext rfl (neg_add x.im y.im)
  commutes' q := Complex.ext (by simp) (by simp)

@[simp]
theorem complexConjAlgEquiv_re (z : ℂ) : (complexConjAlgEquiv z).re = z.re :=
  rfl

@[simp]
theorem complexConjAlgEquiv_im (z : ℂ) : (complexConjAlgEquiv z).im = -z.im :=
  rfl

theorem complexConjAlgEquiv_eq_self_iff (z : ℂ) :
    complexConjAlgEquiv z = z ↔ z.im = 0 := by
  rw [Complex.ext_iff]
  simp only [complexConjAlgEquiv_re, complexConjAlgEquiv_im, true_and]
  constructor <;> intro h <;> linarith

/-- Partition of the complex roots of any separable polynomial `f ∈ ℚ[X]` into real roots
(`{x : ℝ | aeval x f = 0}`) and non-real complex roots (`{z : ℂ | aeval z f = 0 ∧ z.im ≠ 0}`). -/
theorem separable_rat_roots_partition {f : ℚ[X]} (hsep : f.Separable) :
    IsGarlingSplittingFieldExtension ℚ (IntermediateField.adjoin ℚ (garlingRootSet ℚ ℂ f)) f ∧
    (garlingRootSet ℚ ℂ f).ncard = f.natDegree ∧
    {x : ℝ | Polynomial.aeval x f = 0}.Finite ∧
    {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.Finite ∧
    {x : ℝ | Polynomial.aeval x f = 0}.ncard +
      {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = f.natDegree := by
  classical
  have hf0 : f ≠ 0 := hsep.ne_zero
  have hfC_splits : (f.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  have hrootSet_eq : garlingRootSet ℚ ℂ f = f.rootSet ℂ := by
    ext z
    change Polynomial.aeval z f = 0 ↔ z ∈ f.rootSet ℂ
    rw [Polynomial.mem_rootSet_of_ne hf0]
  have hsfE : IsGarlingSplittingFieldExtension ℚ
      (IntermediateField.adjoin ℚ (garlingRootSet ℚ ℂ f)) f := by
    rw [isGarlingSplittingFieldExtension_iff, hrootSet_eq]
    exact IntermediateField.adjoin_rootSet_isSplittingField hfC_splits
  let fC : ℂ[X] := f.map (algebraMap ℚ ℂ)
  have hfC_sep : fC.Separable := hsep.map
  have hfC0 : fC ≠ 0 := hfC_sep.ne_zero
  have hset_C : garlingRootSet ℚ ℂ f = (fC.roots.toFinset : Set ℂ) := by
    ext z
    change Polynomial.aeval z f = 0 ↔ z ∈ (fC.roots.toFinset : Set ℂ)
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hfC0,
      Polynomial.IsRoot.def, fC, Polynomial.eval_map_algebraMap]
  have hncard_C : (garlingRootSet ℚ ℂ f).ncard = f.natDegree := by
    rw [hset_C, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hfC_sep),
      ← hfC_splits.natDegree_eq_card_roots, Polynomial.natDegree_map]
  have hfin_C : (garlingRootSet ℚ ℂ f).Finite := by
    rw [hset_C]
    exact Finset.finite_toSet _
  let C_real : Set ℂ := {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im = 0}
  let C_nonreal : Set ℂ := {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}
  have hC_real_fin : C_real.Finite := hfin_C.subset fun z hz => hz.1
  have hC_nonreal_fin : C_nonreal.Finite := hfin_C.subset fun z hz => hz.1
  have hunion : C_real ∪ C_nonreal = garlingRootSet ℚ ℂ f := by
    ext z
    change (Polynomial.aeval z f = 0 ∧ z.im = 0) ∨ (Polynomial.aeval z f = 0 ∧ z.im ≠ 0) ↔
      Polynomial.aeval z f = 0
    by_cases him : z.im = 0 <;> simp [him]
  have hdisj : Disjoint C_real C_nonreal :=
    Set.disjoint_left.mpr fun z hz1 hz2 => hz2.2 hz1.2
  let R_set : Set ℝ := {x : ℝ | Polynomial.aeval x f = 0}
  have himg_eq : Complex.ofReal '' R_set = C_real := by
    ext z
    simp only [Set.mem_image, R_set, C_real]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have haev : Polynomial.aeval (x : ℂ) f = (Polynomial.aeval x f : ℂ) :=
        Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) x f
      have hx0 : Polynomial.aeval x f = 0 := hx
      exact ⟨by rw [haev, hx0, Complex.ofReal_zero], Complex.ofReal_im x⟩
    · rintro ⟨hz_aev, hz_im⟩
      refine ⟨z.re, ?_, Complex.ext rfl hz_im.symm⟩
      have hz_eq : (z.re : ℂ) = z := Complex.ext rfl hz_im.symm
      have haev : (Polynomial.aeval z.re f : ℂ) = Polynomial.aeval (z.re : ℂ) f :=
        (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) z.re f).symm
      apply Complex.ofReal_injective
      rw [Complex.ofReal_zero, haev, hz_eq, hz_aev]
  have hR_fin : R_set.Finite := by
    have hpre : R_set = Complex.ofReal ⁻¹' C_real := by
      rw [← himg_eq, Set.preimage_image_eq _ Complex.ofReal_injective]
    rw [hpre]
    exact hC_real_fin.preimage Complex.ofReal_injective.injOn
  have hR_ncard : R_set.ncard = C_real.ncard := by
    rw [← himg_eq, Set.ncard_image_of_injective R_set Complex.ofReal_injective]
  have hsum_ncard : R_set.ncard + C_nonreal.ncard = f.natDegree := by
    rw [hR_ncard, ← Set.ncard_union_eq hdisj hC_real_fin hC_nonreal_fin, hunion, hncard_C]
  exact ⟨hsfE, hncard_C, hR_fin, hC_nonreal_fin, hsum_ncard⟩

/-- **Theorem 11.7** (§11.3, printed p. 96 / PDF p. 104):
*"Suppose that `f ∈ ℚ[x]` is irreducible and has prime degree `p`. If `f` has exactly `p - 2` real
roots and `2` complex roots in `ℂ` then the Galois group `Γ(f)` of `f` over `ℚ` is `Σ_p`."*

Here `"complex roots in ℂ"` means non-real complex roots (`z.im ≠ 0`), as Garling's proof on p. 96
explicitly uses (*"complex conjugation restricts to an element `τ` of `Γ(f)` which leaves each of
the real roots invariant, and interchanges the complex roots; `τ` acts as a transposition on `R`"*).
For **every** splitting field extension `L : ℚ` of `f`, the canonical root-permutation homomorphism
`garlingRootPermHom ℚ L f : Γ_ℚ(f) →* Equiv.Perm (garlingRootSet ℚ L f)` is bijective and
`Γ_ℚ(f) ≃* Equiv.Perm (Fin p)` (`|Γ_ℚ(f)| = [L : ℚ] = p!`). -/
theorem theorem_11_7 {f : ℚ[X]} {p : ℕ}
    (hirr : Irreducible f) (hp : Nat.Prime p) (hdeg : f.natDegree = p)
    (_hreal : {x : ℝ | Polynomial.aeval x f = 0}.ncard = p - 2)
    (hcomp : {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2)
    (L : Type*) [Field L] [Algebra ℚ L]
    (hsfL : IsGarlingSplittingFieldExtension ℚ L f) :
    Function.Bijective (garlingRootPermHom ℚ L f) ∧
    Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Equiv.Perm (Fin p)) ∧
    Nat.card (GarlingPolyGaloisGroup ℚ L f) = p.factorial ∧
    Module.finrank ℚ L = p.factorial := by
  classical
  have hsep : f.Separable := hirr.separable
  obtain ⟨hsfE, hncard_C, _, hC_nonreal_fin, _⟩ := separable_rat_roots_partition hsep
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (garlingRootSet ℚ ℂ f)
  -- 1. Restrict complex conjugation to `E` to obtain a transposition on `garlingRootSet ℚ E f`.
  have hconj_roots : ∀ z ∈ garlingRootSet ℚ ℂ f, complexConjAlgEquiv z ∈ garlingRootSet ℚ ℂ f := by
    intro z hz
    change Polynomial.aeval (complexConjAlgEquiv.toAlgHom z) f = 0
    have hz0 : Polynomial.aeval z f = 0 := hz
    rw [Polynomial.aeval_algHom_apply complexConjAlgEquiv.toAlgHom z f, hz0, map_zero]
  have hconj_memE : ∀ z ∈ E, complexConjAlgEquiv z ∈ E := by
    have hle : E ≤ E.comap complexConjAlgEquiv.toAlgHom := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      change complexConjAlgEquiv z ∈ E
      exact IntermediateField.subset_adjoin ℚ (garlingRootSet ℚ ℂ f) (hconj_roots z hz)
    intro z hz
    exact hle hz
  let τ : E ≃ₐ[ℚ] E :=
    { toFun := fun x => ⟨complexConjAlgEquiv x.1, hconj_memE x.1 x.2⟩
      invFun := fun x => ⟨complexConjAlgEquiv x.1, hconj_memE x.1 x.2⟩
      left_inv := fun x => Subtype.ext (complexConjAlgEquiv.left_inv x.1)
      right_inv := fun x => Subtype.ext (complexConjAlgEquiv.left_inv x.1)
      map_mul' := fun x y => Subtype.ext (map_mul complexConjAlgEquiv x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add complexConjAlgEquiv x.1 y.1)
      commutes' := fun q => Subtype.ext (complexConjAlgEquiv.commutes q) }
  -- Extract the `2` distinct non-real roots `z₁ ≠ z₂` in `ℂ`.
  let S_nr : Finset ℂ := hC_nonreal_fin.toFinset
  have hS_nr_card : S_nr.card = 2 := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    exact hcomp
  obtain ⟨z₁, z₂, hz12_ne, hS_nr_eq⟩ := Finset.card_eq_two.mp hS_nr_card
  have hmem_nr : ∀ z : ℂ, (Polynomial.aeval z f = 0 ∧ z.im ≠ 0) ↔ z = z₁ ∨ z = z₂ := by
    intro z
    have h1 : (Polynomial.aeval z f = 0 ∧ z.im ≠ 0) ↔ z ∈ S_nr :=
      (hC_nonreal_fin.mem_toFinset).symm
    rw [h1, hS_nr_eq, Finset.mem_insert, Finset.mem_singleton]
  have hz₁_nr : Polynomial.aeval z₁ f = 0 ∧ z₁.im ≠ 0 := (hmem_nr z₁).mpr (Or.inl rfl)
  have hz₂_nr : Polynomial.aeval z₂ f = 0 ∧ z₂.im ≠ 0 := (hmem_nr z₂).mpr (Or.inr rfl)
  have hconj_z₁ : complexConjAlgEquiv z₁ = z₂ := by
    have haev : Polynomial.aeval (complexConjAlgEquiv z₁) f = 0 := hconj_roots z₁ hz₁_nr.1
    have him : (complexConjAlgEquiv z₁).im ≠ 0 := by
      rw [complexConjAlgEquiv_im, neg_ne_zero]
      exact hz₁_nr.2
    rcases (hmem_nr (complexConjAlgEquiv z₁)).mp ⟨haev, him⟩ with hself | heq2
    · exact (hz₁_nr.2 ((complexConjAlgEquiv_eq_self_iff z₁).mp hself)).elim
    · exact heq2
  have hconj_z₂ : complexConjAlgEquiv z₂ = z₁ := by
    rw [← hconj_z₁]
    exact complexConjAlgEquiv.left_inv z₁
  -- Lift `z₁, z₂` to `r₁, r₂ : garlingRootSet ℚ E f`.
  have haeval_E_iff : ∀ w : E, Polynomial.aeval w f = 0 ↔ Polynomial.aeval w.1 f = 0 := by
    intro w
    have h : Polynomial.aeval (E.val w) f = E.val (Polynomial.aeval w f) :=
      Polynomial.aeval_algHom_apply E.val w f
    exact ⟨fun hw => by change Polynomial.aeval (E.val w) f = 0; rw [h, hw, map_zero],
      fun hw => Subtype.ext (by change E.val (Polynomial.aeval w f) = 0; rw [← h]; exact hw)⟩
  let r₁ : garlingRootSet ℚ E f :=
    ⟨⟨z₁, IntermediateField.subset_adjoin ℚ (garlingRootSet ℚ ℂ f) hz₁_nr.1⟩,
      (haeval_E_iff _).mpr hz₁_nr.1⟩
  let r₂ : garlingRootSet ℚ E f :=
    ⟨⟨z₂, IntermediateField.subset_adjoin ℚ (garlingRootSet ℚ ℂ f) hz₂_nr.1⟩,
      (haeval_E_iff _).mpr hz₂_nr.1⟩
  have hr12_ne : r₁ ≠ r₂ := fun h => hz12_ne (congrArg (fun u : garlingRootSet ℚ E f => u.1.1) h)
  have hτ_swap : garlingRootPermHom ℚ E f τ = Equiv.swap r₁ r₂ := by
    ext r
    change complexConjAlgEquiv r.1.1 = (Equiv.swap r₁ r₂ r).1.1
    have hr_aev : Polynomial.aeval r.1.1 f = 0 := (haeval_E_iff r.1).mp r.2
    by_cases him0 : r.1.1.im = 0
    · have hr_ne1 : r ≠ r₁ := fun h => hz₁_nr.2 (by subst h; exact him0)
      have hr_ne2 : r ≠ r₂ := fun h => hz₂_nr.2 (by subst h; exact him0)
      rw [Equiv.swap_apply_of_ne_of_ne hr_ne1 hr_ne2,
        (complexConjAlgEquiv_eq_self_iff r.1.1).mpr him0]
    · rcases (hmem_nr r.1.1).mp ⟨hr_aev, him0⟩ with heq1 | heq2
      · have hr_eq1 : r = r₁ := Subtype.ext (Subtype.ext heq1)
        rw [hr_eq1, Equiv.swap_apply_left]
        exact hconj_z₁
      · have hr_eq2 : r = r₂ := Subtype.ext (Subtype.ext heq2)
        rw [hr_eq2, Equiv.swap_apply_right]
        exact hconj_z₂
  -- 2. Apply §11.3's prose lemma to `(garlingRootPermHom ℚ E f).range`!
  have hncard_RE : (garlingRootSet ℚ E f).ncard = p :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsfE).trans hdeg
  have hfin_RE : (garlingRootSet ℚ E f).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncard_RE]; exact hp.ne_zero)
  let _ : Fintype (garlingRootSet ℚ E f) := hfin_RE.fintype
  have hfcard_RE : Fintype.card (garlingRootSet ℚ E f) = p := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hncard_RE]
  have htr_E : SubgroupActsTransitively (garlingRootPermHom ℚ E f).range :=
    irreducible_imp_galoisGroup_actsTransitively hirr hsfE
  have hrange_top_E : (garlingRootPermHom ℚ E f).range = ⊤ :=
    transitive_subgroup_eq_top_of_prime_of_exists_swap (hfcard_RE.symm ▸ hp) htr_E
      ⟨r₁, r₂, hr12_ne, ⟨τ, hτ_swap⟩⟩
  have hbij_E : Function.Bijective (garlingRootPermHom ℚ E f) := by
    refine ⟨theorem_11_6 hsfE, fun π => ?_⟩
    have hmem : π ∈ (garlingRootPermHom ℚ E f).range := by rw [hrange_top_E]; trivial
    exact hmem
  -- 3. Transport bijectivity from `E` to the arbitrary splitting field `L`.
  obtain ⟨φ⟩ := splitting_field_unique_up_to_algEquiv hsfL hsfE
  let eRL_RE : garlingRootSet ℚ L f ≃ garlingRootSet ℚ E f :=
    { toFun := fun r => ⟨φ r.1, by
        change Polynomial.aeval (φ.toAlgHom r.1) f = 0
        have hr0 : Polynomial.aeval r.1 f = 0 := r.2
        rw [Polynomial.aeval_algHom_apply φ.toAlgHom r.1 f, hr0, map_zero]⟩
      invFun := fun r => ⟨φ.symm r.1, by
        change Polynomial.aeval (φ.symm.toAlgHom r.1) f = 0
        have hr0 : Polynomial.aeval r.1 f = 0 := r.2
        rw [Polynomial.aeval_algHom_apply φ.symm.toAlgHom r.1 f, hr0, map_zero]⟩
      left_inv := fun r => Subtype.ext (φ.symm_apply_apply r.1)
      right_inv := fun r => Subtype.ext (φ.apply_symm_apply r.1) }
  let conjAut : (L ≃ₐ[ℚ] L) ≃* (E ≃ₐ[ℚ] E) :=
    { toFun := fun σ => φ.symm.trans (σ.trans φ)
      invFun := fun σ' => φ.trans (σ'.trans φ.symm)
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ' => by ext x; simp
      map_mul' := fun σ₁ σ₂ => by ext x; simp [AlgEquiv.mul_apply] }
  have hcomm_perm : ∀ σ : GarlingPolyGaloisGroup ℚ L f,
      Equiv.permCongrHom eRL_RE (garlingRootPermHom ℚ L f σ) =
        garlingRootPermHom ℚ E f (conjAut σ) := by
    intro σ
    ext r
    rfl
  have hbij_L : Function.Bijective (garlingRootPermHom ℚ L f) := by
    refine ⟨theorem_11_6 hsfL, fun π => ?_⟩
    obtain ⟨σE, hσE⟩ := hbij_E.2 (Equiv.permCongrHom eRL_RE π)
    refine ⟨conjAut.symm σE, (Equiv.permCongrHom eRL_RE).injective ?_⟩
    rw [hcomm_perm, conjAut.apply_symm_apply, hσE]
  let _ : Fintype (garlingRootSet ℚ L f) := Fintype.ofEquiv _ eRL_RE.symm
  have hfcard_RL : Fintype.card (garlingRootSet ℚ L f) = p :=
    (Fintype.card_congr eRL_RE).trans hfcard_RE
  let eFinP : garlingRootSet ℚ L f ≃ Fin p := Fintype.equivFinOfCardEq hfcard_RL
  let isoSp : GarlingPolyGaloisGroup ℚ L f ≃* Equiv.Perm (Fin p) :=
    (MulEquiv.ofBijective (garlingRootPermHom ℚ L f) hbij_L).trans (Equiv.permCongrHom eFinP)
  have hcardG : Nat.card (GarlingPolyGaloisGroup ℚ L f) = p.factorial := by
    rw [Nat.card_congr isoSp.toEquiv, Nat.card_perm, Nat.card_fin]
  have hperfQ : IsGarlingPerfectField ℚ :=
    (isGarlingPerfectField_iff_perfectField ℚ).mpr inferInstance
  have hfinL : Module.finrank ℚ L = p.factorial :=
    (theorem_11_5_perfect hperfQ hsfL).2.1.symm.trans hcardG
  exact ⟨hbij_L, ⟨isoSp⟩, hcardG, hfinL⟩

/-- Strengthening of **Theorem 11.7**: since `f ∈ ℚ[X]` of prime degree `p` has `p` distinct roots
in `ℂ`, `{x : ℝ | aeval x f = 0}.ncard = p - 2` automatically forces
`{z : ℂ | aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2`. -/
theorem theorem_11_7_of_real_roots {f : ℚ[X]} {p : ℕ}
    (hirr : Irreducible f) (hp : Nat.Prime p) (hdeg : f.natDegree = p)
    (hreal : {x : ℝ | Polynomial.aeval x f = 0}.ncard = p - 2)
    (L : Type*) [Field L] [Algebra ℚ L]
    (hsfL : IsGarlingSplittingFieldExtension ℚ L f) :
    {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2 ∧
    Function.Bijective (garlingRootPermHom ℚ L f) ∧
    Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Equiv.Perm (Fin p)) := by
  obtain ⟨_, _, _, _, hsum⟩ := separable_rat_roots_partition hirr.separable
  have hp2 : 2 ≤ p := hp.two_le
  have hcomp : {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2 := by omega
  obtain ⟨hbij, hiso, _, _⟩ := theorem_11_7 hirr hp hdeg hreal hcomp L hsfL
  exact ⟨hcomp, hbij, hiso⟩

/-! ### §11.3 Real Root-Counting Helpers, Quintic Example (`x⁵ - 4x + 2`), and Exercise 11.8 -/

/-- Strict open-interval Intermediate Value Theorem for polynomials `P ∈ ℝ[X]`:
if `a < b` and `P.eval a * P.eval b < 0`, there exists `c ∈ (a, b)` with `P.eval c = 0`. -/
theorem exists_Ioo_root_of_mul_neg {P : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hmul : P.eval a * P.eval b < 0) :
    ∃ c ∈ Set.Ioo a b, P.eval c = 0 := by
  have hne_a : P.eval a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hmul; exact lt_irrefl 0 hmul
  have hne_b : P.eval b ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmul; exact lt_irrefl 0 hmul
  rcases mul_neg_iff.mp hmul with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · have hcont : ContinuousOn (fun x => (-P).eval x) (Set.Icc a b) :=
      (-P).continuous.continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc ((-P).eval a) ((-P).eval b) := by
      simp only [Polynomial.eval_neg, Set.mem_Icc]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨c, hcIcc, hc0⟩ := intermediate_value_Icc hab.le hcont h0_mem
    have hPc : P.eval c = 0 := neg_eq_zero.mp (by simpa using hc0)
    have hca : a < c := lt_of_le_of_ne hcIcc.1 (fun h => hne_a (h ▸ hPc))
    have hcb : c < b := lt_of_le_of_ne hcIcc.2 (fun h => hne_b (h ▸ hPc))
    exact ⟨c, ⟨hca, hcb⟩, hPc⟩
  · have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) := P.continuous.continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc (P.eval a) (P.eval b) := ⟨hna.le, hpb.le⟩
    obtain ⟨c, hcIcc, hPc⟩ := intermediate_value_Icc hab.le hcont h0_mem
    have hca : a < c := lt_of_le_of_ne hcIcc.1 (fun h => hne_a (h ▸ hPc))
    have hcb : c < b := lt_of_le_of_ne hcIcc.2 (fun h => hne_b (h ▸ hPc))
    exact ⟨c, ⟨hca, hcb⟩, hPc⟩

/-- Rolle's-theorem bound on real roots of a non-zero polynomial `P ∈ ℝ[X]`:
if `Polynomial.derivative P` has at most `m` real roots, then `P` has at most `m + 1` real roots. -/
theorem ncard_real_roots_le_succ_of_deriv_bound {P : ℝ[X]} (hP0 : P ≠ 0) {m : ℕ}
    (hderiv_fin : {x : ℝ | (Polynomial.derivative P).eval x = 0}.Finite)
    (hderiv_le : {x : ℝ | (Polynomial.derivative P).eval x = 0}.ncard ≤ m) :
    {x : ℝ | P.eval x = 0}.ncard ≤ m + 1 := by
  classical
  let S : Finset ℝ := P.roots.toFinset
  have hS_eq : {x : ℝ | P.eval x = 0} = (S : Set ℝ) := by
    ext x
    change P.eval x = 0 ↔ x ∈ (S : Set ℝ)
    simp only [Finset.mem_coe, S, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
      Polynomial.IsRoot.def]
  rw [hS_eq, Set.ncard_coe_finset]
  by_contra hgt
  have hge : m + 2 ≤ S.card := by omega
  let e : Fin S.card ↪o ℝ := S.orderEmbOfFin rfl
  have hex_c : ∀ i : Fin (m + 1),
      ∃ c : ℝ, e ⟨i.val, by omega⟩ < c ∧ c < e ⟨i.val + 1, by omega⟩ ∧
        (Polynomial.derivative P).eval c = 0 := by
    intro i
    let a := e ⟨i.val, by omega⟩
    let b := e ⟨i.val + 1, by omega⟩
    have hab : a < b := e.strictMono (by simp)
    have haS : a ∈ (S : Set ℝ) := S.orderEmbOfFin_mem rfl _
    have hbS : b ∈ (S : Set ℝ) := S.orderEmbOfFin_mem rfl _
    rw [← hS_eq] at haS hbS
    have ha0 : P.eval a = 0 := haS
    have hb0 : P.eval b = 0 := hbS
    obtain ⟨c, hcIoo, hcd⟩ :=
      exists_deriv_eq_zero hab P.continuous.continuousOn (ha0.trans hb0.symm)
    rw [(P.hasDerivAt c).deriv] at hcd
    exact ⟨c, hcIoo.1, hcIoo.2, hcd⟩
  let c : Fin (m + 1) → ℝ := fun i => (hex_c i).choose
  have hc_lt1 : ∀ i : Fin (m + 1), e ⟨i.val, by omega⟩ < c i := fun i => (hex_c i).choose_spec.1
  have hc_lt2 : ∀ i : Fin (m + 1), c i < e ⟨i.val + 1, by omega⟩ :=
    fun i => (hex_c i).choose_spec.2.1
  have hc_root : ∀ i : Fin (m + 1), (Polynomial.derivative P).eval (c i) = 0 :=
    fun i => (hex_c i).choose_spec.2.2
  have hc_strict : StrictMono c := by
    intro i j hij
    have hle_idx : (⟨i.val + 1, by omega⟩ : Fin S.card) ≤ ⟨j.val, by omega⟩ := by
      change i.val + 1 ≤ j.val
      exact hij
    calc c i < e ⟨i.val + 1, by omega⟩ := hc_lt2 i
      _ ≤ e ⟨j.val, by omega⟩ := e.monotone hle_idx
      _ < c j := hc_lt1 j
  have hsub : Set.range c ⊆ {x : ℝ | (Polynomial.derivative P).eval x = 0} := by
    rintro _ ⟨i, rfl⟩
    exact hc_root i
  have hcard_range : (Set.range c).ncard = m + 1 := by
    rw [Set.ncard_range_of_injective hc_strict.injective, Nat.card_fin]
  have hle_ncard : (Set.range c).ncard ≤ {x : ℝ | (Polynomial.derivative P).eval x = 0}.ncard :=
    Set.ncard_le_ncard hsub hderiv_fin
  omega

/-- **§11.3 Main-Text Worked Example (`f = x⁵ - 4x + 2`)** (printed pp. 96–97 / PDF pp. 104–105):
`f = x⁵ - 4x + 2 ∈ ℚ[x]` is irreducible of prime degree `5`, has `f(-2) = -22`, `f(0) = 2`,
`f(1) = -1`, `f(2) = 26`, has exactly `3` real roots and `2` non-real complex roots in `ℂ`, and
for every splitting field `L : ℚ` of `f`, `garlingRootPermHom ℚ L f` is bijective and
`Γ_ℚ(f) ≃* Equiv.Perm (Fin 5)` (`Σ₅`). -/
theorem section_11_3_quintic_example :
    let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
    Irreducible f ∧
    f.natDegree = 5 ∧
    (f.eval (-2) = -22 ∧ f.eval 0 = 2 ∧ f.eval 1 = -1 ∧ f.eval 2 = 26) ∧
    {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3 ∧
    {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2 ∧
    ∀ (L : Type*) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Function.Bijective (garlingRootPermHom ℚ L f) ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Equiv.Perm (Fin 5)) := by
  intro f
  have hirr : Irreducible f := example_5_2_quintic_irreducible.2.1
  have hdeg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  have hevals : f.eval (-2) = -22 ∧ f.eval 0 = 2 ∧ f.eval 1 = -1 ∧ f.eval 2 = 26 := by
    dsimp [f]
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  let fR : ℝ[X] := f.map (algebraMap ℚ ℝ)
  have hfR_eq : fR = Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2 := by
    simp [fR, f, map_ofNat]
  have hfR0 : fR ≠ 0 := by
    rw [hfR_eq]
    intro h0
    have hev := congrArg (Polynomial.eval 0) h0
    norm_num at hev
  have haev_iff : ∀ x : ℝ, Polynomial.aeval x f = 0 ↔ fR.eval x = 0 := by
    intro x
    rw [Polynomial.aeval_def, Polynomial.eval_map]
  have hset_eq : {x : ℝ | Polynomial.aeval x f = 0} = {x : ℝ | fR.eval x = 0} := by
    ext x; exact haev_iff x
  -- Lower bound `≥ 3` real roots via IVT on `(-2, 0)`, `(0, 1)`, `(1, 2)`.
  obtain ⟨r₁, hr₁Ioo, hr₁0⟩ := exists_Ioo_root_of_mul_neg (P := fR) (a := -2) (b := 0)
    (by norm_num) (by rw [hfR_eq]; norm_num)
  obtain ⟨r₂, hr₂Ioo, hr₂0⟩ := exists_Ioo_root_of_mul_neg (P := fR) (a := 0) (b := 1)
    (by norm_num) (by rw [hfR_eq]; norm_num)
  obtain ⟨r₃, hr₃Ioo, hr₃0⟩ := exists_Ioo_root_of_mul_neg (P := fR) (a := 1) (b := 2)
    (by norm_num) (by rw [hfR_eq]; norm_num)
  obtain ⟨_, _, hR_fin, _, _⟩ := separable_rat_roots_partition hirr.separable
  have hge3 : 3 ≤ {x : ℝ | Polynomial.aeval x f = 0}.ncard := by
    let g3 : Fin 3 → ℝ := ![r₁, r₂, r₃]
    have hg3_inj : Function.Injective g3 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp [g3] at hij ⊢
      all_goals linarith [hr₁Ioo.1, hr₁Ioo.2, hr₂Ioo.1, hr₂Ioo.2, hr₃Ioo.1, hr₃Ioo.2]
    have hsub3 : Set.range g3 ⊆ {x : ℝ | Polynomial.aeval x f = 0} := by
      rintro _ ⟨i, rfl⟩
      rw [hset_eq]
      fin_cases i
      · exact hr₁0
      · exact hr₂0
      · exact hr₃0
    have hcard3 : (Set.range g3).ncard = 3 := by
      rw [Set.ncard_range_of_injective hg3_inj, Nat.card_fin]
    exact hcard3 ▸ Set.ncard_le_ncard hsub3 hR_fin
  -- Upper bound `≤ 3` real roots via Rolle's theorem: `fR' = 5*X^4 - 4` has at most `2` real roots.
  have hderiv_eq : Polynomial.derivative fR = Polynomial.C 5 * Polynomial.X ^ 4 - Polynomial.C 4 := by
    rw [hfR_eq]
    simp [map_ofNat]
    ring
  have hderiv_ne0 : Polynomial.derivative fR ≠ 0 := by
    rw [hderiv_eq]
    intro h0
    have hev := congrArg (Polynomial.eval 0) h0
    norm_num at hev
  have hderiv_fin : {x : ℝ | (Polynomial.derivative fR).eval x = 0}.Finite := by
    have heq : {x : ℝ | (Polynomial.derivative fR).eval x = 0} =
        ((Polynomial.derivative fR).roots.toFinset : Set ℝ) := by
      ext x
      change (Polynomial.derivative fR).eval x = 0 ↔ _
      simp [Polynomial.mem_roots hderiv_ne0]
    rw [heq]
    exact Finset.finite_toSet _
  have hderiv_le2 : {x : ℝ | (Polynomial.derivative fR).eval x = 0}.ncard ≤ 2 := by
    by_contra hgt2
    have hge3_d : 3 ≤ hderiv_fin.toFinset.card := by
      rw [← Set.ncard_coe_finset, hderiv_fin.coe_toFinset]
      omega
    let ed : Fin hderiv_fin.toFinset.card ↪o ℝ := hderiv_fin.toFinset.orderEmbOfFin rfl
    let c₀ := ed ⟨0, by omega⟩
    let c₁ := ed ⟨1, by omega⟩
    let c₂ := ed ⟨2, by omega⟩
    have hc01 : c₀ < c₁ := ed.strictMono (by simp)
    have hc12 : c₁ < c₂ := ed.strictMono (by simp)
    have hd_eval : ∀ x ∈ hderiv_fin.toFinset, 5 * x ^ 4 - 4 = 0 := by
      intro x hx
      have h0 : (Polynomial.derivative fR).eval x = 0 := hderiv_fin.mem_toFinset.mp hx
      rw [hderiv_eq] at h0
      simpa using h0
    have he0 : 5 * c₀ ^ 4 - 4 = 0 := hd_eval c₀ (hderiv_fin.toFinset.orderEmbOfFin_mem rfl _)
    have he1 : 5 * c₁ ^ 4 - 4 = 0 := hd_eval c₁ (hderiv_fin.toFinset.orderEmbOfFin_mem rfl _)
    have he2 : 5 * c₂ ^ 4 - 4 = 0 := hd_eval c₂ (hderiv_fin.toFinset.orderEmbOfFin_mem rfl _)
    have hpm : ∀ a b : ℝ, 5 * a ^ 4 - 4 = 0 → 5 * b ^ 4 - 4 = 0 → a < b → b = -a := by
      intro a b ha hb hab
      have hdiff : 5 * (a - b) * (a + b) * (a ^ 2 + b ^ 2) = 0 := by linear_combination ha - hb
      have hab_ne : 5 * (a - b) ≠ 0 := by linarith
      have hsq_pos : 0 < a ^ 2 + b ^ 2 := by
        by_cases ha0 : a = 0
        · subst ha0; norm_num at ha
        · have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
          have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
          linarith
      rcases mul_eq_zero.mp hdiff with h1 | h2
      · rcases mul_eq_zero.mp h1 with h1a | h1b
        · exact (hab_ne h1a).elim
        · linarith
      · linarith
    have hc1_eq : c₁ = -c₀ := hpm c₀ c₁ he0 he1 hc01
    have hc2_eq : c₂ = -c₀ := hpm c₀ c₂ he0 he2 (hc01.trans hc12)
    linarith
  have hle3 : {x : ℝ | Polynomial.aeval x f = 0}.ncard ≤ 3 := by
    rw [hset_eq]
    exact ncard_real_roots_le_succ_of_deriv_bound hfR0 hderiv_fin hderiv_le2
  have hreal3 : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3 := by omega
  obtain ⟨_, _, _, _, hsum5⟩ := separable_rat_roots_partition hirr.separable
  have hcomp2 : {z : ℂ | Polynomial.aeval z f = 0 ∧ z.im ≠ 0}.ncard = 2 := by omega
  refine ⟨hirr, hdeg, hevals, hreal3, hcomp2, fun L _ _ hsfL => ?_⟩
  obtain ⟨hbij, hiso, _, _⟩ := theorem_11_7 hirr (by decide : Nat.Prime 5) hdeg hreal3 hcomp2 L hsfL
  exact ⟨hbij, hiso⟩

/-- The polynomial `f_r = (x² + 4) x (x² - 4)(x² - 16) ... (x² - 4r²) ∈ ℤ[X]` of **Exercise 11.8**
(§11.3, printed p. 97 / PDF p. 105). -/
noncomputable def ex118Poly (r : ℕ) : ℤ[X] :=
  (Polynomial.X ^ 2 + 4) * Polynomial.X *
    ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℤ) ^ 2))

/-- Rational image `f_r ∈ ℚ[X]` of `ex118Poly r`. -/
noncomputable def ex118RatPoly (r : ℕ) : ℚ[X] :=
  (ex118Poly r).map (algebraMap ℤ ℚ)

/-- Factorization of `X * ∏_{j=1}^r (X² - 4j²)` into the `2r + 1` linear factors
`∏_{m = -r}^r (X - 2m)` in `ℤ[X]`. -/
theorem ex118_linear_prod_eq (r : ℕ) :
    (Polynomial.X * ∏ j ∈ Finset.Icc 1 r,
        (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℤ) ^ 2)) : ℤ[X]) =
      ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (Polynomial.X - Polynomial.C (2 * m)) := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    have hIcc_pos : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hIcc_symm : Finset.Icc (-((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ) =
        insert (-((r + 1 : ℕ) : ℤ)) (insert ((r + 1 : ℕ) : ℤ) (Finset.Icc (-(r : ℤ)) (r : ℤ))) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hnot1 : r + 1 ∉ Finset.Icc 1 r := by simp
    have hnot_neg : (-((r + 1 : ℕ) : ℤ)) ∉
        insert ((r + 1 : ℕ) : ℤ) (Finset.Icc (-(r : ℤ)) (r : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast; omega
    have hnot_pos : ((r + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(r : ℤ)) (r : ℤ) := by
      simp only [Finset.mem_Icc]
      push_cast; omega
    rw [hIcc_pos, Finset.prod_insert hnot1,
      hIcc_symm, Finset.prod_insert hnot_neg, Finset.prod_insert hnot_pos]
    calc Polynomial.X *
          ((Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2)) *
            ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℤ) ^ 2)))
        = (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2)) *
            (Polynomial.X *
              ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℤ) ^ 2))) := by ring
      _ = ((Polynomial.X - Polynomial.C (2 * (-((r + 1 : ℕ) : ℤ)))) *
            (Polynomial.X - Polynomial.C (2 * ((r + 1 : ℕ) : ℤ)))) *
            ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (Polynomial.X - Polynomial.C (2 * m)) := by
          rw [ih]
          congr 1
          simp only [map_mul, map_neg, map_pow, map_ofNat]
          ring
      _ = _ := by ring

/-- Monicity, degree `2r + 3`, and mod-`2` congruence `ex118Poly r = X^(2r+3) + 2*h` for all `r : ℕ`. -/
theorem ex118Poly_monic_deg_and_mod_two (r : ℕ) :
    (ex118Poly r).Monic ∧
    (ex118Poly r).natDegree = 2 * r + 3 ∧
    (ex118Poly r).eval 0 = 0 ∧
    ∃ h : ℤ[X], ex118Poly r = Polynomial.X ^ (2 * r + 3) + 2 * h := by
  have hev0 : (ex118Poly r).eval 0 = 0 := by simp [ex118Poly]
  have hmod2 : ∃ h : ℤ[X], ex118Poly r = Polynomial.X ^ (2 * r + 3) + 2 * h := by
    clear hev0
    induction r with
    | zero =>
      refine ⟨2 * Polynomial.X, ?_⟩
      simp only [ex118Poly, mul_zero, zero_add]
      have hIcc0 : Finset.Icc (1 : ℕ) 0 = ∅ := by decide
      rw [hIcc0, Finset.prod_empty, mul_one]
      ring
    | succ r ih =>
      obtain ⟨h, hh⟩ := ih
      have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : r + 1 ∉ Finset.Icc 1 r := by simp
      have hstep : ex118Poly (r + 1) =
          ex118Poly r * (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2)) := by
        unfold ex118Poly
        rw [hIcc, Finset.prod_insert hnot]
        ring
      refine ⟨h * (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2)) -
          Polynomial.C (2 * ((r + 1 : ℕ) : ℤ) ^ 2) * Polynomial.X ^ (2 * r + 3), ?_⟩
      rw [hstep, hh, show 2 * (r + 1) + 3 = (2 * r + 3) + 2 by omega, pow_add]
      have hC4 : (Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2) : ℤ[X]) =
          2 * Polynomial.C (2 * ((r + 1 : ℕ) : ℤ) ^ 2) := by
        rw [← Polynomial.C_ofNat, ← Polynomial.C_mul]; ring_nf
      rw [hC4]
      ring
  have hmon_deg : (ex118Poly r).Monic ∧ (ex118Poly r).natDegree = 2 * r + 3 := by
    clear hev0 hmod2
    induction r with
    | zero =>
      have h0 : ex118Poly 0 = Polynomial.X ^ 3 + 4 * Polynomial.X := by
        simp only [ex118Poly]
        have hIcc0 : Finset.Icc (1 : ℕ) 0 = ∅ := by decide
        rw [hIcc0, Finset.prod_empty, mul_one]
        ring
      rw [h0]
      exact ⟨by monicity!, by compute_degree!⟩
    | succ r ih =>
      have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : r + 1 ∉ Finset.Icc 1 r := by simp
      have hstep : ex118Poly (r + 1) =
          ex118Poly r * (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2)) := by
        unfold ex118Poly
        rw [hIcc, Finset.prod_insert hnot]
        ring
      have hfac_mon : (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2) : ℤ[X]).Monic :=
        Polynomial.monic_X_pow_sub_C _ (by decide)
      have hfac_deg : (Polynomial.X ^ 2 - Polynomial.C (4 * ((r + 1 : ℕ) : ℤ) ^ 2) : ℤ[X]).natDegree = 2 :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hstep]
      refine ⟨ih.1.mul hfac_mon, ?_⟩
      rw [Polynomial.natDegree_mul ih.1.ne_zero hfac_mon.ne_zero, ih.2, hfac_deg]
      omega
  exact ⟨hmon_deg.1, hmon_deg.2, hev0, hmod2⟩

/-- **Exercise 11.8** (§11.3, printed p. 97 / PDF p. 105; see `QUEUE.md` on `"Sketch / determine"` prompt):
*"Sketch the graph of the polynomial `f_r = (x² + 4) x (x² - 4)(x² - 16) ... (x² - 4r²)`.
Show that if `k` is an odd integer then `|f_r(k)| ≥ 5`. Show that `f_r - 2` is irreducible, and
determine its Galois group over `ℚ` when `2r + 3` is a prime."*

Proves for **all** `r : ℕ`:
1. **Graph / real zeros & sign alternation of `f_r`:** `f_r` is monic of odd degree `2r + 3`, its
   real zeros are `{2m : m ∈ [-r, r]}` (`2r + 1` simple zeros), and `f_r` alternates in sign across
   the `2r + 2` odd integers `2s - 1, 2s + 1` (`-r ≤ s ≤ r`): `f_r(2s - 1) * f_r(2s + 1) < 0`.
2. **Odd-integer bound:** for every odd `k : ℤ`, `|(ex118Poly r).eval k| ≥ 5`.
3. **Irreducibility:** `ex118Poly r - 2` is irreducible in `ℤ[X]` (by Eisenstein `Theorem 5.2` at
   `p = 2`) and `ex118RatPoly r - 2` is irreducible in `ℚ[X]` (by Gauss `Corollary 2 to Theorem 3.13`).
4. **Root structure of `f_r - 2`:** `ex118RatPoly r - 2` has exact real root count `2r + 1` and
   exact non-real complex root count `2` in `ℂ`.
5. **Galois group over `ℚ`:** whenever `Nat.Prime (2 * r + 3)` and `L : ℚ` is any splitting field of
   `ex118RatPoly r - 2`, `garlingRootPermHom ℚ L (ex118RatPoly r - 2)` is bijective and
   `GarlingPolyGaloisGroup ℚ L (ex118RatPoly r - 2) ≃* Equiv.Perm (Fin (2 * r + 3))` (`Σ_{2r+3}`). -/
theorem exercise_11_8 (r : ℕ) :
    -- 1. Graph properties of `f_r`: degree `2r + 3`, exact real zeros `2m` (`-r ≤ m ≤ r`), and sign alternation
    ((ex118RatPoly r).natDegree = 2 * r + 3 ∧
      (∀ x : ℝ, Polynomial.aeval x (ex118RatPoly r) = 0 ↔
        ∃ m : ℤ, -(r : ℤ) ≤ m ∧ m ≤ r ∧ x = 2 * (m : ℝ)) ∧
      (∀ s : ℤ, -(r : ℤ) ≤ s → s ≤ r →
        ((ex118Poly r).eval (2 * s - 1)) * ((ex118Poly r).eval (2 * s + 1)) < 0)) ∧
    -- 2. Odd-integer lower bound `|f_r(k)| ≥ 5`
    (∀ k : ℤ, Odd k → 5 ≤ |(ex118Poly r).eval k|) ∧
    -- 3. Irreducibility of `f_r - 2` in `ℤ[X]` and `ℚ[X]`
    (Irreducible (ex118Poly r - 2) ∧ Irreducible (ex118RatPoly r - 2)) ∧
    -- 4. Exact root counts of `f_r - 2` (`2r + 1` real roots, `2` non-real complex roots)
    ({x : ℝ | Polynomial.aeval x (ex118RatPoly r - 2) = 0}.ncard = 2 * r + 1 ∧
      {z : ℂ | Polynomial.aeval z (ex118RatPoly r - 2) = 0 ∧ z.im ≠ 0}.ncard = 2) ∧
    -- 5. Galois group `Σ_{2r+3}` when `2r + 3` is prime
    (Nat.Prime (2 * r + 3) →
      ∀ (L : Type*) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L (ex118RatPoly r - 2) →
        Function.Bijective (garlingRootPermHom ℚ L (ex118RatPoly r - 2)) ∧
        Nonempty (GarlingPolyGaloisGroup ℚ L (ex118RatPoly r - 2) ≃*
          Equiv.Perm (Fin (2 * r + 3)))) := by
  obtain ⟨hmonZ, hdegZ, hev0Z, hmod2⟩ := ex118Poly_monic_deg_and_mod_two r
  have hdegQ : (ex118RatPoly r).natDegree = 2 * r + 3 :=
    (hmonZ.natDegree_map (algebraMap ℤ ℚ)).trans hdegZ
  -- Part 1a: Real zeros of `f_r` are `{2m : -r ≤ m ≤ r}`.
  have hzeros_fr : ∀ x : ℝ, Polynomial.aeval x (ex118RatPoly r) = 0 ↔
      ∃ m : ℤ, -(r : ℤ) ≤ m ∧ m ≤ r ∧ x = 2 * (m : ℝ) := by
    intro x
    have hlin : ex118Poly r = (Polynomial.X ^ 2 + 4) *
        ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (Polynomial.X - Polynomial.C (2 * m)) := by
      unfold ex118Poly
      rw [mul_assoc, ex118_linear_prod_eq]
    have haev : Polynomial.aeval x (ex118RatPoly r) =
        (x ^ 2 + 4) * ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (x - 2 * (m : ℝ)) := by
      unfold ex118RatPoly
      rw [Polynomial.aeval_map_algebraMap, hlin, map_mul, map_add, map_pow,
        Polynomial.aeval_X, map_ofNat, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      simp
    rw [haev, mul_eq_zero]
    have hx2_pos : x ^ 2 + 4 ≠ 0 := by positivity
    simp only [hx2_pos, false_or, Finset.prod_eq_zero_iff, Finset.mem_Icc, sub_eq_zero]
    exact ⟨fun ⟨m, ⟨hm1, hm2⟩, hxm⟩ => ⟨m, hm1, hm2, hxm⟩,
      fun ⟨m, hm1, hm2, hxm⟩ => ⟨m, ⟨hm1, hm2⟩, hxm⟩⟩
  -- Part 1b: Sign alternation `f_r(2s - 1) * f_r(2s + 1) < 0` for `-r ≤ s ≤ r`.
  have hsign_alt : ∀ s : ℤ, -(r : ℤ) ≤ s → s ≤ r →
      ((ex118Poly r).eval (2 * s - 1)) * ((ex118Poly r).eval (2 * s + 1)) < 0 := by
    intro s hs1 hs2
    have hlin : ex118Poly r = (Polynomial.X ^ 2 + 4) *
        ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (Polynomial.X - Polynomial.C (2 * m)) := by
      unfold ex118Poly
      rw [mul_assoc, ex118_linear_prod_eq]
    have hev : ∀ k : ℤ, (ex118Poly r).eval k =
        (k ^ 2 + 4) * ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (k - 2 * m) := by
      intro k
      rw [hlin, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_prod]
      congr 1
      refine Finset.prod_congr rfl fun m _ => by simp
    rw [hev (2 * s - 1), hev (2 * s + 1)]
    have hs_mem : s ∈ Finset.Icc (-(r : ℤ)) (r : ℤ) := Finset.mem_Icc.mpr ⟨hs1, hs2⟩
    have hprod_mul : (∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s - 1 - 2 * m)) *
        (∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s + 1 - 2 * m)) < 0 := by
      rw [← Finset.prod_mul_distrib, ← Finset.mul_prod_erase _ _ hs_mem]
      have h_at_s : (2 * s - 1 - 2 * s) * (2 * s + 1 - 2 * s) = -1 := by ring
      rw [h_at_s, neg_one_mul, Left.neg_neg_iff]
      refine Finset.prod_pos fun m hm => ?_
      have hm_ne : m ≠ s := (Finset.mem_erase.mp hm).1
      rcases lt_or_gt_of_ne hm_ne with hlt | hgt
      · have h1 : 0 < 2 * s - 1 - 2 * m := by omega
        have h2 : 0 < 2 * s + 1 - 2 * m := by omega
        exact mul_pos h1 h2
      · have h1 : 2 * s - 1 - 2 * m < 0 := by omega
        have h2 : 2 * s + 1 - 2 * m < 0 := by omega
        exact mul_pos_of_neg_of_neg h1 h2
    have hq1 : 0 < (2 * s - 1) ^ 2 + 4 := by positivity
    have hq2 : 0 < (2 * s + 1) ^ 2 + 4 := by positivity
    have hqq : 0 < ((2 * s - 1) ^ 2 + 4) * ((2 * s + 1) ^ 2 + 4) := mul_pos hq1 hq2
    calc (((2 * s - 1) ^ 2 + 4) * ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s - 1 - 2 * m)) *
          (((2 * s + 1) ^ 2 + 4) * ∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s + 1 - 2 * m))
        = (((2 * s - 1) ^ 2 + 4) * ((2 * s + 1) ^ 2 + 4)) *
            ((∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s - 1 - 2 * m)) *
              (∏ m ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), (2 * s + 1 - 2 * m))) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hqq hprod_mul
  -- Part 2: Odd-integer lower bound `|f_r(k)| ≥ 5`.
  have hodd_bound : ∀ k : ℤ, Odd k → 5 ≤ |(ex118Poly r).eval k| := by
    intro k ⟨t, hkt⟩
    unfold ex118Poly
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_prod, abs_mul, abs_mul,
      Finset.abs_prod]
    have hk_ne0 : k ≠ 0 := by omega
    have hk_abs : 1 ≤ |k| := Int.one_le_abs hk_ne0
    have hk2_ge1 : 1 ≤ k ^ 2 := by nlinarith [sq_abs k]
    have hf1 : 5 ≤ |(Polynomial.X ^ 2 + 4 : ℤ[X]).eval k| := by
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      rw [abs_of_pos (by positivity)]
      linarith
    have hf2 : 1 ≤ |(Polynomial.X : ℤ[X]).eval k| := by
      rw [Polynomial.eval_X]
      exact hk_abs
    have hf3 : 1 ≤ ∏ j ∈ Finset.Icc 1 r,
        |(Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℤ) ^ 2) : ℤ[X]).eval k| := by
      refine Finset.prod_induction _ (fun z : ℤ => 1 ≤ z)
        (fun a b ha hb => by nlinarith) (by decide) (fun j _ => ?_)
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      apply Int.one_le_abs
      intro h0
      have hmod2_eq : (k ^ 2 - 4 * (j : ℤ) ^ 2) % 2 = 0 := by rw [h0]; rfl
      rw [hkt] at hmod2_eq
      have hodd_val : ((2 * t + 1) ^ 2 - 4 * (j : ℤ) ^ 2) % 2 = 1 := by
        have heq : (2 * t + 1) ^ 2 - 4 * (j : ℤ) ^ 2 =
            2 * (2 * t ^ 2 + 2 * t - 2 * (j : ℤ) ^ 2) + 1 := by ring
        rw [heq]; omega
      omega
    have h12 : 5 ≤ |(Polynomial.X ^ 2 + 4 : ℤ[X]).eval k| * |(Polynomial.X : ℤ[X]).eval k| := by
      nlinarith
    nlinarith
  -- Part 3: Eisenstein irreducibility of `f_r - 2` in `ℤ[X]` and `ℚ[X]`.
  let gZ : ℤ[X] := ex118Poly r - 2
  have hgZ_deg : gZ.natDegree = 2 * r + 3 := by
    dsimp [gZ]
    have h2 : (2 : ℤ[X]) = Polynomial.C 2 := by simp
    rw [h2, Polynomial.natDegree_sub_C, hdegZ]
  have hgZ_mon : gZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hgZ_deg]
    dsimp [gZ]
    have hfn : (ex118Poly r).coeff (2 * r + 3) = 1 := by
      rw [← hdegZ, ← Polynomial.leadingCoeff, hmonZ.leadingCoeff]
    have hc2 : (2 : ℤ[X]).coeff (2 * r + 3) = 0 := by
      rw [← Polynomial.C_ofNat, Polynomial.coeff_C]
      simp
    rw [Polynomial.coeff_sub, hfn, hc2, sub_zero]
  have hcopZ : IsGarlingRelativelyPrime (Set.range fun i : Fin (2 * r + 4) => gZ.coeff i) :=
    isGarlingRelativelyPrime_coeffs_of_monic hgZ_mon hgZ_deg
  obtain ⟨h_mod, hh_mod⟩ := hmod2
  have hdvdZ : ∀ i < 2 * r + 3, (2 : ℤ) ∣ gZ.coeff i := by
    intro i hi
    have hgZ_mod : gZ = Polynomial.X ^ (2 * r + 3) + 2 * (h_mod - 1) := by
      dsimp [gZ]; rw [hh_mod]; ring
    rw [hgZ_mod, Polynomial.coeff_add, Polynomial.coeff_X_pow]
    simp only [show ¬ (i = 2 * r + 3) by omega, ↓reduceIte, zero_add]
    have h2C : (2 * (h_mod - 1) : ℤ[X]) = Polynomial.C 2 * (h_mod - 1) := by simp
    rw [h2C, Polynomial.coeff_C_mul]
    exact dvd_mul_right 2 _
  have hndvd_top : ¬ ((2 : ℤ) ∣ gZ.coeff (2 * r + 3)) := by
    have h1 : gZ.coeff (2 * r + 3) = 1 := by
      rw [← hgZ_deg, ← Polynomial.leadingCoeff, hgZ_mon.leadingCoeff]
    rw [h1]; decide
  have hndvd_sq : ¬ ((2 : ℤ) ^ 2 ∣ gZ.coeff 0) := by
    have hc0 : gZ.coeff 0 = -2 := by
      dsimp [gZ]
      rw [Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero, hev0Z]
      have hc2 : (2 : ℤ[X]).coeff 0 = 2 := by rw [← Polynomial.C_ofNat]; simp
      rw [hc2]; ring
    rw [hc0]; decide
  have hirrZ : Irreducible gZ :=
    (theorem_5_2 (by omega : 1 ≤ 2 * r + 3) (le_of_eq hgZ_deg) hcopZ Int.prime_two
      hdvdZ hndvd_top hndvd_sq).2.1
  have hirrQ : Irreducible (ex118RatPoly r - 2) := by
    have hmap_gZ : gZ.map (algebraMap ℤ ℚ) = ex118RatPoly r - 2 := by
      simp [gZ, ex118RatPoly]
    rcases (corollary_gauss_lemma ℚ gZ).mp hirrZ with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
    · exfalso
      have hd := congrArg Polynomial.natDegree hC
      rw [hgZ_deg, Polynomial.natDegree_C] at hd
      omega
    · rwa [hmap_gZ] at hmap_irr
  -- Part 4: Exact real (`2r + 1`) and non-real (`2`) root counts of `gQ := ex118RatPoly r - 2`.
  let gQ : ℚ[X] := ex118RatPoly r - 2
  have hgQ_deg : gQ.natDegree = 2 * r + 3 := by
    dsimp [gQ]
    rw [← Polynomial.C_ofNat, Polynomial.natDegree_sub_C, hdegQ]
  obtain ⟨_, _, hR_fin, _, hsum_roots⟩ := separable_rat_roots_partition hirrQ.separable
  let gR : ℝ[X] := gQ.map (algebraMap ℚ ℝ)
  have hgR0 : gR ≠ 0 := hirrQ.separable.map.ne_zero
  have hset_gR : {x : ℝ | Polynomial.aeval x gQ = 0} = {x : ℝ | gR.eval x = 0} := by
    ext x
    change Polynomial.aeval x gQ = 0 ↔ gR.eval x = 0
    rw [Polynomial.aeval_def, Polynomial.eval_map]
  -- 4a. Lower bound `≥ 2r + 1` real roots from sign alternation on `(2s - 1, 2s + 1)` (`s = -r, ..., r`).
  have hreal_ge : 2 * r + 1 ≤ {x : ℝ | Polynomial.aeval x gQ = 0}.ncard := by
    have hex_ρ : ∀ i : Fin (2 * r + 1),
        let s : ℤ := (i.val : ℤ) - (r : ℤ)
        ∃ ρ ∈ Set.Ioo (2 * (s : ℝ) - 1) (2 * (s : ℝ) + 1), gR.eval ρ = 0 := by
      intro i s
      have hs1 : -(r : ℤ) ≤ s := by omega
      have hs2 : s ≤ (r : ℤ) := by omega
      let u : ℤ := (ex118Poly r).eval (2 * s - 1)
      let v : ℤ := (ex118Poly r).eval (2 * s + 1)
      have huv_neg : u * v < 0 := hsign_alt s hs1 hs2
      have hu5 : 5 ≤ |u| := hodd_bound (2 * s - 1) ⟨s - 1, by ring⟩
      have hv5 : 5 ≤ |v| := hodd_bound (2 * s + 1) ⟨s, rfl⟩
      have huv_sub2_neg : (u - 2) * (v - 2) < 0 := by
        rcases le_or_gt 0 u with hu_pos | hu_neg
        · have hu_ge : 5 ≤ u := by rwa [abs_of_nonneg hu_pos] at hu5
          have hv_neg : v < 0 := by nlinarith
          have hv_le : v ≤ -5 := by rw [abs_of_neg hv_neg] at hv5; linarith
          nlinarith
        · have hu_le : u ≤ -5 := by rw [abs_of_neg hu_neg] at hu5; linarith
          have hv_pos : 0 < v := by nlinarith
          have hv_ge : 5 ≤ v := by rwa [abs_of_pos hv_pos] at hv5
          nlinarith
      have hgR_eval_int : ∀ k : ℤ, gR.eval (k : ℝ) = (((ex118Poly r).eval k - 2 : ℤ) : ℝ) := by
        intro k
        let vk : ℤ := (ex118Poly r).eval k
        have hcomp_ZR : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℝ :=
          RingHom.ext fun z => by simp
        have hgR_map : gR = (ex118Poly r - 2).map (algebraMap ℤ ℝ) := by
          dsimp [gR, gQ, ex118RatPoly]
          rw [Polynomial.map_sub, Polynomial.map_map, hcomp_ZR, Polynomial.map_sub]
          simp
        rw [hgR_map, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub, map_ofNat]
        have haevZ : Polynomial.aeval (k : ℝ) (ex118Poly r) = (vk : ℝ) :=
          Polynomial.aeval_algHom_apply (Algebra.ofId ℤ ℝ) k (ex118Poly r)
        rw [haevZ]
        change (vk : ℝ) - 2 = ((vk - 2 : ℤ) : ℝ)
        push_cast; rfl
      have hmul_R : gR.eval (2 * (s : ℝ) - 1) * gR.eval (2 * (s : ℝ) + 1) < 0 := by
        have hk1 : (2 * (s : ℝ) - 1) = ((2 * s - 1 : ℤ) : ℝ) := by push_cast; ring
        have hk2 : (2 * (s : ℝ) + 1) = ((2 * s + 1 : ℤ) : ℝ) := by push_cast; ring
        rw [hk1, hk2, hgR_eval_int, hgR_eval_int]
        exact_mod_cast huv_sub2_neg
      exact exists_Ioo_root_of_mul_neg (by linarith) hmul_R
    let ρ : Fin (2 * r + 1) → ℝ := fun i => (hex_ρ i).choose
    have hρ_strict : StrictMono ρ := by
      intro i j hij
      have h1 := ((hex_ρ i).choose_spec.1).2
      have h2 := ((hex_ρ j).choose_spec.1).1
      have hij_Z : ((i.val : ℤ) - (r : ℤ)) + 1 ≤ (j.val : ℤ) - (r : ℤ) := by
        have hij_N : i.val + 1 ≤ j.val := hij
        omega
      have hij_R : 2 * (((i.val : ℤ) - (r : ℤ) : ℤ) : ℝ) + 1 ≤
          2 * (((j.val : ℤ) - (r : ℤ) : ℤ) : ℝ) - 1 := by
        have hZ : 2 * ((i.val : ℤ) - (r : ℤ)) + 1 ≤ 2 * ((j.val : ℤ) - (r : ℤ)) - 1 := by omega
        exact_mod_cast hZ
      linarith
    have hsub_ρ : Set.range ρ ⊆ {x : ℝ | Polynomial.aeval x gQ = 0} := by
      rintro _ ⟨i, rfl⟩
      rw [hset_gR]
      exact (hex_ρ i).choose_spec.2
    have hcard_ρ : (Set.range ρ).ncard = 2 * r + 1 := by
      rw [Set.ncard_range_of_injective hρ_strict.injective, Nat.card_fin]
    exact hcard_ρ ▸ Set.ncard_le_ncard hsub_ρ hR_fin
  -- 4b. Upper bound `≤ 2r + 1` real roots via purely imaginary critical points `i*y₁, i*y₂` of `f_r`!
  have hreal_le : {x : ℝ | Polynomial.aeval x gQ = 0}.ncard ≤ 2 * r + 1 := by
    let qR : ℝ[X] := (Polynomial.X ^ 2 - 4) * Polynomial.X *
      ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 + Polynomial.C (4 * (j : ℝ) ^ 2))
    -- Real Rolle on `qR` over `[-2, 0]` and `[0, 2]` gives `y₁ ∈ (-2, 0)` and `y₂ ∈ (0, 2)` with `qR'(y_k) = 0`.
    have hqR_m2 : qR.eval (-2) = 0 := by simp [qR]; norm_num
    have hqR_0 : qR.eval 0 = 0 := by simp [qR]
    have hqR_2 : qR.eval 2 = 0 := by simp [qR]; norm_num
    obtain ⟨y₁, hy₁Ioo, hy₁_d⟩ :=
      exists_deriv_eq_zero (a := -2) (b := 0) (by norm_num) qR.continuous.continuousOn
        (hqR_m2.trans hqR_0.symm)
    obtain ⟨y₂, hy₂Ioo, hy₂_d⟩ :=
      exists_deriv_eq_zero (a := 0) (b := 2) (by norm_num) qR.continuous.continuousOn
        (hqR_0.trans hqR_2.symm)
    rw [(qR.hasDerivAt y₁).deriv] at hy₁_d
    rw [(qR.hasDerivAt y₂).deriv] at hy₂_d
    -- Relate `f_r(i * Y)` in `ℂ[X]` to `qR`: `fC.comp (C i * X) = C (i * (-1)^(r+1)) * qR_C`.
    let fC : ℂ[X] := (ex118RatPoly r).map (algebraMap ℚ ℂ)
    let qC : ℂ[X] := qR.map (algebraMap ℝ ℂ)
    have hcomp_id : fC.comp (Polynomial.C Complex.I * Polynomial.X) =
        Polynomial.C (Complex.I * (-1 : ℂ) ^ (r + 1)) * qC := by
      have hfC_def : fC = (Polynomial.X ^ 2 + 4) * Polynomial.X *
          ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℂ) ^ 2)) := by
        simp only [fC, ex118RatPoly, ex118Poly, Polynomial.map_mul, Polynomial.map_add,
          Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_prod,
          Polynomial.map_sub, Polynomial.map_C]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        simp
      have hqC_def : qC = (Polynomial.X ^ 2 - 4) * Polynomial.X *
          ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 + Polynomial.C (4 * (j : ℂ) ^ 2)) := by
        simp only [qC, qR, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_prod, Polynomial.map_add,
          Polynomial.map_C]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        simp
      rw [hfC_def, hqC_def, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.prod_comp]
      have h1 : (Polynomial.X ^ 2 + 4 : ℂ[X]).comp (Polynomial.C Complex.I * Polynomial.X) =
          -(Polynomial.X ^ 2 - 4) := by
        simp only [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp,
          Polynomial.ofNat_comp, mul_pow, ← Polynomial.C_pow, Complex.I_sq, map_neg, map_one]
        ring
      have h2 : (Polynomial.X : ℂ[X]).comp (Polynomial.C Complex.I * Polynomial.X) =
          Polynomial.C Complex.I * Polynomial.X := Polynomial.X_comp
      have h3 : (∏ j ∈ Finset.Icc 1 r,
          (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℂ) ^ 2) : ℂ[X]).comp
            (Polynomial.C Complex.I * Polynomial.X)) =
          Polynomial.C ((-1 : ℂ) ^ r) *
            ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 + Polynomial.C (4 * (j : ℂ) ^ 2)) := by
        have hterm : ∀ j ∈ Finset.Icc 1 r,
            (Polynomial.X ^ 2 - Polynomial.C (4 * (j : ℂ) ^ 2) : ℂ[X]).comp
              (Polynomial.C Complex.I * Polynomial.X) =
              Polynomial.C (-1 : ℂ) * (Polynomial.X ^ 2 + Polynomial.C (4 * (j : ℂ) ^ 2)) := by
          intro j _
          simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
            Polynomial.C_comp, mul_pow, ← Polynomial.C_pow, Complex.I_sq, map_neg, map_one]
          ring
        rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
          Nat.card_Icc, show r + 1 - 1 = r by omega, ← map_pow]
      rw [h1, h2, h3]
      simp only [pow_succ, map_mul, map_neg, map_one]
      ring
    -- Differentiate `hcomp_id` algebraically in `ℂ[X]` via `Polynomial.derivative_comp`!
    have hderiv_comp_id : Polynomial.C Complex.I *
        (Polynomial.derivative fC).comp (Polynomial.C Complex.I * Polynomial.X) =
        Polynomial.C (Complex.I * (-1 : ℂ) ^ (r + 1)) * (Polynomial.derivative qR).map (algebraMap ℝ ℂ) := by
      have hlhs : Polynomial.derivative (fC.comp (Polynomial.C Complex.I * Polynomial.X)) =
          Polynomial.C Complex.I *
            (Polynomial.derivative fC).comp (Polynomial.C Complex.I * Polynomial.X) := by
        rw [Polynomial.derivative_comp, Polynomial.derivative_C_mul, Polynomial.derivative_X,
          mul_one, mul_comm]
      have hrhs : Polynomial.derivative
          (Polynomial.C (Complex.I * (-1 : ℂ) ^ (r + 1)) * qC) =
          Polynomial.C (Complex.I * (-1 : ℂ) ^ (r + 1)) *
            (Polynomial.derivative qR).map (algebraMap ℝ ℂ) := by
        rw [Polynomial.derivative_C_mul, Polynomial.derivative_map]
      exact hlhs.symm.trans ((congrArg Polynomial.derivative hcomp_id).trans hrhs)
    -- Notice `derivative gR` maps to `derivative fC`!
    have hgR_deriv_map : (Polynomial.derivative gR).map (algebraMap ℝ ℂ) =
        Polynomial.derivative fC := by
      have hcomp_QC : (algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ) = algebraMap ℚ ℂ :=
        (IsScalarTower.algebraMap_eq ℚ ℝ ℂ).symm
      have hfC_gR : (gR.map (algebraMap ℝ ℂ)) = fC - 2 := by
        simp [gR, gQ, fC, Polynomial.map_map, hcomp_QC]
      rw [← Polynomial.derivative_map, hfC_gR, Polynomial.derivative_sub,
        ← Polynomial.C_ofNat, Polynomial.derivative_C, sub_zero]
    have himag_root : ∀ y : ℝ, (Polynomial.derivative qR).eval y = 0 →
        (Polynomial.derivative fC).eval (Complex.I * (y : ℂ)) = 0 := by
      intro y hy0
      have hev := congrArg (Polynomial.eval (y : ℂ)) hderiv_comp_id
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_map_algebraMap] at hev
      have hrhs0 : Complex.I * (-1 : ℂ) ^ (r + 1) *
          Polynomial.aeval (y : ℂ) (Polynomial.derivative qR) = 0 := by
        have haev_R : Polynomial.aeval (y : ℂ) (Polynomial.derivative qR) =
            Complex.ofReal ((Polynomial.derivative qR).eval y) :=
          Polynomial.aeval_algHom_apply (Algebra.ofId ℝ ℂ) y (Polynomial.derivative qR)
        rw [haev_R, hy0, Complex.ofReal_zero, mul_zero]
      rw [hrhs0] at hev
      exact (mul_eq_zero.mp hev).resolve_left Complex.I_ne_zero
    -- Count distinct roots of `derivative fC` in `ℂ`: degree is `≤ 2r + 2`, with `2` non-real roots `i*y₁, i*y₂`.
    have hfC_deg : fC.natDegree = 2 * r + 3 :=
      (Polynomial.natDegree_map (algebraMap ℚ ℂ)).trans hdegQ
    have hfC_mon : fC.Monic := by
      have hmonQ : (ex118RatPoly r).Monic := hmonZ.map (algebraMap ℤ ℚ)
      exact hmonQ.map (algebraMap ℚ ℂ)
    have hdfC_deg_le : (Polynomial.derivative fC).natDegree ≤ 2 * r + 2 := by
      have hle := Polynomial.natDegree_derivative_le fC
      omega
    have hdfC_ne0 : Polynomial.derivative fC ≠ 0 := by
      intro h0
      have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * r + 2)) h0
      rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
      have htop : fC.coeff (2 * r + 2 + 1) = 1 := by
        rw [show 2 * r + 2 + 1 = 2 * r + 3 by omega, ← hfC_deg,
          ← Polynomial.leadingCoeff, hfC_mon.leadingCoeff]
      rw [htop, one_mul] at hc
      have hpos : (0 : ℂ) ≠ ((2 * r + 2 : ℕ) + 1 : ℂ) := by
        exact_mod_cast (by omega : 0 ≠ (2 * r + 2) + 1)
      exact hpos hc.symm
    have hdgR_ne0 : Polynomial.derivative gR ≠ 0 := fun h0 => by
      rw [h0, Polynomial.map_zero] at hgR_deriv_map
      exact hdfC_ne0 hgR_deriv_map.symm
    have hdgR_fin : {x : ℝ | (Polynomial.derivative gR).eval x = 0}.Finite := by
      have heq : {x : ℝ | (Polynomial.derivative gR).eval x = 0} =
          ((Polynomial.derivative gR).roots.toFinset : Set ℝ) := by
        ext x
        change (Polynomial.derivative gR).eval x = 0 ↔ _
        simp [Polynomial.mem_roots hdgR_ne0]
      rw [heq]
      exact Finset.finite_toSet _
    have hdgR_le : {x : ℝ | (Polynomial.derivative gR).eval x = 0}.ncard ≤ 2 * r := by
      let realFin : Finset ℂ := hdgR_fin.toFinset.image Complex.ofReal
      let imagFin : Finset ℂ := {Complex.I * (y₁ : ℂ), Complex.I * (y₂ : ℂ)}
      have himag_card : imagFin.card = 2 := by
        refine Finset.card_pair ?_
        intro heq
        have hy_eq : (y₁ : ℂ) = (y₂ : ℂ) := mul_left_cancel₀ Complex.I_ne_zero heq
        have hy_real : y₁ = y₂ := Complex.ofReal_injective hy_eq
        linarith [hy₁Ioo.2, hy₂Ioo.1]
      have hdisj_ri : Disjoint realFin imagFin := by
        rw [Finset.disjoint_left]
        intro z hz_re hz_im
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz_re
        simp only [imagFin, Finset.mem_insert, Finset.mem_singleton] at hz_im
        rcases hz_im with h1 | h2
        · have him := congrArg Complex.im h1
          simp at him
          linarith [hy₁Ioo.2]
        · have him := congrArg Complex.im h2
          simp at him
          linarith [hy₂Ioo.1]
      have hsub_roots : realFin ∪ imagFin ≤ (Polynomial.derivative fC).roots.toFinset := by
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hdfC_ne0, Polynomial.IsRoot.def]
        rcases Finset.mem_union.mp hz with hz_re | hz_im
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz_re
          have hx0 : (Polynomial.derivative gR).eval x = 0 := hdgR_fin.mem_toFinset.mp hx
          rw [← hgR_deriv_map, Polynomial.eval_map, ← Polynomial.aeval_def]
          have haev_x : Polynomial.aeval (x : ℂ) (Polynomial.derivative gR) =
              Complex.ofReal ((Polynomial.derivative gR).eval x) :=
            Polynomial.aeval_algHom_apply (Algebra.ofId ℝ ℂ) x (Polynomial.derivative gR)
          rw [haev_x, hx0, Complex.ofReal_zero]
        · simp only [imagFin, Finset.mem_insert, Finset.mem_singleton] at hz_im
          rcases hz_im with rfl | rfl
          · exact himag_root y₁ hy₁_d
          · exact himag_root y₂ hy₂_d
      have hcard_le_deg : (realFin ∪ imagFin).card ≤ 2 * r + 2 :=
        calc (realFin ∪ imagFin).card
            ≤ (Polynomial.derivative fC).roots.toFinset.card := Finset.card_le_card hsub_roots
          _ ≤ (Polynomial.derivative fC).roots.card := Multiset.toFinset_card_le _
          _ ≤ (Polynomial.derivative fC).natDegree := Polynomial.card_roots' _
          _ ≤ 2 * r + 2 := hdfC_deg_le
      rw [Finset.card_union_of_disjoint hdisj_ri, himag_card,
        Finset.card_image_of_injective _ Complex.ofReal_injective,
        ← Set.ncard_coe_finset, hdgR_fin.coe_toFinset] at hcard_le_deg
      omega
    rw [hset_gR]
    exact ncard_real_roots_le_succ_of_deriv_bound hgR0 hdgR_fin hdgR_le
  have hreal_eq : {x : ℝ | Polynomial.aeval x gQ = 0}.ncard = 2 * r + 1 := by omega
  change {x : ℝ | Polynomial.aeval x gQ = 0}.ncard +
      {z : ℂ | Polynomial.aeval z gQ = 0 ∧ z.im ≠ 0}.ncard = gQ.natDegree at hsum_roots
  have hcomp_eq : {z : ℂ | Polynomial.aeval z gQ = 0 ∧ z.im ≠ 0}.ncard = 2 := by omega
  -- Part 5: Galois group `Σ_{2r+3}` when `Nat.Prime (2 * r + 3)`.
  refine ⟨⟨hdegQ, hzeros_fr, hsign_alt⟩, hodd_bound, ⟨hirrZ, hirrQ⟩, ⟨hreal_eq, hcomp_eq⟩,
    fun hp L _ _ hsfL => ?_⟩
  have hreal_sub2 : {x : ℝ | Polynomial.aeval x gQ = 0}.ncard = (2 * r + 3) - 2 := by omega
  obtain ⟨hbij, hiso, _, _⟩ := theorem_11_7 hirrQ hp hgQ_deg hreal_sub2 hcomp_eq L hsfL
  exact ⟨hbij, hiso⟩

/-! ## §11.4 The fundamental theorem of Galois theory (printed pp. 97–99, PDF pp. 105–107) -/

/-- Canonical promotion of a subfield `M : Subfield L` satisfying `K₀ ≤ M` to an
`IntermediateField K₀ L` without introducing a duplicate `Algebra` diamond on `Subfield L`. -/
def subfieldToIntermediateField {L : Type u} [Field L] {K₀ M : Subfield L} (h : K₀ ≤ M) :
    IntermediateField K₀ L :=
  { M with algebraMap_mem' := fun x => h x.2 }

@[simp]
theorem mem_subfieldToIntermediateField_iff {L : Type u} [Field L] {K₀ M : Subfield L}
    (h : K₀ ≤ M) {x : L} :
    x ∈ subfieldToIntermediateField h ↔ x ∈ M := Iff.rfl

@[simp]
theorem coe_subfieldToIntermediateField {L : Type u} [Field L] {K₀ M : Subfield L}
    (h : K₀ ≤ M) :
    (subfieldToIntermediateField h : Set L) = (M : Set L) := rfl

/-- The fixed-field map `φ : {H ≤ G} → {M : Subfield L // K₀ ≤ M}` of **Theorem 11.8 (i)**
(§11.4, printed p. 97 / PDF p. 105), where `G = Γ(L:K)` and `K₀ = φ(G)`. -/
def garlingFTGPhi {L : Type u} [Field L] (K : Subfield L) :
    {H : Subgroup (GarlingAut L) // H ≤ garlingGamma K} →
      {M : Subfield L // garlingPhi (garlingGamma K : Set (GarlingAut L)) ≤ M} :=
  fun H => ⟨garlingPhi (H.1 : Set (GarlingAut L)), garlingPhi_anti H.2⟩

/-- The Galois-group map `γ : {M : Subfield L // K₀ ≤ M} → {H ≤ G}` of **Theorem 11.8 (i)**
(§11.4, printed p. 97 / PDF p. 105), using `γ(K₀) = γ(φ(γ(K))) = γ(K)` (`Theorem 11.1 (iv)`). -/
def garlingFTGGamma {L : Type u} [Field L] (K : Subfield L) :
    {M : Subfield L // garlingPhi (garlingGamma K : Set (GarlingAut L)) ≤ M} →
      {H : Subgroup (GarlingAut L) // H ≤ garlingGamma K} :=
  fun M => ⟨garlingGamma M.1,
    (garlingGamma_anti M.2).trans (le_of_eq (theorem_11_1 K ∅).2.2.2)⟩

/-- Conjugation formula `γ(σ(M)) = σ γ(M) σ⁻¹` from the proof of **Theorem 11.8 (ii)**
(§11.4, printed p. 97 / PDF p. 105). -/
theorem garlingGamma_map_subfield {L : Type u} [Field L] (M : Subfield L) (σ : GarlingAut L) :
    garlingGamma (M.map σ.toRingHom) =
      Subgroup.map (MulAut.conj σ).toMonoidHom (garlingGamma M) := by
  ext τ
  rw [mem_garlingGamma_iff, Subgroup.mem_map]
  constructor
  · intro hτ
    refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
    · rw [mem_garlingGamma_iff]
      intro m hm
      have hσm : σ m ∈ M.map σ.toRingHom := ⟨m, hm, rfl⟩
      have h1 : τ (σ m) = σ m := hτ (σ m) hσm
      change σ.symm (τ (σ m)) = m
      rw [h1, σ.symm_apply_apply]
    · change σ * (σ⁻¹ * τ * σ) * σ⁻¹ = τ
      group
  · rintro ⟨u, hu, rfl⟩ m ⟨m₀, hm₀, rfl⟩
    change (σ * u * σ⁻¹) (σ m₀) = σ m₀
    have h1 : (σ * u * σ⁻¹) (σ m₀) = σ (u (σ.symm (σ m₀))) := rfl
    rw [h1, σ.symm_apply_apply, hu m₀ hm₀]

/-- Normal-subgroup stability of `φ(H)` under `G`: if `H ≤ G` is normal in `G`, then every `σ ∈ G`
maps `φ(H)` into `φ(H)`. -/
theorem garlingPhi_stable_of_normal {L : Type u} [Field L] (K : Subfield L)
    {H : Subgroup (GarlingAut L)} (hH : H ≤ garlingGamma K)
    (hN : (H.subgroupOf (garlingGamma K)).Normal)
    (σ : garlingGamma K) {x : L} (hx : x ∈ garlingPhi (H : Set (GarlingAut L))) :
    σ.1 x ∈ garlingPhi (H : Set (GarlingAut L)) := by
  intro τ hτ
  have hτ_sub : (⟨τ, hH hτ⟩ : garlingGamma K) ∈ H.subgroupOf (garlingGamma K) :=
    Subgroup.mem_subgroupOf.mpr hτ
  have hconj : σ⁻¹ * ⟨τ, hH hτ⟩ * (σ⁻¹)⁻¹ ∈ H.subgroupOf (garlingGamma K) :=
    hN.conj_mem _ hτ_sub σ⁻¹
  have hconj_H : σ.1⁻¹ * τ * σ.1 ∈ H := by
    simpa [Subgroup.mem_subgroupOf] using hconj
  have hfix : (σ.1⁻¹ * τ * σ.1) x = x := hx _ hconj_H
  have hsymm : σ.1.symm (τ (σ.1 x)) = x := hfix
  have happ := congrArg σ.1 hsymm
  rwa [σ.1.apply_symm_apply] at happ

/-- The restriction homomorphism `σ ↦ σ|_{φ(H)}` from `G = Γ(L:K)` to `Γ(φ(H):K₀)` of
**Theorem 11.8 (iii)** (§11.4, printed p. 97 / PDF p. 105) when `H ◁ G`. -/
def garlingFTGRestrictionHom {L : Type u} [Field L] (K : Subfield L)
    {H : Subgroup (GarlingAut L)} (hH : H ≤ garlingGamma K)
    (hN : (H.subgroupOf (garlingGamma K)).Normal) :
    garlingGamma K →* GarlingGaloisGroup
      (garlingPhi (garlingGamma K : Set (GarlingAut L)))
      (subfieldToIntermediateField (garlingPhi_anti hH)) where
  toFun σ :=
    { toFun := fun x => ⟨σ.1 x.1, garlingPhi_stable_of_normal K hH hN σ x.2⟩
      invFun := fun x => ⟨(σ⁻¹).1 x.1, garlingPhi_stable_of_normal K hH hN σ⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (σ.1.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (σ.1.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul σ.1 x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add σ.1 x.1 y.1)
      commutes' := fun k => Subtype.ext (k.2 σ.1 σ.2) }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[simp]
theorem garlingFTGRestrictionHom_apply_coe {L : Type u} [Field L] (K : Subfield L)
    {H : Subgroup (GarlingAut L)} (hH : H ≤ garlingGamma K)
    (hN : (H.subgroupOf (garlingGamma K)).Normal)
    (σ : garlingGamma K)
    (x : subfieldToIntermediateField (garlingPhi_anti hH)) :
    (garlingFTGRestrictionHom K hH hN σ x : L) = σ.1 x.1 := rfl

/-- **Theorem 11.8** (*The fundamental theorem of Galois theory*, §11.4, printed p. 97 / PDF p. 105;
proof pp. 97–98 / PDF pp. 105–106):
*"Suppose that `L : K` is finite. Let `G = Γ(L:K)`, and let `K₀ = φ(G)`. If `L : M : K₀`, let
`γ(M) = Γ(L, M)` [sic: `:`].
(i) The map `φ` is a one–one map from the set of subgroups of `G` onto the set of fields `M`
intermediate between `L` and `K₀`. `γ` is the inverse map.
(ii) A subgroup `H` of `G` is normal if and only if `φ(H) : K₀` is a normal extension.
(iii) Suppose that `H ◁ G`. If `σ ∈ G`, `σ|_{φ(H)} ∈ Γ(φ(H), K₀)` [sic: `:`]. The map
`σ → σ|_{φ(H)}` is a homomorphism of `G` onto `Γ(φ(H), K₀))` [sic: `:` and extra `)`], with
kernel `H`. Thus `Γ(φ(H):K₀) ≅ G / H`."*

*(Printed p. 97 comma/parenthesis slips `Γ(L, M)` and `Γ(φ(H), K₀))` normalized to `Γ(L:M)` and
`Γ(φ(H):K₀)`; documented in `PROGRESS.md`.)* -/
theorem theorem_11_8 {L : Type u} [Field L] (K : Subfield L) (hfin : IsFiniteExtension K L) :
    let G := garlingGamma K
    let K₀ := garlingPhi (G : Set (GarlingAut L))
    -- (i) `φ` and `γ` are mutually inverse order-reversing bijections between `{H ≤ G}` and `{M // K₀ ≤ M}`
    (Function.LeftInverse (garlingFTGGamma K) (garlingFTGPhi K) ∧
      Function.RightInverse (garlingFTGGamma K) (garlingFTGPhi K) ∧
      Function.Bijective (garlingFTGPhi K) ∧
      (∀ H₁ H₂ : {H : Subgroup (GarlingAut L) // H ≤ G},
        H₁ ≤ H₂ ↔ garlingFTGPhi K H₂ ≤ garlingFTGPhi K H₁)) ∧
    -- (ii) `H ◁ G` iff `φ(H) : K₀` is a normal extension
    (∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G),
      (H.subgroupOf G).Normal ↔
        IsGarlingNormal K₀ (subfieldToIntermediateField (garlingPhi_anti hH))) ∧
    -- (iii) When `H ◁ G`, restriction `G →* Γ(φ(H):K₀)` is surjective with kernel `H`, giving `Γ(φ(H):K₀) ≃* G ⧸ H`
    (∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G) (hN : (H.subgroupOf G).Normal),
      Function.Surjective (garlingFTGRestrictionHom K hH hN) ∧
      (garlingFTGRestrictionHom K hH hN).ker = H.subgroupOf G ∧
      Nonempty (GarlingGaloisGroup K₀ (subfieldToIntermediateField (garlingPhi_anti hH)) ≃*
        (G ⧸ H.subgroupOf G))) := by
  intro G K₀
  have _ : Finite G := finite_garlingGamma_of_isFiniteExtension K hfin
  have h113_G := theorem_11_3 G
  have hfin_K₀L : IsFiniteExtension K₀ L := h113_G.1
  have hG_eq_K₀ : G = garlingGamma K₀ := h113_G.2.2.2.1
  have hgal_K₀L : IsGarlingGaloisExtension K₀ L := h113_G.2.2.2.2
  -- Part (i): LeftInverse and RightInverse of `garlingFTGGamma K` and `garlingFTGPhi K`.
  have hleft : Function.LeftInverse (garlingFTGGamma K) (garlingFTGPhi K) := by
    intro H
    apply Subtype.ext
    have _ : Finite H.1 := Finite.of_injective (Subgroup.inclusion H.2) (Subgroup.inclusion_injective H.2)
    exact (theorem_11_3 H.1).2.2.2.1.symm
  have hright : Function.RightInverse (garlingFTGGamma K) (garlingFTGPhi K) := by
    intro M
    apply Subtype.ext
    let M_int : IntermediateField K₀ L := subfieldToIntermediateField M.2
    have _ : Module.Finite K₀ L := (isFiniteExtension_iff_moduleFinite K₀ L).mp hfin_K₀L
    have _ : Module.Finite M_int L := Module.Finite.of_restrictScalars_finite K₀ M_int L
    have hfin_Mint : IsFiniteExtension M_int L :=
      (isFiniteExtension_iff_moduleFinite M_int L).mpr inferInstance
    have hnorm_Mint : IsGarlingNormal M_int L :=
      corollary_3_to_theorem_9_1 hgal_K₀L.2.1 M_int
    have hsep_Mint : IsGarlingSeparableExtension M_int L :=
      (theorem_10_1 hgal_K₀L.2.2 M_int).1
    have hgal_Mint : IsGarlingGaloisExtension M_int L := ⟨hfin_Mint, hnorm_Mint, hsep_Mint⟩
    -- Transport `IsGarlingGaloisExtension M_int L` to `M.1 : Subfield L` (`M_int` and `M.1` have the same carrier).
    let eM : M_int ≃+* M.1 := RingEquiv.refl _
    have heM_smul : ∀ (c : M_int) (x : L), (eM c) • x = c • x := fun _ _ => rfl
    let b1 := Module.finBasis M_int L
    let b2 : Module.Basis (Fin (Module.finrank M_int L)) M.1 L := b1.mapCoeffs eM heM_smul
    have hmod_M1 : Module.Finite M.1 L := Module.Finite.of_basis b2
    have hfin_M1 : IsFiniteExtension M.1 L :=
      (isFiniteExtension_iff_moduleFinite M.1 L).mpr hmod_M1
    have hdeg_M : Module.finrank M.1 L = Module.finrank M_int L := by
      rw [Module.finrank_eq_card_basis b2, Fintype.card_fin]
    let eAut : (L ≃ₐ[M_int] L) ≃ (L ≃ₐ[M.1] L) :=
      { toFun := fun σ => { σ.toRingEquiv with commutes' := fun x => σ.commutes x }
        invFun := fun τ => { τ.toRingEquiv with commutes' := fun x => τ.commutes x }
        left_inv := fun σ => by ext x; rfl
        right_inv := fun τ => by ext x; rfl }
    have hcard_M : Nat.card (L ≃ₐ[M.1] L) = Module.finrank M.1 L := by
      rw [← Nat.card_congr eAut, hdeg_M]
      exact (theorem_10_4_algEquiv hfin_Mint).1 hgal_Mint
    have hgal_M1 : IsGarlingGaloisExtension M.1 L := by
      by_contra hng
      have hlt := (theorem_10_4_algEquiv hfin_M1).2 hng
      omega
    exact ((theorem_11_4 M.1 hfin_M1).1 hgal_M1).2.2.symm
  have hbij : Function.Bijective (garlingFTGPhi K) := ⟨hleft.injective, hright.surjective⟩
  have hord : ∀ H₁ H₂ : {H : Subgroup (GarlingAut L) // H ≤ G},
      H₁ ≤ H₂ ↔ garlingFTGPhi K H₂ ≤ garlingFTGPhi K H₁ := by
    intro H₁ H₂
    constructor
    · intro h12
      exact garlingPhi_anti h12
    · intro h21
      have hγ : garlingFTGGamma K (garlingFTGPhi K H₁) ≤ garlingFTGGamma K (garlingFTGPhi K H₂) :=
        garlingGamma_anti h21
      rwa [hleft H₁, hleft H₂] at hγ
  -- Part (ii): `H ◁ G` iff `φ(H) : K₀` is normal (`Theorem 9.2` + `garlingGamma_map_subfield`).
  have hii : ∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G),
      (H.subgroupOf G).Normal ↔
        IsGarlingNormal K₀ (subfieldToIntermediateField (garlingPhi_anti hH)) := by
    intro H hH
    let M_H : IntermediateField K₀ L := subfieldToIntermediateField (garlingPhi_anti hH)
    have hH_gamma : garlingGamma (garlingPhi (H : Set (GarlingAut L))) = H :=
      congrArg Subtype.val (hleft ⟨H, hH⟩)
    rw [(theorem_9_2 hfin_K₀L hgal_K₀L.2.1 M_H).2.2]
    constructor
    · intro hN σAlg
      have hσ_K₀ : σAlg.toRingEquiv ∈ garlingGamma K₀ :=
        (garlingGaloisGroupSubfieldMulEquiv K₀ σAlg).2
      have hσG : σAlg.toRingEquiv ∈ G := hG_eq_K₀ ▸ hσ_K₀
      exact Set.Subset.antisymm
        (by rintro _ ⟨x, hx, rfl⟩; exact garlingPhi_stable_of_normal K hH hN ⟨σAlg.toRingEquiv, hσG⟩ hx)
        (fun x hx => ⟨σAlg.symm x,
          garlingPhi_stable_of_normal K hH hN ⟨σAlg.symm.toRingEquiv, G.inv_mem hσG⟩ hx,
          σAlg.apply_symm_apply x⟩)
    · intro hstable
      refine ⟨fun u hu g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      let σAlg : L ≃ₐ[K₀] L :=
        (garlingGaloisGroupSubfieldMulEquiv K₀).symm ⟨g.1, hG_eq_K₀ ▸ g.2⟩
      have himg : (g.1 : L → L) '' (garlingPhi (H : Set (GarlingAut L)) : Set L) =
          (garlingPhi (H : Set (GarlingAut L)) : Set L) := hstable σAlg
      have hmap_sub : (garlingPhi (H : Set (GarlingAut L))).map g.1.toRingHom =
          garlingPhi (H : Set (GarlingAut L)) := by
        ext y
        change y ∈ (g.1 : L → L) '' (garlingPhi (H : Set (GarlingAut L)) : Set L) ↔
          y ∈ (garlingPhi (H : Set (GarlingAut L)) : Set L)
        rw [himg]
      have hconj_eq : Subgroup.map (MulAut.conj g.1).toMonoidHom H = H := by
        calc Subgroup.map (MulAut.conj g.1).toMonoidHom H
            = Subgroup.map (MulAut.conj g.1).toMonoidHom
                (garlingGamma (garlingPhi (H : Set (GarlingAut L)))) := by rw [hH_gamma]
          _ = garlingGamma ((garlingPhi (H : Set (GarlingAut L))).map g.1.toRingHom) :=
                (garlingGamma_map_subfield _ g.1).symm
          _ = garlingGamma (garlingPhi (H : Set (GarlingAut L))) := by rw [hmap_sub]
          _ = H := hH_gamma
      have hmem_map : g.1 * u.1 * g.1⁻¹ ∈ Subgroup.map (MulAut.conj g.1).toMonoidHom H :=
        ⟨u.1, hu, rfl⟩
      rwa [hconj_eq] at hmem_map
  -- Part (iii): Surjectivity and kernel of `garlingFTGRestrictionHom`, and `Γ(φ(H):K₀) ≃* G ⧸ H`.
  have hiii : ∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G) (hN : (H.subgroupOf G).Normal),
      Function.Surjective (garlingFTGRestrictionHom K hH hN) ∧
      (garlingFTGRestrictionHom K hH hN).ker = H.subgroupOf G ∧
      Nonempty (GarlingGaloisGroup K₀ (subfieldToIntermediateField (garlingPhi_anti hH)) ≃*
        (G ⧸ H.subgroupOf G)) := by
    intro H hH hN
    let M_H : IntermediateField K₀ L := subfieldToIntermediateField (garlingPhi_anti hH)
    have hnorm_MH : IsGarlingNormal K₀ M_H := (hii H hH).mp hN
    have _ : Normal K₀ M_H := (isGarlingNormal_iff K₀ M_H).mp hnorm_MH
    have _ : Normal K₀ L := (isGarlingNormal_iff K₀ L).mp hgal_K₀L.2.1
    have hH_gamma : garlingGamma (garlingPhi (H : Set (GarlingAut L))) = H :=
      congrArg Subtype.val (hleft ⟨H, hH⟩)
    have hsurj : Function.Surjective (garlingFTGRestrictionHom K hH hN) := by
      intro ρ
      let σAlg : L ≃ₐ[K₀] L := ρ.liftNormal L
      have hσ_K₀ : σAlg.toRingEquiv ∈ garlingGamma K₀ :=
        (garlingGaloisGroupSubfieldMulEquiv K₀ σAlg).2
      let σG : G := ⟨σAlg.toRingEquiv, hG_eq_K₀ ▸ hσ_K₀⟩
      refine ⟨σG, ?_⟩
      ext x
      exact ρ.liftNormal_commutes L x
    have hker : (garlingFTGRestrictionHom K hH hN).ker = H.subgroupOf G := by
      ext σ
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        rw [← hH_gamma, mem_garlingGamma_iff]
        intro m hm
        exact congrArg (fun f => (f ⟨m, hm⟩ : L)) h1
      · intro hmem
        rw [← hH_gamma, mem_garlingGamma_iff] at hmem
        ext x
        exact hmem x.1 x.2
    let eQuot : (G ⧸ H.subgroupOf G) ≃* GarlingGaloisGroup K₀ M_H :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective (garlingFTGRestrictionHom K hH hN) hsurj)
    exact ⟨hsurj, hker, ⟨eQuot.symm⟩⟩
  exact ⟨⟨hleft, hright, hbij, hord⟩, hii, hiii⟩

/-- `[Algebra K L]` companion to **Theorem 11.8** (§11.4, p. 97), viewing `K` as
`(algebraMap K L).fieldRange : Subfield L`. -/
theorem theorem_11_8_algebra (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    let K_sub := (algebraMap K L).fieldRange
    let G := garlingGamma K_sub
    let K₀ := garlingPhi (G : Set (GarlingAut L))
    Function.LeftInverse (garlingFTGGamma K_sub) (garlingFTGPhi K_sub) ∧
    Function.RightInverse (garlingFTGGamma K_sub) (garlingFTGPhi K_sub) ∧
    Function.Bijective (garlingFTGPhi K_sub) ∧
    (∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G),
      (H.subgroupOf G).Normal ↔
        IsGarlingNormal K₀ (subfieldToIntermediateField (garlingPhi_anti hH))) ∧
    (∀ (H : Subgroup (GarlingAut L)) (hH : H ≤ G) (hN : (H.subgroupOf G).Normal),
      Function.Surjective (garlingFTGRestrictionHom K_sub hH hN) ∧
      (garlingFTGRestrictionHom K_sub hH hN).ker = H.subgroupOf G ∧
      Nonempty (GarlingGaloisGroup K₀ (subfieldToIntermediateField (garlingPhi_anti hH)) ≃*
        (G ⧸ H.subgroupOf G))) := by
  intro K_sub G K₀
  let eK : K ≃+* K_sub := RingEquiv.ofBijective (algebraMap K L).rangeRestrict
    ⟨fun a b hab => (algebraMap K L).injective (congrArg Subtype.val hab),
     fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩
  have heK_smul : ∀ (c : K) (x : L), (eK c) • x = c • x := fun c x => by
    change (algebraMap K L c) * x = c • x
    rw [Algebra.smul_def]
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  let b1 := Module.finBasis K L
  let b2 : Module.Basis (Fin (Module.finrank K L)) K_sub L := b1.mapCoeffs eK heK_smul
  have hfin_sub : IsFiniteExtension K_sub L :=
    (isFiniteExtension_iff_moduleFinite K_sub L).mpr (Module.Finite.of_basis b2)
  obtain ⟨⟨hl, hr, hb, _⟩, hii, hiii⟩ := theorem_11_8 K_sub hfin_sub
  exact ⟨hl, hr, hb, hii, hiii⟩

/-! ### §11.4 Exercises 11.9–11.12 (printed pp. 98–99, PDF pp. 106–107) -/

/-- Subfield-form solution to **Exercise 11.9** (§11.4, printed p. 98 / PDF p. 106):
for any finite group `G : Type u`, letting `L = FractionRing (MvPolynomial G ℚ) : Type u` with `G`
permuting the variables by left multiplication and `K = φ(G) : Subfield L`, `L : K` is a Galois
extension in the **same** universe `Type u` with `Γ(L:K) ≃* G`. -/
theorem exercise_11_9_subfield (G : Type u) [Group G] [Finite G] :
    ∃ (L : Type u) (_ : Field L) (K : Subfield L),
      IsGarlingGaloisExtension K L ∧
      Nonempty (garlingGamma K ≃* G) ∧
      Nonempty (GarlingGaloisGroup K L ≃* G) := by
  let R := MvPolynomial G ℚ
  let L := FractionRing R
  let autR : G →* (R ≃+* R) :=
    { toFun := fun g => (MvPolynomial.renameEquiv ℚ (MulAction.toPermHom G G g)).toRingEquiv
      map_one' := by
        refine RingEquiv.ext fun p => ?_
        change MvPolynomial.rename (MulAction.toPermHom G G 1) p = p
        rw [map_one]
        exact MvPolynomial.rename_id_apply p
      map_mul' := fun g₁ g₂ => by
        refine RingEquiv.ext fun p => ?_
        change (MvPolynomial.rename (MulAction.toPermHom G G (g₁ * g₂))) p =
          (MvPolynomial.rename (MulAction.toPermHom G G g₁))
            ((MvPolynomial.rename (MulAction.toPermHom G G g₂)) p)
        have hfun : (⇑(MulAction.toPermHom G G (g₁ * g₂)) : G → G) =
            ⇑(MulAction.toPermHom G G g₁) ∘ ⇑(MulAction.toPermHom G G g₂) :=
          funext fun x => mul_assoc g₁ g₂ x
        rw [MvPolynomial.rename_rename, hfun] }
  let ψ : G →* GarlingAut L := (IsFractionRing.ringEquivOfRingEquivHom R L).comp autR
  have hψ_inj : Function.Injective ψ := by
    intro g₁ g₂ h
    have haut : autR g₁ = autR g₂ :=
      IsFractionRing.ringEquivOfRingEquivHom_injective R L h
    have hX := congrArg (fun e : R ≃+* R => e (MvPolynomial.X (1 : G))) haut
    change MvPolynomial.rename (MulAction.toPermHom G G g₁) (MvPolynomial.X (1 : G)) =
      MvPolynomial.rename (MulAction.toPermHom G G g₂) (MvPolynomial.X (1 : G)) at hX
    rw [MvPolynomial.rename_X, MvPolynomial.rename_X] at hX
    have hg12 : MulAction.toPermHom G G g₁ (1 : G) = MulAction.toPermHom G G g₂ (1 : G) :=
      MvPolynomial.X_injective (R := ℚ) hX
    simpa [MulAction.toPermHom_apply] using hg12
  let H : Subgroup (GarlingAut L) := ψ.range
  have _ : Finite H := Set.finite_range ψ
  let eGH : G ≃* H := MulEquiv.ofBijective ψ.rangeRestrict
    ⟨fun a b hab => hψ_inj (congrArg Subtype.val hab), ψ.rangeRestrict_surjective⟩
  let K : Subfield L := garlingPhi (H : Set (GarlingAut L))
  have h113 := theorem_11_3 H
  have hH_eq : H = garlingGamma K := h113.2.2.2.1
  let eGammaG : garlingGamma K ≃* G := (MulEquiv.subgroupCongr hH_eq.symm).trans eGH.symm
  let eGalG : GarlingGaloisGroup K L ≃* G :=
    (garlingGaloisGroupSubfieldMulEquiv K).trans eGammaG
  exact ⟨L, inferInstance, K, h113.2.2.2.2, ⟨eGammaG⟩, ⟨eGalG⟩⟩

/-- **Exercise 11.9** (§11.4, printed p. 98 / PDF p. 106):
*"Given a finite group `G` show that there exists a Galois extension `L : K` such that
`Γ(L:K) ≅ G`."* -/
theorem exercise_11_9 (G : Type u) [Group G] [Finite G] :
    ∃ (K L : Type u) (_ : Field K) (_ : Field L) (_ : Algebra K L),
      IsGarlingGaloisExtension K L ∧
      Nonempty (GarlingGaloisGroup K L ≃* G) := by
  obtain ⟨L, instFL, K, hgal, _, ⟨eG⟩⟩ := exercise_11_9_subfield G
  let _ : Field L := instFL
  exact ⟨K, L, inferInstance, instFL, inferInstance, hgal, ⟨eG⟩⟩

/-- **Exercise 11.10** (§11.4, printed pp. 98–99 / PDF pp. 106–107):
*"Suppose that `K₁` and `K₂` are subfields of a field `L` such that `L : K₁` and `L : K₂` are both
Galois extensions, with Galois groups `G₁` and `G₂` respectively. Show that `L : K₁ ∩ K₂` is a
Galois extension if and only if `G`, the group generated by `G₁` and `G₂`, is finite, and that if
this is so then `G = Γ(L : K₁ ∩ K₂)`."*

Proved directly from `Theorem 11.1`, `Corollary` [to `Theorem 11.1`], `Theorem 11.3`, and
`Theorem 11.4`. -/
theorem exercise_11_10 {L : Type u} [Field L] (K₁ K₂ : Subfield L)
    (hgal₁ : IsGarlingGaloisExtension K₁ L) (hgal₂ : IsGarlingGaloisExtension K₂ L) :
    let G₁ := garlingGamma K₁
    let G₂ := garlingGamma K₂
    let G := Subgroup.closure ((G₁ : Set (GarlingAut L)) ∪ (G₂ : Set (GarlingAut L)))
    G = G₁ ⊔ G₂ ∧
    (IsGarlingGaloisExtension (K₁ ⊓ K₂ : Subfield L) L ↔ Finite G) ∧
    (IsGarlingGaloisExtension (K₁ ⊓ K₂ : Subfield L) L → G = garlingGamma (K₁ ⊓ K₂)) := by
  intro G₁ G₂ G
  have hsup : G = G₁ ⊔ G₂ := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro σ (h1 | h2)
      · exact (le_sup_left : G₁ ≤ G₁ ⊔ G₂) h1
      · exact (le_sup_right : G₂ ≤ G₁ ⊔ G₂) h2
    · exact sup_le
        (fun σ h1 => Subgroup.subset_closure (Or.inl h1))
        (fun σ h2 => Subgroup.subset_closure (Or.inr h2))
  have hK₁ : K₁ = garlingPhi (G₁ : Set (GarlingAut L)) :=
    ((theorem_11_4 K₁ hgal₁.1).1 hgal₁).2.2
  have hK₂ : K₂ = garlingPhi (G₂ : Set (GarlingAut L)) :=
    ((theorem_11_4 K₂ hgal₂.1).1 hgal₂).2.2
  have hphi_G : garlingPhi (G : Set (GarlingAut L)) = K₁ ⊓ K₂ := by
    rw [← corollary_to_theorem_11_1 ((G₁ : Set (GarlingAut L)) ∪ (G₂ : Set (GarlingAut L)))]
    ext x
    simp only [mem_garlingPhi_iff, Set.mem_union, Subfield.mem_inf]
    rw [hK₁, hK₂]
    simp only [mem_garlingPhi_iff]
    exact ⟨fun h => ⟨fun σ h1 => h σ (Or.inl h1), fun σ h2 => h σ (Or.inr h2)⟩,
      fun ⟨h1, h2⟩ σ hσ => hσ.elim (h1 σ) (h2 σ)⟩
  have hfin_imp : Finite G →
      IsGarlingGaloisExtension (K₁ ⊓ K₂ : Subfield L) L ∧ G = garlingGamma (K₁ ⊓ K₂) := by
    intro hfinG
    have h113 := theorem_11_3 G
    have hgal_phi : IsGarlingGaloisExtension (garlingPhi (G : Set (GarlingAut L))) L :=
      h113.2.2.2.2
    have hG_eq : G = garlingGamma (garlingPhi (G : Set (GarlingAut L))) := h113.2.2.2.1
    rw [hphi_G] at hgal_phi hG_eq
    exact ⟨hgal_phi, hG_eq⟩
  have hgal_imp_fin : IsGarlingGaloisExtension (K₁ ⊓ K₂ : Subfield L) L → Finite G := by
    intro hgal_inf
    have hle : G ≤ garlingGamma (K₁ ⊓ K₂) := by
      rw [← hphi_G]
      exact (theorem_11_1 ⊥ (G : Set (GarlingAut L))).1
    have _ : Finite (garlingGamma (K₁ ⊓ K₂)) :=
      finite_garlingGamma_of_isFiniteExtension (K₁ ⊓ K₂) hgal_inf.1
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  exact ⟨hsup, ⟨hgal_imp_fin, fun hf => (hfin_imp hf).1⟩,
    fun hg => (hfin_imp (hgal_imp_fin hg)).2⟩

/-- Inline definition of a *Sylow `p`-subgroup* in **Exercise 11.11**
(§11.4, printed p. 99 / PDF p. 107):
*"If `G` is a finite group and `|G| = p^r q` where `p` is a prime which does not divide `q` then
... (A subgroup of order `p^r` is called a Sylow `p`-subgroup.)"* -/
def IsGarlingSylowSubgroup {G : Type*} [Group G] (p : ℕ) (P : Subgroup G) : Prop :=
  Nat.Prime p ∧ ∃ (r q : ℕ), Nat.card G = p ^ r * q ∧ ¬ p ∣ q ∧ Nat.card P = p ^ r

/-- Inline group-theory fact in **Exercise 11.11** (§11.4, printed p. 99 / PDF p. 107):
*"If `G` is a finite group and `|G| = p^r q` where `p` is a prime which does not divide `q` then
`G` has subgroups of order `p^s` for `1 ≤ s ≤ r`."* -/
theorem sylow_prime_power_subgroups {G : Type*} [Group G] [Finite G]
    {p r q : ℕ} (hp : Nat.Prime p) (hcard : Nat.card G = p ^ r * q) (_hndvd : ¬ p ∣ q)
    {s : ℕ} (_hs1 : 1 ≤ s) (hsr : s ≤ r) :
    ∃ P : Subgroup G, Nat.card P = p ^ s := by
  have _ : Fact p.Prime := ⟨hp⟩
  exact Sylow.exists_subgroup_card_pow_prime p ((pow_dvd_pow p hsr).trans ⟨q, hcard⟩)

/-- Constructive algebraic-closure criterion via `Theorem 7.2` (with zero `IsAlgClosed` dependency):
if `L : K` is an algebraic extension and every irreducible polynomial `f ∈ K[X]` splits over `L`,
then `L` is algebraically closed (`IsGarlingAlgebraicallyClosed L`). -/
theorem isGarlingAlgebraicallyClosed_of_irreducible_base_splits
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L)
    (hsp : ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f) :
    IsGarlingAlgebraicallyClosed L := by
  have hroot_irr : ∀ q : L[X], Irreducible q → ∃ r : L, q.eval r = 0 := by
    intro q hq
    obtain ⟨E, instFE, instALE, α, _, halgLE, _, _, haeval⟩ := theorem_7_2 hq rfl
    let _ : Field E := instFE
    let _ : Algebra L E := instALE
    let _ : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
    have _ : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have _ : Algebra.IsAlgebraic K L := (isAlgebraicExtension_iff K L).mp halg
    have _ : Algebra.IsAlgebraic L E := (isAlgebraicExtension_iff L E).mp halgLE
    have _ : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.trans K L E
    have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
    obtain ⟨n, c, β, hexp⟩ := hsp (minpoly K α) (minpoly.irreducible hint)
    have hc0 : c ≠ 0 := (garlingSplitsExplicit_props (minpoly.ne_zero hint) hexp).2.1
    have hmap_min : ((minpoly K α).map (algebraMap K L)).map (algebraMap L E) =
        Polynomial.C (algebraMap L E (algebraMap K L c)) *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (algebraMap L E (β i))) := by
      rw [hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => by simp
    have hev0 : (((minpoly K α).map (algebraMap K L)).map (algebraMap L E)).eval α = 0 := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L E,
        Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval K α]
    rw [hmap_min, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hev0
    have hcE0 : algebraMap L E (algebraMap K L c) ≠ 0 :=
      (map_ne_zero (algebraMap L E)).mpr ((map_ne_zero (algebraMap K L)).mpr hc0)
    have hprod0 : (∏ i : Fin n, (Polynomial.X - Polynomial.C (algebraMap L E (β i))).eval α) = 0 :=
      (mul_eq_zero.mp hev0).resolve_left hcE0
    obtain ⟨i, _, hi0⟩ := Finset.prod_eq_zero_iff.mp hprod0
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi0
    refine ⟨β i, (algebraMap L E).injective ?_⟩
    rw [map_zero]
    change (Algebra.ofId L E) (Polynomial.aeval (β i) q) = 0
    rw [← Polynomial.aeval_algHom_apply (Algebra.ofId L E) (β i) q]
    change Polynomial.aeval (algebraMap L E (β i)) q = 0
    rwa [← hi0]
  intro g
  rw [garlingSplitsOver_iff_splits]
  have hmain : ∀ d : ℕ, ∀ P : L[X], P.natDegree = d → P.Splits := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hdeg
      by_cases hP0 : P = 0
      · subst hP0; exact Polynomial.Splits.zero
      · by_cases hd0 : d = 0
        · exact Polynomial.Splits.of_natDegree_le_one (by omega)
        · have hnot_unit : ¬ IsUnit P := fun hu => by
            have hz := Polynomial.natDegree_eq_zero_of_isUnit hu
            omega
          obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnot_unit hP0
          obtain ⟨r, hr0⟩ := hroot_irr q hq_irr
          have hlin_dvd : Polynomial.X - Polynomial.C r ∣ P :=
            (Polynomial.dvd_iff_isRoot.mpr hr0).trans hq_dvd
          obtain ⟨P₁, hPP₁⟩ := hlin_dvd
          have hlin0 : (Polynomial.X - Polynomial.C r : L[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero r
          have hP₁0 : P₁ ≠ 0 := fun h0 => hP0 (by rw [hPP₁, h0, mul_zero])
          have hdeg_sum : d = 1 + P₁.natDegree := by
            rw [← hdeg, hPP₁, Polynomial.natDegree_mul hlin0 hP₁0, Polynomial.natDegree_X_sub_C]
          have hP₁_sp : P₁.Splits := ih P₁.natDegree (by omega) P₁ rfl
          rw [hPP₁]
          exact Polynomial.Splits.mul (Polynomial.Splits.X_sub_C r) hP₁_sp
  have hg_sp : g.Splits := hmain g.natDegree g rfl
  simpa [Algebra.algebraMap_self, Polynomial.map_id] using hg_sp

/-- No quadratic polynomial in `L[X]` is irreducible when `char L ≠ 2` and every element of `L`
has a square root in `L` (via the quadratic formula). -/
theorem no_irreducible_quadratic_of_sqrt_and_char_ne_two
    {L : Type*} [Field L] (hchar : ringChar L ≠ 2) (hsqrt : ∀ w : L, ∃ u : L, u ^ 2 = w) :
    ¬ ∃ q : L[X], Irreducible q ∧ q.natDegree = 2 := by
  rintro ⟨q, hq_irr, hq_deg⟩
  let a : L := q.coeff 2
  let b : L := q.coeff 1
  let c : L := q.coeff 0
  have ha0 : a ≠ 0 := by
    have hlc : a = q.leadingCoeff := by rw [Polynomial.leadingCoeff, hq_deg]
    rw [hlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq_irr.ne_zero
  have hq_eq : q = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c := by
    rw [q.as_sum_range' 3 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [a, b, c, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one, mul_one]
    ring
  have h2_ne0 : (2 : L) ≠ 0 := by
    intro h20
    have hdvd : ringChar L ∣ 2 := (ringChar.spec L 2).mp (by simpa using h20)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have h10 : ((1 : ℕ) : L) = 0 := (ringChar.spec L 1).mpr (by rw [h1])
      simp at h10
    · exact hchar h2
  obtain ⟨d, hd_sq⟩ := hsqrt (b ^ 2 - 4 * a * c)
  let r : L := (-b + d) / (2 * a)
  have h2a_ne0 : 2 * a ≠ 0 := mul_ne_zero h2_ne0 ha0
  have hr_root : q.eval r = 0 := by
    rw [hq_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, r]
    field_simp [h2_ne0, ha0]
    linear_combination hd_sq
  obtain ⟨s, hqs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
  have hlin0 : (Polynomial.X - Polynomial.C r : L[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero r
  have hs0 : s ≠ 0 := fun h0 => hq_irr.ne_zero (by rw [hqs, h0, mul_zero])
  have hs_deg : s.natDegree = 1 := by
    have hd_sum := congrArg Polynomial.natDegree hqs
    rw [hq_deg, Polynomial.natDegree_mul hlin0 hs0, Polynomial.natDegree_X_sub_C] at hd_sum
    omega
  rcases hq_irr.isUnit_or_isUnit hqs with hu1 | hu2
  · have hz := Polynomial.natDegree_eq_zero_of_isUnit hu1
    rw [Polynomial.natDegree_X_sub_C] at hz; omega
  · have hz := Polynomial.natDegree_eq_zero_of_isUnit hu2
    omega

/-- Explicit complex square-root formula via `Real.sqrt` (with zero `Complex.isAlgClosed` dependency):
every `z ∈ ℂ` has `w ∈ ℂ` with `w ^ 2 = z`. -/
theorem complex_exists_sq_eq (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  let a : ℝ := z.re
  let b : ℝ := z.im
  let r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have habs_le : |a| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg b])
  have hpos_plus : 0 ≤ (r + a) / 2 := by
    have h := neg_abs_le a
    linarith
  have hpos_minus : 0 ≤ (r - a) / 2 := by
    have h := le_abs_self a
    linarith
  let u : ℝ := Real.sqrt ((r + a) / 2)
  let sgn : ℝ := if 0 ≤ b then 1 else -1
  let v : ℝ := sgn * Real.sqrt ((r - a) / 2)
  refine ⟨⟨u, v⟩, ?_⟩
  have hsgn_sq : sgn ^ 2 = 1 := by
    dsimp [sgn]; split_ifs <;> norm_num
  have hu2 : u ^ 2 = (r + a) / 2 := Real.sq_sqrt hpos_plus
  have hv2 : v ^ 2 = (r - a) / 2 := by
    calc v ^ 2 = sgn ^ 2 * (Real.sqrt ((r - a) / 2)) ^ 2 := by ring
      _ = 1 * ((r - a) / 2) := by rw [hsgn_sq, Real.sq_sqrt hpos_minus]
      _ = (r - a) / 2 := one_mul _
  apply Complex.ext
  · simp only [sq, Complex.mul_re]
    change u * u - v * v = a
    calc u * u - v * v = u ^ 2 - v ^ 2 := by ring
      _ = (r + a) / 2 - (r - a) / 2 := by rw [hu2, hv2]
      _ = a := by ring
  · simp only [sq, Complex.mul_im]
    change u * v + v * u = b
    have hmul_sqrt : Real.sqrt ((r + a) / 2) * Real.sqrt ((r - a) / 2) = |b| / 2 := by
      rw [← Real.sqrt_mul hpos_plus]
      have harg : ((r + a) / 2) * ((r - a) / 2) = (b / 2) ^ 2 := by
        calc ((r + a) / 2) * ((r - a) / 2) = (r ^ 2 - a ^ 2) / 4 := by ring
          _ = (a ^ 2 + b ^ 2 - a ^ 2) / 4 := by rw [hr2]
          _ = (b / 2) ^ 2 := by ring
      rw [harg, Real.sqrt_sq_eq_abs, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    calc u * v + v * u
        = sgn * (2 * (Real.sqrt ((r + a) / 2) * Real.sqrt ((r - a) / 2))) := by
            dsimp [u, v]; ring
      _ = sgn * |b| := by rw [hmul_sqrt]; ring
      _ = b := by
            dsimp [sgn]
            split_ifs with hb
            · rw [abs_of_nonneg hb, one_mul]
            · rw [abs_of_neg (lt_of_not_ge hb)]; ring

/-- Elementary Intermediate Value Theorem proof that every odd-degree polynomial `h ∈ ℝ[X]` has a
real root (with zero `Complex.isAlgClosed` dependency). -/
theorem real_odd_natDegree_exists_root (h : ℝ[X]) (hodd : Odd h.natDegree) :
    ∃ x : ℝ, h.eval x = 0 := by
  have hwlog : ∀ P : ℝ[X], Odd P.natDegree → 0 < P.leadingCoeff → ∃ x : ℝ, P.eval x = 0 := by
    intro P hPodd hlc_pos
    let n : ℕ := P.natDegree
    have hn_odd : Odd n := hPodd
    have hn_pos : 1 ≤ n := by
      rcases hn_odd with ⟨k, hk⟩; omega
    let c : ℝ := P.leadingCoeff
    let S : ℝ := ∑ i ∈ Finset.range n, |P.coeff i|
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    let R : ℝ := 1 + S / c
    have hR_ge1 : 1 ≤ R := by
      dsimp [R]
      have hdiv : 0 ≤ S / c := div_nonneg hS_nonneg hlc_pos.le
      linarith
    have hS_lt : S < c * R := by
      have hc0 : c ≠ 0 := hlc_pos.ne'
      have hcR : c * R = c + S := by
        dsimp [R]; field_simp [hc0]
      linarith
    have htail_bound : ∀ x : ℝ, |x| = R →
        |∑ i ∈ Finset.range n, P.coeff i * x ^ i| < c * R ^ n := by
      intro x hxR
      have h1 : |∑ i ∈ Finset.range n, P.coeff i * x ^ i| ≤
          ∑ i ∈ Finset.range n, |P.coeff i| * R ^ (n - 1) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [abs_mul, abs_pow, hxR]
        have hi_le : i ≤ n - 1 := by
          have hi_lt := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR_ge1 hi_le) (abs_nonneg _)
      have h2 : (∑ i ∈ Finset.range n, |P.coeff i| * R ^ (n - 1)) = S * R ^ (n - 1) :=
        (Finset.sum_mul _ _ _).symm
      have hRn1_pos : 0 < R ^ (n - 1) := pow_pos (by linarith) _
      have h3 : S * R ^ (n - 1) < (c * R) * R ^ (n - 1) :=
        mul_lt_mul_of_pos_right hS_lt hRn1_pos
      have h4 : (c * R) * R ^ (n - 1) = c * R ^ n := by
        rw [mul_assoc, ← pow_succ', show n - 1 + 1 = n by omega]
      linarith
    have heval_split : ∀ x : ℝ,
        P.eval x = (∑ i ∈ Finset.range n, P.coeff i * x ^ i) + c * x ^ n := by
      intro x
      rw [Polynomial.eval_eq_sum_range, show P.natDegree = n from rfl, Finset.sum_range_succ]
      rfl
    have hpos_at_R : 0 < P.eval R := by
      have hb := (abs_lt.mp (htail_bound R (abs_of_pos (by linarith)))).1
      rw [heval_split R]
      linarith
    have hneg_at_negR : P.eval (-R) < 0 := by
      have hb := (abs_lt.mp (htail_bound (-R) (by rw [abs_neg, abs_of_pos (by linarith)]))).2
      rw [heval_split (-R), hn_odd.neg_pow]
      linarith
    obtain ⟨x, _, hx0⟩ := exists_Ioo_root_of_mul_neg (a := -R) (b := R) (by linarith)
      (mul_neg_of_neg_of_pos hneg_at_negR hpos_at_R)
    exact ⟨x, hx0⟩
  have hh0 : h ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hodd
    exact Nat.not_odd_zero hodd
  have hlc_ne : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh0
  rcases lt_or_gt_of_ne hlc_ne with hneg | hpos
  · have hdeg_neg : (-h).natDegree = h.natDegree := Polynomial.natDegree_neg h
    have hlc_neg : 0 < (-h).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg]; linarith
    obtain ⟨x, hx⟩ := hwlog (-h) (hdeg_neg ▸ hodd) hlc_neg
    rw [Polynomial.eval_neg, neg_eq_zero] at hx
    exact ⟨x, hx⟩
  · exact hwlog h hodd hpos

/-- Counterexamples for the unbound exponent `n` in **Exercise 11.11 (i)–(ii)**
(§11.4, printed p. 99 / PDF p. 107; see `QUEUE.md`), proved with **zero** `Complex.isAlgClosed`:
for `K = ℝ`, `L = ℂ`, and `f = X² + 1 ∈ ℝ[X]` (`Irreducible f`, `f.natDegree = 2 > 1`) with
splitting field `M = ℂ` over `L = ℂ`:
1. `Nat.card (GarlingGaloisGroup ℝ ℂ) = 2 = 2 ^ 1`, so `¬ ∀ n : ℕ, |G| = 2 ^ n` (universal `n` is false).
2. `|G| = 2 ≠ 2 ^ (f.natDegree)` and `ℂ[X]` has no irreducible quadratic, refuting `n := deg f`. -/
theorem exercise_11_11_unbound_n_counterexamples :
    let f : ℝ[X] := Polynomial.X ^ 2 + 1
    Irreducible f ∧
    IsGarlingSplittingFieldExtension ℂ ℂ (f.map (algebraMap ℝ ℂ)) ∧
    Nat.card (GarlingGaloisGroup ℝ ℂ) = 2 ∧
    (¬ ∀ n : ℕ, Nat.card (GarlingGaloisGroup ℝ ℂ) = 2 ^ n) ∧
    Nat.card (GarlingGaloisGroup ℝ ℂ) ≠ 2 ^ f.natDegree ∧
    (¬ ∃ q : ℂ[X], Irreducible q ∧ q.natDegree = 2) := by
  intro f
  have hf_deg : f.natDegree = 2 := by dsimp [f]; compute_degree!
  have hf_mon : f.Monic := by dsimp [f]; monicity!
  have hf_noroots : ∀ x : ℝ, f.eval x ≠ 0 := by
    intro x
    dsimp [f]; simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    positivity
  have hf_irr : Irreducible f := by
    refine ⟨fun hu => by have hz := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, ?_⟩
    intro a b hab
    by_contra hnot
    push Not at hnot
    obtain ⟨hua, hub⟩ := hnot
    have ha0 : a ≠ 0 := fun h0 => hf_mon.ne_zero (by rw [hab, h0, zero_mul])
    have hb0 : b ≠ 0 := fun h0 => hf_mon.ne_zero (by rw [hab, h0, mul_zero])
    have ha_pos : 0 < a.natDegree := Nat.pos_of_ne_zero fun hz =>
      hua (Polynomial.isUnit_iff.mpr ⟨a.coeff 0, isUnit_iff_ne_zero.mpr fun h0 =>
        ha0 ((Polynomial.eq_C_of_natDegree_eq_zero hz).trans (by rw [h0, map_zero])),
        (Polynomial.eq_C_of_natDegree_eq_zero hz).symm⟩)
    have hb_pos : 0 < b.natDegree := Nat.pos_of_ne_zero fun hz =>
      hub (Polynomial.isUnit_iff.mpr ⟨b.coeff 0, isUnit_iff_ne_zero.mpr fun h0 =>
        hb0 ((Polynomial.eq_C_of_natDegree_eq_zero hz).trans (by rw [h0, map_zero])),
        (Polynomial.eq_C_of_natDegree_eq_zero hz).symm⟩)
    have hsum : 2 = a.natDegree + b.natDegree := by
      rw [← hf_deg, hab, Polynomial.natDegree_mul ha0 hb0]
    have ha1 : a.natDegree = 1 := by omega
    let c1 : ℝ := a.coeff 1
    let c0 : ℝ := a.coeff 0
    have ha_eq : a = Polynomial.C c1 * Polynomial.X + Polynomial.C c0 :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq ha1)
    have hc1_ne : c1 ≠ 0 := by
      dsimp [c1]
      rw [← ha1, ← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr ha0
    have hroot : a.eval (-c0 / c1) = 0 := by
      rw [ha_eq]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      field_simp [hc1_ne]; ring
    exact hf_noroots (-c0 / c1)
      (by rw [hab, Polynomial.eval_mul, hroot, zero_mul])
  have hfC_fac : f.map (algebraMap ℝ ℂ) =
      (Polynomial.X - Polynomial.C Complex.I) * (Polynomial.X - Polynomial.C (-Complex.I)) := by
    have hmap : f.map (algebraMap ℝ ℂ) = Polynomial.X ^ 2 + 1 := by simp [f]
    rw [hmap]
    calc (Polynomial.X ^ 2 + 1 : ℂ[X])
        = Polynomial.X ^ 2 - Polynomial.C (Complex.I * Complex.I) := by
            rw [Complex.I_mul_I, map_neg, map_one, sub_neg_eq_add]
      _ = (Polynomial.X - Polynomial.C Complex.I) *
            (Polynomial.X - Polynomial.C (-Complex.I)) := by
            simp only [map_neg, sub_neg_eq_add, map_mul]; ring
  have hsf_CC : IsGarlingSplittingFieldExtension ℂ ℂ (f.map (algebraMap ℝ ℂ)) := by
    rw [isGarlingSplittingFieldExtension_iff]
    refine ⟨?_, ?_⟩
    · have hsp : ((Polynomial.X - Polynomial.C Complex.I) *
          (Polynomial.X - Polynomial.C (-Complex.I))).Splits :=
        Polynomial.Splits.mul
          (Polynomial.Splits.X_sub_C Complex.I) (Polynomial.Splits.X_sub_C (-Complex.I))
      rw [Algebra.algebraMap_self, Polynomial.map_id, hfC_fac]
      exact hsp
    · exact eq_top_iff.mpr fun z _ => Subalgebra.algebraMap_mem _ z
  -- `ℂ : ℝ` is a splitting field of separable `X^2 + 1`, hence Galois of degree `2`.
  have hsf_RC : IsGarlingSplittingFieldExtension ℝ ℂ f := by
    rw [isGarlingSplittingFieldExtension_iff]
    refine ⟨?_, ?_⟩
    · rw [hfC_fac]
      exact Polynomial.Splits.mul
        (Polynomial.Splits.X_sub_C Complex.I) (Polynomial.Splits.X_sub_C (-Complex.I))
    · rw [eq_top_iff]
      intro z _
      have hI_mem : Complex.I ∈ f.rootSet ℂ := by
        rw [Polynomial.mem_rootSet_of_ne hf_mon.ne_zero, Polynomial.aeval_def,
          ← Polynomial.eval_map, hfC_fac]
        simp
      have hre : (z.re : ℂ) ∈ Algebra.adjoin ℝ (f.rootSet ℂ) := Subalgebra.algebraMap_mem _ z.re
      have him : (z.im : ℂ) ∈ Algebra.adjoin ℝ (f.rootSet ℂ) := Subalgebra.algebraMap_mem _ z.im
      have hI_adj : Complex.I ∈ Algebra.adjoin ℝ (f.rootSet ℂ) := Algebra.subset_adjoin hI_mem
      have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
      rw [hz_eq]
      exact Subalgebra.add_mem _ hre (Subalgebra.mul_mem _ him hI_adj)
  have hperfR : IsGarlingPerfectField ℝ := isGarlingPerfectField_of_char_zero ringChar.eq_zero
  have hcard_RC : Nat.card (GarlingGaloisGroup ℝ ℂ) = 2 :=
    (theorem_11_5_perfect hperfR hsf_RC).2.1.trans Complex.finrank_real_complex
  have hnot_forall : ¬ ∀ n : ℕ, Nat.card (GarlingGaloisGroup ℝ ℂ) = 2 ^ n := by
    intro hall
    have h0 := hall 0
    rw [hcard_RC] at h0; norm_num at h0
  have hne_deg : Nat.card (GarlingGaloisGroup ℝ ℂ) ≠ 2 ^ f.natDegree := by
    rw [hcard_RC, hf_deg]; norm_num
  have hno_quadC : ¬ ∃ q : ℂ[X], Irreducible q ∧ q.natDegree = 2 :=
    no_irreducible_quadratic_of_sqrt_and_char_ne_two
      (by rw [ringChar.eq_zero]; decide) complex_exists_sq_eq
  exact ⟨hf_irr, hsf_CC, hcard_RC, hnot_forall, hne_deg, hno_quadC⟩

/-- Universe-polymorphic helper proving parts `(i)` and `(ii)` of **Exercise 11.11** for any
splitting field `M : Type w` of `f ∈ K[X]` over `L : Type v`. -/
private theorem exercise_11_11_parts_i_ii {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    (hdim : Module.finrank K L = 2)
    (hodd_root : ∀ h : K[X], Odd h.natDegree → ∃ x : K, h.eval x = 0)
    (hchar : ringChar K ≠ 2)
    {f : K[X]} (hf : Irreducible f)
    (M : Type w) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hsf_LM : IsGarlingSplittingFieldExtension L M (f.map (algebraMap K L))) :
    IsGarlingGaloisExtension K M ∧
    (∃ n : ℕ, 1 ≤ n ∧ Nat.card (GarlingGaloisGroup K M) = 2 ^ n) ∧
    (∀ n : ℕ, Nat.card (GarlingGaloisGroup K M) = 2 ^ n → 1 < n →
      (∃ J : Subgroup (GarlingGaloisGroup L M), J.index = 2) ∧
      (∃ q : L[X], Irreducible q ∧ q.natDegree = 2)) := by
  classical
  have hperfK : IsGarlingPerfectField K := by
    by_cases hp0 : ringChar K = 0
    · exact isGarlingPerfectField_of_char_zero hp0
    · have hp_prime : Nat.Prime (ringChar K) :=
        (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hp0
      have hp_odd : Odd (ringChar K) := hp_prime.odd_of_ne_two hchar
      rw [exercise_10_7 rfl hp0]
      obtain ⟨_, hmono, _⟩ := theorem_10_7 (K := K) rfl hp0
      refine ⟨hmono, fun a => ?_⟩
      let h : K[X] := Polynomial.X ^ (ringChar K) - Polynomial.C a
      have hh_deg : h.natDegree = ringChar K := Polynomial.natDegree_X_pow_sub_C
      obtain ⟨b, hb⟩ := hodd_root h (hh_deg ▸ hp_odd)
      refine ⟨b, ?_⟩
      rw [garlingFrobenius_apply]
      dsimp [h] at hb
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hb
      exact sub_eq_zero.mp hb
  have _ : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by omega)
  have hbot_ne_top : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro heq
    have h1 : Module.finrank K (⊥ : IntermediateField K L) = 1 := IntermediateField.finrank_bot
    have h2 : Module.finrank K (⊤ : IntermediateField K L) = 2 :=
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans hdim
    rw [heq] at h1; omega
  have hex_β : ∃ β : L, β ∉ (⊥ : IntermediateField K L) := by
    by_contra hall; push Not at hall
    exact hbot_ne_top (eq_top_iff.mpr fun x _ => hall x)
  obtain ⟨β, hβ_not_bot⟩ := hex_β
  have hβ_int : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hKβ_fin : Module.finrank K K⟮β⟯ = 2 := by
    have hmul := Module.finrank_mul_finrank K K⟮β⟯ L
    have hpos1 : 0 < Module.finrank K K⟮β⟯ := Module.finrank_pos
    have hne1 : Module.finrank K K⟮β⟯ ≠ 1 := by
      intro h1
      have hbot : K⟮β⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
      exact hβ_not_bot (hbot ▸ IntermediateField.mem_adjoin_simple_self K β)
    rw [hdim] at hmul
    have hle2 : Module.finrank K K⟮β⟯ ≤ 2 := Nat.le_of_dvd (by decide) ⟨_, hmul.symm⟩
    omega
  have hKβ_top : K⟮β⟯ = ⊤ := by
    have hsub_top : K⟮β⟯.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hKβ_fin.trans hdim.symm)
    ext x
    exact ⟨fun _ => trivial, fun _ => by change x ∈ K⟮β⟯.toSubmodule; rw [hsub_top]; trivial⟩
  let mβ : K[X] := minpoly K β
  have hmβ_deg : mβ.natDegree = 2 :=
    (IntermediateField.adjoin.finrank hβ_int).symm.trans hKβ_fin
  have hmβ_ne0 : mβ ≠ 0 := minpoly.ne_zero hβ_int
  have hmβ_spL : GarlingSplitsOver K L mβ := by
    rw [garlingSplitsOver_iff_splits]
    have hroot : (mβ.map (algebraMap K L)).IsRoot β := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval K β
    obtain ⟨q, hmq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hmap_deg : (mβ.map (algebraMap K L)).natDegree = 2 :=
      (Polynomial.natDegree_map (algebraMap K L)).trans hmβ_deg
    have hlin0 : (Polynomial.X - Polynomial.C β : L[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero β
    have hq0 : q ≠ 0 := fun h0 => by
      have hm0 : mβ.map (algebraMap K L) = 0 := by rw [hmq, h0, mul_zero]
      rw [hm0, Polynomial.natDegree_zero] at hmap_deg; omega
    have hq_deg : q.natDegree = 1 := by
      have hd := congrArg Polynomial.natDegree hmq
      rw [hmap_deg, Polynomial.natDegree_mul hlin0 hq0, Polynomial.natDegree_X_sub_C] at hd
      omega
    rw [hmq]
    exact Polynomial.Splits.mul (Polynomial.Splits.X_sub_C β)
      (Polynomial.Splits.of_natDegree_le_one (le_of_eq hq_deg))
  let P : K[X] := mβ * f
  have hsf_KM : IsGarlingSplittingFieldExtension K M P := by
    have hP_spM : GarlingSplitsOver K M P := by
      rw [garlingSplitsOver_mul_iff hmβ_ne0 hf.ne_zero]
      refine ⟨?_, ?_⟩
      · rw [garlingSplitsOver_iff_splits, IsScalarTower.algebraMap_eq K L M, ← Polynomial.map_map]
        exact ((garlingSplitsOver_iff_splits K L mβ).mp hmβ_spL).map (algebraMap L M)
      · rw [garlingSplitsOver_iff_splits, IsScalarTower.algebraMap_eq K L M, ← Polynomial.map_map]
        exact (garlingSplitsOver_iff_splits L M (f.map (algebraMap K L))).mp hsf_LM.1
    refine ⟨hP_spM, fun M₀ hM₀_ne hspM₀ => hM₀_ne ?_⟩
    obtain ⟨hmβ_M₀, hf_M₀⟩ := (garlingSplitsOver_mul_iff hmβ_ne0 hf.ne_zero).mp hspM₀
    have hβM_root : Polynomial.aeval (algebraMap L M β) mβ = 0 := by
      change Polynomial.aeval ((IsScalarTower.toAlgHom K L M) β) mβ = 0
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval K β, map_zero]
    have hβ_in_M₀ : algebraMap L M β ∈ M₀ :=
      mem_of_garlingSplitsOver_intermediateField hmβ_ne0 hmβ_M₀ hβM_root
    let M₀_in_L : IntermediateField K L := M₀.comap (IsScalarTower.toAlgHom K L M)
    have hβ_in_L : β ∈ M₀_in_L := hβ_in_M₀
    have hKβ_le : K⟮β⟯ ≤ M₀_in_L :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_in_L)
    have hM₀_in_L_top : M₀_in_L = ⊤ := top_unique (hKβ_top ▸ hKβ_le)
    have hL_in_M₀ : ∀ l : L, algebraMap L M l ∈ M₀ := fun l => by
      have hl : l ∈ M₀_in_L := hM₀_in_L_top ▸ IntermediateField.mem_top
      exact hl
    let M₀_L : IntermediateField L M := { M₀.toSubfield with algebraMap_mem' := hL_in_M₀ }
    have hfL_sp : GarlingSplitsOver L M₀_L (f.map (algebraMap K L)) := by
      rw [garlingSplitsOver_iff_splits]
      have hmap : (f.map (algebraMap K L)).map (algebraMap L M₀_L) = f.map (algebraMap K M₀) := by
        rw [Polynomial.map_map]
        congr 1
        ext k
        exact (IsScalarTower.algebraMap_apply K L M k).symm
      rw [hmap]
      exact (garlingSplitsOver_iff_splits K M₀ f).mp hf_M₀
    have htop_L : M₀_L = ⊤ := by
      by_contra hne
      exact hsf_LM.2 M₀_L hne hfL_sp
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hz : z ∈ M₀_L := htop_L.symm ▸ (IntermediateField.mem_top : z ∈ (⊤ : IntermediateField L M))
    exact hz
  have hfinKM : IsFiniteExtension K M := (corollary_to_theorem_7_1 hsf_KM).1
  have hnormKM : IsGarlingNormal K M := (corollary_1_to_theorem_9_1 hfinKM).mpr ⟨P, hsf_KM⟩
  have hsepKM : IsGarlingSeparableExtension K M :=
    exercise_10_8_mp_univ hperfK hnormKM.1
  have hgalKM : IsGarlingGaloisExtension K M := ⟨hfinKM, hnormKM, hsepKM⟩
  have ⟨hfdKM, hisGalKM⟩ := (isGarlingGaloisExtension_iff K M).mp hgalKM
  have _ : FiniteDimensional L M := FiniteDimensional.right K L M
  have _ : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hgalLM : IsGarlingGaloisExtension L M :=
    (isGarlingGaloisExtension_iff L M).mpr ⟨inferInstance, inferInstance⟩
  let G := GarlingGaloisGroup K M
  have hcardG_deg : Nat.card G = Module.finrank K M :=
    (theorem_10_4_algEquiv hfinKM).1 hgalKM
  have hdeg_tower : Module.finrank K M = 2 * Module.finrank L M := by
    rw [← Module.finrank_mul_finrank K L M, hdim]
  have hpos_LM : 0 < Module.finrank L M := Module.finrank_pos
  have _ : Finite G := Finite.of_fintype (M ≃ₐ[K] M)
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := Classical.arbitrary (Sylow 2 G)
  let E : IntermediateField K M := IntermediateField.fixedField S.toSubgroup
  have hfin_EM : Module.finrank E M = Nat.card S.toSubgroup :=
    IntermediateField.finrank_fixedField_eq_card S.toSubgroup
  have hcardS_pos : 0 < Nat.card S.toSubgroup := Nat.card_pos
  have hfin_KE_eq_idx : Module.finrank K E = S.toSubgroup.index := by
    have h1 : Module.finrank K E * Nat.card S.toSubgroup = Nat.card G := by
      rw [← hfin_EM, Module.finrank_mul_finrank K E M, hcardG_deg]
    have h2 : S.toSubgroup.index * Nat.card S.toSubgroup = Nat.card G :=
      Subgroup.index_mul_card S.toSubgroup
    exact Nat.eq_of_mul_eq_mul_right hcardS_pos (h1.trans h2.symm)
  have hnot_2_dvd : ¬ 2 ∣ Module.finrank K E := by
    rw [hfin_KE_eq_idx]
    exact S.not_dvd_index
  have hKE_odd : Odd (Module.finrank K E) :=
    Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr hnot_2_dvd)
  have hE_bot : ∀ γ : E, γ ∈ Set.range (algebraMap K E) := by
    intro γ
    have hγ_int : IsIntegral K γ := Algebra.IsIntegral.isIntegral γ
    have hdvd_deg : (minpoly K γ).natDegree ∣ Module.finrank K E := by
      rw [← IntermediateField.adjoin.finrank hγ_int]
      exact ⟨Module.finrank K⟮γ⟯ E, (Module.finrank_mul_finrank K K⟮γ⟯ E).symm⟩
    have hodd_γ : Odd (minpoly K γ).natDegree := by
      by_contra hnot_odd
      obtain ⟨v, hv⟩ := Nat.not_odd_iff_even.mp hnot_odd
      rcases hdvd_deg with ⟨t, ht⟩
      exact Nat.not_even_iff_odd.mpr hKE_odd ⟨v * t, by rw [ht, hv]; ring⟩
    obtain ⟨x, hx0⟩ := hodd_root (minpoly K γ) hodd_γ
    have hlin_dvd : Polynomial.X - Polynomial.C x ∣ minpoly K γ :=
      Polynomial.dvd_iff_isRoot.mpr hx0
    have hmin_irr : Irreducible (minpoly K γ) := minpoly.irreducible hγ_int
    have hmin_mon : (minpoly K γ).Monic := minpoly.monic hγ_int
    obtain ⟨u, hu⟩ := hlin_dvd
    have hu_unit : IsUnit u :=
      (hmin_irr.isUnit_or_isUnit hu).resolve_left
        (Polynomial.irreducible_X_sub_C x).not_isUnit
    have hu_deg0 : u.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_unit
    have huc : u = Polynomial.C (u.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hu_deg0
    have hlc1 : u.coeff 0 = 1 := by
      have hlc := hmin_mon.leadingCoeff
      rw [hu, huc, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C,
        Polynomial.leadingCoeff_C, one_mul] at hlc
      exact hlc
    have hmin_eq : minpoly K γ = Polynomial.X - Polynomial.C x := by
      rw [hu, huc, hlc1, map_one, mul_one]
    have haev := minpoly.aeval K γ
    rw [hmin_eq, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at haev
    exact ⟨x, (sub_eq_zero.mp haev).symm⟩
  have hE_eq_bot : E = ⊥ := by
    ext z
    refine ⟨fun hz => ?_, fun hz => (bot_le : (⊥ : IntermediateField K M) ≤ E) hz⟩
    obtain ⟨x, hx⟩ := hE_bot ⟨z, hz⟩
    exact IntermediateField.mem_bot.mpr ⟨x, congrArg Subtype.val hx⟩
  have hidx1 : S.toSubgroup.index = 1 := by
    rw [← hfin_KE_eq_idx, hE_eq_bot]
    exact IntermediateField.finrank_bot
  have hcardG_eq_S : Nat.card G = Nat.card S.toSubgroup := by
    have h2 := Subgroup.index_mul_card S.toSubgroup
    rw [hidx1, one_mul] at h2
    exact h2.symm
  obtain ⟨n₀, hn₀_S⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hn₀_ge1 : 1 ≤ n₀ := by
    by_contra hlt
    have hn0 : n₀ = 0 := by omega
    have h1 : Nat.card G = 1 := by rw [hcardG_eq_S, hn₀_S, hn0, pow_zero]
    omega
  have hii_claim : ∀ n : ℕ, Nat.card G = 2 ^ n → 1 < n →
      (∃ J : Subgroup (GarlingGaloisGroup L M), J.index = 2) ∧
      (∃ q : L[X], Irreducible q ∧ q.natDegree = 2) := by
    intro n hn_card hn_gt1
    let H := GarlingGaloisGroup L M
    have _ : Finite H := Finite.of_fintype (M ≃ₐ[L] M)
    have hcardH_deg : Nat.card H = Module.finrank L M :=
      (theorem_10_4_algEquiv hgalLM.1).1 hgalLM
    have hcardH : Nat.card H = 2 ^ (n - 1) := by
      have h2H : 2 * Nat.card H = 2 * 2 ^ (n - 1) := by
        calc 2 * Nat.card H = Module.finrank K M := by rw [hcardH_deg, hdeg_tower]
          _ = 2 ^ n := by rw [← hcardG_deg, hn_card]
          _ = 2 ^ ((n - 1) + 1) := by congr 1; omega
          _ = 2 * 2 ^ (n - 1) := by rw [pow_succ']
      omega
    have hdvd_n2 : 2 ^ (n - 2) ∣ Nat.card H := by
      rw [hcardH]
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨J, hcardJ⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 hdvd_n2
    have hJ_idx : J.index = 2 := by
      have hmulJ := Subgroup.index_mul_card J
      have hpow_pos : 0 < 2 ^ (n - 2) := by positivity
      have hpow_split : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
        rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
      rw [hcardJ, hcardH, hpow_split] at hmulJ
      exact Nat.eq_of_mul_eq_mul_right hpow_pos hmulJ
    let F : IntermediateField L M := IntermediateField.fixedField J
    have hfin_FM : Module.finrank F M = Nat.card J :=
      IntermediateField.finrank_fixedField_eq_card J
    have hfin_LF : Module.finrank L F = 2 := by
      have hmulF := Module.finrank_mul_finrank L F M
      have hJ_pos : 0 < Nat.card J := Nat.card_pos
      have hHM : Module.finrank L M = 2 * Nat.card J := by
        rw [← hcardH_deg, ← Subgroup.index_mul_card J, hJ_idx]
      rw [hfin_FM, hHM] at hmulF
      exact Nat.eq_of_mul_eq_mul_right hJ_pos hmulF
    have hF_not_le_bot : ¬ (F ≤ (⊥ : IntermediateField L M)) := by
      intro hle
      have hF_bot : F = (⊥ : IntermediateField L M) := le_antisymm hle bot_le
      have h1 : Module.finrank L (⊥ : IntermediateField L M) = 1 := IntermediateField.finrank_bot
      rw [hF_bot] at hfin_LF
      omega
    have hex_δ : ∃ δ : M, δ ∈ F ∧ δ ∉ (⊥ : IntermediateField L M) := by
      by_contra hall
      exact hF_not_le_bot fun x hx => by
        by_contra hx_bot
        exact hall ⟨x, hx, hx_bot⟩
    obtain ⟨δ, hδ_in_F, hδ_not_bot⟩ := hex_δ
    have hδ_int : IsIntegral L δ := Algebra.IsIntegral.isIntegral δ
    have hLδ_le_F : L⟮δ⟯ ≤ F :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hδ_in_F)
    have hLδ_fin : Module.finrank L L⟮δ⟯ = 2 := by
      have hle_fr : Module.finrank L L⟮δ⟯ ≤ Module.finrank L F :=
        Submodule.finrank_mono (show L⟮δ⟯.toSubmodule ≤ F.toSubmodule from hLδ_le_F)
      have hpos1 : 0 < Module.finrank L L⟮δ⟯ := Module.finrank_pos
      have hne1 : Module.finrank L L⟮δ⟯ ≠ 1 := by
        intro h1
        have hb : L⟮δ⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
        exact hδ_not_bot (hb ▸ IntermediateField.mem_adjoin_simple_self L δ)
      omega
    refine ⟨⟨J, hJ_idx⟩, ⟨minpoly L δ, minpoly.irreducible hδ_int,
      (IntermediateField.adjoin.finrank hδ_int).symm.trans hLδ_fin⟩⟩
  exact ⟨hgalKM, ⟨n₀, hn₀_ge1, hcardG_eq_S.trans hn₀_S⟩, hii_claim⟩

/-- **Exercise 11.11 (i)–(iii)** (§11.4, printed p. 99 / PDF p. 107; see `QUEUE.md` on unbound `n`):
*"Suppose that `L : K` is an extension with `[L:K] = 2`, that every element of `L` has a square root
in `L`, that every polynomial of odd degree in `K[x]` has a root in `K` and that `char K ≠ 2`. Let
`f` be an irreducible polynomial in `K[x]`, let `M : L` be a splitting field extension for `f` over
`L`, let `G = Γ(M:K)` and let `H = Γ(M:L)`.
(i) By considering the fixed field of a Sylow `2`-subgroup of `G`, show that `|G| = 2^n`.
(ii) By considering a subgroup of index `2` in `H`, show that if `n > 1` then there is an
irreducible quadratic in `L[x]`.
(iii) Show that `L` is algebraically closed."*

Proved across arbitrary universes `u, v, w` with **zero** `IsAlgClosed` dependency. -/
theorem exercise_11_11 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hdim : Module.finrank K L = 2)
    (hsqrt : ∀ w : L, ∃ u : L, u ^ 2 = w)
    (hodd_root : ∀ h : K[X], Odd h.natDegree → ∃ x : K, h.eval x = 0)
    (hchar : ringChar K ≠ 2) :
    (∀ {f : K[X]}, Irreducible f →
      ∀ (M : Type w) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M],
        IsGarlingSplittingFieldExtension L M (f.map (algebraMap K L)) →
        IsGarlingGaloisExtension K M ∧
        (∃ n : ℕ, 1 ≤ n ∧ Nat.card (GarlingGaloisGroup K M) = 2 ^ n) ∧
        (∀ n : ℕ, Nat.card (GarlingGaloisGroup K M) = 2 ^ n → 1 < n →
          (∃ J : Subgroup (GarlingGaloisGroup L M), J.index = 2) ∧
          (∃ q : L[X], Irreducible q ∧ q.natDegree = 2))) ∧
    IsGarlingAlgebraicallyClosed L := by
  have _ : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by omega)
  have hfinKL : IsFiniteExtension K L :=
    (isFiniteExtension_iff_moduleFinite K L).mpr inferInstance
  have hcharL : ringChar L ≠ 2 := by
    intro hcharL2
    have h0L : ((2 : ℕ) : L) = 0 := (ringChar.spec L 2).mpr (dvd_of_eq hcharL2)
    have h0K : ((2 : ℕ) : K) = 0 := (algebraMap K L).injective (by rw [map_natCast, h0L, map_zero])
    have hdvdK : ringChar K ∣ 2 := (ringChar.spec K 2).mp h0K
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvdK with h1 | h2
    · have h1K : ((1 : ℕ) : K) = 0 := (ringChar.spec K 1).mpr (by rw [h1])
      simp at h1K
    · exact hchar h2
  have hno_quadL : ¬ ∃ q : L[X], Irreducible q ∧ q.natDegree = 2 :=
    no_irreducible_quadratic_of_sqrt_and_char_ne_two hcharL hsqrt
  have halgKL : IsAlgebraicExtension K L := ((theorem_4_6 K L).1.mp hfinKL).1
  have hL_closed : IsGarlingAlgebraicallyClosed L := by
    refine isGarlingAlgebraicallyClosed_of_irreducible_base_splits halgKL fun f hf => ?_
    obtain ⟨M, instFM, instALM, hsf_LM, _⟩ := theorem_7_3_natDegree (f.map (algebraMap K L))
    let _ : Field M := instFM
    let _ : Algebra L M := instALM
    let _ : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
    have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨hgalKM, ⟨n, hn1, hn_card⟩, hii⟩ :=
      exercise_11_11_parts_i_ii.{u, v, v} hdim hodd_root hchar hf M hsf_LM
    have hn_eq1 : n = 1 := by
      by_contra hne1
      have hgt1 : 1 < n := by omega
      exact hno_quadL (hii n hn_card hgt1).2
    have hcardG2 : Nat.card (GarlingGaloisGroup K M) = 2 := by rw [hn_card, hn_eq1, pow_one]
    have hdegKM2 : Module.finrank K M = 2 :=
      ((theorem_10_4_algEquiv hgalKM.1).1 hgalKM).symm.trans hcardG2
    have _ : FiniteDimensional K M := (isGarlingGaloisExtension_iff K M).mp hgalKM |>.1
    have hdegLM1 : Module.finrank L M = 1 := by
      have hmul := Module.finrank_mul_finrank K L M
      rw [hdim, hdegKM2] at hmul; omega
    have hsurj_LM : Function.Surjective (algebraMap L M) :=
      (bot_eq_top_iff_surjective_algebraMap L M).mp
        (IntermediateField.finrank_eq_one_iff.mp
          (IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans hdegLM1)).symm
    have hbij_LM : Function.Bijective (algebraMap L M) := ⟨(algebraMap L M).injective, hsurj_LM⟩
    let eLM : L ≃+* M := RingEquiv.ofBijective (algebraMap L M) hbij_LM
    rw [garlingSplitsOver_iff_splits]
    have hspM : ((f.map (algebraMap K L)).map eLM.toRingHom).Splits :=
      (garlingSplitsOver_iff_splits L M (f.map (algebraMap K L))).mp hsf_LM.1
    have hback := hspM.map eLM.symm.toRingHom
    have hid : eLM.symm.toRingHom.comp eLM.toRingHom = RingHom.id L :=
      RingHom.ext fun x => eLM.symm_apply_apply x
    rwa [Polynomial.map_map, hid, Polynomial.map_id] at hback
  exact ⟨fun hf M _ _ _ _ hsf =>
    exercise_11_11_parts_i_ii.{u, v, w} hdim hodd_root hchar hf M hsf, hL_closed⟩

/-- **Exercise 11.11 (iv)** (*Fundamental Theorem of Algebra*, §11.4, printed p. 99 / PDF p. 107):
*"Show that the complex numbers are algebraically closed."*

Proved strictly by specializing `exercise_11_11` `(iii)` to `K = ℝ, L = ℂ` via
`Complex.finrank_real_complex`, `complex_exists_sq_eq`, and `real_odd_natDegree_exists_root`,
with **zero** reference to `Complex.isAlgClosed` or `complex_isGarlingAlgebraicallyClosed`. -/
theorem exercise_11_11_iv_complex_algebraically_closed :
    IsGarlingAlgebraicallyClosed ℂ :=
  (exercise_11_11.{0, 0, 0} (K := ℝ) (L := ℂ)
    Complex.finrank_real_complex
    complex_exists_sq_eq
    real_odd_natDegree_exists_root
    (by rw [ringChar.eq_zero]; decide)).2

/-- Refutation of the literal printed wording *"the splitting field of all polynomials of odd
degree over `ℤ₂`"* in **Exercise 11.12** (§11.4, printed p. 99 / PDF p. 107; see `QUEUE.md`):
since `X * f` has odd degree whenever `f ∈ ℤ₂[X]` has positive even degree, any splitting field
extension `K : ℤ₂` of `{f : (ZMod 2)[X] | Odd f.natDegree}` is **already algebraically closed**,
and therefore has **no** degree-`2` extension `L : K`! -/
theorem exercise_11_12_literal_all_odd_is_algClosed
    {K : Type u} [Field K] [Algebra (ZMod 2) K]
    (hsf : IsGarlingSplittingFieldExtensionSet (ZMod 2) K
      {f : (ZMod 2)[X] | Odd f.natDegree}) :
    IsGarlingAlgebraicallyClosed K ∧
    ¬ ∃ (L : Type v) (_ : Field L) (_ : Algebra K L), Module.finrank K L = 2 := by
  have halg : IsAlgebraicExtension (ZMod 2) K :=
    ((theorem_9_1 (ZMod 2) K).mpr ⟨{f : (ZMod 2)[X] | Odd f.natDegree}, hsf⟩).1
  have hK_closed : IsGarlingAlgebraicallyClosed K := by
    refine isGarlingAlgebraicallyClosed_of_irreducible_base_splits halg fun f hf => ?_
    by_cases hodd : Odd f.natDegree
    · exact hsf.1 f hodd
    · have hf0 : f ≠ 0 := hf.ne_zero
      have hdeg_pos : 0 < f.natDegree := hf.natDegree_pos
      have heven : Even f.natDegree := Nat.not_odd_iff_even.mp hodd
      have hXf_odd : Odd (Polynomial.X * f).natDegree := by
        rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hf0, Polynomial.natDegree_X]
        rcases heven with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      have hXf_sp : GarlingSplitsOver (ZMod 2) K (Polynomial.X * f) := hsf.1 _ hXf_odd
      exact ((garlingSplitsOver_mul_iff Polynomial.X_ne_zero hf0).mp hXf_sp).2
  refine ⟨hK_closed, ?_⟩
  rintro ⟨L, instFL, instAKL, hdim2⟩
  let _ : Field L := instFL
  let _ : Algebra K L := instAKL
  have _ : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by omega)
  have hbot_ne : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro heq
    have h1 : Module.finrank K (⊥ : IntermediateField K L) = 1 := IntermediateField.finrank_bot
    have h2 : Module.finrank K (⊤ : IntermediateField K L) = 2 :=
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans hdim2
    rw [heq] at h1; omega
  have hex_β : ∃ β : L, β ∉ (⊥ : IntermediateField K L) := by
    by_contra hall; push Not at hall
    exact hbot_ne (eq_top_iff.mpr fun x _ => hall x)
  obtain ⟨β, hβ_not⟩ := hex_β
  have hβ_int : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hm_irr : Irreducible (minpoly K β) := minpoly.irreducible hβ_int
  have hm_deg2 : (minpoly K β).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hβ_int]
    have hmul := Module.finrank_mul_finrank K K⟮β⟯ L
    have hne1 : Module.finrank K K⟮β⟯ ≠ 1 := fun h1 =>
      hβ_not ((IntermediateField.finrank_eq_one_iff.mp h1) ▸
        IntermediateField.mem_adjoin_simple_self K β)
    rw [hdim2] at hmul
    have hle2 : Module.finrank K K⟮β⟯ ≤ 2 := Nat.le_of_dvd (by decide) ⟨_, hmul.symm⟩
    have hpos : 0 < Module.finrank K K⟮β⟯ := Module.finrank_pos
    omega
  have hm_sp : (minpoly K β).Splits := by
    have h := (garlingSplitsOver_iff_splits K K (minpoly K β)).mp (hK_closed (minpoly K β))
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using h
  have hdeg1 : (minpoly K β).natDegree = 1 := hm_sp.natDegree_eq_one_of_irreducible hm_irr
  omega

/-- Helper: every polynomial of odd degree over a field has at least one irreducible factor of odd degree. -/
private theorem exists_irreducible_factor_odd_natDegree {F : Type*} [Field F]
    {P : F[X]} (hodd : Odd P.natDegree) :
    ∃ g : F[X], Irreducible g ∧ g ∣ P ∧ Odd g.natDegree := by
  have hmain : ∀ d : ℕ, ∀ Q : F[X], Q.natDegree = d → Odd d →
      ∃ g : F[X], Irreducible g ∧ g ∣ Q ∧ Odd g.natDegree := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hdeg hd_odd
      by_cases hQ_irr : Irreducible Q
      · exact ⟨Q, hQ_irr, dvd_rfl, hdeg ▸ hd_odd⟩
      · have hd_pos : 1 ≤ d := by rcases hd_odd with ⟨k, hk⟩; omega
        have hQ0 : Q ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at hdeg; omega
        have hQ_nu : ¬ IsUnit Q := fun hu => by
          have hz := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
        rw [irreducible_iff] at hQ_irr
        push Not at hQ_irr
        obtain ⟨A, B, hQAB, hAnu, hBnu⟩ := hQ_irr hQ_nu
        have hA0 : A ≠ 0 := fun h0 => hQ0 (by rw [hQAB, h0, zero_mul])
        have hB0 : B ≠ 0 := fun h0 => hQ0 (by rw [hQAB, h0, mul_zero])
        have hA_pos : 0 < A.natDegree := Nat.pos_of_ne_zero fun hz =>
          hAnu (Polynomial.isUnit_iff.mpr ⟨A.coeff 0,
            isUnit_iff_ne_zero.mpr fun h0 =>
              hA0 ((Polynomial.eq_C_of_natDegree_eq_zero hz).trans (by rw [h0, map_zero])),
            (Polynomial.eq_C_of_natDegree_eq_zero hz).symm⟩)
        have hB_pos : 0 < B.natDegree := Nat.pos_of_ne_zero fun hz =>
          hBnu (Polynomial.isUnit_iff.mpr ⟨B.coeff 0,
            isUnit_iff_ne_zero.mpr fun h0 =>
              hB0 ((Polynomial.eq_C_of_natDegree_eq_zero hz).trans (by rw [h0, map_zero])),
            (Polynomial.eq_C_of_natDegree_eq_zero hz).symm⟩)
        have hsum_deg : d = A.natDegree + B.natDegree := by
          rw [← hdeg, hQAB, Polynomial.natDegree_mul hA0 hB0]
        by_cases hA_odd : Odd A.natDegree
        · obtain ⟨g, hg_irr, hg_dvd, hg_odd⟩ := ih A.natDegree (by omega) A rfl hA_odd
          exact ⟨g, hg_irr, hg_dvd.trans ⟨B, hQAB⟩, hg_odd⟩
        · have hB_odd : Odd B.natDegree := by
            obtain ⟨kA, hkA⟩ := Nat.not_odd_iff_even.mp hA_odd
            obtain ⟨kd, hkd⟩ := hd_odd
            exact ⟨kd - kA, by omega⟩
          obtain ⟨g, hg_irr, hg_dvd, hg_odd⟩ := ih B.natDegree (by omega) B rfl hB_odd
          exact ⟨g, hg_irr, hg_dvd.trans ⟨A, by rw [hQAB, mul_comm]⟩, hg_odd⟩
  exact hmain P.natDegree P rfl hodd

/-- **Exercise 11.12** (§11.4, printed p. 99 / PDF p. 107; see `QUEUE.md` on odd-*irreducible* repair):
*"By considering the splitting field of all [irreducible] polynomials of odd degree over `ℤ₂`, show
that the condition `char K ≠ 2` cannot be dropped from question 11.11."*

Constructs inside Chapter 8's algebraic closure `Ω` of `ℤ₂` (`Theorem 8.2`) the splitting field
`K` of `{f : (ZMod 2)[X] | Irreducible f ∧ Odd f.natDegree}` (`K = {x ∈ Ω | ∃ d odd, x^(2^d) = x}`)
and its quadratic extension `L = K(ω)` (`ω² + ω + 1 = 0`), proving:
1. `IsGarlingSplittingFieldExtensionSet (ZMod 2) K {f : (ZMod 2)[X] | Irreducible f ∧ Odd f.natDegree}`;
2. `ringChar K = 2` and `Module.finrank K L = 2`;
3. Every element of `L` has a square root in `L`, and every odd-degree polynomial in `K[X]` has a root in `K`;
4. `¬ IsGarlingAlgebraicallyClosed L` (`X⁴ + X + 1 ∈ L[X]` has no root in `L`), refuting `11.11 (iii)` when `char K ≠ 2` is dropped. -/
theorem exercise_11_12 :
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra (ZMod 2) K) (_ : Algebra K L),
      IsGarlingSplittingFieldExtensionSet (ZMod 2) K
        {f : (ZMod 2)[X] | Irreducible f ∧ Odd f.natDegree} ∧
      ringChar K = 2 ∧
      Module.finrank K L = 2 ∧
      (∀ w : L, ∃ u : L, u ^ 2 = w) ∧
      (∀ h : K[X], Odd h.natDegree → ∃ x : K, h.eval x = 0) ∧
      ¬ IsGarlingAlgebraicallyClosed L := by
  have hz2_sq : ∀ c : ZMod 2, c ^ 2 = c := by decide
  have hz2_eq_one : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hz2_two_zero : ((2 : ℕ) : ZMod 2) = 0 := by decide
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ω, instFΩ, instAΩ, hclΩ⟩ := theorem_8_2 (ZMod 2)
  let _ : Field Ω := instFΩ
  let _ : Algebra (ZMod 2) Ω := instAΩ
  have _ : IsAlgClosed Ω := (isGarlingAlgebraicallyClosed_iff Ω).mp hclΩ.2
  have hcharΩ : ringChar Ω = 2 := by
    have h0 : ((2 : ℕ) : Ω) = 0 := by
      rw [← map_natCast (algebraMap (ZMod 2) Ω), hz2_two_zero, map_zero]
    rcases (Nat.dvd_prime Nat.prime_two).mp ((ringChar.spec Ω 2).mp h0) with h1 | h2
    · exfalso
      have h10 : ((1 : ℕ) : Ω) = 0 := (ringChar.spec Ω 1).mpr (by rw [h1])
      simp at h10
    · exact h2
  have _ : CharP Ω 2 := hcharΩ ▸ ringChar.charP Ω
  have htwoΩ : (2 : Ω) = 0 := by simpa using CharP.cast_eq_zero Ω 2
  have hpow_mul : ∀ {x : Ω} {d : ℕ}, x ^ (2 ^ d) = x → ∀ k : ℕ, x ^ (2 ^ (d * k)) = x := by
    intro x d hx k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]
  have hz2_pow2d : ∀ (c : ZMod 2) (d : ℕ), (algebraMap (ZMod 2) Ω c) ^ (2 ^ d) =
      algebraMap (ZMod 2) Ω c := by
    intro c d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ, pow_mul, ih, ← map_pow, hz2_sq c]
  -- Finite subfield `E_d = {z : Ω | z ^ (2 ^ d) = z}` of cardinality `2 ^ d` for every `d ≥ 1`.
  let Ed : ℕ → IntermediateField (ZMod 2) Ω := fun d =>
    { carrier := {z : Ω | z ^ (2 ^ d) = z}
      mul_mem' := fun {a b} ha hb => by change (a * b) ^ (2 ^ d) = a * b; rw [mul_pow, ha, hb]
      one_mem' := one_pow _
      add_mem' := fun {a b} ha hb => by
        change (a + b) ^ (2 ^ d) = a + b
        rw [add_pow_char_pow a b, ha, hb]
      zero_mem' := zero_pow (by positivity)
      inv_mem' := fun {a} ha => by change a⁻¹ ^ (2 ^ d) = a⁻¹; rw [inv_pow, ha]
      algebraMap_mem' := fun c => hz2_pow2d c d }
  have hEd_card_and_finrank : ∀ d : ℕ, 1 ≤ d →
      Finite (Ed d) ∧ Nat.card (Ed d) = 2 ^ d ∧ Module.finrank (ZMod 2) (Ed d) = d := by
    intro d hd1
    let Pd : Ω[X] := Polynomial.X ^ (2 ^ d) - Polynomial.X
    have h2d_gt1 : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
    have hPd_deg : Pd.natDegree = 2 ^ d := by
      dsimp [Pd]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow (2 ^ d)
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        exact h2d_gt1
    have hPd_ne0 : Pd ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at hPd_deg; omega
    have hPd_deriv : Polynomial.derivative Pd = -1 := by
      dsimp [Pd]
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      have hcast2 : ((2 : ℕ) : Ω) = 0 := CharP.cast_eq_zero Ω 2
      have hcast0 : ((2 ^ d : ℕ) : Ω) = 0 := by
        rw [Nat.cast_pow, hcast2, zero_pow (by omega)]
      rw [hcast0, map_zero, zero_mul, zero_sub]
    have hPd_sep : Pd.Separable := ⟨0, -1, by rw [hPd_deriv]; ring⟩
    have hPd_sp : Pd.Splits := IsAlgClosed.splits Pd
    have hset_eq : (Ed d : Set Ω) = (Pd.roots.toFinset : Set Ω) := by
      ext z
      change z ^ (2 ^ d) = z ↔ z ∈ (Pd.roots.toFinset : Set Ω)
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hPd_ne0,
        Polynomial.IsRoot.def, Pd, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        sub_eq_zero]
    have hfin_Ed : Finite (Ed d) := by
      change Finite (Ed d : Set Ω)
      rw [hset_eq]
      exact Finset.finite_toSet _
    have hcard_Ed : Nat.card (Ed d) = 2 ^ d := by
      change Nat.card (Ed d : Set Ω) = 2 ^ d
      rw [hset_eq, Nat.card_coe_set_eq, Set.ncard_coe_finset,
        Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hPd_sep),
        ← hPd_sp.natDegree_eq_card_roots, hPd_deg]
    have _ : Finite (Ed d) := hfin_Ed
    let bEd := Module.finBasis (ZMod 2) (Ed d)
    have hcard_basis : Nat.card (Ed d) = 2 ^ Module.finrank (ZMod 2) (Ed d) := by
      rw [Nat.card_congr bEd.equivFun.toEquiv, Nat.card_fun,
        Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card 2, Nat.card_fin]
    have hfinrank_Ed : Module.finrank (ZMod 2) (Ed d) = d :=
      Nat.pow_right_injective (by decide : 2 ≤ 2) (hcard_basis.symm.trans hcard_Ed)
    exact ⟨hfin_Ed, hcard_Ed, hfinrank_Ed⟩
  -- Helper: in any finite extension `F : Type` of `ZMod 2` of dimension `m`, every `y ∈ F` satisfies `y ^ (2 ^ m) = y`.
  have hpow_finrank_eq_self : ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
      (y : F), y ^ (2 ^ Module.finrank (ZMod 2) F) = y := by
    intro F _ _ _ y
    let m := Module.finrank (ZMod 2) F
    let bF := Module.finBasis (ZMod 2) F
    let _ : Fintype F := Fintype.ofEquiv (Fin m → ZMod 2) bF.equivFun.symm.toEquiv
    have hcardF : Fintype.card F = 2 ^ m := by
      rw [Fintype.card_congr bF.equivFun.toEquiv, Fintype.card_fun, ZMod.card 2, Fintype.card_fin]
    by_cases hy0 : y = 0
    · rw [hy0, zero_pow (by positivity)]
    · have hu_card : Fintype.card Fˣ = 2 ^ m - 1 := by
        rw [Fintype.card_units, hcardF]
      have hu_pow : (Units.mk0 y hy0) ^ (2 ^ m - 1) = 1 := by
        rw [← hu_card]
        exact pow_card_eq_one
      have hy_pow1 : y ^ (2 ^ m - 1) = 1 := by
        have h := congrArg Units.val hu_pow
        simpa using h
      have h2m_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      calc y ^ (2 ^ m) = y ^ ((2 ^ m - 1) + 1) := by rw [Nat.sub_add_cancel h2m_pos]
        _ = y ^ (2 ^ m - 1) * y := by rw [pow_succ]
        _ = y := by rw [hy_pow1, one_mul]
  -- Define `K_int : IntermediateField (ZMod 2) Ω` as `{x : Ω | ∃ d, Odd d ∧ x ^ (2 ^ d) = x}`.
  let K_int : IntermediateField (ZMod 2) Ω :=
    { carrier := {x : Ω | ∃ d : ℕ, Odd d ∧ x ^ (2 ^ d) = x}
      mul_mem' := fun {a b} ⟨d₁, hd₁, ha⟩ ⟨d₂, hd₂, hb⟩ =>
        ⟨d₁ * d₂, hd₁.mul hd₂, by
          rw [mul_pow, hpow_mul ha d₂, mul_comm d₁ d₂, hpow_mul hb d₁]⟩
      one_mem' := ⟨1, odd_one, by simp⟩
      add_mem' := fun {a b} ⟨d₁, hd₁, ha⟩ ⟨d₂, hd₂, hb⟩ =>
        ⟨d₁ * d₂, hd₁.mul hd₂, by
          rw [add_pow_char_pow a b, hpow_mul ha d₂, mul_comm d₁ d₂, hpow_mul hb d₁]⟩
      zero_mem' := ⟨1, odd_one, by simp⟩
      inv_mem' := fun {a} ⟨d, hd, ha⟩ => ⟨d, hd, by rw [inv_pow, ha]⟩
      algebraMap_mem' := fun c => ⟨1, odd_one, hz2_pow2d c 1⟩ }
  -- 1. Prove `IsGarlingSplittingFieldExtensionSet (ZMod 2) K_int S_odd_irr`.
  let S_odd_irr : Set (ZMod 2)[X] := {f : (ZMod 2)[X] | Irreducible f ∧ Odd f.natDegree}
  have hsf_K : IsGarlingSplittingFieldExtensionSet (ZMod 2) K_int S_odd_irr := by
    refine ⟨?_, ?_⟩
    · intro f ⟨hf_irr, hf_odd⟩
      have hfΩ : GarlingSplitsOver (ZMod 2) Ω f := by
        rw [garlingSplitsOver_iff_splits]
        exact IsAlgClosed.splits _
      obtain ⟨n, c, α, hexp⟩ := hfΩ
      refine (garlingSplitsOver_intermediateField_iff K_int f).mpr ⟨n, c, α, fun j => ?_, hexp⟩
      have hroots : Set.range α = f.rootSet Ω :=
        (garlingSplitsExplicit_props hf_irr.ne_zero hexp).2.2.2
      have hα_root : Polynomial.aeval (α j) f = 0 :=
        (Polynomial.mem_rootSet.mp (hroots ▸ ⟨j, rfl⟩)).2
      have hf_mon : f.Monic :=
        hz2_eq_one f.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hf_irr.ne_zero)
      have hmin_α : minpoly (ZMod 2) (α j) = f :=
        (minpoly.eq_of_irreducible_of_monic hf_irr hα_root hf_mon).symm
      have hα_int : IsIntegral (ZMod 2) (α j) := ⟨f, hf_mon, hα_root⟩
      have _ : FiniteDimensional (ZMod 2) (ZMod 2)⟮α j⟯ :=
        IntermediateField.adjoin.finiteDimensional hα_int
      have hdim_α : Module.finrank (ZMod 2) (ZMod 2)⟮α j⟯ = f.natDegree := by
        rw [IntermediateField.adjoin.finrank hα_int, hmin_α]
      let gen_j : (ZMod 2)⟮α j⟯ := IntermediateField.AdjoinSimple.gen (ZMod 2) (α j)
      have hpow_gen := hpow_finrank_eq_self (ZMod 2)⟮α j⟯ gen_j
      rw [hdim_α] at hpow_gen
      exact ⟨f.natDegree, hf_odd, congrArg Subtype.val hpow_gen⟩
    · intro L' hL'
      ext x
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨d, hd_odd, hx_pow⟩ := x.2
      have hd1 : 1 ≤ d := by rcases hd_odd with ⟨k, hk⟩; omega
      obtain ⟨hEd_fin, _, hEd_fr⟩ := hEd_card_and_finrank d hd1
      have hx_in_Ed : x.1 ∈ Ed d := hx_pow
      have hadj_le_Ed : (ZMod 2)⟮x.1⟯ ≤ Ed d :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx_in_Ed)
      have hx_int : IsIntegral (ZMod 2) x.1 :=
        (isGarlingAlgebraic_iff_isIntegral (ZMod 2) x.1).mp (hclΩ.1 x.1)
      let F_sub : IntermediateField (ZMod 2) (Ed d) :=
        { carrier := {y : Ed d | y.1 ∈ (ZMod 2)⟮x.1⟯}
          mul_mem' := fun {_ _} ha hb => (ZMod 2)⟮x.1⟯.mul_mem ha hb
          one_mem' := (ZMod 2)⟮x.1⟯.one_mem
          add_mem' := fun {_ _} ha hb => (ZMod 2)⟮x.1⟯.add_mem ha hb
          zero_mem' := (ZMod 2)⟮x.1⟯.zero_mem
          inv_mem' := fun {_} ha => (ZMod 2)⟮x.1⟯.inv_mem ha
          algebraMap_mem' := fun c => (ZMod 2)⟮x.1⟯.algebraMap_mem c }
      let eFx : (ZMod 2)⟮x.1⟯ ≃ₐ[ZMod 2] F_sub :=
        { toFun := fun y => ⟨⟨y.1, hadj_le_Ed y.2⟩, y.2⟩
          invFun := fun y => ⟨y.1.1, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl
          commutes' := fun _ => rfl }
      have _ : Finite (Ed d) := hEd_fin
      have hmul_fr : Module.finrank (ZMod 2) F_sub * Module.finrank F_sub (Ed d) = d :=
        (Module.finrank_mul_finrank (ZMod 2) F_sub (Ed d)).trans hEd_fr
      have hdeg_min_dvd : (minpoly (ZMod 2) x.1).natDegree ∣ d := by
        rw [← IntermediateField.adjoin.finrank hx_int, eFx.toLinearEquiv.finrank_eq]
        exact ⟨Module.finrank F_sub (Ed d), hmul_fr.symm⟩
      have hmin_odd : Odd (minpoly (ZMod 2) x.1).natDegree := by
        by_contra hno
        obtain ⟨v, hv⟩ := Nat.not_odd_iff_even.mp hno
        rcases hdeg_min_dvd with ⟨t, ht⟩
        exact Nat.not_even_iff_odd.mpr hd_odd ⟨v * t, by rw [ht, hv]; ring⟩
      have hmin_mem : minpoly (ZMod 2) x.1 ∈ S_odd_irr :=
        ⟨minpoly.irreducible hx_int, hmin_odd⟩
      have hxK_root : Polynomial.aeval x (minpoly (ZMod 2) x.1) = 0 := by
        apply Subtype.ext
        change K_int.val (Polynomial.aeval x (minpoly (ZMod 2) x.1)) = 0
        rw [← Polynomial.aeval_algHom_apply K_int.val x]
        change Polynomial.aeval x.1 (minpoly (ZMod 2) x.1) = 0
        exact minpoly.aeval (ZMod 2) x.1
      exact mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hx_int)
        (hL' _ hmin_mem) hxK_root
  -- 2. `ringChar K_int = 2`.
  have hcharK : ringChar K_int = 2 := by
    have h0 : ((2 : ℕ) : K_int) = 0 := by
      rw [← map_natCast (algebraMap (ZMod 2) K_int), hz2_two_zero, map_zero]
    rcases (Nat.dvd_prime Nat.prime_two).mp ((ringChar.spec K_int 2).mp h0) with h1 | h2
    · exfalso
      have h10 : ((1 : ℕ) : K_int) = 0 := (ringChar.spec K_int 1).mpr (by rw [h1])
      simp at h10
    · exact h2
  -- 3. Every odd-degree polynomial `h ∈ K_int[X]` has a root in `K_int`.
  have hodd_root_K : ∀ h : K_int[X], Odd h.natDegree → ∃ x : K_int, h.eval x = 0 := by
    intro h hh_odd
    obtain ⟨g, hg_irr, hg_dvd, hg_odd⟩ := exists_irreducible_factor_odd_natDegree hh_odd
    choose d_fn hd_odd_fn hd_pow_fn using fun i : ℕ => (g.coeff i).2
    let D : ℕ := ∏ i ∈ Finset.range (g.natDegree + 1), d_fn i
    have hD_odd : Odd D := by
      refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => hd_odd_fn i
    have hD1 : 1 ≤ D := by rcases hD_odd with ⟨k, hk⟩; omega
    obtain ⟨hED_fin, hED_card, _⟩ := hEd_card_and_finrank D hD1
    have hcoeff_in_ED : ∀ i : ℕ, (g.coeff i : Ω) ∈ Ed D := by
      intro i
      by_cases hi : i < g.natDegree + 1
      · have hdvd_D : d_fn i ∣ D := Finset.dvd_prod_of_mem d_fn (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ := hdvd_D
        change (g.coeff i : Ω) ^ (2 ^ D) = (g.coeff i : Ω)
        rw [hk]
        exact hpow_mul (hd_pow_fn i) k
      · have hgt : g.natDegree < i := by omega
        have hc0 : g.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
        rw [hc0]
        exact (Ed D).zero_mem
    have hED_le_K : Ed D ≤ K_int := fun z hz => ⟨D, hD_odd, hz⟩
    let incED : Ed D →+* K_int :=
      { toFun := fun z => ⟨z.1, hED_le_K z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let subED : Ed D →+* Ω := (Ed D).toSubfield.subtype
    let g₀ : (Ed D)[X] :=
      ∑ i ∈ Finset.range (g.natDegree + 1),
        Polynomial.C ⟨(g.coeff i : Ω), hcoeff_in_ED i⟩ * Polynomial.X ^ i
    have hg₀_map : g₀.map incED = g := by
      ext k
      rw [Polynomial.coeff_map]
      dsimp [g₀]
      rw [Polynomial.finsetSum_coeff]
      simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hk : k < g.natDegree + 1
      · rw [Finset.sum_eq_single k]
        · simp
          apply Subtype.ext; rfl
        · intro j _ hjk
          simp [show ¬ (k = j) by omega]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr hk)).elim
      · have hgt : g.natDegree < k := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, Finset.sum_eq_zero]
        · simp
        · intro j hj
          have hjl := Finset.mem_range.mp hj
          simp [show ¬ (k = j) by omega]
    have hg₀_deg : g₀.natDegree = g.natDegree := by
      rw [← hg₀_map, Polynomial.natDegree_map incED]
    have hg₀_irr : Irreducible g₀ := by
      refine ⟨fun hu => hg_irr.not_isUnit (hg₀_map ▸ hu.map (Polynomial.mapRingHom incED)), ?_⟩
      intro a b hab
      have hmap_ab : g = a.map incED * b.map incED := by rw [← hg₀_map, hab, Polynomial.map_mul]
      rcases hg_irr.isUnit_or_isUnit hmap_ab with hua | hub
      · left
        have hd0 : a.natDegree = 0 := by
          rw [← Polynomial.natDegree_map incED]
          exact Polynomial.natDegree_eq_zero_of_isUnit hua
        have ha0 : a ≠ 0 := fun h0 => hg_irr.ne_zero (by rw [← hg₀_map, hab, h0, zero_mul, Polynomial.map_zero])
        exact Polynomial.isUnit_iff.mpr ⟨a.coeff 0,
          isUnit_iff_ne_zero.mpr (fun hc => ha0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by rw [hc, map_zero]))),
          (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩
      · right
        have hd0 : b.natDegree = 0 := by
          rw [← Polynomial.natDegree_map incED]
          exact Polynomial.natDegree_eq_zero_of_isUnit hub
        have hb0 : b ≠ 0 := fun h0 => hg_irr.ne_zero (by rw [← hg₀_map, hab, h0, mul_zero, Polynomial.map_zero])
        exact Polynomial.isUnit_iff.mpr ⟨b.coeff 0,
          isUnit_iff_ne_zero.mpr (fun hc => hb0 ((Polynomial.eq_C_of_natDegree_eq_zero hd0).trans (by rw [hc, map_zero]))),
          (Polynomial.eq_C_of_natDegree_eq_zero hd0).symm⟩
    have hg₀Ω_deg : (g₀.map subED).natDegree = g.natDegree :=
      (Polynomial.natDegree_map subED).trans hg₀_deg
    have hg₀Ω_pos : 0 < (g₀.map subED).natDegree := by
      rw [hg₀Ω_deg]; exact hg_irr.natDegree_pos
    obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (g₀.map subED)
      (Polynomial.degree_ne_of_natDegree_ne hg₀Ω_pos.ne')
    have hα_aev : Polynomial.aeval α g₀ = 0 := by
      have heq_sub : subED = algebraMap (Ed D) Ω := rfl
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← heq_sub]
      exact hα_root
    let g₀_mon : (Ed D)[X] := Polynomial.C g₀.leadingCoeff⁻¹ * g₀
    have hlc0 : g₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg₀_irr.ne_zero
    have hg₀_mon_monic : g₀_mon.Monic := by
      dsimp [g₀_mon]
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hlc0]
    have hg₀_mon_irr : Irreducible g₀_mon :=
      (associated_unit_mul_left g₀ _
        ((isUnit_iff_ne_zero.mpr (inv_ne_zero hlc0)).map Polynomial.C)).symm.irreducible hg₀_irr
    have hα_aev_mon : Polynomial.aeval α g₀_mon = 0 := by
      dsimp [g₀_mon]; rw [map_mul, hα_aev, mul_zero]
    have hmin_ED_α : minpoly (Ed D) α = g₀_mon :=
      (minpoly.eq_of_irreducible_of_monic hg₀_mon_irr hα_aev_mon hg₀_mon_monic).symm
    have hα_int_ED : IsIntegral (Ed D) α := ⟨g₀_mon, hg₀_mon_monic, hα_aev_mon⟩
    have _ : Finite (Ed D) := hED_fin
    have _ : FiniteDimensional (Ed D) (Ed D)⟮α⟯ :=
      IntermediateField.adjoin.finiteDimensional hα_int_ED
    have hfr_ED_α : Module.finrank (Ed D) (Ed D)⟮α⟯ = g.natDegree := by
      rw [IntermediateField.adjoin.finrank hα_int_ED, hmin_ED_α]
      dsimp [g₀_mon]
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc0), hg₀_deg]
    let bα := Module.finBasis (Ed D) (Ed D)⟮α⟯
    let _ : Fintype (Ed D) := Fintype.ofFinite (Ed D)
    let _ : Fintype (Ed D)⟮α⟯ :=
      Fintype.ofEquiv (Fin (Module.finrank (Ed D) (Ed D)⟮α⟯) → Ed D) bα.equivFun.symm.toEquiv
    have hcard_ED_fintype : Fintype.card (Ed D) = 2 ^ D := by
      rw [← Nat.card_eq_fintype_card, hED_card]
    have hcard_Eα : Fintype.card (Ed D)⟮α⟯ = 2 ^ (D * g.natDegree) := by
      rw [Fintype.card_congr bα.equivFun.toEquiv, Fintype.card_fun, hcard_ED_fintype,
        Fintype.card_fin, hfr_ED_α, ← pow_mul]
    let genα : (Ed D)⟮α⟯ := IntermediateField.AdjoinSimple.gen (Ed D) α
    have hpow_α_Ω : α ^ (2 ^ (D * g.natDegree)) = α := by
      by_cases hα0 : genα = 0
      · have h0 : α = 0 := congrArg Subtype.val hα0
        rw [h0, zero_pow (by positivity)]
      · have hu_card : Fintype.card ((Ed D)⟮α⟯)ˣ = 2 ^ (D * g.natDegree) - 1 := by
          rw [Fintype.card_units, hcard_Eα]
        have hu_pow : (Units.mk0 genα hα0) ^ (2 ^ (D * g.natDegree) - 1) = 1 := by
          rw [← hu_card]
          exact pow_card_eq_one
        have hgen_pow1 : genα ^ (2 ^ (D * g.natDegree) - 1) = 1 := by
          have h := congrArg Units.val hu_pow
          simpa using h
        have hα_pow1 : α ^ (2 ^ (D * g.natDegree) - 1) = 1 := congrArg Subtype.val hgen_pow1
        have hpos_pow : 1 ≤ 2 ^ (D * g.natDegree) := Nat.one_le_two_pow
        calc α ^ (2 ^ (D * g.natDegree))
            = α ^ ((2 ^ (D * g.natDegree) - 1) + 1) := by rw [Nat.sub_add_cancel hpos_pow]
          _ = α ^ (2 ^ (D * g.natDegree) - 1) * α := by rw [pow_succ]
          _ = α := by rw [hα_pow1, one_mul]
    have hα_in_K : α ∈ K_int := ⟨D * g.natDegree, hD_odd.mul hg_odd, hpow_α_Ω⟩
    let xK : K_int := ⟨α, hα_in_K⟩
    have hg_eval0 : g.eval xK = 0 := by
      apply Subtype.ext
      change K_int.toSubfield.subtype (g.eval xK) = 0
      have hval_comp : K_int.toSubfield.subtype.comp incED = subED := rfl
      have hxK_val : K_int.toSubfield.subtype xK = α := rfl
      rw [← hg₀_map, Polynomial.eval_map, Polynomial.hom_eval₂, hval_comp, hxK_val,
        ← Polynomial.eval_map]
      exact hα_root
    obtain ⟨q, hhq⟩ := hg_dvd
    exact ⟨xK, by rw [hhq, Polynomial.eval_mul, hg_eval0, zero_mul]⟩
  -- 4. Adjoin a root `ω ∈ Ω` of `X^2 + X + 1` to obtain `L_int := K_int⟮ω⟯` of degree `2` over `K_int`.
  let pω : Ω[X] := Polynomial.X ^ 2 + Polynomial.X + 1
  have hpω_deg : pω.natDegree = 2 := by dsimp [pω]; compute_degree!
  have hpω_ne0 : pω.natDegree ≠ 0 := by rw [hpω_deg]; decide
  obtain ⟨ω, hω_root⟩ := IsAlgClosed.exists_root pω
    (Polynomial.degree_ne_of_natDegree_ne hpω_ne0)
  rw [Polynomial.IsRoot.def] at hω_root
  have hω_sq : ω ^ 2 = ω + 1 := by
    dsimp [pω] at hω_root
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hω_root
    linear_combination hω_root - (ω + 1) * htwoΩ
  have hω_fourth : ω ^ 4 = ω := by
    calc ω ^ 4 = (ω ^ 2) ^ 2 := by ring
      _ = (ω + 1) ^ 2 := by rw [hω_sq]
      _ = ω ^ 2 + 1 ^ 2 := by linear_combination ω * htwoΩ
      _ = (ω + 1) + 1 := by rw [hω_sq, one_pow]
      _ = ω + 2 * 1 := by ring
      _ = ω := by rw [htwoΩ]; ring
  have hω_even_pow : ∀ k : ℕ, ω ^ (2 ^ (2 * k)) = ω := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul, ih]
      exact hω_fourth
  have hω_not_K : ω ∉ K_int := by
    rintro ⟨d, ⟨k, hk⟩, hωd⟩
    have h1 : ω ^ (2 ^ (2 * k + 1)) = ω + 1 := by
      rw [pow_succ, pow_mul, hω_even_pow k, hω_sq]
    rw [hk, h1] at hωd
    have h10 : (1 : Ω) = 0 := by linear_combination hωd
    exact one_ne_zero h10
  let L_int : IntermediateField K_int Ω := K_int⟮ω⟯
  let qω : K_int[X] := Polynomial.X ^ 2 + Polynomial.X + 1
  have hqω_mon : qω.Monic := by dsimp [qω]; monicity!
  have hqω_deg : qω.natDegree = 2 := by dsimp [qω]; compute_degree!
  have hω_aev_qω : Polynomial.aeval ω qω = 0 := by
    dsimp [qω]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    dsimp [pω] at hω_root
    simpa using hω_root
  have hω_int_K : IsIntegral K_int ω := ⟨qω, hqω_mon, hω_aev_qω⟩
  have hdim_KL : Module.finrank K_int L_int = 2 := by
    dsimp [L_int]
    rw [IntermediateField.adjoin.finrank hω_int_K]
    have hdvd : (minpoly K_int ω).natDegree ≤ 2 :=
      (Polynomial.natDegree_le_of_dvd (minpoly.dvd K_int ω hω_aev_qω) hqω_mon.ne_zero).trans_eq hqω_deg
    have hpos : 0 < (minpoly K_int ω).natDegree := (minpoly.irreducible hω_int_K).natDegree_pos
    have hne1 : (minpoly K_int ω).natDegree ≠ 1 := by
      intro h1
      have hfin1 : Module.finrank K_int K_int⟮ω⟯ = 1 :=
        (IntermediateField.adjoin.finrank hω_int_K).trans h1
      have hb : K_int⟮ω⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin1
      have hmem : ω ∈ (⊥ : IntermediateField K_int Ω) :=
        hb ▸ IntermediateField.mem_adjoin_simple_self K_int ω
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
      exact hω_not_K (hc ▸ c.2)
    omega
  -- 5. Every element of `L_int` has a square root in `L_int` (via the subfield of squares in char `2`).
  have htwoL : (2 : L_int) = 0 := Subtype.ext htwoΩ
  have hsqrt_L : ∀ w : L_int, ∃ u : L_int, u ^ 2 = w := by
    let SqField : IntermediateField K_int L_int :=
      { carrier := {w : L_int | ∃ u : L_int, u ^ 2 = w}
        mul_mem' := fun {a b} ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ =>
          ⟨u₁ * u₂, by rw [mul_pow, hu₁, hu₂]⟩
        one_mem' := ⟨1, one_pow 2⟩
        add_mem' := fun {a b} ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ =>
          ⟨u₁ + u₂, by linear_combination (u₁ * u₂) * htwoL + hu₁ + hu₂⟩
        zero_mem' := ⟨0, zero_pow (by decide)⟩
        inv_mem' := fun {a} ⟨u, hu⟩ => ⟨u⁻¹, by rw [inv_pow, hu]⟩
        algebraMap_mem' := fun c => by
          obtain ⟨d, hd_odd, hcd⟩ := c.2
          have hd1 : 1 ≤ d := by rcases hd_odd with ⟨k, hk⟩; omega
          let sΩ : Ω := c.1 ^ (2 ^ (d - 1))
          have hsΩ_sq : sΩ ^ 2 = c.1 := by
            dsimp [sΩ]
            rw [← pow_mul, ← pow_succ, show d - 1 + 1 = d by omega, hcd]
          have hs_in_K : sΩ ∈ K_int := ⟨d, hd_odd, by
            dsimp [sΩ]
            rw [← pow_mul, mul_comm, pow_mul, hcd]⟩
          refine ⟨algebraMap K_int L_int ⟨sΩ, hs_in_K⟩, ?_⟩
          apply Subtype.ext
          exact hsΩ_sq }
    let genω : L_int := IntermediateField.AdjoinSimple.gen K_int ω
    have hgen_in_Sq : genω ∈ SqField := by
      refine ⟨genω + 1, ?_⟩
      apply Subtype.ext
      change (ω + 1) ^ 2 = ω
      calc (ω + 1) ^ 2 = ω ^ 2 + 1 ^ 2 := by linear_combination ω * htwoΩ
        _ = (ω + 1) + 1 := by rw [hω_sq, one_pow]
        _ = ω + 2 * 1 := by ring
        _ = ω := by rw [htwoΩ]; ring
    have hSq_top : SqField = ⊤ := by
      have hle : L_int ≤ SqField.map L_int.val := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact ⟨genω, hgen_in_Sq, rfl⟩
      ext w
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨y, hy, hyw⟩ := hle w.2
      exact (L_int.val.injective hyw) ▸ hy
    intro w
    have hw_mem : w ∈ SqField := hSq_top ▸ IntermediateField.mem_top
    exact hw_mem
  -- 6. `¬ IsGarlingAlgebraicallyClosed L_int`.
  have hnot_closed_L : ¬ IsGarlingAlgebraicallyClosed L_int := by
    intro hclosed
    let L_even_odd : IntermediateField K_int Ω :=
      { carrier := {z : Ω | ∃ d : ℕ, Odd d ∧ z ^ (2 ^ (2 * d)) = z}
        mul_mem' := fun {a b} ⟨d₁, hd₁, ha⟩ ⟨d₂, hd₂, hb⟩ =>
          ⟨d₁ * d₂, hd₁.mul hd₂, by
            rw [mul_pow, show 2 * (d₁ * d₂) = (2 * d₁) * d₂ by ring, hpow_mul ha d₂,
              show (2 * d₁) * d₂ = (2 * d₂) * d₁ by ring, hpow_mul hb d₁]⟩
        one_mem' := ⟨1, odd_one, by simp⟩
        add_mem' := fun {a b} ⟨d₁, hd₁, ha⟩ ⟨d₂, hd₂, hb⟩ =>
          ⟨d₁ * d₂, hd₁.mul hd₂, by
            rw [add_pow_char_pow a b,
              show 2 * (d₁ * d₂) = (2 * d₁) * d₂ by ring, hpow_mul ha d₂,
              show (2 * d₁) * d₂ = (2 * d₂) * d₁ by ring, hpow_mul hb d₁]⟩
        zero_mem' := ⟨1, odd_one, by simp⟩
        inv_mem' := fun {a} ⟨d, hd, ha⟩ => ⟨d, hd, by rw [inv_pow, ha]⟩
        algebraMap_mem' := fun c => by
          obtain ⟨d, hd, hcd⟩ := c.2
          exact ⟨d, hd, by rw [mul_comm 2 d]; exact hpow_mul hcd 2⟩ }
    have hL_le_eo : L_int ≤ L_even_odd := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨1, odd_one, hω_fourth⟩
    let p4 : L_int[X] := Polynomial.X ^ 4 + Polynomial.X + 1
    have hp4_deg : p4.natDegree = 4 := by dsimp [p4]; compute_degree!
    have hp4_ne0 : p4.natDegree ≠ 0 := by rw [hp4_deg]; decide
    have _ : IsAlgClosed L_int := (isGarlingAlgebraicallyClosed_iff L_int).mp hclosed
    obtain ⟨lam, hlam_root⟩ := IsAlgClosed.exists_root p4
      (Polynomial.degree_ne_of_natDegree_ne hp4_ne0)
    rw [Polynomial.IsRoot.def] at hlam_root
    have hlam4 : lam.1 ^ 4 = lam.1 + 1 := by
      have h0 : lam.1 ^ 4 + lam.1 + 1 = 0 := by
        have hv := congrArg Subtype.val hlam_root
        simpa [p4] using hv
      linear_combination h0 - (lam.1 + 1) * htwoΩ
    have hlam16 : lam.1 ^ 16 = lam.1 := by
      calc lam.1 ^ 16 = (lam.1 ^ 4) ^ 4 := by ring
        _ = (lam.1 + 1) ^ 4 := by rw [hlam4]
        _ = lam.1 ^ 4 + 1 := by
            linear_combination (2 * lam.1 ^ 3 + 3 * lam.1 ^ 2 + 2 * lam.1) * htwoΩ
        _ = (lam.1 + 1) + 1 := by rw [hlam4]
        _ = lam.1 + 2 * 1 := by ring
        _ = lam.1 := by rw [htwoΩ]; ring
    have hlam_4k : ∀ k : ℕ, lam.1 ^ (2 ^ (4 * k)) = lam.1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 4 * (k + 1) = 4 * k + 4 by omega, pow_add, pow_mul, ih]
        exact hlam16
    obtain ⟨d, ⟨k, hk⟩, hlam_eo⟩ := hL_le_eo lam.2
    have h4k2 : lam.1 ^ (2 ^ (2 * d)) = lam.1 + 1 := by
      rw [hk, show 2 * (2 * k + 1) = 4 * k + 2 by omega, pow_add, pow_mul, hlam_4k k]
      exact hlam4
    rw [h4k2] at hlam_eo
    have h10 : (1 : Ω) = 0 := by linear_combination hlam_eo
    exact one_ne_zero h10
  exact ⟨K_int, L_int, inferInstance, inferInstance, inferInstance, inferInstance,
    hsf_K, hcharK, hdim_KL, hsqrt_L, hodd_root_K, hnot_closed_L⟩

/-! ## §11.5 The theorem on natural irrationalities (printed pp. 99–100, PDF pp. 107–108) -/

/-- **§11.5 Introductory Prose Example** (printed p. 99 / PDF p. 107):
*"For example suppose that `f` is separable over `K`, that `F : K` is a splitting field extension
for `f` over `K` and that `F : L : K`. Then `Γ_L(f) = Γ(F:L) ⊆ Γ(F:K) = Γ_K(f)`."* -/
theorem section_11_5_intermediate_example {F : Type u} [Field F] (K L : Subfield F)
    (hKL : K ≤ L) {f : K[X]} (hf0 : f ≠ 0)
    (hsep : IsGarlingSeparablePoly f)
    (hsf : IsGarlingSplittingFieldExtension K F f) :
    let incKL : K →+* L := Subfield.inclusion hKL
    let fL : L[X] := f.map incKL
    IsGarlingSplittingFieldExtension L F fL ∧
    IsGarlingSeparablePoly fL ∧
    garlingPolyGaloisSubgroup L F fL = garlingGamma L ∧
    garlingPolyGaloisSubgroup K F f = garlingGamma K ∧
    garlingGamma L ≤ garlingGamma K := by
  intro incKL fL
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff incKL.injective).mpr hf0
  have hcomp : L.subtype.comp incKL = K.subtype := rfl
  have hsf_LF : IsGarlingSplittingFieldExtension L F fL := by
    rw [isGarlingSplittingFieldExtension_iff L F fL]
    have ⟨hsp_KF, hadj_KF⟩ := (isGarlingSplittingFieldExtension_iff K F f).mp hsf
    refine ⟨?_, ?_⟩
    · dsimp [fL]
      rw [Polynomial.map_map]
      exact hsp_KF
    · rw [eq_top_iff]
      intro z _
      have hz_K : z ∈ Algebra.adjoin K (f.rootSet F) := by
        rw [hadj_KF]; trivial
      have hroots_eq : f.rootSet F = fL.rootSet F := by
        ext r
        rw [Polynomial.mem_rootSet_of_ne hf0, Polynomial.mem_rootSet_of_ne hfL0]
        dsimp [fL]
        simp only [Polynomial.aeval_def, Polynomial.eval₂_map]
        rfl
      rw [← hroots_eq]
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz_K
      · intro r hr
        exact Algebra.subset_adjoin hr
      · intro k
        exact Subalgebra.algebraMap_mem (Algebra.adjoin L (f.rootSet F)) (incKL k)
      · intro x y _ _ hx hy
        exact Subalgebra.add_mem _ hx hy
      · intro x y _ _ hx hy
        exact Subalgebra.mul_mem _ hx hy
  have hsep_KF : IsGarlingSeparableExtension K F := corollary_3_to_theorem_10_3 hsep hsf
  have hsep_LF : IsGarlingSeparableExtension L F := by
    let L_int : IntermediateField K F := subfieldToIntermediateField hKL
    have hsep_Lint : IsGarlingSeparableExtension L_int F :=
      (theorem_10_1_tower (K := K) (M := L_int) (L := F) hsep_KF).1
    let eL : L_int ≃+* L :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    intro x
    obtain ⟨⟨p, hp0, hpeval⟩, hmin_sep⟩ := hsep_Lint x
    have halg_L : IsGarlingAlgebraic L x := by
      refine ⟨p.map eL.toRingHom, (Polynomial.map_ne_zero_iff eL.injective).mpr hp0, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact hpeval
    have hint_Lint : IsIntegral L_int x :=
      (isGarlingAlgebraic_iff_isIntegral L_int x).mp ⟨p, hp0, hpeval⟩
    have hirr_map : Irreducible ((minpoly L_int x).map eL.toRingHom) := by
      have heq_map : (minpoly L_int x).map eL.toRingHom =
          Polynomial.mapEquiv eL (minpoly L_int x) := rfl
      rw [heq_map]
      exact (minpoly.irreducible hint_Lint).map (Polynomial.mapEquiv eL)
    have hmin_map : minpoly L x = (minpoly L_int x).map eL.toRingHom := by
      have hmon : ((minpoly L_int x).map eL.toRingHom).Monic :=
        (minpoly.monic hint_Lint).map eL.toRingHom
      have haev : Polynomial.aeval x ((minpoly L_int x).map eL.toRingHom) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        exact minpoly.aeval L_int x
      exact (minpoly.eq_of_irreducible_of_monic hirr_map haev hmon).symm
    have hsep_min_Lint : (minpoly L_int x).Separable :=
      (isGarlingSeparablePoly_of_irreducible_iff (minpoly.irreducible hint_Lint)).mp hmin_sep
    have hsep_min_L : (minpoly L x).Separable := by
      rw [hmin_map]
      exact hsep_min_Lint.map
    have hirr_min_L : Irreducible (minpoly L x) := hmin_map ▸ hirr_map
    exact ⟨halg_L, (isGarlingSeparablePoly_of_irreducible_iff hirr_min_L).mpr hsep_min_L⟩
  have hsep_fL : IsGarlingSeparablePoly fL :=
    (isGarlingSeparableExtension_iff_poly_of_splittingField hfL0 hsf_LF).mp hsep_LF
  have hsub_L : garlingPolyGaloisSubgroup L F fL = garlingGamma L := by
    ext σ
    simp only [mem_garlingGaloisSubgroup_iff, mem_garlingGamma_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hsub_K : garlingPolyGaloisSubgroup K F f = garlingGamma K := by
    ext σ
    simp only [mem_garlingGaloisSubgroup_iff, mem_garlingGamma_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  exact ⟨hsf_LF, hsep_fL, hsub_L, hsub_K, garlingGamma_anti hKL⟩

/-- **Counterexample to the literal `f = 0` edge case of `Theorem 11.9`**
(§11.5, printed pp. 99–100 / PDF pp. 107–108; `BRIEF.md` Flag 4 & `QUEUE.md`):
on `K = ℚ`, `L = N = FractionRing ℚ[X]`, and `f = 0 ∈ ℚ[X]`, `N : L` is a splitting field
extension for `0` over `L`, yet the root set `garlingRootSet ℚ N 0 = Set.univ` is **infinite**
(cannot be enumerated by any finite tuple `α₁, …, α_n`) and generates `M = N ≠ ℚ`, which is **not**
a splitting field extension for `0` over `ℚ` (refuting the parenthetical *"so that `M : K` is a
splitting field extension for `f` over `K`"*). -/
theorem theorem_11_9_zero_counterexample :
    let N := FractionRing ℚ[X]
    IsGarlingSplittingFieldExtension N N ((0 : ℚ[X]).map (algebraMap ℚ N)) ∧
    garlingRootSet ℚ N 0 = Set.univ ∧
    (garlingRootSet ℚ N 0).Infinite ∧
    (¬ ∃ (n : ℕ) (α : Fin n → N), Set.range α = garlingRootSet ℚ N 0) ∧
    ¬ IsGarlingSplittingFieldExtension ℚ (IntermediateField.adjoin ℚ (garlingRootSet ℚ N 0)) 0 := by
  intro N
  have hsf_NN : IsGarlingSplittingFieldExtension N N ((0 : ℚ[X]).map (algebraMap ℚ N)) := by
    rw [Polynomial.map_zero, isGarlingSplittingFieldExtension_zero_iff]
    exact Subsingleton.elim _ _
  have hroots_univ : garlingRootSet ℚ N 0 = Set.univ := by
    ext x
    simp [garlingRootSet]
  have hinf : (garlingRootSet ℚ N 0).Infinite := by
    rw [hroots_univ]
    exact Set.infinite_univ
  have hno_tuple : ¬ ∃ (n : ℕ) (α : Fin n → N), Set.range α = garlingRootSet ℚ N 0 := by
    rintro ⟨n, α, hrange⟩
    exact hinf (hrange ▸ Set.finite_range α)
  have hnot_sf_QM :
      ¬ IsGarlingSplittingFieldExtension ℚ (IntermediateField.adjoin ℚ (garlingRootSet ℚ N 0)) 0 := by
    rw [isGarlingSplittingFieldExtension_zero_iff,
      bot_eq_top_iff_surjective_algebraMap]
    intro hsurj
    let t : N := ratFuncVar ℚ
    have ht_mem : t ∈ IntermediateField.adjoin ℚ (garlingRootSet ℚ N 0) := by
      rw [hroots_univ, IntermediateField.adjoin_univ]
      trivial
    obtain ⟨q, hq⟩ := hsurj ⟨t, ht_mem⟩
    have ht_eq : algebraMap ℚ N q = t := congrArg Subtype.val hq
    have hC_eq : algebraMap ℚ[X] N (Polynomial.C q) = algebraMap ℚ N q :=
      (map_ratCast ((algebraMap ℚ[X] N).comp Polynomial.C) q).trans
        (map_ratCast (algebraMap ℚ N) q).symm
    have hpoly_eq : (Polynomial.C q : ℚ[X]) = Polynomial.X :=
      (IsFractionRing.injective ℚ[X] N) (hC_eq.trans ht_eq)
    have hd := congrArg Polynomial.natDegree hpoly_eq
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X] at hd
    omega
  exact ⟨hsf_NN, hroots_univ, hinf, hno_tuple, hnot_sf_QM⟩

/-- The intermediate field `M = K(α₁, …, α_n) ≤ N` generated over `K` by the roots of `f ∈ K[X]`
in `N` (**Theorem 11.9**, §11.5, printed p. 99 / PDF p. 107). -/
def garlingNatIrrM (K L N : Type*) [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] (f : K[X]) :
    IntermediateField K N :=
  IntermediateField.adjoin K (garlingRootSet K N f)

/-- The intersection subfield `L₀ ∩ M` viewed inside `M = garlingNatIrrM K L N f`, where
`L₀ = φ(Γ_L(f))` is the fixed field of `Γ_L(f)` in `N` (**Theorem 11.9**, §11.5, printed p. 99). -/
def garlingNatIrrInter (K L N : Type*) [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] (f : K[X]) :
    Subfield (garlingNatIrrM K L N f) :=
  (garlingPhi
    (garlingPolyGaloisSubgroup L N (f.map (algebraMap K L)) : Set (GarlingAut N))).comap
      (garlingNatIrrM K L N f).val.toRingHom

@[simp]
theorem mem_garlingNatIrrInter_iff {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] {f : K[X]}
    {x : garlingNatIrrM K L N f} :
    x ∈ garlingNatIrrInter K L N f ↔
      x.1 ∈ garlingPhi
        (garlingPolyGaloisSubgroup L N (f.map (algebraMap K L)) : Set (GarlingAut N)) :=
  Iff.rfl

/-- Stability of `M = K(α₁, …, α_n)` under any `σ ∈ Γ_L(f)` (`N ≃ₐ[L] N`), supporting the
restriction map `θ : σ ↦ σ|_M` in **Theorem 11.9** (§11.5, p. 100). -/
theorem garlingNatIrrM_stable {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] (f : K[X])
    (σ : GarlingPolyGaloisGroup L N (f.map (algebraMap K L)))
    {x : N} (hx : x ∈ garlingNatIrrM K L N f) :
    σ x ∈ garlingNatIrrM K L N f := by
  let σK : N ≃ₐ[K] N := σ.restrictScalars K
  have hle : garlingNatIrrM K L N f ≤ (garlingNatIrrM K L N f).comap σK.toAlgHom := by
    rw [garlingNatIrrM, IntermediateField.adjoin_le_iff]
    intro r hr
    change σK r ∈ garlingNatIrrM K L N f
    have hr0 : Polynomial.aeval r f = 0 := hr
    have hσr0 : Polynomial.aeval (σK r) f = 0 := by
      change Polynomial.aeval (σK.toAlgHom r) f = 0
      rw [Polynomial.aeval_algHom_apply σK.toAlgHom r f, hr0, map_zero]
    exact IntermediateField.subset_adjoin K (garlingRootSet K N f) hσr0
  exact hle hx

/-- The restriction homomorphism `θ : σ ↦ σ|_M` from `Γ_L(f)` into `Aut M` in **Theorem 11.9**
(§11.5, printed pp. 99–100 / PDF pp. 107–108). -/
def garlingNatIrrTheta (K L N : Type*) [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] (f : K[X]) :
    GarlingPolyGaloisGroup L N (f.map (algebraMap K L)) →*
      GarlingAut (garlingNatIrrM K L N f) where
  toFun σ :=
    { toFun := fun x => ⟨σ x.1, garlingNatIrrM_stable f σ x.2⟩
      invFun := fun x => ⟨σ.symm x.1, garlingNatIrrM_stable f σ.symm x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[simp]
theorem garlingNatIrrTheta_apply_coe {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] (f : K[X])
    (σ : GarlingPolyGaloisGroup L N (f.map (algebraMap K L)))
    (x : garlingNatIrrM K L N f) :
    ((garlingNatIrrTheta K L N f σ) x : N) = σ x.1 := rfl

/-- **Theorem 11.9** (*The theorem on natural irrationalities*, §11.5, printed pp. 99–100 /
PDF pp. 107–108; see `QUEUE.md` on `f = 0`):
*"Suppose that `f ∈ K[x]` and that `L : K` is an extension. Let `N : L` be a splitting field
extension for `f` over `L`, let `α₁, …, α_n` be the roots of `f` in `N` and let `M = K(α₁, …, α_n)`
(so that `M : K` is a splitting field extension for `f` over `K`). Let `L₀` be the fixed field of
`Γ_L(f)`. Then if `σ ∈ Γ_L(f)`, `σ|_M ∈ Γ(M : L₀ ∩ M)`, and the map `θ : σ → σ|_M` is an
isomorphism of `Γ_L(f)` onto the subgroup `Γ(M : L₀ ∩ M)` of `Γ_K(f)`."*

Proved across arbitrary universes `u, v, w` for all `f ≠ 0` (including degree-`0` non-zero
constants `n = 0`) following Garling's p. 100 proof via `Theorem 11.3`. -/
theorem theorem_11_9 {K : Type u} {L : Type v} {N : Type w}
    [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    {f : K[X]} (hf0 : f ≠ 0)
    (hsf_LN : IsGarlingSplittingFieldExtension L N (f.map (algebraMap K L))) :
    let fL : L[X] := f.map (algebraMap K L)
    let M := garlingNatIrrM K L N f
    let L₀_inter_M := garlingNatIrrInter K L N f
    let θ := garlingNatIrrTheta K L N f
    -- 1. Existence of finite root tuple `α₁, …, α_n` generating `M = K(α₁, …, α_n)` & splitting field `M : K`
    (∃ (n : ℕ) (α : Fin n → N),
      Set.range α = garlingRootSet K N f ∧
      IntermediateField.adjoin K (Set.range α) = M) ∧
    IsGarlingSplittingFieldExtension K M f ∧
    -- 2. `Γ(M : L₀ ∩ M)` is a subgroup of `Γ_K(f) = garlingPolyGaloisSubgroup K M f`
    garlingGamma L₀_inter_M ≤ garlingPolyGaloisSubgroup K M f ∧
    -- 3. Every `σ ∈ Γ_L(f)` restricts into `Γ(M : L₀ ∩ M)`, and `θ` is injective with range `Γ(M : L₀ ∩ M)`
    (∀ σ : GarlingPolyGaloisGroup L N fL, θ σ ∈ garlingGamma L₀_inter_M) ∧
    Function.Injective θ ∧
    θ.range = garlingGamma L₀_inter_M ∧
    -- 4. Group isomorphism `Γ_L(f) ≃* Γ(M : L₀ ∩ M)`
    Nonempty (GarlingPolyGaloisGroup L N fL ≃* garlingGamma L₀_inter_M) ∧
    Nonempty (GarlingPolyGaloisGroup L N fL ≃* GarlingGaloisGroup L₀_inter_M M) := by
  classical
  intro fL M L₀_inter_M θ
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  have ⟨hsp_LN, hadj_LN⟩ := (isGarlingSplittingFieldExtension_iff L N fL).mp hsf_LN
  have hsp_KN : (f.map (algebraMap K N)).Splits := by
    rw [IsScalarTower.algebraMap_eq K L N, ← Polynomial.map_map]
    exact hsp_LN
  have hrootSet_eq : garlingRootSet K N f = f.rootSet N := garlingRootSet_eq_rootSet hf0
  -- 1. Finite tuple `α₁, …, α_n` of roots of `f` in `N`, and `IsGarlingSplittingFieldExtension K M f`.
  have hfin_roots : (garlingRootSet K N f).Finite := by
    rw [hrootSet_eq]
    exact Polynomial.rootSet_finite f N
  let sFin : Finset N := hfin_roots.toFinset
  let eFin : Fin sFin.card ≃ sFin := sFin.equivFin.symm
  have htuple : ∃ (n : ℕ) (α : Fin n → N),
      Set.range α = garlingRootSet K N f ∧
      IntermediateField.adjoin K (Set.range α) = M := by
    refine ⟨sFin.card, fun i => (eFin i).1, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact hfin_roots.mem_toFinset.mp (eFin i).2
      · intro hx
        have hxS : x ∈ sFin := hfin_roots.mem_toFinset.mpr hx
        exact ⟨eFin.symm ⟨x, hxS⟩, by simp⟩
    · congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact hfin_roots.mem_toFinset.mp (eFin i).2
      · intro hx
        have hxS : x ∈ sFin := hfin_roots.mem_toFinset.mpr hx
        exact ⟨eFin.symm ⟨x, hxS⟩, by simp⟩
  have hsf_KM : IsGarlingSplittingFieldExtension K M f := by
    rw [isGarlingSplittingFieldExtension_iff K M f]
    change Polynomial.IsSplittingField K (IntermediateField.adjoin K (garlingRootSet K N f)) f
    rw [hrootSet_eq]
    exact IntermediateField.adjoin_rootSet_isSplittingField hsp_KN
  -- 2. `garlingGamma L₀_inter_M ≤ garlingPolyGaloisSubgroup K M f` (since `K ⊆ L ⊆ L₀` and `K ⊆ M`).
  have hK_le_inter : (algebraMap K M).fieldRange ≤ L₀_inter_M := by
    rintro _ ⟨k, rfl⟩
    rw [mem_garlingNatIrrInter_iff, mem_garlingPhi_iff]
    intro τ hτ
    change τ (algebraMap K N k) = algebraMap K N k
    rw [IsScalarTower.algebraMap_apply K L N k]
    exact mem_garlingGaloisSubgroup_iff.mp hτ (algebraMap K L k)
  have hsub_galK : garlingGamma L₀_inter_M ≤ garlingPolyGaloisSubgroup K M f :=
    garlingGamma_anti hK_le_inter
  -- 3a. Every `θ σ` fixes `L₀_inter_M`.
  have hθ_mem : ∀ σ : GarlingPolyGaloisGroup L N fL, θ σ ∈ garlingGamma L₀_inter_M := by
    intro σ x hx
    apply Subtype.ext
    change σ x.1 = x.1
    have hσ_mem : σ.toRingEquiv ∈ garlingPolyGaloisSubgroup L N fL :=
      (garlingGaloisGroupMulEquiv L N σ).2
    exact hx σ.toRingEquiv hσ_mem
  -- 3b. `θ` is injective: if `θ σ = 1`, `σ` fixes all roots of `f` in `N` and fixes `L`, hence fixes `N`.
  have hroots_fL : fL.rootSet N = garlingRootSet K N f := by
    ext r
    rw [Polynomial.mem_rootSet_of_ne hfL0, mem_garlingRootSet_iff]
    dsimp [fL]
    rw [Polynomial.aeval_map_algebraMap]
  have hθ_inj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ1
    rw [MonoidHom.mem_ker] at hσ1
    have hfix_roots : ∀ r ∈ fL.rootSet N, σ r = r := by
      intro r hr
      have hrK : r ∈ garlingRootSet K N f := hroots_fL ▸ hr
      let rM : M := ⟨r, IntermediateField.subset_adjoin K (garlingRootSet K N f) hrK⟩
      have h1 := congrArg (fun g : GarlingAut M => (g rM : N)) hσ1
      exact h1
    let eqSub : Subalgebra L N := AlgHom.equalizer σ.toAlgHom (AlgHom.id L N)
    have htop_le : (⊤ : Subalgebra L N) ≤ eqSub := by
      rw [← hadj_LN, Algebra.adjoin_le_iff]
      intro r hr
      exact hfix_roots r hr
    ext z
    exact htop_le (trivial : z ∈ (⊤ : Subalgebra L N))
  -- 3c. Garling's p. 100 proof via `Theorem 11.3`: `φ(θ.range) = L₀ ∩ M`, so `θ.range = γ(L₀ ∩ M)`!
  have hfin_LN : IsFiniteExtension L N := (corollary_to_theorem_7_1 hsf_LN).1
  have _ : Module.Finite L N := (isFiniteExtension_iff_moduleFinite L N).mp hfin_LN
  have _ : Finite (GarlingPolyGaloisGroup L N fL) := Finite.of_fintype (N ≃ₐ[L] N)
  have _ : Finite θ.range := Set.finite_range θ
  have hphi_range : garlingPhi (θ.range : Set (GarlingAut M)) = L₀_inter_M := by
    ext x
    rw [mem_garlingPhi_iff, mem_garlingNatIrrInter_iff, mem_garlingPhi_iff]
    constructor
    · intro hx τ hτ
      let σ : GarlingPolyGaloisGroup L N fL :=
        (garlingGaloisGroupMulEquiv L N).symm ⟨τ, hτ⟩
      have h1 : θ σ x = x := hx (θ σ) ⟨σ, rfl⟩
      exact congrArg Subtype.val h1
    · rintro hx _ ⟨σ, rfl⟩
      apply Subtype.ext
      change σ x.1 = x.1
      exact hx σ.toRingEquiv (garlingGaloisGroupMulEquiv L N σ).2
  have hrange_eq : θ.range = garlingGamma L₀_inter_M := by
    have h113 := (theorem_11_3 θ.range).2.2.2.1
    rwa [hphi_range] at h113
  -- 4. Construct `Γ_L(f) ≃* garlingGamma L₀_inter_M` and `Γ_L(f) ≃* GarlingGaloisGroup L₀_inter_M M`.
  let eRange : GarlingPolyGaloisGroup L N fL ≃* θ.range :=
    MulEquiv.ofBijective θ.rangeRestrict
      ⟨fun a b hab => hθ_inj (congrArg Subtype.val hab), θ.rangeRestrict_surjective⟩
  let eGamma : GarlingPolyGaloisGroup L N fL ≃* garlingGamma L₀_inter_M :=
    eRange.trans (MulEquiv.subgroupCongr hrange_eq)
  let eGal : GarlingPolyGaloisGroup L N fL ≃* GarlingGaloisGroup L₀_inter_M M :=
    eGamma.trans (garlingGaloisGroupSubfieldMulEquiv L₀_inter_M).symm
  exact ⟨htuple, hsf_KM, hsub_galK, hθ_mem, hθ_inj, hrange_eq, ⟨eGamma⟩, ⟨eGal⟩⟩

/-- **§11.5 Closing Separable Remark** (printed p. 100 / PDF p. 108):
*"Note that if `f` is separable over `K`, then `f` is separable over `L`, and so `L = L₀`: in this
case the theorem becomes a little simpler."*

When `f ≠ 0` is separable over `K`, `f.map (algebraMap K L)` is separable over `L`, `L₀` equals
`(algebraMap L N).fieldRange`, `L₀ ∩ M = L ∩ M`, and `Γ_L(f) ≃* Γ(M : L ∩ M)` (with `[N : L] =
[M : L ∩ M]`). -/
theorem theorem_11_9_separable {K : Type u} {L : Type v} {N : Type w}
    [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    {f : K[X]} (hf0 : f ≠ 0) (hsep : IsGarlingSeparablePoly f)
    (hsf_LN : IsGarlingSplittingFieldExtension L N (f.map (algebraMap K L))) :
    let fL : L[X] := f.map (algebraMap K L)
    let M := garlingNatIrrM K L N f
    let L_inter_M : Subfield M := (algebraMap L N).fieldRange.comap M.val.toRingHom
    IsGarlingSeparablePoly fL ∧
    (algebraMap L N).fieldRange =
      garlingPhi (garlingPolyGaloisSubgroup L N fL : Set (GarlingAut N)) ∧
    garlingNatIrrInter K L N f = L_inter_M ∧
    Nonempty (GarlingPolyGaloisGroup L N fL ≃* garlingGamma L_inter_M) ∧
    Nonempty (GarlingPolyGaloisGroup L N fL ≃* GarlingGaloisGroup L_inter_M M) ∧
    Module.finrank L N = Module.finrank L_inter_M M := by
  classical
  intro fL M L_inter_M
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  obtain ⟨⟨n, α, hrange_α, hadj_α⟩, hsf_KM, _, _, _, hrange_eq, ⟨eGamma⟩, _⟩ :=
    theorem_11_9 hf0 hsf_LN
  -- Every root `α i` lies in `M` (which is separable over `K` by `Corollary 3` to `Theorem 10.3`),
  -- hence is separable over `K`, and therefore separable over `L` by `Theorem 10.1`!
  have hsep_KM : IsGarlingSeparableExtension K M := corollary_3_to_theorem_10_3 hsep hsf_KM
  have hα_sep_L : ∀ i : Fin n, IsGarlingSeparableElement L (α i) := by
    intro i
    have hα_in_M : α i ∈ M := by
      change α i ∈ garlingNatIrrM K L N f
      rw [← hadj_α]
      exact IntermediateField.subset_adjoin K (Set.range α) ⟨i, rfl⟩
    let αM : M := ⟨α i, hα_in_M⟩
    have hsep_αM : IsGarlingSeparableElement K αM := hsep_KM αM
    have hmin_eq : minpoly K (α i) = minpoly K αM :=
      minpoly.algHom_eq M.val M.val.injective αM
    have hsep_K : IsGarlingSeparableElement K (α i) := by
      obtain ⟨⟨p, hp0, hpeval⟩, hs⟩ := hsep_αM
      refine ⟨⟨p, hp0, ?_⟩, hmin_eq ▸ hs⟩
      change Polynomial.aeval (M.val αM) p = 0
      rw [Polynomial.aeval_algHom_apply M.val αM p, hpeval, map_zero]
    exact isGarlingSeparableElement_tower_top hsep_K
  -- Since `N = L(α₁, …, α_n)`, `Corollary 2` to `Theorem 10.3` gives `IsGarlingSeparableExtension L N`!
  have hfin_LN : IsFiniteExtension L N := (corollary_to_theorem_7_1 hsf_LN).1
  have hadj_LN_top : IntermediateField.adjoin L (Set.range α) = ⊤ := by
    have ⟨_, hadj_alg⟩ := (isGarlingSplittingFieldExtension_iff L N fL).mp hsf_LN
    have hroots_fL : fL.rootSet N = Set.range α := by
      rw [hrange_α]
      ext r
      rw [Polynomial.mem_rootSet_of_ne hfL0, mem_garlingRootSet_iff]
      dsimp [fL]; rw [Polynomial.aeval_map_algebraMap]
    rw [eq_top_iff]
    intro z _
    have hz_alg : z ∈ Algebra.adjoin L (Set.range α) := by
      rw [← hroots_fL, hadj_alg]; trivial
    exact Algebra.adjoin_le (fun r hr => IntermediateField.subset_adjoin L (Set.range α) hr) hz_alg
  have hsep_LN : IsGarlingSeparableExtension L N :=
    corollary_2_to_theorem_10_3 hfin_LN α hadj_LN_top hα_sep_L
  have hsep_fL : IsGarlingSeparablePoly fL :=
    (isGarlingSeparableExtension_iff_poly_of_splittingField hfL0 hsf_LN).mp hsep_LN
  have h115_L := (theorem_11_5 hfL0 hsf_LN).1 hsep_fL
  have hL_eq_L₀ : (algebraMap L N).fieldRange =
      garlingPhi (garlingPolyGaloisSubgroup L N fL : Set (GarlingAut N)) := h115_L.2.2
  have hinter_eq : garlingNatIrrInter K L N f = L_inter_M := by
    ext x
    change x.1 ∈ garlingPhi (garlingPolyGaloisSubgroup L N fL : Set (GarlingAut N)) ↔
      x.1 ∈ (algebraMap L N).fieldRange
    rw [hL_eq_L₀]
  let eGammaL : GarlingPolyGaloisGroup L N fL ≃* garlingGamma L_inter_M :=
    eGamma.trans (MulEquiv.subgroupCongr (congrArg garlingGamma hinter_eq))
  let eGalL : GarlingPolyGaloisGroup L N fL ≃* GarlingGaloisGroup L_inter_M M :=
    eGammaL.trans (garlingGaloisGroupSubfieldMulEquiv L_inter_M).symm
  -- Degree equality `[N : L] = |Γ_L(f)| = |Γ(M : L ∩ M)| = [M : L ∩ M]` (`Theorem 11.3`).
  have _ : Module.Finite L N := (isFiniteExtension_iff_moduleFinite L N).mp hfin_LN
  have _ : Finite (GarlingPolyGaloisGroup L N fL) := Finite.of_fintype (N ≃ₐ[L] N)
  have _ : Finite (garlingGamma L_inter_M) :=
    Equiv.finite_iff eGammaL.symm.toEquiv |>.mpr inferInstance
  have hphi_inter : garlingPhi (garlingGamma L_inter_M : Set (GarlingAut M)) = L_inter_M := by
    rw [← hinter_eq, ← hrange_eq]
    have h113_theta := (theorem_11_3 (garlingNatIrrTheta K L N f).range).2.2.2.1
    -- Actually from `theorem_11_9`'s proof, `garlingGamma (garlingNatIrrInter K L N f) = θ.range`,
    -- and `garlingPhi θ.range = garlingNatIrrInter K L N f`:
    ext x
    rw [mem_garlingPhi_iff, mem_garlingNatIrrInter_iff, mem_garlingPhi_iff]
    constructor
    · intro hx τ hτ
      let σ : GarlingPolyGaloisGroup L N fL :=
        (garlingGaloisGroupMulEquiv L N).symm ⟨τ, hτ⟩
      exact congrArg Subtype.val (hx (garlingNatIrrTheta K L N f σ) ⟨σ, rfl⟩)
    · rintro hx _ ⟨σ, rfl⟩
      exact Subtype.ext (hx σ.toRingEquiv (garlingGaloisGroupMulEquiv L N σ).2)
  have hdeg_M : Nat.card (garlingGamma L_inter_M) = Module.finrank L_inter_M M := by
    have h113_M := (theorem_11_3 (garlingGamma L_inter_M)).2.2.1
    rwa [hphi_inter] at h113_M
  have hdeg_eq : Module.finrank L N = Module.finrank L_inter_M M := by
    rw [← h115_L.2.1, Nat.card_congr eGammaL.toEquiv, hdeg_M]
  exact ⟨hsep_fL, hL_eq_L₀, hinter_eq, ⟨eGammaL⟩, ⟨eGalL⟩, hdeg_eq⟩

end Garling.Chapter11
