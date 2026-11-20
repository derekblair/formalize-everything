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
import Garling.Chapter11
import Garling.Chapter12
import Garling.Chapter13
import Garling.Chapter14
import Garling.Chapter15
import Garling.Chapter16
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup

/-!
# Chapter 17: Solution by radicals

Formalization of Chapter 17 (*Solution by radicals*, printed pp. 131–138 / PDF pp. 139–146)
of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
6-line unnumbered chapter preamble, all four sections (`§17.1`–`§17.4`), all 7 main-text
theorem/corollary items (`Theorem 17.1`–`Theorem 17.6` + unnumbered `Corollary` [to `Theorem 17.2`]),
all 7 numbered exercises (`Exercise 17.1`–`Exercise 17.7`), and all unnumbered inline prose
definitions and results in exact source order.

Note: `Garling.Chapter15` and `Garling.Chapter16` are both imported (both merged on main), and
qualified explicitly where needed to avoid name overlap between their independent definitions of
`IsGarlingPrimitiveRoot` and `pos_and_natCast_ne_zero_of_not_ringChar_dvd`.
-/

namespace Garling.Chapter17

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter08 Garling.Chapter09
open Garling.Chapter10 Garling.Chapter11 Garling.Chapter12
open Garling.Chapter14
open scoped BigOperators Polynomial IntermediateField commutatorElement

universe u v w

/-! ## §17.1 Soluble groups: examples (printed pp. 131–132, PDF pp. 139–140) -/

/-- Garling's inline prose definition of a *soluble* group (§17.1, printed p. 131 / PDF p. 139):
*"A group `G` is said to be **soluble** if there is a finite series of subgroups
`{e} = G_n ⊆ G_{n-1} ⊆ … ⊆ G_1 ⊆ G_0 = G` such that (i) `G_i ⊲ G_{i-1}` for `1 ≤ i ≤ n`, and
(ii) `G_{i-1}/G_i` is cyclic, for `1 ≤ i ≤ n`."*

On finite groups this coincides with Mathlib's `Group.IsSolvable G`
(`isGarlingSoluble_iff_isSolvable_of_finite`); on infinite groups it defines polycyclic groups and
is strictly stronger than `Group.IsSolvable` (`additive_rat_isSolvable_not_isGarlingSoluble`). -/
def IsGarlingSoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G),
    H 0 = ⊤ ∧
    H (Fin.last n) = ⊥ ∧
    (∀ i : Fin n, H i.succ ≤ H i.castSucc) ∧
    ∀ i : Fin n,
      ∃ (_ : ((H i.succ).subgroupOf (H i.castSucc)).Normal),
        IsCyclic ((H i.castSucc) ⧸ (H i.succ).subgroupOf (H i.castSucc))

/-- Forward transport of `IsGarlingSoluble` along a group isomorphism `G₁ ≃* G₂`. -/
private theorem isGarlingSoluble_of_mulEquiv {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (φ : G₁ ≃* G₂) (h : IsGarlingSoluble G₁) :
    IsGarlingSoluble G₂ := by
  rcases h with ⟨n, H, h0, hlast, hle, hstep⟩
  refine ⟨n, fun j => (H j).map φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · simp [hlast]
  · intro i
    exact Subgroup.map_mono (hle i)
  · intro i
    obtain ⟨hN, hCyc⟩ := hstep i
    let N₁ : Subgroup (H i.castSucc) := (H i.succ).subgroupOf (H i.castSucc)
    let N₂ : Subgroup ((H i.castSucc).map φ.toMonoidHom) :=
      ((H i.succ).map φ.toMonoidHom).subgroupOf ((H i.castSucc).map φ.toMonoidHom)
    have : N₁.Normal := hN
    let ψ : H i.castSucc ≃* (H i.castSucc).map φ.toMonoidHom :=
      φ.subgroupMap (H i.castSucc)
    have hmapN : N₁.map ψ.toMonoidHom = N₂ := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, N₁, N₂, ψ]
      constructor
      · rintro ⟨⟨x, hx⟩, hxs, heq⟩
        exact ⟨x, hxs, congrArg Subtype.val heq⟩
      · rintro ⟨x, hxs, hxy⟩
        exact ⟨⟨x, hle i hxs⟩, hxs, Subtype.ext hxy⟩
    have hN₂ : N₂.Normal := by
      rw [← hmapN]
      exact hN.map ψ.toMonoidHom ψ.surjective
    have : N₂.Normal := hN₂
    let heqQ : (H i.castSucc ⧸ N₁) ≃* (((H i.castSucc).map φ.toMonoidHom) ⧸ N₂) :=
      QuotientGroup.congr N₁ N₂ ψ hmapN
    exact ⟨hN₂, isCyclic_of_surjective heqQ.toMonoidHom heqQ.surjective⟩

/-- Transport of `IsGarlingSoluble` along a group isomorphism `G₁ ≃* G₂`. -/
theorem isGarlingSoluble_congr {G₁ : Type u} {G₂ : Type v}
    [Group G₁] [Group G₂] (e : G₁ ≃* G₂) :
    IsGarlingSoluble G₁ ↔ IsGarlingSoluble G₂ :=
  ⟨isGarlingSoluble_of_mulEquiv e, isGarlingSoluble_of_mulEquiv e.symm⟩

/-- Every trivial (`Subsingleton`) group is Garling-soluble (`n = 0`). -/
theorem isGarlingSoluble_of_subsingleton {G : Type*} [Group G] [Subsingleton G] :
    IsGarlingSoluble G := by
  refine ⟨0, fun _ => ⊤, rfl, ?_, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  exact Subsingleton.elim _ _

/-- Every cyclic group is Garling-soluble (`n = 1`). -/
theorem isGarlingSoluble_of_isCyclic {G : Type*} [Group G] [IsCyclic G] :
    IsGarlingSoluble G := by
  refine ⟨1, ![⊤, ⊥], rfl, rfl, fun i => by fin_cases i; exact bot_le, fun i => ?_⟩
  fin_cases i
  have hbot : (⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G) = ⊥ := by ext x; simp
  have hN : ((⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)).Normal := by
    rw [hbot]; infer_instance
  refine ⟨hN, ?_⟩
  let e1 : (⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G) ≃*
      (⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G)) :=
    QuotientGroup.quotientMulEquivOfEq hbot
  let e2 : (⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G)) ≃* (⊤ : Subgroup G) :=
    QuotientGroup.quotientBot
  let e3 : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let e : G ≃* ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)) :=
    (e1.trans (e2.trans e3)).symm
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- **§17.1 Prose Proposition (printed p. 131 / PDF p. 139):** Every finitely generated abelian
group (and in particular every finite abelian group) is Garling-soluble. -/
theorem isGarlingSoluble_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] :
    IsGarlingSoluble G := by
  classical
  obtain ⟨s, hs⟩ := Group.FG.out (G := G)
  let n := s.card
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
  let g : Fin n → G := fun k => (e k).1
  let H : Fin (n + 1) → Subgroup G := fun j =>
    Subgroup.closure {x : G | ∃ k : Fin n, (k : ℕ) < n - (j : ℕ) ∧ x = g k}
  have hH0 : H 0 = ⊤ := by
    rw [← hs]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨k, _, rfl⟩
      exact Subgroup.subset_closure (e k).2
    · rw [Subgroup.closure_le]
      intro x hx
      refine Subgroup.subset_closure ⟨e.symm ⟨x, hx⟩, ?_, ?_⟩
      · simp [(e.symm ⟨x, hx⟩).2]
      · simp [g]
  have hHlast : H (Fin.last n) = ⊥ := by
    simp [H]
  have hle : ∀ i : Fin n, H i.succ ≤ H i.castSucc := by
    intro i
    apply Subgroup.closure_mono
    rintro x ⟨k, hk, rfl⟩
    exact ⟨k, by simp only [Fin.val_succ, Fin.val_castSucc] at hk ⊢; omega, rfl⟩
  refine ⟨n, H, hH0, hHlast, hle, fun i => ?_⟩
  let N : Subgroup (H i.castSucc) := (H i.succ).subgroupOf (H i.castSucc)
  have hN : N.Normal := inferInstance
  refine ⟨hN, ?_⟩
  let idx : Fin n := ⟨n - 1 - (i : ℕ), by omega⟩
  have hmem_idx : g idx ∈ H i.castSucc := by
    apply Subgroup.subset_closure
    exact ⟨idx, by simp only [Fin.val_castSucc, idx]; omega, rfl⟩
  refine ⟨⟨QuotientGroup.mk ⟨g idx, hmem_idx⟩, ?_⟩⟩
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hsub : H i.castSucc ≤ Subgroup.closure (insert (g idx) (H i.succ : Set G)) := by
    rw [Subgroup.closure_le]
    rintro z ⟨k, hk, rfl⟩
    simp only [Fin.val_castSucc] at hk
    by_cases hkeq : (k : ℕ) = n - 1 - (i : ℕ)
    · have hk_eq : k = idx := Fin.ext hkeq
      rw [hk_eq]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · apply Subgroup.subset_closure
      apply Set.mem_insert_of_mem
      apply Subgroup.subset_closure
      exact ⟨k, by simp only [Fin.val_succ]; omega, rfl⟩
  let P : Subgroup G :=
    { carrier := {w : G | ∃ m : ℤ, ∃ u ∈ H i.succ, w = g idx ^ m * u}
      one_mem' := ⟨0, 1, (H i.succ).one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨m₁, u₁, hu₁, rfl⟩ ⟨m₂, u₂, hu₂, rfl⟩
        refine ⟨m₁ + m₂, u₁ * u₂, (H i.succ).mul_mem hu₁ hu₂, ?_⟩
        rw [zpow_add]
        calc g idx ^ m₁ * u₁ * (g idx ^ m₂ * u₂)
            = g idx ^ m₁ * (u₁ * g idx ^ m₂) * u₂ := by simp only [mul_assoc]
          _ = g idx ^ m₁ * (g idx ^ m₂ * u₁) * u₂ := by rw [mul_comm u₁ (g idx ^ m₂)]
          _ = g idx ^ m₁ * g idx ^ m₂ * (u₁ * u₂) := by simp only [mul_assoc]
      inv_mem' := by
        rintro a ⟨m, u, hu, rfl⟩
        refine ⟨-m, u⁻¹, (H i.succ).inv_mem hu, ?_⟩
        rw [zpow_neg, mul_inv_rev, mul_comm] }
  have hP : Subgroup.closure (insert (g idx) (H i.succ : Set G)) ≤ P := by
    rw [Subgroup.closure_le]
    rintro w (rfl | hw)
    · exact ⟨1, 1, (H i.succ).one_mem, by simp⟩
    · exact ⟨0, w, hw, by simp⟩
  obtain ⟨m, u, hu, hx_eq⟩ := hP (hsub hx)
  refine ⟨m, ?_⟩
  dsimp only
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
  change ((⟨g idx, hmem_idx⟩ : H i.castSucc) ^ m)⁻¹ * ⟨x, hx⟩ ∈ N
  simp only [N, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv,
    SubgroupClass.coe_zpow, hx_eq]
  simpa [mul_assoc] using hu

/-- Every finite abelian group is Garling-soluble. -/
theorem isGarlingSoluble_of_commGroup_finite {G : Type*} [CommGroup G] [Finite G] :
    IsGarlingSoluble G := by
  have : Group.FG G := Group.fg_of_finite
  exact isGarlingSoluble_of_commGroup_fg

/-- Helper: given a Garling-soluble series `H : Fin (m + 2) → Subgroup G`, the tail
`H 1 ≥ H 2 ≥ … ≥ H (m + 1) = ⊥` gives a length-`m` soluble series for `H 1`. -/
private theorem isGarlingSoluble_tail {G : Type*} [Group G] {m : ℕ}
    (H : Fin (m + 2) → Subgroup G)
    (hlast : H (Fin.last (m + 1)) = ⊥)
    (hle : ∀ i : Fin (m + 1), H i.succ ≤ H i.castSucc)
    (hstep : ∀ i : Fin (m + 1),
      ∃ (_ : ((H i.succ).subgroupOf (H i.castSucc)).Normal),
        IsCyclic ((H i.castSucc) ⧸ (H i.succ).subgroupOf (H i.castSucc))) :
    ∃ H' : Fin (m + 1) → Subgroup (H 1),
      H' 0 = ⊤ ∧
      H' (Fin.last m) = ⊥ ∧
      (∀ i : Fin m, H' i.succ ≤ H' i.castSucc) ∧
      ∀ i : Fin m,
        ∃ (_ : ((H' i.succ).subgroupOf (H' i.castSucc)).Normal),
          IsCyclic ((H' i.castSucc) ⧸ (H' i.succ).subgroupOf (H' i.castSucc)) := by
  let K : Subgroup G := H 1
  have hle1 : ∀ j : Fin (m + 1), H j.succ ≤ K := by
    intro ⟨k, hk⟩
    induction k with
    | zero => exact le_refl _
    | succ r ihr => exact (hle ⟨r + 1, by omega⟩).trans (ihr (by omega))
  let H' : Fin (m + 1) → Subgroup K := fun j => (H j.succ).subgroupOf K
  refine ⟨H', ?_, ?_, ?_, ?_⟩
  · ext ⟨x, hx⟩; simp [H', K]
  · ext ⟨x, hx⟩
    have hl : (Fin.last m).succ = Fin.last (m + 1) := rfl
    simp [H', hl, hlast]
  · intro i ⟨x, _⟩ hx; exact hle i.succ hx
  · intro i
    obtain ⟨hNi, hCyci⟩ := hstep i.succ
    let N1 : Subgroup (H' i.castSucc) := (H' i.succ).subgroupOf (H' i.castSucc)
    let N2 : Subgroup (H i.succ.castSucc) := (H i.succ.succ).subgroupOf (H i.succ.castSucc)
    have : N2.Normal := hNi
    let eSub : H' i.castSucc ≃* H i.succ.castSucc :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hle1 i.castSucc y.2⟩, y.2⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl
        map_mul' := fun _ _ => rfl }
    have hmap : N1.map eSub.toMonoidHom = N2 := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, N1, N2, H', eSub]
      constructor
      · rintro ⟨⟨⟨x, _⟩, _⟩, hx2, heq⟩
        have hxy : x = y := congrArg Subtype.val heq
        simpa [hxy] using hx2
      · intro hy2
        exact ⟨⟨⟨y, hle1 i.castSucc hy⟩, hy⟩, hy2, rfl⟩
    have hN1 : N1.Normal := by
      have hcomap : N2.comap eSub.toMonoidHom = N1 := by
        rw [← hmap]; ext x; simp only [Subgroup.mem_comap, Subgroup.mem_map]
        exact ⟨fun ⟨y, hy, heq⟩ => (eSub.injective heq) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
      rw [← hcomap]
      exact hNi.comap eSub.toMonoidHom
    have : N1.Normal := hN1
    let eQ : (H' i.castSucc ⧸ N1) ≃* (H i.succ.castSucc ⧸ N2) :=
      QuotientGroup.congr N1 N2 eSub hmap
    exact ⟨hN1, isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective⟩

/-- Helper: in a Garling-soluble series `H : Fin (m + 2) → Subgroup G` with `H 0 = ⊤`,
`H 1` is normal in `G` and `G ⧸ H 1` is cyclic. -/
private theorem isGarlingSoluble_head {G : Type*} [Group G] {m : ℕ}
    (H : Fin (m + 2) → Subgroup G) (h0 : H 0 = ⊤)
    (hstep0 : ∃ (_ : ((H 1).subgroupOf (H 0)).Normal),
      IsCyclic ((H 0) ⧸ (H 1).subgroupOf (H 0))) :
    ∃ (_ : (H 1).Normal), IsCyclic (G ⧸ H 1) := by
  obtain ⟨hN0, hCyc0⟩ := hstep0
  let N0 : Subgroup (H 0) := (H 1).subgroupOf (H 0)
  have : N0.Normal := hN0
  let eTop : H 0 ≃* G := (MulEquiv.subgroupCongr h0).trans Subgroup.topEquiv
  have hmap0 : N0.map eTop.toMonoidHom = H 1 := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, N0, eTop]
    constructor
    · rintro ⟨_, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, h0.symm ▸ Subgroup.mem_top x⟩, hx, rfl⟩
  have hK_norm : (H 1).Normal := by
    rw [← hmap0]
    exact hN0.map eTop.toMonoidHom eTop.surjective
  have : (H 1).Normal := hK_norm
  let eQ0 : (H 0 ⧸ N0) ≃* (G ⧸ H 1) := QuotientGroup.congr N0 (H 1) eTop hmap0
  exact ⟨hK_norm, isCyclic_of_surjective eQ0.toMonoidHom eQ0.surjective⟩

/-- Every Garling-soluble group is finitely generated (polycyclic ⊆ FG). -/
theorem group_fg_of_isGarlingSoluble {G : Type*} [Group G] (h : IsGarlingSoluble G) :
    Group.FG G := by
  classical
  rcases h with ⟨n, H, h0, hlast, hle, hstep⟩
  induction n generalizing G with
  | zero =>
    have htb : (⊤ : Subgroup G) = ⊥ := h0.symm.trans hlast
    have : Subsingleton G := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := Subgroup.mem_bot.mp (htb ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (htb ▸ Subgroup.mem_top b)
      rw [ha, hb]
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  | succ m ih =>
    obtain ⟨H', hH'0, hH'last, hH'le, hH'step⟩ := isGarlingSoluble_tail H hlast hle hstep
    have hFG_K : Group.FG (H 1) := ih H' hH'0 hH'last hH'le hH'step
    obtain ⟨sK, hsK⟩ := hFG_K.out
    obtain ⟨hK_norm, hCycQ⟩ := isGarlingSoluble_head H h0 (hstep 0)
    have : (H 1).Normal := hK_norm
    have : IsCyclic (G ⧸ H 1) := hCycQ
    obtain ⟨qgen, hqgen⟩ := IsCyclic.exists_generator (α := G ⧸ H 1)
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective qgen
    refine ⟨⟨insert g0 (sK.image (H 1).subtype), ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, hk⟩ := hqgen (QuotientGroup.mk x)
    dsimp only at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
    have hmem_K : g0 ^ (-k) * x ∈ H 1 := by
      simpa [zpow_neg] using hk
    have hmem_cl_K : (⟨g0 ^ (-k) * x, hmem_K⟩ : H 1) ∈ Subgroup.closure (sK : Set (H 1)) := by
      rw [hsK]; exact Subgroup.mem_top _
    have hmap_sub : (Subgroup.closure (sK : Set (H 1))).map (H 1).subtype ≤
        Subgroup.closure ((insert g0 (sK.image (H 1).subtype) : Finset G) : Set G) := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff]
      exact Or.inr hy
    have h1 : g0 ^ (-k) * x ∈ Subgroup.closure ((insert g0 (sK.image (H 1).subtype) : Finset G) : Set G) :=
      hmap_sub ⟨⟨g0 ^ (-k) * x, hmem_K⟩, hmem_cl_K, rfl⟩
    have h2 : g0 ^ k ∈ Subgroup.closure ((insert g0 (sK.image (H 1).subtype) : Finset G) : Set G) :=
      Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
    have hx_eq : x = g0 ^ k * (g0 ^ (-k) * x) := by group
    rw [hx_eq]
    exact Subgroup.mul_mem _ h2 h1

/-- Explicit witness for `BRIEF.md` Flag 3: `(ℚ, +)` (`Multiplicative ℚ`) is abelian and therefore
Mathlib-solvable (`Group.IsSolvable`), yet not finitely generated and therefore **not**
Garling-soluble (`¬ IsGarlingSoluble`). -/
theorem additive_rat_isSolvable_not_isGarlingSoluble :
    Group.IsSolvable (Multiplicative ℚ) ∧ ¬ IsGarlingSoluble (Multiplicative ℚ) := by
  refine ⟨inferInstance, fun hsol => ?_⟩
  have hfg := group_fg_of_isGarlingSoluble hsol
  obtain ⟨s, hs⟩ := hfg.out
  let D : ℕ := ∏ x ∈ s, (Multiplicative.toAdd x).den
  have hD_pos : 0 < D := Finset.prod_pos fun x _ => (Multiplicative.toAdd x).pos
  let P : Subgroup (Multiplicative ℚ) :=
    { carrier := {y | ∃ z : ℤ, Multiplicative.toAdd y = (z : ℚ) / (D : ℚ)}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
        refine ⟨za + zb, ?_⟩
        rw [toAdd_mul, ha, hb]
        push_cast
        ring
      inv_mem' := by
        rintro a ⟨za, ha⟩
        refine ⟨-za, ?_⟩
        rw [toAdd_inv, ha]
        push_cast
        ring }
  have hsP : Subgroup.closure (s : Set (Multiplicative ℚ)) ≤ P := by
    rw [Subgroup.closure_le]
    intro x hx
    have hdvd : (Multiplicative.toAdd x).den ∣ D := Finset.dvd_prod_of_mem _ hx
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨(Multiplicative.toAdd x).num * (m : ℤ), ?_⟩
    have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD_pos)
    have hden_ne : ((Multiplicative.toAdd x).den : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Multiplicative.toAdd x).pos)
    have hrat := (Multiplicative.toAdd x).num_div_den
    have hmQ : (D : ℚ) = ((Multiplicative.toAdd x).den : ℚ) * (m : ℚ) := by
      exact_mod_cast hm
    have hm_ne : (m : ℚ) ≠ 0 := by
      intro hm0
      rw [hm0, mul_zero] at hmQ
      exact hD_ne hmQ
    conv_lhs => rw [← hrat]
    push_cast
    rw [hmQ]
    field_simp
  have hmem : Multiplicative.ofAdd ((1 : ℚ) / (2 * (D : ℚ))) ∈ P := by
    apply hsP
    rw [hs]
    exact Subgroup.mem_top _
  obtain ⟨z, hz⟩ := hmem
  rw [toAdd_ofAdd] at hz
  have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD_pos)
  have h2z : (2 : ℚ) * (z : ℚ) = 1 := by
    have h1 := congrArg (fun t : ℚ => t * (2 * (D : ℚ))) hz
    field_simp at h1
    linarith
  have h2z_int : (2 : ℤ) * z = 1 := by exact_mod_cast h2z
  omega

/-- Every Garling-soluble group is Mathlib-solvable (`Group.IsSolvable`), for arbitrary (finite or
infinite) groups. -/
theorem isSolvable_of_isGarlingSoluble {G : Type*} [Group G] (h : IsGarlingSoluble G) :
    Group.IsSolvable G := by
  rcases h with ⟨n, H, h0, hlast, hle, hstep⟩
  induction n generalizing G with
  | zero =>
    have htb : (⊤ : Subgroup G) = ⊥ := h0.symm.trans hlast
    have : Subsingleton G := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := Subgroup.mem_bot.mp (htb ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (htb ▸ Subgroup.mem_top b)
      rw [ha, hb]
    infer_instance
  | succ m ih =>
    obtain ⟨H', hH'0, hH'last, hH'le, hH'step⟩ := isGarlingSoluble_tail H hlast hle hstep
    have : Group.IsSolvable (H 1) := ih H' hH'0 hH'last hH'le hH'step
    obtain ⟨hK_norm, hCycQ⟩ := isGarlingSoluble_head H h0 (hstep 0)
    have : (H 1).Normal := hK_norm
    have : IsCyclic (G ⧸ H 1) := hCycQ
    let : CommGroup (G ⧸ H 1) := IsCyclic.commGroup
    have : Group.IsSolvable (G ⧸ H 1) := inferInstance
    exact (Group.isSolvable_iff_subgroup_quotient (H 1)).mpr ⟨inferInstance, inferInstance⟩

/-- Garling's inline prose definition of a *simple* group (§17.1, printed pp. 131–132 /
PDF pp. 139–140): *"they have no non-trivial normal subgroups"* (where §1.1 p. 4 defines `{e}` and
`G` to be the trivial subgroups of `G`). -/
def IsGarlingSimple (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤

/-- Bridge between Mathlib's `IsSimpleGroup G` and `Nontrivial G ∧ IsGarlingSimple G`. -/
theorem isSimpleGroup_iff_nontrivial_and_isGarlingSimple (G : Type*) [Group G] :
    IsSimpleGroup G ↔ Nontrivial G ∧ IsGarlingSimple G := by
  constructor
  · intro h
    exact ⟨h.toNontrivial, fun H hH => h.eq_bot_or_eq_top_of_normal H hH⟩
  · rintro ⟨hnt, hsimp⟩
    exact { exists_pair_ne := hnt.exists_pair_ne, eq_bot_or_eq_top_of_normal := hsimp }

/-- **§17.1 Prose Deduction (printed p. 132 / PDF p. 140):** Any non-cyclic simple group (with
`Nontrivial G`) is not Garling-soluble. -/
theorem not_isGarlingSoluble_of_isSimpleGroup_of_not_isCyclic {G : Type*} [Group G]
    [hsimp : IsSimpleGroup G] (hnc : ¬ IsCyclic G) :
    ¬ IsGarlingSoluble G := by
  classical
  rintro ⟨n, H, h0, hlast, _, hstep⟩
  have hbot_ne_top : (⊥ : Subgroup G) ≠ ⊤ := by
    intro heq
    obtain ⟨a, b, hab⟩ := hsimp.exists_pair_ne
    have ha : a = 1 := Subgroup.mem_bot.mp (heq ▸ Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (heq ▸ Subgroup.mem_top b)
    exact hab (ha.trans hb.symm)
  have hlast_ne : H (Fin.last n) ≠ ⊤ := by rw [hlast]; exact hbot_ne_top
  have hex : ∃ k : ℕ, ∃ hk : k < n + 1, H ⟨k, hk⟩ ≠ ⊤ :=
    ⟨n, Nat.lt_succ_self n, hlast_ne⟩
  let k := Nat.find hex
  obtain ⟨hk_lt, hHk_ne⟩ := Nat.find_spec hex
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    apply hHk_ne
    convert h0 using 2
    exact Fin.ext hk_eq
  let i : Fin n := ⟨k - 1, by omega⟩
  have hi_cast : H i.castSucc = ⊤ := by
    by_contra hne
    have hlt : k - 1 < k := by omega
    exact Nat.find_min hex hlt ⟨by omega, hne⟩
  have hi_succ_eq : i.succ = ⟨k, hk_lt⟩ := Fin.ext (by simp [i]; omega)
  obtain ⟨hNi, hCyci⟩ := hstep i
  let N : Subgroup (H i.castSucc) := (H i.succ).subgroupOf (H i.castSucc)
  have : N.Normal := hNi
  let eTop : H i.castSucc ≃* G := (MulEquiv.subgroupCongr hi_cast).trans Subgroup.topEquiv
  have hmapHi : N.map eTop.toMonoidHom = H i.succ := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, N, eTop]
    constructor
    · rintro ⟨_, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hi_cast.symm ▸ Subgroup.mem_top x⟩, hx, rfl⟩
  have hHi_norm : (H i.succ).Normal := by
    rw [← hmapHi]
    exact hNi.map eTop.toMonoidHom eTop.surjective
  have hHi_bot : H i.succ = ⊥ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal (H i.succ) hHi_norm with hbot | htop
    · exact hbot
    · exact (hHk_ne (hi_succ_eq ▸ htop)).elim
  have hmapN : N.map eTop.toMonoidHom = ⊥ := hmapHi.trans hHi_bot
  let eQ : (H i.castSucc ⧸ N) ≃* G :=
    (QuotientGroup.congr N ⊥ eTop hmapN).trans QuotientGroup.quotientBot
  exact hnc (isCyclic_of_surjective eQ.toMonoidHom eQ.surjective)

/-- Witness refuting Garling's p. 131 bottom-line typographical slip `"for n ≤ 5"` (corrected two
lines later on p. 132 to `"for n ≥ 5"`): `A_4` is **not** simple, because the Viergruppe `N` is a
non-trivial normal subgroup of `A_4`. -/
theorem section_17_1_p131_le_five_typo_witness :
    ¬ IsGarlingSimple (alternatingGroup (Fin 4)) ∧
    ¬ IsSimpleGroup (alternatingGroup (Fin 4)) := by
  let V : Subgroup (alternatingGroup (Fin 4)) := viergruppe.subgroupOf (alternatingGroup (Fin 4))
  have hVN : V.Normal := viergruppe_normal.comap (alternatingGroup (Fin 4)).subtype
  have hV_ne_bot : V ≠ ⊥ := by
    intro hbot
    let σ : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide⟩
    have hmem : σ ∈ V := by
      change (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) ∈ viergruppeFinset
      decide
    rw [hbot, Subgroup.mem_bot] at hmem
    have hne : (σ : Equiv.Perm (Fin 4)) ≠ 1 := by decide
    exact hne (congrArg Subtype.val hmem)
  have hV_ne_top : V ≠ ⊤ := by
    intro htop
    let τ : alternatingGroup (Fin 4) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide⟩
    have hmem : τ ∈ V := htop ▸ Subgroup.mem_top τ
    have hnot : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ∉ viergruppeFinset := by decide
    exact hnot hmem
  have hnot_gsimp : ¬ IsGarlingSimple (alternatingGroup (Fin 4)) := fun h =>
    (h V hVN).elim hV_ne_bot hV_ne_top
  exact ⟨hnot_gsimp, fun h => hnot_gsimp
    ((isSimpleGroup_iff_nontrivial_and_isGarlingSimple _).mp h).2⟩

/-! ## §17.2 Soluble groups: basic theory (printed pp. 132–134, PDF pp. 140–142) -/

/-- **Theorem 17.1(i) — Counterexample 1 (non-normality of `A` in `HA`, printed p. 132):**
In `G = Σ_3` with `H = A_3 ⊲ G` and `A = ⟨(12)⟩`, `HA = Σ_3`, `A` is **not** normal in `HA` (so
the printed `HA/A` is not even a quotient group), and the coset count `|HA/A| = 3` differs from
`|A/(H ∩ A)| = 2`. -/
theorem theorem_17_1_i_not_normal_counterexample :
    let G := SigmaN 3
    let H : Subgroup G := alternatingGroup (Fin 3)
    let A : Subgroup G := Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)
    H.Normal ∧
    H ⊔ A = ⊤ ∧
    ¬ (A.subgroupOf (H ⊔ A)).Normal ∧
    Nat.card (↥A ⧸ (H ⊓ A).subgroupOf A) = 2 ∧
    Nat.card (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A)) = 3 ∧
    Nat.card (↥A ⧸ (H ⊓ A).subgroupOf A) ≠ Nat.card (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A)) := by
  intro G H A
  have hHN : H.Normal := inferInstance
  have hHA : H ⊔ A = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    by_cases heven : Equiv.Perm.sign σ = 1
    · exact Subgroup.mem_sup_left heven
    · have hodd : Equiv.Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left heven
      have hs01_sign : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 :=
        Equiv.Perm.sign_swap (by decide)
      have hprod : σ * Equiv.swap 0 1 ∈ H := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, hodd, hs01_sign]; decide
      have hs01_A : Equiv.swap (0 : Fin 3) 1 ∈ A := Subgroup.mem_zpowers _
      have hσ_eq : σ = (σ * Equiv.swap 0 1) * Equiv.swap 0 1 := by
        rw [mul_assoc, Equiv.swap_mul_self, mul_one]
      rw [hσ_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hprod) (Subgroup.mem_sup_right hs01_A)
  have hzpow_two : ∀ k : ℤ, (Equiv.swap (0 : Fin 3) 1) ^ k = 1 ∨
      (Equiv.swap (0 : Fin 3) 1) ^ k = Equiv.swap 0 1 := by
    intro k
    have hsq : (Equiv.swap (0 : Fin 3) 1) ^ (2 : ℤ) = 1 := by
      change (Equiv.swap (0 : Fin 3) 1) ^ (2 : ℕ) = 1; decide
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      have hk2 : k = 2 * (k / 2) := by omega
      rw [hk2, zpow_mul, hsq, one_zpow]
    · right
      have hk2 : k = 2 * (k / 2) + 1 := by omega
      rw [hk2, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
  have hnot_norm : ¬ (A.subgroupOf (H ⊔ A)).Normal := by
    intro hN
    have hconj : (⟨Equiv.swap 1 2, hHA ▸ Subgroup.mem_top _⟩ : ↥(H ⊔ A)) *
        ⟨Equiv.swap 0 1, hHA ▸ Subgroup.mem_top _⟩ *
        (⟨Equiv.swap 1 2, hHA ▸ Subgroup.mem_top _⟩ : ↥(H ⊔ A))⁻¹ ∈ A.subgroupOf (H ⊔ A) :=
      hN.conj_mem _ (Subgroup.mem_zpowers _) _
    change Equiv.swap 1 2 * Equiv.swap 0 1 * (Equiv.swap 1 2)⁻¹ ∈ A at hconj
    obtain ⟨k, hk⟩ := hconj
    dsimp only at hk
    rcases hzpow_two k with h1 | h2
    · rw [h1] at hk
      exact (by decide : (1 : G) ≠ Equiv.swap 1 2 * Equiv.swap 0 1 * (Equiv.swap 1 2)⁻¹) hk
    · rw [h2] at hk
      exact (by decide : Equiv.swap (0 : Fin 3) 1 ≠
        Equiv.swap 1 2 * Equiv.swap 0 1 * (Equiv.swap 1 2)⁻¹) hk
  have hcardA : Nat.card A = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  have hHA_inf : (H ⊓ A).subgroupOf A = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_bot]
    constructor
    · rintro ⟨hxH, _⟩
      obtain ⟨k, rfl⟩ := hx
      dsimp only at hxH
      rcases hzpow_two k with h1 | h2
      · exact Subtype.ext h1
      · rw [h2] at hxH
        have hnotH : Equiv.swap (0 : Fin 3) 1 ∉ H := by
          rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]; decide
        exact (hnotH hxH).elim
    · intro h1
      have hx1 : x = 1 := congrArg Subtype.val h1
      rw [hx1]
      exact ⟨H.one_mem, A.one_mem⟩
  have hcard1 : Nat.card (↥A ⧸ (H ⊓ A).subgroupOf A) = 2 := by
    rw [hHA_inf, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcardA]
  have hcard2 : Nat.card (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A)) = 3 := by
    have hlag := (A.subgroupOf (H ⊔ A)).card_mul_index
    rw [Subgroup.index_eq_card] at hlag
    have hcard_top : Nat.card ↥(H ⊔ A) = 6 := by
      rw [hHA, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    have hcard_sub : Nat.card (A.subgroupOf (H ⊔ A)) = 2 := by
      let e : A.subgroupOf (H ⊔ A) ≃ A :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun y => ⟨⟨y.1, hHA ▸ Subgroup.mem_top y.1⟩, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, hcardA]
    rw [hcard_top, hcard_sub] at hlag
    omega
  exact ⟨hHN, hHA, hnot_norm, hcard1, hcard2, by omega⟩

/-- **Theorem 17.1(i) — Counterexample 2 (false even when `A ⊲ G`, printed p. 132):**
In the abelian group `G = ℤ_2` (`Multiplicative (ZMod 2)`) with `H = ⊥ ⊲ G` and `A = ⊤ ⊲ G`,
both `A/(H ∩ A)` and `HA/A` are genuine quotient groups, yet `|A/(H ∩ A)| = 2 ≠ 1 = |HA/A|`, so
`A/(H ∩ A) ≇ HA/A`. -/
theorem theorem_17_1_i_normal_card_counterexample :
    let G := Multiplicative (ZMod 2)
    let H : Subgroup G := ⊥
    let A : Subgroup G := ⊤
    H.Normal ∧ A.Normal ∧
    Nat.card (↥A ⧸ (H ⊓ A).subgroupOf A) = 2 ∧
    Nat.card (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A)) = 1 ∧
    IsEmpty ((↥A ⧸ (H ⊓ A).subgroupOf A) ≃* (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A))) := by
  intro G H A
  have h1 : Nat.card (↥A ⧸ (H ⊓ A).subgroupOf A) = 2 := by
    have hbot : (H ⊓ A).subgroupOf A = ⊥ := by ext x; simp [H, A]
    rw [hbot, Nat.card_congr QuotientGroup.quotientBot.toEquiv,
      Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
  have h2 : Nat.card (↥(H ⊔ A) ⧸ A.subgroupOf (H ⊔ A)) = 1 := by
    have htop : A.subgroupOf (H ⊔ A) = ⊤ := by ext x; simp [A]
    rw [htop, Nat.card_eq_one_iff_exists]
    refine ⟨1, fun q => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_top y)
  refine ⟨inferInstance, inferInstance, h1, h2, ⟨fun e => ?_⟩⟩
  have hc := Nat.card_congr e.toEquiv
  omega

/-- **Theorem 17.1(i), first half (literal, printed p. 132):** If `H ⊲ G` and `A ≤ G`, then
`H ∩ A ⊲ A`. -/
theorem theorem_17_1_i_part1 {G : Type*} [Group G] (H A : Subgroup G) [hH : H.Normal] :
    ((H ⊓ A).subgroupOf A).Normal := by
  have heq : (H ⊓ A).subgroupOf A = H.subgroupOf A := by ext ⟨x, hx⟩; simp
  rw [heq]
  exact hH.comap A.subtype

/-- Explicit Second Isomorphism Theorem equivalence `A / (H ∩ A) ≃* HA / H`
(**Theorem 17.1(i)**, repaired from Garling's printed typo `HA/A` to match his p. 133 proof). -/
noncomputable def theorem_17_1_i_equiv {G : Type*} [Group G] (H A : Subgroup G) [hH : H.Normal] :
    haveI : ((H ⊓ A).subgroupOf A).Normal := theorem_17_1_i_part1 H A
    (↥A ⧸ (H ⊓ A).subgroupOf A) ≃* (↥(H ⊔ A) ⧸ H.subgroupOf (H ⊔ A)) := by
  haveI : ((H ⊓ A).subgroupOf A).Normal := theorem_17_1_i_part1 H A
  have h1 : (H ⊓ A).subgroupOf A = H.subgroupOf A := by ext ⟨x, hx⟩; simp
  have h2 : H ⊔ A = A ⊔ H := sup_comm H A
  let e1 : (↥A ⧸ (H ⊓ A).subgroupOf A) ≃* (↥A ⧸ H.subgroupOf A) :=
    QuotientGroup.quotientMulEquivOfEq h1
  let e2 : (↥A ⧸ H.subgroupOf A) ≃* (↥(A ⊔ H) ⧸ H.subgroupOf (A ⊔ H)) :=
    QuotientGroup.quotientInfEquivProdNormalQuotient A H
  let eSup : ↥(A ⊔ H) ≃* ↥(H ⊔ A) := MulEquiv.subgroupCongr h2.symm
  have hmap : (H.subgroupOf (A ⊔ H)).map eSup.toMonoidHom = H.subgroupOf (H ⊔ A) := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, eSup]
    constructor
    · rintro ⟨⟨y, _⟩, hy, heq⟩
      have hxy : y = x := congrArg Subtype.val heq
      rwa [← hxy]
    · intro hxH
      exact ⟨⟨x, h2 ▸ hx⟩, hxH, rfl⟩
  let e3 : (↥(A ⊔ H) ⧸ H.subgroupOf (A ⊔ H)) ≃*
      (↥(H ⊔ A) ⧸ H.subgroupOf (H ⊔ A)) :=
    QuotientGroup.congr (H.subgroupOf (A ⊔ H)) (H.subgroupOf (H ⊔ A)) eSup hmap
  exact e1.trans (e2.trans e3)

/-- **Theorem 17.1(i), repaired (printed pp. 132–133 / PDF pp. 140–141):**
If `H ⊲ G` and `A ≤ G`, then `HA = H ⊔ A = {h * a | h ∈ H, a ∈ A}`, `H ∩ A ⊲ A`, `H ⊲ HA`, and
`A/(H ∩ A) ≃* HA/H`. -/
theorem theorem_17_1_i_repaired {G : Type*} [Group G] (H A : Subgroup G) [H.Normal] :
    ((H ⊔ A : Subgroup G) : Set G) = {g : G | ∃ h ∈ H, ∃ a ∈ A, g = h * a} ∧
    (H.subgroupOf (H ⊔ A)).Normal ∧
    ∃ (_ : ((H ⊓ A).subgroupOf A).Normal),
      Nonempty ((↥A ⧸ (H ⊓ A).subgroupOf A) ≃* (↥(H ⊔ A) ⧸ H.subgroupOf (H ⊔ A))) := by
  have hset : ((H ⊔ A : Subgroup G) : Set G) = {g : G | ∃ h ∈ H, ∃ a ∈ A, g = h * a} := by
    rw [Subgroup.normal_mul H A]
    ext g
    simp [Set.mem_mul, eq_comm]
  have hN : ((H ⊓ A).subgroupOf A).Normal := theorem_17_1_i_part1 H A
  exact ⟨hset, inferInstance, hN, ⟨theorem_17_1_i_equiv H A⟩⟩

/-- Explicit Third Isomorphism Theorem equivalence `(G/H) / (A/H) ≃* G/A`
(**Theorem 17.1(ii)**, literal, printed pp. 132–133). -/
def theorem_17_1_ii_equiv {G : Type*} [Group G] (H A : Subgroup G) [H.Normal] [A.Normal]
    (hHA : H ≤ A) :
    ((G ⧸ H) ⧸ A.map (QuotientGroup.mk' H)) ≃* (G ⧸ A) :=
  QuotientGroup.quotientQuotientEquivQuotient H A hHA

/-- **Theorem 17.1(ii) (literal, printed pp. 132–133 / PDF pp. 140–141):**
If `H ⊲ G`, `A ⊲ G`, and `H ≤ A`, then `H ⊲ A`, `A/H ⊲ G/H`, and `(G/H)/(A/H) ≃* G/A`. -/
theorem theorem_17_1_ii {G : Type*} [Group G] (H A : Subgroup G) [H.Normal] [A.Normal]
    (hHA : H ≤ A) :
    (H.subgroupOf A).Normal ∧
    (A.map (QuotientGroup.mk' H)).Normal ∧
    Nonempty (((G ⧸ H) ⧸ A.map (QuotientGroup.mk' H)) ≃* (G ⧸ A)) :=
  ⟨inferInstance, inferInstance, ⟨theorem_17_1_ii_equiv H A hHA⟩⟩

/-- **Theorem 17.1 (bundled repaired `(i)` + literal `(ii)`, printed pp. 132–133 / PDF pp. 140–141).** -/
theorem theorem_17_1 {G : Type*} [Group G] (H A : Subgroup G) [H.Normal] :
    (((H ⊔ A : Subgroup G) : Set G) = {g : G | ∃ h ∈ H, ∃ a ∈ A, g = h * a} ∧
      (H.subgroupOf (H ⊔ A)).Normal ∧
      ∃ (_ : ((H ⊓ A).subgroupOf A).Normal),
        Nonempty ((↥A ⧸ (H ⊓ A).subgroupOf A) ≃* (↥(H ⊔ A) ⧸ H.subgroupOf (H ⊔ A)))) ∧
    (H ≤ A → ∀ [A.Normal],
      (H.subgroupOf A).Normal ∧
      (A.map (QuotientGroup.mk' H)).Normal ∧
      Nonempty (((G ⧸ H) ⧸ A.map (QuotientGroup.mk' H)) ≃* (G ⧸ A))) :=
  ⟨theorem_17_1_i_repaired H A, fun hHA hAN => @theorem_17_1_ii G _ H A _ hAN hHA⟩

/-- **Theorem 17.2(i) (literal, printed p. 133 / PDF p. 141):**
If `G` is a Garling-soluble group (finite or infinite) and `A` is a subgroup of `G`, then `A` is
Garling-soluble. -/
theorem theorem_17_2_i {G : Type*} [Group G] (hG : IsGarlingSoluble G) (A : Subgroup G) :
    IsGarlingSoluble A := by
  rcases hG with ⟨n, H, h0, hlast, hle, hstep⟩
  refine ⟨n, fun j => (H j).subgroupOf A, ?_, ?_, ?_, ?_⟩
  · ext ⟨x, _⟩; simp [h0]
  · ext ⟨x, _⟩; simp [hlast]
  · intro i ⟨x, _⟩ hx; exact hle i hx
  · intro i
    obtain ⟨hNi, hCyci⟩ := hstep i
    let Gprev := H i.castSucc
    let Gcurr : Subgroup Gprev := (H i.succ).subgroupOf Gprev
    have : Gcurr.Normal := hNi
    have : IsCyclic (Gprev ⧸ Gcurr) := hCyci
    let Aprev : Subgroup A := (H i.castSucc).subgroupOf A
    let Acurr : Subgroup Aprev := ((H i.succ).subgroupOf A).subgroupOf Aprev
    let ι : Aprev →* Gprev :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let φ : Aprev →* (Gprev ⧸ Gcurr) := (QuotientGroup.mk' Gcurr).comp ι
    have hker : φ.ker = Acurr := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, φ, ι, Gcurr, Acurr]
      rfl
    have hN : Acurr.Normal := hker ▸ φ.normal_ker
    have : Acurr.Normal := hN
    let e : (Aprev ⧸ Acurr) ≃* φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
    have : IsCyclic φ.range := inferInstance
    exact ⟨hN, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩

/-- **Theorem 17.2(ii) (literal, printed pp. 133–134 / PDF pp. 141–142):**
Suppose `G` is a group (finite or infinite) and `H ⊲ G`. Then `G` is Garling-soluble if and only
if `H` and `G/H` are Garling-soluble. -/
theorem theorem_17_2_ii {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    IsGarlingSoluble G ↔ IsGarlingSoluble H ∧ IsGarlingSoluble (G ⧸ H) := by
  constructor
  · intro hG
    refine ⟨theorem_17_2_i hG H, ?_⟩
    rcases hG with ⟨n, S, h0, hlast, hle, hstep⟩
    let q : G →* G ⧸ H := QuotientGroup.mk' H
    have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective H
    refine ⟨n, fun j => (S j).map q, ?_, ?_, ?_, ?_⟩
    · simp [h0, Subgroup.map_top_of_surjective q hq_surj]
    · simp [hlast]
    · intro i; exact Subgroup.map_mono (hle i)
    · intro i
      obtain ⟨hNi, hCyci⟩ := hstep i
      let Sprev := S i.castSucc
      let Scurr : Subgroup Sprev := (S i.succ).subgroupOf Sprev
      have : Scurr.Normal := hNi
      have : IsCyclic (Sprev ⧸ Scurr) := hCyci
      let Qprev : Subgroup (G ⧸ H) := (S i.castSucc).map q
      let Qcurr : Subgroup Qprev := ((S i.succ).map q).subgroupOf Qprev
      have hQnorm : Qcurr.Normal := by
        constructor
        rintro ⟨w, hw⟩ hw_curr ⟨v, hv⟩
        obtain ⟨u, hu, rfl⟩ := hw_curr
        obtain ⟨y, hy, rfl⟩ := hv
        change (q y) * (q u) * (q y)⁻¹ ∈ (S i.succ).map q
        rw [← map_inv, ← map_mul, ← map_mul]
        have hconj : (⟨y, hy⟩ : Sprev) * ⟨u, hle i hu⟩ * (⟨y, hy⟩ : Sprev)⁻¹ ∈ Scurr :=
          hNi.conj_mem _ hu ⟨y, hy⟩
        exact ⟨y * u * y⁻¹, hconj, rfl⟩
      have : Qcurr.Normal := hQnorm
      let ψ : Sprev →* (Qprev ⧸ Qcurr) :=
        (QuotientGroup.mk' Qcurr).comp
          { toFun := fun x => ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
            map_one' := Subtype.ext (map_one q)
            map_mul' := fun a b => Subtype.ext (map_mul q a.1 b.1) }
      have hψ_surj : Function.Surjective ψ := by
        intro z
        obtain ⟨⟨w, x, hx, rfl⟩, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨⟨x, hx⟩, rfl⟩
      have hScurr_le : Scurr ≤ ψ.ker := by
        intro x hx
        simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Qcurr, Subgroup.mem_subgroupOf]
        exact ⟨x.1, hx, rfl⟩
      let θ : (Sprev ⧸ Scurr) →* (Qprev ⧸ Qcurr) := QuotientGroup.lift Scurr ψ hScurr_le
      have hθ_surj : Function.Surjective θ := by
        intro z
        obtain ⟨x, rfl⟩ := hψ_surj z
        exact ⟨QuotientGroup.mk x, rfl⟩
      exact ⟨hQnorm, isCyclic_of_surjective θ hθ_surj⟩
  · rintro ⟨⟨n, SH, hSH0, hSHlast, hSHle, hSHstep⟩, ⟨m, SQ, hSQ0, hSQlast, hSQle, hSQstep⟩⟩
    let q : G →* G ⧸ H := QuotientGroup.mk' H
    have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective H
    let T : Fin (m + n + 1) → Subgroup G := fun j =>
      if hj : (j : ℕ) ≤ m then
        (SQ ⟨j, Nat.lt_succ_of_le hj⟩).comap q
      else
        (SH ⟨(j : ℕ) - m, by omega⟩).map H.subtype
    have hT_low : ∀ k (hk : k ≤ m),
        T ⟨k, by omega⟩ = (SQ ⟨k, Nat.lt_succ_of_le hk⟩).comap q := fun k hk => by
      simp [T, hk]
    have hT_high : ∀ k (hk : k ≤ n),
        T ⟨m + k, by omega⟩ = (SH ⟨k, Nat.lt_succ_of_le hk⟩).map H.subtype := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.add_zero, T, le_refl, ↓reduceDIte]
        have hlast_m : (⟨m, Nat.lt_succ_of_le (le_refl m)⟩ : Fin (m + 1)) = Fin.last m := rfl
        have h0_n : (⟨0, Nat.lt_succ_of_le (Nat.zero_le n)⟩ : Fin (n + 1)) = 0 := rfl
        rw [hlast_m, hSQlast, h0_n, hSH0]
        ext x
        simp [q]
      · have hnot : ¬ (m + k ≤ m) := by omega
        simp [T, hnot]
    refine ⟨m + n, T, ?_, ?_, ?_, ?_⟩
    · change T ⟨0, by omega⟩ = ⊤
      rw [hT_low 0 (Nat.zero_le m)]
      have h0m : (⟨0, Nat.lt_succ_of_le (Nat.zero_le m)⟩ : Fin (m + 1)) = 0 := rfl
      rw [h0m, hSQ0]
      exact Subgroup.comap_top q
    · have hl : Fin.last (m + n) = ⟨m + n, by omega⟩ := rfl
      rw [hl, hT_high n (le_refl n)]
      have hln : (⟨n, Nat.lt_succ_of_le (le_refl n)⟩ : Fin (n + 1)) = Fin.last n := rfl
      rw [hln, hSHlast]
      exact Subgroup.map_bot H.subtype
    · intro i
      by_cases hi : (i : ℕ) < m
      · have hc : i.castSucc = ⟨i, by omega⟩ := rfl
        have hs : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := rfl
        rw [hc, hs, hT_low i (Nat.le_of_lt hi), hT_low (i + 1) hi]
        exact Subgroup.comap_mono (hSQle ⟨i, hi⟩)
      · let i₂ : Fin n := ⟨(i : ℕ) - m, by omega⟩
        have hc : i.castSucc = ⟨m + i₂, by omega⟩ := Fin.ext (by dsimp [i₂]; omega)
        have hs : i.succ = ⟨m + (i₂ + 1), by omega⟩ := Fin.ext (by dsimp [i₂]; omega)
        rw [hc, hs, hT_high i₂ (Nat.le_of_lt i₂.2), hT_high (i₂ + 1) i₂.2]
        exact Subgroup.map_mono (hSHle i₂)
    · intro i
      by_cases hi : (i : ℕ) < m
      · let i₁ : Fin m := ⟨i, hi⟩
        have hc : T i.castSucc = (SQ i₁.castSucc).comap q := hT_low i (Nat.le_of_lt hi)
        have hs : T i.succ = (SQ i₁.succ).comap q := hT_low (i + 1) hi
        obtain ⟨hNi, hCyci⟩ := hSQstep i₁
        let Qprev := SQ i₁.castSucc
        let Qcurr : Subgroup Qprev := (SQ i₁.succ).subgroupOf Qprev
        have : Qcurr.Normal := hNi
        have : IsCyclic (Qprev ⧸ Qcurr) := hCyci
        let qRestr : T i.castSucc →* Qprev :=
          { toFun := fun x => ⟨q x.1, by simpa [hc] using x.2⟩
            map_one' := Subtype.ext (map_one q)
            map_mul' := fun a b => Subtype.ext (map_mul q a.1 b.1) }
        have hqRestr_surj : Function.Surjective qRestr := by
          rintro ⟨w, hw⟩
          obtain ⟨g, rfl⟩ := hq_surj w
          exact ⟨⟨g, by simpa [hc] using hw⟩, rfl⟩
        let φ : T i.castSucc →* (Qprev ⧸ Qcurr) := (QuotientGroup.mk' Qcurr).comp qRestr
        have hφ_surj : Function.Surjective φ :=
          (QuotientGroup.mk'_surjective Qcurr).comp hqRestr_surj
        have hker : φ.ker = (T i.succ).subgroupOf (T i.castSucc) := by
          ext x
          simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hs, Subgroup.mem_comap,
            Qcurr, qRestr, φ]
          rfl
        have hN : ((T i.succ).subgroupOf (T i.castSucc)).Normal := hker ▸ φ.normal_ker
        have : ((T i.succ).subgroupOf (T i.castSucc)).Normal := hN
        let e : (T i.castSucc ⧸ (T i.succ).subgroupOf (T i.castSucc)) ≃* (Qprev ⧸ Qcurr) :=
          (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj)
        exact ⟨hN, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩
      · let i₂ : Fin n := ⟨(i : ℕ) - m, by omega⟩
        have hc : T i.castSucc = (SH i₂.castSucc).map H.subtype := by
          have heq : i.castSucc = ⟨m + i₂, by omega⟩ := Fin.ext (by dsimp [i₂]; omega)
          rw [heq]; exact hT_high i₂ (Nat.le_of_lt i₂.2)
        have hs : T i.succ = (SH i₂.succ).map H.subtype := by
          have heq : i.succ = ⟨m + (i₂ + 1), by omega⟩ := Fin.ext (by dsimp [i₂]; omega)
          rw [heq]; exact hT_high (i₂ + 1) i₂.2
        obtain ⟨hNi, hCyci⟩ := hSHstep i₂
        let Hprev := SH i₂.castSucc
        let Hcurr : Subgroup Hprev := (SH i₂.succ).subgroupOf Hprev
        have : Hcurr.Normal := hNi
        have : IsCyclic (Hprev ⧸ Hcurr) := hCyci
        have hmem_iff : ∀ y : G, y ∈ T i.castSucc ↔ ∃ h : H, h ∈ Hprev ∧ (h : G) = y := by
          intro y; rw [hc]; rfl
        let eSub : Hprev ≃* T i.castSucc :=
          { toFun := fun x => ⟨x.1.1, (hmem_iff x.1.1).mpr ⟨x.1, x.2, rfl⟩⟩
            invFun := fun y =>
              let hy := (hmem_iff y.1).mp y.2
              ⟨⟨y.1, by obtain ⟨h, _, heq⟩ := hy; exact heq ▸ h.2⟩,
               by obtain ⟨h, hh, heq⟩ := hy
                  have hsub : h = ⟨y.1, heq ▸ h.2⟩ := Subtype.ext heq
                  exact hsub ▸ hh⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _⟩ => rfl
            map_mul' := fun _ _ => rfl }
        have hmap : Hcurr.map eSub.toMonoidHom = (T i.succ).subgroupOf (T i.castSucc) := by
          ext ⟨y, hy⟩
          simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, hs, Hcurr, eSub]
          constructor
          · rintro ⟨⟨x, hx⟩, hxs, heq⟩
            exact ⟨x, hxs, congrArg Subtype.val heq⟩
          · rintro ⟨x, hxs, rfl⟩
            exact ⟨⟨x, hSHle i₂ hxs⟩, hxs, rfl⟩
        have hN : ((T i.succ).subgroupOf (T i.castSucc)).Normal := by
          rw [← hmap]
          exact hNi.map eSub.toMonoidHom eSub.surjective
        have : ((T i.succ).subgroupOf (T i.castSucc)).Normal := hN
        let eQ : (Hprev ⧸ Hcurr) ≃* (T i.castSucc ⧸ (T i.succ).subgroupOf (T i.castSucc)) :=
          QuotientGroup.congr Hcurr ((T i.succ).subgroupOf (T i.castSucc)) eSub hmap
        exact ⟨hN, isCyclic_of_surjective eQ.toMonoidHom eQ.surjective⟩

/-- **Theorem 17.2 (bundled, literal, printed pp. 133–134 / PDF pp. 141–142).** -/
theorem theorem_17_2 {G : Type*} [Group G] :
    (IsGarlingSoluble G → ∀ A : Subgroup G, IsGarlingSoluble A) ∧
    (∀ (H : Subgroup G) [H.Normal],
      IsGarlingSoluble G ↔ IsGarlingSoluble H ∧ IsGarlingSoluble (G ⧸ H)) :=
  ⟨fun hG A => theorem_17_2_i hG A, fun H _ => theorem_17_2_ii H⟩

/-- **Bridge theorem (Flag 3):** For **finite** groups `G`, Garling's *soluble* (`IsGarlingSoluble`)
is logically equivalent to Mathlib's `Group.IsSolvable`. -/
theorem isGarlingSoluble_iff_isSolvable_of_finite {G : Type*} [Group G] [Finite G] :
    IsGarlingSoluble G ↔ Group.IsSolvable G := by
  refine ⟨isSolvable_of_isGarlingSoluble, fun hsol => ?_⟩
  obtain ⟨k, hk⟩ := hsol.solvable
  induction k generalizing G with
  | zero =>
    rw [derivedSeries_zero] at hk
    have : Subsingleton G := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := Subgroup.mem_bot.mp (hk ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (hk ▸ Subgroup.mem_top b)
      rw [ha, hb]
    exact isGarlingSoluble_of_subsingleton
  | succ m ih =>
    let D : Subgroup G := derivedSeries G 1
    have : D.Normal := derivedSeries_normal G 1
    let : CommGroup (G ⧸ D) :=
      { mul_comm := fun a b => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hc : ⁅y⁻¹, x⁻¹⁆ ∈ D := by
            rw [show D = ⁅(⊤ : Subgroup G), ⊤⁆ from derivedSeries_one G]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
          simpa [commutatorElement_def, mul_assoc] using hc }
    have hQ : IsGarlingSoluble (G ⧸ D) := isGarlingSoluble_of_commGroup_finite
    have hD_der : derivedSeries D m = ⊥ := by
      have hmap_eq : ∀ j : ℕ, (derivedSeries D j).map D.subtype = derivedSeries G (j + 1) := by
        intro j
        induction j with
        | zero =>
          rw [derivedSeries_zero]
          ext x
          constructor
          · rintro ⟨⟨y, hy⟩, _, rfl⟩; exact hy
          · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
        | succ r ihr =>
          rw [derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator, ihr]
      have h0 : (derivedSeries D m).map D.subtype = ⊥ := by rw [hmap_eq m, hk]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_bot]
      constructor
      · intro hxm
        have hm' : x ∈ (derivedSeries D m).map D.subtype := ⟨⟨x, hx⟩, hxm, rfl⟩
        rw [h0, Subgroup.mem_bot] at hm'
        exact Subtype.ext hm'
      · intro h1; rw [h1]; exact (derivedSeries D m).one_mem
    have hD_sol : Group.IsSolvable D := ⟨⟨m, hD_der⟩⟩
    have hD : IsGarlingSoluble D := ih hD_sol hD_der
    exact (theorem_17_2_ii D).mpr ⟨hD, hQ⟩

/-- **§17.1 Unnumbered Main-Text Prose Theorem (printed pp. 131–132 / PDF pp. 139–140):**
For every `n ≥ 5`, the alternating group `A_n` is simple (both `IsSimpleGroup` and
`IsGarlingSimple`), non-cyclic, not Garling-soluble, and not Mathlib-solvable. -/
theorem section_17_1_alternating_simple_and_not_soluble {n : ℕ} (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) ∧
    IsGarlingSimple (alternatingGroup (Fin n)) ∧
    ¬ IsCyclic (alternatingGroup (Fin n)) ∧
    ¬ IsGarlingSoluble (alternatingGroup (Fin n)) ∧
    ¬ Group.IsSolvable (alternatingGroup (Fin n)) := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hsimp : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup hcard
  have : IsSimpleGroup (alternatingGroup (Fin n)) := hsimp
  have hgsimp : IsGarlingSimple (alternatingGroup (Fin n)) :=
    ((isSimpleGroup_iff_nontrivial_and_isGarlingSimple _).mp hsimp).2
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
  have h13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
  let c1 : alternatingGroup (Fin n) :=
    ⟨Equiv.swap i0 i1 * Equiv.swap i1 i2, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h12]; decide⟩
  let c2 : alternatingGroup (Fin n) :=
    ⟨Equiv.swap i1 i2 * Equiv.swap i2 i3, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap h12, Equiv.Perm.sign_swap h23]; decide⟩
  have hnc_comm : c1 * c2 ≠ c2 * c1 := by
    intro heq
    have hval := congrArg (fun σ : alternatingGroup (Fin n) => (σ : Equiv.Perm (Fin n)) i0) heq
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, c1, c2] at hval
    have hlhs : Equiv.swap i0 i1 (Equiv.swap i1 i2 (Equiv.swap i1 i2 (Equiv.swap i2 i3 i0))) = i1 := by
      rw [Equiv.swap_apply_of_ne_of_ne h02 h03, Equiv.swap_apply_of_ne_of_ne h01 h02,
        Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_left]
    have hrhs : Equiv.swap i1 i2 (Equiv.swap i2 i3 (Equiv.swap i0 i1 (Equiv.swap i1 i2 i0))) = i2 := by
      rw [Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne h12 h13, Equiv.swap_apply_left]
    rw [hlhs, hrhs] at hval
    exact h12 hval
  have hnot_cyc : ¬ IsCyclic (alternatingGroup (Fin n)) := by
    intro hcyc
    let : CommGroup (alternatingGroup (Fin n)) := IsCyclic.commGroup
    exact hnc_comm (mul_comm c1 c2)
  have hnot_gsol : ¬ IsGarlingSoluble (alternatingGroup (Fin n)) :=
    not_isGarlingSoluble_of_isSimpleGroup_of_not_isCyclic hnot_cyc
  have hnot_sol : ¬ Group.IsSolvable (alternatingGroup (Fin n)) := fun hsol =>
    hnot_gsol (isGarlingSoluble_iff_isSolvable_of_finite.mpr hsol)
  exact ⟨hsimp, hgsimp, hnot_cyc, hnot_gsol, hnot_sol⟩

/-- **§17.1 Worked Examples (printed p. 131 / PDF p. 139):**
`A_3`, `Σ_3`, `A_4`, and `Σ_4` are all Garling-soluble; also documents Garling's p. 131 Viergruppe
slip (`(12) ∉ N`, whereas `(12)(34) ∈ N`). -/
theorem section_17_1_soluble_examples :
    IsGarlingSoluble (alternatingGroup (Fin 3)) ∧
    IsGarlingSoluble (SigmaN 3) ∧
    IsGarlingSoluble (alternatingGroup (Fin 4)) ∧
    IsGarlingSoluble (SigmaN 4) ∧
    Equiv.swap (0 : Fin 4) 1 ∉ viergruppe ∧
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ∈ viergruppe := by
  have hA3_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hA3 : IsGarlingSoluble (alternatingGroup (Fin 3)) := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hA3_card
    exact isGarlingSoluble_of_isCyclic
  have hS3 : IsGarlingSoluble (SigmaN 3) := by
    rw [theorem_17_2_ii (alternatingGroup (Fin 3))]
    refine ⟨hA3, ?_⟩
    have hcard : Nat.card (SigmaN 3 ⧸ alternatingGroup (Fin 3)) = 2 := by
      have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (alternatingGroup (Fin 3))
      change Nat.card (SigmaN 3) =
        Nat.card (SigmaN 3 ⧸ alternatingGroup (Fin 3)) * Nat.card (alternatingGroup (Fin 3)) at hlag
      have hc1 : Nat.card (SigmaN 3) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
      rw [hc1, hA3_card] at hlag
      omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (SigmaN 3 ⧸ alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
    exact isGarlingSoluble_of_isCyclic
  have hS4 : IsGarlingSoluble (SigmaN 4) := by
    have : viergruppe.Normal := viergruppe_normal
    rw [theorem_17_2_ii viergruppe]
    refine ⟨?_, ?_⟩
    · have hvg_comm : ∀ a b : viergruppe, a * b = b * a := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        apply Subtype.ext
        change a * b = b * a
        have ha' : a ∈ viergruppeFinset := ha
        have hb' : b ∈ viergruppeFinset := hb
        fin_cases ha' <;> fin_cases hb' <;> decide
      let : CommGroup viergruppe := { mul_comm := hvg_comm }
      exact isGarlingSoluble_of_commGroup_finite
    · obtain ⟨e⟩ := s4_quot_viergruppe_mulEquiv_s3
      exact (isGarlingSoluble_congr e).mpr hS3
  have hA4 : IsGarlingSoluble (alternatingGroup (Fin 4)) :=
    theorem_17_2_i hS4 (alternatingGroup (Fin 4))
  have hnot_swap : Equiv.swap (0 : Fin 4) 1 ∉ viergruppe := by
    change Equiv.swap (0 : Fin 4) 1 ∉ viergruppeFinset; decide
  have hmem_dbl : Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ∈ viergruppe := by
    change Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ∈ viergruppeFinset; decide
  exact ⟨hA3, hS3, hA4, hS4, hnot_swap, hmem_dbl⟩

/-- **Corollary [to Theorem 17.2] (literal, printed p. 134 / PDF p. 142):**
`Σ_n` is not soluble, for `n ≥ 5`. (Proved via its non-soluble subgroup `A_n` — and `A_5` — by
`Theorem 17.2(i)` and `section_17_1_alternating_simple_and_not_soluble`.) -/
theorem corollary_to_theorem_17_2 {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsGarlingSoluble (SigmaN n) ∧ ¬ Group.IsSolvable (SigmaN n) := by
  have hnot_gsol : ¬ IsGarlingSoluble (SigmaN n) := fun hsol =>
    (section_17_1_alternating_simple_and_not_soluble hn).2.2.2.1
      (theorem_17_2_i hsol (alternatingGroup (Fin n)))
  exact ⟨hnot_gsol, fun h => hnot_gsol (isGarlingSoluble_iff_isSolvable_of_finite.mpr h)⟩

/-- Garling's **literal printed** definition of *nilpotent* in `Exercise 17.1`
(§17.2, printed p. 134 / PDF p. 142):
*"A group `G` is **nilpotent** if there is a finite series of subgroups
`{e} = G_n ⊆ G_{n-1} ⊆ … ⊆ G_0 = G` and that [sic] each `G_i` is normal in `G` and
`G_i/G_{i+1}` is abelian for `0 ≤ i < n`."*

Genuine textbook error: the derived series of every soluble group satisfies this predicate, so on
finite groups it is equivalent to `IsGarlingSoluble` (`exercise_17_1_printed_equiv_soluble_of_finite`)
and renders Part 2 of `Exercise 17.1` unsatisfiable (`exercise_17_1_printed_part2_unsatisfiable`). -/
def IsGarlingPrintedNilpotent (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G),
    H 0 = ⊤ ∧
    H (Fin.last n) = ⊥ ∧
    (∀ i : Fin n, H i.succ ≤ H i.castSucc) ∧
    ∃ (hnorm : ∀ j : Fin (n + 1), (H j).Normal),
      ∀ i : Fin n,
        haveI : ((H i.succ).subgroupOf (H i.castSucc)).Normal :=
          (hnorm i.succ).comap (H i.castSucc).subtype
        ∀ x y : (H i.castSucc) ⧸ (H i.succ).subgroupOf (H i.castSucc), x * y = y * x

/-- Standard **central-series** definition of *nilpotent* (the intended definition in
`Exercise 17.1`): there exists `{e} = G_n ⊆ G_{n-1} ⊆ … ⊆ G_0 = G` with each `G_i ⊲ G` and
`G_i/G_{i+1} ⊆ Z(G/G_{i+1})` for `0 ≤ i < n`. -/
def IsGarlingCentralNilpotent (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G),
    H 0 = ⊤ ∧
    H (Fin.last n) = ⊥ ∧
    (∀ i : Fin n, H i.succ ≤ H i.castSucc) ∧
    ∃ (hnorm : ∀ j : Fin (n + 1), (H j).Normal),
      ∀ i : Fin n,
        haveI := hnorm i.succ
        (H i.castSucc).map (QuotientGroup.mk' (H i.succ)) ≤ Subgroup.center (G ⧸ H i.succ)

/-- Equivalence between `IsGarlingCentralNilpotent G` and Mathlib's `Group.IsNilpotent G`. -/
theorem isGarlingCentralNilpotent_iff_isNilpotent (G : Type*) [Group G] :
    IsGarlingCentralNilpotent G ↔ Group.IsNilpotent G := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  constructor
  · rintro ⟨n, H, h0, hlast, _, hnorm, hcent⟩
    refine ⟨n, ?_⟩
    suffices hle_lcs : ∀ k : ℕ, (hk : k < n + 1) →
        Subgroup.lowerCentralSeries (⊤ : Subgroup G) k ≤ H ⟨k, hk⟩ by
      exact le_bot_iff.mp ((hle_lcs n (Nat.lt_succ_self n)).trans_eq hlast)
    intro k
    induction k with
    | zero =>
      intro _
      rw [Subgroup.lowerCentralSeries_zero,
        show (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = 0 from rfl, h0]
    | succ r ih =>
      intro hr
      let i : Fin n := ⟨r, Nat.lt_of_succ_lt_succ hr⟩
      have hprev : Subgroup.lowerCentralSeries (⊤ : Subgroup G) r ≤ H i.castSucc := ih (by omega)
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
      intro x hx g _
      have : (H i.succ).Normal := hnorm i.succ
      have hmem_cent : QuotientGroup.mk x ∈ Subgroup.center (G ⧸ H i.succ) :=
        hcent i ⟨x, hprev hx, rfl⟩
      rw [Subgroup.mem_center_iff] at hmem_cent
      have hcomm := hmem_cent (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
      have h1 : (g * x)⁻¹ * (x * g) ∈ H i.succ := hcomm
      have h2 := (hnorm i.succ).conj_mem _ h1 (g * x)
      have heq : (g * x) * ((g * x)⁻¹ * (x * g)) * (g * x)⁻¹ = ⁅x, g⁆ := by
        simp only [commutatorElement_def]; group
      rwa [heq] at h2
  · rintro ⟨n, hn⟩
    let H : Fin (n + 1) → Subgroup G := fun j => Subgroup.lowerCentralSeries (⊤ : Subgroup G) j
    have hnorm : ∀ j : Fin (n + 1), (H j).Normal := by
      intro ⟨k, hk⟩
      dsimp only [H]
      induction k with
      | zero => rw [Subgroup.lowerCentralSeries_zero]; infer_instance
      | succ r ihr =>
        rw [Subgroup.lowerCentralSeries_succ]
        have : (Subgroup.lowerCentralSeries (⊤ : Subgroup G) r).Normal := ihr (by omega)
        exact Subgroup.commutator_normal _ _
    refine ⟨n, H, Subgroup.lowerCentralSeries_zero _, hn,
      fun i => Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (Nat.le_succ i),
      hnorm, fun i => ?_⟩
    have : (H i.succ).Normal := hnorm i.succ
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    change QuotientGroup.mk g * QuotientGroup.mk x = QuotientGroup.mk x * QuotientGroup.mk g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm : ⁅x⁻¹, g⁻¹⁆ ∈ H i.succ := by
      have h1 : ⁅x⁻¹, g⁻¹⁆ ∈ ⁅H i.castSucc, (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator ((H i.castSucc).inv_mem hx) (Subgroup.mem_top _)
      have h2 : ⁅H i.castSucc, (⊤ : Subgroup G)⁆ = H i.succ := by
        simp only [H, Fin.val_succ, Fin.val_castSucc, Subgroup.lowerCentralSeries_succ]
      rwa [h2] at h1
    simpa [commutatorElement_def, mul_assoc] using hcomm

/-- **Exercise 17.1 — Blocker Proof 1 (printed p. 134):** For every **finite** group `G`, Garling's
literal printed *nilpotent* predicate `IsGarlingPrintedNilpotent G` is logically equivalent to
`IsGarlingSoluble G` (witnessed in `(⇐)` by the derived series `derivedSeries G`). -/
theorem exercise_17_1_printed_equiv_soluble_of_finite {G : Type*} [Group G] [Finite G] :
    IsGarlingPrintedNilpotent G ↔ IsGarlingSoluble G := by
  constructor
  · rintro ⟨n, H, h0, hlast, _, hnorm, hab⟩
    rw [isGarlingSoluble_iff_isSolvable_of_finite]
    suffices hder : ∀ k : ℕ, (hk : k < n + 1) → derivedSeries G k ≤ H ⟨k, hk⟩ by
      exact ⟨⟨n, le_bot_iff.mp ((hder n (Nat.lt_succ_self n)).trans_eq hlast)⟩⟩
    intro k
    induction k with
    | zero =>
      intro _
      rw [derivedSeries_zero, show (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) = 0 from rfl, h0]
    | succ r ih =>
      intro hr
      let i : Fin n := ⟨r, Nat.lt_of_succ_lt_succ hr⟩
      have hprev : derivedSeries G r ≤ H i.castSucc := ih (by omega)
      rw [derivedSeries_succ, Subgroup.commutator_le]
      intro x hx y hy
      have : ((H i.succ).subgroupOf (H i.castSucc)).Normal :=
        (hnorm i.succ).comap (H i.castSucc).subtype
      have hcomm := hab i (QuotientGroup.mk ⟨x, hprev hx⟩) (QuotientGroup.mk ⟨y, hprev hy⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
      have h1 : (x * y)⁻¹ * (y * x) ∈ H i.succ := hcomm
      have h2 := (hnorm i.succ).conj_mem _ h1 (x * y)
      have h3 := (H i.succ).inv_mem h2
      have heq : ((x * y) * ((x * y)⁻¹ * (y * x)) * (x * y)⁻¹)⁻¹ = ⁅x, y⁆ := by
        simp only [commutatorElement_def]; group
      rwa [heq] at h3
  · intro hsol
    have hmsol : Group.IsSolvable G := isSolvable_of_isGarlingSoluble hsol
    obtain ⟨n, hn⟩ := hmsol.solvable
    let H : Fin (n + 1) → Subgroup G := fun j => derivedSeries G j
    have hnorm : ∀ j : Fin (n + 1), (H j).Normal := fun j => derivedSeries_normal G j
    refine ⟨n, H, derivedSeries_zero G, hn,
      fun i => derivedSeries_antitone G (Nat.le_succ i), hnorm, fun i x y => ?_⟩
    have : ((H i.succ).subgroupOf (H i.castSucc)).Normal :=
      (hnorm i.succ).comap (H i.castSucc).subtype
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    change (a * b)⁻¹ * (b * a) ∈ H i.succ
    have hc : ⁅b⁻¹, a⁻¹⁆ ∈ H i.succ := by
      simp only [H, Fin.val_succ, derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ((H i.castSucc).inv_mem hb)
        ((H i.castSucc).inv_mem ha)
    simpa [commutatorElement_def, mul_assoc] using hc

/-- **Exercise 17.1 — Blocker Proof 2 (printed p. 134):** Part 2 (*"give an example of a finite
soluble group which is not nilpotent"*) is **logically unsatisfiable** under Garling's literal
printed definition `IsGarlingPrintedNilpotent`. -/
theorem exercise_17_1_printed_part2_unsatisfiable :
    ¬ ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      IsGarlingSoluble G ∧ ¬ IsGarlingPrintedNilpotent G := by
  rintro ⟨G, _, _, hsol, hnot⟩
  exact hnot (exercise_17_1_printed_equiv_soluble_of_finite.mpr hsol)

/-- **Exercise 17.1, Part 1 (under literal printed definition, p. 134):** Every finite
`IsGarlingPrintedNilpotent` group is Garling-soluble. -/
theorem exercise_17_1_part1_printed {G : Type*} [Group G] [Finite G]
    (h : IsGarlingPrintedNilpotent G) : IsGarlingSoluble G :=
  exercise_17_1_printed_equiv_soluble_of_finite.mp h

/-- Helper: a nontrivial nilpotent group has nontrivial centre (`Subgroup.center G ≠ ⊥`). -/
private theorem center_ne_bot_of_isNilpotent {G : Type*} [Group G] [Nontrivial G]
    [hnil : Group.IsNilpotent G] :
    Subgroup.center G ≠ ⊥ := by
  intro hbot
  have hall : ∀ k : ℕ, Subgroup.upperCentralSeries G k = ⊥ := by
    intro k
    induction k with
    | zero => exact Subgroup.upperCentralSeries_zero G
    | succ r ih =>
      ext x
      rw [Subgroup.mem_upperCentralSeries_succ_iff, ih]
      simp only [Subgroup.mem_bot]
      constructor
      · intro hx
        have hmem : x ∈ Subgroup.center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact (commutatorElement_eq_one_iff_mul_comm.mp (hx g)).symm
        rwa [hbot, Subgroup.mem_bot] at hmem
      · rintro rfl g; simp
  obtain ⟨k, hk⟩ := hnil.nilpotent
  rw [hall k] at hk
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have ha : a = 1 := Subgroup.mem_bot.mp (hk.symm ▸ Subgroup.mem_top a)
  have hb : b = 1 := Subgroup.mem_bot.mp (hk.symm ▸ Subgroup.mem_top b)
  exact hab (ha.trans hb.symm)

/-- **Exercise 17.1 (repaired under standard central-series nilpotency, printed p. 134 /
PDF p. 142):**
1. Every finite nilpotent group (`IsGarlingCentralNilpotent` / `Group.IsNilpotent`) is soluble.
2. Both `Σ_3` (order `6`, trivial centre) and `A_4` (order `12`, trivial centre) are finite
   Garling-soluble groups which are **not** nilpotent (while satisfying Garling's flawed printed
   predicate `IsGarlingPrintedNilpotent`). -/
theorem exercise_17_1_repaired :
    (∀ {G : Type u} [Group G] [Finite G], IsGarlingCentralNilpotent G → IsGarlingSoluble G) ∧
    (Finite (SigmaN 3) ∧ IsGarlingSoluble (SigmaN 3) ∧
      ¬ IsGarlingCentralNilpotent (SigmaN 3) ∧ ¬ Group.IsNilpotent (SigmaN 3) ∧
      IsGarlingPrintedNilpotent (SigmaN 3)) ∧
    (Finite (alternatingGroup (Fin 4)) ∧ IsGarlingSoluble (alternatingGroup (Fin 4)) ∧
      ¬ IsGarlingCentralNilpotent (alternatingGroup (Fin 4)) ∧
      ¬ Group.IsNilpotent (alternatingGroup (Fin 4)) ∧
      IsGarlingPrintedNilpotent (alternatingGroup (Fin 4))) := by
  have hpart1 : ∀ {G : Type u} [Group G] [Finite G],
      IsGarlingCentralNilpotent G → IsGarlingSoluble G := by
    intro G _ _ hnil
    have : Group.IsNilpotent G := (isGarlingCentralNilpotent_iff_isNilpotent G).mp hnil
    exact isGarlingSoluble_iff_isSolvable_of_finite.mpr inferInstance
  have hnot_nil_S3 : ¬ Group.IsNilpotent (SigmaN 3) := by
    intro hnil
    have : Group.IsNilpotent (SigmaN 3) := hnil
    have : Nontrivial (SigmaN 3) := ⟨⟨1, Equiv.swap 0 1, by decide⟩⟩
    apply center_ne_bot_of_isNilpotent (G := SigmaN 3)
    ext σ
    simp only [Subgroup.mem_center_iff, Subgroup.mem_bot]
    refine ⟨fun h => ?_, fun h => by subst h; simp⟩
    have hfin : ∀ τ : SigmaN 3, (∀ g : SigmaN 3, g * τ = τ * g) → τ = 1 := by decide
    exact hfin σ h
  have hnot_nil_A4 : ¬ Group.IsNilpotent (alternatingGroup (Fin 4)) := by
    intro hnil
    have : Group.IsNilpotent (alternatingGroup (Fin 4)) := hnil
    have hmemA4 : Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; decide
    have : Nontrivial (alternatingGroup (Fin 4)) :=
      ⟨⟨1, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, hmemA4⟩, fun h =>
        (by decide : (1 : SigmaN 4) ≠ Equiv.swap 0 1 * Equiv.swap 2 3) (congrArg Subtype.val h)⟩⟩
    apply center_ne_bot_of_isNilpotent (G := alternatingGroup (Fin 4))
    ext σ
    simp only [Subgroup.mem_center_iff, Subgroup.mem_bot]
    refine ⟨fun h => ?_, fun h => by subst h; simp⟩
    have hfin : ∀ τ : alternatingGroup (Fin 4),
        (∀ g : alternatingGroup (Fin 4), g * τ = τ * g) → τ = 1 := by decide
    exact hfin σ h
  have hS3_sol := section_17_1_soluble_examples.2.1
  have hA4_sol := section_17_1_soluble_examples.2.2.1
  refine ⟨hpart1,
    ⟨inferInstance, hS3_sol,
      fun h => hnot_nil_S3 ((isGarlingCentralNilpotent_iff_isNilpotent _).mp h),
      hnot_nil_S3,
      exercise_17_1_printed_equiv_soluble_of_finite.mpr hS3_sol⟩,
    ⟨inferInstance, hA4_sol,
      fun h => hnot_nil_A4 ((isGarlingCentralNilpotent_iff_isNilpotent _).mp h),
      hnot_nil_A4,
      exercise_17_1_printed_equiv_soluble_of_finite.mpr hA4_sol⟩⟩

/-- Garling's inline prose definition of the *centre* `Z` of a group `G` (`Exercise 17.2`, §17.2,
printed p. 134 / PDF p. 142):
`Z = {z : gz = zg for all g in G}`. -/
def garlingCentre (G : Type*) [Group G] : Subgroup G where
  carrier := {z : G | ∀ g : G, g * z = z * g}
  one_mem' g := by simp
  mul_mem' {a b} ha hb g := by
    calc g * (a * b) = (g * a) * b := (mul_assoc g a b).symm
      _ = (a * g) * b := by rw [ha g]
      _ = a * (g * b) := mul_assoc a g b
      _ = a * (b * g) := by rw [hb g]
      _ = (a * b) * g := (mul_assoc a b g).symm
  inv_mem' {a} ha g := by
    have h1 := ha g
    calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
      _ = a⁻¹ * (g * a) * a⁻¹ := by rw [h1]
      _ = a⁻¹ * g := by group

/-- Bridge between `garlingCentre G` and Mathlib's `Subgroup.center G`. -/
theorem garlingCentre_eq_center (G : Type*) [Group G] :
    garlingCentre G = Subgroup.center G := by
  ext z
  simp [garlingCentre, Subgroup.mem_center_iff]

/-- **Exercise 17.2 — Counterexample at `n = 0` (printed p. 134):**
The printed statement omits `1 ≤ n`. For every prime `p`, the trivial group `G = {e}` has order
`p^0 = 1`, while `|Z| = 1 < p`, falsifying `|Z| ≥ p`. -/
theorem exercise_17_2_n0_counterexample {p : ℕ} (hp : Nat.Prime p) :
    Nat.card (Multiplicative Unit) = p ^ 0 ∧
    setOrder (Multiplicative Unit) = ((p ^ 0 : ℕ) : ℕ∞) ∧
    Nat.card (garlingCentre (Multiplicative Unit)) = 1 ∧
    ¬ (p ≤ Nat.card (garlingCentre (Multiplicative Unit))) := by
  have hc2 : Nat.card (garlingCentre (Multiplicative Unit)) = 1 := Nat.card_unique
  have hso : setOrder (Multiplicative Unit) = ((p ^ 0 : ℕ) : ℕ∞) := by
    simp [setOrder]
  have hp2 : 2 ≤ p := hp.two_le
  exact ⟨by simp, hso, hc2, by omega⟩

/-- **Exercise 17.2, Part 2 (unconditional for all `n : ℕ`, printed p. 134):**
Every group of order `p^n` (`p` prime, `n ≥ 0`) is nilpotent under both standard central-series
nilpotency (`IsGarlingCentralNilpotent` / `Group.IsNilpotent`) and Garling's printed predicate
(`IsGarlingPrintedNilpotent`). -/
theorem exercise_17_2_part2_unconditional {G : Type*} [Group G] [Finite G] {p n : ℕ}
    (hp : Nat.Prime p) (hcard : Nat.card G = p ^ n) :
    IsGarlingCentralNilpotent G ∧ Group.IsNilpotent G ∧ IsGarlingPrintedNilpotent G := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hpG : IsPGroup p G := IsPGroup.of_card hcard
  have hnil : Group.IsNilpotent G := hpG.isNilpotent
  have hcnil : IsGarlingCentralNilpotent G :=
    (isGarlingCentralNilpotent_iff_isNilpotent G).mpr hnil
  have hsol : IsGarlingSoluble G := isGarlingSoluble_iff_isSolvable_of_finite.mpr inferInstance
  have hpnil : IsGarlingPrintedNilpotent G :=
    exercise_17_1_printed_equiv_soluble_of_finite.mpr hsol
  exact ⟨hcnil, hnil, hpnil⟩

/-- **Exercise 17.2 (repaired with `1 ≤ n`, printed p. 134 / PDF p. 142):**
If `|G| = p^n` with `p` prime and `1 ≤ n`, then the centre `Z` has at least `p` elements
(`p ≤ |Z|` and `(p : ℕ∞) ≤ setOrder Z`) and `G` is nilpotent (under both central-series and printed
definitions). -/
theorem exercise_17_2_repaired {G : Type*} [Group G] [Finite G] {p n : ℕ}
    (hp : Nat.Prime p) (hn : 1 ≤ n) (hcard : Nat.card G = p ^ n) :
    p ≤ Nat.card (garlingCentre G) ∧
    (p : ℕ∞) ≤ setOrder (garlingCentre G) ∧
    IsGarlingCentralNilpotent G ∧ Group.IsNilpotent G ∧ IsGarlingPrintedNilpotent G := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hpG : IsPGroup p G := IsPGroup.of_card hcard
  have hG_gt1 : 1 < Nat.card G := by
    rw [hcard]
    calc 1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hG_gt1
  have hZ_nt : Nontrivial (Subgroup.center G) := hpG.center_nontrivial
  have hZ_gt1 : 1 < Nat.card (Subgroup.center G) :=
    Finite.one_lt_card_iff_nontrivial.mpr hZ_nt
  have hZ_dvd : Nat.card (Subgroup.center G) ∣ p ^ n := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card (Subgroup.center G)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hZ_dvd
  have hk_pos : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    rw [hk_eq, pow_zero] at hk
    omega
  have hp_le_Z : p ≤ Nat.card (garlingCentre G) := by
    rw [garlingCentre_eq_center, hk]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk_pos
  have hp_le_setOrder : (p : ℕ∞) ≤ setOrder (garlingCentre G) := by
    rw [setOrder, ENat.card_eq_coe_natCard]
    exact_mod_cast hp_le_Z
  obtain ⟨h1, h2, h3⟩ := exercise_17_2_part2_unconditional hp hcard
  exact ⟨hp_le_Z, hp_le_setOrder, h1, h2, h3⟩

/-- **Exercise 17.2 — Exact `iff` characterization for `|Z| ≥ p` across all `n : ℕ`:**
For a group `G` of order `p^n` (`p` prime), `|Z| ≥ p` holds if and only if `1 ≤ n`. -/
theorem exercise_17_2_centre_iff {G : Type*} [Group G] [Finite G] {p n : ℕ}
    (hp : Nat.Prime p) (hcard : Nat.card G = p ^ n) :
    p ≤ Nat.card (garlingCentre G) ↔ 1 ≤ n := by
  constructor
  · intro hpZ
    by_contra hn0
    have hn : n = 0 := by omega
    rw [hn, pow_zero] at hcard
    have hle : Nat.card (garlingCentre G) ≤ Nat.card G :=
      Nat.le_of_dvd (by omega) (Subgroup.card_subgroup_dvd_card (garlingCentre G))
    have hp2 : 2 ≤ p := hp.two_le
    omega
  · intro hn
    exact (exercise_17_2_repaired hp hn hcard).1

/-! ## §17.3 Polynomials with soluble Galois groups (printed pp. 134–135, PDF pp. 142–143) -/

/-- Helper: `ringChar K` does not divide `1` for any field `K` (since `ringChar K` is `0` or prime). -/
private theorem not_ringChar_dvd_one (K : Type*) [Field K] : ¬ (ringChar K ∣ 1) := by
  intro hdvd
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · exact hp.not_dvd_one hdvd
  · rw [h0, zero_dvd_iff] at hdvd; omega

/-- Helper: `ringChar K` does not divide a finite product `∏ i, n i` iff it divides none of `n i`. -/
theorem not_ringChar_dvd_prod_iff (K : Type*) [Field K] {r : ℕ} (n : Fin r → ℕ) :
    ¬ (ringChar K ∣ ∏ i : Fin r, n i) ↔ ∀ i : Fin r, ¬ (ringChar K ∣ n i) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · rw [hp.prime.dvd_finsetProd_iff]
    simp
  · rw [h0]
    simp only [zero_dvd_iff, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, not_exists]

/-- Helper: `ringChar` is preserved along any field extension `K → L`. -/
private theorem ringChar_eq_of_field_algebra (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : ringChar L = ringChar K :=
  ringChar.eq_iff.mpr (charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K))

/-- Helper: `GarlingSplitsOver` lifts along a scalar tower `K → L → N` (`f.map (algebraMap K L)`
splits over `N` implies `f` splits over `N`). -/
private theorem garlingSplitsOver_of_map {K : Type u} {L : Type v} {N : Type w}
    [Field K] [Field L] [Field N] [Algebra K L] [Algebra L N] [Algebra K N]
    [IsScalarTower K L N] {f : K[X]}
    (hspl : GarlingSplitsOver L N (f.map (algebraMap K L))) :
    GarlingSplitsOver K N f := by
  rcases hspl with ⟨n, c, α, hexp⟩
  by_cases hf0 : f = 0
  · subst hf0
    exact ⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
  · have hmap : (f.map (algebraMap K L)).map (algebraMap L N) = f.map (algebraMap K N) := by
      rw [Polynomial.map_map, IsScalarTower.algebraMap_eq K L N]
    rw [GarlingSplitsExplicit, hmap] at hexp
    have hc_eq : algebraMap L N c = algebraMap K N f.leadingCoeff := by
      have hlc := congrArg Polynomial.leadingCoeff hexp
      have hmon : (∏ j : Fin n, (Polynomial.X - Polynomial.C (α j))).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (α j)
      rw [Polynomial.leadingCoeff_map_of_injective (algebraMap K N).injective,
        Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff, mul_one] at hlc
      exact hlc.symm
    refine ⟨n, f.leadingCoeff, α, ?_⟩
    rw [GarlingSplitsExplicit, hexp, hc_eq]

/-- Helper: `GarlingSplitsOver K L f` pushes forward along `L → M` in a scalar tower `K → L → M`. -/
private theorem garlingSplitsOver_tower_right {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] {f : K[X]} (hspl : GarlingSplitsOver K L f) :
    GarlingSplitsOver K M f := by
  rcases hspl with ⟨n, c, α, hexp⟩
  refine ⟨n, c, fun i => algebraMap L M (α i), ?_⟩
  rw [GarlingSplitsExplicit, IsScalarTower.algebraMap_eq K L M, ← Polynomial.map_map, hexp,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- Helper: transport `IsGarlingGaloisExtension K L₁` along a `K`-algebra isomorphism `L₁ ≃ₐ[K] L₂`. -/
private theorem isGarlingGaloisExtension_congr {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (h : IsGarlingGaloisExtension K L₁) :
    IsGarlingGaloisExtension K L₂ := by
  rw [isGarlingGaloisExtension_iff] at h ⊢
  obtain ⟨hfin, hgal⟩ := h
  have : FiniteDimensional K L₁ := hfin
  have : IsGalois K L₁ := hgal
  have : FiniteDimensional K L₂ := Module.Finite.equiv e.toLinearEquiv
  have : Normal K L₂ := Normal.of_algEquiv e
  have : Algebra.IsSeparable K L₂ := by
    refine ⟨fun x => ?_⟩
    rw [IsSeparable, ← minpoly.algEquiv_eq e.symm x]
    exact Algebra.IsSeparable.isSeparable K (e.symm x)
  exact ⟨inferInstance, ⟨⟩⟩

/-- Helper: underlying subfield of `IntermediateField.adjoin` equals `Subfield.closure`. -/
private theorem adjoin_toSubfield_eq_closure_ch17 {M : Type v} {L : Type w}
    [Field M] [Field L] [Algebra M L] (S : Set L) :
    (IntermediateField.adjoin M S).toSubfield =
      Subfield.closure (Set.range (algebraMap M L) ∪ S) := by
  apply le_antisymm
  · let C : Subfield L := Subfield.closure (Set.range (algebraMap M L) ∪ S)
    let CM : IntermediateField M L :=
      { C with algebraMap_mem' := fun m => Subfield.subset_closure (Or.inl ⟨m, rfl⟩) }
    have hle : IntermediateField.adjoin M S ≤ CM :=
      IntermediateField.adjoin_le_iff.mpr fun s hs => Subfield.subset_closure (Or.inr hs)
    exact hle
  · rw [Subfield.closure_le]
    rintro x (⟨m, rfl⟩ | hx)
    · exact (IntermediateField.adjoin M S).algebraMap_mem m
    · exact IntermediateField.subset_adjoin M S hx

/-- Helper: given a finite Galois extension `N / L` and a subgroup `G₀ ≤ Gal(N/L)` with normal
subgroup `G₁ ≤ G₀` and cyclic quotient `G₀ / G₁`, if `F₀ = fixedField G₀` and `F₁ = fixedField G₁`
and `L` contains a primitive `d`th root of unity with `|Gal(N/L)| ∣ d` and `char L ∤ d`, then
there exist `m ≥ 1` and `β ∈ N` with `β ^ m ∈ F₀` and `F₁ = L(F₀ ∪ {β})`. -/
private theorem cyclic_fixedField_step_radical {L : Type u} {N : Type v}
    [Field L] [Field N] [Algebra L N] [FiniteDimensional L N] [IsGalois L N]
    {d : ℕ} (hchar : ¬ (ringChar L ∣ d)) {ε : L} (hε : IsPrimitiveRoot ε d)
    (hdvd_gal : Nat.card (N ≃ₐ[L] N) ∣ d)
    {G₀ G₁ : Subgroup (N ≃ₐ[L] N)} (hle : G₁ ≤ G₀)
    (hnorm : (G₁.subgroupOf G₀).Normal)
    (hcyc : IsCyclic (↥G₀ ⧸ G₁.subgroupOf G₀)) :
    let F₀ : IntermediateField L N := IntermediateField.fixedField G₀
    let F₁ : IntermediateField L N := IntermediateField.fixedField G₁
    ∃ (β : N) (m : ℕ), 1 ≤ m ∧ β ^ m ∈ F₀ ∧
      F₁ = IntermediateField.adjoin L ((F₀ : Set N) ∪ {β}) := by
  classical
  intro F₀ F₁
  have hF01 : F₀ ≤ F₁ := IntermediateField.fixedField_antitone hle
  -- `N / F₀` is finite Galois, and `Gal(N / F₀) ≃* G₀`
  have : FiniteDimensional F₀ N := FiniteDimensional.right L F₀ N
  have : IsGalois F₀ N := IsGalois.tower_top_of_isGalois L F₀ N
  let eG0 : (N ≃ₐ[F₀] N) ≃* G₀ :=
    { toFun := fun σ =>
        ⟨σ.restrictScalars L, by
          have hmem : σ.restrictScalars L ∈ F₀.fixingSubgroup := by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact σ.commutes ⟨x, hx⟩
          rwa [IntermediateField.fixingSubgroup_fixedField] at hmem⟩
      invFun := fun τ =>
        { τ.1.toRingEquiv with
          commutes' := fun ⟨x, hx⟩ => by
            have hfx := (IntermediateField.mem_fixedField_iff G₀ x).mp hx
            exact hfx τ.1 τ.2 }
      left_inv := fun σ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl
      map_mul' := fun _ _ => by ext x; rfl }
  let H₁ : Subgroup (N ≃ₐ[F₀] N) := (G₁.subgroupOf G₀).comap eG0.toMonoidHom
  have : H₁.Normal := hnorm.comap eG0.toMonoidHom
  have hmapH1 : H₁.map eG0.toMonoidHom = G₁.subgroupOf G₀ := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_comap, H₁]
    exact ⟨fun ⟨y, hy, heq⟩ => heq ▸ hy, fun hx => ⟨eG0.symm x, by simpa using hx, eG0.apply_symm_apply x⟩⟩
  let E₁ : IntermediateField F₀ N := IntermediateField.fixedField H₁
  have hE1_carrier : (E₁ : Set N) = (F₁ : Set N) := by
    ext x
    simp only [SetLike.mem_coe, IntermediateField.mem_fixedField_iff, E₁, F₁, H₁,
      Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · intro hx σ hσ
      let τ : N ≃ₐ[F₀] N := eG0.symm ⟨σ, hle hσ⟩
      have hτ : τ ∈ H₁ := by
        change eG0 τ ∈ G₁.subgroupOf G₀
        rw [eG0.apply_symm_apply]
        exact hσ
      exact hx τ hτ
    · intro hx σ hσ
      exact hx (σ.restrictScalars L) hσ
  have : IsGalois F₀ E₁ := IsGalois.of_fixedField_normal_subgroup H₁
  have : FiniteDimensional F₀ E₁ := FiniteDimensional.left F₀ E₁ N
  have hgal_F0_E1 : IsGarlingGaloisExtension F₀ E₁ :=
    (isGarlingGaloisExtension_iff F₀ E₁).mpr ⟨inferInstance, inferInstance⟩
  let eGalQ : ((N ≃ₐ[F₀] N) ⧸ H₁) ≃* (E₁ ≃ₐ[F₀] E₁) :=
    IsGalois.normalAutEquivQuotient H₁
  let eQuot : ((N ≃ₐ[F₀] N) ⧸ H₁) ≃* (↥G₀ ⧸ G₁.subgroupOf G₀) :=
    QuotientGroup.congr H₁ (G₁.subgroupOf G₀) eG0 hmapH1
  let eGal : (E₁ ≃ₐ[F₀] E₁) ≃* (↥G₀ ⧸ G₁.subgroupOf G₀) := eGalQ.symm.trans eQuot
  have hcyc_E1 : IsCyclic (GarlingGaloisGroup F₀ E₁) :=
    isCyclic_of_surjective eGal.symm.toMonoidHom eGal.symm.surjective
  have hcyc_ext : Garling.Chapter16.IsGarlingCyclicExtension F₀ E₁ := ⟨hgal_F0_E1, hcyc_E1⟩
  let m := Module.finrank F₀ E₁
  have hm_eq_card : m = Nat.card (↥G₀ ⧸ G₁.subgroupOf G₀) := by
    calc m = Nat.card (E₁ ≃ₐ[F₀] E₁) := (IsGalois.card_aut_eq_finrank F₀ E₁).symm
      _ = Nat.card (↥G₀ ⧸ G₁.subgroupOf G₀) := Nat.card_congr eGal.toEquiv
  have hm_dvd_G0 : m ∣ Nat.card G₀ := by
    rw [hm_eq_card]
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (G₁.subgroupOf G₀)
    exact ⟨Nat.card (G₁.subgroupOf G₀), hlag⟩
  have hm_dvd_d : m ∣ d :=
    hm_dvd_G0.trans ((Subgroup.card_subgroup_dvd_card G₀).trans hdvd_gal)
  have hchar_F0 : ¬ (ringChar F₀ ∣ m) := by
    rw [ringChar_eq_of_field_algebra L F₀]
    exact fun h => hchar (h.trans hm_dvd_d)
  have hm_pos : 1 ≤ m :=
    (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar_F0).1
  have hd_pos : 1 ≤ d :=
    (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar).1
  have hq_ne0 : d / m ≠ 0 := by
    have hle_md : m ≤ d := Nat.le_of_dvd (by omega) hm_dvd_d
    exact Nat.ne_of_gt (Nat.div_pos hle_md (by omega))
  have hq_dvd : d / m ∣ d := Nat.div_dvd_of_dvd hm_dvd_d
  have hprim_L : IsPrimitiveRoot (ε ^ (d / m)) m := by
    have h1 := hε.pow_of_dvd hq_ne0 hq_dvd
    rwa [Nat.div_div_self hm_dvd_d (by omega)] at h1
  let ω : F₀ := algebraMap L F₀ (ε ^ (d / m))
  have hω : IsPrimitiveRoot ω m := hprim_L.map_of_injective (algebraMap L F₀).injective
  obtain ⟨θ, _, hsf_E1, hgen_E1⟩ :=
    Garling.Chapter16.theorem_16_4 hcyc_ext rfl hchar_F0 hω
  -- Extract a root `β₁ ∈ E₁` of `X^m - C θ` from splitting of `X^m - C θ` over `E₁`
  obtain ⟨k, c, α, hexp⟩ := hsf_E1.1
  have hf0 : (Polynomial.X ^ m - Polynomial.C θ : F₀[X]) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C θ (by omega)).ne_zero
  have hk_eq : k = m := by
    have hdeg := (garlingSplitsExplicit_props hf0 hexp).2.2.1
    change k = (Polynomial.X ^ m - Polynomial.C θ : F₀[X]).natDegree at hdeg
    rw [Polynomial.natDegree_X_pow_sub_C] at hdeg
    exact hdeg
  let idx0 : Fin k := ⟨0, by omega⟩
  let β₁ : E₁ := α idx0
  have hβ₁_root : Polynomial.aeval β₁ (Polynomial.X ^ m - Polynomial.C θ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp, Polynomial.eval_mul,
      Polynomial.eval_prod]
    have hzero : (∏ i : Fin k, (Polynomial.X - Polynomial.C (α i))).eval β₁ = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ idx0) (by simp [β₁])
    rw [Polynomial.eval_prod] at hzero
    rw [hzero, mul_zero]
  have hβ₁_pow : β₁ ^ m = algebraMap F₀ E₁ θ := by
    have h := hβ₁_root
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h
    exact h
  have hβ₁_gen : IntermediateField.adjoin F₀ ({β₁} : Set E₁) = ⊤ := hgen_E1 β₁ hβ₁_root
  refine ⟨β₁.1, m, hm_pos, ?_, ?_⟩
  · have hpow_val : β₁.1 ^ m = θ.1 := congrArg Subtype.val hβ₁_pow
    rw [hpow_val]
    exact θ.2
  · apply IntermediateField.toSubfield_injective
    rw [adjoin_toSubfield_eq_closure_ch17]
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ E₁ := by rwa [← SetLike.mem_coe, hE1_carrier]
      have hx_top : (⟨x, hxE⟩ : E₁) ∈ IntermediateField.adjoin F₀ ({β₁} : Set E₁) := by
        rw [hβ₁_gen]; exact IntermediateField.mem_top
      have hsub_map : (IntermediateField.adjoin F₀ ({β₁} : Set E₁)).toSubfield.map E₁.val.toRingHom ≤
          Subfield.closure (Set.range (algebraMap L N) ∪ ((F₀ : Set N) ∪ {β₁.1})) := by
        rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
        rintro y (⟨a, rfl⟩ | rfl)
        · exact Subfield.subset_closure (Or.inr (Or.inl a.2))
        · exact Subfield.subset_closure (Or.inr (Or.inr rfl))
      exact hsub_map ⟨⟨x, hxE⟩, hx_top, rfl⟩
    · rw [Subfield.closure_le]
      rintro x (⟨l, rfl⟩ | hxF0 | rfl)
      · exact F₁.algebraMap_mem l
      · exact hF01 hxF0
      · have hmem : β₁.1 ∈ (E₁ : Set N) := β₁.2
        rwa [hE1_carrier] at hmem

/-- **Theorem 17.3 (literal, printed pp. 134–135 / PDF pp. 142–143):**
*"Suppose that `f` is a separable polynomial in `K[x]` whose Galois group `Γ_K(f)` is soluble,
and suppose that `char K` does not divide `|Γ_K(f)|`. Then `f` is solvable by radicals."*

Proved literally under Garling's §10.1 definition `IsGarlingSeparablePoly f` for **every**
`f ∈ K[X]` (including `f = 0`, constants, and polynomials with repeated separable factors),
following Garling's exact pp. 134–135 proof via `Theorem 11.9`, `Theorem 17.2(i)`, FTG, and
`Theorem 16.4`. -/
theorem theorem_17_3 {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {f : K[X]} (hsep : IsGarlingSeparablePoly f)
    (hsf : IsGarlingSplittingFieldExtension K F f)
    (hsol : IsGarlingSoluble (GarlingPolyGaloisGroup K F f))
    (hchar : ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K F f))) :
    IsGarlingSolvableByRadicals f := by
  classical
  by_cases hf0 : f = 0
  · subst hf0
    exact isGarlingSolvableByRadicals_of_extension (isGarlingExtensionByRadicals_self K)
      ⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
  · let d := Nat.card (GarlingPolyGaloisGroup K F f)
    have hd_pos : 1 ≤ d :=
      (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar).1
    -- Step 1: Adjoin a primitive `d`th root of unity `ε` via splitting field `L` of `X^d - 1`
    let L := Polynomial.SplittingField (Polynomial.X ^ d - 1 : K[X])
    have hsf_L : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ d - 1) :=
      (isGarlingSplittingFieldExtension_iff K L _).mpr inferInstance
    have hsf_L1 : IsGarlingSplittingFieldExtension K L (Polynomial.X ^ d - Polynomial.C 1) := by
      simpa using hsf_L
    obtain ⟨_, ⟨ε, hε⟩, _⟩ :=
      Garling.Chapter16.theorem_16_1 (one_ne_zero : (1 : K) ≠ 0) hchar hsf_L1
    have hsf_cyc_L : IsGarlingSplittingFieldExtension K L (Polynomial.cyclotomic d K) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hchar).1.mpr hsf_L
    have hε_garl : Garling.Chapter15.IsGarlingPrimitiveRoot d ε :=
      (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hd_pos ε).mpr hε
    have hL_eq_adj : IntermediateField.adjoin K ({ε} : Set L) = ⊤ :=
      ((Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hchar).2 hsf_cyc_L hε_garl).1
    have hKL_rad : IsGarlingExtensionByRadicals K L :=
      isGarlingExtensionByRadicals_single ⟨d, hd_pos, 1, by rw [map_one, hε.pow_eq_one]⟩ hL_eq_adj
    -- Step 2: Splitting field `N : L` for `fL = f.map (algebraMap K L)`
    let fL : L[X] := f.map (algebraMap K L)
    have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
    let N := Polynomial.SplittingField fL
    have hsf_LN : IsGarlingSplittingFieldExtension L N fL :=
      (isGarlingSplittingFieldExtension_iff L N fL).mpr inferInstance
    let M := garlingNatIrrM K L N f
    obtain ⟨_, hsf_KM, hsub_le, _, _, _, ⟨eGamma⟩, _⟩ := theorem_11_9 hf0 hsf_LN
    obtain ⟨hfL_sep, _, _, _, _, _⟩ := theorem_11_9_separable hf0 hsep hsf_LN
    have hgal_LN : IsGarlingGaloisExtension L N :=
      Garling.Chapter16.isGarlingGalois_of_splittingField hfL0 hsf_LN hfL_sep
    have hfin_LN : FiniteDimensional L N := (isGarlingGaloisExtension_iff L N).mp hgal_LN |>.1
    have hgal_LN' : IsGalois L N := (isGarlingGaloisExtension_iff L N).mp hgal_LN |>.2
    -- Embed `Γ(N : L)` into `Γ_K(f)` via `Theorem 11.9`
    obtain ⟨eMF⟩ := garlingPolyGaloisGroup_independent_of_splittingField hsf_KM hsf
    let eM_sub : GarlingPolyGaloisGroup K M f ≃* garlingPolyGaloisSubgroup K M f :=
      garlingGaloisGroupMulEquiv K M
    let ι_sub : garlingGamma (garlingNatIrrInter K L N f) →* garlingPolyGaloisSubgroup K M f :=
      Subgroup.inclusion hsub_le
    let embGal : GarlingPolyGaloisGroup L N fL →* GarlingPolyGaloisGroup K F f :=
      eMF.toMonoidHom.comp (eM_sub.symm.toMonoidHom.comp (ι_sub.comp eGamma.toMonoidHom))
    have hemb_inj : Function.Injective embGal :=
      eMF.injective.comp (eM_sub.symm.injective.comp
        ((Subgroup.inclusion_injective hsub_le).comp eGamma.injective))
    let eRange : GarlingPolyGaloisGroup L N fL ≃* embGal.range :=
      MulEquiv.ofBijective embGal.rangeRestrict
        ⟨fun a b h => hemb_inj (congrArg Subtype.val h), embGal.rangeRestrict_surjective⟩
    have hsol_LN : IsGarlingSoluble (N ≃ₐ[L] N) :=
      (isGarlingSoluble_congr eRange).mpr (theorem_17_2_i hsol embGal.range)
    have hdvd_LN : Nat.card (N ≃ₐ[L] N) ∣ d := by
      rw [Nat.card_congr eRange.toEquiv]
      exact Subgroup.card_subgroup_dvd_card embGal.range
    -- Step 3: Build radical tower `L = L_0 ≤ L_1 ≤ … ≤ L_r = N` via `Theorem 16.4`
    have hcharL : ¬ (ringChar L ∣ d) := by
      rwa [ringChar_eq_of_field_algebra K L]
    rcases hsol_LN with ⟨r, G, hG0, hGlast, hGle, hGstep⟩
    let E : Fin (r + 1) → IntermediateField L N := fun j => IntermediateField.fixedField (G j)
    have hE0 : E 0 = ⊥ := by
      dsimp only [E]
      rw [hG0]
      have h := IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField L N)
      rwa [IntermediateField.fixingSubgroup_bot] at h
    have hElast : E (Fin.last r) = ⊤ := by
      dsimp only [E]
      rw [hGlast]
      exact IntermediateField.fixedField_bot
    have hstep_rad : ∀ i : Fin r, ∃ (β : N) (m : ℕ),
        1 ≤ m ∧ β ^ m ∈ E i.castSucc ∧
        E i.succ = IntermediateField.adjoin L ((E i.castSucc : Set N) ∪ {β}) := by
      intro i
      obtain ⟨hNi, hCyci⟩ := hGstep i
      exact cyclic_fixedField_step_radical hcharL hε hdvd_LN (hGle i) hNi hCyci
    have hLN_rad : IsGarlingExtensionByRadicals L N := by
      refine ⟨r, E, fun i => Classical.choose (hstep_rad i), hE0, hElast, fun i => ?_⟩
      have hspec := Classical.choose_spec (hstep_rad i)
      obtain ⟨m, hm, hpow, hadj⟩ := hspec
      exact ⟨⟨m, hm, hpow⟩, hadj⟩
    have hKN_rad : IsGarlingExtensionByRadicals K N :=
      isGarlingExtensionByRadicals_tower K L N hKL_rad hLN_rad
    exact isGarlingSolvableByRadicals_of_extension hKN_rad (garlingSplitsOver_of_map hsf_LN.1)

/-- Companion of **Theorem 17.3** stated under Mathlib's squarefree `Polynomial.Separable`. -/
theorem theorem_17_3_mathlib_separable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {f : K[X]} (hsep : f.Separable)
    (hsf : IsGarlingSplittingFieldExtension K F f)
    (hsol : IsGarlingSoluble (GarlingPolyGaloisGroup K F f))
    (hchar : ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K F f))) :
    IsGarlingSolvableByRadicals f :=
  theorem_17_3 ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep).2.2
    hsf hsol hchar

/-- **§17.3 Post-Proof Characteristic Remark (printed p. 135 / PDF p. 143):**
*"Notice that if `f ∈ K[x]` and if either `char K = 0` or `char K > degree f`, then `f` must be
separable, by Theorem 10.6, and `char K` cannot divide `|Γ_K(f)|`, since `|Γ_K(f)|` divides
`(degree f)!`."* -/
theorem section_17_3_char_remark {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {f : K[X]} (hf0 : f ≠ 0)
    (hchar : ringChar K = 0 ∨ f.natDegree < ringChar K)
    (hsf : IsGarlingSplittingFieldExtension K F f) :
    IsGarlingSeparablePoly f ∧
    Nat.card (GarlingPolyGaloisGroup K F f) ∣ f.natDegree.factorial ∧
    ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K F f)) := by
  have hsep : IsGarlingSeparablePoly f := by
    rw [isGarlingSeparablePoly_iff]
    intro g hg hdvd
    rcases hchar with h0 | hgt
    · have : CharP K 0 := h0 ▸ ringChar.charP K
      have : CharZero K := CharP.charP_to_charZero K
      exact hg.separable
    · have hdeg_le : g.natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hdvd hf0
      have hg_lt : g.natDegree < ringChar K := lt_of_le_of_lt hdeg_le hgt
      by_contra hns
      have hns_g : ¬ IsGarlingSeparablePoly g :=
        fun h => hns ((isGarlingSeparablePoly_of_irreducible_iff hg).mp h)
      obtain ⟨p, hp_char, hp_pos, m, a, hg_sum⟩ := (theorem_10_6 hg).mp hns_g
      have hdeg_pos : 0 < g.natDegree := hg.natDegree_pos
      have hdeg_lt_p : g.natDegree < p := by omega
      have hcoeff_zero : g.coeff g.natDegree = 0 := by
        have hsum0 : (∑ i : Fin (m + 1),
            Polynomial.C (a i) * Polynomial.X ^ ((i : ℕ) * p)).coeff g.natDegree = 0 := by
          rw [Polynomial.finsetSum_coeff]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          have hne : g.natDegree ≠ (i : ℕ) * p := by
            intro heq
            have hdvd_p : p ∣ g.natDegree := ⟨i, by rw [heq, mul_comm]⟩
            have hle_p : p ≤ g.natDegree := Nat.le_of_dvd hdeg_pos hdvd_p
            omega
          simp [hne]
        rwa [← hg_sum] at hsum0
      exact hg.ne_zero (Polynomial.leadingCoeff_eq_zero.mp hcoeff_zero)
  have hgal : IsGarlingGaloisExtension K F :=
    Garling.Chapter16.isGarlingGalois_of_splittingField hf0 hsf hsep
  have : FiniteDimensional K F := (isGarlingGaloisExtension_iff K F).mp hgal |>.1
  have : IsGalois K F := (isGarlingGaloisExtension_iff K F).mp hgal |>.2
  have hdvd_fac : Nat.card (GarlingPolyGaloisGroup K F f) ∣ f.natDegree.factorial := by
    rw [IsGalois.card_aut_eq_finrank K F]
    exact (exercise_7_9_natDegree hsf).1
  have hndvd : ¬ (ringChar K ∣ Nat.card (GarlingPolyGaloisGroup K F f)) := by
    rcases hchar with h0 | hgt
    · rw [h0, zero_dvd_iff]
      exact Nat.ne_of_gt Nat.card_pos
    · have hprime : Nat.Prime (ringChar K) :=
        (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right (by omega)
      intro hdvd
      have hdvd_f : ringChar K ∣ f.natDegree.factorial := hdvd.trans hdvd_fac
      have hle := (hprime.dvd_factorial).mp hdvd_f
      omega
  exact ⟨hsep, hdvd_fac, hndvd⟩

/-! ## §17.4 Polynomials which are solvable by radicals (printed pp. 135–138, PDF pp. 143–146) -/

/-- Radical extension whose step exponents `n_1, …, n_r` satisfy `char K ∤ n_1 ⋯ n_r`
(exact hypothesis of **Theorem 17.5**, p. 137's post-proof remark, and **Theorem 17.6**). -/
def IsGarlingRadicalExtensionNotCharDvd (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ (r : ℕ) (F : Fin (r + 1) → IntermediateField K L) (β : Fin r → L) (n : Fin r → ℕ),
    F 0 = ⊥ ∧
    F (Fin.last r) = ⊤ ∧
    ¬ (ringChar K ∣ ∏ i : Fin r, n i) ∧
    ∀ i : Fin r,
      (β i) ^ (n i) ∈ F i.castSucc ∧
      F i.succ = IntermediateField.adjoin K ((F i.castSucc : Set L) ∪ {β i})

/-- Every `IsGarlingRadicalExtensionNotCharDvd K L` is an `IsGarlingExtensionByRadicals K L`
(since `char K ∤ ∏ n_i` forces `1 ≤ n_i` for every `i`). -/
theorem isGarlingExtensionByRadicals_of_notCharDvd {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (h : IsGarlingRadicalExtensionNotCharDvd K L) :
    IsGarlingExtensionByRadicals K L := by
  rcases h with ⟨r, F, β, n, h0, hlast, hchar, hstep⟩
  have hchar_i := (not_ringChar_dvd_prod_iff K n).mp hchar
  refine ⟨r, F, β, h0, hlast, fun i => ?_⟩
  have hn_pos : 1 ≤ n i :=
    (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd (hchar_i i)).1
  exact ⟨⟨n i, hn_pos, (hstep i).1⟩, (hstep i).2⟩

/-- In characteristic `0`, every `IsGarlingExtensionByRadicals K L` automatically satisfies
`IsGarlingRadicalExtensionNotCharDvd K L`. -/
theorem isGarlingRadicalExtensionNotCharDvd_of_charZero {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [CharZero K]
    (h : IsGarlingExtensionByRadicals K L) :
    IsGarlingRadicalExtensionNotCharDvd K L := by
  classical
  rcases h with ⟨r, F, β, h0, hlast, hstep⟩
  let n : Fin r → ℕ := fun i => Classical.choose (hstep i).1
  refine ⟨r, F, β, n, h0, hlast, ?_, fun i => ?_⟩
  · rw [not_ringChar_dvd_prod_iff]
    intro i
    rw [ringChar.eq_zero, zero_dvd_iff]
    have hn1 : 1 ≤ n i := (Classical.choose_spec (hstep i).1).1
    omega
  · exact ⟨(Classical.choose_spec (hstep i).1).2, (hstep i).2⟩

/-- Trivial `0`-step radical extension with `char K ∤ 1`. -/
theorem isGarlingRadicalExtensionNotCharDvd_of_bot_eq_top {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (h : (⊥ : IntermediateField K L) = ⊤) :
    IsGarlingRadicalExtensionNotCharDvd K L :=
  ⟨0, fun _ => ⊥, Fin.elim0, Fin.elim0, rfl, h, by simpa using not_ringChar_dvd_one K,
    fun i => Fin.elim0 i⟩

/-- Single-step radical extension with `char K ∤ n`. -/
theorem isGarlingRadicalExtensionNotCharDvd_single {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {β : L} {n : ℕ}
    (hchar : ¬ (ringChar K ∣ n)) (hpow : β ^ n ∈ Set.range (algebraMap K L))
    (hadj : IntermediateField.adjoin K ({β} : Set L) = ⊤) :
    IsGarlingRadicalExtensionNotCharDvd K L := by
  rcases hpow with ⟨c, hc⟩
  refine ⟨1, ![⊥, ⊤], ![β], ![n], rfl, rfl, by simpa using hchar, fun i => ?_⟩
  fin_cases i
  refine ⟨?_, ?_⟩
  · simp only [Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero]
    rw [← hc]
    exact (⊥ : IntermediateField K L).algebraMap_mem c
  · simp only [Fin.zero_eta, Fin.succ_zero_eq_one, Fin.castSucc_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← hadj]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.subset_union_right.trans (IntermediateField.subset_adjoin K _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | hx)
      · exact (bot_le : (⊥ : IntermediateField K L) ≤ _) hx
      · exact IntermediateField.subset_adjoin K ({β} : Set L) hx

/-- Tower transitivity for `IsGarlingRadicalExtensionNotCharDvd`. -/
theorem isGarlingRadicalExtensionNotCharDvd_tower (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    (hKM : IsGarlingRadicalExtensionNotCharDvd K M)
    (hML : IsGarlingRadicalExtensionNotCharDvd M L) :
    IsGarlingRadicalExtensionNotCharDvd K L := by
  rcases hKM with ⟨r₁, F₁, β₁, n₁, hF₁0, hF₁last, hchar₁, hstep₁⟩
  rcases hML with ⟨r₂, F₂, β₂, n₂, hF₂0, hF₂last, hchar₂, hstep₂⟩
  have hchar₁_i := (not_ringChar_dvd_prod_iff K n₁).mp hchar₁
  have hchar₂_i := (not_ringChar_dvd_prod_iff M n₂).mp hchar₂
  let ι : M →ₐ[K] L := IsScalarTower.toAlgHom K M L
  have hbridge : (F₁ (Fin.last r₁)).map ι = (F₂ 0).restrictScalars K := by
    rw [hF₁last, hF₂0]
    ext x
    simp only [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot,
      IntermediateField.mem_map, IntermediateField.mem_top, true_and]
    rfl
  let F : Fin (r₁ + r₂ + 1) → IntermediateField K L := fun k =>
    if hk : (k : ℕ) ≤ r₁ then
      (F₁ ⟨k, Nat.lt_succ_of_le hk⟩).map ι
    else
      (F₂ ⟨(k : ℕ) - r₁, by omega⟩).restrictScalars K
  let β : Fin (r₁ + r₂) → L := fun i =>
    if hi : (i : ℕ) < r₁ then ι (β₁ ⟨i, hi⟩) else β₂ ⟨(i : ℕ) - r₁, by omega⟩
  let n : Fin (r₁ + r₂) → ℕ := fun i =>
    if hi : (i : ℕ) < r₁ then n₁ ⟨i, hi⟩ else n₂ ⟨(i : ℕ) - r₁, by omega⟩
  have hF_low : ∀ m (hm : m ≤ r₁), F ⟨m, by omega⟩ = (F₁ ⟨m, Nat.lt_succ_of_le hm⟩).map ι :=
    fun m hm => by simp [F, hm]
  have hF_high : ∀ m (hm : m ≤ r₂),
      F ⟨r₁ + m, by omega⟩ = (F₂ ⟨m, Nat.lt_succ_of_le hm⟩).restrictScalars K := by
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.add_zero, F, le_refl, ↓reduceDIte]
      exact hbridge
    · have hnot : ¬ (r₁ + m ≤ r₁) := by omega
      simp [F, hnot]
  refine ⟨r₁ + r₂, F, β, n, ?_, ?_, ?_, fun i => ?_⟩
  · change F ⟨0, by omega⟩ = ⊥
    rw [hF_low 0 (Nat.zero_le r₁)]
    have h0' : (⟨0, Nat.lt_succ_of_le (Nat.zero_le r₁)⟩ : Fin (r₁ + 1)) = 0 := rfl
    rw [h0', hF₁0]
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_bot]
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩; exact ⟨k, IsScalarTower.algebraMap_apply K M L k⟩
    · rintro ⟨k, rfl⟩; exact ⟨algebraMap K M k, ⟨k, rfl⟩, (IsScalarTower.algebraMap_apply K M L k).symm⟩
  · have hlast_eq : Fin.last (r₁ + r₂) = ⟨r₁ + r₂, by omega⟩ := rfl
    rw [hlast_eq, hF_high r₂ (le_refl r₂)]
    have hl2 : (⟨r₂, Nat.lt_succ_of_le (le_refl r₂)⟩ : Fin (r₂ + 1)) = Fin.last r₂ := rfl
    rw [hl2, hF₂last]
    rfl
  · rw [not_ringChar_dvd_prod_iff]
    intro i
    by_cases hi : (i : ℕ) < r₁
    · simp only [n, hi, ↓reduceDIte]
      exact hchar₁_i ⟨i, hi⟩
    · simp only [n, hi, ↓reduceDIte]
      have h := hchar₂_i ⟨(i : ℕ) - r₁, by omega⟩
      rwa [ringChar_eq_of_field_algebra K M] at h
  · by_cases hi : (i : ℕ) < r₁
    · let i₁ : Fin r₁ := ⟨i, hi⟩
      have hcast : F i.castSucc = (F₁ i₁.castSucc).map ι := hF_low i (Nat.le_of_lt hi)
      have hsucc : F i.succ = (F₁ i₁.succ).map ι := hF_low (i + 1) hi
      have hβ : β i = ι (β₁ i₁) := by simp [β, hi, i₁]
      have hn : n i = n₁ i₁ := by simp [n, hi, i₁]
      rw [hcast, hsucc, hβ, hn]
      obtain ⟨hpow, hadj⟩ := hstep₁ i₁
      refine ⟨⟨(β₁ i₁) ^ (n₁ i₁), hpow, map_pow ι (β₁ i₁) (n₁ i₁)⟩, ?_⟩
      rw [hadj]
      apply le_antisymm
      · rw [IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff]
        rintro x (hx | rfl)
        · exact IntermediateField.subset_adjoin K _ (Or.inl ⟨x, hx, rfl⟩)
        · exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
      · rw [IntermediateField.adjoin_le_iff]
        rintro y (⟨x, hx, rfl⟩ | rfl)
        · exact ⟨x, IntermediateField.subset_adjoin K _ (Or.inl hx), rfl⟩
        · exact ⟨β₁ i₁, IntermediateField.subset_adjoin K _ (Or.inr rfl), rfl⟩
    · let i₂ : Fin r₂ := ⟨(i : ℕ) - r₁, by omega⟩
      have hi_eq : (i : ℕ) = r₁ + i₂ := by dsimp [i₂]; omega
      have hcast : F i.castSucc = (F₂ i₂.castSucc).restrictScalars K := by
        have hc : i.castSucc = ⟨r₁ + i₂, by omega⟩ := Fin.ext hi_eq
        rw [hc, hF_high i₂ (Nat.le_of_lt i₂.2)]; rfl
      have hsucc : F i.succ = (F₂ i₂.succ).restrictScalars K := by
        have hs : i.succ = ⟨r₁ + (i₂ + 1), by omega⟩ := Fin.ext (by simp [hi_eq, Nat.add_assoc])
        rw [hs, hF_high (i₂ + 1) i₂.2]; rfl
      have hβ : β i = β₂ i₂ := by simp [β, hi, i₂]
      have hn : n i = n₂ i₂ := by simp [n, hi, i₂]
      rw [hcast, hsucc, hβ, hn]
      obtain ⟨hpow, hadj⟩ := hstep₂ i₂
      refine ⟨hpow, ?_⟩
      rw [hadj]
      apply IntermediateField.toSubfield_injective
      change (IntermediateField.adjoin M ((F₂ i₂.castSucc : Set L) ∪ {β₂ i₂})).toSubfield =
        (IntermediateField.adjoin K
          ((((F₂ i₂.castSucc).restrictScalars K : IntermediateField K L) : Set L) ∪
            {β₂ i₂})).toSubfield
      rw [adjoin_toSubfield_eq_closure_ch17, adjoin_toSubfield_eq_closure_ch17]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_range, IntermediateField.coe_restrictScalars]
      constructor
      · rintro (⟨m, rfl⟩ | hx | hx)
        · exact Or.inr (Or.inl ((F₂ i₂.castSucc).algebraMap_mem m))
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
      · rintro (⟨k, rfl⟩ | hx | hx)
        · rw [IsScalarTower.algebraMap_apply K M L k]
          exact Or.inl ⟨algebraMap K M k, rfl⟩
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)

/-- Generic helper: adjoining a finite tuple of `n`-th roots of elements of `K` with `char K ∤ n`
produces an `IsGarlingRadicalExtensionNotCharDvd K L`. -/
private theorem isGarlingRadicalExtensionNotCharDvd_of_tuple {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {m n : ℕ} (hchar : ¬ (ringChar K ∣ n))
    (γ : Fin m → L) (hpow : ∀ i : Fin m, (γ i) ^ n ∈ Set.range (algebraMap K L))
    (hadj : IntermediateField.adjoin K (Set.range γ) = ⊤) :
    IsGarlingRadicalExtensionNotCharDvd K L := by
  let T : Fin (m + 1) → IntermediateField K L := fun j =>
    IntermediateField.adjoin K {x : L | ∃ k : Fin m, (k : ℕ) < (j : ℕ) ∧ x = γ k}
  have hT0 : T 0 = ⊥ := by
    dsimp only [T]
    have hempty : {x : L | ∃ k : Fin m, (k : ℕ) < ((0 : Fin (m + 1)) : ℕ) ∧ x = γ k} = ∅ := by
      ext x; simp
    rw [hempty]
    exact IntermediateField.adjoin_empty K L
  have hTlast : T (Fin.last m) = ⊤ := by
    dsimp only [T]
    rw [← hadj]
    congr 1
    ext x
    simp only [Fin.val_last, Set.mem_ofPred_eq, Set.mem_range]
    exact ⟨fun ⟨k, _, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, k.2, hk.symm⟩⟩
  refine ⟨m, T, γ, fun _ => n, hT0, hTlast,
    (not_ringChar_dvd_prod_iff K (fun _ : Fin m => n)).mpr fun _ => hchar, fun i => ?_⟩
  refine ⟨?_, ?_⟩
  · rcases hpow i with ⟨c, hc⟩
    rw [← hc]
    exact (T i.castSucc).algebraMap_mem c
  · apply IntermediateField.toSubfield_injective
    dsimp only [T]
    rw [adjoin_toSubfield_eq_closure_ch17, adjoin_toSubfield_eq_closure_ch17]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro x (⟨c, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
      · simp only [Fin.val_succ] at hk
        by_cases hki : (k : ℕ) = (i : ℕ)
        · have hk_eq : k = i := Fin.ext hki
          rw [hk_eq]
          exact Subfield.subset_closure (Or.inr (Or.inr rfl))
        · exact Subfield.subset_closure (Or.inr (Or.inl
            (IntermediateField.subset_adjoin K _ ⟨k, by simp only [Fin.val_castSucc]; omega, rfl⟩)))
    · rw [Subfield.closure_le]
      rintro x (⟨c, rfl⟩ | hxT | rfl)
      · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
      · have hmono : T i.castSucc ≤ T i.succ := IntermediateField.adjoin.mono K _ _
          (fun y ⟨k, hk, hy⟩ => ⟨k, by simp only [Fin.val_castSucc, Fin.val_succ] at hk ⊢; omega, hy⟩)
        have hx' := hmono hxT
        rw [← IntermediateField.mem_toSubfield, adjoin_toSubfield_eq_closure_ch17] at hx'
        exact hx'
      · exact Subfield.subset_closure (Or.inr ⟨i, by simp, rfl⟩)

/-- Strengthened **Theorem 17.4** preserving the characteristic condition on `N : M`
(used directly in `Theorem 17.5` and p. 137's characteristic-preservation remark). -/
theorem theorem_17_4_with_char {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hgal : IsGarlingGaloisExtension K L)
    {β : M} {n : ℕ} {θ : L}
    (hadj : IntermediateField.adjoin L ({β} : Set M) = ⊤)
    (hroot : Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C θ) = 0)
    (hchar : ¬ (ringChar K ∣ n)) :
    ∃ (N : Type w) (_ : Field N) (_ : Algebra M N) (_ : Algebra K N) (_ : IsScalarTower K M N),
      IsGarlingRadicalExtensionNotCharDvd M N ∧ IsGarlingGaloisExtension K N := by
  classical
  obtain ⟨hn_pos, _⟩ := Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar
  have hβ_pow : β ^ n = algebraMap L M θ := by
    have h := hroot
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h
    exact h
  have hfinKL : FiniteDimensional K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.1
  have hgalKL : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
  -- Case 1: `θ = 0` (`β = 0`, so `M = L`, take `N = M`)
  by_cases hθ : θ = 0
  · subst hθ
    rw [map_zero] at hβ_pow
    have hβ0 : β = 0 := eq_zero_of_pow_eq_zero hβ_pow
    have hbot_top : (⊥ : IntermediateField L M) = ⊤ := by
      rw [← hadj, hβ0]
      apply le_antisymm bot_le
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact (⊥ : IntermediateField L M).zero_mem
    have hbij : Function.Bijective (IsScalarTower.toAlgHom K L M) := by
      refine ⟨(algebraMap L M).injective, fun y => ?_⟩
      have hy : y ∈ (⊥ : IntermediateField L M) := hbot_top.symm ▸ IntermediateField.mem_top
      exact hy
    let eLM : L ≃ₐ[K] M := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M) hbij
    exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
      isGarlingRadicalExtensionNotCharDvd_of_bot_eq_top (Subsingleton.elim _ _),
      isGarlingGaloisExtension_congr eLM hgal⟩
  -- Case 2: `θ ≠ 0` (Garling's symmetrization proof, pp. 135–136)
  · have hcharL : ¬ (ringChar L ∣ n) := by rwa [ringChar_eq_of_field_algebra K L]
    have hcharM : ¬ (ringChar M ∣ n) := by rwa [ringChar_eq_of_field_algebra K M]
    -- Step 1: Adjoin a primitive `n`th root of unity `ε` to `M` via splitting field `Mε` of `X^n - 1`
    let Mε := Polynomial.SplittingField (Polynomial.X ^ n - 1 : M[X])
    have hsf_Mε : IsGarlingSplittingFieldExtension M Mε (Polynomial.X ^ n - 1) :=
      (isGarlingSplittingFieldExtension_iff M Mε _).mpr inferInstance
    have hsf_Mε1 : IsGarlingSplittingFieldExtension M Mε (Polynomial.X ^ n - Polynomial.C 1) := by
      simpa using hsf_Mε
    obtain ⟨_, ⟨ε, hε⟩, _⟩ :=
      Garling.Chapter16.theorem_16_1 (one_ne_zero : (1 : M) ≠ 0) hcharM hsf_Mε1
    have hsf_cyc_Mε : IsGarlingSplittingFieldExtension M Mε (Polynomial.cyclotomic n M) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharM).1.mpr hsf_Mε
    have hε_garl : Garling.Chapter15.IsGarlingPrimitiveRoot n ε :=
      (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hn_pos ε).mpr hε
    have hMε_adj : IntermediateField.adjoin M ({ε} : Set Mε) = ⊤ :=
      ((Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharM).2
        hsf_cyc_Mε hε_garl).1
    have hM_Mε_rad : IsGarlingRadicalExtensionNotCharDvd M Mε :=
      isGarlingRadicalExtensionNotCharDvd_single hcharM ⟨1, by simp [hε.pow_eq_one]⟩ hMε_adj
    -- Step 2: Construct `fL = ∏_{σ ∈ Γ(L:K)} (X^n - σ(θ))` and descend to `f ∈ K[X]`
    let G := L ≃ₐ[K] L
    let fL : L[X] := ∏ σ : G, (Polynomial.X ^ n - Polynomial.C (σ θ))
    have hfL_monic : fL.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_pow_sub_C (σ θ) (by omega)
    have hfL_fixed : ∀ τ : G, fL.map τ.toRingHom = fL := by
      intro τ
      dsimp only [fL]
      rw [Polynomial.map_prod]
      have hstep : ∀ σ : G, (Polynomial.X ^ n - Polynomial.C (σ θ)).map τ.toRingHom =
          Polynomial.X ^ n - Polynomial.C ((τ * σ) θ) := by
        intro σ
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
        rfl
      simp_rw [hstep]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
    have hcoeff_mem : ∀ k : ℕ, ∃ c : K, algebraMap K L c = fL.coeff k := by
      intro k
      apply Garling.Chapter16.mem_range_algebraMap_of_forall_gal_fix
      intro τ
      have h := congrArg (fun p : L[X] => p.coeff k) (hfL_fixed τ)
      simpa [Polynomial.coeff_map] using h
    let f : K[X] :=
      ∑ k ∈ Finset.range (fL.natDegree + 1),
        Polynomial.C (Classical.choose (hcoeff_mem k)) * Polynomial.X ^ k
    have hf_map : f.map (algebraMap K L) = fL := by
      ext k
      rw [Polynomial.coeff_map]
      by_cases hk : k < fL.natDegree + 1
      · simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        rw [Finset.sum_eq_single k]
        · simp only [↓reduceIte, mul_one]
          exact Classical.choose_spec (hcoeff_mem k)
        · intro b _ hbk; simp [hbk.symm]
        · intro hnot; exact (hnot (Finset.mem_range.mpr hk)).elim
      · have hgt : fL.natDegree < k := by omega
        have hzeroL : fL.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
        have hzeroK : f.coeff k = 0 := by
          simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          refine Finset.sum_eq_zero fun b hb => ?_
          have hbk : k ≠ b := by
            have := Finset.mem_range.mp hb; omega
          simp [hbk]
        rw [hzeroK, map_zero, hzeroL]
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hf_map
      exact hfL_monic.ne_zero hf_map.symm
    -- Step 3: Splitting field `N : Mε` of `f` over `Mε`
    have : IsScalarTower K L Mε := IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K M Mε, IsScalarTower.algebraMap_apply K L M,
        ← IsScalarTower.algebraMap_apply L M Mε]
    let fMε : Mε[X] := f.map (algebraMap K Mε)
    have hfMε_eq : fMε = ∏ σ : G, (Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ))) := by
      dsimp only [fMε]
      rw [IsScalarTower.algebraMap_eq K L Mε, ← Polynomial.map_map, hf_map]
      dsimp only [fL]
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun σ _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    let N := Polynomial.SplittingField fMε
    have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K Mε N, IsScalarTower.algebraMap_apply K L Mε,
        ← IsScalarTower.algebraMap_apply L Mε N]
    have : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq fun l => by
      rw [IsScalarTower.algebraMap_apply L Mε N, IsScalarTower.algebraMap_apply L M Mε,
        ← IsScalarTower.algebraMap_apply M Mε N]
    have : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K Mε N, IsScalarTower.algebraMap_apply K M Mε,
        ← IsScalarTower.algebraMap_apply M Mε N]
    -- Step 4: Extract one root `γ σ ∈ N` for each `X^n - σ(θ)` and show `N : Mε` is radical
    have hsf_MεN : Polynomial.IsSplittingField Mε N fMε := inferInstance
    have hfMε_splits : (fMε.map (algebraMap Mε N)).Splits := hsf_MεN.splits
    have hroot_ex : ∀ σ : G, ∃ γ : N, γ ^ n = algebraMap L N (σ θ) := by
      intro σ
      have hdvd : (Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ))) ∣ fMε := by
        rw [hfMε_eq]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ σ)
      have hspl_σ : ((Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ))).map
          (algebraMap Mε N)).Splits :=
        Polynomial.Splits.of_dvd hfMε_splits (by
          rw [Polynomial.map_ne_zero_iff (algebraMap Mε N).injective]
          exact (Polynomial.map_ne_zero_iff (algebraMap K Mε).injective).mpr hf0)
          (Polynomial.map_dvd _ hdvd)
      have hdeg_pos : ((Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ))).map
          (algebraMap Mε N)).degree ≠ 0 := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
          Polynomial.degree_X_pow_sub_C (by omega)]
        intro h0
        have hn0 : (n : ℕ) = 0 := WithBot.coe_inj.mp h0
        omega
      obtain ⟨γ, hγ⟩ := hspl_σ.exists_eval_eq_zero hdeg_pos
      refine ⟨γ, ?_⟩
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hγ
      exact hγ
    let γ : G → N := fun σ => Classical.choose (hroot_ex σ)
    have hγ_pow : ∀ σ : G, (γ σ) ^ n = algebraMap L N (σ θ) :=
      fun σ => Classical.choose_spec (hroot_ex σ)
    have hεN : IsPrimitiveRoot (algebraMap Mε N ε) n :=
      hε.map_of_injective (algebraMap Mε N).injective
    have hfac_σ : ∀ σ : G,
        Polynomial.X ^ n - Polynomial.C (algebraMap L N (σ θ)) =
          ∏ k : Fin n, (Polynomial.X - Polynomial.C ((algebraMap Mε N ε) ^ (k : ℕ) * γ σ)) := by
      intro σ
      rw [← hγ_pow σ]
      exact Garling.Chapter16.X_pow_sub_C_pow_eq_prod hn_pos hεN (γ σ)
    have hMεN_adjoin_γ : IntermediateField.adjoin Mε (Set.range γ) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Algebra.adjoin Mε (fMε.rootSet N) := by
        rw [hsf_MεN.adjoin_rootSet]; exact Algebra.mem_top
      have hle_alg : Algebra.adjoin Mε (fMε.rootSet N) ≤
          (IntermediateField.adjoin Mε (Set.range γ)).toSubalgebra := by
        rw [Algebra.adjoin_le_iff]
        intro y hy
        rw [Polynomial.mem_rootSet] at hy
        have hprod0 : (∏ σ : G, (Polynomial.X ^ n - Polynomial.C (algebraMap L N (σ θ)))).eval y = 0 := by
          have h1 := hy.2
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h1
          have hm : fMε.map (algebraMap Mε N) =
              ∏ σ : G, (Polynomial.X ^ n - Polynomial.C (algebraMap L N (σ θ))) := by
            rw [congrArg (Polynomial.map (algebraMap Mε N)) hfMε_eq, Polynomial.map_prod]
            refine Finset.prod_congr rfl fun σ _ => ?_
            rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
            rfl
          rwa [hm] at h1
        rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hprod0
        obtain ⟨σ, _, hσ0⟩ := hprod0
        rw [hfac_σ σ, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hσ0
        obtain ⟨k, _, hk0⟩ := hσ0
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk0
        rw [hk0]
        change (algebraMap Mε N ε) ^ (k : ℕ) * γ σ ∈ IntermediateField.adjoin Mε (Set.range γ)
        exact mul_mem
          (pow_mem ((IntermediateField.adjoin Mε (Set.range γ)).algebraMap_mem ε) (k : ℕ))
          (IntermediateField.subset_adjoin Mε (Set.range γ) ⟨σ, rfl⟩)
      exact hle_alg hx
    -- Build radical tower from `Mε` to `N` with all exponents equal to `n`
    let m := Fintype.card G
    let eG : Fin m ≃ G := (Fintype.equivFin G).symm
    have hcharMε : ¬ (ringChar Mε ∣ n) := by rwa [ringChar_eq_of_field_algebra K Mε]
    have hMεN_rad : IsGarlingRadicalExtensionNotCharDvd Mε N :=
      isGarlingRadicalExtensionNotCharDvd_of_tuple hcharMε (fun i => γ (eG i))
        (fun i => ⟨algebraMap L Mε ((eG i) θ), (hγ_pow (eG i)).symm⟩)
        (by
          rw [← hMεN_adjoin_γ]
          congr 1
          ext y
          simp only [Set.mem_range]
          exact ⟨fun ⟨i, hi⟩ => ⟨eG i, hi⟩, fun ⟨σ, hσ⟩ => ⟨eG.symm σ, by simpa using hσ⟩⟩)
    have hMN_rad : IsGarlingRadicalExtensionNotCharDvd M N :=
      isGarlingRadicalExtensionNotCharDvd_tower M Mε N hM_Mε_rad hMεN_rad
    -- Step 5: Show `N : K` is a Garling Galois extension (finite + normal + separable)
    -- 5a. Finite dimensional
    have hfin_LM : FiniteDimensional L M := by
      have hrad_LM : IsGarlingRadicalOver L β := ⟨n, hn_pos, θ, hβ_pow.symm⟩
      have hint_β : IsIntegral L β :=
        (isGarlingAlgebraic_iff_isIntegral L β).mp (isGarlingAlgebraic_of_isGarlingRadicalOver hrad_LM)
      have hfin_adj : FiniteDimensional L (IntermediateField.adjoin L ({β} : Set M)) :=
        IntermediateField.adjoin.finiteDimensional hint_β
      rw [hadj] at hfin_adj
      exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv
    have hfin_MMε : FiniteDimensional M Mε :=
      Polynomial.IsSplittingField.finiteDimensional Mε (Polynomial.X ^ n - 1)
    have hfin_MεN : FiniteDimensional Mε N :=
      Polynomial.IsSplittingField.finiteDimensional N fMε
    have hfin_KM : FiniteDimensional K M := FiniteDimensional.trans K L M
    have hfin_KMε : FiniteDimensional K Mε := FiniteDimensional.trans K M Mε
    have hfin_KN : FiniteDimensional K N := FiniteDimensional.trans K Mε N
    -- 5b. Normal (`N : K` is a splitting field of `f * g'`, where `g' = ∏ i, minpoly K (b i)`)
    let bL := Module.finBasis K L
    let g' : K[X] := ∏ i, minpoly K (bL i)
    have hg'_mon : g'.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ =>
        minpoly.monic (Algebra.IsIntegral.isIntegral (bL i))
    have hg'0 : g' ≠ 0 := hg'_mon.ne_zero
    let fg : K[X] := f * g'
    have hfg0 : fg ≠ 0 := mul_ne_zero hf0 hg'0
    have hfg_splits : (fg.map (algebraMap K N)).Splits := by
      rw [Polynomial.map_mul]
      refine Polynomial.Splits.mul ?_ ?_
      · have hm : f.map (algebraMap K N) = fMε.map (algebraMap Mε N) := by
          dsimp only [fMε]
          rw [Polynomial.map_map, IsScalarTower.algebraMap_eq K Mε N]
        rw [hm]
        exact hfMε_splits
      · have hm : g'.map (algebraMap K N) = (g'.map (algebraMap K L)).map (algebraMap L N) := by
          rw [Polynomial.map_map, IsScalarTower.algebraMap_eq K L N]
        rw [hm]
        have hsp_g' : (g'.map (algebraMap K L)).Splits := by
          rw [Polynomial.map_prod]
          exact Polynomial.Splits.prod fun i _ => Normal.splits hgalKL.to_normal (bL i)
        exact Polynomial.Splits.map hsp_g' (algebraMap L N)
    have hfg_adjoin_if : IntermediateField.adjoin K (fg.rootSet N) = ⊤ := by
      let S : IntermediateField K N := IntermediateField.adjoin K (fg.rootSet N)
      have hroot_f : ∀ x : N, Polynomial.aeval x f = 0 → x ∈ S := fun x hx =>
        IntermediateField.subset_adjoin K (fg.rootSet N)
          (Polynomial.mem_rootSet.mpr ⟨hfg0, by rw [map_mul, hx, zero_mul]⟩)
      have hroot_g' : ∀ x : N, Polynomial.aeval x g' = 0 → x ∈ S := fun x hx =>
        IntermediateField.subset_adjoin K (fg.rootSet N)
          (Polynomial.mem_rootSet.mpr ⟨hfg0, by rw [map_mul, hx, mul_zero]⟩)
      -- (1) `L ≤ S`
      have hbi_S : ∀ i, algebraMap L N (bL i) ∈ S := by
        intro i
        apply hroot_g'
        have hgi : Polynomial.aeval (bL i) g' = 0 := by
          rw [map_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (bL i))
        have h1 := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K L N) (bL i) g'
        rw [hgi, map_zero] at h1
        exact h1
      have hL_le_S : ∀ l : L, algebraMap L N l ∈ S := by
        intro l
        have hl := (bL.sum_repr l).symm
        rw [hl, map_sum]
        refine S.sum_mem fun i _ => ?_
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K L N]
        exact S.mul_mem (S.algebraMap_mem _) (hbi_S i)
      -- (2) `β_N ∈ S`, hence `M ≤ S`
      have haeval_f_of_pow : ∀ (x : N) (σ : G), x ^ n = algebraMap L N (σ θ) →
          Polynomial.aeval x f = 0 := by
        intro x σ hx
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        have hm : f.map (algebraMap K N) =
            ∏ τ : G, (Polynomial.X ^ n - Polynomial.C (algebraMap L N (τ θ))) := by
          rw [IsScalarTower.algebraMap_eq K L N, ← Polynomial.map_map, hf_map]
          dsimp only [fL]
          rw [Polynomial.map_prod]
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
        rw [hm, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ σ) (by simp [hx])
      have hβN_mem : algebraMap M N β ∈ S := by
        apply hroot_f
        apply haeval_f_of_pow _ (1 : G)
        rw [← map_pow, hβ_pow]
        rfl
      have hM_le_S : ∀ x : M, algebraMap M N x ∈ S := by
        intro x
        have hx : x ∈ IntermediateField.adjoin L ({β} : Set M) := by
          rw [hadj]; exact IntermediateField.mem_top
        have hsub : (IntermediateField.adjoin L ({β} : Set M)).toSubfield.map (algebraMap M N) ≤
            S.toSubfield := by
          rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro y (⟨l, rfl⟩ | hyβ)
          · exact hL_le_S l
          · rw [Set.mem_singleton_iff] at hyβ; rw [hyβ]; exact hβN_mem
        exact hsub ⟨x, hx, rfl⟩
      -- (3) `ε_N ∈ S`, hence `Mε ≤ S`
      have hεN_mem : algebraMap Mε N ε ∈ S := by
        have hβN_ne0 : algebraMap M N β ≠ 0 := by
          intro h0
          have hp0 : (algebraMap M N β) ^ n = 0 := by rw [h0, zero_pow (by omega)]
          rw [← map_pow, hβ_pow, ← IsScalarTower.algebraMap_apply L M N] at hp0
          exact hθ ((algebraMap L N).injective (hp0.trans (map_zero _).symm))
        have hεβ_mem : algebraMap Mε N ε * algebraMap M N β ∈ S := by
          apply hroot_f
          apply haeval_f_of_pow _ (1 : G)
          rw [mul_pow, hεN.pow_eq_one, one_mul, ← map_pow, hβ_pow]
          rfl
        have hε_eq : algebraMap Mε N ε =
            (algebraMap Mε N ε * algebraMap M N β) * (algebraMap M N β)⁻¹ := by
          rw [mul_inv_cancel_right₀ hβN_ne0]
        rw [hε_eq]
        exact S.mul_mem hεβ_mem (S.inv_mem hβN_mem)
      have hMε_le_S : ∀ x : Mε, algebraMap Mε N x ∈ S := by
        intro x
        have hx : x ∈ IntermediateField.adjoin M ({ε} : Set Mε) := by
          rw [hMε_adj]; exact IntermediateField.mem_top
        have hsub : (IntermediateField.adjoin M ({ε} : Set Mε)).toSubfield.map (algebraMap Mε N) ≤
            S.toSubfield := by
          rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro y (⟨m0, rfl⟩ | hyε)
          · exact hM_le_S m0
          · rw [Set.mem_singleton_iff] at hyε; rw [hyε]; exact hεN_mem
        exact hsub ⟨x, hx, rfl⟩
      -- (4) Every `γ σ ∈ S`, hence `N = Mε(range γ) ≤ S`, so `S = ⊤`
      have hγ_mem : ∀ σ : G, γ σ ∈ S := fun σ => hroot_f (γ σ) (haeval_f_of_pow (γ σ) σ (hγ_pow σ))
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin Mε (Set.range γ) := by
        rw [hMεN_adjoin_γ]; exact IntermediateField.mem_top
      have hsub : (IntermediateField.adjoin Mε (Set.range γ)).toSubfield ≤ S.toSubfield := by
        rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
        rintro y (⟨c, rfl⟩ | ⟨σ, rfl⟩)
        · exact hMε_le_S c
        · exact hγ_mem σ
      exact hsub hx
    have hfg_adjoin : Algebra.adjoin K (fg.rootSet N) = ⊤ := by
      have halg : ∀ x ∈ fg.rootSet N, IsAlgebraic K x := fun x hx =>
        ⟨fg, hfg0, (Polynomial.mem_rootSet.mp hx).2⟩
      have hsub := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
      rw [hfg_adjoin_if] at hsub
      exact hsub.symm
    have hsp_fg : Polynomial.IsSplittingField K N fg :=
      ⟨hfg_splits, hfg_adjoin⟩
    have hnorm_KN : Normal K N := Normal.of_isSplittingField fg
    -- 5c. Separable (`K → L → M → Mε → N`)
    have hsep_KL : Algebra.IsSeparable K L := hgalKL.to_isSeparable
    have hsep_LM : Algebra.IsSeparable L M := by
      have hpoly_sep : (Polynomial.X ^ n - Polynomial.C θ : L[X]).Separable :=
        (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero hθ hcharL).2.2.2.1
      have hβ_sep : IsSeparable L β := hpoly_sep.of_dvd (minpoly.dvd L β hroot)
      have h_adj : Algebra.IsSeparable L (IntermediateField.adjoin L ({β} : Set M)) :=
        (IntermediateField.isSeparable_adjoin_iff_isSeparable L M).mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx; exact hβ_sep
      let e : IntermediateField.adjoin L ({β} : Set M) ≃ₐ[L] M :=
        (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
      exact AlgEquiv.Algebra.isSeparable e
    have hsep_MMε : Algebra.IsSeparable M Mε := by
      have hpoly_sep : (Polynomial.X ^ n - Polynomial.C (1 : M) : M[X]).Separable :=
        (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero one_ne_zero hcharM).2.2.2.1
      have hε_root : Polynomial.aeval ε (Polynomial.X ^ n - Polynomial.C (1 : M)) = 0 := by
        simp [hε.pow_eq_one]
      have hε_sep : IsSeparable M ε := hpoly_sep.of_dvd (minpoly.dvd M ε hε_root)
      have h_adj : Algebra.IsSeparable M (IntermediateField.adjoin M ({ε} : Set Mε)) :=
        (IntermediateField.isSeparable_adjoin_iff_isSeparable M Mε).mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx; exact hε_sep
      let e : IntermediateField.adjoin M ({ε} : Set Mε) ≃ₐ[M] Mε :=
        (IntermediateField.equivOfEq hMε_adj).trans IntermediateField.topEquiv
      exact AlgEquiv.Algebra.isSeparable e
    have hsep_MεN : Algebra.IsSeparable Mε N := by
      have h_adj : Algebra.IsSeparable Mε (IntermediateField.adjoin Mε (Set.range γ)) := by
        refine (IntermediateField.isSeparable_adjoin_iff_isSeparable Mε N).mpr ?_
        rintro _ ⟨σ, rfl⟩
        have hστ_ne0 : algebraMap L Mε (σ θ) ≠ 0 := by
          intro h0
          exact hθ (σ.injective ((algebraMap L Mε).injective (h0.trans (map_zero _).symm) |>.trans
            (map_zero σ).symm))
        have hpoly_sep : (Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ)) : Mε[X]).Separable :=
          (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero hστ_ne0 hcharMε).2.2.2.1
        have hγ_root : Polynomial.aeval (γ σ)
            (Polynomial.X ^ n - Polynomial.C (algebraMap L Mε (σ θ))) = 0 := by
          rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hγ_pow σ, sub_eq_zero]
          rfl
        exact hpoly_sep.of_dvd (minpoly.dvd Mε (γ σ) hγ_root)
      let e : IntermediateField.adjoin Mε (Set.range γ) ≃ₐ[Mε] N :=
        (IntermediateField.equivOfEq hMεN_adjoin_γ).trans IntermediateField.topEquiv
      exact AlgEquiv.Algebra.isSeparable e
    have hsep_KM : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    have hsep_KMε : Algebra.IsSeparable K Mε := Algebra.IsSeparable.trans K M Mε
    have hsep_KN : Algebra.IsSeparable K N := Algebra.IsSeparable.trans K Mε N
    have hgal_KN : IsGarlingGaloisExtension K N :=
      (isGarlingGaloisExtension_iff K N).mpr ⟨hfin_KN, ⟨⟩⟩
    exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, hMN_rad, hgal_KN⟩

/-- **Theorem 17.4 (literal, printed pp. 135–136 / PDF pp. 143–144):**
*"Suppose that `L : K` is a Galois extension, that `M = L(β)`, where `β` is a root of `x^n - θ`
(with `θ` in `L`) and that `char K` does not divide `n`. Then there exists an extension by radicals
`N : M` such that `N : K` is a Galois extension."* -/
theorem theorem_17_4 {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hgal : IsGarlingGaloisExtension K L)
    {β : M} {n : ℕ} {θ : L}
    (hadj : IntermediateField.adjoin L ({β} : Set M) = ⊤)
    (hroot : Polynomial.aeval β (Polynomial.X ^ n - Polynomial.C θ) = 0)
    (hchar : ¬ (ringChar K ∣ n)) :
    ∃ (N : Type w) (_ : Field N) (_ : Algebra M N) (_ : Algebra K N) (_ : IsScalarTower K M N),
      IsGarlingExtensionByRadicals M N ∧ IsGarlingGaloisExtension K N := by
  obtain ⟨N, fN, aMN, aKN, hT, hrad, hgalN⟩ := theorem_17_4_with_char hgal hadj hroot hchar
  exact ⟨N, fN, aMN, aKN, hT, isGarlingExtensionByRadicals_of_notCharDvd hrad, hgalN⟩

/-- Helper for `Theorem 17.5`: given `L = L'(β)` with `β^n = θ ∈ L'` (`n ≥ 1`) and a `K`-extension
`Mprev : L'`, construct an abstract simple radical extension `E = Mprev(γ)` (`γ^n = θ`) together
with a `K`-embedding `emb : L →ₐ[K] E`. Keeping `E` existentially abstracted isolates `AdjoinRoot`
from the induction in `theorem_17_5_with_char`. -/
private theorem exists_simple_radical_extension_embedding
    {K : Type u} {L : Type v} {Mprev : Type v}
    [Field K] [Field L] [Field Mprev] [Algebra K L] [Algebra K Mprev]
    (L' : IntermediateField K L) [Algebra L' Mprev] [IsScalarTower K L' Mprev]
    {β : L} {n : ℕ} {θ : L'} (hn : 1 ≤ n) (hpow : β ^ n = (θ : L))
    (hadj : IntermediateField.adjoin L' ({β} : Set L) = ⊤) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra Mprev E) (_ : Algebra K E)
      (_ : IsScalarTower K Mprev E) (γ : E) (_ : L →ₐ[K] E),
      IntermediateField.adjoin Mprev ({γ} : Set E) = ⊤ ∧
      Polynomial.aeval γ (Polynomial.X ^ n - Polynomial.C (algebraMap L' Mprev θ)) = 0 := by
  classical
  have hint_β : IsIntegral L' β :=
    (isGarlingAlgebraic_iff_isIntegral L' β).mp
      (isGarlingAlgebraic_of_isGarlingRadicalOver ⟨n, hn, θ, hpow.symm⟩)
  let mr : L'[X] := minpoly L' β
  have hmr_monic : mr.Monic := minpoly.monic hint_β
  have hmr_deg : 1 ≤ mr.natDegree := minpoly.natDegree_pos hint_β
  let mrM : Mprev[X] := mr.map (algebraMap L' Mprev)
  have hmrM_monic : mrM.Monic := hmr_monic.map (algebraMap L' Mprev)
  have hmrM_nu : ¬ IsUnit mrM := by
    intro hu
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap L' Mprev).injective] at hd
    omega
  obtain ⟨nr, hnr_irr, hnr_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hmrM_nu hmrM_monic.ne_zero
  have : Fact (Irreducible nr) := ⟨hnr_irr⟩
  let E := AdjoinRoot nr
  have : IsScalarTower K L' E := IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply K Mprev E, IsScalarTower.algebraMap_apply K L' Mprev,
      ← IsScalarTower.algebraMap_apply L' Mprev E]
  let γ : E := AdjoinRoot.root nr
  have hγ_mr : Polynomial.aeval γ mr = 0 := by
    have h1 : Polynomial.aeval γ mrM = 0 := by
      obtain ⟨q, hq⟩ := hnr_dvd
      rw [hq, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    simpa [mrM, Polynomial.aeval_map_algebraMap] using h1
  let pb := IntermediateField.adjoin.powerBasis hint_β
  let embAdj : IntermediateField.adjoin L' ({β} : Set L) →ₐ[L'] E :=
    pb.lift γ (by
      have hmp : minpoly L' pb.gen = mr := by
        have h1 := minpoly.algHom_eq
          (IntermediateField.adjoin L' ({β} : Set L)).val Subtype.val_injective pb.gen
        simpa [mr, pb, IntermediateField.adjoin.powerBasis_gen] using h1.symm
      rw [hmp]
      exact hγ_mr)
  let eL_adj : L ≃ₐ[L'] IntermediateField.adjoin L' ({β} : Set L) :=
    IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hadj.symm)
  let embL' : L →ₐ[L'] E := embAdj.comp eL_adj.toAlgHom
  have hemb_β : embL' β = γ := by
    change embAdj ⟨β, _⟩ = γ
    rw [show (⟨β, _⟩ : IntermediateField.adjoin L' ({β} : Set L)) = pb.gen from rfl]
    exact pb.lift_gen γ _
  have hγ_root : Polynomial.aeval γ
      (Polynomial.X ^ n - Polynomial.C (algebraMap L' Mprev θ)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero]
    rw [← hemb_β, ← map_pow]
    have hpow_eq : β ^ n = algebraMap L' L θ := hpow
    rw [hpow_eq, embL'.commutes]
    exact IsScalarTower.algebraMap_apply L' Mprev E θ
  have hE_adj : IntermediateField.adjoin Mprev ({γ} : Set E) = ⊤ := by
    have hall : ∀ x : E, x ∈ IntermediateField.adjoin Mprev ({γ} : Set E) := by
      intro x
      induction x using AdjoinRoot.induction_on with
      | ih p =>
        rw [← AdjoinRoot.aeval_eq]
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
          rw [map_add]
          exact add_mem hp hq
        | monomial k a =>
          rw [Polynomial.aeval_monomial]
          exact mul_mem (IntermediateField.algebraMap_mem _ a)
            (pow_mem (IntermediateField.subset_adjoin Mprev _ (Set.mem_singleton γ)) k)
    exact eq_top_iff.mpr fun x _ => hall x
  let embK : L →ₐ[K] E := embL'.restrictScalars K
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, γ, embK, hE_adj, hγ_root⟩

/-- Helper for `Theorem 17.5`: slice a length-`(s + 1)` radical tower into its length-`s` prefix
inside `L' = F (Fin.last s).castSucc` plus the final simple radical step `L = L'(β_last)`. -/
private theorem radical_tower_prefix {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {s : ℕ} {F : Fin (s + 1 + 1) → IntermediateField K L} {β : Fin (s + 1) → L}
    {n : Fin (s + 1) → ℕ}
    (h0 : F 0 = ⊥) (hlast : F (Fin.last (s + 1)) = ⊤)
    (hchar : ¬ (ringChar K ∣ ∏ i : Fin (s + 1), n i))
    (hstep : ∀ i : Fin (s + 1),
      (β i) ^ (n i) ∈ F i.castSucc ∧
      F i.succ = IntermediateField.adjoin K ((F i.castSucc : Set L) ∪ {β i})) :
    let L' : IntermediateField K L := F (Fin.last s).castSucc
    let β_last : L := β (Fin.last s)
    let n_last : ℕ := n (Fin.last s)
    (∃ (F' : Fin (s + 1) → IntermediateField K L') (β' : Fin s → L') (n' : Fin s → ℕ),
      F' 0 = ⊥ ∧ F' (Fin.last s) = ⊤ ∧ ¬ (ringChar K ∣ ∏ i : Fin s, n' i) ∧
      ∀ i : Fin s,
        (β' i) ^ (n' i) ∈ F' i.castSucc ∧
        F' i.succ = IntermediateField.adjoin K ((F' i.castSucc : Set L') ∪ {β' i})) ∧
    ¬ (ringChar K ∣ n_last) ∧
    β_last ^ n_last ∈ L' ∧
    IntermediateField.adjoin L' ({β_last} : Set L) = ⊤ := by
  classical
  have hchar_i := (not_ringChar_dvd_prod_iff K n).mp hchar
  let L' : IntermediateField K L := F (Fin.last s).castSucc
  have hle_L' : ∀ j : Fin (s + 1), F j.castSucc ≤ L' := by
    intro ⟨k, hk⟩
    have hmono : ∀ a b : ℕ, (ha : a ≤ b) → (hb : b < s + 2) →
        F ⟨a, by omega⟩ ≤ F ⟨b, hb⟩ := by
      intro a b hab hb
      induction b with
      | zero =>
        have ha0 : a = 0 := by omega
        subst ha0; exact le_refl _
      | succ m ihm =>
        by_cases ham : a ≤ m
        · exact (ihm ham (by omega)).trans (by
            have hs := (hstep ⟨m, by omega⟩).2
            intro x hx
            change x ∈ F (⟨m, by omega⟩ : Fin (s + 1)).succ
            rw [hs]
            exact IntermediateField.subset_adjoin K _ (Or.inl hx))
        · have ha_eq : a = m + 1 := by omega
          subst ha_eq; exact le_refl _
    exact hmono k s (by omega) (by omega)
  let F' : Fin (s + 1) → IntermediateField K L' := fun j =>
    { (F j.castSucc).toSubfield.comap L'.val.toRingHom with
      algebraMap_mem' := fun k => (F j.castSucc).algebraMap_mem k }
  let β' : Fin s → L' := fun i =>
    ⟨β i.castSucc, hle_L' i.succ (by
      rw [← Fin.succ_castSucc, (hstep i.castSucc).2]
      exact IntermediateField.subset_adjoin K _ (Or.inr rfl))⟩
  let n' : Fin s → ℕ := fun i => n i.castSucc
  have hF'0 : F' 0 = ⊥ := by
    ext ⟨x, hx⟩
    change x ∈ F 0 ↔ (⟨x, hx⟩ : L') ∈ (⊥ : IntermediateField K L')
    rw [h0]
    simp only [IntermediateField.mem_bot]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩; exact ⟨k, congrArg Subtype.val hk⟩
  have hF'last : F' (Fin.last s) = ⊤ := by
    ext ⟨x, hx⟩
    simp [F', L', hx]
  have hchar' : ¬ (ringChar K ∣ ∏ i : Fin s, n' i) :=
    (not_ringChar_dvd_prod_iff K n').mpr fun i => hchar_i i.castSucc
  have hstep' : ∀ i : Fin s,
      (β' i) ^ (n' i) ∈ F' i.castSucc ∧
      F' i.succ = IntermediateField.adjoin K ((F' i.castSucc : Set L') ∪ {β' i}) := by
    intro i
    refine ⟨?_, ?_⟩
    · have hcoe : (((β' i) ^ (n' i) : L') : L) = (β i.castSucc) ^ (n i.castSucc) :=
        map_pow L'.val (β' i) (n' i)
      change (((β' i) ^ (n' i) : L') : L) ∈ F i.castSucc.castSucc
      rw [hcoe]
      exact (hstep i.castSucc).1
    · apply IntermediateField.toSubfield_injective
      rw [adjoin_toSubfield_eq_closure_ch17]
      apply le_antisymm
      · intro x hx
        have hxL : (x : L) ∈ F i.castSucc.succ := hx
        rw [(hstep i.castSucc).2] at hxL
        let S_L : Subfield L :=
          (Subfield.closure (Set.range (algebraMap K L') ∪
            ((F' i.castSucc : Set L') ∪ {β' i}))).map L'.val.toRingHom
        have hle_SL : (IntermediateField.adjoin K
            ((F i.castSucc.castSucc : Set L) ∪ {β i.castSucc})).toSubfield ≤ S_L := by
          rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro y (⟨k, rfl⟩ | hyF | hyβ)
          · exact ⟨algebraMap K L' k, Subfield.subset_closure (Or.inl ⟨k, rfl⟩), rfl⟩
          · exact ⟨⟨y, hle_L' i.castSucc hyF⟩,
              Subfield.subset_closure (Or.inr (Or.inl hyF)), rfl⟩
          · rw [Set.mem_singleton_iff] at hyβ; rw [hyβ]
            exact ⟨β' i, Subfield.subset_closure (Or.inr (Or.inr rfl)), rfl⟩
        obtain ⟨y, hy, hyx⟩ := hle_SL hxL
        have hxy : y = x := Subtype.ext hyx
        rwa [← hxy]
      · rw [Subfield.closure_le]
        rintro x (⟨k, rfl⟩ | hxF | hxβ)
        · exact (F' i.succ).algebraMap_mem k
        · change (x : L) ∈ F i.castSucc.succ
          rw [(hstep i.castSucc).2]
          exact IntermediateField.subset_adjoin K _ (Or.inl hxF)
        · rw [Set.mem_singleton_iff] at hxβ; rw [hxβ]
          change β i.castSucc ∈ F i.castSucc.succ
          rw [(hstep i.castSucc).2]
          exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
  have hadj_L'L : IntermediateField.adjoin L' ({β (Fin.last s)} : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K ((L' : Set L) ∪ {β (Fin.last s)}) := by
      have hlast_step := (hstep (Fin.last s)).2
      rw [show (Fin.last s).succ = Fin.last (s + 1) from rfl, hlast] at hlast_step
      rw [← hlast_step]
      exact IntermediateField.mem_top
    have hle : IntermediateField.adjoin K ((L' : Set L) ∪ {β (Fin.last s)}) ≤
        (IntermediateField.adjoin L' ({β (Fin.last s)} : Set L)).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      rintro y (hy | hy)
      · exact (IntermediateField.adjoin L' ({β (Fin.last s)} : Set L)).algebraMap_mem ⟨y, hy⟩
      · exact IntermediateField.subset_adjoin L' ({β (Fin.last s)} : Set L) hy
    exact hle hx
  exact ⟨⟨F', β', n', hF'0, hF'last, hchar', hstep'⟩,
    hchar_i (Fin.last s), (hstep (Fin.last s)).1, hadj_L'L⟩

/-- Helper for `Theorem 17.5`: single inductive step lifting a Galois radical closure `Mprev : L'`
to a Galois radical closure `M : L` when `L = L'(β_last)` with `β_last ^ n_last ∈ L'` and
`char K ∤ n_last`. -/
private theorem theorem_17_5_step {K : Type u} {L : Type v} {Mprev : Type v}
    [Field K] [Field L] [Field Mprev] [Algebra K L] [Algebra K Mprev]
    (L' : IntermediateField K L) [Algebra L' Mprev] [IsScalarTower K L' Mprev]
    (hgal_Mprev : IsGarlingGaloisExtension K Mprev)
    (hrad_Mprev : IsGarlingRadicalExtensionNotCharDvd K Mprev)
    {β_last : L} {n_last : ℕ} (hn_last_char : ¬ (ringChar K ∣ n_last))
    (hβ_last_pow : β_last ^ n_last ∈ L')
    (hadj_L'L : IntermediateField.adjoin L' ({β_last} : Set L) = ⊤) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra L M) (_ : Algebra K M) (_ : IsScalarTower K L M),
      IsGarlingGaloisExtension K M ∧ IsGarlingRadicalExtensionNotCharDvd K M := by
  have hn_last_pos : 1 ≤ n_last :=
    (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hn_last_char).1
  let θ_last : L' := ⟨β_last ^ n_last, hβ_last_pow⟩
  obtain ⟨E, fE, aMprevE, aKE, hT_KMprevE, γ, emb, hE_adj, hγ_root⟩ :=
    exists_simple_radical_extension_embedding (Mprev := Mprev) L' (θ := θ_last) hn_last_pos rfl
      hadj_L'L
  let : Field E := fE
  let : Algebra Mprev E := aMprevE
  let : Algebra K E := aKE
  have : IsScalarTower K Mprev E := hT_KMprevE
  have hMprev_E_rad : IsGarlingRadicalExtensionNotCharDvd Mprev E :=
    isGarlingRadicalExtensionNotCharDvd_single
      (by rwa [ringChar_eq_of_field_algebra K Mprev])
      ⟨algebraMap L' Mprev θ_last, by
        have h := hγ_root
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h
        exact h.symm⟩
      hE_adj
  obtain ⟨M, fM, aEM, aKM, hT_KEM, hEM_rad, hgal_KM⟩ :=
    theorem_17_4_with_char hgal_Mprev hE_adj hγ_root hn_last_char
  let : Field M := fM
  let : Algebra E M := aEM
  let : Algebra K M := aKM
  have : IsScalarTower K E M := hT_KEM
  let : Algebra Mprev M := RingHom.toAlgebra ((algebraMap E M).comp (algebraMap Mprev E))
  have : IsScalarTower Mprev E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K Mprev M := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap K M k = algebraMap E M (algebraMap Mprev E (algebraMap K Mprev k))
    rw [← IsScalarTower.algebraMap_apply K Mprev E k, IsScalarTower.algebraMap_apply K E M k]
  have hKM_rad : IsGarlingRadicalExtensionNotCharDvd K M :=
    isGarlingRadicalExtensionNotCharDvd_tower K Mprev M hrad_Mprev
      (isGarlingRadicalExtensionNotCharDvd_tower Mprev E M hMprev_E_rad hEM_rad)
  let aLM : Algebra L M := RingHom.toAlgebra ((algebraMap E M).comp emb.toRingHom)
  have hT_KLM : @IsScalarTower K L M _ aLM.toSMul _ := by
    let : Algebra L M := aLM
    exact IsScalarTower.of_algebraMap_eq fun k => by
      change algebraMap K M k = algebraMap E M (emb (algebraMap K L k))
      rw [emb.commutes k, IsScalarTower.algebraMap_apply K E M k]
  exact ⟨M, fM, aLM, aKM, hT_KLM, hgal_KM, hKM_rad⟩

/-- **Theorem 17.5 + p. 137 Post-Proof Remark (printed pp. 136–137 / PDF pp. 144–145):**
If `L : K` is an extension by radicals whose step exponents `n_1, …, n_r` satisfy
`char K ∤ n_1 ⋯ n_r`, then there exists an extension `M : L` such that `M : K` is a Galois
extension by radicals **whose step exponents also satisfy the `char K` coprimality condition**. -/
theorem theorem_17_5_with_char {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (h : IsGarlingRadicalExtensionNotCharDvd K L) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra L M) (_ : Algebra K M) (_ : IsScalarTower K L M),
      IsGarlingGaloisExtension K M ∧ IsGarlingRadicalExtensionNotCharDvd K M := by
  rcases h with ⟨r, F, β, n, h0, hlast, hchar, hstep⟩
  induction r generalizing L with
  | zero =>
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ := h0.symm.trans hlast
    have hbij : Function.Bijective (Algebra.ofId K L) := by
      refine ⟨(algebraMap K L).injective, fun y => ?_⟩
      have hy : y ∈ (⊥ : IntermediateField K L) := hbot_top.symm ▸ IntermediateField.mem_top
      exact hy
    let eKL : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) hbij
    have hgalK : IsGarlingGaloisExtension K K :=
      (isGarlingGaloisExtension_iff K K).mpr ⟨inferInstance, inferInstance⟩
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      isGarlingGaloisExtension_congr eKL hgalK,
      isGarlingRadicalExtensionNotCharDvd_of_bot_eq_top hbot_top⟩
  | succ s ih =>
    obtain ⟨⟨F', β', n', hF'0, hF'last, hchar', hstep'⟩, hn_last_char, hβ_last_pow, hadj_L'L⟩ :=
      radical_tower_prefix h0 hlast hchar hstep
    obtain ⟨Mprev, fMprev, aL'M, aKMprev, hT_KL'M, hgal_Mprev, hrad_Mprev⟩ :=
      ih F' β' n' hF'0 hF'last hchar' hstep'
    let : Field Mprev := fMprev
    let : Algebra (F (Fin.last s).castSucc) Mprev := aL'M
    let : Algebra K Mprev := aKMprev
    have : IsScalarTower K (F (Fin.last s).castSucc) Mprev := hT_KL'M
    exact theorem_17_5_step (F (Fin.last s).castSucc) hgal_Mprev hrad_Mprev hn_last_char
      hβ_last_pow hadj_L'L

/-- **Theorem 17.5 (literal, printed pp. 136–137 / PDF pp. 144–145):**
*"Suppose that `L = L_r : L_{r-1} : … : L_0 = K` is an extension by radicals, with
`L_i = L_{i-1}(β_i)`, where `β_i` is a root of `x^{n_i} - θ_i` (with `θ_i ∈ L_{i-1}`). Then if
`char K` does not divide `n_1 n_2 … n_r`, there exists an extension `M : L` such that `M : K` is
a Galois extension by radicals."* -/
theorem theorem_17_5 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {r : ℕ} {F : Fin (r + 1) → IntermediateField K L} {β : Fin r → L} {n : Fin r → ℕ}
    (h0 : F 0 = ⊥) (hlast : F (Fin.last r) = ⊤)
    (hstep : ∀ i : Fin r,
      (β i) ^ (n i) ∈ F i.castSucc ∧
      F i.succ = IntermediateField.adjoin K ((F i.castSucc : Set L) ∪ {β i}))
    (hchar : ¬ (ringChar K ∣ ∏ i : Fin r, n i)) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra L M) (_ : Algebra K M) (_ : IsScalarTower K L M),
      IsGarlingGaloisExtension K M ∧ IsGarlingExtensionByRadicals K M := by
  obtain ⟨M, fM, aLM, aKM, hT, hgal, hrad⟩ :=
    theorem_17_5_with_char ⟨r, F, β, n, h0, hlast, hchar, hstep⟩
  exact ⟨M, fM, aLM, aKM, hT, hgal, isGarlingExtensionByRadicals_of_notCharDvd hrad⟩

/-- Helper: if `E : K` is finite Galois and `B : IntermediateField K E` is normal over `K`, then
`IsGarlingSoluble (E ≃ₐ[K] E)` iff `IsGarlingSoluble (E ≃ₐ[B] E)` and
`IsGarlingSoluble (B ≃ₐ[K] B)`. -/
private theorem isGarlingSoluble_gal_iff_of_normal {K : Type u} {E : Type v}
    [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (B : IntermediateField K E) [Normal K B] :
    IsGarlingSoluble (E ≃ₐ[K] E) ↔
      IsGarlingSoluble (E ≃ₐ[B] E) ∧ IsGarlingSoluble (B ≃ₐ[K] B) := by
  let res : (E ≃ₐ[K] E) →* (B ≃ₐ[K] B) := AlgEquiv.restrictNormalHom B
  have hsurj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective E
  have hker_iff : ∀ σ : E ≃ₐ[K] E, σ ∈ res.ker ↔ ∀ x : B, σ x = x := by
    intro σ
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      have hx := congrArg (fun f : B ≃ₐ[K] B => (f x : E)) h
      simpa [res, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormal_commutes] using hx
    · intro h
      ext x
      have hx : ((res σ x : B) : E) = σ x := AlgEquiv.restrictNormal_commutes σ B x
      simpa [hx] using h x
  let eKer : (E ≃ₐ[B] E) ≃* res.ker :=
    { toFun := fun σ =>
        ⟨σ.restrictScalars K, (hker_iff _).mpr fun x => σ.commutes x⟩
      invFun := fun τ =>
        { τ.1.toRingEquiv with
          commutes' := fun x => (hker_iff τ.1).mp τ.2 x }
      left_inv := fun _ => by ext x; rfl
      right_inv := fun _ => by ext x; rfl
      map_mul' := fun _ _ => by ext x; rfl }
  let eQuot : ((E ≃ₐ[K] E) ⧸ res.ker) ≃* (B ≃ₐ[K] B) :=
    QuotientGroup.quotientKerEquivOfSurjective res hsurj
  rw [theorem_17_2_ii res.ker, isGarlingSoluble_congr eKer, isGarlingSoluble_congr eQuot]

/-- Helper for `Theorem 17.6`: if `ε ∈ E` is a primitive `D`th root of unity (`1 ≤ D`), then
`K(ε) : K` is a splitting field extension for `X ^ D - 1`. Abstracting `E` avoids unfolding
`SplittingField` inside `theorem_17_6`. -/
private theorem splittingField_X_pow_sub_one_adjoin_primRoot {K : Type u} {E : Type v}
    [Field K] [Field E] [Algebra K E] {D : ℕ} (hD : 1 ≤ D) {ε : E} (hε : IsPrimitiveRoot ε D) :
    IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K ({ε} : Set E))
      (Polynomial.X ^ D - 1) := by
  let Kε : IntermediateField K E := IntermediateField.adjoin K ({ε} : Set E)
  let εK : Kε := ⟨ε, IntermediateField.mem_adjoin_simple_self K ε⟩
  have hεK : IsPrimitiveRoot εK D :=
    (IsPrimitiveRoot.iff_def _ _).mpr
      ⟨Subtype.ext hε.pow_eq_one, fun l hl => hε.dvd_of_pow_eq_one l (congrArg Subtype.val hl)⟩
  have hfac : (Polynomial.X ^ D - 1 : K[X]).map (algebraMap K Kε) =
      ∏ j : Fin D, (Polynomial.X - Polynomial.C (εK ^ (j : ℕ))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    have h1 := Garling.Chapter16.X_pow_sub_C_pow_eq_prod hD hεK (1 : Kε)
    simpa only [one_pow, map_one, mul_one] using h1
  have hspl_Kε : ((Polynomial.X ^ D - 1 : K[X]).map (algebraMap K Kε)).Splits := by
    rw [hfac]
    exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
  have hεK_root : εK ∈ (Polynomial.X ^ D - 1 : K[X]).rootSet Kε := by
    rw [Polynomial.mem_rootSet]
    exact ⟨(Polynomial.monic_X_pow_sub_C (1 : K) (by omega)).ne_zero,
      by simp [hεK.pow_eq_one]⟩
  have hint_ε : IsIntegral K ε :=
    ⟨Polynomial.X ^ D - 1, Polynomial.monic_X_pow_sub_C (1 : K) (by omega),
      by simp [hε.pow_eq_one]⟩
  have hadj_Kε : Algebra.adjoin K ((Polynomial.X ^ D - 1 : K[X]).rootSet Kε) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨x, hx⟩ _
    have hxAlg : x ∈ Algebra.adjoin K ({ε} : Set E) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_ε.isAlgebraic]
      exact hx
    have hsub : Algebra.adjoin K ({ε} : Set E) ≤
        (Algebra.adjoin K ((Polynomial.X ^ D - 1 : K[X]).rootSet Kε)).map Kε.val := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨εK, Algebra.subset_adjoin hεK_root, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub hxAlg
    have heq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← heq]
  exact (isGarlingSplittingFieldExtension_iff K Kε _).mpr ⟨hspl_Kε, hadj_Kε⟩

/-- Helper for `Theorem 17.6`: if `B = A(γ)` with `γ^m = θ ≠ 0` (`θ ∈ A`), `char A ∤ m`, and `A`
already contains a primitive `m`th root of unity `ω`, then `B : A` is a Garling Galois extension
with cyclic Galois group `Gal(B / A)` (via `Theorem 16.1`). Abstracting `A, B` avoids nested
`IntermediateField` / `SplittingField` unfolding inside `theorem_17_6`. -/
private theorem cyclic_gal_of_radical_with_primRoot {A : Type u} {B : Type v}
    [Field A] [Field B] [Algebra A B] {m : ℕ} {θ ω : A} {γ : B}
    (hθ : θ ≠ 0) (hchar : ¬ (ringChar A ∣ m))
    (hω : IsPrimitiveRoot ω m) (hγ_pow : γ ^ m = algebraMap A B θ)
    (hadj : IntermediateField.adjoin A ({γ} : Set B) = ⊤) :
    IsGarlingGaloisExtension A B ∧ IsCyclic (B ≃ₐ[A] B) := by
  have hm_pos : 1 ≤ m :=
    (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar).1
  have hωB : IsPrimitiveRoot (algebraMap A B ω) m :=
    hω.map_of_injective (algebraMap A B).injective
  have hsf_BA : IsGarlingSplittingFieldExtension A B (Polynomial.X ^ m - Polynomial.C θ) := by
    have hfac : (Polynomial.X ^ m - Polynomial.C θ).map (algebraMap A B) =
        ∏ j : Fin m, (Polynomial.X - Polynomial.C ((algebraMap A B ω) ^ (j : ℕ) * γ)) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hγ_pow]
      exact Garling.Chapter16.X_pow_sub_C_pow_eq_prod hm_pos hωB γ
    have hspl_BA : ((Polynomial.X ^ m - Polynomial.C θ).map (algebraMap A B)).Splits := by
      rw [hfac]
      exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
    have hγ_root : γ ∈ (Polynomial.X ^ m - Polynomial.C θ).rootSet B := by
      rw [Polynomial.mem_rootSet]
      refine ⟨(Polynomial.monic_X_pow_sub_C θ (by omega)).ne_zero, ?_⟩
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hγ_pow, sub_self]
    have hint_γ : IsIntegral A γ :=
      ⟨Polynomial.X ^ m - Polynomial.C θ, Polynomial.monic_X_pow_sub_C θ (by omega),
        (Polynomial.mem_rootSet.mp hγ_root).2⟩
    have hadj_BA : Algebra.adjoin A ((Polynomial.X ^ m - Polynomial.C θ).rootSet B) = ⊤ := by
      have hAlg : Algebra.adjoin A ({γ} : Set B) = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_γ.isAlgebraic, hadj]
        rfl
      exact eq_top_iff.mpr (hAlg ▸ Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hγ_root))
    exact (isGarlingSplittingFieldExtension_iff A B _).mpr ⟨hspl_BA, hadj_BA⟩
  have hpoly_sep : IsGarlingSeparablePoly (Polynomial.X ^ m - Polynomial.C θ : A[X]) :=
    (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero hθ hchar).2.2.2.2
  have hgal_BA : IsGarlingGaloisExtension A B :=
    Garling.Chapter16.isGarlingGalois_of_splittingField
      (Polynomial.monic_X_pow_sub_C θ (by omega)).ne_zero hsf_BA hpoly_sep
  have h161 := (Garling.Chapter16.theorem_16_1 hθ hchar hsf_BA).2.2 (algebraMap A B ω) hωB
  have hAω_eq_bot : (A⟮algebraMap A B ω⟯ : IntermediateField A B) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact (⊥ : IntermediateField A B).algebraMap_mem ω
  let eGalA : (B ≃ₐ[A] B) ≃* (B ≃ₐ[A⟮algebraMap A B ω⟯] B) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := fun ⟨y, hy⟩ => by
            rw [hAω_eq_bot, IntermediateField.mem_bot] at hy
            rcases hy with ⟨a, rfl⟩
            exact σ.commutes a }
      invFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := fun a => σ.commutes ⟨algebraMap A B a, (A⟮algebraMap A B ω⟯).algebraMap_mem a⟩ }
      left_inv := fun _ => by ext x; rfl
      right_inv := fun _ => by ext x; rfl
      map_mul' := fun _ _ => by ext x; rfl }
  have : IsCyclic (B ≃ₐ[A⟮algebraMap A B ω⟯] B) := h161.2.1
  exact ⟨hgal_BA, isCyclic_of_surjective eGalA.symm.toMonoidHom eGalA.symm.surjective⟩

/-- **Theorem 17.6 (literal, printed pp. 137–138 / PDF pp. 145–146):**
*"Suppose that `L = L_r : L_{r-1} : … : L_0 = K` is an extension by radicals, with
`L_i = L_{i-1}(β_i)`, where `β_i` is a root of `x^{n_i} - θ_i` (with `θ_i` in `L_{i-1}`), and that
`char K` does not divide `n_1 … n_r`. If `f ∈ K[x]` splits over `L`, then the Galois group
`Γ_K(f)` is soluble."*

Proved literally for every `r : ℕ`, every `θ_i` (including `θ_i = 0`), every `f ∈ K[X]` (including
`f = 0` and non-separable `f`), and every splitting field `F : K` of `f`, via `Theorem 17.5`,
`Theorem 16.1`, `Theorem 15.4`, and `Theorem 17.2`. -/
theorem theorem_17_6 {K : Type u} {L : Type v} {F : Type w}
    [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    {r : ℕ} {T : Fin (r + 1) → IntermediateField K L} {β : Fin r → L} {n : Fin r → ℕ}
    (h0 : T 0 = ⊥) (hlast : T (Fin.last r) = ⊤)
    (hstep : ∀ i : Fin r,
      (β i) ^ (n i) ∈ T i.castSucc ∧
      T i.succ = IntermediateField.adjoin K ((T i.castSucc : Set L) ∪ {β i}))
    (hchar : ¬ (ringChar K ∣ ∏ i : Fin r, n i))
    {f : K[X]} (hspl : GarlingSplitsOver K L f)
    (hsf : IsGarlingSplittingFieldExtension K F f) :
    IsGarlingSoluble (GarlingPolyGaloisGroup K F f) := by
  classical
  by_cases hf0 : f = 0
  · subst hf0
    have hbot : (⊥ : IntermediateField K F) = ⊤ :=
      (isGarlingSplittingFieldExtension_zero_iff K F).mp hsf
    have : Subsingleton (F ≃ₐ[K] F) := by
      refine ⟨fun σ τ => ?_⟩
      ext x
      have hx : x ∈ (⊥ : IntermediateField K F) := hbot.symm ▸ IntermediateField.mem_top
      rcases hx with ⟨k, rfl⟩
      change σ (algebraMap K F k) = τ (algebraMap K F k)
      rw [σ.commutes, τ.commutes]
    exact isGarlingSoluble_of_subsingleton
  · -- Step 1: Pass to a Galois radical extension `M : K` extending `L` with `char K ∤ ∏ m_i`
    obtain ⟨M, fM, aLM, aKM, hT_KLM, hgal_KM, hrad_KM⟩ :=
      theorem_17_5_with_char ⟨r, T, β, n, h0, hlast, hchar, hstep⟩
    let : Field M := fM
    let : Algebra L M := aLM
    let : Algebra K M := aKM
    have : IsScalarTower K L M := hT_KLM
    rcases hrad_KM with ⟨s, MF, γ, m, hMF0, hMFlast, hchar_m, hstep_m⟩
    have hchar_mi := (not_ringChar_dvd_prod_iff K m).mp hchar_m
    let D : ℕ := ∏ i : Fin s, m i
    have hD_pos : 1 ≤ D :=
      (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd hchar_m).1
    have hcharM : ¬ (ringChar M ∣ D) := by rwa [ringChar_eq_of_field_algebra K M]
    -- Step 2: Adjoin a primitive `D`th root of unity `ε` on top of `M` via splitting field `E`
    let E := Polynomial.SplittingField (Polynomial.X ^ D - 1 : M[X])
    have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K M E, IsScalarTower.algebraMap_apply K L M,
        ← IsScalarTower.algebraMap_apply L M E]
    have hsf_ME : IsGarlingSplittingFieldExtension M E (Polynomial.X ^ D - 1) :=
      (isGarlingSplittingFieldExtension_iff M E (Polynomial.X ^ D - 1)).mpr inferInstance
    have hsf_ME1 : IsGarlingSplittingFieldExtension M E (Polynomial.X ^ D - Polynomial.C 1) := by
      simpa using hsf_ME
    obtain ⟨_, ⟨ε, hε⟩, _⟩ :=
      Garling.Chapter16.theorem_16_1 (one_ne_zero : (1 : M) ≠ 0) hcharM hsf_ME1
    have hsf_cyc_ME : IsGarlingSplittingFieldExtension M E (Polynomial.cyclotomic D M) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharM).1.mpr hsf_ME
    have hε_garl : Garling.Chapter15.IsGarlingPrimitiveRoot D ε :=
      (Garling.Chapter15.isGarlingPrimitiveRoot_iff_isPrimitiveRoot hD_pos ε).mpr hε
    have hE_adj : IntermediateField.adjoin M ({ε} : Set E) = ⊤ :=
      ((Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hcharM).2
        hsf_cyc_ME hε_garl).1
    -- Show `E : K` is finite Galois
    have hfin_KM : FiniteDimensional K M := (isGarlingGaloisExtension_iff K M).mp hgal_KM |>.1
    have hgal_KM' : IsGalois K M := (isGarlingGaloisExtension_iff K M).mp hgal_KM |>.2
    have hfin_ME : FiniteDimensional M E :=
      Polynomial.IsSplittingField.finiteDimensional E (Polynomial.X ^ D - 1)
    have hfin_KE : FiniteDimensional K E := FiniteDimensional.trans K M E
    have hnorm_KE : Normal K E := by
      let b := Module.finBasis K M
      let g' : K[X] := ∏ i, minpoly K (b i)
      have hg'_mon : g'.Monic :=
        Polynomial.monic_prod_of_monic _ _ fun i _ =>
          minpoly.monic (Algebra.IsIntegral.isIntegral (b i))
      have hg'0 : g' ≠ 0 := hg'_mon.ne_zero
      let p : K[X] := g' * (Polynomial.X ^ D - 1)
      have hp0 : p ≠ 0 :=
        mul_ne_zero hg'0 (Polynomial.monic_X_pow_sub_C (1 : K) (by omega)).ne_zero
      have hp_splits : (p.map (algebraMap K E)).Splits := by
        rw [Polynomial.map_mul]
        refine Polynomial.Splits.mul ?_ ?_
        · have hm : g'.map (algebraMap K E) = (g'.map (algebraMap K M)).map (algebraMap M E) := by
            rw [Polynomial.map_map, IsScalarTower.algebraMap_eq K M E]
          rw [hm]
          have hsp_g' : (g'.map (algebraMap K M)).Splits := by
            rw [Polynomial.map_prod]
            exact Polynomial.Splits.prod fun i _ => Normal.splits hgal_KM'.to_normal (b i)
          exact Polynomial.Splits.map hsp_g' (algebraMap M E)
        · have hm : (Polynomial.X ^ D - 1 : K[X]).map (algebraMap K E) =
              ((Polynomial.X ^ D - 1 : M[X]).map (algebraMap M E)) := by
            simp
          rw [hm]
          exact ((isGarlingSplittingFieldExtension_iff M E _).mp hsf_ME).splits
      have hp_adj : Algebra.adjoin K (p.rootSet E) = ⊤ := by
        let S : Subalgebra K E := Algebra.adjoin K (p.rootSet E)
        have hbi_S : ∀ i, algebraMap M E (b i) ∈ S := by
          intro i
          apply Algebra.subset_adjoin
          rw [Polynomial.mem_rootSet]
          refine ⟨hp0, ?_⟩
          have hgi : Polynomial.aeval (b i) g' = 0 := by
            rw [map_prod]
            exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (b i))
          have hgiE : Polynomial.aeval (algebraMap M E (b i)) g' = 0 := by
            have h1 := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K M E) (b i) g'
            rw [hgi, map_zero] at h1
            exact h1
          simp [p, hgiE]
        have hM_le_S : ∀ x : M, algebraMap M E x ∈ S := by
          intro x
          have hx := (b.sum_repr x).symm
          rw [hx, map_sum]
          refine S.sum_mem fun i _ => ?_
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K M E]
          exact S.mul_mem (S.algebraMap_mem _) (hbi_S i)
        have hε_S : ε ∈ S :=
          Algebra.subset_adjoin (Polynomial.mem_rootSet.mpr ⟨hp0, by simp [p, hε.pow_eq_one]⟩)
        have hint_ε : IsIntegral M ε :=
          ⟨Polynomial.X ^ D - 1, Polynomial.monic_X_pow_sub_C 1 (by omega), by simp [hε.pow_eq_one]⟩
        have hAlgM : Algebra.adjoin M ({ε} : Set E) = ⊤ := by
          rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_ε.isAlgebraic,
            hE_adj]
          rfl
        rw [eq_top_iff]
        intro x _
        have hxM : x ∈ Algebra.adjoin M ({ε} : Set E) := hAlgM ▸ Algebra.mem_top
        exact Algebra.adjoin_induction
          (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hε_S)
          (fun c => hM_le_S c)
          (fun _ _ _ _ ha hb => S.add_mem ha hb)
          (fun _ _ _ _ ha hb => S.mul_mem ha hb)
          hxM
      have hsp_p : Polynomial.IsSplittingField K E p := ⟨hp_splits, hp_adj⟩
      exact Normal.of_isSplittingField p
    have hsep_ME : Algebra.IsSeparable M E := by
      have hpoly_sep : IsGarlingSeparablePoly (Polynomial.X ^ D - Polynomial.C (1 : M) : M[X]) :=
        (Garling.Chapter16.X_pow_sub_C_separable_of_ne_zero one_ne_zero hcharM).2.2.2.2
      have hgal_ME : IsGarlingGaloisExtension M E :=
        Garling.Chapter16.isGarlingGalois_of_splittingField
          (Polynomial.monic_X_pow_sub_C (1 : M) (by omega)).ne_zero hsf_ME1 hpoly_sep
      exact ((isGarlingGaloisExtension_iff M E).mp hgal_ME).2.to_isSeparable
    have hsep_KE : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K M E
    have hgal_KE : IsGalois K E := ⟨⟩
    -- Step 3: Build tower `K⟮ε⟯ = L'_0 ≤ L'_1 ≤ … ≤ L'_s = E` where each step is cyclic
    let L' : Fin (s + 1) → IntermediateField K E := fun j =>
      IntermediateField.adjoin K
        ((((MF j).map (IsScalarTower.toAlgHom K M E) : IntermediateField K E) : Set E) ∪ {ε})
    have hL'0 : L' 0 = IntermediateField.adjoin K ({ε} : Set E) := by
      apply IntermediateField.toSubfield_injective
      dsimp only [L']
      rw [hMF0, adjoin_toSubfield_eq_closure_ch17, adjoin_toSubfield_eq_closure_ch17]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_range, SetLike.mem_coe, IntermediateField.mem_map,
        IntermediateField.mem_bot]
      constructor
      · rintro (⟨k, rfl⟩ | ⟨_, ⟨k, rfl⟩, rfl⟩ | hx)
        · exact Or.inl ⟨k, rfl⟩
        · exact Or.inl ⟨k, IsScalarTower.algebraMap_apply K M E k⟩
        · exact Or.inr hx
      · rintro (⟨k, rfl⟩ | hx)
        · exact Or.inl ⟨k, rfl⟩
        · exact Or.inr (Or.inr hx)
    have hL'last : L' (Fin.last s) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin M ({ε} : Set E) := by
        rw [hE_adj]; exact IntermediateField.mem_top
      have hsub : (IntermediateField.adjoin M ({ε} : Set E)).toSubfield ≤
          (L' (Fin.last s)).toSubfield := by
        rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
        rintro y (⟨c, rfl⟩ | hyε)
        · exact IntermediateField.subset_adjoin K _ (Or.inl ⟨c, hMFlast.symm ▸ IntermediateField.mem_top, rfl⟩)
        · rw [Set.mem_singleton_iff] at hyε; rw [hyε]
          exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
      exact hsub hx
    have hL'le : ∀ i : Fin s, L' i.castSucc ≤ L' i.succ := by
      intro i
      apply IntermediateField.adjoin.mono
      apply Set.union_subset_union_left
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      rw [(hstep_m i).2]
      exact IntermediateField.subset_adjoin K _ (Or.inl hy)
    -- Downward induction: for every `k ≤ s`, `Gal(E / L'(s - k))` is Garling-soluble
    have hdown : ∀ k : ℕ, (hk : k ≤ s) → IsGarlingSoluble (E ≃ₐ[L' ⟨s - k, by omega⟩] E) := by
      intro k
      induction k with
      | zero =>
        intro _
        have htop : L' ⟨s - 0, by omega⟩ = ⊤ := by
          simpa [Fin.last] using hL'last
        have : Subsingleton (E ≃ₐ[L' ⟨s - 0, by omega⟩] E) := by
          refine ⟨fun σ τ => ?_⟩
          ext x
          have hx : x ∈ L' ⟨s - 0, by omega⟩ := htop.symm ▸ IntermediateField.mem_top
          have h1 := σ.commutes ⟨x, hx⟩
          have h2 := τ.commutes ⟨x, hx⟩
          exact h1.trans h2.symm
        exact isGarlingSoluble_of_subsingleton
      | succ t iht =>
        intro ht
        let idx : Fin s := ⟨s - (t + 1), by omega⟩
        have hsucc_eq : idx.succ = ⟨s - t, by omega⟩ := Fin.ext (by simp [idx]; omega)
        let A : IntermediateField K E := L' idx.castSucc
        let B : IntermediateField K E := L' idx.succ
        have hAB : A ≤ B := hL'le idx
        have hIH : IsGarlingSoluble (E ≃ₐ[B] E) := by
          have hBeq : B = L' ⟨s - t, by omega⟩ := congrArg L' hsucc_eq
          let eIH : (E ≃ₐ[B] E) ≃* (E ≃ₐ[L' ⟨s - t, by omega⟩] E) :=
            { toFun := fun σ => { σ.toRingEquiv with commutes' := fun a => σ.commutes ⟨a.1, by rw [hBeq]; exact a.2⟩ }
              invFun := fun σ => { σ.toRingEquiv with commutes' := fun a => σ.commutes ⟨a.1, by rw [← hBeq]; exact a.2⟩ }
              left_inv := fun _ => by ext x; rfl
              right_inv := fun _ => by ext x; rfl
              map_mul' := fun _ _ => by ext x; rfl }
          exact (isGarlingSoluble_congr eIH).mpr (iht (by omega))
        -- Lift `B` as an `IntermediateField A E`
        let B_A : IntermediateField A E :=
          { B.toSubfield with algebraMap_mem' := fun a => hAB a.2 }
        have hfin_AE : FiniteDimensional A E := FiniteDimensional.right K A E
        have hgal_AE : IsGalois A E := IsGalois.tower_top_of_isGalois K A E
        let eBE : (E ≃ₐ[B_A] E) ≃* (E ≃ₐ[B] E) :=
          { toFun := fun σ => { σ.toRingEquiv with commutes' := fun b => σ.commutes b }
            invFun := fun σ => { σ.toRingEquiv with commutes' := fun b => σ.commutes b }
            left_inv := fun _ => by ext x; rfl
            right_inv := fun _ => by ext x; rfl
            map_mul' := fun _ _ => by ext x; rfl }
        let γ_i : E := algebraMap M E (γ idx)
        have hγ_pow_A : γ_i ^ (m idx) ∈ A := by
          have hpow : (γ idx) ^ (m idx) ∈ MF idx.castSucc := (hstep_m idx).1
          have hmap : γ_i ^ (m idx) = algebraMap M E ((γ idx) ^ (m idx)) := (map_pow _ _ _).symm
          rw [hmap]
          exact IntermediateField.subset_adjoin K _ (Or.inl ⟨(γ idx) ^ (m idx), hpow, rfl⟩)
        let θ_i : A := ⟨γ_i ^ (m idx), hγ_pow_A⟩
        have hγ_mem_B : γ_i ∈ B_A := by
          change algebraMap M E (γ idx) ∈ L' idx.succ
          apply IntermediateField.subset_adjoin K _
          left
          refine ⟨γ idx, ?_, rfl⟩
          rw [(hstep_m idx).2]
          exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
        have hBA_adj : IntermediateField.adjoin A ({⟨γ_i, hγ_mem_B⟩} : Set B_A) = ⊤ := by
          apply IntermediateField.toSubfield_injective
          apply le_antisymm le_top
          intro ⟨x, hxB⟩ _
          let S_E : Subfield E :=
            (IntermediateField.adjoin A ({⟨γ_i, hγ_mem_B⟩} : Set B_A)).toSubfield.map
              B_A.val.toRingHom
          have hB_le_SE : B.toSubfield ≤ S_E := by
            dsimp only [B, L']
            rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
            rintro y (⟨k, rfl⟩ | ⟨z, hz, rfl⟩ | hyε)
            · exact ⟨algebraMap A B_A (algebraMap K A k),
                (IntermediateField.adjoin A _).algebraMap_mem _, rfl⟩
            · rw [(hstep_m idx).2] at hz
              have hsubM : (IntermediateField.adjoin K
                  ((MF idx.castSucc : Set M) ∪ {γ idx})).toSubfield.map (algebraMap M E) ≤ S_E := by
                rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
                rintro w (⟨k, rfl⟩ | hwMF | hwγ)
                · exact ⟨algebraMap A B_A (algebraMap K A k),
                    (IntermediateField.adjoin A _).algebraMap_mem _,
                    (IsScalarTower.algebraMap_apply K M E k).symm⟩
                · have hwA : algebraMap M E w ∈ A :=
                    IntermediateField.subset_adjoin K _ (Or.inl ⟨w, hwMF, rfl⟩)
                  exact ⟨algebraMap A B_A ⟨algebraMap M E w, hwA⟩,
                    (IntermediateField.adjoin A _).algebraMap_mem _, rfl⟩
                · rw [Set.mem_singleton_iff] at hwγ; rw [hwγ]
                  exact ⟨⟨γ_i, hγ_mem_B⟩,
                    IntermediateField.subset_adjoin A _ rfl, rfl⟩
              exact hsubM ⟨z, hz, rfl⟩
            · rw [Set.mem_singleton_iff] at hyε; rw [hyε]
              have hεA : ε ∈ A := IntermediateField.subset_adjoin K _ (Or.inr rfl)
              exact ⟨algebraMap A B_A ⟨ε, hεA⟩,
                (IntermediateField.adjoin A _).algebraMap_mem _, rfl⟩
          obtain ⟨y, hy, hyx⟩ := hB_le_SE hxB
          have heq : y = ⟨x, hxB⟩ := Subtype.ext hyx
          rwa [← heq]
        -- Case split on `θ_i = 0` vs `θ_i ≠ 0`
        by_cases hθ0 : θ_i = 0
        · have hmi_pos : 1 ≤ m idx :=
            (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd (hchar_mi idx)).1
          have hγ0 : γ_i = 0 := by
            have hp : γ_i ^ (m idx) = 0 := congrArg Subtype.val hθ0
            exact eq_zero_of_pow_eq_zero hp
          have hBA_bot : (⊥ : IntermediateField A B_A) = ⊤ := by
            rw [← hBA_adj]
            apply le_antisymm bot_le
            rw [IntermediateField.adjoin_le_iff]
            rintro _ rfl
            have h0 : (⟨γ_i, hγ_mem_B⟩ : B_A) = 0 := Subtype.ext hγ0
            rw [h0]
            exact (⊥ : IntermediateField A B_A).zero_mem
          have hA_eq_B : A = B := by
            apply le_antisymm hAB
            intro x hxB
            have hx_bot : (⟨x, hxB⟩ : B_A) ∈ (⊥ : IntermediateField A B_A) :=
              hBA_bot.symm ▸ IntermediateField.mem_top
            rcases hx_bot with ⟨a, ha⟩
            have hax : (a : E) = x := congrArg Subtype.val ha
            exact hax ▸ a.2
          let eAB_E : (E ≃ₐ[A] E) ≃* (E ≃ₐ[B] E) :=
            { toFun := fun σ => { σ.toRingEquiv with commutes' := fun b => σ.commutes ⟨b.1, by rw [hA_eq_B]; exact b.2⟩ }
              invFun := fun σ => { σ.toRingEquiv with commutes' := fun a => σ.commutes ⟨a.1, by rw [← hA_eq_B]; exact a.2⟩ }
              left_inv := fun _ => by ext x; rfl
              right_inv := fun _ => by ext x; rfl
              map_mul' := fun _ _ => by ext x; rfl }
          change IsGarlingSoluble (E ≃ₐ[A] E)
          exact (isGarlingSoluble_congr eAB_E).mpr hIH
        · -- `θ_i ≠ 0`: `A` contains a primitive `(m idx)`th root of unity, so `B_A : A` is cyclic!
          have hmi_dvd : m idx ∣ D := Finset.dvd_prod_of_mem m (Finset.mem_univ idx)
          have hmi_pos : 1 ≤ m idx :=
            (Garling.Chapter16.pos_and_natCast_ne_zero_of_not_ringChar_dvd (hchar_mi idx)).1
          have hq_ne0 : D / m idx ≠ 0 :=
            Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (by omega) hmi_dvd) (by omega))
          have hprim_E : IsPrimitiveRoot (ε ^ (D / m idx)) (m idx) := by
            have h1 := hε.pow_of_dvd hq_ne0 (Nat.div_dvd_of_dvd hmi_dvd)
            rwa [Nat.div_div_self hmi_dvd (by omega)] at h1
          have hε_A : ε ∈ A := IntermediateField.subset_adjoin K _ (Or.inr rfl)
          let ωA : A := ⟨ε ^ (D / m idx), pow_mem hε_A (D / m idx)⟩
          have hωA : IsPrimitiveRoot ωA (m idx) :=
            (IsPrimitiveRoot.iff_def _ _).mpr
              ⟨Subtype.ext hprim_E.pow_eq_one, fun l hl => hprim_E.dvd_of_pow_eq_one l (congrArg Subtype.val hl)⟩
          have hcharA : ¬ (ringChar A ∣ m idx) := by
            rw [ringChar_eq_of_field_algebra K A]
            exact hchar_mi idx
          obtain ⟨hgal_BA, hcyc_BA⟩ :=
            cyclic_gal_of_radical_with_primRoot hθ0 hcharA hωA (Subtype.ext rfl) hBA_adj
          have hnorm_BA : Normal A B_A := ((isGarlingGaloisExtension_iff A B_A).mp hgal_BA).2.to_normal
          change IsGarlingSoluble (E ≃ₐ[A] E)
          rw [isGarlingSoluble_gal_iff_of_normal B_A]
          exact ⟨(isGarlingSoluble_congr eBE).mpr hIH, isGarlingSoluble_of_isCyclic⟩
    -- Step 4: `Gal(E / K(ε))` is Garling-soluble, and `Gal(K(ε) / K)` is abelian by `Theorem 15.4`
    have hsol_E_Kε : IsGarlingSoluble (E ≃ₐ[IntermediateField.adjoin K ({ε} : Set E)] E) := by
      have h0_eq : L' ⟨s - s, by omega⟩ = IntermediateField.adjoin K ({ε} : Set E) := by
        simpa using hL'0
      have hs0 := hdown s (le_refl s)
      let e0 : (E ≃ₐ[L' ⟨s - s, by omega⟩] E) ≃*
          (E ≃ₐ[IntermediateField.adjoin K ({ε} : Set E)] E) :=
        { toFun := fun σ => { σ.toRingEquiv with commutes' := fun a => σ.commutes ⟨a.1, by rw [h0_eq]; exact a.2⟩ }
          invFun := fun σ => { σ.toRingEquiv with commutes' := fun a => σ.commutes ⟨a.1, by rw [← h0_eq]; exact a.2⟩ }
          left_inv := fun _ => by ext x; rfl
          right_inv := fun _ => by ext x; rfl
          map_mul' := fun _ _ => by ext x; rfl }
      exact (isGarlingSoluble_congr e0).mp hs0
    let Kε : IntermediateField K E := IntermediateField.adjoin K ({ε} : Set E)
    have hsf_Kε : IsGarlingSplittingFieldExtension K Kε (Polynomial.X ^ D - 1) :=
      splittingField_X_pow_sub_one_adjoin_primRoot hD_pos hε
    have hsf_cyc_Kε : IsGarlingSplittingFieldExtension K Kε (Polynomial.cyclotomic D K) :=
      (Garling.Chapter15.section_15_3_splittingField_cyclotomic_iff hchar_m).1.mpr hsf_Kε
    have hab_Kε : ∀ σ τ : Kε ≃ₐ[K] Kε, σ * τ = τ * σ :=
      (Garling.Chapter15.theorem_15_4 hchar_m hsf_cyc_Kε).1
    have hsp_Kε : Polynomial.IsSplittingField K Kε (Polynomial.X ^ D - 1) :=
      (isGarlingSplittingFieldExtension_iff K Kε _).mp hsf_Kε
    have hnorm_Kε : Normal K Kε := Normal.of_isSplittingField (Polynomial.X ^ D - 1)
    have hsol_Kε : IsGarlingSoluble (Kε ≃ₐ[K] Kε) := by
      let : CommGroup (Kε ≃ₐ[K] Kε) := { mul_comm := hab_Kε }
      have : FiniteDimensional K Kε := FiniteDimensional.left K Kε E
      exact isGarlingSoluble_of_commGroup_finite
    have hsol_KE : IsGarlingSoluble (E ≃ₐ[K] E) :=
      (isGarlingSoluble_gal_iff_of_normal Kε).mpr ⟨hsol_E_Kε, hsol_Kε⟩
    -- Step 5: `f` splits over `L ≤ E`; restrict `Gal(E / K)` onto splitting subfield `N ≤ E` of `f`
    have hspl_E : GarlingSplitsOver K E f := garlingSplitsOver_tower_right hspl
    obtain ⟨nf, cf, αf, hexpf⟩ := hspl_E
    let N : IntermediateField K E := IntermediateField.adjoin K (Set.range αf)
    have hsf_N : IsGarlingSplittingFieldExtension K N f := theorem_7_1 hf0 hexpf
    have hsp_N : Polynomial.IsSplittingField K N f :=
      (isGarlingSplittingFieldExtension_iff K N f).mp hsf_N
    have hnorm_N : Normal K N := Normal.of_isSplittingField f
    have hsol_N : IsGarlingSoluble (N ≃ₐ[K] N) :=
      ((isGarlingSoluble_gal_iff_of_normal N).mp hsol_KE).2
    obtain ⟨eNF⟩ := garlingPolyGaloisGroup_independent_of_splittingField hsf_N hsf
    exact (isGarlingSoluble_congr eNF).mp hsol_N

/-- **§17.4 Unnumbered Main-Text Prose Theorem (printed p. 138 / PDF p. 146):**
*"As an example, we have seen that the quintic `x^5 - 4x + 2` is irreducible over `ℚ`, and has
Galois group `Σ_5`. `Σ_5` is not soluble, and so `x^5 - 4x + 2` cannot be solved by radicals!"* -/
theorem section_17_4_quintic_not_solvable_by_radicals :
    let f : ℚ[X] := Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2
    Irreducible f ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ F],
      IsGarlingSplittingFieldExtension ℚ F f →
      Nonempty (GarlingPolyGaloisGroup ℚ F f ≃* SigmaN 5) ∧
      ¬ IsGarlingSoluble (GarlingPolyGaloisGroup ℚ F f)) ∧
    ¬ IsGarlingSolvableByRadicals f := by
  intro f
  have hirr : Irreducible f := example_5_2_quintic_irreducible.2.1
  have hgal_all : ∀ (F : Type u) [Field F] [Algebra ℚ F],
      IsGarlingSplittingFieldExtension ℚ F f →
      Nonempty (GarlingPolyGaloisGroup ℚ F f ≃* SigmaN 5) ∧
      ¬ IsGarlingSoluble (GarlingPolyGaloisGroup ℚ F f) := by
    intro F _ _ hsfF
    obtain ⟨_, ⟨e⟩⟩ := section_11_3_quintic_example.{u}.2.2.2.2.2 F hsfF
    refine ⟨⟨e⟩, fun hsol => ?_⟩
    exact (corollary_to_theorem_17_2 (le_refl 5)).1 ((isGarlingSoluble_congr e).mp hsol)
  refine ⟨hirr, hgal_all, ?_⟩
  rintro ⟨L, fL, aL, hrad, hspl⟩
  let : Field L := fL
  let : Algebra ℚ L := aL
  obtain ⟨r, T, β, n, h0, hlast, hchar, hstep⟩ :=
    isGarlingRadicalExtensionNotCharDvd_of_charZero hrad
  let F := Polynomial.SplittingField f
  have hsfF : IsGarlingSplittingFieldExtension ℚ F f :=
    (isGarlingSplittingFieldExtension_iff ℚ F f).mpr inferInstance
  have hsol_F : IsGarlingSoluble (GarlingPolyGaloisGroup ℚ F f) :=
    theorem_17_6 h0 hlast hstep hchar hspl hsfF
  obtain ⟨_, ⟨e⟩⟩ := section_11_3_quintic_example.{0}.2.2.2.2.2 F hsfF
  exact (corollary_to_theorem_17_2 (le_refl 5)).1 ((isGarlingSoluble_congr e).mp hsol_F)

/-! ### Exercises 17.3–17.7 (§17.4, printed p. 138 / PDF p. 146) -/

/-- `3^{1/2} ∈ ℝ` for `Exercise 17.3` (printed p. 138). -/
noncomputable def ex173Sqrt3 : ℝ := Real.sqrt 3

/-- `(3^{1/2} + 1)^{1/2} ∈ ℝ` for `Exercise 17.3` (printed p. 138). -/
noncomputable def ex173Alpha : ℝ := Real.sqrt (Real.sqrt 3 + 1)

/-- `L_1 = ℚ(3^{1/2}) ⊆ ℝ` for `Exercise 17.3` (printed p. 138). -/
noncomputable def ex173L1 : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({ex173Sqrt3} : Set ℝ)

/-- `L_2 = ℚ((3^{1/2} + 1)^{1/2}) ⊆ ℝ` for `Exercise 17.3` (printed p. 138). -/
noncomputable def ex173L2 : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({ex173Alpha} : Set ℝ)

/-- `L_2` viewed as an extension of `L_1` inside `ℝ`: `L_1((3^{1/2} + 1)^{1/2})`. -/
noncomputable def ex173L2OverL1 : IntermediateField ex173L1 ℝ :=
  IntermediateField.adjoin ex173L1 ({ex173Alpha} : Set ℝ)

/-- Minimal polynomial `x^4 - 2x^2 - 2 ∈ ℚ[x]` of `(3^{1/2} + 1)^{1/2}` over `ℚ`
(`Exercise 17.3`, printed p. 138). -/
noncomputable def ex173Poly : ℚ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 2 * Polynomial.X ^ 2 - Polynomial.C 2

private theorem ex173Alpha_sq : ex173Alpha ^ 2 = ex173Sqrt3 + 1 := by
  dsimp only [ex173Alpha, ex173Sqrt3]
  exact Real.sq_sqrt (by positivity)

private theorem ex173Sqrt3_sq : ex173Sqrt3 ^ 2 = 3 := by
  dsimp only [ex173Sqrt3]
  exact Real.sq_sqrt (by norm_num)

private theorem ex173Poly_monic : ex173Poly.Monic := by
  dsimp only [ex173Poly]; monicity!

private theorem ex173Poly_natDegree : ex173Poly.natDegree = 4 := by
  dsimp only [ex173Poly]; compute_degree!

private theorem ex173Poly_irreducible : Irreducible ex173Poly := by
  let fZ : ℤ[X] := Polynomial.X ^ 4 - Polynomial.C 2 * Polynomial.X ^ 2 - Polynomial.C 2
  have hfZ_deg : fZ.natDegree = 4 := by dsimp [fZ]; compute_degree!
  have hfZ_mon : fZ.Monic := by dsimp [fZ]; monicity!
  have hfZ_irr : Irreducible fZ := by
    refine (theorem_5_2 (p := (2 : ℤ)) (n := 4) (by omega) (le_of_eq hfZ_deg)
      (isGarlingRelativelyPrime_coeffs_of_monic hfZ_mon hfZ_deg) Int.prime_two ?_ ?_ ?_).2.1
    · intro i hi
      dsimp [fZ]
      interval_cases i <;> simp
    · dsimp [fZ]; simp
    · dsimp [fZ]; norm_num
  rcases (corollary_gauss_lemma ℚ fZ).mp hfZ_irr with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
  · exfalso
    have hd := congrArg Polynomial.natDegree hC
    rw [hfZ_deg, Polynomial.natDegree_C] at hd
    omega
  · have hmap_eq : fZ.map (algebraMap ℤ ℚ) = ex173Poly := by
      dsimp [fZ, ex173Poly]; simp [map_ofNat]
    rwa [hmap_eq] at hmap_irr

private theorem ex173_real_roots_eq (x : ℝ) (hx : Polynomial.aeval x ex173Poly = 0) :
    x = ex173Alpha ∨ x = -ex173Alpha := by
  have heq : x ^ 4 - 2 * x ^ 2 - 2 = 0 := by
    simpa [ex173Poly] using hx
  have hsq : (x ^ 2 - 1) ^ 2 = ex173Sqrt3 ^ 2 := by
    rw [ex173Sqrt3_sq]; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
  · have hx2 : x ^ 2 = ex173Alpha ^ 2 := by rw [ex173Alpha_sq]; linarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hx2
  · exfalso
    have hgt : (1 : ℝ) < ex173Sqrt3 := by
      have h1 : (1 : ℝ) = Real.sqrt 1 := by simp
      rw [h1]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hnn : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    linarith

private theorem ex173_carrier_eq : (ex173L2OverL1 : Set ℝ) = (ex173L2 : Set ℝ) := by
  have hsqrt3_mem_L2 : ex173Sqrt3 ∈ ex173L2 := by
    have hα : ex173Alpha ∈ ex173L2 := IntermediateField.mem_adjoin_simple_self ℚ ex173Alpha
    have heq : ex173Sqrt3 = ex173Alpha ^ 2 - 1 := by linarith [ex173Alpha_sq]
    rw [heq]
    exact sub_mem (pow_mem hα 2) ex173L2.one_mem
  have hL1_le_L2 : ex173L1 ≤ ex173L2 := by
    rw [ex173L1, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hsqrt3_mem_L2
  have hsf : ex173L2OverL1.toSubfield = ex173L2.toSubfield := by
    apply le_antisymm
    · dsimp only [ex173L2OverL1]
      rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro x (⟨y, rfl⟩ | hxα)
      · exact hL1_le_L2 y.2
      · rw [Set.mem_singleton_iff] at hxα; rw [hxα]
        exact IntermediateField.mem_adjoin_simple_self ℚ ex173Alpha
    · dsimp only [ex173L2]
      rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro x (⟨q, rfl⟩ | hxα)
      · exact ex173L2OverL1.algebraMap_mem (algebraMap ℚ ex173L1 q)
      · rw [Set.mem_singleton_iff] at hxα; rw [hxα]
        exact IntermediateField.mem_adjoin_simple_self ex173L1 ex173Alpha
  exact congrArg SetLike.coe hsf

private theorem ex173_normal_L1 : IsGarlingNormal ℚ ex173L1 := by
  rw [isGarlingNormal_iff]
  let p1 : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 3
  have hp1_ne0 : p1 ≠ 0 := (Polynomial.monic_X_pow_sub_C (3 : ℚ) (by decide)).ne_zero
  let s3 : ex173L1 := ⟨ex173Sqrt3, IntermediateField.mem_adjoin_simple_self ℚ ex173Sqrt3⟩
  have hs3_sq : s3 ^ 2 = algebraMap ℚ ex173L1 3 := Subtype.ext (by
    change ex173Sqrt3 ^ 2 = (3 : ℝ); exact ex173Sqrt3_sq)
  have hspl1 : (p1.map (algebraMap ℚ ex173L1)).Splits := by
    have hfac : p1.map (algebraMap ℚ ex173L1) =
        (Polynomial.X - Polynomial.C s3) * (Polynomial.X - Polynomial.C (-s3)) := by
      dsimp only [p1]
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hs3_sq]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  have hs3_root : s3 ∈ p1.rootSet ex173L1 := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp1_ne0, ?_⟩
    dsimp only [p1]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hs3_sq, sub_self]
  have hint_s3 : IsIntegral ℚ ex173Sqrt3 :=
    ⟨p1, Polynomial.monic_X_pow_sub_C (3 : ℚ) (by decide), by
      dsimp only [p1]; simp [ex173Sqrt3_sq]⟩
  have hadj1 : Algebra.adjoin ℚ (p1.rootSet ex173L1) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨x, hx⟩ _
    have hxAlg : x ∈ Algebra.adjoin ℚ ({ex173Sqrt3} : Set ℝ) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_s3.isAlgebraic]
      exact hx
    have hsub : Algebra.adjoin ℚ ({ex173Sqrt3} : Set ℝ) ≤
        (Algebra.adjoin ℚ (p1.rootSet ex173L1)).map ex173L1.val := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨s3, Algebra.subset_adjoin hs3_root, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub hxAlg
    have heq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← heq]
  have : Polynomial.IsSplittingField ℚ ex173L1 p1 := ⟨hspl1, hadj1⟩
  exact Normal.of_isSplittingField p1

private theorem ex173_normal_L21 : IsGarlingNormal ex173L1 ex173L2OverL1 := by
  rw [isGarlingNormal_iff]
  let c2 : ex173L1 := ⟨ex173Sqrt3 + 1,
    add_mem (IntermediateField.mem_adjoin_simple_self ℚ ex173Sqrt3) ex173L1.one_mem⟩
  let p2 : ex173L1[X] := Polynomial.X ^ 2 - Polynomial.C c2
  have hp2_ne0 : p2 ≠ 0 := (Polynomial.monic_X_pow_sub_C c2 (by decide)).ne_zero
  let α2 : ex173L2OverL1 :=
    ⟨ex173Alpha, IntermediateField.mem_adjoin_simple_self ex173L1 ex173Alpha⟩
  have hα2_sq : α2 ^ 2 = algebraMap ex173L1 ex173L2OverL1 c2 :=
    Subtype.ext ex173Alpha_sq
  have hspl2 : (p2.map (algebraMap ex173L1 ex173L2OverL1)).Splits := by
    have hfac : p2.map (algebraMap ex173L1 ex173L2OverL1) =
        (Polynomial.X - Polynomial.C α2) * (Polynomial.X - Polynomial.C (-α2)) := by
      dsimp only [p2]
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, ← hα2_sq]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  have hα2_root : α2 ∈ p2.rootSet ex173L2OverL1 := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp2_ne0, ?_⟩
    dsimp only [p2]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα2_sq, sub_self]
  have hint_α2 : IsIntegral ex173L1 ex173Alpha :=
    ⟨p2, Polynomial.monic_X_pow_sub_C c2 (by decide), by
      dsimp only [p2]
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        sub_eq_zero]
      exact ex173Alpha_sq⟩
  have hadj2 : Algebra.adjoin ex173L1 (p2.rootSet ex173L2OverL1) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨x, hx⟩ _
    have hxAlg : x ∈ Algebra.adjoin ex173L1 ({ex173Alpha} : Set ℝ) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint_α2.isAlgebraic]
      exact hx
    have hsub : Algebra.adjoin ex173L1 ({ex173Alpha} : Set ℝ) ≤
        (Algebra.adjoin ex173L1 (p2.rootSet ex173L2OverL1)).map ex173L2OverL1.val := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨α2, Algebra.subset_adjoin hα2_root, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub hxAlg
    have heq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← heq]
  have : Polynomial.IsSplittingField ex173L1 ex173L2OverL1 p2 := ⟨hspl2, hadj2⟩
  exact Normal.of_isSplittingField p2

private theorem ex173_aeval_alpha : Polynomial.aeval ex173Alpha ex173Poly = 0 := by
  dsimp only [ex173Poly]
  simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    eq_ratCast, Rat.cast_ofNat]
  have h4 : ex173Alpha ^ 4 = (ex173Alpha ^ 2) ^ 2 := by ring
  rw [h4, ex173Alpha_sq]
  have hsq3 := ex173Sqrt3_sq
  nlinarith

private theorem ex173_minpoly_alpha : minpoly ℚ ex173Alpha = ex173Poly :=
  (minpoly.eq_of_irreducible_of_monic ex173Poly_irreducible ex173_aeval_alpha ex173Poly_monic).symm

private theorem ex173_not_normal_L2 : ¬ IsGarlingNormal ℚ ex173L2 := by
  classical
  intro hnorm
  rw [isGarlingNormal_iff] at hnorm
  let αL2 : ex173L2 := ⟨ex173Alpha, IntermediateField.mem_adjoin_simple_self ℚ ex173Alpha⟩
  have hmin_αL2 : minpoly ℚ αL2 = ex173Poly := by
    have h1 := minpoly.algHom_eq ex173L2.val Subtype.val_injective αL2
    exact h1.symm.trans ex173_minpoly_alpha
  have hspl_L2 : (ex173Poly.map (algebraMap ℚ ex173L2)).Splits := by
    rw [← hmin_αL2]
    exact Normal.splits hnorm αL2
  have hspl_R : (ex173Poly.map (algebraMap ℚ ℝ)).Splits := by
    have hm : ex173Poly.map (algebraMap ℚ ℝ) =
        (ex173Poly.map (algebraMap ℚ ex173L2)).map ex173L2.val.toRingHom := by
      rw [Polynomial.map_map]; rfl
    rw [hm]
    exact Polynomial.Splits.map hspl_L2 ex173L2.val.toRingHom
  have hcard_roots : (ex173Poly.map (algebraMap ℚ ℝ)).roots.card = 4 := by
    rw [← hspl_R.natDegree_eq_card_roots, Polynomial.natDegree_map, ex173Poly_natDegree]
  have hsep_R : (ex173Poly.map (algebraMap ℚ ℝ)).Separable :=
    ex173Poly_irreducible.separable.map
  have hnodup : (ex173Poly.map (algebraMap ℚ ℝ)).roots.Nodup :=
    Polynomial.nodup_roots hsep_R
  have hsub_fin : (ex173Poly.map (algebraMap ℚ ℝ)).roots.toFinset ⊆
      ({ex173Alpha, -ex173Alpha} : Finset ℝ) := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr ex173Poly_monic.ne_zero),
      Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def] at hx
    rcases ex173_real_roots_eq x hx with rfl | rfl <;> simp
  have hle2 : (ex173Poly.map (algebraMap ℚ ℝ)).roots.card ≤ 2 := by
    calc (ex173Poly.map (algebraMap ℚ ℝ)).roots.card
        = (ex173Poly.map (algebraMap ℚ ℝ)).roots.toFinset.card :=
          (Multiset.toFinset_card_of_nodup hnodup).symm
      _ ≤ ({ex173Alpha, -ex173Alpha} : Finset ℝ).card := Finset.card_le_card hsub_fin
      _ ≤ 2 := Finset.card_le_two
  omega

private noncomputable def ex173AlphaC : ℂ := (ex173Alpha : ℂ)
private noncomputable def ex173ISqrt2 : ℂ := Complex.I * (Real.sqrt 2 : ℂ)
private noncomputable def ex173BetaC : ℂ := ex173ISqrt2 / ex173AlphaC
private noncomputable def ex173E0 : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({ex173AlphaC, ex173ISqrt2} : Set ℂ)

private theorem ex173E0_splittingField :
    IsGarlingSplittingFieldExtension ℚ ex173E0 ex173Poly := by
  have hα_pos : (0 : ℝ) < ex173Alpha := by
    dsimp only [ex173Alpha]; exact Real.sqrt_pos.mpr (by positivity)
  have hαC_ne : ex173AlphaC ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα_pos)
  have hαC_sq : ex173AlphaC ^ 2 = (ex173Sqrt3 : ℂ) + 1 := by
    dsimp only [ex173AlphaC]
    rw [← Complex.ofReal_pow, ex173Alpha_sq, Complex.ofReal_add, Complex.ofReal_one]
  have hiS2_sq : ex173ISqrt2 ^ 2 = -2 := by
    dsimp only [ex173ISqrt2]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h3 : (ex173Sqrt3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, ex173Sqrt3_sq]; norm_num
  have hβC_sq : ex173BetaC ^ 2 = 1 - (ex173Sqrt3 : ℂ) := by
    dsimp only [ex173BetaC]
    rw [div_pow, hiS2_sq, hαC_sq, div_eq_iff (by rw [← hαC_sq]; exact pow_ne_zero 2 hαC_ne)]
    linear_combination h3
  have hαC_E₀ : ex173AlphaC ∈ ex173E0 := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hiS2_E₀ : ex173ISqrt2 ∈ ex173E0 := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hβC_E₀ : ex173BetaC ∈ ex173E0 := div_mem hiS2_E₀ hαC_E₀
  let αE : ex173E0 := ⟨ex173AlphaC, hαC_E₀⟩
  let βE : ex173E0 := ⟨ex173BetaC, hβC_E₀⟩
  let iS2E : ex173E0 := ⟨ex173ISqrt2, hiS2_E₀⟩
  have hfac : ex173Poly.map (algebraMap ℚ ex173E0) =
      (Polynomial.X - Polynomial.C αE) * (Polynomial.X - Polynomial.C (-αE)) *
      (Polynomial.X - Polynomial.C βE) * (Polynomial.X - Polynomial.C (-βE)) := by
    apply Polynomial.map_injective ex173E0.val.toRingHom ex173E0.val.injective
    rw [Polynomial.map_map]
    have hcomp : ex173E0.val.toRingHom.comp (algebraMap ℚ ex173E0) = algebraMap ℚ ℂ := rfl
    rw [hcomp]
    have hαE_val : ex173E0.val.toRingHom αE = ex173AlphaC := rfl
    have hβE_val : ex173E0.val.toRingHom βE = ex173BetaC := rfl
    have hlhs : ex173Poly.map (algebraMap ℚ ℂ) =
        Polynomial.X ^ 4 - Polynomial.C (2 : ℂ) * Polynomial.X ^ 2 - Polynomial.C (2 : ℂ) := by
      dsimp only [ex173Poly]
      rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      simp only [map_ofNat]
    have hrhs1 : ((Polynomial.X - Polynomial.C αE) * (Polynomial.X - Polynomial.C (-αE)) *
        (Polynomial.X - Polynomial.C βE) * (Polynomial.X - Polynomial.C (-βE))).map
          ex173E0.val.toRingHom =
        (Polynomial.X - Polynomial.C ex173AlphaC) * (Polynomial.X - Polynomial.C (-ex173AlphaC)) *
        (Polynomial.X - Polynomial.C ex173BetaC) * (Polynomial.X - Polynomial.C (-ex173BetaC)) := by
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_X,
        Polynomial.map_C, map_neg, hαE_val, hβE_val]
    rw [hlhs, hrhs1]
    have hsum : ex173AlphaC ^ 2 + ex173BetaC ^ 2 = 2 := by rw [hαC_sq, hβC_sq]; ring
    have hprod : ex173AlphaC ^ 2 * ex173BetaC ^ 2 = -2 := by
      rw [hαC_sq, hβC_sq]; linear_combination -h3
    have hrhs : (Polynomial.X - Polynomial.C ex173AlphaC) * (Polynomial.X - Polynomial.C (-ex173AlphaC)) *
        (Polynomial.X - Polynomial.C ex173BetaC) * (Polynomial.X - Polynomial.C (-ex173BetaC)) =
        Polynomial.X ^ 4 - Polynomial.C (ex173AlphaC ^ 2 + ex173BetaC ^ 2) * Polynomial.X ^ 2 +
        Polynomial.C (ex173AlphaC ^ 2 * ex173BetaC ^ 2) := by
      simp only [map_neg, map_add, map_mul, map_pow]
      ring
    rw [hrhs, hsum, hprod]
    simp only [map_neg, map_ofNat]
    ring
  have hspl : (ex173Poly.map (algebraMap ℚ ex173E0)).Splits := by
    rw [hfac]
    exact (((Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)).mul
      (Polynomial.Splits.X_sub_C _)).mul (Polynomial.Splits.X_sub_C _)
  have hαE_root : αE ∈ ex173Poly.rootSet ex173E0 := by
    rw [Polynomial.mem_rootSet]
    refine ⟨ex173Poly_monic.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hfac]
    simp
  have hβE_root : βE ∈ ex173Poly.rootSet ex173E0 := by
    rw [Polynomial.mem_rootSet]
    refine ⟨ex173Poly_monic.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hfac]
    simp
  have hiS2_eq : iS2E = αE * βE := Subtype.ext (by
    change ex173ISqrt2 = ex173AlphaC * (ex173ISqrt2 / ex173AlphaC)
    exact (mul_div_cancel₀ ex173ISqrt2 hαC_ne).symm)
  have hadj_if : IntermediateField.adjoin ℚ (ex173Poly.rootSet ex173E0) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨x, hx⟩ _
    have hsub : ex173E0.toSubfield ≤
        (IntermediateField.adjoin ℚ (ex173Poly.rootSet ex173E0)).toSubfield.map ex173E0.val.toRingHom := by
      dsimp only [ex173E0]
      rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · exact ⟨algebraMap ℚ ex173E0 q, (IntermediateField.adjoin ℚ _).algebraMap_mem q, rfl⟩
      · rcases hy with rfl | rfl
        · exact ⟨αE, IntermediateField.subset_adjoin ℚ _ hαE_root, rfl⟩
        · exact ⟨iS2E, hiS2_eq ▸ mul_mem (IntermediateField.subset_adjoin ℚ _ hαE_root)
            (IntermediateField.subset_adjoin ℚ _ hβE_root), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub hx
    have heq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← heq]
  have hadj : Algebra.adjoin ℚ (ex173Poly.rootSet ex173E0) = ⊤ := by
    have halg : ∀ x ∈ ex173Poly.rootSet ex173E0, IsAlgebraic ℚ x := fun x hx =>
      ⟨ex173Poly, ex173Poly_monic.ne_zero, (Polynomial.mem_rootSet.mp hx).2⟩
    have hsub := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
    rw [hadj_if] at hsub
    exact hsub.symm
  exact (isGarlingSplittingFieldExtension_iff ℚ ex173E0 ex173Poly).mpr ⟨hspl, hadj⟩

private theorem ex173E0_finrank : Module.finrank ℚ ex173E0 = 8 := by
  classical
  have hαC_E₀ : ex173AlphaC ∈ ex173E0 := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hiS2_E₀ : ex173ISqrt2 ∈ ex173E0 := IntermediateField.subset_adjoin ℚ _ (by simp)
  let αE : ex173E0 := ⟨ex173AlphaC, hαC_E₀⟩
  let iS2E : ex173E0 := ⟨ex173ISqrt2, hiS2_E₀⟩
  let Kα : IntermediateField ℚ ex173E0 := IntermediateField.adjoin ℚ ({αE} : Set ex173E0)
  have hmin_αE : minpoly ℚ αE = ex173Poly := by
    have h2 := minpoly.algHom_eq ex173E0.val Subtype.val_injective αE
    have h4 : minpoly ℚ ex173AlphaC = ex173Poly := by
      let embRC : ℝ →ₐ[ℚ] ℂ := Complex.ofRealAm.restrictScalars ℚ
      have h5 : embRC ex173Alpha = ex173AlphaC := rfl
      rw [← h5, minpoly.algHom_eq embRC Complex.ofReal_injective ex173Alpha]
      exact ex173_minpoly_alpha
    exact h2.symm.trans h4
  have hint_αE : IsIntegral ℚ αE :=
    ⟨ex173Poly, ex173Poly_monic, by
      have h1 := minpoly.aeval ℚ αE
      rw [hmin_αE] at h1
      exact h1⟩
  have hfin_Kα : Module.finrank ℚ Kα = 4 := by
    rw [IntermediateField.adjoin.finrank hint_αE, hmin_αE, ex173Poly_natDegree]
  have him_Kα : ∀ z : Kα, ((z : ex173E0) : ℂ).im = 0 := by
    intro ⟨z, hz⟩
    have hsub : Kα.toSubfield.map ex173E0.val.toRingHom ≤ Complex.ofRealHom.fieldRange := by
      dsimp only [Kα]
      rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · exact ⟨(q : ℝ), by simp⟩
      · rw [Set.mem_singleton_iff] at hy; rw [hy]
        exact ⟨ex173Alpha, rfl⟩
    obtain ⟨r, hr⟩ := hsub ⟨z, hz, rfl⟩
    have h1 : (z : ℂ) = (r : ℂ) := hr.symm
    change (z : ℂ).im = 0
    rw [h1]
    exact Complex.ofReal_im r
  have hiS2_sq : ex173ISqrt2 ^ 2 = -2 := by
    dsimp only [ex173ISqrt2]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let q2 : Kα[X] := Polynomial.X ^ 2 + Polynomial.C 2
  have hq2_mon : q2.Monic := by dsimp only [q2]; monicity!
  have hq2_deg : q2.natDegree = 2 := by dsimp only [q2]; compute_degree!
  have hq2_no_root : ∀ z : Kα, q2.eval z ≠ 0 := by
    intro z hz
    have hzC : (((z : ex173E0) : ℂ) ^ 2 + 2) = 0 := by
      have h1 := congrArg (fun w : Kα => ex173E0.val (Kα.val w)) hz
      dsimp only [q2] at h1
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h1
      simp only [map_add, map_pow, map_ofNat, map_zero] at h1
      exact h1
    have hre := congrArg Complex.re hzC
    simp only [Complex.add_re, sq, Complex.mul_re, him_Kα z, mul_zero, sub_zero,
      Complex.re_ofNat, Complex.zero_re] at hre
    nlinarith [sq_nonneg (((z : ex173E0) : ℂ).re)]
  have hq2_irr : Irreducible q2 := by
    rw [irreducible_iff]
    refine ⟨fun hu => by have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, fun a b hab => ?_⟩
    have ha0 : a ≠ 0 := fun h0 => hq2_mon.ne_zero (by rw [hab, h0, zero_mul])
    have hb0 : b ≠ 0 := fun h0 => hq2_mon.ne_zero (by rw [hab, h0, mul_zero])
    have hdeg_sum : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hq2_deg]
    by_cases ha0d : a.natDegree = 0
    · left
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree ha0, ha0d]; rfl)
    · by_cases hb0d : b.natDegree = 0
      · right
        exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hb0, hb0d]; rfl)
      · exfalso
        have ha1 : a.natDegree = 1 := by omega
        let c1 : Kα := a.coeff 1
        let c0 : Kα := a.coeff 0
        have hc1_ne : c1 ≠ 0 := by
          dsimp only [c1]; rw [← ha1]; exact Polynomial.leadingCoeff_ne_zero.mpr ha0
        have ha_eq : a = Polynomial.C c1 * Polynomial.X + Polynomial.C c0 :=
          Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq ha1))
        have hroot : q2.eval (-c0 / c1) = 0 := by
          rw [hab, Polynomial.eval_mul, ha_eq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          have h0 : c1 * (-c0 / c1) + c0 = 0 := by field_simp [hc1_ne]; ring
          rw [h0, zero_mul]
        exact hq2_no_root (-c0 / c1) hroot
  have hq2_aeval : Polynomial.aeval iS2E q2 = 0 := by
    dsimp only [q2]
    rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    apply Subtype.ext
    change ex173ISqrt2 ^ 2 + (2 : ℂ) = 0
    rw [hiS2_sq]; ring
  have hmin_iS2 : minpoly Kα iS2E = q2 :=
    (minpoly.eq_of_irreducible_of_monic hq2_irr hq2_aeval hq2_mon).symm
  have hint_iS2 : IsIntegral Kα iS2E := ⟨q2, hq2_mon, hq2_aeval⟩
  have hadj_Kα_E₀ : IntermediateField.adjoin Kα ({iS2E} : Set ex173E0) = ⊤ := by
    rw [eq_top_iff]
    intro ⟨x, hx⟩ _
    have hE0_sf : ex173E0.toSubfield =
        Subfield.closure (Set.range (algebraMap ℚ ℂ) ∪ {ex173AlphaC, ex173ISqrt2}) :=
      adjoin_toSubfield_eq_closure_ch17 ({ex173AlphaC, ex173ISqrt2} : Set ℂ)
    have hsub : ex173E0.toSubfield ≤
        (IntermediateField.adjoin Kα ({iS2E} : Set ex173E0)).toSubfield.map ex173E0.val.toRingHom := by
      rw [hE0_sf, Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · exact ⟨algebraMap Kα ex173E0 (algebraMap ℚ Kα q),
          (IntermediateField.adjoin Kα _).algebraMap_mem _, rfl⟩
      · rcases hy with rfl | rfl
        · exact ⟨algebraMap Kα ex173E0 ⟨αE, IntermediateField.mem_adjoin_simple_self ℚ αE⟩,
            (IntermediateField.adjoin Kα _).algebraMap_mem _, rfl⟩
        · exact ⟨iS2E, IntermediateField.mem_adjoin_simple_self Kα iS2E, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub hx
    have heq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← heq]
  have hfin_E₀_Kα : Module.finrank Kα ex173E0 = 2 := by
    have h1 : Module.finrank Kα (IntermediateField.adjoin Kα ({iS2E} : Set ex173E0)) = 2 := by
      rw [IntermediateField.adjoin.finrank hint_iS2, hmin_iS2, hq2_deg]
    rw [hadj_Kα_E₀] at h1
    exact (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).symm.trans h1
  have htower := Module.finrank_mul_finrank ℚ Kα ex173E0
  rw [hfin_Kα, hfin_E₀_Kα] at htower
  linarith

private theorem ex173_galoisGroup_L2 :
    Nat.card (GarlingGaloisGroup ℚ ex173L2) = 2 ∧
    Nonempty (GarlingGaloisGroup ℚ ex173L2 ≃* Multiplicative (ZMod 2)) := by
  classical
  let αL2 : ex173L2 := ⟨ex173Alpha, IntermediateField.mem_adjoin_simple_self ℚ ex173Alpha⟩
  have hα_pos : (0 : ℝ) < ex173Alpha := Real.sqrt_pos.mpr (by positivity)
  have hαL2_ne_neg : αL2 ≠ -αL2 := by
    intro h
    have h1 : ex173Alpha = -ex173Alpha := congrArg Subtype.val h
    linarith
  have hint_α : IsIntegral ℚ ex173Alpha := ⟨ex173Poly, ex173Poly_monic, ex173_aeval_alpha⟩
  have hneg_aeval : Polynomial.aeval (-αL2) ex173Poly = 0 := by
    apply ex173L2.val.injective
    rw [map_zero]
    change ex173L2.val (Polynomial.aeval (-αL2) ex173Poly) = 0
    rw [← Polynomial.aeval_algHom_apply ex173L2.val (-αL2) ex173Poly]
    change Polynomial.aeval (-ex173Alpha) ex173Poly = 0
    dsimp only [ex173Poly]
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      eq_ratCast, Rat.cast_ofNat]
    have h1 := ex173_aeval_alpha
    dsimp only [ex173Poly] at h1
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      eq_ratCast, Rat.cast_ofNat] at h1
    linarith
  have h_ext : ∀ f g : ex173L2 →ₐ[ℚ] ex173L2, f αL2 = g αL2 → f = g := by
    intro f g hfg
    ext x
    have hsub : ex173L2.toSubfield ≤
        ((AlgHom.equalizer f g).toSubring.toSubmonoid.carrier |> fun _ =>
          ({ (AlgHom.equalizer f g) with
              inv_mem' := fun {a} ha => by
                change f a⁻¹ = g a⁻¹
                rw [map_inv₀, map_inv₀]
                exact congrArg Inv.inv ha } : IntermediateField ℚ ex173L2)).toSubfield.map
          ex173L2.val.toRingHom := by
      have hsf : ex173L2.toSubfield =
          Subfield.closure (Set.range (algebraMap ℚ ℝ) ∪ {ex173Alpha}) :=
        adjoin_toSubfield_eq_closure_ch17 ({ex173Alpha} : Set ℝ)
      rw [hsf, Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · exact ⟨algebraMap ℚ ex173L2 q, by
          change f (algebraMap ℚ ex173L2 q) = g (algebraMap ℚ ex173L2 q)
          rw [f.commutes, g.commutes], rfl⟩
      · rw [Set.mem_singleton_iff] at hy; rw [hy]
        exact ⟨αL2, hfg, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hsub x.2
    have heq : y = x := Subtype.ext hyx
    rw [← heq]
    exact congrArg Subtype.val hy
  let pb := IntermediateField.adjoin.powerBasis hint_α
  have hmin_pb : minpoly ℚ pb.gen = ex173Poly := by
    have h1 := minpoly.algHom_eq ex173L2.val Subtype.val_injective pb.gen
    exact h1.symm.trans ex173_minpoly_alpha
  let τHom : ex173L2 →ₐ[ℚ] ex173L2 := pb.lift (-αL2) (by rw [hmin_pb]; exact hneg_aeval)
  have hτ_α : τHom αL2 = -αL2 := pb.lift_gen (-αL2) _
  have hτ_sq : τHom.comp τHom = AlgHom.id ℚ ex173L2 := by
    apply h_ext
    rw [AlgHom.comp_apply, AlgHom.id_apply, hτ_α, map_neg, hτ_α, neg_neg]
  let τ : ex173L2 ≃ₐ[ℚ] ex173L2 := AlgEquiv.ofAlgHom τHom τHom hτ_sq hτ_sq
  have hτ_ne1 : τ ≠ 1 := by
    intro h
    have h1 : τ αL2 = αL2 := congrArg (fun f : ex173L2 ≃ₐ[ℚ] ex173L2 => f αL2) h
    exact hαL2_ne_neg (h1.symm.trans hτ_α)
  have hτ_mul : τ * τ = 1 := AlgEquiv.ext fun x => AlgHom.congr_fun hτ_sq x
  have hall : ∀ σ : ex173L2 ≃ₐ[ℚ] ex173L2, σ = 1 ∨ σ = τ := by
    intro σ
    have hroot : Polynomial.aeval ((σ αL2 : ex173L2) : ℝ) ex173Poly = 0 := by
      have ha : Polynomial.aeval αL2 ex173Poly = 0 := by
        apply ex173L2.val.injective
        rw [map_zero]
        change ex173L2.val (Polynomial.aeval αL2 ex173Poly) = 0
        rw [← Polynomial.aeval_algHom_apply ex173L2.val αL2 ex173Poly]
        exact ex173_aeval_alpha
      have h1 : Polynomial.aeval (σ αL2) ex173Poly = 0 := by
        change Polynomial.aeval (σ.toAlgHom αL2) ex173Poly = 0
        rw [Polynomial.aeval_algHom_apply σ.toAlgHom αL2 ex173Poly, ha, map_zero]
      have h2 := Polynomial.aeval_algHom_apply ex173L2.val (σ αL2) ex173Poly
      rw [h1, map_zero] at h2
      exact h2
    rcases ex173_real_roots_eq (σ αL2 : ℝ) hroot with hpos | hneg
    · left
      have hσ_α : σ αL2 = αL2 := Subtype.ext hpos
      exact AlgEquiv.coe_toAlgHom_injective (h_ext _ _ (by change σ αL2 = αL2; exact hσ_α))
    · right
      have hσ_α : σ αL2 = -αL2 := Subtype.ext hneg
      exact AlgEquiv.coe_toAlgHom_injective (h_ext _ _ (by
        change σ αL2 = τHom αL2; rw [hσ_α, hτ_α]))
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  let φ : Multiplicative (ZMod 2) →* GarlingGaloisGroup ℚ ex173L2 :=
    { toFun := fun x => if Multiplicative.toAdd x = 0 then 1 else τ
      map_one' := by simp
      map_mul' := fun x y => by
        change (if Multiplicative.toAdd x + Multiplicative.toAdd y = 0 then 1 else τ) =
          (if Multiplicative.toAdd x = 0 then 1 else τ) *
            (if Multiplicative.toAdd y = 0 then 1 else τ)
        rcases hz2 (Multiplicative.toAdd x) with hx | hx <;>
        rcases hz2 (Multiplicative.toAdd y) with hy | hy
        · simp [hx, hy]
        · simp [hx, hy, h10]
        · simp [hx, hy, h10]
        · simp [hx, hy, h10, h11, hτ_mul] }
  have hbij : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun σ => ?_⟩
    · apply Multiplicative.toAdd.injective
      have hxy' : (if Multiplicative.toAdd x = 0 then 1 else τ) =
          (if Multiplicative.toAdd y = 0 then 1 else τ) := hxy
      rcases hz2 (Multiplicative.toAdd x) with hx | hx <;>
      rcases hz2 (Multiplicative.toAdd y) with hy | hy
      · rw [hx, hy]
      · exfalso; rw [hx, hy] at hxy'; exact hτ_ne1 (by simpa [h10] using hxy'.symm)
      · exfalso; rw [hx, hy] at hxy'; exact hτ_ne1 (by simpa [h10] using hxy')
      · rw [hx, hy]
    · rcases hall σ with rfl | rfl
      · exact ⟨Multiplicative.ofAdd (0 : ZMod 2), by simp [φ]⟩
      · exact ⟨Multiplicative.ofAdd (1 : ZMod 2), by simp [φ, h10]⟩
  let e2 : GarlingGaloisGroup ℚ ex173L2 ≃* Multiplicative (ZMod 2) :=
    (MulEquiv.ofBijective φ hbij).symm
  have hcard : Nat.card (GarlingGaloisGroup ℚ ex173L2) = 2 := by
    rw [Nat.card_congr e2.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact ⟨hcard, ⟨e2⟩⟩

/-- **Exercise 17.3 (printed p. 138 / PDF p. 146 — queued in `QUEUE.md` for non-propositional
`"Find..."` prompts; complete solution kernel-proved here):**
*"Let `L_0 = ℚ`, `L_1 = ℚ(3^{1/2})`, `L_2 = ℚ((3^{1/2} + 1)^{1/2})`. Show that `L_1 : L_0` and
`L_2 : L_1` are both normal extensions but that `L_2 : L_0` is not normal. Find the minimal
polynomial of `(3^{1/2} + 1)^{1/2}` over `ℚ`, and find its Galois group."*

Proves every clause:
1. `(ex173L2OverL1 : Set ℝ) = (ex173L2 : Set ℝ)` (`L_2 = L_1(α) = ℚ(α)` with `L_1 ≤ L_2`).
2. `IsGarlingNormal ℚ ex173L1` and `IsGarlingNormal ex173L1 ex173L2OverL1`.
3. `¬ IsGarlingNormal ℚ ex173L2`.
4. `minpoly ℚ ex173Alpha = ex173Poly` (`x^4 - 2x^2 - 2`), which is irreducible of degree `4`.
5. For **every** splitting field `E` of `ex173Poly` over `ℚ` (in any universe), `[E : ℚ] = 8`,
   `|Γ_ℚ(x^4 - 2x^2 - 2)| = 8`, and `Γ_ℚ(x^4 - 2x^2 - 2) ≃* DihedralGroup 4` (`D_4`).
6. Also `|Γ(L_2 : ℚ)| = 2` and `Γ(L_2 : ℚ) ≃* Multiplicative (ZMod 2)` (covering both readings of
   *"its Galois group"*). -/
theorem exercise_17_3 :
    (ex173L2OverL1 : Set ℝ) = (ex173L2 : Set ℝ) ∧
    IsGarlingNormal ℚ ex173L1 ∧
    IsGarlingNormal ex173L1 ex173L2OverL1 ∧
    ¬ IsGarlingNormal ℚ ex173L2 ∧
    minpoly ℚ ex173Alpha = ex173Poly ∧
    Irreducible ex173Poly ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ E],
      IsGarlingSplittingFieldExtension ℚ E ex173Poly →
      Module.finrank ℚ E = 8 ∧
      Nat.card (GarlingPolyGaloisGroup ℚ E ex173Poly) = 8 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ E ex173Poly ≃* DihedralGroup 4)) ∧
    Nat.card (GarlingGaloisGroup ℚ ex173L2) = 2 ∧
    Nonempty (GarlingGaloisGroup ℚ ex173L2 ≃* Multiplicative (ZMod 2)) :=
  ⟨ex173_carrier_eq, ex173_normal_L1, ex173_normal_L21, ex173_not_normal_L2,
    ex173_minpoly_alpha, ex173Poly_irreducible,
    fun E _ _ hsfE => Garling.Chapter11.quartic_galoisGroup_d4_of_splittingField_finrank_eight
      ex173Poly_irreducible.separable ex173Poly_natDegree ex173E0_splittingField ex173E0_finrank
      E hsfE,
    ex173_galoisGroup_L2.1, ex173_galoisGroup_L2.2⟩

/-- Helper: discriminant tuple for a cubic (`n = 3`) is `((α 1 - α 0) * (α 2 - α 0) * (α 2 - α 1))^2`. -/
private theorem garlingDiscTuple_three {L : Type*} [CommRing L] (α : Fin 3 → L) :
    garlingDiscTuple α = ((α 1 - α 0) * (α 2 - α 0) * (α 2 - α 1)) ^ 2 := by
  dsimp only [garlingDiscTuple, garlingDeltaTuple]
  rw [Fin.prod_univ_three]
  have hf0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have hf1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have hf2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  rw [hf0, hf1, hf2, Finset.prod_pair (by decide), Finset.prod_singleton, Finset.prod_empty]
  ring

private theorem garlingDiscTuple_three_perm {L : Type*} [CommRing L] (α : Fin 3 → L)
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    garlingDiscTuple α = ((α i - α j) * (α i - α k) * (α j - α k)) ^ 2 := by
  rw [garlingDiscTuple_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

/-- **Exercise 17.4 (literal, printed p. 138 / PDF p. 146):**
*"Let `f` be an irreducible cubic in `K[x]`, where `K` is a subfield of `ℝ`. Show that `f` has
three real roots if and only if its discriminant is positive."*

Proves the full five-way equivalence between:
1. `{x : ℝ | Polynomial.aeval x f = 0}.ncard = 3` (three distinct real roots),
2. `(f.map (algebraMap K ℝ)).roots.card = 3` (three real roots counted with multiplicity),
3. `GarlingSplitsOver K ℝ f` (`f` splits into linear factors over `ℝ`),
4. `(0 : ℝ) < (garlingDiscriminant f).1` (Garling's discriminant `Δ = ∏_{i < j} (α_j - α_i)^2` is positive),
5. `(0 : ℝ) < (f.leadingCoeff).1 ^ 4 * (garlingDiscriminant f).1` (standard non-monic cubic discriminant `a_3^4 Δ` is positive). -/
theorem exercise_17_4 (K : Subfield ℝ) {f : K[X]} (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) :
    ({x : ℝ | Polynomial.aeval x f = 0}.ncard = 3 ↔ (0 : ℝ) < (garlingDiscriminant f).1) ∧
    ((f.map (algebraMap K ℝ)).roots.card = 3 ↔ (0 : ℝ) < (garlingDiscriminant f).1) ∧
    (GarlingSplitsOver K ℝ f ↔ (0 : ℝ) < (garlingDiscriminant f).1) ∧
    ((0 : ℝ) < (garlingDiscriminant f).1 ↔
      (0 : ℝ) < (f.leadingCoeff).1 ^ 4 * (garlingDiscriminant f).1) := by
  classical
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hlc_ne : (f.leadingCoeff).1 ≠ 0 := by
    intro h0
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0 (Subtype.ext h0)
  have hlc4_pos : (0 : ℝ) < (f.leadingCoeff).1 ^ 4 := by positivity
  have hdisc_equiv : (0 : ℝ) < (garlingDiscriminant f).1 ↔
      (0 : ℝ) < (f.leadingCoeff).1 ^ 4 * (garlingDiscriminant f).1 :=
    ⟨fun h => mul_pos hlc4_pos h, fun h => pos_of_mul_pos_right h (le_of_lt hlc4_pos)⟩
  -- Embed `K → ℝ → ℂ` and split `f` in `ℂ`
  let : Algebra K ℂ := RingHom.toAlgebra (Complex.ofRealHom.comp K.subtype)
  have : IsScalarTower K ℝ ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hspl_C : GarlingSplitsOver K ℂ f :=
    (garlingSplitsOver_iff_splits K ℂ f).mpr (IsAlgClosed.splits _)
  obtain ⟨n, c, α, hexp⟩ := hspl_C
  have hn : n = 3 := by
    have h1 := (garlingSplitsExplicit_props hf0 hexp).2.2.1
    simpa [garlingDegree, hdeg] using h1
  subst hn
  have hc_ne : c ≠ 0 := (garlingSplitsExplicit_props hf0 hexp).2.1
  have hcC_ne : algebraMap K ℂ c ≠ 0 :=
    (map_ne_zero_iff (algebraMap K ℂ) (algebraMap K ℂ).injective).mpr hc_ne
  have hsep_C : (f.map (algebraMap K ℂ)).Separable := hirr.separable.map
  have hdiscC : ((garlingDiscriminant f).1 : ℂ) = garlingDiscTuple α := by
    change algebraMap K ℂ (garlingDiscriminant f) = garlingDiscTuple α
    exact garlingDiscriminant_eq_discTuple hf0 hexp
  have hfac_C : f.map (algebraMap K ℂ) =
      Polynomial.C (algebraMap K ℂ c) * ((Polynomial.X - Polynomial.C (α 0)) *
        (Polynomial.X - Polynomial.C (α 1)) * (Polynomial.X - Polynomial.C (α 2))) := by
    simpa [GarlingSplitsExplicit, Fin.prod_univ_three, mul_assoc] using hexp
  have hα_inj : Function.Injective α := by
    have hnodup : (f.map (algebraMap K ℂ)).roots.Nodup := Polynomial.nodup_roots hsep_C
    have hroots_eq : (f.map (algebraMap K ℂ)).roots = α 0 ::ₘ α 1 ::ₘ α 2 ::ₘ 0 := by
      rw [hfac_C, Polynomial.roots_C_mul _ hcC_ne]
      have hne0 : (Polynomial.X - Polynomial.C (α 0)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
      have hne1 : (Polynomial.X - Polynomial.C (α 1)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
      have hne2 : (Polynomial.X - Polynomial.C (α 2)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
      rw [Polynomial.roots_mul (mul_ne_zero (mul_ne_zero hne0 hne1) hne2),
        Polynomial.roots_mul (mul_ne_zero hne0 hne1),
        Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
      simp
    rw [hroots_eq] at hnodup
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero,
      Multiset.nodup_zero, or_false, not_or, and_true] at hnodup
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  -- Roots of `f` in `ℂ` are exactly `{α 0, α 1, α 2}`
  have hroot_C_iff : ∀ z : ℂ, Polynomial.aeval z f = 0 ↔ z = α 0 ∨ z = α 1 ∨ z = α 2 := by
    intro z
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hfac_C]
    simp [hcC_ne, sub_eq_zero, or_assoc]
  -- Complex conjugation permutes the roots of `f`
  have hconj_root : ∀ z : ℂ, Polynomial.aeval z f = 0 → Polynomial.aeval (starRingEnd ℂ z) f = 0 := by
    intro z hz
    have h1 : Polynomial.aeval (starRingEnd ℂ z) f = starRingEnd ℂ (Polynomial.aeval z f) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      ext a
      exact (Complex.conj_ofReal a.1).symm
    rw [h1, hz, map_zero]
  -- Real roots of `f` correspond bijectively to `α i` with `(α i).im = 0`
  have hreal_root_iff : ∀ x : ℝ, Polynomial.aeval x f = 0 ↔
      (x : ℂ) = α 0 ∨ (x : ℂ) = α 1 ∨ (x : ℂ) = α 2 := by
    intro x
    rw [← hroot_C_iff (x : ℂ)]
    have h1 : Polynomial.aeval (x : ℂ) f = ((Polynomial.aeval x f : ℝ) : ℂ) := by
      change Polynomial.eval₂ (algebraMap K ℂ) (Complex.ofRealHom x) f =
        Complex.ofRealHom (Polynomial.eval₂ (algebraMap K ℝ) x f)
      rw [Polynomial.hom_eval₂]
      rfl
    rw [h1, Complex.ofReal_eq_zero]
  -- Case split on whether all three roots in `ℂ` are real
  by_cases hall_real : ∀ i : Fin 3, (α i).im = 0
  · -- All three roots are real
    let r : Fin 3 → ℝ := fun i => (α i).re
    have hrC : ∀ i : Fin 3, (r i : ℂ) = α i := fun i =>
      Complex.ext rfl (by simp [hall_real i])
    have hr_inj : Function.Injective r := fun i j hij =>
      hα_inj (by rw [← hrC i, ← hrC j, hij])
    have hdisc_pos : (0 : ℝ) < (garlingDiscriminant f).1 := by
      have h1 : ((garlingDiscriminant f).1 : ℂ) =
          ((((r 1 - r 0) * (r 2 - r 0) * (r 2 - r 1)) ^ 2 : ℝ) : ℂ) := by
        rw [hdiscC, garlingDiscTuple_three]
        simp only [← hrC, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub]
      have h2 := Complex.ofReal_injective h1
      rw [h2]
      refine sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
      · exact sub_ne_zero.mpr fun h => absurd (hr_inj h) (by decide)
      · exact sub_ne_zero.mpr fun h => absurd (hr_inj h) (by decide)
      · exact sub_ne_zero.mpr fun h => absurd (hr_inj h) (by decide)
    have hncard3 : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3 := by
      have hset : {x : ℝ | Polynomial.aeval x f = 0} = Set.range r := by
        ext x
        simp only [Set.mem_ofPred_eq, hreal_root_iff, Set.mem_range]
        constructor
        · rintro (h | h | h)
          · exact ⟨0, Complex.ofReal_injective ((hrC 0).trans h.symm)⟩
          · exact ⟨1, Complex.ofReal_injective ((hrC 1).trans h.symm)⟩
          · exact ⟨2, Complex.ofReal_injective ((hrC 2).trans h.symm)⟩
        · rintro ⟨i, rfl⟩
          fin_cases i
          · exact Or.inl (hrC 0)
          · exact Or.inr (Or.inl (hrC 1))
          · exact Or.inr (Or.inr (hrC 2))
      rw [hset, Set.ncard_range_of_injective hr_inj, Nat.card_fin]
    have hspl_R : GarlingSplitsOver K ℝ f := by
      refine ⟨3, f.leadingCoeff, r, ?_⟩
      apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
      rw [Polynomial.map_map]
      have hcomp : Complex.ofRealHom.comp (algebraMap K ℝ) = algebraMap K ℂ := rfl
      rw [hcomp, hexp]
      have hc_eq : c = f.leadingCoeff := (garlingSplitsExplicit_props hf0 hexp).1
      rw [hc_eq, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
      refine congrArg₂ (· * ·) rfl ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      change Polynomial.X - Polynomial.C (α i) = Polynomial.X - Polynomial.C (r i : ℂ)
      rw [hrC i]
    have hroots3 : (f.map (algebraMap K ℝ)).roots.card = 3 := by
      have hs := (garlingSplitsOver_iff_splits K ℝ f).mp hspl_R
      rw [← hs.natDegree_eq_card_roots, Polynomial.natDegree_map, hdeg]
    exact ⟨⟨fun _ => hdisc_pos, fun _ => hncard3⟩,
      ⟨fun _ => hdisc_pos, fun _ => hroots3⟩,
      ⟨fun _ => hdisc_pos, fun _ => hspl_R⟩,
      hdisc_equiv⟩
  · -- At least one non-real root: conjugate pair + one real root ⇒ Δ < 0 and only 1 real root
    push Not at hall_real
    obtain ⟨i, hi_im⟩ := hall_real
    have hconj_ne : starRingEnd ℂ (α i) ≠ α i := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.conj_im] at him
      exact hi_im (by linarith)
    have hi_root : Polynomial.aeval (α i) f = 0 := by
      rw [hroot_C_iff]; fin_cases i <;> simp
    have hconj_mem : ∃ j : Fin 3, starRingEnd ℂ (α i) = α j := by
      rcases (hroot_C_iff _).mp (hconj_root _ hi_root) with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    obtain ⟨j, hj_eq⟩ := hconj_mem
    have hij : i ≠ j := fun h => hconj_ne (by rw [hj_eq, h])
    have hk_ex : ∀ a b : Fin 3, a ≠ b → ∃ k : Fin 3, k ≠ a ∧ k ≠ b := by decide
    obtain ⟨k, hki, hkj⟩ := hk_ex i j hij
    have hk_root : Polynomial.aeval (α k) f = 0 := by
      rw [hroot_C_iff]; fin_cases k <;> simp
    have hk_conj_mem : ∃ l : Fin 3, starRingEnd ℂ (α k) = α l := by
      rcases (hroot_C_iff _).mp (hconj_root _ hk_root) with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    obtain ⟨l, hl_eq⟩ := hk_conj_mem
    have hfin3_two : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ c → d = a ∨ d = b := by decide
    have hl_eq_k : l = k := by
      by_contra hlk
      rcases hfin3_two i j k l hij hki hkj hlk with rfl | rfl
      · have h1 := congrArg (starRingEnd ℂ) hl_eq
        simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
        rw [hj_eq] at h1
        exact hkj (hα_inj h1)
      · have h1 := congrArg (starRingEnd ℂ) hl_eq
        simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
        rw [← hj_eq, starRingEnd_self_apply] at h1
        exact hki (hα_inj h1)
    have hk_conj : starRingEnd ℂ (α k) = α k := hl_eq_k ▸ hl_eq
    have hk_im : (α k).im = 0 := by
      have him := congrArg Complex.im hk_conj
      simp only [Complex.conj_im] at him
      linarith
    -- Compute `Δ = -4 b² ((a - r)² + b²)² < 0`
    have hdisc_neg : (garlingDiscriminant f).1 < 0 := by
      have hperm : garlingDiscTuple α = ((α i - α j) * (α i - α k) * (α j - α k)) ^ 2 :=
        garlingDiscTuple_three_perm α hij hki hkj
      let a : ℝ := (α i).re
      let b : ℝ := (α i).im
      let r : ℝ := (α k).re
      have hαi : α i = (a : ℂ) + (b : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [a, b]
      have hαj : α j = (a : ℂ) - (b : ℂ) * Complex.I := by
        rw [← hj_eq, hαi]
        apply Complex.ext <;> simp
      have hαk : α k = (r : ℂ) := by
        apply Complex.ext <;> simp [r, hk_im]
      have hprod_eq : (α i - α j) * (α i - α k) * (α j - α k) =
          (2 * (b : ℂ) * Complex.I) * (((a : ℂ) - (r : ℂ)) ^ 2 + (b : ℂ) ^ 2) := by
        rw [hαi, hαj, hαk]
        linear_combination -(2 * (b : ℂ) ^ 3 * Complex.I) * Complex.I_sq
      have hvalC : ((garlingDiscriminant f).1 : ℂ) =
          (((-4 * b ^ 2 * ((a - r) ^ 2 + b ^ 2) ^ 2) : ℝ) : ℂ) := by
        rw [hdiscC, hperm, hprod_eq]
        simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
          Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub]
        linear_combination (4 * (b : ℂ) ^ 2 * (((a : ℂ) - (r : ℂ)) ^ 2 + (b : ℂ) ^ 2) ^ 2) *
          Complex.I_sq
      have hvalR := Complex.ofReal_injective hvalC
      rw [hvalR]
      have hb2 : (0 : ℝ) < b ^ 2 := sq_pos_of_ne_zero hi_im
      have hsum : (0 : ℝ) < (a - r) ^ 2 + b ^ 2 := by positivity
      have hsum2 : (0 : ℝ) < ((a - r) ^ 2 + b ^ 2) ^ 2 := by positivity
      nlinarith
    have hnot_pos : ¬ ((0 : ℝ) < (garlingDiscriminant f).1) := not_lt.mpr (le_of_lt hdisc_neg)
    have hj_im : (α j).im ≠ 0 := by
      rw [← hj_eq, Complex.conj_im]; exact neg_ne_zero.mpr hi_im
    have hfin3_all : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d = a ∨ d = b ∨ d = c := by decide
    have hreal_only_k : ∀ x : ℝ, Polynomial.aeval x f = 0 → x = (α k).re := by
      intro x hx
      have hx_ex : ∃ m : Fin 3, (x : ℂ) = α m := by
        rcases (hreal_root_iff x).mp hx with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      obtain ⟨m, hm⟩ := hx_ex
      rcases hfin3_all i j k m hij hki hkj with rfl | rfl | rfl
      · exfalso; exact hi_im (by rw [← hm]; exact Complex.ofReal_im x)
      · exfalso; exact hj_im (by rw [← hm]; exact Complex.ofReal_im x)
      · exact congrArg Complex.re hm
    have hncard_ne3 : {x : ℝ | Polynomial.aeval x f = 0}.ncard ≠ 3 := by
      have hsub : {x : ℝ | Polynomial.aeval x f = 0} ⊆ {(α k).re} :=
        fun x hx => Set.mem_singleton_iff.mpr (hreal_only_k x hx)
      have hle1 : {x : ℝ | Polynomial.aeval x f = 0}.ncard ≤ 1 := by
        calc {x : ℝ | Polynomial.aeval x f = 0}.ncard
            ≤ ({(α k).re} : Set ℝ).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton _)
          _ = 1 := Set.ncard_singleton _
      omega
    have hroots_ne3 : (f.map (algebraMap K ℝ)).roots.card ≠ 3 := by
      have hnodup : (f.map (algebraMap K ℝ)).roots.Nodup :=
        Polynomial.nodup_roots hirr.separable.map
      have hsub : (f.map (algebraMap K ℝ)).roots.toFinset ⊆ {(α k).re} := by
        intro x hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots
          ((Polynomial.map_ne_zero_iff (algebraMap K ℝ).injective).mpr hf0),
          Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def] at hx
        exact Finset.mem_singleton.mpr (hreal_only_k x hx)
      have hle1 : (f.map (algebraMap K ℝ)).roots.card ≤ 1 := by
        calc (f.map (algebraMap K ℝ)).roots.card
            = (f.map (algebraMap K ℝ)).roots.toFinset.card :=
              (Multiset.toFinset_card_of_nodup hnodup).symm
          _ ≤ ({(α k).re} : Finset ℝ).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
      omega
    have hnot_spl : ¬ GarlingSplitsOver K ℝ f := by
      intro hs
      have h1 := ((garlingSplitsOver_iff_splits K ℝ f).mp hs).natDegree_eq_card_roots
      rw [Polynomial.natDegree_map, hdeg] at h1
      exact hroots_ne3 h1.symm
    exact ⟨⟨fun h => (hncard_ne3 h).elim, fun h => (hnot_pos h).elim⟩,
      ⟨fun h => (hroots_ne3 h).elim, fun h => (hnot_pos h).elim⟩,
      ⟨fun h => (hnot_spl h).elim, fun h => (hnot_pos h).elim⟩,
      hdisc_equiv⟩

/-- **Exercise 17.5 (literal, printed p. 138 / PDF p. 146):**
*"Suppose that `K` is a subfield of `ℝ` and that `f` is an irreducible cubic in `K[x]` with three
real roots. Suppose that `L = K(r)`, where `r ∈ ℝ` and `r^p ∈ K` for some prime `p`. Show that `f`
is irreducible over `L`."* -/
theorem exercise_17_5 (K : Subfield ℝ) {f : K[X]} (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) (hroots : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3)
    {r : ℝ} {p : ℕ} (hp : Nat.Prime p) (hrp : r ^ p ∈ K) :
    Irreducible (f.map (algebraMap K (IntermediateField.adjoin K ({r} : Set ℝ)))) := by
  classical
  let L : IntermediateField K ℝ := IntermediateField.adjoin K ({r} : Set ℝ)
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hfL0 : f.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  have hfL_deg : (f.map (algebraMap K L)).natDegree = 3 := by
    rw [Polynomial.natDegree_map, hdeg]
  by_contra hred
  -- Step 1: A reducible cubic over a field has a root `α ∈ L`
  have hnot_unit : ¬ IsUnit (f.map (algebraMap K L)) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have hroot_ex : ∃ α : L, Polynomial.aeval α f = 0 := by
    rw [irreducible_iff] at hred
    push Not at hred
    obtain ⟨g, h, hgh, hgnu, hhnu⟩ := hred hnot_unit
    have hg0 : g ≠ 0 := fun h0 => hfL0 (by rw [hgh, h0, zero_mul])
    have hh0 : h ≠ 0 := fun h0 => hfL0 (by rw [hgh, h0, mul_zero])
    have hg_pos : 1 ≤ g.natDegree := by
      by_contra h0
      have hd0 : g.natDegree = 0 := by omega
      exact hgnu (Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hg0, hd0]; rfl))
    have hh_pos : 1 ≤ h.natDegree := by
      by_contra h0
      have hd0 : h.natDegree = 0 := by omega
      exact hhnu (Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hh0, hd0]; rfl))
    have hdeg_sum : g.natDegree + h.natDegree = 3 := by
      rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hfL_deg]
    have hlin_root : ∀ q : L[X], q.natDegree = 1 → q ∣ f.map (algebraMap K L) →
        ∃ α : L, Polynomial.aeval α f = 0 := by
      intro q hqd hdvd
      let a1 : L := q.coeff 1
      let a0 : L := q.coeff 0
      have hq1_ne : a1 ≠ 0 := by
        dsimp only [a1]; rw [← hqd]
        exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; simp [h0] at hqd)
      refine ⟨-a0 / a1, ?_⟩
      have hq_eq : q = Polynomial.C a1 * Polynomial.X + Polynomial.C a0 :=
        Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hqd))
      have hq_eval : q.eval (-a0 / a1) = 0 := by
        rw [hq_eq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        field_simp [hq1_ne]
        ring
      rcases hdvd with ⟨u, hu⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hu, Polynomial.eval_mul, hq_eval,
        zero_mul]
    by_cases hg1 : g.natDegree = 1
    · exact hlin_root g hg1 ⟨h, hgh⟩
    · exact hlin_root h (by omega) ⟨g, by rw [hgh, mul_comm]⟩
  obtain ⟨α, hα_root⟩ := hroot_ex
  -- Step 2: `3 ∣ [L : K]` since `[K(α) : K] = 3`
  let Kα : IntermediateField K L := IntermediateField.adjoin K ({α} : Set L)
  have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  let f_mon : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hf_mon_mon : f_mon.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc_ne]
  have hf_mon_irr : Irreducible f_mon := by
    have hunit : IsUnit (Polynomial.C f.leadingCoeff⁻¹ : K[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc_ne))
    have hassoc : Associated f f_mon := ⟨hunit.unit, by simp [f_mon, mul_comm]⟩
    exact hassoc.irreducible hirr
  have hf_mon_deg : f_mon.natDegree = 3 := by
    dsimp only [f_mon]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_ne), hdeg]
  have hf_mon_aeval : Polynomial.aeval α f_mon = 0 := by
    dsimp only [f_mon]; rw [map_mul, hα_root, mul_zero]
  have hmin_α : minpoly K α = f_mon :=
    (minpoly.eq_of_irreducible_of_monic hf_mon_irr hf_mon_aeval hf_mon_mon).symm
  have hint_α : IsIntegral K α :=
    ⟨f_mon, hf_mon_mon, by rw [← Polynomial.aeval_def]; exact hf_mon_aeval⟩
  have hfin_Kα : Module.finrank K Kα = 3 := by
    rw [IntermediateField.adjoin.finrank hint_α, hmin_α, hf_mon_deg]
  -- Step 3: `X^p - θ` is irreducible over `K`, forcing `p = 3` and `K(α) = L`
  let θ : K := ⟨r ^ p, hrp⟩
  have hxp_no_root : ¬ ∃ c : K, (Polynomial.X ^ p - Polynomial.C θ).eval c = 0 := by
    rintro ⟨c, hc⟩
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hc
    have hpow_R : (c : ℝ) ^ p = r ^ p := congrArg Subtype.val hc
    have hr_mem_K : r ∈ K := by
      by_cases hp2 : p = 2
      · subst hp2
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpow_R with h | h
        · exact h ▸ c.2
        · have hneg : r = -(c : ℝ) := by linarith
          exact hneg ▸ K.neg_mem c.2
      · have hodd : Odd p := hp.odd_of_ne_two hp2
        have hcr : (c : ℝ) = r := hodd.strictMono_pow.injective hpow_R
        exact hcr ▸ c.2
    have hL_bot : L = ⊥ := by
      apply le_antisymm _ bot_le
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨⟨r, hr_mem_K⟩, rfl⟩
    have hfin_L1 : Module.finrank K L = 1 := by
      rw [hL_bot]
      exact IntermediateField.finrank_bot
    have hdvd3 : 3 ∣ Module.finrank K L := by
      rw [← hfin_Kα]
      exact ⟨Module.finrank Kα L, (Module.finrank_mul_finrank K Kα L).symm⟩
    rw [hfin_L1] at hdvd3
    exact absurd (Nat.le_of_dvd (by decide) hdvd3) (by decide)
  have hcharK : ringChar K ≠ p := by
    rw [ringChar.eq_zero]
    exact hp.ne_zero.symm
  have hxp_irr : Irreducible (Polynomial.X ^ p - Polynomial.C θ : K[X]) :=
    (Garling.Chapter16.theorem_16_2_part1_unconditional hp θ hcharK).resolve_right
      (fun h => hxp_no_root h.1) |>.1
  have hxp_mon : (Polynomial.X ^ p - Polynomial.C θ : K[X]).Monic :=
    Polynomial.monic_X_pow_sub_C θ hp.ne_zero
  have hxp_aeval : Polynomial.aeval r (Polynomial.X ^ p - Polynomial.C θ) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero]
    rfl
  have hmin_r : minpoly K r = Polynomial.X ^ p - Polynomial.C θ :=
    (minpoly.eq_of_irreducible_of_monic hxp_irr hxp_aeval hxp_mon).symm
  have hint_r : IsIntegral K r := ⟨Polynomial.X ^ p - Polynomial.C θ, hxp_mon, hxp_aeval⟩
  have hfin_L : Module.finrank K L = p := by
    rw [IntermediateField.adjoin.finrank hint_r, hmin_r, Polynomial.natDegree_X_pow_sub_C]
  have hdvd3p : 3 ∣ p := by
    rw [← hfin_L, ← hfin_Kα]
    exact ⟨Module.finrank Kα L, (Module.finrank_mul_finrank K Kα L).symm⟩
  have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd3p).symm
  subst hp3
  have hKα_top : Kα = ⊤ := by
    have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hint_r
    have hle : Kα.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        change Module.finrank K Kα = Module.finrank K L
        rw [hfin_Kα, hfin_L])
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    change x ∈ Kα.toSubmodule
    rw [hle]
    trivial
  -- Step 4: `r ∈ K(α) ≤ N`, where `N ⊆ ℝ` is the splitting field of `f` over `K`
  have hspl_R : GarlingSplitsOver K ℝ f :=
    ((exercise_17_4 K hirr hdeg).2.2.1).mpr (((exercise_17_4 K hirr hdeg).1).mp hroots)
  obtain ⟨_, cR, αR, hexpR⟩ := hspl_R
  let N : IntermediateField K ℝ := IntermediateField.adjoin K (Set.range αR)
  have hsf_N : IsGarlingSplittingFieldExtension K N f := theorem_7_1 hf0 hexpR
  have hsp_N : Polynomial.IsSplittingField K N f :=
    (isGarlingSplittingFieldExtension_iff K N f).mp hsf_N
  have hnorm_N : Normal K N := Normal.of_isSplittingField f
  have hαR_mem_N : (α : ℝ) ∈ N := by
    have hα_rootR : Polynomial.aeval (α : ℝ) f = 0 := by
      have h1 := Polynomial.aeval_algHom_apply L.val α f
      rw [hα_root, map_zero] at h1
      exact h1
    have h1 := (Polynomial.aeval_def (α : ℝ) f).symm.trans hα_rootR
    rw [Polynomial.eval₂_eq_eval_map, hexpR, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod] at h1
    have hc_ne : algebraMap K ℝ cR ≠ 0 :=
      (map_ne_zero_iff (algebraMap K ℝ) (algebraMap K ℝ).injective).mpr
        (garlingSplitsExplicit_props hf0 hexpR).2.1
    rcases mul_eq_zero.mp h1 with hc0 | hprod0
    · exact absurd hc0 hc_ne
    · rw [Finset.prod_eq_zero_iff] at hprod0
      obtain ⟨idx, _, hidx⟩ := hprod0
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hidx
      rw [hidx]
      exact IntermediateField.subset_adjoin K (Set.range αR) ⟨idx, rfl⟩
  have hL_le_N : L ≤ N := by
    have hr_in_Kα : (⟨r, IntermediateField.mem_adjoin_simple_self K r⟩ : L) ∈ Kα :=
      hKα_top.symm ▸ IntermediateField.mem_top
    have hsub : Kα.toSubfield.map L.val.toRingHom ≤ N.toSubfield := by
      dsimp only [Kα]
      rw [Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | hy)
      · exact N.algebraMap_mem c
      · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hαR_mem_N
    have hr_N : r ∈ N := hsub ⟨⟨r, IntermediateField.mem_adjoin_simple_self K r⟩, hr_in_Kα, rfl⟩
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hr_N
  -- Step 5: `X^3 - θ` splits over `N ⊆ ℝ` with 3 distinct roots, contradicting injectivity of `x ↦ x^3` on `ℝ`
  let rN : N := ⟨r, hL_le_N (IntermediateField.mem_adjoin_simple_self K r)⟩
  have hmin_rN : minpoly K rN = Polynomial.X ^ 3 - Polynomial.C θ := by
    have h1 := minpoly.algHom_eq N.val Subtype.val_injective rN
    exact h1.symm.trans hmin_r
  have hspl_N : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K N)).Splits := by
    rw [← hmin_rN]
    exact Normal.splits hnorm_N rN
  have hspl_cube_R : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).Splits := by
    have hm : (Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ) =
        ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K N)).map N.val.toRingHom := by
      rw [Polynomial.map_map]; rfl
    rw [hm]
    exact Polynomial.Splits.map hspl_N N.val.toRingHom
  have hcard3 : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.card = 3 := by
    rw [← hspl_cube_R.natDegree_eq_card_roots, Polynomial.natDegree_map,
      Polynomial.natDegree_X_pow_sub_C]
  have hnodup3 : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.Nodup :=
    Polynomial.nodup_roots hxp_irr.separable.map
  have hsub1 : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.toFinset ⊆
      {r} := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (algebraMap K ℝ).injective).mpr hxp_mon.ne_zero),
      Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def,
      map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hx
    have hpow : x ^ 3 = r ^ 3 := hx
    exact Finset.mem_singleton.mpr ((by decide : Odd 3).strictMono_pow.injective hpow)
  have hle1 : ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.card ≤ 1 := by
    calc ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.card
        = ((Polynomial.X ^ 3 - Polynomial.C θ : K[X]).map (algebraMap K ℝ)).roots.toFinset.card :=
          (Multiset.toFinset_card_of_nodup hnodup3).symm
      _ ≤ ({r} : Finset ℝ).card := Finset.card_le_card hsub1
      _ = 1 := Finset.card_singleton r
  omega

/-- Helper for `Exercise 17.6`: adjoining a single real `n`-th root (`n ≥ 1`) preserves
irreducibility of any irreducible cubic `f ∈ K[x]` (`K ≤ ℝ`) with three real roots. -/
private theorem exercise_17_6_single_step :
    ∀ (n : ℕ), 1 ≤ n → ∀ (K : Subfield ℝ) (f : K[X]),
      Irreducible f → f.natDegree = 3 →
      {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3 →
      ∀ (β : ℝ), β ^ n ∈ K →
      Irreducible (f.map (algebraMap K (IntermediateField.adjoin K ({β} : Set ℝ)))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn K f hirr hdeg hroots β hβn
    by_cases hn1 : n = 1
    · subst hn1
      have hβK : β ∈ K := by simpa using hβn
      have hbot : IntermediateField.adjoin K ({β} : Set ℝ) = ⊥ := by
        apply le_antisymm _ bot_le
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact ⟨⟨β, hβK⟩, rfl⟩
      let e : K ≃+* IntermediateField.adjoin K ({β} : Set ℝ) :=
        RingEquiv.ofBijective (algebraMap K (IntermediateField.adjoin K ({β} : Set ℝ)))
          ⟨(algebraMap K _).injective, fun ⟨x, hx⟩ => by
            rw [hbot] at hx
            rcases hx with ⟨c, hc⟩
            exact ⟨c, Subtype.ext hc⟩⟩
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mpr hirr
    · have hn_gt1 : 1 < n := by omega
      let p : ℕ := n.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have hp_dvd : p ∣ n := Nat.minFac_dvd n
      let m : ℕ := n / p
      have hm_mul : p * m = n := Nat.mul_div_cancel' hp_dvd
      have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp.pos
      have hm_lt : m < n := Nat.div_lt_self (by omega) hp.one_lt
      let r : ℝ := β ^ m
      have hrp : r ^ p ∈ K := by
        have h1 : r ^ p = β ^ n := by
          dsimp only [r]; rw [← pow_mul, mul_comm, hm_mul]
        rwa [h1]
      have hirr1 : Irreducible (f.map (algebraMap K (IntermediateField.adjoin K ({r} : Set ℝ)))) :=
        exercise_17_5 K hirr hdeg hroots hp hrp
      let K1 : Subfield ℝ := (IntermediateField.adjoin K ({r} : Set ℝ)).toSubfield
      have hK_le_K1 : K ≤ K1 := fun x hx =>
        (IntermediateField.adjoin K ({r} : Set ℝ)).algebraMap_mem ⟨x, hx⟩
      let f1 : K1[X] := f.map (Subfield.inclusion hK_le_K1)
      have hirr_f1 : Irreducible f1 := hirr1
      have hdeg_f1 : f1.natDegree = 3 := by
        dsimp only [f1]; rw [Polynomial.natDegree_map, hdeg]
      have hroots_f1 : {x : ℝ | Polynomial.aeval x f1 = 0}.ncard = 3 := by
        have hset : {x : ℝ | Polynomial.aeval x f1 = 0} = {x : ℝ | Polynomial.aeval x f = 0} := by
          ext x
          simp only [Set.mem_ofPred_eq, f1, Polynomial.aeval_def, Polynomial.eval₂_map]
          rfl
        rwa [hset]
      have hβm_K1 : β ^ m ∈ K1 :=
        IntermediateField.mem_adjoin_simple_self K r
      have hirr2 : Irreducible (f1.map (algebraMap K1 (IntermediateField.adjoin K1 ({β} : Set ℝ)))) :=
        ih m hm_lt hm_pos K1 f1 hirr_f1 hdeg_f1 hroots_f1 β hβm_K1
      -- Show `(IntermediateField.adjoin K1 {β}).toSubfield = (IntermediateField.adjoin K {β}).toSubfield`
      have hsf_eq : (IntermediateField.adjoin K1 ({β} : Set ℝ)).toSubfield =
          (IntermediateField.adjoin K ({β} : Set ℝ)).toSubfield := by
        apply le_antisymm
        · rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro x (⟨y, rfl⟩ | hxβ)
          · have hK1_le : K1 ≤ (IntermediateField.adjoin K ({β} : Set ℝ)).toSubfield := by
              dsimp only [K1]
              rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
              rintro z (⟨c, rfl⟩ | hzr)
              · exact (IntermediateField.adjoin K ({β} : Set ℝ)).algebraMap_mem c
              · rw [Set.mem_singleton_iff] at hzr; rw [hzr]
                exact pow_mem (IntermediateField.mem_adjoin_simple_self K β) m
            exact hK1_le y.2
          · rw [Set.mem_singleton_iff] at hxβ; rw [hxβ]
            exact IntermediateField.mem_adjoin_simple_self K β
        · rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro x (⟨c, rfl⟩ | hxβ)
          · exact (IntermediateField.adjoin K1 ({β} : Set ℝ)).algebraMap_mem ⟨c.1, hK_le_K1 c.2⟩
          · rw [Set.mem_singleton_iff] at hxβ; rw [hxβ]
            exact IntermediateField.mem_adjoin_simple_self K1 β
      let e2 : IntermediateField.adjoin K1 ({β} : Set ℝ) ≃+*
          IntermediateField.adjoin K ({β} : Set ℝ) :=
        { toFun := fun x => ⟨x.1, by
            change x.1 ∈ (IntermediateField.adjoin K ({β} : Set ℝ)).toSubfield
            rw [← hsf_eq]; exact x.2⟩
          invFun := fun x => ⟨x.1, by
            change x.1 ∈ (IntermediateField.adjoin K1 ({β} : Set ℝ)).toSubfield
            rw [hsf_eq]; exact x.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_mul' := fun _ _ => Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl }
      have hmap_eq : (f1.map (algebraMap K1 (IntermediateField.adjoin K1 ({β} : Set ℝ)))).map e2.toRingHom =
          f.map (algebraMap K (IntermediateField.adjoin K ({β} : Set ℝ))) := by
        dsimp only [f1]
        rw [Polynomial.map_map, Polynomial.map_map]
        rfl
      rw [← hmap_eq]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e2).toMulEquiv).mpr hirr2

/-- **Exercise 17.6 (literal, printed p. 138 / PDF p. 146 — `IntermediateField K ℝ` form):**
*"Suppose that `K` is a subfield of `ℝ` and that `f` is an irreducible cubic in `K[x]` with three
real roots. Show that if `L : K` is an extension by radicals with `L ⊆ ℝ` then `f` is irreducible
over `L`. (It is not possible to solve `f` only by extracting real roots!)"* -/
theorem exercise_17_6 (K : Subfield ℝ) {f : K[X]} (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) (hroots : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3)
    (L : IntermediateField K ℝ) (hrad : IsGarlingExtensionByRadicals K L) :
    Irreducible (f.map (algebraMap K L)) := by
  classical
  rcases hrad with ⟨r, F, β, h0, hlast, hstep⟩
  -- Map each intermediate field `F j` of `L : K` to a `Subfield ℝ`
  let S : Fin (r + 1) → Subfield ℝ := fun j => (F j).toSubfield.map L.val.toRingHom
  have hS0 : S 0 = K := by
    ext x
    simp only [S, h0, Subfield.mem_map, IntermediateField.mem_toSubfield, IntermediateField.mem_bot]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact c.2
    · intro hx; exact ⟨algebraMap K L ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hSlast : S (Fin.last r) = L.toSubfield := by
    ext x
    simp only [S, hlast, Subfield.mem_map, IntermediateField.mem_toSubfield, IntermediateField.mem_top,
      true_and]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hK_le_S : ∀ j : Fin (r + 1), K ≤ S j := fun j x hx =>
    ⟨algebraMap K L ⟨x, hx⟩, (F j).algebraMap_mem ⟨x, hx⟩, rfl⟩
  have hirr_S : ∀ k : ℕ, (hk : k ≤ r) →
      Irreducible (f.map (Subfield.inclusion (hK_le_S ⟨k, by omega⟩))) := by
    intro k
    induction k with
    | zero =>
      intro _
      let e0 : K ≃+* S 0 :=
        { toFun := Subfield.inclusion (hK_le_S 0)
          invFun := fun x => ⟨x.1, hS0 ▸ x.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_mul' := fun _ _ => Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl }
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e0).toMulEquiv).mpr hirr
    | succ t iht =>
      intro ht
      let idx : Fin r := ⟨t, by omega⟩
      have hIH : Irreducible (f.map (Subfield.inclusion (hK_le_S idx.castSucc))) := iht (by omega)
      obtain ⟨⟨n, hn, hpow⟩, hadj⟩ := hstep idx
      let Ki : Subfield ℝ := S idx.castSucc
      let fi : Ki[X] := f.map (Subfield.inclusion (hK_le_S idx.castSucc))
      have hdeg_fi : fi.natDegree = 3 := by
        dsimp only [fi]; rw [Polynomial.natDegree_map, hdeg]
      have hroots_fi : {x : ℝ | Polynomial.aeval x fi = 0}.ncard = 3 := by
        have hset : {x : ℝ | Polynomial.aeval x fi = 0} = {x : ℝ | Polynomial.aeval x f = 0} := by
          ext x
          simp only [Set.mem_ofPred_eq, fi, Polynomial.aeval_def, Polynomial.eval₂_map]
          rfl
        rwa [hset]
      have hβn : ((β idx : L) : ℝ) ^ n ∈ Ki :=
        ⟨(β idx) ^ n, hpow, map_pow L.val (β idx) n⟩
      have hstep_irr : Irreducible
          (fi.map (algebraMap Ki (IntermediateField.adjoin Ki ({((β idx : L) : ℝ)} : Set ℝ)))) :=
        exercise_17_6_single_step n hn Ki fi hIH hdeg_fi hroots_fi ((β idx : L) : ℝ) hβn
      -- Show `(IntermediateField.adjoin Ki {β idx}).toSubfield = S idx.succ`
      have hsf_eq : (IntermediateField.adjoin Ki ({((β idx : L) : ℝ)} : Set ℝ)).toSubfield =
          S idx.succ := by
        apply le_antisymm
        · rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
          rintro x (⟨y, rfl⟩ | hxβ)
          · obtain ⟨z, hz, hzx⟩ := y.2
            refine ⟨z, ?_, hzx⟩
            change z ∈ F idx.succ
            rw [hadj]
            exact IntermediateField.subset_adjoin K _ (Or.inl hz)
          · rw [Set.mem_singleton_iff] at hxβ; rw [hxβ]
            refine ⟨β idx, ?_, rfl⟩
            change β idx ∈ F idx.succ
            rw [hadj]
            exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
        · dsimp only [S]
          rw [hadj, Subfield.map_le_iff_le_comap, adjoin_toSubfield_eq_closure_ch17,
            Subfield.closure_le]
          rintro y (⟨c, rfl⟩ | hyF | hyβ)
          · exact (IntermediateField.adjoin Ki _).algebraMap_mem ⟨c.1, hK_le_S idx.castSucc c.2⟩
          · exact (IntermediateField.adjoin Ki _).algebraMap_mem ⟨(y : ℝ), ⟨y, hyF, rfl⟩⟩
          · rw [Set.mem_singleton_iff] at hyβ; rw [hyβ]
            exact IntermediateField.mem_adjoin_simple_self Ki ((β idx : L) : ℝ)
      let e_step : IntermediateField.adjoin Ki ({((β idx : L) : ℝ)} : Set ℝ) ≃+* S idx.succ :=
        { toFun := fun x => ⟨x.1, by rw [← hsf_eq]; exact x.2⟩
          invFun := fun x => ⟨x.1, by
            change x.1 ∈ (IntermediateField.adjoin Ki ({((β idx : L) : ℝ)} : Set ℝ)).toSubfield
            rw [hsf_eq]; exact x.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_mul' := fun _ _ => Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl }
      have hmap_eq : (fi.map (algebraMap Ki
            (IntermediateField.adjoin Ki ({((β idx : L) : ℝ)} : Set ℝ)))).map e_step.toRingHom =
          f.map (Subfield.inclusion (hK_le_S ⟨t + 1, by omega⟩)) := by
        dsimp only [fi]
        rw [Polynomial.map_map, Polynomial.map_map]
        rfl
      rw [← hmap_eq]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e_step).toMulEquiv).mpr hstep_irr
  have hlast_irr := hirr_S r (le_refl r)
  let eL : S (Fin.last r) ≃+* L :=
    { toFun := fun x => ⟨x.1, by
        change x.1 ∈ L.toSubfield
        rw [← hSlast]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [hSlast]; exact x.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hmap_L : (f.map (Subfield.inclusion (hK_le_S (Fin.last r)))).map eL.toRingHom =
      f.map (algebraMap K L) := by
    rw [Polynomial.map_map]
    rfl
  rw [← hmap_L]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv eL).toMulEquiv).mpr hlast_irr

/-- **Exercise 17.6 (`Subfield ℝ` inclusion variant):** if `K ≤ L` are subfields of `ℝ` with `L : K`
an extension by radicals, then every irreducible cubic `f ∈ K[x]` with three real roots stays
irreducible over `L`. -/
theorem exercise_17_6_subfield {K L : Subfield ℝ} (hKL : K ≤ L) {f : K[X]}
    (hirr : Irreducible f) (hdeg : f.natDegree = 3)
    (hroots : {x : ℝ | Polynomial.aeval x f = 0}.ncard = 3)
    [Algebra K L] (halg : algebraMap K L = Subfield.inclusion hKL)
    (hrad : IsGarlingExtensionByRadicals K L) :
    Irreducible (f.map (algebraMap K L)) := by
  let L_if : IntermediateField K ℝ := IntermediateField.adjoin K (L : Set ℝ)
  have hL_if_eq : L_if.toSubfield = L := by
    apply le_antisymm
    · dsimp only [L_if]
      rw [adjoin_toSubfield_eq_closure_ch17, Subfield.closure_le]
      rintro x (⟨c, rfl⟩ | hxL)
      · exact hKL c.2
      · exact hxL
    · intro x hxL
      exact IntermediateField.subset_adjoin K (L : Set ℝ) hxL
  let e : L ≃ₐ[K] L_if :=
    { toFun := fun x => ⟨x.1, by change x.1 ∈ L_if.toSubfield; rw [hL_if_eq]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [← hL_if_eq]; exact x.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      commutes' := fun c => by
        apply Subtype.ext
        have h := congrArg Subtype.val (RingHom.congr_fun halg c)
        exact h }
  have hrad_if : IsGarlingExtensionByRadicals K L_if := isGarlingExtensionByRadicals_congr e hrad
  have hirr_if := exercise_17_6 K hirr hdeg hroots L_if hrad_if
  have hmap : (f.map (algebraMap K L_if)).map e.symm.toRingEquiv.toRingHom = f.map (algebraMap K L) := by
    rw [Polynomial.map_map]
    congr 1
    ext c
    exact congrArg Subtype.val (e.symm.commutes c)
  rw [← hmap]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e.symm.toRingEquiv).toMulEquiv).mpr hirr_if

/-- Explicit witness polynomial `x^3 - 3x - 1 ∈ ℚ[x]` for `Exercise 17.7` (printed p. 138):
irreducible over `ℚ`, discriminant `81 > 0` (hence three real roots), solvable by radicals, yet
none of its splitting fields is an extension by radicals over `ℚ`. -/
noncomputable def ex177Poly : ℚ[X] :=
  Polynomial.X ^ 3 - Polynomial.C 3 * Polynomial.X - Polynomial.C 1

/-- **Exercise 17.7 (explicit witness `x^3 - 3x - 1 ∈ ℚ[x]`, printed p. 138 / PDF p. 146):**
Proves that `f = x^3 - 3x - 1 ∈ ℚ[x]` is irreducible of degree `3`, has discriminant `81 > 0` and
three real roots, is solvable by radicals over `ℚ`, and yet for **every** splitting field `L` of `f`
over `ℚ` (in any universe `u`), `L : ℚ` is **not** an extension by radicals. -/
theorem exercise_17_7_witness :
    ex177Poly.natDegree = 3 ∧
    Irreducible ex177Poly ∧
    garlingDiscriminant ex177Poly = 81 ∧
    {x : ℝ | Polynomial.aeval x ex177Poly = 0}.ncard = 3 ∧
    IsGarlingSolvableByRadicals ex177Poly ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L ex177Poly →
      ¬ IsGarlingExtensionByRadicals ℚ L := by
  classical
  have hdeg : ex177Poly.natDegree = 3 := by dsimp only [ex177Poly]; compute_degree!
  have hmon : ex177Poly.Monic := by dsimp only [ex177Poly]; monicity!
  -- 1. Irreducibility via shift `x ↦ x + 1`: `(x + 1)^3 - 3(x + 1) - 1 = x^3 + 3x^2 - 3` (Eisenstein at `p = 3`)
  have hirr : Irreducible ex177Poly := by
    let fZ : ℤ[X] := Polynomial.X ^ 3 - Polynomial.C 3 * Polynomial.X - Polynomial.C 1
    let gZ : ℤ[X] := Polynomial.X ^ 3 + Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C 3
    have hshift : polyShiftEquiv ℤ 1 fZ = gZ := by
      change polyShiftHom ℤ 1 fZ = gZ
      dsimp [fZ, gZ, polyShiftHom]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simp only [map_one, map_ofNat]
      ring
    have hgZ_deg : gZ.natDegree = 3 := by dsimp [gZ]; compute_degree!
    have hgZ_mon : gZ.Monic := by dsimp [gZ]; monicity!
    have hp3 : Prime (3 : ℤ) := Int.prime_three
    have hgZ_irr : Irreducible gZ := by
      refine (theorem_5_2 (p := (3 : ℤ)) (n := 3) (by omega) (le_of_eq hgZ_deg)
        (isGarlingRelativelyPrime_coeffs_of_monic hgZ_mon hgZ_deg) hp3 ?_ ?_ ?_).2.1
      · intro i hi
        dsimp [gZ]
        interval_cases i <;> simp
      · dsimp [gZ]; simp
      · dsimp [gZ]; norm_num
    have hfZ_irr : Irreducible fZ :=
      (MulEquiv.irreducible_iff (polyShiftEquiv ℤ 1).toMulEquiv).mp
        (by simpa [hshift] using hgZ_irr)
    have hfZ_deg : fZ.natDegree = 3 := by dsimp [fZ]; compute_degree!
    rcases (corollary_gauss_lemma ℚ fZ).mp hfZ_irr with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
    · exfalso
      have hd := congrArg Polynomial.natDegree hC
      rw [hfZ_deg, Polynomial.natDegree_C] at hd
      omega
    · have hmap_eq : fZ.map (algebraMap ℤ ℚ) = ex177Poly := by
        dsimp [fZ, ex177Poly]; simp [map_ofNat]
      rwa [hmap_eq] at hmap_irr
  -- 2. Discriminant `= 81` via `garlingDiscriminant_monic_cubic`
  have hdisc : garlingDiscriminant ex177Poly = 81 := by
    have hrew : ex177Poly = Polynomial.X ^ 3 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (-3 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ) := by
      dsimp only [ex177Poly]
      simp only [map_zero, zero_mul, add_zero, map_neg, map_ofNat, map_one]
      ring
    rw [hrew, garlingDiscriminant_monic_cubic]
    norm_num
  -- 3. Transport to `K₀ = (algebraMap ℚ ℝ).fieldRange : Subfield ℝ` to invoke `Exercise 17.4` and `Exercise 17.6`
  let K₀ : Subfield ℝ := (algebraMap ℚ ℝ).fieldRange
  let eQ : ℚ ≃+* K₀ :=
    RingEquiv.ofBijective (algebraMap ℚ K₀)
      ⟨(algebraMap ℚ K₀).injective, fun ⟨x, hx⟩ => by
        rcases hx with ⟨q, rfl⟩
        exact ⟨q, rfl⟩⟩
  let fK₀ : K₀[X] := ex177Poly.map eQ.toRingHom
  have hirr_K₀ : Irreducible fK₀ :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv eQ).toMulEquiv).mpr hirr
  have hdeg_K₀ : fK₀.natDegree = 3 := by
    dsimp only [fK₀]; rw [Polynomial.natDegree_map, hdeg]
  have hdisc_K₀ : (garlingDiscriminant fK₀).1 = 81 := by
    have h1 : fK₀ = Polynomial.X ^ 3 + Polynomial.C (0 : K₀) * Polynomial.X ^ 2 +
        Polynomial.C (-3 : K₀) * Polynomial.X + Polynomial.C (-1 : K₀) := by
      dsimp only [fK₀, ex177Poly]
      rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      simp only [map_zero, zero_mul, add_zero, map_neg, map_ofNat, map_one]
      ring
    rw [h1, garlingDiscriminant_monic_cubic]
    have hval : ((-4 : K₀) * 0 ^ 3 * (-1) + 0 ^ 2 * (-3) ^ 2 + 18 * 0 * (-3) * (-1) -
        4 * (-3) ^ 3 - 27 * (-1) ^ 2 : K₀) = (81 : K₀) := by norm_num
    rw [hval]
    norm_cast
  have hdisc_pos : (0 : ℝ) < (garlingDiscriminant fK₀).1 := by rw [hdisc_K₀]; norm_num
  have hroots_K₀ : {x : ℝ | Polynomial.aeval x fK₀ = 0}.ncard = 3 :=
    ((exercise_17_4 K₀ hirr_K₀ hdeg_K₀).1).mpr hdisc_pos
  have hset_roots : {x : ℝ | Polynomial.aeval x ex177Poly = 0} =
      {x : ℝ | Polynomial.aeval x fK₀ = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, fK₀, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hroots_Q : {x : ℝ | Polynomial.aeval x ex177Poly = 0}.ncard = 3 := by
    rwa [hset_roots]
  -- 4. Solvable by radicals (via Chapter 14 cubic solvability)
  have hsolv : IsGarlingSolvableByRadicals ex177Poly :=
    cubic_solvable_by_radicals (by rw [ringChar.eq_zero]; decide)
      (by rw [ringChar.eq_zero]; decide) hmon.ne_zero (by omega)
  -- 5. No splitting field `L` over `ℚ` is an extension by radicals
  have hnot_rad : ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L ex177Poly →
      ¬ IsGarlingExtensionByRadicals ℚ L := by
    intro L _ _ hsfL hradL
    have hspl_K₀ : GarlingSplitsOver K₀ ℝ fK₀ :=
      ((exercise_17_4 K₀ hirr_K₀ hdeg_K₀).2.2.1).mpr hdisc_pos
    obtain ⟨n, c, α, hexp_K₀⟩ := hspl_K₀
    have hexp_Q : GarlingSplitsExplicit ℚ ℝ ex177Poly n (eQ.symm c) α := by
      dsimp only [GarlingSplitsExplicit, fK₀] at hexp_K₀ ⊢
      rw [Polynomial.map_map] at hexp_K₀
      have hc_eq : algebraMap ℚ ℝ (eQ.symm c) = algebraMap K₀ ℝ c :=
        congrArg Subtype.val (eQ.apply_symm_apply c)
      rw [hc_eq]
      exact hexp_K₀
    let E : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ (Set.range α)
    have hsfE : IsGarlingSplittingFieldExtension ℚ E ex177Poly := theorem_7_1 hmon.ne_zero hexp_Q
    obtain ⟨eLE⟩ := splitting_field_unique_up_to_algEquiv hsfL hsfE
    have hradE : IsGarlingExtensionByRadicals ℚ E := isGarlingExtensionByRadicals_congr eLE hradL
    -- Transport `IsGarlingExtensionByRadicals ℚ E` to `IsGarlingExtensionByRadicals K₀ E_K₀`
    let E_K₀ : IntermediateField K₀ ℝ :=
      { E.toSubfield with
        algebraMap_mem' := fun ⟨x, hx⟩ => by
          rcases hx with ⟨q, rfl⟩
          exact E.algebraMap_mem q }
    have hradE_K₀ : IsGarlingExtensionByRadicals K₀ E_K₀ := by
      rcases hradE with ⟨r, F, β, hF0, hFlast, hFstep⟩
      refine ⟨r, fun j =>
        { (F j).toSubfield with
          algebraMap_mem' := fun ⟨x, hx⟩ => by
            rcases hx with ⟨q, rfl⟩
            exact (F j).algebraMap_mem q },
        fun i => ⟨(β i : ℝ), (β i).2⟩, ?_, ?_, fun i => ?_⟩
      · ext ⟨x, hx⟩
        change (⟨x, hx⟩ : E) ∈ F 0 ↔ (⟨x, hx⟩ : E_K₀) ∈ (⊥ : IntermediateField K₀ E_K₀)
        rw [hF0]
        simp only [IntermediateField.mem_bot]
        constructor
        · rintro ⟨q, hq⟩
          refine ⟨eQ q, Subtype.ext (congrArg Subtype.val hq)⟩
        · rintro ⟨c, hc⟩
          exact ⟨eQ.symm c, Subtype.ext (by
            have h1 := congrArg Subtype.val hc
            have h2 : (eQ (eQ.symm c) : ℝ) = (c : ℝ) := congrArg Subtype.val (eQ.apply_symm_apply c)
            simpa [eQ] using h2.trans h1)⟩
      · ext ⟨x, hx⟩
        change (⟨x, hx⟩ : E) ∈ F (Fin.last r) ↔ True
        rw [hFlast]; simp
      · obtain ⟨⟨n_i, hn_i, hpow_i⟩, hadj_i⟩ := hFstep i
        refine ⟨⟨n_i, hn_i, hpow_i⟩, ?_⟩
        apply IntermediateField.toSubfield_injective
        rw [adjoin_toSubfield_eq_closure_ch17]
        have hstep_sf : (F i.succ).toSubfield =
            Subfield.closure (Set.range (algebraMap ℚ E) ∪ ((F i.castSucc : Set E) ∪ {β i})) := by
          rw [hadj_i, adjoin_toSubfield_eq_closure_ch17]
        change (F i.succ).toSubfield = _
        rw [hstep_sf]
        congr 1
        ext ⟨x, hx⟩
        simp only [Set.mem_union, Set.mem_range, SetLike.mem_coe, Set.mem_singleton_iff]
        constructor
        · rintro (⟨q, hq⟩ | hxF | hxβ)
          · exact Or.inl ⟨eQ q, Subtype.ext (congrArg Subtype.val hq)⟩
          · exact Or.inr (Or.inl hxF)
          · exact Or.inr (Or.inr (Subtype.ext (congrArg Subtype.val hxβ)))
        · rintro (⟨c, hc⟩ | hxF | hxβ)
          · refine Or.inl ⟨eQ.symm c, Subtype.ext ?_⟩
            have h1 := congrArg Subtype.val hc
            have h2 : (eQ (eQ.symm c) : ℝ) = (c : ℝ) := congrArg Subtype.val (eQ.apply_symm_apply c)
            simpa [eQ] using h2.trans h1
          · exact Or.inr (Or.inl hxF)
          · exact Or.inr (Or.inr (Subtype.ext (congrArg Subtype.val hxβ)))
    have hirr_E_K₀ : Irreducible (fK₀.map (algebraMap K₀ E_K₀)) :=
      exercise_17_6 K₀ hirr_K₀ hdeg_K₀ hroots_K₀ E_K₀ hradE_K₀
    -- Yet `fK₀` has a root in `E_K₀`, contradicting irreducibility of a cubic!
    have hn_eq3 : n = 3 := by
      have h1 := (garlingSplitsExplicit_props hmon.ne_zero hexp_Q).2.2.1
      simpa [garlingDegree, hdeg] using h1
    subst hn_eq3
    let r0 : E_K₀ := ⟨α 0, IntermediateField.subset_adjoin ℚ (Set.range α) ⟨0, rfl⟩⟩
    have hr0_root : (fK₀.map (algebraMap K₀ E_K₀)).IsRoot r0 := by
      rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
      apply Subtype.ext
      have h1 : Polynomial.aeval (α 0) ex177Poly = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hexp_Q, Polynomial.eval_mul,
          Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) (by simp))
      have h2 : ((Polynomial.aeval r0 fK₀ : E_K₀) : ℝ) = Polynomial.aeval (α 0) ex177Poly := by
        dsimp only [fK₀]
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
        change (E_K₀.val.toRingHom) (Polynomial.eval₂ ((algebraMap K₀ E_K₀).comp eQ.toRingHom) r0 ex177Poly) = _
        rw [Polynomial.hom_eval₂]
        rfl
      exact h2.trans h1
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr0_root
    have hfE0 : fK₀.map (algebraMap K₀ E_K₀) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap K₀ E_K₀).injective).mpr hirr_K₀.ne_zero
    have hq0 : q ≠ 0 := fun h0 => hfE0 (by rw [hq, h0, mul_zero])
    have hdeg_eq := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_map, hdeg_K₀,
      Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r0) hq0,
      Polynomial.natDegree_X_sub_C] at hdeg_eq
    rcases hirr_E_K₀.isUnit_or_isUnit hq with hu1 | hu2
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu1
      rw [Polynomial.natDegree_X_sub_C] at this
      omega
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu2
      omega
  exact ⟨hdeg, hirr, hdisc, hroots_Q, hsolv, hnot_rad⟩

/-- **Exercise 17.7 (printed p. 138 / PDF p. 146 — queued in `QUEUE.md` as an example-request prompt;
existential form witnessed by `x^3 - 3x - 1 ∈ ℚ[x]`):**
*"Give an example of a polynomial in `ℚ[x]` which is solvable by radicals, but whose splitting
field is not an extension by radicals."* -/
theorem exercise_17_7 :
    ∃ f : ℚ[X], IsGarlingSolvableByRadicals f ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        IsGarlingSplittingFieldExtension ℚ L f →
        ¬ IsGarlingExtensionByRadicals ℚ L :=
  ⟨ex177Poly, exercise_17_7_witness.{u}.2.2.2.2.1, exercise_17_7_witness.{u}.2.2.2.2.2⟩

end Garling.Chapter17
