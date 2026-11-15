import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Chapter 1: Groups, fields and vector spaces

Formalization of Chapter 1 (printed pp. 3–13, PDF pp. 11–21) of D. J. H. Garling,
*A Course in Galois Theory* (Cambridge University Press, 1986), following the chapter's
three sections (§1.1 *Groups*, §1.2 *Fields*, §1.3 *Vector spaces*) and all numbered
items in source order.
-/

namespace Garling.Chapter01

open scoped BigOperators

/-! ## §1.1 Groups (printed pp. 3–8) -/

/-- A law of composition on a set `S` is a binary operation `S → S → S` (§1.1, p. 3). -/
abbrev LawOfComposition (S : Type*) := S → S → S

/-- Garling's raw three-axiom characterization of a group on a non-empty set `G` (§1.1, p. 3),
prior to choosing canonical unit or inverse operations. -/
structure IsGarlingGroup (G : Type*) (comp : LawOfComposition G) : Prop where
  nonempty : Nonempty G
  assoc : ∀ g₁ g₂ g₃ : G, comp g₁ (comp g₂ g₃) = comp (comp g₁ g₂) g₃
  exists_unit : ∃ e : G, (∀ g : G, comp e g = g ∧ comp g e = g) ∧
    (∀ g : G, ∃ h : G, comp g h = e ∧ comp h g = e)

/-- Every standard `Group` satisfies Garling's raw group axioms (§1.1, p. 3). -/
theorem Group.isGarlingGroup (G : Type*) [Group G] :
    IsGarlingGroup G (· * ·) where
  nonempty := ⟨1⟩
  assoc a b c := (mul_assoc a b c).symm
  exists_unit := ⟨1, fun g => ⟨one_mul g, mul_one g⟩,
    fun g => ⟨g⁻¹, mul_inv_cancel g, inv_mul_cancel g⟩⟩

/-- Garling's set order `|S|` in `ℕ ∪ {+∞}` (§1.1, p. 4). -/
noncomputable abbrev setOrder (S : Type*) : ℕ∞ := ENat.card S

/-- The permutation group `Σ_S` of bijections of `S` under composition (§1.1, p. 4). -/
abbrev SigmaSet (S : Type*) := Equiv.Perm S

/-- The symmetric group `Σ_n` on `n` elements (§1.1, p. 4). -/
abbrev SigmaN (n : ℕ) := Equiv.Perm (Fin n)

/-- `|Σ_n| = n!` (§1.1, p. 4). -/
theorem setOrder_sigmaN (n : ℕ) : setOrder (SigmaN n) = n.factorial := by
  simp [setOrder, SigmaN, ENat.card_eq_coe_fintype_card, Fintype.card_perm]

/-- `Σ_S` is not abelian if `S` has more than two elements (§1.1, p. 4). -/
theorem sigmaSet_not_abelian {S : Type*} (hS : (2 : ℕ∞) < setOrder S) :
    ∃ σ₁ σ₂ : SigmaSet S, σ₁ * σ₂ ≠ σ₂ * σ₁ := by
  classical
  have h0 : (∅ : Finset S).card < ENat.card S := by
    simp only [Finset.card_empty, Nat.cast_zero]
    exact lt_trans (by decide : (0 : ℕ∞) < 2) hS
  obtain ⟨a, _⟩ := Finset.exists_not_mem_of_card_lt_enatCard h0
  have h1 : ({a} : Finset S).card < ENat.card S := by
    simp only [Finset.card_singleton, Nat.cast_one]
    exact lt_trans (by decide : (1 : ℕ∞) < 2) hS
  obtain ⟨b, hb⟩ := Finset.exists_not_mem_of_card_lt_enatCard h1
  have hab : a ≠ b := by
    intro h
    subst h
    exact hb (Finset.mem_singleton_self a)
  have h2 : ({a, b} : Finset S).card < ENat.card S := by
    rw [Finset.card_pair hab]
    exact hS
  obtain ⟨c, hc⟩ := Finset.exists_not_mem_of_card_lt_enatCard h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases hc with ⟨hca, hcb⟩
  refine ⟨Equiv.swap a b, Equiv.swap b c, ?_⟩
  intro hcomm
  have eval_c : (Equiv.swap a b * Equiv.swap b c) c = (Equiv.swap b c * Equiv.swap a b) c :=
    congrArg (fun f => f c) hcomm
  have hlhs : (Equiv.swap a b * Equiv.swap b c) c = a := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hrhs : (Equiv.swap b c * Equiv.swap a b) c = b := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
  rw [hlhs, hrhs] at eval_c
  exact hab eval_c

/-- Every additive subgroup of `ℤ` has the form `nℤ` for some `n : ℕ` (§1.1, p. 4). -/
theorem int_addSubgroup_eq_zmultiples (H : AddSubgroup ℤ) :
    ∃ n : ℕ, H = AddSubgroup.zmultiples (n : ℤ) := by
  obtain ⟨z, hz⟩ := Int.subgroup_cyclic H
  have hcl : AddSubgroup.closure ({z} : Set ℤ) = AddSubgroup.zmultiples z :=
    le_antisymm
      ((AddSubgroup.closure_le (K := AddSubgroup.zmultiples z)).mpr
        (Set.singleton_subset_iff.mpr (AddSubgroup.mem_zmultiples z)))
      (AddSubgroup.zmultiples_le_of_mem (AddSubgroup.subset_closure rfl))
  rw [hcl] at hz
  refine ⟨z.natAbs, ?_⟩
  rw [hz]
  rcases Int.natAbs_eq z with h | h
  · rw [← h]
  · conv_lhs => rw [h]
    exact AddSubgroup.zmultiples_neg

/-- Garling's definition of `A_n`: permutations in `Σ_n` expressible as a product of an even
number of transpositions, proved equal to `alternatingGroup (Fin n)` (§1.1, p. 4). -/
theorem mem_alternatingGroup_iff_even_swap_prod {n : ℕ} (σ : SigmaN n) :
    (∃ L : List (SigmaN n), (∀ τ ∈ L, τ.IsSwap) ∧ Even L.length ∧ L.prod = σ) ↔
      σ ∈ alternatingGroup (Fin n) := by
  constructor
  · rintro ⟨L, hL, heven, rfl⟩
    exact (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length hL).mpr heven
  · intro hmem
    have hprod : ∀ π : SigmaN n, ∃ L : List (SigmaN n), (∀ τ ∈ L, τ.IsSwap) ∧ L.prod = π := by
      intro π
      induction π using Equiv.Perm.swap_induction_on with
      | one => exact ⟨[], by simp, List.prod_nil⟩
      | swap_mul f x y hxy ih =>
        obtain ⟨L, hL, hf⟩ := ih
        refine ⟨Equiv.swap x y :: L, ?_, ?_⟩
        · intro τ hτ
          simp only [List.mem_cons] at hτ
          rcases hτ with rfl | hτ
          · exact ⟨x, y, hxy, rfl⟩
          · exact hL τ hτ
        · simp [List.prod_cons, hf]
    obtain ⟨L, hL, rfl⟩ := hprod σ
    exact ⟨L, hL, (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length hL).mp hmem, rfl⟩

/-- Garling's right coset `H ∘ g = {h * g | h ∈ H}` (§1.1, p. 4). -/
def RightCoset {G : Type*} [Group G] (H : Subgroup G) (g : G) : Set G :=
  {x : G | ∃ h ∈ H, h * g = x}

/-- The collection `G / H` of right cosets of `H` in `G` (§1.1, p. 4). -/
def RightCosets {G : Type*} [Group G] (H : Subgroup G) : Set (Set G) :=
  Set.range (RightCoset H)

/-- Bijection between left cosets `G ⧸ H` and Garling's right cosets `RightCosets H` via inversion. -/
noncomputable def quotientEquivRightCosets {G : Type*} [Group G] (H : Subgroup G) :
    (G ⧸ H) ≃ RightCosets H := by
  refine Equiv.ofBijective
    (Quotient.lift (fun g : G => ⟨RightCoset H g⁻¹, g⁻¹, rfl⟩) ?_) ⟨?_, ?_⟩
  · intro a b hab
    have hq : (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b := Quotient.sound hab
    have habH : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hq
    ext x
    unfold RightCoset
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h * (a⁻¹ * b), H.mul_mem hh habH, by group⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h * (a⁻¹ * b)⁻¹, H.mul_mem hh (H.inv_mem habH), by group⟩
  · intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn with | h a =>
    induction q₂ using Quotient.inductionOn with | h b =>
    change (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have hset : RightCoset H a⁻¹ = RightCoset H b⁻¹ := Subtype.ext_iff.mp hq
    have ha : a⁻¹ ∈ RightCoset H b⁻¹ := by
      rw [← hset]
      exact ⟨1, H.one_mem, one_mul _⟩
    rcases ha with ⟨h, hh, hmul⟩
    have heq : a⁻¹ * b = h := by
      calc a⁻¹ * b = (h * b⁻¹) * b := by rw [hmul]
        _ = h := by group
    simpa [heq] using hh
  · rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g⁻¹, by simp⟩

/-- Lagrange's theorem in Garling's right-coset cardinalities: `|G| = |G/H| · |H|` (§1.1, p. 4). -/
theorem lagrange_theorem {G : Type*} [Group G] (H : Subgroup G) :
    setOrder G = setOrder (RightCosets H) * setOrder H := by
  have hcard : Cardinal.mk G = Cardinal.mk (G ⧸ H) * Cardinal.mk H := by
    simpa [Cardinal.mk_prod] using
      Cardinal.mk_congr (@Subgroup.groupEquivQuotientProdSubgroup G _ H)
  have hENat := congrArg Cardinal.toENat hcard
  rw [map_mul] at hENat
  change ENat.card G = ENat.card (G ⧸ H) * ENat.card H at hENat
  rw [setOrder, setOrder, setOrder, hENat, ENat.card_congr (quotientEquivRightCosets H)]

/-- Garling's quotient group `ℤ_n = ℤ / nℤ` (§1.1, p. 5). -/
abbrev Zn (n : ℕ) := ℤ ⧸ AddSubgroup.zmultiples (n : ℤ)

/-- Canonical additive homomorphism `Zn n →+ ZMod n` sending `a + nℤ` to `(a : ZMod n)`. -/
def znToZModHom (n : ℕ) : Zn n →+ ZMod n :=
  QuotientAddGroup.lift _ (Int.castAddHom (ZMod n)) (by
    intro x hx
    rcases AddSubgroup.mem_zmultiples_iff.mp hx with ⟨k, rfl⟩
    simp)

/-- Canonical additive isomorphism `Zn n ≃+ ZMod n`. -/
noncomputable def znAddEquivZMod (n : ℕ) : Zn n ≃+ ZMod n := by
  refine AddEquiv.ofBijective (znToZModHom n) ⟨?_, ?_⟩
  · intro x y hxy
    induction x using Quotient.inductionOn with | h a =>
    induction y using Quotient.inductionOn with | h b =>
    change (QuotientAddGroup.mk a : Zn n) = QuotientAddGroup.mk b
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    have hab : ((-a + b : ℤ) : ZMod n) = 0 := by
      have hcast : (a : ZMod n) = (b : ZMod n) := hxy
      simp [hcast]
    rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (-a + b) n).mp hab with ⟨k, hk⟩
    exact ⟨k, by rw [zsmul_eq_mul, mul_comm]; exact hk.symm⟩
  · intro z
    cases n with
    | zero => exact ⟨QuotientAddGroup.mk z, rfl⟩
    | succ k =>
      refine ⟨QuotientAddGroup.mk (z.val : ℤ), ?_⟩
      change ((z.val : ℤ) : ZMod (k + 1)) = z
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- For `n > 0`, `|ℤ_n| = n` (§1.1, p. 5). -/
theorem setOrder_Zn {n : ℕ} (hn : 0 < n) : setOrder (Zn n) = n := by
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [setOrder, ENat.card_congr (znAddEquivZMod n).toEquiv, ENat.card_eq_coe_fintype_card,
      ZMod.card n]

/-- Finite carrier of the Viergruppe `N = {e, (12)(34), (13)(24), (14)(23)} ⊆ Σ_4` (§1.1, p. 7). -/
def viergruppeFinset : Finset (SigmaN 4) :=
  {1,
   Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3,
   Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3,
   Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2}

/-- The Viergruppe `N ◁ Σ_4` (§1.1, p. 7). -/
def viergruppe : Subgroup (SigmaN 4) where
  carrier := (viergruppeFinset : Set (SigmaN 4))
  mul_mem' := by
    intro a b ha hb
    change a ∈ viergruppeFinset at ha
    change b ∈ viergruppeFinset at hb
    change a * b ∈ viergruppeFinset
    revert a b ha hb
    decide
  one_mem' := by
    change (1 : SigmaN 4) ∈ viergruppeFinset
    decide
  inv_mem' := by
    intro a ha
    change a ∈ viergruppeFinset at ha
    change a⁻¹ ∈ viergruppeFinset
    revert a ha
    decide

theorem viergruppe_normal : viergruppe.Normal := by
  constructor
  intro n hn g
  change n ∈ viergruppeFinset at hn
  change g * n * g⁻¹ ∈ viergruppeFinset
  revert g n hn
  decide

/-! ### Exercises 1.1–1.10 (§1.1, printed pp. 7–8) -/

/-- **Exercise 1.1** (§1.1, p. 7): Every element of a group has a unique inverse, proved directly
from Garling's raw group axioms. -/
theorem exercise_1_1_raw {G : Type*} {comp : LawOfComposition G}
    (hG : IsGarlingGroup G comp) :
    ∃ e : G, (∀ g : G, comp e g = g ∧ comp g e = g) ∧
      ∀ g : G, ∃! h : G, comp g h = e ∧ comp h g = e := by
  obtain ⟨e, he, hinv⟩ := hG.exists_unit
  refine ⟨e, he, fun g => ?_⟩
  obtain ⟨h, hgh, hhg⟩ := hinv g
  refine ⟨h, ⟨hgh, hhg⟩, fun h' ⟨hgh', _⟩ => ?_⟩
  calc h' = comp e h' := (he h').1.symm
    _ = comp (comp h g) h' := by rw [hhg]
    _ = comp h (comp g h') := (hG.assoc h g h').symm
    _ = comp h e := by rw [hgh']
    _ = h := (he h).2

/-- **Exercise 1.1** (§1.1, p. 7): Standard `Group` formulation of uniqueness of the inverse. -/
theorem exercise_1_1 {G : Type*} [Group G] (g : G) :
    ∃! h : G, g * h = 1 ∧ h * g = 1 := by
  refine ⟨g⁻¹, ⟨mul_inv_cancel g, inv_mul_cancel g⟩, fun h ⟨hgh, _⟩ => ?_⟩
  calc h = 1 * h := (one_mul h).symm
    _ = (g⁻¹ * g) * h := by rw [inv_mul_cancel]
    _ = g⁻¹ * (g * h) := mul_assoc g⁻¹ g h
    _ = g⁻¹ * 1 := by rw [hgh]
    _ = g⁻¹ := mul_one g⁻¹

/-- **Exercise 1.2** (§1.1, p. 7): The First Isomorphism Theorem for groups — `K = ker φ` is
normal in `G₁`, and there is a group isomorphism `φ̃ : G₁ ⧸ K ≃* φ(G₁)` factoring `φ = i ∘ φ̃ ∘ q`. -/
theorem exercise_1_2 {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂) :
    φ.ker.Normal ∧
      ∃ ψ : (G₁ ⧸ φ.ker) ≃* φ.range,
        ∀ g : G₁, φ g = φ.range.subtype (ψ (QuotientGroup.mk g)) := by
  refine ⟨φ.normal_ker, QuotientGroup.quotientKerEquivRange φ, fun g => rfl⟩

/-- **Exercise 1.3** (§1.1, p. 7): Every subgroup `H` of `G` of index `2` (in Garling's right-coset
cardinality `|G / H| = 2`) is a normal subgroup of `G`. -/
theorem exercise_1_3 {G : Type*} [Group G] (H : Subgroup G)
    (hidx : setOrder (RightCosets H) = 2) : H.Normal := by
  have hq : ENat.card (G ⧸ H) = (2 : ℕ) := by
    simpa [setOrder] using (ENat.card_congr (quotientEquivRightCosets H)).trans hidx
  have hfin : Finite (G ⧸ H) := ENat.card_lt_top.mp (by rw [hq]; exact ENat.natCast_lt_top 2)
  have hnat : H.index = 2 := by
    rw [Subgroup.index, ← ENat.natCast_inj]
    rw [← ENat.card_eq_coe_natCard]
    exact hq
  exact Subgroup.normal_of_index_eq_two hnat

/-- **Exercise 1.4** (§1.1, p. 7): If `G` has a unique subgroup `H` of order `k`, then `H` is a
normal subgroup of `G`. Stated with `setOrder` (`ℕ∞`) so no infinite-group junk value arises. -/
theorem exercise_1_4 {G : Type*} [Group G] (H : Subgroup G) (k : ℕ∞)
    (hord : setOrder H = k)
    (huniq : ∀ H' : Subgroup G, setOrder H' = k → H' = H) :
    H.Normal := by
  constructor
  intro h hh g
  let α : G ≃* G := MulAut.conj g
  let H' : Subgroup G := H.map α.toMonoidHom
  have hcard : setOrder H' = k := by
    rw [← hord, setOrder, setOrder]
    exact ENat.card_congr (α.subgroupMap H).symm.toEquiv
  have hEq : H' = H := huniq H' hcard
  rw [← hEq]
  exact ⟨h, hh, rfl⟩

/-- **Exercise 1.5** (§1.1, p. 7): Normality is not transitive — there exist a group `G` and
subgroups `K ≤ H ≤ G` with `H ◁ G` and `K ◁ H` such that `K` is not normal in `G`
(witnessed using Garling's Viergruppe `N ◁ Σ_4`). -/
theorem exercise_1_5 :
    ¬ (∀ (G : Type) [Group G] (H K : Subgroup G),
        K ≤ H → H.Normal → (K.subgroupOf H).Normal → K.Normal) := by
  intro hall
  let τ : SigmaN 4 := Equiv.swap 0 1 * Equiv.swap 2 3
  let K : Subgroup (SigmaN 4) := Subgroup.zpowers τ
  have hKH : K ≤ viergruppe := by
    rw [Subgroup.zpowers_le]
    change τ ∈ viergruppeFinset
    decide
  have hKsubN : (K.subgroupOf viergruppe).Normal := by
    have hcomm : ∀ a b : SigmaN 4, a ∈ viergruppeFinset → b ∈ viergruppeFinset → a * b = b * a := by
      decide
    constructor
    intro x hx g
    have hgx : g * x = x * g := Subtype.ext (hcomm g.1 x.1 g.2 x.2)
    have hconj : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hgx]
      _ = x := by group
    simpa [hconj] using hx
  have hKN : K.Normal := hall (SigmaN 4) viergruppe K hKH viergruppe_normal hKsubN
  let g : SigmaN 4 := Equiv.swap 1 2
  have hconj : g * τ * g⁻¹ ∈ K := hKN.conj_mem τ (Subgroup.mem_zpowers τ) g
  have hnot : g * τ * g⁻¹ ∉ K := by
    intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    rcases hmem with ⟨m, hm⟩
    have hord : τ ^ (2 : ℤ) = 1 := by decide
    have hmod : τ ^ m = τ ^ (m % 2) := by
      conv_lhs => rw [show m = 2 * (m / 2) + m % 2 by omega]
      rw [zpow_add, zpow_mul, zpow_ofNat, show τ ^ 2 = 1 from by decide,
          one_zpow, one_mul]
    rw [hmod] at hm
    have hcases : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0, zpow_zero] at hm
      revert hm; decide
    · rw [h1, zpow_one] at hm
      revert hm; decide
  exact hnot hconj

open Classical in
/-- **Exercise 1.6** (§1.1, p. 7): Every permutation of a finite set can be written as a product
of transpositions. -/
theorem exercise_1_6 {S : Type*} [Finite S] (σ : SigmaSet S) :
    ∃ L : List (SigmaSet S), (∀ τ ∈ L, τ.IsSwap) ∧ L.prod = σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨[], by simp, List.prod_nil⟩
  | swap_mul f x y hxy ih =>
    obtain ⟨L, hL, hf⟩ := ih
    refine ⟨Equiv.swap x y :: L, ?_, ?_⟩
    · intro τ hτ
      simp only [List.mem_cons] at hτ
      rcases hτ with rfl | hτ
      · exact ⟨x, y, hxy, rfl⟩
      · exact hL τ hτ
    · simp [List.prod_cons, hf]

/-- **Exercise 1.7 (degenerate trivial-group counterexample)** (§1.1, p. 7; queued fidelity hold):
If `|G| = 1`, `G` has no non-unit elements, so universal quantification over `g ≠ 1` holds
vacuously while `|G| = 1` is not prime. -/
theorem exercise_1_7_trivial_counterexample :
    (∀ g : Multiplicative Unit, g ≠ 1 → Subgroup.zpowers g = ⊤) ∧
      ¬ (Finite (Multiplicative Unit) ∧ IsCyclic (Multiplicative Unit) ∧
          Nat.Prime (Nat.card (Multiplicative Unit))) := by
  refine ⟨fun g hg => (hg (Subsingleton.elim g 1)).elim, ?_⟩
  rintro ⟨_, _, hprime⟩
  rw [Nat.card_unique] at hprime
  exact Nat.not_prime_one hprime

/-- **Exercise 1.7 (non-trivial groups)** (§1.1, p. 7): A non-trivial group `G` is generated by
each of its non-unit elements if and only if `G` is a finite cyclic group of prime order. -/
theorem exercise_1_7 {G : Type*} [Group G] [Nontrivial G] :
    (∀ g : G, g ≠ 1 → Subgroup.zpowers g = ⊤) ↔
      (Finite G ∧ IsCyclic G ∧ Nat.Prime (Nat.card G)) := by
  constructor
  · intro hgen
    obtain ⟨g, hg1⟩ := exists_ne (1 : G)
    have htop : Subgroup.zpowers g = ⊤ := hgen g hg1
    have hcyc : IsCyclic G := ⟨g, fun x => Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top x)⟩
    have hfin : Finite G := by
      by_contra hinf
      have hinfG : Infinite G := not_finite_iff_infinite.mp hinf
      have hnotFinOrd : ¬ IsOfFinOrder g := by
        intro hfinOrd
        have hpos : 0 < orderOf g := hfinOrd.orderOf_pos
        have hsurj : Function.Surjective (fun i : Fin (orderOf g) => g ^ (i : ℕ)) := by
          intro x
          have hx : x ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top x
          rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, rfl⟩
          have hmod_nn : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg k (by omega)
          have hmod_lt : k % (orderOf g : ℤ) < orderOf g := Int.emod_lt_of_pos k (by omega)
          refine ⟨⟨(k % (orderOf g : ℤ)).toNat, by omega⟩, ?_⟩
          have htoNat : ((k % (orderOf g : ℤ)).toNat : ℤ) = k % (orderOf g : ℤ) :=
            Int.toNat_of_nonneg hmod_nn
          dsimp only
          rw [← zpow_natCast, htoNat]
          conv_rhs => rw [show k = (orderOf g : ℤ) * (k / (orderOf g : ℤ)) + k % (orderOf g : ℤ) by
            linarith [Int.ediv_mul_add_emod k (orderOf g)]]
          rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, one_mul]
        exact hinf (Finite.of_surjective _ hsurj)
      have hord0 : orderOf g = 0 := orderOf_eq_zero_iff.mpr hnotFinOrd
      have hg2_ne1 : g ^ (2 : ℤ) ≠ 1 := by
        intro h2
        have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h2)
        rw [hord0, zero_dvd_iff] at hd
        omega
      have htop2 : Subgroup.zpowers (g ^ (2 : ℤ)) = ⊤ := hgen (g ^ (2 : ℤ)) hg2_ne1
      have hg_mem : g ∈ Subgroup.zpowers (g ^ (2 : ℤ)) := htop2 ▸ Subgroup.mem_top g
      rcases Subgroup.mem_zpowers_iff.mp hg_mem with ⟨k, hk⟩
      rw [← zpow_mul] at hk
      have hdiff : g ^ (2 * k - 1 : ℤ) = 1 := by
        rw [zpow_sub, zpow_one, hk, mul_inv_cancel]
      have hne_exp : (2 * k - 1 : ℤ) ≠ 0 := by omega
      have hpos_exp : 0 < (2 * k - 1).natAbs := Int.natAbs_pos.mpr hne_exp
      have hpow1 : g ^ (2 * k - 1).natAbs = 1 := by
        rcases Int.natAbs_eq (2 * k - 1) with heq | heq
        · exact zpow_natCast g _ ▸ heq ▸ hdiff
        · have := inv_eq_one.mpr (heq ▸ hdiff)
          simpa [← zpow_neg, ← zpow_natCast] using this
      exact hnotFinOrd (isOfFinOrder_iff_pow_eq_one.mpr ⟨(2 * k - 1).natAbs, hpos_exp, hpow1⟩)
    have : Finite G := hfin
    refine ⟨hfin, hcyc, ?_⟩
    by_contra hnotp
    have hgt1 : 1 < Nat.card G := Finite.one_lt_card
    obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgt1)
    have hord_g : orderOf g = Nat.card G := by
      rw [← Nat.card_zpowers, htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rcases hdvd with ⟨q, hq⟩
    have hq_pos : 0 < q := by
      by_contra hq0
      rw [Nat.eq_zero_of_not_pos hq0, mul_zero] at hq
      omega
    have hq_gt1 : 1 < q := by
      by_contra hq1
      have hqe1 : q = 1 := by omega
      rw [hqe1, mul_one] at hq
      exact hnotp (hq ▸ hp)
    let x := g ^ p
    have hx_ne1 : x ≠ 1 := by
      intro hx1
      have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hx1
      have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos hd
      nlinarith
    have hx_ord : orderOf x = q := by
      rw [orderOf_pow' g hp.ne_zero, hord_g, hq, Nat.gcd_eq_right (dvd_mul_right p q),
          Nat.mul_div_cancel_left q hp.pos]
    have hx_top := hgen x hx_ne1
    have hcard_x : Nat.card G = q := by
      calc Nat.card G = Nat.card (⊤ : Subgroup G) := (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
        _ = Nat.card (Subgroup.zpowers x) := by rw [hx_top]
        _ = orderOf x := Nat.card_zpowers x
        _ = q := hx_ord
    nlinarith [hp.two_le]
  · rintro ⟨hfin, _, hprime⟩ g hg1
    have : Finite G := hfin
    have : Fintype G := Fintype.ofFinite G
    have : Fintype (Subgroup.zpowers g) := Fintype.ofFinite _
    have hdvd : Nat.card (Subgroup.zpowers g) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | hself
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact hg1 h1
    · exact Subgroup.eq_top_of_card_eq _ hself

/-- **Exercise 1.8** (§1.1, p. 8): For any positive integer `n`, the coset `a + nℤ` generates
`ℤ_n = ℤ / nℤ` if and only if `gcd(a, n) = 1`. -/
theorem exercise_1_8 {n : ℕ} (_hn : 0 < n) (a : ℤ) :
    AddSubgroup.zmultiples (QuotientAddGroup.mk a : Zn n) = ⊤ ↔ Int.gcd a n = 1 := by
  constructor
  · intro htop
    have hmem : (QuotientAddGroup.mk 1 : Zn n) ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk a : Zn n) :=
      htop ▸ AddSubgroup.mem_top _
    rcases AddSubgroup.mem_zmultiples_iff.mp hmem with ⟨k, hk⟩
    have hk' : (QuotientAddGroup.mk (k * a) : Zn n) = QuotientAddGroup.mk 1 := by
      simpa [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul] using hk
    have hrel := QuotientAddGroup.eq.mp hk'
    rcases AddSubgroup.mem_zmultiples_iff.mp hrel with ⟨m, hm⟩
    rw [zsmul_eq_mul, Int.cast_id] at hm
    have hbez : k * a + m * (n : ℤ) = 1 := by linarith
    have hdvd1 : (Int.gcd a (n : ℤ) : ℤ) ∣ 1 := by
      have ha : (Int.gcd a (n : ℤ) : ℤ) ∣ a := Int.gcd_dvd_left a (n : ℤ)
      have hn' : (Int.gcd a (n : ℤ) : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_right a (n : ℤ)
      rw [← hbez]
      exact dvd_add (dvd_mul_of_dvd_right ha k) (dvd_mul_of_dvd_right hn' m)
    exact Nat.eq_one_of_dvd_one (Int.ofNat_dvd_left.mp hdvd1)
  · intro hcop
    rw [eq_top_iff]
    intro x _
    induction x using Quotient.inductionOn with | h b =>
    have hbez : (Int.gcd a (n : ℤ) : ℤ) = a * Int.gcdA a (n : ℤ) + (n : ℤ) * Int.gcdB a (n : ℤ) :=
      Int.gcd_eq_gcd_ab a (n : ℤ)
    rw [hcop, Nat.cast_one] at hbez
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨b * Int.gcdA a (n : ℤ), ?_⟩
    change (b * Int.gcdA a (n : ℤ)) • (QuotientAddGroup.mk a : Zn n) = QuotientAddGroup.mk b
    rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul, QuotientAddGroup.eq,
        AddSubgroup.mem_zmultiples_iff]
    refine ⟨b * Int.gcdB a (n : ℤ), ?_⟩
    rw [zsmul_eq_mul]
    calc (b * Int.gcdB a (n : ℤ)) * (n : ℤ)
      _ = b * ((n : ℤ) * Int.gcdB a (n : ℤ)) := by ring
      _ = b * (1 - a * Int.gcdA a (n : ℤ)) := by rw [show (n : ℤ) * Int.gcdB a (n : ℤ) = 1 - a * Int.gcdA a (n : ℤ) by linarith]
      _ = -(b * Int.gcdA a (n : ℤ) * a) + b := by ring

/-- **Exercise 1.9** (§1.1, p. 8): There exists a non-abelian group of order `8` all of whose
subgroups are normal (witnessed by the quaternion group `QuaternionGroup 2`). -/
theorem exercise_1_9 :
    ∃ (G : Type) (_ : Group G),
      setOrder G = 8 ∧
      (∃ x y : G, x * y ≠ y * x) ∧
      (∀ H : Subgroup G, H.Normal) := by
  refine ⟨QuaternionGroup 2, inferInstance, ?_, ?_, ?_⟩
  · simp [setOrder, ENat.card_eq_coe_fintype_card, QuaternionGroup.card]
  · refine ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, ?_⟩
    decide
  · intro H
    constructor
    intro h hh g
    have hsq : ∀ (g x : QuaternionGroup 2), g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x ^ 3 := by
      decide
    rcases hsq g h with heq | heq
    · rw [heq]; exact hh
    · rw [heq]; exact H.pow_mem hh 3

/-- Garling's explicit rational product formula for the sign of `π ∈ Σ_n` (§1.1, Ex. 1.10, p. 8):
`ε(π) = (∏_{i < j} (π(j) - π(i))) / (∏_{i < j} (j - i))`. -/
def garlingEpsilon (n : ℕ) (π : SigmaN n) : ℚ :=
  (∏ j : Fin n, ∏ i ∈ Finset.Iio j, ((π j : ℕ) - (π i : ℕ) : ℚ)) /
  (∏ j : Fin n, ∏ i ∈ Finset.Iio j, ((j : ℕ) - (i : ℕ) : ℚ))

/-- Identification of Garling's product quotient `garlingEpsilon n π` with `π.sign` for all `n`. -/
theorem garlingEpsilon_eq_sign (n : ℕ) (π : SigmaN n) :
    garlingEpsilon n π = ((Equiv.Perm.sign π : ℤ) : ℚ) := by
  unfold garlingEpsilon
  let f : Fin n → Fin n → ℚ := fun i j => (j : ℕ) - (i : ℕ)
  have hf : ∀ i j, f i j = -f j i := fun i j => by simp [f]
  have hnum := Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod π hf
  change (∏ j, ∏ i ∈ Finset.Iio j, f (π i) (π j)) / (∏ j, ∏ i ∈ Finset.Iio j, f i j) = _
  rw [hnum]
  have hden_pos : (0 : ℚ) < ∏ j : Fin n, ∏ i ∈ Finset.Iio j, f i j := by
    refine Finset.prod_pos fun j _ => Finset.prod_pos fun i hi => ?_
    simp only [Finset.mem_Iio] at hi
    simp only [f, sub_pos, Nat.cast_lt]
    exact hi
  have hden_ne : (∏ j : Fin n, ∏ i ∈ Finset.Iio j, f i j) ≠ 0 := ne_of_gt hden_pos
  exact mul_div_cancel_right₀ _ hden_ne

/-- `garlingEpsilon n` packaged as a homomorphism `Σ_n →* ℤˣ` (`{1, -1}`) via its exact agreement
with Garling's rational product formula (§1.1, Ex. 1.10, p. 8). -/
def garlingEpsilonHom (n : ℕ) : SigmaN n →* ℤˣ where
  toFun π := if garlingEpsilon n π = 1 then 1 else -1
  map_one' := by
    simp [garlingEpsilon_eq_sign]
  map_mul' π₁ π₂ := by
    rw [garlingEpsilon_eq_sign, garlingEpsilon_eq_sign, garlingEpsilon_eq_sign, map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π₁) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign π₂) with h₂ | h₂ <;>
    norm_num [h₁, h₂]

theorem garlingEpsilonHom_coe (n : ℕ) (π : SigmaN n) :
    ((garlingEpsilonHom n π : ℤ) : ℚ) = garlingEpsilon n π := by
  rw [garlingEpsilon_eq_sign]
  unfold garlingEpsilonHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, garlingEpsilon_eq_sign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> norm_num [h]

/-- **Exercise 1.10 (homomorphism and kernel, all `n`)** (§1.1, p. 8): `ε` maps `Σ_n` into `{1, -1}`
as a group homomorphism whose kernel is `A_n`. -/
theorem exercise_1_10_ker (n : ℕ) :
    (garlingEpsilonHom n).ker = alternatingGroup (Fin n) := by
  ext π
  rw [MonoidHom.mem_ker, Equiv.Perm.mem_alternatingGroup]
  have hcoe := garlingEpsilonHom_coe n π
  rw [garlingEpsilon_eq_sign] at hcoe
  have hinj : (garlingEpsilonHom n π : ℤ) = (Equiv.Perm.sign π : ℤ) := by exact_mod_cast hcoe
  exact ⟨fun h => Units.ext (by simpa [h] using hinj.symm),
         fun h => Units.ext (by simpa [h] using hinj)⟩

/-- **Exercise 1.10 (surjectivity for `n ≥ 2`)** (§1.1, p. 8): For `n ≥ 2`, `ε : Σ_n →* {1, -1}`
is onto. -/
theorem exercise_1_10_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (garlingEpsilonHom n) := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · let i₀ : Fin n := ⟨0, by omega⟩
    let i₁ : Fin n := ⟨1, by omega⟩
    have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    refine ⟨Equiv.swap i₀ i₁, ?_⟩
    apply Units.ext
    have hcoe := garlingEpsilonHom_coe n (Equiv.swap i₀ i₁)
    rw [garlingEpsilon_eq_sign, Equiv.Perm.sign_swap hne] at hcoe
    exact_mod_cast hcoe

/-- **Exercise 1.10 (degenerate `n < 2` counterexample to surjectivity)** (§1.1, p. 8; queued
fidelity hold): For `n < 2` (in particular `n = 1` where `S = {1}`), `|Σ_n| = 1`, so `ε` is not
onto `{1, -1}`. -/
theorem exercise_1_10_not_surjective_of_lt_two {n : ℕ} (hn : n < 2) :
    ¬ Function.Surjective (garlingEpsilonHom n) := by
  intro hsurj
  obtain ⟨π, hπ⟩ := hsurj (-1)
  have hsub : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
  have hπ1 : π = 1 := Subsingleton.elim π 1
  rw [hπ1, map_one] at hπ
  revert hπ; decide

/-! ## §1.2 Fields (printed pp. 8–9) -/

/-- Garling's field axioms (§1.2, p. 8) on `(K, +, *)`: `K` is an additive abelian group with
neutral element `0`, `K* = K \ {0}` is a (non-empty) multiplicative abelian group with unit `1`,
`(a) 0 * x = x * 0 = 0`, and `(c) x * (y + z) = x * y + x * z`. -/
structure IsGarlingField (K : Type*) (add mul : LawOfComposition K) : Prop where
  exists_zero_one : ∃ (zero one : K),
    zero ≠ one ∧
    (∀ x y z : K, add x (add y z) = add (add x y) z) ∧
    (∀ x y : K, add x y = add y x) ∧
    (∀ x : K, add zero x = x ∧ add x zero = x) ∧
    (∀ x : K, ∃ nx : K, add x nx = zero ∧ add nx x = zero) ∧
    (∀ x : K, mul zero x = zero ∧ mul x zero = zero) ∧
    (∀ x y : K, x ≠ zero → y ≠ zero → mul x y ≠ zero) ∧
    (∀ x y z : K, x ≠ zero → y ≠ zero → z ≠ zero → mul x (mul y z) = mul (mul x y) z) ∧
    (∀ x y : K, x ≠ zero → y ≠ zero → mul x y = mul y x) ∧
    (∀ x : K, x ≠ zero → mul one x = x ∧ mul x one = x) ∧
    (∀ x : K, x ≠ zero → ∃ ix : K, ix ≠ zero ∧ mul x ix = one ∧ mul ix x = one) ∧
    (∀ x y z : K, mul x (add y z) = add (mul x y) (mul x z))

/-- Every standard `Field` satisfies Garling's field axioms (§1.2, p. 8). -/
theorem Field.isGarlingField (K : Type*) [Field K] :
    IsGarlingField K (· + ·) (· * ·) where
  exists_zero_one := ⟨0, 1, zero_ne_one,
    fun x y z => (add_assoc x y z).symm,
    add_comm,
    fun x => ⟨zero_add x, add_zero x⟩,
    fun x => ⟨-x, add_neg_cancel x, neg_add_cancel x⟩,
    fun x => ⟨zero_mul x, mul_zero x⟩,
    fun _ _ hx hy => mul_ne_zero hx hy,
    fun x y z _ _ _ => (mul_assoc x y z).symm,
    fun x y _ _ => mul_comm x y,
    fun x _ => ⟨one_mul x, mul_one x⟩,
    fun x hx => ⟨x⁻¹, inv_ne_zero hx, mul_inv_cancel₀ hx, inv_mul_cancel₀ hx⟩,
    mul_add⟩

/-- Irrationality of `√2` (§1.2, p. 8). -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

/-- `{r + s√2 : r, s ∈ ℚ}` is a subfield of `ℝ` (§1.2, p. 8). -/
noncomputable def qSqrtTwoSubfield : Subfield ℝ where
  carrier := {x : ℝ | ∃ r s : ℚ, x = r + s * Real.sqrt 2}
  mul_mem' := by
    rintro _ _ ⟨r₁, s₁, rfl⟩ ⟨r₂, s₂, rfl⟩
    refine ⟨r₁ * r₂ + 2 * s₁ * s₂, r₁ * s₂ + r₂ * s₁, ?_⟩
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    push_cast
    linear_combination (s₁ : ℝ) * (s₂ : ℝ) * hsq
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨r₁, s₁, rfl⟩ ⟨r₂, s₂, rfl⟩
    exact ⟨r₁ + r₂, s₁ + s₂, by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨r, s, rfl⟩
    exact ⟨-r, -s, by push_cast; ring⟩
  inv_mem' := by
    rintro x ⟨r, s, rfl⟩
    by_cases hrs : r = 0 ∧ s = 0
    · rcases hrs with ⟨rfl, rfl⟩
      exact ⟨0, 0, by simp⟩
    · have hd_ne : r ^ 2 - 2 * s ^ 2 ≠ 0 := by
        intro hd0
        have hs0 : s = 0 := by
          by_contra hs
          have h2 : (r / s : ℝ) ^ 2 = 2 := by
            have hsR : (s : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hs
            have hdR : (r : ℝ) ^ 2 - 2 * (s : ℝ) ^ 2 = 0 := by exact_mod_cast hd0
            field_simp [hsR]
            linarith
          have hsqrt : |(r / s : ℝ)| = Real.sqrt 2 := by
            rw [← Real.sqrt_sq_eq_abs, h2]
          rcases abs_cases (r / s : ℝ) with ⟨habs, _⟩ | ⟨habs, _⟩
          · exact sqrt_two_irrational ⟨r / s, by simpa [habs] using hsqrt⟩
          · exact sqrt_two_irrational ⟨-(r / s), by push_cast; linarith⟩
        have hr0 : r = 0 := by nlinarith
        exact hrs ⟨hr0, hs0⟩
      let d : ℚ := r ^ 2 - 2 * s ^ 2
      let u : ℚ := r / d
      let v : ℚ := -s / d
      refine ⟨u, v, ?_⟩
      have hmul1 : ((r : ℝ) + (s : ℝ) * Real.sqrt 2) * ((u : ℝ) + (v : ℝ) * Real.sqrt 2) = 1 := by
        have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hdR : (d : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hd_ne
        have hnum : ((r : ℝ) + (s : ℝ) * Real.sqrt 2) * ((r : ℝ) - (s : ℝ) * Real.sqrt 2) =
            (d : ℝ) := by
          simp only [d]
          push_cast
          linear_combination -(s : ℝ) ^ 2 * hsq
        calc ((r : ℝ) + (s : ℝ) * Real.sqrt 2) * ((u : ℝ) + (v : ℝ) * Real.sqrt 2)
          _ = (((r : ℝ) + (s : ℝ) * Real.sqrt 2) * ((r : ℝ) - (s : ℝ) * Real.sqrt 2)) /
                (d : ℝ) := by
              simp only [u, v]
              push_cast
              ring
          _ = (d : ℝ) / (d : ℝ) := by rw [hnum]
          _ = 1 := div_self hdR
      exact inv_eq_of_mul_eq_one_right hmul1

/-! ### Exercises 1.11–1.13 (§1.2, printed p. 9) -/

/-- **Exercise 1.11** (§1.2, p. 9): Every field has at least two elements, and there exists a field
with exactly two elements. -/
theorem exercise_1_11 :
    (∀ (K : Type*) [Field K], (2 : ℕ∞) ≤ setOrder K) ∧
      ∃ (K : Type) (_ : Field K), setOrder K = 2 := by
  refine ⟨fun K _ => ?_, ⟨ZMod 2, inferInstance, ?_⟩⟩
  · have hpair : ({(0 : K), 1} : Set K).encard = 2 := Set.encard_pair zero_ne_one
    have hle : ({(0 : K), 1} : Set K).encard ≤ ENat.card K := Set.encard_le_card
    simpa [hpair, setOrder] using hle
  · simp [setOrder, ENat.card_eq_coe_fintype_card]

/-- **Exercise 1.12 (well-definedness)** (§1.2, p. 9): Coset multiplication
`(a + nℤ) ∘ (b + nℤ) = ab + nℤ` is independent of coset representatives. -/
theorem exercise_1_12_well_defined (n : ℕ) {a a' b b' : ℤ}
    (ha : a - a' ∈ AddSubgroup.zmultiples (n : ℤ))
    (hb : b - b' ∈ AddSubgroup.zmultiples (n : ℤ)) :
    a * b - a' * b' ∈ AddSubgroup.zmultiples (n : ℤ) := by
  rcases AddSubgroup.mem_zmultiples_iff.mp ha with ⟨k, hk⟩
  rcases AddSubgroup.mem_zmultiples_iff.mp hb with ⟨m, hm⟩
  rw [zsmul_eq_mul, Int.cast_id] at hk hm
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨k * b + a' * m, ?_⟩
  rw [zsmul_eq_mul, Int.cast_id]
  calc (k * b + a' * m) * (n : ℤ)
    _ = (k * (n : ℤ)) * b + a' * (m * (n : ℤ)) := by ring
    _ = (a - a') * b + a' * (b - b') := by rw [hk, hm]
    _ = a * b - a' * b' := by ring

/-- Multiplication on `ℤ_n = ℤ / nℤ` defined on cosets by `(a + nℤ) ∘ (b + nℤ) = ab + nℤ`
(§1.2, Ex. 1.12, p. 9). -/
def znMul (n : ℕ) : Zn n → Zn n → Zn n :=
  Quotient.lift₂ (fun a b : ℤ => (QuotientAddGroup.mk (a * b) : Zn n)) (by
    intro a₁ b₁ a₂ b₂ ha hb
    have ha' : -a₁ + a₂ ∈ AddSubgroup.zmultiples (n : ℤ) :=
      QuotientAddGroup.eq.mp (Quotient.sound ha)
    have hb' : -b₁ + b₂ ∈ AddSubgroup.zmultiples (n : ℤ) :=
      QuotientAddGroup.eq.mp (Quotient.sound hb)
    apply QuotientAddGroup.eq.mpr
    change -(a₁ * b₁) + a₂ * b₂ ∈ AddSubgroup.zmultiples (n : ℤ)
    have hdiff := exercise_1_12_well_defined n
      (show a₂ - a₁ ∈ AddSubgroup.zmultiples (n : ℤ) by convert ha' using 1; ring)
      (show b₂ - b₁ ∈ AddSubgroup.zmultiples (n : ℤ) by convert hb' using 1; ring)
    convert hdiff using 1
    ring)

theorem znAddEquivZMod_map_mul (n : ℕ) (x y : Zn n) :
    znAddEquivZMod n (znMul n x y) = znAddEquivZMod n x * znAddEquivZMod n y := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  exact Int.cast_mul a b

/-- **Exercise 1.12** (§1.2, p. 9): `ℤ_n` equipped with its addition and the coset multiplication
`znMul n` is a field (in Garling's §1.2 sense) if and only if `n` is a prime number. -/
theorem exercise_1_12 (n : ℕ) :
    IsGarlingField (Zn n) (· + ·) (znMul n) ↔ Nat.Prime n := by
  let e := znAddEquivZMod n
  constructor
  · rintro ⟨zero, one, hne01, _, _, hzero, _, _, hmul_nz, _, _, hone, hinv, _⟩
    have hz0 : zero = 0 := by
      have := (hzero 0).2
      simpa using this
    subst hz0
    have he1 : e one = 1 := by
      have h1ne0 : e.symm 1 ≠ 0 := by
        intro h
        have h10 : (1 : ZMod n) = 0 := by simpa using congrArg e h
        have hall0 : ∀ z : ZMod n, z = 0 := fun z => by
          calc z = z * 1 := (mul_one z).symm
            _ = z * 0 := by rw [h10]
            _ = 0 := mul_zero z
        exact hne01 (e.injective (by rw [map_zero, hall0 (e one)] )).symm
      have := (hone (e.symm 1) h1ne0).1
      have hm := znAddEquivZMod_map_mul n one (e.symm 1)
      rw [this, e.apply_symm_apply] at hm
      simpa using hm.symm
    have hn1 : n ≠ 1 := by
      intro rfl
      have hsub : Subsingleton (ZMod 1) := inferInstance
      exact hne01 (e.injective (Subsingleton.elim _ _))
    have hn0 : n ≠ 0 := by
      intro rfl
      let f : ZMod 0 →+* ℤ := ZMod.castHom (dvd_refl 0) ℤ
      have h2ne0 : e.symm 2 ≠ 0 := by
        intro h
        have h20 : f 2 = f 0 := congrArg f (by simpa using congrArg e h)
        simp only [map_ofNat, map_zero] at h20
        omega
      obtain ⟨u, _, hu1, _⟩ := hinv (e.symm 2) h2ne0
      have hm := znAddEquivZMod_map_mul 0 (e.symm 2) u
      rw [hu1, he1, e.apply_symm_apply] at hm
      have hf := congrArg f hm
      simp only [map_one, map_mul, map_ofNat] at hf
      omega
    have hn2 : 2 ≤ n := by omega
    by_contra hnotp
    let p := n.minFac
    have hp_prime : Nat.Prime p := Nat.minFac_prime hn1
    have hp_dvd : p ∣ n := Nat.minFac_dvd n
    rcases hp_dvd with ⟨q, hq⟩
    have hq_gt1 : 1 < q := by
      by_contra hqle
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp at hq; omega
      · simp at hq; exact hnotp (hq ▸ hp_prime)
    have hp_lt : p < n := by nlinarith [hp_prime.two_le]
    have hq_lt : q < n := by nlinarith [hp_prime.two_le]
    have : NeZero n := ⟨hn0⟩
    have hpZ : (p : ZMod n) ≠ 0 := by
      intro hp0
      have hdvd : n ∣ p := (ZMod.natCast_eq_zero_iff p n).mp hp0
      exact Nat.not_le_of_gt hp_lt (Nat.le_of_dvd hp_prime.pos hdvd)
    have hqZ : (q : ZMod n) ≠ 0 := by
      intro hq0
      have hdvd : n ∣ q := (ZMod.natCast_eq_zero_iff q n).mp hq0
      exact Nat.not_le_of_gt hq_lt (Nat.le_of_dvd (by omega) hdvd)
    have hpZn : e.symm (p : ZMod n) ≠ 0 := fun h => hpZ (by simpa using congrArg e h)
    have hqZn : e.symm (q : ZMod n) ≠ 0 := fun h => hqZ (by simpa using congrArg e h)
    have hprod_nz := hmul_nz _ _ hpZn hqZn
    apply hprod_nz
    apply e.injective
    rw [map_zero, znAddEquivZMod_map_mul, e.apply_symm_apply, e.apply_symm_apply,
        ← Nat.cast_mul, ← hq, ZMod.natCast_self]
  · intro hp
    have : Fact (Nat.Prime n) := ⟨hp⟩
    have he_mul : ∀ x y : Zn n, e (znMul n x y) = e x * e y := znAddEquivZMod_map_mul n
    refine ⟨0, e.symm 1, ?_,
      fun x y z => (add_assoc x y z).symm,
      add_comm,
      fun x => ⟨zero_add x, add_zero x⟩,
      fun x => ⟨-x, add_neg_cancel x, neg_add_cancel x⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have : (0 : ZMod n) = 1 := by simpa using congrArg e h
      exact zero_ne_one this
    · intro x
      constructor <;> apply e.injective <;> simp [he_mul]
    · intro x y hx hy hxy
      have hx' : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
      have hy' : e y ≠ 0 := fun h => hy (e.injective (by simpa using h))
      have h0 : e x * e y = 0 := by
        have := congrArg e hxy
        rwa [he_mul, map_zero] at this
      exact mul_ne_zero hx' hy' h0
    · intro x y z _ _ _
      apply e.injective
      simp [he_mul, mul_assoc]
    · intro x y _ _
      apply e.injective
      simp [he_mul, mul_comm]
    · intro x _
      constructor <;> apply e.injective <;> simp [he_mul]
    · intro x hx
      have hx' : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
      refine ⟨e.symm (e x)⁻¹, ?_, ?_, ?_⟩
      · intro h
        exact inv_ne_zero hx' (by simpa using congrArg e h)
      · apply e.injective
        simp [he_mul, mul_inv_cancel₀ hx']
      · apply e.injective
        simp [he_mul, inv_mul_cancel₀ hx']
    · intro x y z
      apply e.injective
      simp [he_mul, mul_add]

/-- A subset `S ⊆ ℂ` is a subfield of `ℂ` if it is the carrier of a `Subfield ℂ` (§1.2, Ex. 1.13). -/
def IsComplexSubfield (S : Set ℂ) : Prop :=
  ∃ F : Subfield ℂ, (F : Set ℂ) = S

/-- Candidate subset `(i)` of Exercise 1.13: `{a + ib : a, b ∈ ℚ}` (§1.2, p. 9). -/
def set_1_13_i : Set ℂ :=
  {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + Complex.I * (b : ℂ)}

/-- `ω = (-1 + √3 i) / 2` in Exercise 1.13(ii) (§1.2, p. 9). -/
noncomputable def garlingOmega : ℂ :=
  (1 / 2 : ℂ) * (-1 + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I)

/-- Candidate subset `(ii)` of Exercise 1.13: `{a + ωb : a, b ∈ ℚ}` (§1.2, p. 9). -/
def set_1_13_ii : Set ℂ :=
  {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + garlingOmega * (b : ℂ)}

/-- Real cube root `2^{1/3}` cast to `ℂ` (§1.2, Ex. 1.13, p. 9). -/
noncomputable def cbrtTwo : ℂ := (((2 : ℝ) ^ ((1 : ℝ) / 3) : ℝ) : ℂ)

/-- Real cube root `4^{1/3}` cast to `ℂ` (§1.2, Ex. 1.13, p. 9). -/
noncomputable def cbrtFour : ℂ := (((4 : ℝ) ^ ((1 : ℝ) / 3) : ℝ) : ℂ)

/-- Candidate subset `(iii)` of Exercise 1.13: `{a + 2^{1/3} b : a, b ∈ ℚ}` (§1.2, p. 9). -/
def set_1_13_iii : Set ℂ :=
  {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + cbrtTwo * (b : ℂ)}

/-- Candidate subset `(iv)` of Exercise 1.13: `{a + 2^{1/3} b + 4^{1/3} c : a, b, c ∈ ℚ}` (§1.2, p. 9). -/
def set_1_13_iv : Set ℂ :=
  {z : ℂ | ∃ a b c : ℚ, z = (a : ℂ) + cbrtTwo * (b : ℂ) + cbrtFour * (c : ℂ)}

private lemma garlingOmega_sq : garlingOmega ^ 2 = -garlingOmega - 1 := by
  unfold garlingOmega
  have h3 : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  calc ((1 / 2 : ℂ) * (-1 + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I)) ^ 2
    _ = (1 / 4 : ℂ) * (1 - 2 * ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I +
          (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 * Complex.I ^ 2) := by ring
    _ = (1 / 4 : ℂ) * (1 - 2 * ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I + 3 * (-1)) := by
        rw [h3, Complex.I_sq]
    _ = -((1 / 2 : ℂ) * (-1 + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I)) - 1 := by ring

private lemma rCbrtTwo_cubed : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma rCbrtFour_eq_sq : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), sq]

private lemma cbrtTwo_cubed : cbrtTwo ^ 3 = 2 := by
  unfold cbrtTwo
  exact_mod_cast rCbrtTwo_cubed

private lemma cbrtFour_eq_sq : cbrtFour = cbrtTwo ^ 2 := by
  unfold cbrtFour cbrtTwo
  exact_mod_cast rCbrtFour_eq_sq

private lemma even_of_cube_even {x : ℤ} (h : 2 ∣ x ^ 3) : 2 ∣ x := by
  rcases Int.emod_two_eq_zero_or_one x with h0 | h1
  · exact Int.dvd_of_emod_eq_zero h0
  · exfalso
    rcases h with ⟨k, hk⟩
    let q := x / 2
    have hx : x = 2 * q + 1 := by omega
    rw [hx] at hk
    have : (2 * q + 1) ^ 3 = 2 * (4 * q ^ 3 + 6 * q ^ 2 + 3 * q) + 1 := by ring
    omega

private lemma int_cubic_form_eq_zero :
    ∀ n : ℕ, ∀ {A B C : ℤ}, A.natAbs + B.natAbs + C.natAbs ≤ n →
      A ^ 3 + 2 * B ^ 3 + 4 * C ^ 3 - 6 * A * B * C = 0 →
      A = 0 ∧ B = 0 ∧ C = 0
  | 0, A, B, C, hle, _ => by omega
  | n + 1, A, B, C, hle, h0 => by
    by_cases hall : A = 0 ∧ B = 0 ∧ C = 0
    · exact hall
    · have hA_even : 2 ∣ A := even_of_cube_even ⟨-B ^ 3 - 2 * C ^ 3 + 3 * A * B * C, by linarith⟩
      rcases hA_even with ⟨A₁, rfl⟩
      have h1 : B ^ 3 + 2 * C ^ 3 + 4 * A₁ ^ 3 - 6 * B * C * A₁ = 0 := by linarith
      have hB_even : 2 ∣ B := even_of_cube_even ⟨-C ^ 3 - 2 * A₁ ^ 3 + 3 * B * C * A₁, by linarith⟩
      rcases hB_even with ⟨B₁, rfl⟩
      have h2 : C ^ 3 + 2 * A₁ ^ 3 + 4 * B₁ ^ 3 - 6 * C * A₁ * B₁ = 0 := by linarith
      have hC_even : 2 ∣ C := even_of_cube_even ⟨-A₁ ^ 3 - 2 * B₁ ^ 3 + 3 * C * A₁ * B₁, by linarith⟩
      rcases hC_even with ⟨C₁, rfl⟩
      have h3 : A₁ ^ 3 + 2 * B₁ ^ 3 + 4 * C₁ ^ 3 - 6 * A₁ * B₁ * C₁ = 0 := by linarith
      have hpos : 0 < A₁.natAbs + B₁.natAbs + C₁.natAbs := by
        by_contra hzero
        have : A₁ = 0 ∧ B₁ = 0 ∧ C₁ = 0 := by omega
        rcases this with ⟨rfl, rfl, rfl⟩
        exact hall ⟨rfl, rfl, rfl⟩
      have hsum : (2 * A₁).natAbs + (2 * B₁).natAbs + (2 * C₁).natAbs =
          2 * (A₁.natAbs + B₁.natAbs + C₁.natAbs) := by
        simp [Int.natAbs_mul]
        omega
      have hlt : A₁.natAbs + B₁.natAbs + C₁.natAbs ≤ n := by omega
      rcases int_cubic_form_eq_zero n hlt h3 with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

private lemma rat_cubic_form_eq_zero {a b c : ℚ}
    (h : a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let D : ℕ := a.den * b.den * c.den
  have hD_pos : 0 < D := by positivity
  let A : ℤ := a.num * b.den * c.den
  let B : ℤ := b.num * a.den * c.den
  let C : ℤ := c.num * a.den * b.den
  have ha : (A : ℚ) = a * D := by
    simp only [A, D, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.pos.ne'
    calc (a.num : ℚ) * (b.den : ℚ) * (c.den : ℚ)
      _ = ((a.num : ℚ) / (a.den : ℚ)) * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by
          field_simp
      _ = a * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by rw [Rat.num_div_den]
  have hb : (B : ℚ) = b * D := by
    simp only [B, D, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.pos.ne'
    calc (b.num : ℚ) * (a.den : ℚ) * (c.den : ℚ)
      _ = ((b.num : ℚ) / (b.den : ℚ)) * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by
          field_simp
      _ = b * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by rw [Rat.num_div_den]
  have hc : (C : ℚ) = c * D := by
    simp only [C, D, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have : (c.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr c.pos.ne'
    calc (c.num : ℚ) * (a.den : ℚ) * (b.den : ℚ)
      _ = ((c.num : ℚ) / (c.den : ℚ)) * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by
          field_simp
      _ = c * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by rw [Rat.num_div_den]
  have hQ : ((A ^ 3 + 2 * B ^ 3 + 4 * C ^ 3 - 6 * A * B * C : ℤ) : ℚ) = 0 := by
    push_cast
    rw [ha, hb, hc]
    calc (a * D) ^ 3 + 2 * (b * D) ^ 3 + 4 * (c * D) ^ 3 - 6 * (a * D) * (b * D) * (c * D)
      _ = (a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c) * (D : ℚ) ^ 3 := by ring
      _ = 0 := by rw [h, zero_mul]
  have hZ : A ^ 3 + 2 * B ^ 3 + 4 * C ^ 3 - 6 * A * B * C = 0 := Int.cast_eq_zero.mp hQ
  rcases int_cubic_form_eq_zero (A.natAbs + B.natAbs + C.natAbs) le_rfl hZ with ⟨hA0, hB0, hC0⟩
  have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by simpa [hA0] using ha.symm)).resolve_right hDQ
  · exact (mul_eq_zero.mp (by simpa [hB0] using hb.symm)).resolve_right hDQ
  · exact (mul_eq_zero.mp (by simpa [hC0] using hc.symm)).resolve_right hDQ

private lemma cbrtTwo_norm_identity (a b c : ℚ) :
    ((a : ℂ) + cbrtTwo * (b : ℂ) + cbrtTwo ^ 2 * (c : ℂ)) *
      (((a ^ 2 - 2 * b * c : ℚ) : ℂ) + cbrtTwo * ((2 * c ^ 2 - a * b : ℚ) : ℂ) +
        cbrtTwo ^ 2 * ((b ^ 2 - a * c : ℚ) : ℂ)) =
      ((a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c : ℚ) : ℂ) := by
  have h3 := cbrtTwo_cubed
  push_cast
  linear_combination
    ((b : ℂ) ^ 3 + 2 * (c : ℂ) ^ 3 - 2 * (a : ℂ) * (b : ℂ) * (c : ℂ) +
      ((b : ℂ) ^ 2 * (c : ℂ) - (a : ℂ) * (c : ℂ) ^ 2) * cbrtTwo) * h3

/-- **Exercise 1.13** (§1.2, p. 9): Complete determination of which of the four subsets `(i)`–`(iv)`
are subfields of `ℂ`: `(i)` Yes, `(ii)` Yes, `(iii)` No, `(iv)` Yes. -/
theorem exercise_1_13 :
    IsComplexSubfield set_1_13_i ∧
    IsComplexSubfield set_1_13_ii ∧
    ¬ IsComplexSubfield set_1_13_iii ∧
    IsComplexSubfield set_1_13_iv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) Q(i) is a subfield of C
    refine ⟨{
      carrier := set_1_13_i
      mul_mem' := by
        rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
        refine ⟨a₁ * a₂ - b₁ * b₂, a₁ * b₂ + b₁ * a₂, ?_⟩
        have hI : Complex.I ^ 2 = -1 := Complex.I_sq
        push_cast
        linear_combination (b₁ : ℂ) * (b₂ : ℂ) * hI
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
        exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨-a, -b, by push_cast; ring⟩
      inv_mem' := by
        rintro z ⟨a, b, rfl⟩
        by_cases hab : a = 0 ∧ b = 0
        · rcases hab with ⟨rfl, rfl⟩
          exact ⟨0, 0, by simp⟩
        · have hd_pos : 0 < a ^ 2 + b ^ 2 := by
            rcases not_and_or.mp hab with ha | hb
            · have : 0 < a ^ 2 := sq_pos_of_ne_zero ha
              positivity
            · have : 0 < b ^ 2 := sq_pos_of_ne_zero hb
              positivity
          let d : ℚ := a ^ 2 + b ^ 2
          refine ⟨a / d, -b / d, ?_⟩
          apply inv_eq_of_mul_eq_one_right
          have hI : Complex.I ^ 2 = -1 := Complex.I_sq
          have hdC : (d : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd_pos.ne'
          have hnum : ((a : ℂ) + Complex.I * (b : ℂ)) * ((a : ℂ) - Complex.I * (b : ℂ)) =
              (d : ℂ) := by
            simp only [d]
            push_cast
            linear_combination -(b : ℂ) ^ 2 * hI
          calc ((a : ℂ) + Complex.I * (b : ℂ)) *
                (((a / d : ℚ) : ℂ) + Complex.I * ((-b / d : ℚ) : ℂ))
            _ = (((a : ℂ) + Complex.I * (b : ℂ)) * ((a : ℂ) - Complex.I * (b : ℂ))) / (d : ℂ) := by
                push_cast; ring
            _ = (d : ℂ) / (d : ℂ) := by rw [hnum]
            _ = 1 := div_self hdC
    }, rfl⟩
  · -- (ii) Q(ω) is a subfield of C
    refine ⟨{
      carrier := set_1_13_ii
      mul_mem' := by
        rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
        refine ⟨a₁ * a₂ - b₁ * b₂, a₁ * b₂ + b₁ * a₂ - b₁ * b₂, ?_⟩
        push_cast
        linear_combination (b₁ : ℂ) * (b₂ : ℂ) * garlingOmega_sq
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
        exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, b, rfl⟩
        exact ⟨-a, -b, by push_cast; ring⟩
      inv_mem' := by
        rintro z ⟨a, b, rfl⟩
        by_cases hab : a = 0 ∧ b = 0
        · rcases hab with ⟨rfl, rfl⟩
          exact ⟨0, 0, by simp⟩
        · have hd_pos : 0 < a ^ 2 - a * b + b ^ 2 := by
            have hid : 4 * (a ^ 2 - a * b + b ^ 2) = (2 * a - b) ^ 2 + 3 * b ^ 2 := by ring
            rcases not_and_or.mp hab with ha | hb
            · by_cases hb0 : b = 0
              · subst hb0; nlinarith [sq_pos_of_ne_zero ha]
              · nlinarith [sq_pos_of_ne_zero hb0, sq_nonneg (2 * a - b)]
            · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg (2 * a - b)]
          let d : ℚ := a ^ 2 - a * b + b ^ 2
          refine ⟨(a - b) / d, -b / d, ?_⟩
          apply inv_eq_of_mul_eq_one_right
          have hdC : (d : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd_pos.ne'
          have hprod : ((a : ℂ) + garlingOmega * (b : ℂ)) *
              (((a : ℂ) - (b : ℂ)) + garlingOmega * (-(b : ℂ))) = (d : ℂ) := by
            simp only [d]
            push_cast
            linear_combination -(b : ℂ) ^ 2 * garlingOmega_sq
          calc ((a : ℂ) + garlingOmega * (b : ℂ)) *
                ((((a - b) / d : ℚ) : ℂ) + garlingOmega * ((-b / d : ℚ) : ℂ))
            _ = (((a : ℂ) + garlingOmega * (b : ℂ)) *
                  (((a : ℂ) - (b : ℂ)) + garlingOmega * (-(b : ℂ)))) / (d : ℂ) := by
                push_cast; ring
            _ = (d : ℂ) / (d : ℂ) := by rw [hprod]
            _ = 1 := div_self hdC
    }, rfl⟩
  · -- (iii) {a + 2^{1/3} b : a, b ∈ Q} is NOT a subfield of C
    rintro ⟨F, hF⟩
    have hcbrt_mem : cbrtTwo ∈ F := by
      change cbrtTwo ∈ (F : Set ℂ)
      rw [hF]
      exact ⟨0, 1, by simp⟩
    have hsq_mem : cbrtTwo * cbrtTwo ∈ (F : Set ℂ) := F.mul_mem hcbrt_mem hcbrt_mem
    rw [hF] at hsq_mem
    rcases hsq_mem with ⟨a, b, hab⟩
    have hlin : (a : ℂ) + cbrtTwo * (b : ℂ) + cbrtTwo ^ 2 * ((-1 : ℚ) : ℂ) = 0 := by
      push_cast
      linear_combination -hab
    have hnorm := cbrtTwo_norm_identity a b (-1)
    rw [hlin, zero_mul] at hnorm
    have hrat : a ^ 3 + 2 * b ^ 3 + 4 * (-1 : ℚ) ^ 3 - 6 * a * b * (-1) = 0 :=
      Rat.cast_eq_zero.mp hnorm.symm
    have hc0 := (rat_cubic_form_eq_zero hrat).2.2
    norm_num at hc0
  · -- (iv) {a + 2^{1/3} b + 4^{1/3} c : a, b, c ∈ Q} IS a subfield of C
    refine ⟨{
      carrier := set_1_13_iv
      mul_mem' := by
        rintro _ _ ⟨a₁, b₁, c₁, rfl⟩ ⟨a₂, b₂, c₂, rfl⟩
        refine ⟨a₁ * a₂ + 2 * b₁ * c₂ + 2 * c₁ * b₂,
                a₁ * b₂ + b₁ * a₂ + 2 * c₁ * c₂,
                a₁ * c₂ + b₁ * b₂ + c₁ * a₂, ?_⟩
        rw [cbrtFour_eq_sq]
        push_cast
        linear_combination
          ((b₁ : ℂ) * (c₂ : ℂ) + (c₁ : ℂ) * (b₂ : ℂ) + (c₁ : ℂ) * (c₂ : ℂ) * cbrtTwo) *
            cbrtTwo_cubed
      one_mem' := ⟨1, 0, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, c₁, rfl⟩ ⟨a₂, b₂, c₂, rfl⟩
        exact ⟨a₁ + a₂, b₁ + b₂, c₁ + c₂, by push_cast; ring⟩
      zero_mem' := ⟨0, 0, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, b, c, rfl⟩
        exact ⟨-a, -b, -c, by push_cast; ring⟩
      inv_mem' := by
        rintro z ⟨a, b, c, rfl⟩
        by_cases habc : a = 0 ∧ b = 0 ∧ c = 0
        · rcases habc with ⟨rfl, rfl, rfl⟩
          exact ⟨0, 0, 0, by simp⟩
        · let d : ℚ := a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c
          have hd_ne : d ≠ 0 := fun hd0 => habc (rat_cubic_form_eq_zero hd0)
          refine ⟨(a ^ 2 - 2 * b * c) / d, (2 * c ^ 2 - a * b) / d, (b ^ 2 - a * c) / d, ?_⟩
          apply inv_eq_of_mul_eq_one_right
          rw [cbrtFour_eq_sq]
          have hnorm := cbrtTwo_norm_identity a b c
          have hdC : (d : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hd_ne
          calc ((a : ℂ) + cbrtTwo * (b : ℂ) + cbrtTwo ^ 2 * (c : ℂ)) *
                ((((a ^ 2 - 2 * b * c) / d : ℚ) : ℂ) +
                  cbrtTwo * (((2 * c ^ 2 - a * b) / d : ℚ) : ℂ) +
                  cbrtTwo ^ 2 * (((b ^ 2 - a * c) / d : ℚ) : ℂ))
            _ = (((a : ℂ) + cbrtTwo * (b : ℂ) + cbrtTwo ^ 2 * (c : ℂ)) *
                  (((a ^ 2 - 2 * b * c : ℚ) : ℂ) + cbrtTwo * ((2 * c ^ 2 - a * b : ℚ) : ℂ) +
                    cbrtTwo ^ 2 * ((b ^ 2 - a * c : ℚ) : ℂ))) / (d : ℂ) := by
                push_cast; ring
            _ = (d : ℂ) / (d : ℂ) := by rw [hnorm]
            _ = 1 := div_self hdC
    }, rfl⟩

/-! ## §1.3 Vector spaces (printed pp. 9–13) -/

/-- The function vector space `K^S` of mappings `S → K` (§1.3, p. 9). -/
abbrev FunSpace (S K : Type*) := S → K

/-- The coordinate vector space `K^n` (`Fin n → K`) (§1.3, p. 9). -/
abbrev Kn (n : ℕ) (K : Type*) := Fin n → K

/-- The span `span(A)` of a subset `A ⊆ V` over `K` (§1.3, p. 10). -/
abbrev garlingSpan (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (A : Set V) : Submodule K V :=
  Submodule.span K A

/-- `A` spans `V` over `K` if `span(A) = V` (§1.3, p. 10). -/
def Spans (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    (A : Set V) : Prop :=
  Submodule.span K A = ⊤

/-- Garling's subset linear dependence over `K` (§1.3, p. 10): there exist finitely many distinct
elements `x₁, ..., x_k` of `A` and scalars `c₁, ..., c_k` in `K`, not all zero, such that
`∑ i, c_i • x_i = 0`. -/
def IsLinearlyDependent (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (A : Set V) : Prop :=
  ∃ (k : ℕ) (x : Fin k → V) (c : Fin k → K),
    Function.Injective x ∧ (∀ i, x i ∈ A) ∧ (∃ i, c i ≠ 0) ∧ ∑ i, c i • x i = 0

/-- Garling's subset linear independence over `K` (§1.3, p. 10): `A` is not linearly dependent
over `K`. -/
def IsLinearlyIndependent (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (A : Set V) : Prop :=
  ¬ IsLinearlyDependent K A

theorem IsLinearlyIndependent.mono {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {A B : Set V} (hAB : A ⊆ B)
    (hB : IsLinearlyIndependent K B) : IsLinearlyIndependent K A := by
  rintro ⟨k, x, c, hx_inj, hxA, hnz, hsum⟩
  exact hB ⟨k, x, c, hx_inj, fun i => hAB (hxA i), hnz, hsum⟩

theorem empty_isLinearlyIndependent (K : Type*) [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] : IsLinearlyIndependent K (∅ : Set V) := by
  rintro ⟨_, x, _, _, hx, ⟨i₀, _⟩, _⟩
  exact hx i₀

/-- Equivalence between Garling's subset `IsLinearlyIndependent K A` and Mathlib's
`LinearIndepOn K id A` (`LinearIndependent K ((↑) : A → V)`). -/
theorem isLinearlyIndependent_iff {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (A : Set V) :
    IsLinearlyIndependent K A ↔ LinearIndepOn K id A := by
  rw [IsLinearlyIndependent, IsLinearlyDependent, LinearIndepOn, linearIndependent_iff']
  constructor
  · intro hnot s g hsum a ha
    by_contra hga
    classical
    let e : Fin s.card ≃ s := s.equivFin.symm
    apply hnot
    refine ⟨s.card, fun i => ((e i : s) : A).1, fun i => g (e i : s).1, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext (Subtype.ext hij))
    · intro i
      exact ((e i : s) : A).2
    · refine ⟨e.symm ⟨a, ha⟩, ?_⟩
      simp [hga]
    · have hsum' : ∑ x : s, g x.1 • (x.1 : V) = ∑ x ∈ s, g x • (x : V) :=
        s.sum_coe_sort (fun x : A => g x • (x : V))
      have hcomp : (∑ i : Fin s.card, g (e i : s).1 • (((e i : s) : A).1 : V)) =
          ∑ x : s, g x.1 • (x.1 : V) :=
        Equiv.sum_comp e (fun x : s => g x.1 • (x.1 : V))
      rw [hcomp, hsum']
      exact hsum
  · rintro hli ⟨k, x, c, hx_inj, hxA, ⟨i₀, hc₀⟩, hsum⟩
    let f : Fin k → A := fun i => ⟨x i, hxA i⟩
    have hf_inj : Function.Injective f := fun i j hij => hx_inj (congrArg Subtype.val hij)
    have hli_k : LinearIndependent K x := (linearIndependent_iff'.mpr hli).comp f hf_inj
    exact hc₀ (linearIndependent_iff'.mp hli_k Finset.univ c hsum i₀ (Finset.mem_univ i₀))

/-- A subset `B ⊆ V` is a basis for `V` over `K` if it is linearly independent and spans `V`
(§1.3, p. 10). -/
def IsBasis (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    (B : Set V) : Prop :=
  IsLinearlyIndependent K B ∧ Spans K V B

/-- `V` is finite-dimensional over `K` if there exists a finite subset of `V` spanning `V`
(§1.3, p. 10). -/
def IsFiniteDimensional (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] :
    Prop :=
  ∃ A : Set V, A.Finite ∧ Spans K V A

/-! ### Main-text results in §1.3 (Theorems 1.1–1.4 and Corollaries, printed pp. 10–12) -/

/-- **Theorem 1.1** (§1.3, p. 10): If `A` is a finite subset of a vector space `V` over `K` that
spans `V`, and `C ⊆ A` is linearly independent (`C` possibly empty), then there exists a basis `B`
of `V` with `C ⊆ B ⊆ A`. -/
theorem theorem_1_1 {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {A C : Set V} (hAfin : A.Finite) (hAspan : Spans K V A)
    (hCA : C ⊆ A) (hCind : IsLinearlyIndependent K C) :
    ∃ B : Set V, C ⊆ B ∧ B ⊆ A ∧ IsBasis K V B := by
  classical
  have hCfin : C.Finite := hAfin.subset hCA
  let A₀ : Finset V := hAfin.toFinset
  let C₀ : Finset V := hCfin.toFinset
  let 𝒞 : Finset (Finset V) :=
    A₀.powerset.filter (fun S => C₀ ⊆ S ∧ IsLinearlyIndependent K (S : Set V))
  have hC₀_mem : C₀ ∈ 𝒞 := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, Finset.Subset.refl _, ?_⟩
    · intro x hx
      exact hAfin.mem_toFinset.mpr (hCA (hCfin.mem_toFinset.mp hx))
    · simpa [C₀, hCfin.coe_toFinset] using hCind
  obtain ⟨B₀, hB₀_mem, hB₀_max⟩ := Finset.exists_max_image 𝒞 Finset.card ⟨C₀, hC₀_mem⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hB₀_mem
  rcases hB₀_mem with ⟨hB₀A₀, hC₀B₀, hB₀ind⟩
  refine ⟨(B₀ : Set V), ?_, ?_, hB₀ind, ?_⟩
  · intro x hx
    exact hC₀B₀ (hCfin.mem_toFinset.mpr hx)
  · intro x hx
    exact hAfin.mem_toFinset.mp (hB₀A₀ hx)
  · rw [Spans, eq_top_iff, ← hAspan, Submodule.span_le]
    intro a haA
    by_cases haB : a ∈ (B₀ : Set V)
    · exact Submodule.subset_span haB
    · have ha_notB₀ : a ∉ B₀ := haB
      have hnot_mem : insert a B₀ ∉ 𝒞 := by
        intro hmem
        have hle := hB₀_max (insert a B₀) hmem
        rw [Finset.card_insert_of_notMem ha_notB₀] at hle
        omega
      have hins_sub : insert a B₀ ⊆ A₀ :=
        Finset.insert_subset (hAfin.mem_toFinset.mpr haA) hB₀A₀
      have hC₀_ins : C₀ ⊆ insert a B₀ := hC₀B₀.trans (Finset.subset_insert a B₀)
      have hnot_ind : ¬ IsLinearlyIndependent K ((insert a B₀ : Finset V) : Set V) := by
        intro hind
        apply hnot_mem
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hins_sub, hC₀_ins, hind⟩
      rw [Finset.coe_insert, isLinearlyIndependent_iff, linearIndepOn_id_insert haB] at hnot_ind
      have hliB : LinearIndepOn K id (B₀ : Set V) := (isLinearlyIndependent_iff _).mp hB₀ind
      by_contra ha_nspan
      exact hnot_ind ⟨hliB, ha_nspan⟩

private lemma steinitz_exchange_finset {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [DecidableEq V]
    (C₀ A₀ : Finset V) (hCind : IsLinearlyIndependent K (C₀ : Set V))
    (hAspan : Spans K V (A₀ : Set V)) :
    ∃ D₀ : Finset V, C₀ ⊆ D₀ ∧ D₀ ⊆ A₀ ∪ C₀ ∧ D₀.card = A₀.card ∧ Spans K V (D₀ : Set V) := by
  induction C₀ using Finset.induction_on with
  | empty =>
    exact ⟨A₀, Finset.empty_subset _, Finset.subset_union_left, rfl, hAspan⟩
  | insert c C' hcC' ih =>
    have hC'ind : IsLinearlyIndependent K (C' : Set V) :=
      hCind.mono (by simp [Finset.coe_insert, Set.subset_insert])
    obtain ⟨D', hC'D', hD'sub, hD'card, hD'span⟩ := ih hC'ind
    by_cases hcD' : c ∈ D'
    · refine ⟨D', Finset.insert_subset hcD' hC'D', ?_, hD'card, hD'span⟩
      exact hD'sub.trans (Finset.union_subset_union_right (Finset.subset_insert c C'))
    · have hc_nspanC' : c ∉ Submodule.span K (C' : Set V) := by
        have hli := (isLinearlyIndependent_iff _).mp hCind
        rw [Finset.coe_insert, linearIndepOn_id_insert hcC'] at hli
        exact hli.2
      have hc_spanD' : c ∈ Submodule.span K (D' : Set V) := by
        rw [hD'span]
        exact Submodule.mem_top
      obtain ⟨f, _, hf_sum⟩ := Submodule.mem_span_finset.mp hc_spanD'
      have hex : ∃ a ∈ D', a ∉ C' ∧ f a ≠ 0 := by
        by_contra hnone
        push Not at hnone
        apply hc_nspanC'
        have hsum_eq : ∑ x ∈ D', f x • x = ∑ x ∈ C', f x • x := by
          refine (Finset.sum_subset hC'D' ?_).symm
          intro x hxD' hxnotC'
          rw [hnone x hxD' hxnotC', zero_smul]
        rw [← hf_sum, hsum_eq]
        exact Submodule.mem_span_finset.mpr
          ⟨fun x => if x ∈ C' then f x else 0,
           fun x hx => by
             simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hx
             exact hx.1,
           Finset.sum_congr rfl (fun x hx => by simp [hx])⟩
      obtain ⟨a, haD', ha_notC', hfa_ne⟩ := hex
      let D₀ : Finset V := insert c (D'.erase a)
      have hc_not_erase : c ∉ D'.erase a := fun h => hcD' (Finset.mem_of_mem_erase h)
      refine ⟨D₀, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxc | hxC'
        · rw [hxc]
          exact Finset.mem_insert_self c _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨fun hxa => ha_notC' (hxa ▸ hxC'), hC'D' hxC'⟩)
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxc | hx_er
        · rw [hxc]
          exact Finset.mem_union_right _ (Finset.mem_insert_self c C')
        · have hxD' := Finset.mem_of_mem_erase hx_er
          exact Finset.union_subset_union_right (Finset.subset_insert c C') (hD'sub hxD')
      · have hpos : 1 ≤ D'.card := Finset.one_le_card.mpr ⟨a, haD'⟩
        rw [Finset.card_insert_of_notMem hc_not_erase, Finset.card_erase_of_mem haD']
        omega
      · rw [Spans, eq_top_iff, ← hD'span, Submodule.span_le]
        intro x hxD'
        by_cases hxa : x = a
        · subst hxa
          have hsum_er := Finset.add_sum_erase D' (fun y => f y • y) hxD'
          rw [hf_sum] at hsum_er
          have hx_eq : x = (f x)⁻¹ • (c - ∑ y ∈ D'.erase x, f y • y) := by
            have hfx : f x • x = c - ∑ y ∈ D'.erase x, f y • y := eq_sub_of_add_eq hsum_er
            rw [← hfx, inv_smul_smul₀ hfa_ne]
          rw [hx_eq]
          refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
          · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self c _))
          · refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ ?_
            exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hy))
        · exact Submodule.subset_span
            (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa, hxD'⟩)))

private lemma exists_finset_subset_card_eq {V : Type*} [DecidableEq V] {C : Set V} :
    ∀ m : ℕ, (m : ℕ∞) ≤ setOrder C → ∃ S : Finset V, (S : Set V) ⊆ C ∧ S.card = m
  | 0, _ => ⟨∅, by simp, rfl⟩
  | m + 1, hle => by
    have hm : (m : ℕ∞) ≤ setOrder C := le_trans (Nat.cast_le.mpr (Nat.le_succ m)) hle
    obtain ⟨S, hSC, hScard⟩ := exists_finset_subset_card_eq m hm
    let emb : {x // x ∈ S} ↪ C :=
      ⟨fun x => ⟨x.1, hSC x.2⟩,
       fun a b (h : (⟨a.1, hSC a.2⟩ : C) = ⟨b.1, hSC b.2⟩) =>
         Subtype.ext (congrArg (Subtype.val : C → V) h)⟩
    let S' : Finset C := S.attach.map emb
    have hS'lt : (S'.card : ℕ∞) < ENat.card C := by
      rw [Finset.card_map, Finset.card_attach, hScard]
      exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) hle
    obtain ⟨y, hy⟩ := Finset.exists_not_mem_of_card_lt_enatCard hS'lt
    have hy_notS : y.1 ∉ S := by
      intro hyS
      apply hy
      rw [Finset.mem_map]
      exact ⟨⟨y.1, hyS⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
    refine ⟨insert y.1 S, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset y.2 hSC
    · rw [Finset.card_insert_of_notMem hy_notS, hScard]

private lemma setOrder_eq_toFinset_card {V : Type*} {A : Set V} (hA : A.Finite) :
    setOrder A = (hA.toFinset.card : ℕ∞) := by
  have : Fintype A := hA.fintype
  rw [setOrder, ENat.card_eq_coe_fintype_card, Set.Finite.card_toFinset]

/-- **Theorem 1.2** (§1.3, p. 11): In a vector space `V` over `K`, if `A` spans `V` and `C ⊆ V`
is linearly independent, then `|C| ≤ |A|`. -/
theorem theorem_1_2 {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {A C : Set V} (hAspan : Spans K V A) (hCind : IsLinearlyIndependent K C) :
    setOrder C ≤ setOrder A := by
  by_cases hAfin : A.Finite
  · classical
    rw [setOrder_eq_toFinset_card hAfin]
    by_contra hnot
    have hlt : ((hAfin.toFinset.card + 1 : ℕ) : ℕ∞) ≤ setOrder C := by
      have hgt : (hAfin.toFinset.card : ℕ∞) < setOrder C := not_le.mp hnot
      exact Order.add_one_le_of_lt hgt
    obtain ⟨C₀, hC₀C, hC₀card⟩ := exists_finset_subset_card_eq (hAfin.toFinset.card + 1) hlt
    have hA₀span : Spans K V (hAfin.toFinset : Set V) := by simpa using hAspan
    obtain ⟨D₀, hC₀D₀, _, hD₀card, _⟩ :=
      steinitz_exchange_finset C₀ hAfin.toFinset (hCind.mono hC₀C) hA₀span
    have hle := Finset.card_le_card hC₀D₀
    omega
  · have htop : setOrder A = ⊤ := by
      rw [setOrder, ENat.card_eq_top]
      have : ¬ Finite A := fun h => hAfin h
      exact not_finite_iff_infinite.mp this
    rw [htop]
    exact le_top

/-- **Theorem 1.3 (The Steinitz exchange theorem)** (§1.3, p. 11): If `C ⊆ V` is linearly
independent with `|C| = r` (`r : ℕ`) and `A ⊆ V` spans `V` with `|A| = s` (`s : ℕ`), then there
exists `D ⊆ V` with `C ⊆ D ⊆ A ∪ C`, `|D| = s`, and `D` spanning `V`. -/
theorem theorem_1_3 {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {C A : Set V} {r s : ℕ}
    (hCr : setOrder C = r) (hCind : IsLinearlyIndependent K C)
    (hAs : setOrder A = s) (hAspan : Spans K V A) :
    ∃ D : Set V, C ⊆ D ∧ D ⊆ A ∪ C ∧ setOrder D = s ∧ Spans K V D := by
  classical
  have hCfin : C.Finite := ENat.card_lt_top.mp (by rw [← setOrder, hCr]; exact ENat.natCast_lt_top r)
  have hAfin : A.Finite := ENat.card_lt_top.mp (by rw [← setOrder, hAs]; exact ENat.natCast_lt_top s)
  have hAcard : hAfin.toFinset.card = s :=
    Nat.cast_injective (R := ℕ∞) (by rw [← setOrder_eq_toFinset_card hAfin, hAs])
  obtain ⟨D₀, hCD₀, hD₀sub, hD₀card, hD₀span⟩ :=
    steinitz_exchange_finset hCfin.toFinset hAfin.toFinset
      (by simpa using hCind) (by simpa using hAspan)
  refine ⟨(D₀ : Set V), ?_, ?_, ?_, hD₀span⟩
  · simpa using Finset.coe_subset.mpr hCD₀
  · have := Finset.coe_subset.mpr hD₀sub
    simpa [Finset.coe_union] using this
  · have hDfin : (D₀ : Set V).Finite := D₀.finite_toSet
    rw [setOrder_eq_toFinset_card hDfin, Finset.finite_toSet_toFinset, hD₀card, hAcard]

/-- **Corollary (to Theorem 1.2)** (§1.3, p. 12): Any two bases of a finite-dimensional vector
space have the same finite number of elements. -/
theorem corollary_to_theorem_1_2 {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V)
    {B₁ B₂ : Set V} (hB₁ : IsBasis K V B₁) (hB₂ : IsBasis K V B₂) :
    ∃ n : ℕ, setOrder B₁ = n ∧ setOrder B₂ = n := by
  obtain ⟨A, hAfin, hAspan⟩ := hV
  have hleA : setOrder B₁ ≤ setOrder A := theorem_1_2 hAspan hB₁.1
  have hlt : setOrder B₁ < ⊤ :=
    lt_of_le_of_lt hleA (by rw [setOrder_eq_toFinset_card hAfin]; exact ENat.natCast_lt_top _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  have h12 : setOrder B₁ ≤ setOrder B₂ := theorem_1_2 hB₂.2 hB₁.1
  have h21 : setOrder B₂ ≤ setOrder B₁ := theorem_1_2 hB₁.2 hB₂.1
  have heq : setOrder B₁ = setOrder B₂ := le_antisymm h12 h21
  exact ⟨n, hn.symm, heq ▸ hn.symm⟩

/-- Existence of a finite basis for any finite-dimensional vector space (§1.3, p. 10). -/
theorem exists_finite_basis {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V) :
    ∃ B : Set V, B.Finite ∧ IsBasis K V B := by
  obtain ⟨A, hAfin, hAspan⟩ := hV
  obtain ⟨B, _, hBA, hB⟩ :=
    theorem_1_1 hAfin hAspan (Set.empty_subset A) (empty_isLinearlyIndependent K)
  exact ⟨B, hAfin.subset hBA, hB⟩

/-- Garling's dimension `dim V : ℕ` of a finite-dimensional vector space `V` over `K`, defined as
the number of elements in a basis (§1.3, p. 12). -/
noncomputable def garlingDim (K : Type*) [Field K] (V : Type*)
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V) : ℕ :=
  (exists_finite_basis hV).choose_spec.1.toFinset.card

/-- Every basis `B` of a finite-dimensional vector space `V` has `|B| = dim V` (§1.3, p. 12). -/
theorem garlingDim_spec {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V)
    {B : Set V} (hB : IsBasis K V B) :
    setOrder B = garlingDim K V hV := by
  let B₀ := (exists_finite_basis hV).choose
  have hB₀fin : B₀.Finite := (exists_finite_basis hV).choose_spec.1
  have hB₀ : IsBasis K V B₀ := (exists_finite_basis hV).choose_spec.2
  obtain ⟨n, hn, hn₀⟩ := corollary_to_theorem_1_2 hV hB hB₀
  rw [setOrder_eq_toFinset_card hB₀fin] at hn₀
  have hcard : n = garlingDim K V hV := Nat.cast_injective (R := ℕ∞) hn₀.symm
  exact hcard ▸ hn

private lemma linearMap_inj_isLinearlyIndependent {K : Type*} [Field K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {φ : V₁ →ₗ[K] V₂} (hφ : Function.Injective φ) {C : Set V₁}
    (hC : IsLinearlyIndependent K C) :
    IsLinearlyIndependent K (φ '' C) := by
  rintro ⟨k, y, c, hy_inj, hy_mem, hnz, hsum⟩
  choose x hxC hxy using hy_mem
  have hx_inj : Function.Injective x := fun i j hij =>
    hy_inj (by rw [← hxy i, ← hxy j, hij])
  have hsum_x : ∑ i, c i • x i = 0 := by
    apply hφ
    rw [map_zero, map_sum]
    simp_rw [map_smul, hxy]
    exact hsum
  exact hC ⟨k, x, c, hx_inj, hxC, hnz, hsum_x⟩

private lemma setOrder_image_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) (S : Set α) :
    setOrder (f '' S) = setOrder S :=
  ENat.card_congr (Equiv.Set.image f S hf).symm

/-- Every linear subspace `U` of a finite-dimensional vector space `V` is finite-dimensional
(§1.3, p. 12). -/
theorem subspace_isFiniteDimensional {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V) (U : Submodule K V) :
    IsFiniteDimensional K U := by
  classical
  obtain ⟨A₀, hA₀fin, hA₀span⟩ := hV
  let m : ℕ := hA₀fin.toFinset.card
  let P : Finset ℕ :=
    (Finset.range (m + 1)).filter (fun k => ∃ C : Set U, setOrder C = k ∧ IsLinearlyIndependent K C)
  have h0P : 0 ∈ P := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.zero_lt_succ m, ∅, ?_, empty_isLinearlyIndependent K⟩
    simp [setOrder]
  obtain ⟨d, hd_mem, hd_max⟩ := Finset.exists_max_image P id ⟨0, h0P⟩
  rw [Finset.mem_filter, Finset.mem_range] at hd_mem
  rcases hd_mem with ⟨_, C, hCd, hCind⟩
  have hCfin : C.Finite := ENat.card_lt_top.mp (by rw [← setOrder, hCd]; exact ENat.natCast_lt_top d)
  refine ⟨C, hCfin, ?_⟩
  rw [Spans, eq_top_iff]
  intro u _
  by_contra hu_nspan
  have hu_notC : u ∉ C := fun huC => hu_nspan (Submodule.subset_span huC)
  have hins_ind : IsLinearlyIndependent K (insert u C) := by
    rw [isLinearlyIndependent_iff, linearIndepOn_id_insert hu_notC]
    exact ⟨(isLinearlyIndependent_iff C).mp hCind, hu_nspan⟩
  have hins_card : setOrder (insert u C : Set U) = (d + 1 : ℕ) := by
    have hfin_ins : (insert u C).Finite := hCfin.insert u
    rw [setOrder_eq_toFinset_card hfin_ins, Set.Finite.toFinset_insert,
        Finset.card_insert_of_notMem (by simpa using hu_notC)]
    have hCcard : hCfin.toFinset.card = d :=
      Nat.cast_injective (R := ℕ∞) (by rw [← setOrder_eq_toFinset_card hCfin, hCd])
    simp [hCcard]
  have himg_ind : IsLinearlyIndependent K (U.subtype '' (insert u C)) :=
    linearMap_inj_isLinearlyIndependent Subtype.val_injective hins_ind
  have hle_m : ((d + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
    have hle := theorem_1_2 hA₀span himg_ind
    rwa [setOrder_image_of_injective (f := U.subtype) Subtype.val_injective, hins_card,
         setOrder_eq_toFinset_card hA₀fin] at hle
  have hd1_le_m : d + 1 ≤ m := Nat.cast_le.mp hle_m
  have hd1_mem : d + 1 ∈ P := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hd1_le_m, (insert u C : Set U), hins_card, hins_ind⟩
  have hmax := hd_max (d + 1) hd1_mem
  simp only [id_eq] at hmax
  omega

/-- **Theorem 1.4** (§1.3, p. 12): If `U` is a linear subspace of a finite-dimensional vector space
`V` over `K`, then `dim U ≤ dim V`, and `dim U = dim V` if and only if `U = V`. -/
theorem theorem_1_4 {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (hV : IsFiniteDimensional K V) (U : Submodule K V) :
    garlingDim K U (subspace_isFiniteDimensional hV U) ≤ garlingDim K V hV ∧
      (garlingDim K U (subspace_isFiniteDimensional hV U) = garlingDim K V hV ↔ U = ⊤) := by
  classical
  let hU := subspace_isFiniteDimensional hV U
  obtain ⟨B_U, hBUfin, hBU⟩ := exists_finite_basis hU
  let C : Set V := U.subtype '' B_U
  have hCfin : C.Finite := hBUfin.image U.subtype
  have hCind : IsLinearlyIndependent K C :=
    linearMap_inj_isLinearlyIndependent Subtype.val_injective hBU.1
  have hCcard : setOrder C = garlingDim K U hU := by
    rw [setOrder_image_of_injective (f := U.subtype) Subtype.val_injective, garlingDim_spec hU hBU]
  have hCspan : Submodule.span K C = U := by
    have hmap : Submodule.map U.subtype (Submodule.span K B_U) = Submodule.span K C :=
      Submodule.map_span U.subtype B_U
    rw [← hmap, hBU.2]
    ext x
    simp
  obtain ⟨A₁, hA₁fin, hA₁span⟩ := id hV
  have hCA_fin : (C ∪ A₁).Finite := hCfin.union hA₁fin
  have hCA_span : Spans K V (C ∪ A₁) := by
    rw [Spans, eq_top_iff, ← hA₁span]
    exact Submodule.span_mono Set.subset_union_right
  obtain ⟨B, hCB, hBsub, hB⟩ := theorem_1_1 hCA_fin hCA_span Set.subset_union_left hCind
  have hBfin : B.Finite := hCA_fin.subset hBsub
  have hBcard : setOrder B = garlingDim K V hV := garlingDim_spec hV hB
  have hle_enat : (garlingDim K U hU : ℕ∞) ≤ (garlingDim K V hV : ℕ∞) := by
    rw [← hCcard, ← hBcard, setOrder_eq_toFinset_card hCfin, setOrder_eq_toFinset_card hBfin]
    exact Nat.cast_le.mpr (Finset.card_le_card (Set.Finite.toFinset_subset_toFinset.mpr hCB))
  have hle : garlingDim K U hU ≤ garlingDim K V hV := Nat.cast_le.mp hle_enat
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    have hCB_card : hCfin.toFinset.card = hBfin.toFinset.card := by
      have hc1 : (hCfin.toFinset.card : ℕ∞) = garlingDim K U hU := by
        rw [← setOrder_eq_toFinset_card hCfin, hCcard]
      have hc2 : (hBfin.toFinset.card : ℕ∞) = garlingDim K V hV := by
        rw [← setOrder_eq_toFinset_card hBfin, hBcard]
      exact Nat.cast_injective (R := ℕ∞) (by rw [hc1, hc2, heq])
    have hfin_eq : hCfin.toFinset = hBfin.toFinset :=
      Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_subset_toFinset.mpr hCB)
        (Nat.le_of_eq hCB_card.symm)
    have hCB_eq : C = B := by
      simpa using congrArg (fun S : Finset V => (S : Set V)) hfin_eq
    rw [← hCspan, hCB_eq, hB.2]
  · rintro rfl
    have htop_basis : IsBasis K V C := by
      refine ⟨hCind, ?_⟩
      rw [Spans, hCspan]
    have hc1 := garlingDim_spec hV htop_basis
    exact Nat.cast_injective (R := ℕ∞) (hCcard.symm.trans hc1)

/-- **Corollary 1** (to Theorem 1.4; §1.3, p. 12): If `A` is a finite subset of a
finite-dimensional vector space `V` over `K` with `|A| > dim V`, then `A` is linearly dependent
over `K`. -/
theorem corollary_1_to_theorem_1_4 {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V)
    {A : Set V} (_hAfin : A.Finite) (hgt : (garlingDim K V hV : ℕ∞) < setOrder A) :
    IsLinearlyDependent K A := by
  by_contra hnot
  have hAind : IsLinearlyIndependent K A := hnot
  obtain ⟨B, _, hB⟩ := exists_finite_basis hV
  have hle : setOrder A ≤ setOrder B := theorem_1_2 hB.2 hAind
  rw [garlingDim_spec hV hB] at hle
  exact not_lt_of_ge hle hgt

/-- **Corollary 2** (to Theorem 1.4; §1.3, p. 12): If `φ : V₁ →ₗ[K] V₂` is a `K`-linear mapping
between finite-dimensional vector spaces with `dim V₁ > dim V₂`, then `φ` is not one-to-one and
there exists a non-zero `x ∈ V₁` such that `φ x = 0`. -/
theorem corollary_2_to_theorem_1_4 {K : Type*} [Field K]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    (hV₁ : IsFiniteDimensional K V₁) (hV₂ : IsFiniteDimensional K V₂)
    (φ : V₁ →ₗ[K] V₂) (hdim : garlingDim K V₂ hV₂ < garlingDim K V₁ hV₁) :
    ¬ Function.Injective φ ∧ ∃ x : V₁, x ≠ 0 ∧ φ x = 0 := by
  have hnot_inj : ¬ Function.Injective φ := by
    intro hinj
    obtain ⟨B₁, hB₁fin, hB₁⟩ := exists_finite_basis hV₁
    have hAind : IsLinearlyIndependent K (φ '' B₁) :=
      linearMap_inj_isLinearlyIndependent hinj hB₁.1
    have hgt : (garlingDim K V₂ hV₂ : ℕ∞) < setOrder (φ '' B₁) := by
      rw [setOrder_image_of_injective hinj, garlingDim_spec hV₁ hB₁]
      exact Nat.cast_lt.mpr hdim
    exact hAind (corollary_1_to_theorem_1_4 hV₂ (hB₁fin.image φ) hgt)
  refine ⟨hnot_inj, ?_⟩
  have hex : ∃ a b : V₁, φ a = φ b ∧ a ≠ b := by
    by_contra hall
    push Not at hall
    exact hnot_inj hall
  obtain ⟨a, b, hab, hne⟩ := hex
  exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩

/-! ### Exercises 1.14–1.18 (§1.3, printed p. 13) -/

/-- Standard coordinate vector `e_j = (0, ..., 0, 1, 0, ..., 0) ∈ K^n` (§1.3, Ex. 1.14, p. 13). -/
def garlingStdVec (K : Type*) [Field K] {n : ℕ} (j : Fin n) : Kn n K :=
  fun i => if i = j then 1 else 0

/-- Prefix sum vector `f_j = e_1 + ... + e_j ∈ K^n` (§1.3, Ex. 1.14, p. 13). -/
def garlingPrefixVec (K : Type*) [Field K] {n : ℕ} (j : Fin n) : Kn n K :=
  ∑ k ∈ Finset.Iic j, garlingStdVec K k

private lemma garlingPrefixVec_apply {K : Type*} [Field K] {n : ℕ} (j i : Fin n) :
    garlingPrefixVec K j i = if i ≤ j then 1 else 0 := by
  rw [garlingPrefixVec, Finset.sum_apply]
  simp only [garlingStdVec]
  by_cases hij : i ≤ j
  · have hmem : i ∈ Finset.Iic j := Finset.mem_Iic.mpr hij
    rw [Finset.sum_eq_single i
      (fun k _ hki => by simp [Ne.symm hki])
      (fun hnot => (hnot hmem).elim)]
    simp [hij]
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkj : k ≤ j := Finset.mem_Iic.mp hk
    have hik : i ≠ k := fun h => hij (h ▸ hkj)
    simp [hik]

private lemma garlingStdVec_injective (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (garlingStdVec K (n := n)) := by
  intro j₁ j₂ h
  have hj := congrArg (fun f => f j₁) h
  simp only [garlingStdVec, ↓reduceIte] at hj
  by_contra hne
  simp only [hne, ↓reduceIte] at hj
  exact one_ne_zero hj

/-- **Exercise 1.14(a)** (§1.3, p. 13): `{e_1, ..., e_n}` is a basis for `K^n`. -/
theorem exercise_1_14_a (K : Type*) [Field K] (n : ℕ) :
    IsBasis K (Kn n K) (Set.range (garlingStdVec K (n := n))) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, x, c, hx_inj, hx_mem, ⟨m₀, hcm₀⟩, hsum⟩
    choose j hj using hx_mem
    have hj_inj : Function.Injective j := fun m₁ m₂ hm =>
      hx_inj (by rw [← hj m₁, ← hj m₂, hm])
    have heval := congrArg (fun f : Kn n K => f (j m₀)) hsum
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
    have hterm : ∀ m : Fin k, c m * x m (j m₀) = if m = m₀ then c m₀ else 0 := by
      intro m
      rw [← hj m, garlingStdVec]
      by_cases hm : m = m₀
      · subst hm; simp
      · have hne : j m₀ ≠ j m := fun h => hm (hj_inj h.symm)
        simp [hm, hne]
    simp_rw [hterm] at heval
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at heval
    exact hcm₀ heval
  · rw [Spans, eq_top_iff]
    intro v _
    have hv : v = ∑ j : Fin n, v j • garlingStdVec K j := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, garlingStdVec]
      rw [Finset.sum_eq_single i
        (fun j _ hji => by simp [Ne.symm hji])
        (fun hnot => (hnot (Finset.mem_univ i)).elim)]
      simp
    rw [hv]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Exercise 1.14(b)** (§1.3, p. 13): `{f_1, ..., f_n}` is a basis for `K^n`. -/
theorem exercise_1_14_b (K : Type*) [Field K] (n : ℕ) :
    IsBasis K (Kn n K) (Set.range (garlingPrefixVec K (n := n))) := by
  have hli_f : LinearIndependent K (garlingPrefixVec K (n := n)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum i
    have htail : ∀ t : Fin n, ∑ j ∈ Finset.Ici t, g j = 0 := by
      intro t
      have ht := congrArg (fun f : Kn n K => f t) hsum
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
                 garlingPrefixVec_apply] at ht
      rw [← ht, ← Finset.sum_subset (Finset.subset_univ (Finset.Ici t))
        (fun x _ hx => by simp [Finset.mem_Ici.not.mp hx])]
      exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_Ici.mp hx]
    by_cases hsucc : i.val + 1 < n
    · let i' : Fin n := ⟨i.val + 1, hsucc⟩
      have hIci_eq : Finset.Ici i = insert i (Finset.Ici i') := by
        ext j
        simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff, i']
        omega
      have hi_not : i ∉ Finset.Ici i' := by
        simp [Finset.mem_Ici, Fin.le_iff_val_le_val, i']
      have hi_sum := htail i
      rw [hIci_eq, Finset.sum_insert hi_not, htail i', add_zero] at hi_sum
      exact hi_sum
    · have hIci_single : Finset.Ici i = {i} := by
        ext j
        simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
        omega
      have hi_sum := htail i
      rwa [hIci_single, Finset.sum_singleton] at hi_sum
  have hli_set : IsLinearlyIndependent K (Set.range (garlingPrefixVec K (n := n))) := by
    rintro ⟨k, x, c, hx_inj, hx_mem, ⟨m₀, hcm₀⟩, hsum⟩
    choose idx hidx using hx_mem
    have hidx_inj : Function.Injective idx := fun a b hab =>
      hx_inj (by rw [← hidx a, ← hidx b, hab])
    have hli_k : LinearIndependent K x := by
      have hx_eq : x = garlingPrefixVec K (n := n) ∘ idx := funext fun a => (hidx a).symm
      rw [hx_eq]
      exact hli_f.comp idx hidx_inj
    exact hcm₀ (Fintype.linearIndependent_iff.mp hli_k c hsum m₀)
  refine ⟨hli_set, ?_⟩
  rw [Spans, eq_top_iff, ← (exercise_1_14_a K n).2, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj0 : j.val = 0
  · have heq : garlingStdVec K j = garlingPrefixVec K j := by
      ext i
      rw [garlingStdVec, garlingPrefixVec_apply]
      have hiff : (i ≤ j) ↔ i = j := by
        simp only [Fin.le_iff_val_le_val, Fin.ext_iff]
        omega
      by_cases hij : i = j <;> simp [hiff, hij]
    rw [heq]
    exact Submodule.subset_span ⟨j, rfl⟩
  · let j' : Fin n := ⟨j.val - 1, by omega⟩
    have heq : garlingStdVec K j = garlingPrefixVec K j - garlingPrefixVec K j' := by
      ext i
      simp only [Pi.sub_apply, garlingStdVec, garlingPrefixVec_apply]
      by_cases hij : i = j
      · subst hij
        have hnle : ¬ (i ≤ j') := by
          simp only [Fin.le_iff_val_le_val, j']
          omega
        simp [hnle]
      · by_cases hle : i ≤ j
        · have hle' : i ≤ j' := by
            have hne_val : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
            have hlt_val : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hle
            simp only [Fin.le_iff_val_le_val, j']
            omega
          simp [hij, hle, hle']
        · have hnle' : ¬ (i ≤ j') := by
            simp only [Fin.le_iff_val_le_val, j'] at hle ⊢
            omega
          simp [hij, hle, hnle']
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩) (Submodule.subset_span ⟨j', rfl⟩)

/-- **Exercise 1.14(c) (subset sense)** (§1.3, p. 13): Because `f_1 = e_1`, the subset
`{e_1, f_1, f_2, ..., f_{n+1}}` of `K^{n+1}` coincides with `{f_1, ..., f_{n+1}}` and is therefore
a basis in Garling's §1.3 subset sense. -/
theorem exercise_1_14_c_set (K : Type*) [Field K] (n : ℕ) :
    IsBasis K (Kn (n + 1) K)
      (insert (garlingStdVec K (0 : Fin (n + 1)))
        (Set.range (garlingPrefixVec K (n := n + 1)))) := by
  have he0 : garlingStdVec K (0 : Fin (n + 1)) = garlingPrefixVec K (0 : Fin (n + 1)) := by
    ext i
    rw [garlingStdVec, garlingPrefixVec_apply]
    have hiff : (i ≤ (0 : Fin (n + 1))) ↔ i = 0 :=
      ⟨fun h => Fin.ext (Nat.eq_zero_of_le_zero h), fun h => h ▸ le_rfl⟩
    by_cases hi : i = 0 <;> simp [hiff, hi]
  have hins :
      insert (garlingStdVec K (0 : Fin (n + 1)))
        (Set.range (garlingPrefixVec K (n := n + 1))) =
      Set.range (garlingPrefixVec K (n := n + 1)) :=
    Set.insert_eq_of_mem ⟨0, he0.symm⟩
  rw [hins]
  exact exercise_1_14_b K (n + 1)

/-- Indexed `(n + 2)`-tuple `(e_1, f_1, f_2, ..., f_{n+1})` for Exercise 1.14(c) (§1.3, p. 13). -/
def garlingEx114cTuple (K : Type*) [Field K] (n : ℕ) : Fin (n + 2) → Kn (n + 1) K :=
  Fin.cons (garlingStdVec K (0 : Fin (n + 1))) (garlingPrefixVec K (n := n + 1))

/-- **Exercise 1.14(c) (indexed-family sense)** (§1.3, p. 13): As an `(n + 2)`-element indexed
family `(e_1, f_1, f_2, ..., f_{n+1})`, `e_1 = f_1` repeats a vector, so the family is not
linearly independent. -/
theorem exercise_1_14_c_tuple_not_linearIndependent (K : Type*) [Field K] (n : ℕ) :
    ¬ LinearIndependent K (garlingEx114cTuple K n) := by
  intro hli
  have he0 : garlingStdVec K (0 : Fin (n + 1)) = garlingPrefixVec K (0 : Fin (n + 1)) := by
    ext i
    rw [garlingStdVec, garlingPrefixVec_apply]
    have hiff : (i ≤ (0 : Fin (n + 1))) ↔ i = 0 :=
      ⟨fun h => Fin.ext (Nat.eq_zero_of_le_zero h), fun h => h ▸ le_rfl⟩
    by_cases hi : i = 0 <;> simp [hiff, hi]
  have heq :
      garlingEx114cTuple K n 0 = garlingEx114cTuple K n (0 : Fin (n + 1)).succ := by
    simp [garlingEx114cTuple, he0]
  have h01 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := hli.injective heq
  exact Fin.succ_ne_zero (0 : Fin (n + 1)) h01.symm

/-- **Exercise 1.14** (§1.3, p. 13): Combined package of parts `(a)`, `(b)`, and `(c)`. -/
theorem exercise_1_14 (K : Type*) [Field K] (n : ℕ) :
    IsBasis K (Kn n K) (Set.range (garlingStdVec K (n := n))) ∧
    IsBasis K (Kn n K) (Set.range (garlingPrefixVec K (n := n))) ∧
    IsBasis K (Kn (n + 1) K)
      (insert (garlingStdVec K (0 : Fin (n + 1)))
        (Set.range (garlingPrefixVec K (n := n + 1)))) ∧
    ¬ LinearIndependent K (garlingEx114cTuple K n) :=
  ⟨exercise_1_14_a K n,
   exercise_1_14_b K n,
   exercise_1_14_c_set K n,
   exercise_1_14_c_tuple_not_linearIndependent K n⟩

/-- Kronecker indicator function `e_s ∈ K^S` (`e_s(t) = 1` if `s = t`, `0` otherwise)
(§1.3, Ex. 1.15, p. 13). -/
noncomputable def garlingKronecker (K : Type*) [Field K] {S : Type*} (s : S) : FunSpace S K := by
  classical
  exact fun t => if s = t then 1 else 0

/-- Linear independence of `{e_s : s ∈ S} ⊆ K^S` (§1.3, Ex. 1.15, p. 13). -/
theorem exercise_1_15_linearlyIndependent (K : Type*) [Field K] (S : Type*) :
    IsLinearlyIndependent K (Set.range (garlingKronecker K (S := S))) := by
  rintro ⟨k, x, c, hx_inj, hx_mem, ⟨m₀, hcm₀⟩, hsum⟩
  choose s hs using hx_mem
  have hs_inj : Function.Injective s := fun m₁ m₂ hm =>
    hx_inj (by rw [← hs m₁, ← hs m₂, hm])
  have heval := congrArg (fun f : FunSpace S K => f (s m₀)) hsum
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
  have hterm : ∀ m : Fin k, c m * x m (s m₀) = if m = m₀ then c m₀ else 0 := by
    intro m
    rw [← hs m, garlingKronecker]
    by_cases hm : m = m₀
    · subst hm; simp
    · have hne : s m ≠ s m₀ := fun h => hm (hs_inj h)
      simp [hm, hne]
  simp_rw [hterm] at heval
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at heval
  exact hcm₀ heval

/-- **Exercise 1.15** (§1.3, p. 13): When `S` is infinite, `{e_s : s ∈ S}` is linearly independent
in `K^S` but does not span `K^S`, so it is NOT a basis for `K^S`. -/
theorem exercise_1_15 (K : Type*) [Field K] (S : Type*) [Infinite S] :
    ¬ IsBasis K (FunSpace S K) (Set.range (garlingKronecker K (S := S))) := by
  rintro ⟨_, hspan⟩
  classical
  have hone_mem : (fun _ : S => (1 : K)) ∈ Submodule.span K (Set.range (garlingKronecker K (S := S))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc_sub, hc_sum⟩ := Submodule.mem_span_set.mp hone_mem
  let s₀ : S := (Infinite.nonempty S).some
  let idx : FunSpace S K → S :=
    fun f => if h : f ∈ Set.range (garlingKronecker K (S := S)) then h.choose else s₀
  let T : Finset S := c.support.image idx
  obtain ⟨t₀, ht₀⟩ := Infinite.exists_notMem_finset T
  have heval := congrArg (fun g : FunSpace S K => g t₀) hc_sum
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
  have hzero : ∑ f ∈ c.support, c f * f t₀ = 0 := by
    refine Finset.sum_eq_zero fun f hf => ?_
    have hf_range : f ∈ Set.range (garlingKronecker K (S := S)) := hc_sub hf
    have hf_eq : garlingKronecker K (idx f) = f := by
      dsimp only [idx]
      simp only [hf_range, ↓reduceDIte]
      exact hf_range.choose_spec
    have hidx_mem : idx f ∈ T := Finset.mem_image_of_mem idx hf
    have hne : idx f ≠ t₀ := fun h => ht₀ (h ▸ hidx_mem)
    rw [← hf_eq, garlingKronecker]
    simp [hne]
  rw [hzero] at heval
  exact one_ne_zero heval.symm

private lemma real_exp_nat_mul_log {p : ℕ} (hp : 0 < p) :
    ∀ n : ℕ, Real.exp ((n : ℝ) * Real.log (p : ℝ)) = (p : ℝ) ^ n
  | 0 => by simp
  | n + 1 => by
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
    push_cast
    rw [add_mul, one_mul, Real.exp_add, real_exp_nat_mul_log hp n, Real.exp_log hpR, ← pow_succ]

/-- Infinite subset `{log p : p prime} ⊆ ℝ` for Exercise 1.16 (§1.3, p. 13). -/
noncomputable def primeLogSet : Set ℝ :=
  (fun p : ℕ => Real.log (p : ℝ)) '' {p : ℕ | Nat.Prime p}

theorem primeLogSet_infinite : primeLogSet.Infinite := by
  refine Nat.infinite_setOfPred_prime.image ?_
  intro p₁ hp₁ p₂ hp₂ hlog
  have hp₁R : (0 : ℝ) < (p₁ : ℝ) := Nat.cast_pos.mpr hp₁.pos
  have hp₂R : (0 : ℝ) < (p₂ : ℝ) := Nat.cast_pos.mpr hp₂.pos
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log hp₁R, Real.exp_log hp₂R] at hexp
  exact Nat.cast_injective hexp

theorem primeLogSet_linearlyIndependent : IsLinearlyIndependent ℚ primeLogSet := by
  rintro ⟨k, x, c, hx_inj, hx_mem, ⟨i₀, hc₀⟩, hsum⟩
  choose p hp hxp using hx_mem
  have hp_inj : Function.Injective p := fun i₁ i₂ hi =>
    hx_inj (by rw [← hxp i₁, ← hxp i₂, hi])
  let D : ℕ := ∏ j : Fin k, (c j).den
  have hD_pos : 0 < D := Finset.prod_pos fun j _ => (c j).pos
  have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos.ne'
  let m : Fin k → ℤ := fun i => (c i).num * ↑(∏ j ∈ Finset.univ.erase i, (c j).den)
  have hm_eq : ∀ i : Fin k, (m i : ℚ) = c i * (D : ℚ) := by
    intro i
    have hprod_D : (D : ℚ) = ((c i).den : ℚ) * (∏ j ∈ Finset.univ.erase i, ((c j).den : ℚ)) := by
      have hsplit := Finset.mul_prod_erase Finset.univ (fun j : Fin k => (c j).den) (Finset.mem_univ i)
      exact_mod_cast hsplit.symm
    have hden_ne : ((c i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (c i).pos.ne'
    dsimp only [m]
    push_cast
    rw [hprod_D]
    calc ((c i).num : ℚ) * ∏ x ∈ Finset.univ.erase i, ((c x).den : ℚ)
      _ = (((c i).num : ℚ) / ((c i).den : ℚ)) *
            (((c i).den : ℚ) * ∏ x ∈ Finset.univ.erase i, ((c x).den : ℚ)) := by
          field_simp
      _ = c i * (((c i).den : ℚ) * ∏ x ∈ Finset.univ.erase i, ((c x).den : ℚ)) := by
          rw [Rat.num_div_den]
  have hm_ne : m i₀ ≠ 0 := by
    intro hm0
    have h0 : c i₀ * (D : ℚ) = 0 := by simpa [hm0] using (hm_eq i₀).symm
    exact hc₀ ((mul_eq_zero.mp h0).resolve_right hD_ne)
  have hsum_int : ∑ i : Fin k, (m i : ℝ) * Real.log (p i : ℝ) = 0 := by
    have hmul := congrArg (fun r : ℝ => (D : ℝ) * r) hsum
    simp only [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def, ← hxp i, ← mul_assoc]
    have hmR : (m i : ℝ) = (D : ℝ) * (c i : ℝ) := by
      have hq := hm_eq i
      have hr : ((m i : ℚ) : ℝ) = ((c i * (D : ℚ) : ℚ) : ℝ) := congrArg Rat.cast hq
      push_cast at hr
      linarith
    rw [hmR]
  let a : Fin k → ℕ := fun i => (m i).toNat
  let b : Fin k → ℕ := fun i => (-m i).toNat
  have hab_diff : ∀ i : Fin k, (m i : ℝ) = (a i : ℝ) - (b i : ℝ) := by
    intro i
    have hz : m i = (a i : ℤ) - (b i : ℤ) := by
      dsimp only [a, b]
      omega
    exact_mod_cast hz
  have hsum_ab :
      ∑ i : Fin k, (a i : ℝ) * Real.log (p i : ℝ) =
      ∑ i : Fin k, (b i : ℝ) * Real.log (p i : ℝ) := by
    have hsub :
        ∑ i : Fin k, ((a i : ℝ) * Real.log (p i : ℝ) - (b i : ℝ) * Real.log (p i : ℝ)) = 0 := by
      rw [← hsum_int]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hab_diff i, sub_mul]
    rw [Finset.sum_sub_distrib] at hsub
    exact sub_eq_zero.mp hsub
  have hexp := congrArg Real.exp hsum_ab
  rw [Real.exp_sum, Real.exp_sum] at hexp
  have hlhs :
      ∏ i : Fin k, Real.exp ((a i : ℝ) * Real.log (p i : ℝ)) =
      ((∏ i : Fin k, p i ^ a i : ℕ) : ℝ) := by
    rw [Finset.prod_congr rfl fun i _ => real_exp_nat_mul_log (hp i).pos (a i)]
    norm_cast
  have hrhs :
      ∏ i : Fin k, Real.exp ((b i : ℝ) * Real.log (p i : ℝ)) =
      ((∏ i : Fin k, p i ^ b i : ℕ) : ℝ) := by
    rw [Finset.prod_congr rfl fun i _ => real_exp_nat_mul_log (hp i).pos (b i)]
    norm_cast
  rw [hlhs, hrhs] at hexp
  have hprod_nat : (∏ i : Fin k, p i ^ a i) = ∏ i : Fin k, p i ^ b i :=
    Nat.cast_injective hexp
  have hfac := congrArg (fun N : ℕ => N.factorization (p i₀)) hprod_nat
  rw [Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (hp i).ne_zero),
      Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (hp i).ne_zero)] at hfac
  have heval_fac : ∀ f : Fin k → ℕ,
      (∑ i : Fin k, (p i ^ f i).factorization (p i₀)) = f i₀ := by
    intro f
    have hterm : ∀ i : Fin k,
        (p i ^ f i).factorization (p i₀) = if i = i₀ then f i₀ else 0 := by
      intro i
      rw [Nat.Prime.factorization_pow (hp i), Finsupp.single_apply]
      by_cases hi : i = i₀
      · subst hi; simp
      · have hne : p i ≠ p i₀ := fun h => hi (hp_inj h)
        simp [hi, hne]
    simp_rw [hterm]
    simp
  rw [heval_fac a, heval_fac b] at hfac
  have hm0 : m i₀ = 0 := by
    dsimp only [a, b] at hfac
    omega
  exact hm_ne hm0

/-- **Exercise 1.16** (§1.3, p. 13): `ℝ` is not finite-dimensional over `ℚ`, and there exists an
infinite subset of `ℝ` (`{log p : p prime}`) that is linearly independent over `ℚ`. -/
theorem exercise_1_16 :
    ¬ IsFiniteDimensional ℚ ℝ ∧
      ∃ S : Set ℝ, S.Infinite ∧ IsLinearlyIndependent ℚ S := by
  refine ⟨?_, ⟨primeLogSet, primeLogSet_infinite, primeLogSet_linearlyIndependent⟩⟩
  rintro ⟨A, hAfin, hAspan⟩
  have hle := theorem_1_2 hAspan primeLogSet_linearlyIndependent
  rw [setOrder_eq_toFinset_card hAfin] at hle
  have hfin : Finite primeLogSet :=
    ENat.card_lt_top.mp (lt_of_le_of_lt hle (ENat.natCast_lt_top _))
  exact primeLogSet_infinite hfin

/-- **Exercise 1.17** (§1.3, p. 13): Over an infinite field `K`, a vector space `V` cannot be
expressed as a finite union `⋃ i : Fin n, U i` of proper linear subspaces `U i ≠ ⊤`. -/
theorem exercise_1_17 {K : Type*} [Field K] [Infinite K]
    {V : Type*} [AddCommGroup V] [Module K V] :
    ∀ (n : ℕ) (U : Fin n → Submodule K V),
      (∀ i : Fin n, U i ≠ ⊤) → (⋃ i : Fin n, (U i : Set V)) ≠ Set.univ
  | 0, U, _ => by
    intro hcov
    have h0 : (0 : V) ∈ (⋃ i : Fin 0, (U i : Set V)) := by rw [hcov]; trivial
    simp at h0
  | n + 1, U, hproper => by
    intro hcov
    let U' : Fin n → Submodule K V := fun j => U j.succ
    have hnot_univ := exercise_1_17 n U' (fun j => hproper j.succ)
    have hex_x : ∃ x : V, ∀ j : Fin n, x ∉ U j.succ := by
      by_contra hall
      push Not at hall
      apply hnot_univ
      ext z
      simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
      exact hall z
    obtain ⟨x, hx⟩ := hex_x
    have hex_y : ∃ y : V, y ∉ U 0 := by
      by_contra hall
      push Not at hall
      apply hproper 0
      rw [eq_top_iff]
      intro y _
      exact hall y
    obtain ⟨y, hy⟩ := hex_y
    by_cases hx0 : x ∈ U 0
    · have hline : ∀ c : {c : K // c ≠ 0}, ∃ j : Fin n, x + c.1 • y ∈ U j.succ := by
        intro c
        have hmem_univ : x + c.1 • y ∈ (⋃ i : Fin (n + 1), (U i : Set V)) := by
          rw [hcov]; trivial
        rcases Set.mem_iUnion.mp hmem_univ with ⟨i, hi⟩
        refine Fin.cases (fun h0 => ?_) (fun j hj => ⟨j, hj⟩) i hi
        exfalso
        have hcy : c.1 • y ∈ U 0 := by
          have hsub := (U 0).sub_mem h0 hx0
          simpa using hsub
        have hy_in : y ∈ U 0 := by
          have hsmul := (U 0).smul_mem c.1⁻¹ hcy
          rwa [inv_smul_smul₀ c.2] at hsmul
        exact hy hy_in
      choose g hg using hline
      have hg_inj : Function.Injective g := by
        intro c₁ c₂ hgc
        by_contra hne
        have hval_ne : c₁.1 ≠ c₂.1 := fun hv => hne (Subtype.ext hv)
        have hdiff_ne : c₁.1 - c₂.1 ≠ 0 := sub_ne_zero.mpr hval_ne
        let j := g c₁
        have h₁ : x + c₁.1 • y ∈ U j.succ := hg c₁
        have h₂ : x + c₂.1 • y ∈ U j.succ := by
          dsimp only [j]
          rw [hgc]
          exact hg c₂
        have hsub : (c₁.1 - c₂.1) • y ∈ U j.succ := by
          have hs := (U j.succ).sub_mem h₁ h₂
          have heq : (x + c₁.1 • y) - (x + c₂.1 • y) = (c₁.1 - c₂.1) • y := by
            rw [sub_smul]; abel
          rwa [heq] at hs
        have hy_j : y ∈ U j.succ := by
          have hsm := (U j.succ).smul_mem (c₁.1 - c₂.1)⁻¹ hsub
          rwa [inv_smul_smul₀ hdiff_ne] at hsm
        have hx_j : x ∈ U j.succ := by
          have hc₁y : c₁.1 • y ∈ U j.succ := (U j.succ).smul_mem c₁.1 hy_j
          have hs := (U j.succ).sub_mem h₁ hc₁y
          simpa using hs
        exact hx j hx_j
      have hfin_nz : Finite {c : K // c ≠ 0} := Finite.of_injective g hg_inj
      let toOpt : K → Option {c : K // c ≠ 0} := by
        classical
        exact fun c => if hc : c = 0 then none else some ⟨c, hc⟩
      have htoOpt_inj : Function.Injective toOpt := by
        classical
        intro a b hab
        dsimp only [toOpt] at hab
        by_cases ha : a = 0 <;> by_cases hb : b = 0
        · rw [ha, hb]
        · simp [ha, hb] at hab
        · simp [ha, hb] at hab
        · simp only [ha, hb, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hab
          exact hab
      have hfinK : Finite K := Finite.of_injective toOpt htoOpt_inj
      exact not_finite_iff_infinite.mpr ‹Infinite K› hfinK
    · have hmem_univ : x ∈ (⋃ i : Fin (n + 1), (U i : Set V)) := by rw [hcov]; trivial
      rcases Set.mem_iUnion.mp hmem_univ with ⟨i, hi⟩
      exact Fin.cases (fun h0 => hx0 h0) (fun j hj => hx j hj) i hi

private noncomputable def basisEquivFunOnFinite {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {B : Set V} (hBfin : B.Finite) (hB : IsBasis K V B) :
    V ≃ (hBfin.toFinset → K) := by
  have hspan : (⊤ : Submodule K V) ≤ Submodule.span K (Set.range fun x : B => id (x : V)) := by
    have hrange : (Set.range fun x : B => id (x : V)) = B := by
      ext v
      simp
    rw [hrange, hB.2]
  let b : Module.Basis B K V :=
    Module.Basis.mk ((isLinearlyIndependent_iff B).mp hB.1) hspan
  have : Fintype B := hBfin.fintype
  let eB : B ≃ hBfin.toFinset :=
    ⟨fun x => ⟨x.1, hBfin.mem_toFinset.mpr x.2⟩,
     fun x => ⟨x.1, hBfin.mem_toFinset.mp x.2⟩,
     fun _ => rfl, fun _ => rfl⟩
  exact b.equivFun.toEquiv.trans (Equiv.arrowCongr eB (Equiv.refl K))

private lemma fintype_card_eq_pow_garlingDim {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
    (hV : IsFiniteDimensional K V) :
    Fintype.card V = (Fintype.card K) ^ (garlingDim K V hV) := by
  classical
  obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
  let e := basisEquivFunOnFinite hBfin hB
  have hBcard : hBfin.toFinset.card = garlingDim K V hV :=
    Nat.cast_injective (R := ℕ∞) (by rw [← setOrder_eq_toFinset_card hBfin, garlingDim_spec hV hB])
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, hBcard]

private lemma kn_isFiniteDimensional (K : Type*) [Field K] (n : ℕ) :
    IsFiniteDimensional K (Kn n K) :=
  ⟨Set.range (garlingStdVec K (n := n)), Set.finite_range _, (exercise_1_14_a K n).2⟩

private lemma garlingDim_kn (K : Type*) [Field K] (n : ℕ) :
    garlingDim K (Kn n K) (kn_isFiniteDimensional K n) = n := by
  have hspec := garlingDim_spec (kn_isFiniteDimensional K n) (exercise_1_14_a K n)
  have hcard : setOrder (Set.range (garlingStdVec K (n := n))) = (n : ℕ∞) := by
    have heq : Set.range (garlingStdVec K (n := n)) = garlingStdVec K (n := n) '' Set.univ :=
      Set.image_univ.symm
    rw [heq, setOrder_image_of_injective (garlingStdVec_injective K n)]
    have e : (Set.univ : Set (Fin n)) ≃ Fin n := Equiv.Set.univ (Fin n)
    rw [setOrder, ENat.card_congr e, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  exact Nat.cast_injective (R := ℕ∞) (hspec.symm.trans hcard)

/-- **Exercise 1.18 (counterexample to printed lower bound for `r ≥ 3`)** (§1.3, p. 13; queued
fidelity hold): Over `K = ZMod 2` (`k = 2`) and `V = K^3` (`r = 3`), `(k^r - 1) / (k - 1) = 7`,
yet `V` is covered by `n = 3 < 7` proper linear subspaces (`v_2 = 0`, `v_3 = 0`, and
`v_2 + v_3 = 0`). -/
theorem exercise_1_18_printed_lower_bound_counterexample :
    ∃ (U : Fin 3 → Submodule (ZMod 2) (Kn 3 (ZMod 2))),
      setOrder (ZMod 2) = 2 ∧
      garlingDim (ZMod 2) (Kn 3 (ZMod 2)) (kn_isFiniteDimensional (ZMod 2) 3) = 3 ∧
      (∀ i : Fin 3, U i ≠ ⊤) ∧
      (⋃ i : Fin 3, (U i : Set (Kn 3 (ZMod 2)))) = Set.univ ∧
      3 < (2 ^ 3 - 1) / (2 - 1) := by
  let p₁ : Kn 3 (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (1 : Fin 3)
  let p₂ : Kn 3 (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2) (2 : Fin 3)
  let U₀ : Submodule (ZMod 2) (Kn 3 (ZMod 2)) := LinearMap.ker p₁
  let U₁ : Submodule (ZMod 2) (Kn 3 (ZMod 2)) := LinearMap.ker p₂
  let U₂ : Submodule (ZMod 2) (Kn 3 (ZMod 2)) := LinearMap.ker (p₁ + p₂)
  let U : Fin 3 → Submodule (ZMod 2) (Kn 3 (ZMod 2)) :=
    fun i => if i = 0 then U₀ else if i = 1 then U₁ else U₂
  refine ⟨U, ?_, garlingDim_kn (ZMod 2) 3, ?_, ?_, by decide⟩
  · simp [setOrder, ENat.card_eq_coe_fintype_card]
  · intro i
    fin_cases i
    · intro htop
      have htop₀ : U₀ = ⊤ := by simpa [U] using htop
      have hmem : (fun _ : Fin 3 => (1 : ZMod 2)) ∈ U₀ := htop₀ ▸ Submodule.mem_top
      change (1 : ZMod 2) = 0 at hmem
      revert hmem; decide
    · intro htop
      have htop₁ : U₁ = ⊤ := by simpa [U] using htop
      have hmem : (fun _ : Fin 3 => (1 : ZMod 2)) ∈ U₁ := htop₁ ▸ Submodule.mem_top
      change (1 : ZMod 2) = 0 at hmem
      revert hmem; decide
    · intro htop
      have htop₂ : U₂ = ⊤ := by simpa [U] using htop
      have hmem : garlingStdVec (ZMod 2) (1 : Fin 3) ∈ U₂ := htop₂ ▸ Submodule.mem_top
      change garlingStdVec (ZMod 2) (1 : Fin 3) 1 + garlingStdVec (ZMod 2) (1 : Fin 3) 2 = 0 at hmem
      revert hmem; decide
  · ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
    by_cases hv1 : v 1 = 0
    · exact ⟨0, by change v ∈ U₀; exact hv1⟩
    · by_cases hv2 : v 2 = 0
      · exact ⟨1, by change v ∈ U₁; exact hv2⟩
      · refine ⟨2, ?_⟩
        have hsum0 : v 1 + v 2 = 0 := by
          have hzmod2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
          have h1 : v 1 = 1 := (hzmod2 (v 1)).resolve_left hv1
          have h2 : v 2 = 1 := (hzmod2 (v 2)).resolve_left hv2
          rw [h1, h2]
          decide
        change v ∈ U₂
        exact hsum0

/-- **Exercise 1.18 (`r ≤ 1` edge case)** (§1.3, p. 13; queued fidelity hold): When `dim_K V ≤ 1`,
no finite family of proper linear subspaces can have union equal to `V`. -/
theorem exercise_1_18_no_proper_cover_of_dim_le_one {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] (hV : IsFiniteDimensional K V)
    (hr : garlingDim K V hV ≤ 1) (n : ℕ) (U : Fin n → Submodule K V)
    (hproper : ∀ i : Fin n, U i ≠ ⊤) :
    (⋃ i : Fin n, (U i : Set V)) ≠ Set.univ := by
  intro hcov
  have hU_bot : ∀ i : Fin n, U i = ⊥ := by
    intro i
    have h14 := theorem_1_4 hV (U i)
    have hlt : garlingDim K (U i) (subspace_isFiniteDimensional hV (U i)) < garlingDim K V hV :=
      lt_of_le_of_ne h14.1 (fun heq => hproper i (h14.2.mp heq))
    have hdim0 : garlingDim K (U i) (subspace_isFiniteDimensional hV (U i)) = 0 := by omega
    obtain ⟨B_U, hBUfin, hBU⟩ := exists_finite_basis (subspace_isFiniteDimensional hV (U i))
    have hBcard : hBUfin.toFinset.card = 0 := by
      have hc := garlingDim_spec (subspace_isFiniteDimensional hV (U i)) hBU
      rw [setOrder_eq_toFinset_card hBUfin, hdim0] at hc
      exact Nat.cast_injective (R := ℕ∞) hc
    have hBempty : B_U = ∅ := by
      have hfe : hBUfin.toFinset = ∅ := Finset.card_eq_zero.mp hBcard
      simpa using congrArg (fun S : Finset (U i) => (S : Set (U i))) hfe
    rw [eq_bot_iff]
    intro x hx
    have hx_u : (⟨x, hx⟩ : U i) ∈ (⊤ : Submodule K (U i)) := Submodule.mem_top
    rw [← hBU.2, hBempty, Submodule.span_empty, Submodule.mem_bot] at hx_u
    exact congrArg Subtype.val hx_u
  by_cases hr0 : garlingDim K V hV = 0
  · obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
    have hBcard : hBfin.toFinset.card = 0 := by
      have hc := garlingDim_spec hV hB
      rw [setOrder_eq_toFinset_card hBfin, hr0] at hc
      exact Nat.cast_injective (R := ℕ∞) hc
    have hBempty : B = ∅ := by
      have hfe : hBfin.toFinset = ∅ := Finset.card_eq_zero.mp hBcard
      simpa using congrArg (fun S : Finset V => (S : Set V)) hfe
    have h0mem : (0 : V) ∈ (⋃ i : Fin n, (U i : Set V)) := by rw [hcov]; trivial
    rcases Set.mem_iUnion.mp h0mem with ⟨i, _⟩
    apply hproper i
    rw [eq_top_iff]
    intro x _
    have hx_top : x ∈ (⊤ : Submodule K V) := Submodule.mem_top
    rw [← hB.2, hBempty, Submodule.span_empty, Submodule.mem_bot] at hx_top
    rw [hx_top]
    exact (U i).zero_mem
  · have hr1 : garlingDim K V hV = 1 := by omega
    obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
    have hBcard : hBfin.toFinset.card = 1 := by
      have hc := garlingDim_spec hV hB
      rw [setOrder_eq_toFinset_card hBfin, hr1] at hc
      exact Nat.cast_injective (R := ℕ∞) hc
    obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp hBcard
    have hvB : v ∈ B := hBfin.mem_toFinset.mp (by rw [hv_eq]; exact Finset.mem_singleton_self v)
    have hv_ne0 : v ≠ 0 := by
      intro hv0
      apply hB.1
      refine ⟨1, fun _ => v, fun _ => 1, fun _ _ _ => Subsingleton.elim _ _,
              fun _ => hvB, ⟨0, one_ne_zero⟩, ?_⟩
      simp [hv0]
    have hv_mem : v ∈ (⋃ i : Fin n, (U i : Set V)) := by rw [hcov]; trivial
    rcases Set.mem_iUnion.mp hv_mem with ⟨i, hvi⟩
    rw [hU_bot i, Submodule.bot_coe, Set.mem_singleton_iff] at hvi
    exact hv_ne0 hvi

/-- **Exercise 1.18 (sharp lower bound for arbitrary proper subspaces)** (§1.3, p. 13): Over a
finite field `K` with `k` elements, if an `r`-dimensional vector space `V` is covered by `n` proper
linear subspaces `U_1, ..., U_n`, then `k + 1 ≤ n`. -/
theorem exercise_1_18_sharp_lower_bound {K : Type*} [Field K] {k : ℕ}
    (hK : setOrder K = k) {V : Type*} [AddCommGroup V] [Module K V]
    (hV : IsFiniteDimensional K V) {r : ℕ} (hr : garlingDim K V hV = r)
    {n : ℕ} (U : Fin n → Submodule K V) (hproper : ∀ i : Fin n, U i ≠ ⊤)
    (hcov : (⋃ i : Fin n, (U i : Set V)) = Set.univ) :
    k + 1 ≤ n := by
  classical
  have hk2 : 2 ≤ k := by
    have h2 := (exercise_1_11).1 K
    rw [hK] at h2
    exact Nat.cast_le.mp h2
  by_cases hr_le1 : r ≤ 1
  · exact (exercise_1_18_no_proper_cover_of_dim_le_one hV (hr ▸ hr_le1) n U hproper hcov).elim
  have hr2 : 2 ≤ r := by omega
  have hKfin : Finite K := ENat.card_lt_top.mp (by rw [← setOrder, hK]; exact ENat.natCast_lt_top k)
  have : Fintype K := Fintype.ofFinite K
  have hk_card : Fintype.card K = k :=
    Nat.cast_injective (R := ℕ∞) (by rw [← ENat.card_eq_coe_fintype_card, ← setOrder, hK])
  obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
  have : Fintype V := Fintype.ofEquiv _ (basisEquivFunOnFinite hBfin hB).symm
  have hVcard : Fintype.card V = k ^ r := by
    rw [fintype_card_eq_pow_garlingDim hV, hk_card, hr]
  let S : Finset V := Finset.univ.erase 0
  have hScard : S.card = k ^ r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hVcard]
  let piece : Fin n → Finset V := fun i => (Finset.univ.filter (fun x : V => x ∈ U i)).erase 0
  have hS_sub : S ⊆ Finset.univ.biUnion piece := by
    intro x hx
    have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have hx_univ : x ∈ (⋃ i : Fin n, (U i : Set V)) := by rw [hcov]; trivial
    rcases Set.mem_iUnion.mp hx_univ with ⟨i, hxi⟩
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxi⟩⟩⟩
  have hpiece_le : ∀ i : Fin n, (piece i).card ≤ k ^ (r - 1) - 1 := by
    intro i
    have h14 := theorem_1_4 hV (U i)
    have hlt : garlingDim K (U i) (subspace_isFiniteDimensional hV (U i)) < r := by
      rw [← hr]
      exact lt_of_le_of_ne h14.1 (fun heq => hproper i (h14.2.mp heq))
    have hd_le : garlingDim K (U i) (subspace_isFiniteDimensional hV (U i)) ≤ r - 1 := by omega
    have hUcard : Fintype.card (U i) ≤ k ^ (r - 1) := by
      rw [fintype_card_eq_pow_garlingDim (subspace_isFiniteDimensional hV (U i)), hk_card]
      exact Nat.pow_le_pow_right (by omega) hd_le
    have hfilter_card : (Finset.univ.filter (fun x : V => x ∈ U i)).card = Fintype.card (U i) := by
      refine Finset.card_bij (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : U i))
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun u _ => ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ u.1, u.2⟩, rfl⟩)
    have h0_in : (0 : V) ∈ Finset.univ.filter (fun x : V => x ∈ U i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ 0, (U i).zero_mem⟩
    dsimp only [piece]
    rw [Finset.card_erase_of_mem h0_in, hfilter_card]
    omega
  have hcount : k ^ r - 1 ≤ n * (k ^ (r - 1) - 1) := by
    calc k ^ r - 1 = S.card := hScard.symm
      _ ≤ (Finset.univ.biUnion piece).card := Finset.card_le_card hS_sub
      _ ≤ ∑ i : Fin n, (piece i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, (k ^ (r - 1) - 1) := Finset.sum_le_sum (fun i _ => hpiece_le i)
      _ = n * (k ^ (r - 1) - 1) := by simp
  by_contra hnot
  have hn_le : n ≤ k := by omega
  have hmul_le : n * (k ^ (r - 1) - 1) ≤ k * (k ^ (r - 1) - 1) :=
    Nat.mul_le_mul_right _ hn_le
  have hk_pow_pos : 1 ≤ k ^ (r - 1) := Nat.one_le_pow (r - 1) k (by omega)
  have hpow_split : k * k ^ (r - 1) = k ^ r := by
    conv_rhs => rw [show r = (r - 1) + 1 by omega, pow_succ, mul_comm]
  have hprod_eq : k * (k ^ (r - 1) - 1) = k ^ r - k := by
    rw [Nat.mul_sub_one, hpow_split]
  have hkr_ge_k : k ≤ k ^ r := by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ r := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Exercise 1.18 (printed lower bound for `1`-dimensional subspaces, including all proper
subspaces when `r = 2`)** (§1.3, p. 13): If each `U_i` has `dim_K U_i ≤ 1` and
`V = ⋃_{i=1}^n U_i`, then `(k^r - 1) / (k - 1) ≤ n`. -/
theorem exercise_1_18_one_dim_lower_bound {K : Type*} [Field K] {k : ℕ}
    (hK : setOrder K = k) {V : Type*} [AddCommGroup V] [Module K V]
    (hV : IsFiniteDimensional K V) {r : ℕ} (hr : garlingDim K V hV = r)
    {n : ℕ} (U : Fin n → Submodule K V)
    (hdim1 : ∀ i : Fin n, garlingDim K (U i) (subspace_isFiniteDimensional hV (U i)) ≤ 1)
    (hcov : (⋃ i : Fin n, (U i : Set V)) = Set.univ) :
    (k ^ r - 1) / (k - 1) ≤ n := by
  classical
  have hk2 : 2 ≤ k := by
    have h2 := (exercise_1_11).1 K
    rw [hK] at h2
    exact Nat.cast_le.mp h2
  have hKfin : Finite K := ENat.card_lt_top.mp (by rw [← setOrder, hK]; exact ENat.natCast_lt_top k)
  have : Fintype K := Fintype.ofFinite K
  have hk_card : Fintype.card K = k :=
    Nat.cast_injective (R := ℕ∞) (by rw [← ENat.card_eq_coe_fintype_card, ← setOrder, hK])
  obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
  have : Fintype V := Fintype.ofEquiv _ (basisEquivFunOnFinite hBfin hB).symm
  have hVcard : Fintype.card V = k ^ r := by
    rw [fintype_card_eq_pow_garlingDim hV, hk_card, hr]
  let S : Finset V := Finset.univ.erase 0
  have hScard : S.card = k ^ r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hVcard]
  let piece : Fin n → Finset V := fun i => (Finset.univ.filter (fun x : V => x ∈ U i)).erase 0
  have hS_sub : S ⊆ Finset.univ.biUnion piece := by
    intro x hx
    have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have hx_univ : x ∈ (⋃ i : Fin n, (U i : Set V)) := by rw [hcov]; trivial
    rcases Set.mem_iUnion.mp hx_univ with ⟨i, hxi⟩
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Finset.mem_erase.mpr ⟨hx_ne, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxi⟩⟩⟩
  have hpiece_le : ∀ i : Fin n, (piece i).card ≤ k - 1 := by
    intro i
    have hUcard : Fintype.card (U i) ≤ k ^ 1 := by
      rw [fintype_card_eq_pow_garlingDim (subspace_isFiniteDimensional hV (U i)), hk_card]
      exact Nat.pow_le_pow_right (by omega) (hdim1 i)
    rw [pow_one] at hUcard
    have hfilter_card : (Finset.univ.filter (fun x : V => x ∈ U i)).card = Fintype.card (U i) := by
      refine Finset.card_bij (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : U i))
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun u _ => ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ u.1, u.2⟩, rfl⟩)
    have h0_in : (0 : V) ∈ Finset.univ.filter (fun x : V => x ∈ U i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ 0, (U i).zero_mem⟩
    dsimp only [piece]
    rw [Finset.card_erase_of_mem h0_in, hfilter_card]
    omega
  have hcount : k ^ r - 1 ≤ n * (k - 1) := by
    calc k ^ r - 1 = S.card := hScard.symm
      _ ≤ (Finset.univ.biUnion piece).card := Finset.card_le_card hS_sub
      _ ≤ ∑ i : Fin n, (piece i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, (k - 1) := Finset.sum_le_sum (fun i _ => hpiece_le i)
      _ = n * (k - 1) := by simp
  exact Nat.div_le_of_le_mul (by linarith)

/-- **Exercise 1.18 (existence of `(k^r - 1) / (k - 1)` proper subspaces covering `V` for `r ≥ 2`)**
(§1.3, p. 13): When `2 ≤ r = dim_K V` over a finite field `K` of order `k`, there exist
`(k^r - 1) / (k - 1)` distinct proper linear subspaces of `V` whose union is `V`. -/
theorem exercise_1_18_exists_proper_subspaces_union {K : Type*} [Field K] {k : ℕ}
    (hK : setOrder K = k) {V : Type*} [AddCommGroup V] [Module K V]
    (hV : IsFiniteDimensional K V) {r : ℕ} (hr : garlingDim K V hV = r) (hr2 : 2 ≤ r) :
    ∃ U : Fin ((k ^ r - 1) / (k - 1)) → Submodule K V,
      Function.Injective U ∧
      (∀ i, U i ≠ ⊤) ∧
      (⋃ i, (U i : Set V)) = Set.univ := by
  classical
  have hk2 : 2 ≤ k := by
    have h2 := (exercise_1_11).1 K
    rw [hK] at h2
    exact Nat.cast_le.mp h2
  have hKfin : Finite K := ENat.card_lt_top.mp (by rw [← setOrder, hK]; exact ENat.natCast_lt_top k)
  have : Fintype K := Fintype.ofFinite K
  have hk_card : Fintype.card K = k :=
    Nat.cast_injective (R := ℕ∞) (by rw [← ENat.card_eq_coe_fintype_card, ← setOrder, hK])
  obtain ⟨B, hBfin, hB⟩ := exists_finite_basis hV
  have : Fintype V := Fintype.ofEquiv _ (basisEquivFunOnFinite hBfin hB).symm
  have hVcard : Fintype.card V = k ^ r := by
    rw [fintype_card_eq_pow_garlingDim hV, hk_card, hr]
  let S : Finset V := Finset.univ.erase 0
  have hScard : S.card = k ^ r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hVcard]
  let π : V → Submodule K V := fun v => Submodule.span K {v}
  let L₀ : Finset (Submodule K V) := S.image π
  have hfiber_card : ∀ W ∈ L₀, (S.filter (fun x => π x = W)).card = k - 1 := by
    intro W hW
    rcases Finset.mem_image.mp hW with ⟨v, hvS, rfl⟩
    have hv_ne : v ≠ 0 := (Finset.mem_erase.mp hvS).1
    let Kstar : Finset K := Finset.univ.erase 0
    have hKstar_card : Kstar.card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hk_card]
    rw [← hKstar_card]
    refine (Finset.card_bij (fun (c : K) (_ : c ∈ Kstar) => c • v) ?_ ?_ ?_).symm
    · intro c hc
      have hc_ne : c ≠ 0 := (Finset.mem_erase.mp hc).1
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_erase.mpr ⟨smul_ne_zero hc_ne hv_ne, Finset.mem_univ _⟩, ?_⟩
      dsimp only [π]
      apply le_antisymm
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        have hmem : c⁻¹ • (c • v) ∈ Submodule.span K ({c • v} : Set V) :=
          Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (Set.mem_singleton (c • v)))
        rwa [inv_smul_smul₀ hc_ne v] at hmem
    · intro c₁ _ c₂ _ heq
      have hsub : (c₁ - c₂) • v = 0 := by rw [sub_smul, heq, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hv_ne)
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hx_span⟩
      have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hxS).1
      have hx_mem : x ∈ π v := by
        rw [← hx_span]
        exact Submodule.subset_span (Set.mem_singleton x)
      rcases Submodule.mem_span_singleton.mp hx_mem with ⟨c, rfl⟩
      have hc_ne : c ≠ 0 := fun hc0 => hx_ne (by simp [hc0])
      exact ⟨c, Finset.mem_erase.mpr ⟨hc_ne, Finset.mem_univ c⟩, rfl⟩
  have hsum_fibers : S.card = L₀.card * (k - 1) := by
    rw [Finset.card_eq_sum_card_image π S]
    calc ∑ W ∈ L₀, (S.filter (fun x => π x = W)).card
      _ = ∑ _W ∈ L₀, (k - 1) := Finset.sum_congr rfl hfiber_card
      _ = L₀.card * (k - 1) := by simp
  have hL₀_card : L₀.card = (k ^ r - 1) / (k - 1) := by
    rw [hScard] at hsum_fibers
    rw [hsum_fibers, Nat.mul_div_cancel _ (by omega)]
  let e : Fin ((k ^ r - 1) / (k - 1)) ≃ L₀ :=
    (Fin.castOrderIso hL₀_card.symm).toEquiv.trans L₀.equivFin.symm
  refine ⟨fun i => (e i).1, fun i₁ i₂ h => e.injective (Subtype.ext h), ?_, ?_⟩
  · intro i
    rcases Finset.mem_image.mp (e i).2 with ⟨v, _, hv_eq⟩
    intro htop
    have hspan_top : Spans K V {v} := by
      change π v = ⊤
      rw [hv_eq]
      exact htop
    obtain ⟨B₀, _, hB₀⟩ := exists_finite_basis hV
    have hle := theorem_1_2 hspan_top hB₀.1
    rw [garlingDim_spec hV hB₀, hr] at hle
    have hsingle : setOrder ({v} : Set V) = 1 := by
      have hf : ({v} : Set V).Finite := Set.finite_singleton v
      rw [setOrder_eq_toFinset_card hf]
      simp
    rw [hsingle] at hle
    have hr_le1 : r ≤ 1 := Nat.cast_le.mp hle
    omega
  · ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
    by_cases hx0 : x = 0
    · subst hx0
      have hpos : 0 < (k ^ r - 1) / (k - 1) := by
        have hge : k - 1 ≤ k ^ r - 1 := by
          have hk1 : k ^ 1 ≤ k ^ r := Nat.pow_le_pow_right (by omega) (by omega)
          rw [pow_one] at hk1
          omega
        exact Nat.div_pos hge (by omega)
      exact ⟨⟨0, hpos⟩, (e ⟨0, hpos⟩).1.zero_mem⟩
    · have hπ_mem : π x ∈ L₀ :=
        Finset.mem_image_of_mem π (Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ x⟩)
      refine ⟨e.symm ⟨π x, hπ_mem⟩, ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact Submodule.subset_span (Set.mem_singleton x)

end Garling.Chapter01
