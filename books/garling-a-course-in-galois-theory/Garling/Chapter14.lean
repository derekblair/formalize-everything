import Garling.Chapter11
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Chapter 14: Cubics and quartics

Formalization of Chapter 14 (*Cubics and quartics*, printed pp. 110–117 / PDF pp. 118–125)
of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering the
4-line unnumbered chapter preamble, all four sections (`§14.1`–`§14.4`), the main-text theorem
(`Theorem 14.1`), all 8 numbered exercises (`Exercise 14.1`–`Exercise 14.8`), and all unnumbered
prose definitions and structural derivations in exact source order.
-/

namespace Garling.Chapter14

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter08 Garling.Chapter09
open Garling.Chapter10 Garling.Chapter11
open scoped BigOperators Polynomial IntermediateField Matrix Classical

universe u v w

/-! ## §14.1 Extension by radicals (printed p. 110, PDF p. 118) -/

/-- Garling's prose definition of a *radical over `K`* (§14.1, printed p. 110 / PDF p. 118):
*"If `L : K` is an extension, and `β ∈ L`, we say that `β` is a **radical** over `K` if `βⁿ ∈ K`
for some `n`. Thus a radical over `K` is an `n`th root of some element of `K`, possibly in a larger
field."*

As noted in `PROGRESS.md` (`BRIEF.md` Flag 4), *"an `n`th root"* requires a positive integer
exponent `1 ≤ n` (`n = 0` would give `β⁰ = 1 ∈ K` for every element of every extension, including
transcendental elements; see `radical_zero_exponent_trivial`).
*(OCR warning verified against 200 DPI scan p. 110 / PDF p. 118: `garling1986_pages.txt` splits
`βⁿ ∈ K` across three lines as `{3 / 11 / E K`.)* -/
def IsGarlingRadicalOver (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (β : L) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ β ^ n ∈ Set.range (algebraMap K L)

/-- Subfield variant of *radical* (`β ∈ L` is a radical over a subfield `F ⊆ L`). -/
def IsGarlingRadicalOverSubfield {L : Type u} [Field L] (F : Subfield L) (β : L) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ β ^ n ∈ F

theorem isGarlingRadicalOver_iff_subfield {L : Type u} [Field L] (F : Subfield L) (β : L) :
    IsGarlingRadicalOver F β ↔ IsGarlingRadicalOverSubfield F β := by
  unfold IsGarlingRadicalOver IsGarlingRadicalOverSubfield
  constructor <;> rintro ⟨n, hn, hmem⟩ <;> refine ⟨n, hn, ?_⟩
  · rcases hmem with ⟨x, hx⟩
    rw [← hx]
    exact x.2
  · exact ⟨⟨β ^ n, hmem⟩, rfl⟩

/-- Witness showing why `1 ≤ n` is essential in `IsGarlingRadicalOver`: at `n = 0`, even the
transcendental generator `X ∈ FractionRing ℚ[X]` satisfies `X ^ 0 = 1 ∈ ℚ`, while it is not
algebraic over `ℚ` and satisfies `¬ IsGarlingRadicalOver ℚ X`. -/
theorem radical_zero_exponent_trivial :
    let t : FractionRing ℚ[X] := ratFuncVar ℚ
    t ^ 0 ∈ Set.range (algebraMap ℚ (FractionRing ℚ[X])) ∧
    IsGarlingTranscendental ℚ t ∧
    ¬ IsGarlingRadicalOver ℚ t := by
  intro t
  have h0 : t ^ 0 ∈ Set.range (algebraMap ℚ (FractionRing ℚ[X])) := ⟨1, by simp⟩
  have hinj : Function.Injective (algebraMap ℚ[X] (FractionRing ℚ[X])) :=
    IsFractionRing.injective ℚ[X] (FractionRing ℚ[X])
  have heq : ∀ g : ℚ[X], Polynomial.aeval t g = algebraMap ℚ[X] (FractionRing ℚ[X]) g := by
    intro g
    induction g using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.aeval_C,
        Polynomial.aeval_X, map_mul, map_pow]
      congr 1
      exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (FractionRing ℚ[X]) a
  have htr : IsGarlingTranscendental ℚ t := by
    rintro ⟨f, hf0, hfeval⟩
    exact hf0 (hinj (by rw [← heq f, hfeval, map_zero]))
  have hnot_rad : ¬ IsGarlingRadicalOver ℚ t := by
    rintro ⟨n, hn, c, hc⟩
    apply htr
    refine ⟨Polynomial.X ^ n - Polynomial.C c, ?_, ?_⟩
    · intro hzero
      have hdeg := congrArg Polynomial.natDegree hzero
      rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at hdeg
      omega
    · simp [hc]
  exact ⟨h0, htr, hnot_rad⟩

/-- Every radical over `K` is algebraic over `K`. -/
theorem isGarlingAlgebraic_of_isGarlingRadicalOver {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {β : L} (h : IsGarlingRadicalOver K β) :
    IsGarlingAlgebraic K β := by
  rcases h with ⟨n, hn, c, hc⟩
  refine ⟨Polynomial.X ^ n - Polynomial.C c, ?_, ?_⟩
  · intro h0
    have hd := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at hd
    omega
  · simp [hc]

/-- Exact `Subfield` characterization of `IntermediateField.adjoin`: its underlying subfield is
`Subfield.closure (Set.range (algebraMap M L) ∪ S)`, avoiding all multi-algebra diamonds. -/
private theorem adjoin_toSubfield_eq_closure {M : Type v} {L : Type w}
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

/-- When `F : Subfield L` already contains `Set.range (algebraMap M L)`, adjoining `F ∪ S` over `M`
has underlying subfield `Subfield.closure (F ∪ S)`. -/
private theorem adjoin_sup_toSubfield_eq_closure {M : Type v} {L : Type w}
    [Field M] [Field L] [Algebra M L] (F : Subfield L) (S : Set L)
    (hM : ∀ m : M, algebraMap M L m ∈ F) :
    (IntermediateField.adjoin M ((F : Set L) ∪ S)).toSubfield =
      Subfield.closure ((F : Set L) ∪ S) := by
  rw [adjoin_toSubfield_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_range]
  constructor
  · rintro (⟨m, rfl⟩ | hx | hx)
    · exact Or.inl (hM m)
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)

/-- Garling's prose definition of an *extension by radicals* (§14.1, printed p. 110 / PDF p. 118):
*"We shall say that an extension `L : K` is an **extension by radicals** if there are intermediate
fields `L = L_r : L_{r-1} : … : L_0 = K` such that `L_i = L_{i-1}(β_i)`, with `β_i` a radical over
`L_{i-1}`, for `1 ≤ i ≤ r`. Thus `L : K` is an extension by radicals if `L` can be obtained by
successively adjoining radicals."* -/
def IsGarlingExtensionByRadicals (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Prop :=
  ∃ (r : ℕ) (F : Fin (r + 1) → IntermediateField K L) (β : Fin r → L),
    F 0 = ⊥ ∧
    F (Fin.last r) = ⊤ ∧
    ∀ i : Fin r,
      (∃ n : ℕ, 1 ≤ n ∧ (β i) ^ n ∈ F i.castSucc) ∧
      F i.succ = IntermediateField.adjoin K ((F i.castSucc : Set L) ∪ {β i})

/-- Trivial `0`-step radical extension when `L = K` (`⊥ = ⊤`). -/
theorem isGarlingExtensionByRadicals_of_bot_eq_top {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (h : (⊥ : IntermediateField K L) = ⊤) :
    IsGarlingExtensionByRadicals K L :=
  ⟨0, fun _ => ⊥, Fin.elim0, rfl, h, fun i => Fin.elim0 i⟩

/-- Reflexivity: `K : K` is an extension by radicals. -/
theorem isGarlingExtensionByRadicals_self (K : Type u) [Field K] :
    IsGarlingExtensionByRadicals K K :=
  isGarlingExtensionByRadicals_of_bot_eq_top (Subsingleton.elim _ _)

/-- Single-step radical extension: if `L = K(β)` with `β` a radical over `K`, then `L : K` is an
extension by radicals (`r = 1`). -/
theorem isGarlingExtensionByRadicals_single {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {β : L}
    (hrad : IsGarlingRadicalOver K β) (hadj : IntermediateField.adjoin K ({β} : Set L) = ⊤) :
    IsGarlingExtensionByRadicals K L := by
  rcases hrad with ⟨n, hn, c, hc⟩
  refine ⟨1, ![⊥, ⊤], ![β], rfl, rfl, fun i => ?_⟩
  fin_cases i
  refine ⟨⟨n, hn, ?_⟩, ?_⟩
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

/-- Transport of `IsGarlingExtensionByRadicals` along a `K`-algebra isomorphism `L₁ ≃ₐ[K] L₂`. -/
theorem isGarlingExtensionByRadicals_congr {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (h : IsGarlingExtensionByRadicals K L₁) :
    IsGarlingExtensionByRadicals K L₂ := by
  rcases h with ⟨r, F, β, h0, hlast, hstep⟩
  refine ⟨r, fun j => (F j).map e.toAlgHom, fun i => e (β i), ?_, ?_, fun i => ?_⟩
  · dsimp only
    rw [h0]
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (e.toAlgHom.commutes k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨algebraMap K L₁ k, ⟨k, rfl⟩, e.toAlgHom.commutes k⟩
  · dsimp only
    rw [hlast]
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and, iff_true]
    exact ⟨e.symm x, e.apply_symm_apply x⟩
  · dsimp only
    obtain ⟨⟨n, hn, hpow⟩, hadj⟩ := hstep i
    refine ⟨⟨n, hn, ⟨(β i) ^ n, hpow, map_pow e (β i) n⟩⟩, ?_⟩
    rw [hadj]
    apply le_antisymm
    · rw [IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact IntermediateField.subset_adjoin K _ (Or.inl ⟨x, hx, rfl⟩)
      · exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
    · rw [IntermediateField.adjoin_le_iff]
      rintro y (⟨x, hx, rfl⟩ | rfl)
      · exact ⟨x, IntermediateField.subset_adjoin K _ (Or.inl hx), rfl⟩
      · exact ⟨β i, IntermediateField.subset_adjoin K _ (Or.inr rfl), rfl⟩

/-- Tower transitivity of extensions by radicals: if `M : K` and `L : M` are extensions by radicals
in a scalar tower `K → M → L`, then `L : K` is an extension by radicals. -/
theorem isGarlingExtensionByRadicals_tower (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    (hKM : IsGarlingExtensionByRadicals K M) (hML : IsGarlingExtensionByRadicals M L) :
    IsGarlingExtensionByRadicals K L := by
  rcases hKM with ⟨r₁, F₁, β₁, hF₁0, hF₁last, hstep₁⟩
  rcases hML with ⟨r₂, F₂, β₂, hF₂0, hF₂last, hstep₂⟩
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
    if hi : (i : ℕ) < r₁ then
      ι (β₁ ⟨i, hi⟩)
    else
      β₂ ⟨(i : ℕ) - r₁, by omega⟩
  have hF_low : ∀ m (hm : m ≤ r₁), F ⟨m, by omega⟩ = (F₁ ⟨m, Nat.lt_succ_of_le hm⟩).map ι := by
    intro m hm
    simp [F, hm]
  have hF_high : ∀ m (hm : m ≤ r₂),
      F ⟨r₁ + m, by omega⟩ = (F₂ ⟨m, Nat.lt_succ_of_le hm⟩).restrictScalars K := by
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.add_zero, F, le_refl, ↓reduceDIte]
      exact hbridge
    · have hnot : ¬ (r₁ + m ≤ r₁) := by omega
      simp [F, hnot]
  refine ⟨r₁ + r₂, F, β, ?_, ?_, fun i => ?_⟩
  · change F ⟨0, by omega⟩ = ⊥
    rw [hF_low 0 (Nat.zero_le r₁)]
    have h0' : (⟨0, Nat.lt_succ_of_le (Nat.zero_le r₁)⟩ : Fin (r₁ + 1)) = 0 := rfl
    rw [h0', hF₁0]
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, IsScalarTower.algebraMap_apply K M L k⟩
    · rintro ⟨k, rfl⟩
      exact ⟨algebraMap K M k, ⟨k, rfl⟩, (IsScalarTower.algebraMap_apply K M L k).symm⟩
  · have hlast_eq : Fin.last (r₁ + r₂) = ⟨r₁ + r₂, by omega⟩ := rfl
    rw [hlast_eq, hF_high r₂ (le_refl r₂)]
    have hl2 : (⟨r₂, Nat.lt_succ_of_le (le_refl r₂)⟩ : Fin (r₂ + 1)) = Fin.last r₂ := rfl
    rw [hl2, hF₂last]
    rfl
  · by_cases hi : (i : ℕ) < r₁
    · let i₁ : Fin r₁ := ⟨i, hi⟩
      have hcast : F i.castSucc = (F₁ i₁.castSucc).map ι := hF_low i (Nat.le_of_lt hi)
      have hsucc : F i.succ = (F₁ i₁.succ).map ι := hF_low (i + 1) hi
      have hβ : β i = ι (β₁ i₁) := by simp [β, hi, i₁]
      rw [hcast, hsucc, hβ]
      obtain ⟨⟨n, hn, hpow⟩, hadj⟩ := hstep₁ i₁
      refine ⟨⟨n, hn, ⟨(β₁ i₁) ^ n, hpow, map_pow ι (β₁ i₁) n⟩⟩, ?_⟩
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
        rw [hc, hF_high i₂ (Nat.le_of_lt i₂.2)]
        rfl
      have hsucc : F i.succ = (F₂ i₂.succ).restrictScalars K := by
        have hs : i.succ = ⟨r₁ + (i₂ + 1), by omega⟩ := Fin.ext (by simp [hi_eq, Nat.add_assoc])
        rw [hs, hF_high (i₂ + 1) i₂.2]
        rfl
      have hβ : β i = β₂ i₂ := by simp [β, hi, i₂]
      rw [hcast, hsucc, hβ]
      obtain ⟨⟨n, hn, hpow⟩, hadj⟩ := hstep₂ i₂
      refine ⟨⟨n, hn, hpow⟩, ?_⟩
      rw [hadj]
      apply IntermediateField.toSubfield_injective
      change (IntermediateField.adjoin M ((F₂ i₂.castSucc : Set L) ∪ {β₂ i₂})).toSubfield =
        (IntermediateField.adjoin K
          ((((F₂ i₂.castSucc).restrictScalars K : IntermediateField K L) : Set L) ∪
            {β₂ i₂})).toSubfield
      rw [adjoin_toSubfield_eq_closure, adjoin_toSubfield_eq_closure]
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

/-- Every extension by radicals is a finite extension (`[L : K] < ∞`). -/
theorem isFiniteExtension_of_isGarlingExtensionByRadicals {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (h : IsGarlingExtensionByRadicals K L) :
    IsFiniteExtension K L := by
  rcases h with ⟨r, F, β, h0, hlast, hstep⟩
  have hfin_step : ∀ k : ℕ, (hk : k ≤ r) → Module.Finite K (F ⟨k, Nat.lt_succ_of_le hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0' : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (r + 1)) = 0 := rfl
      rw [h0', h0]
      infer_instance
    | succ m ih =>
      intro hm
      let i : Fin r := ⟨m, hm⟩
      have _ : Module.Finite K (F i.castSucc) := ih (Nat.le_of_lt hm)
      obtain ⟨⟨n, hn, hpow⟩, hadj⟩ := hstep i
      have hrad_i : IsGarlingRadicalOver (F i.castSucc) (β i) :=
        ⟨n, hn, ⟨(β i) ^ n, hpow⟩, rfl⟩
      have hint_i : IsIntegral (F i.castSucc) (β i) :=
        (isGarlingAlgebraic_iff_isIntegral (F i.castSucc) (β i)).mp
          (isGarlingAlgebraic_of_isGarlingRadicalOver hrad_i)
      let E : IntermediateField (F i.castSucc) L := IntermediateField.adjoin (F i.castSucc) {β i}
      have _ : Module.Finite (F i.castSucc) E := IntermediateField.adjoin.finiteDimensional hint_i
      have _ : Module.Finite K E := Module.Finite.trans (F i.castSucc) E
      have hEq : F i.succ = E.restrictScalars K := by
        rw [hadj]
        apply IntermediateField.toSubfield_injective
        change (IntermediateField.adjoin K ((F i.castSucc : Set L) ∪ {β i})).toSubfield =
          (IntermediateField.adjoin (F i.castSucc) ({β i} : Set L)).toSubfield
        rw [adjoin_toSubfield_eq_closure, adjoin_toSubfield_eq_closure]
        congr 1
        ext x
        simp only [Set.mem_union, Set.mem_range]
        constructor
        · rintro (⟨k, rfl⟩ | hx | hx)
          · exact Or.inl ⟨⟨algebraMap K L k, (F i.castSucc).algebraMap_mem k⟩, rfl⟩
          · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
          · exact Or.inr hx
        · rintro (⟨a, rfl⟩ | hx)
          · exact Or.inr (Or.inl a.2)
          · exact Or.inr (Or.inr hx)
      have hs : (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (r + 1)) = i.succ := rfl
      rw [hs, hEq]
      change Module.Finite K E
      infer_instance
  have htop_fin : Module.Finite K (⊤ : IntermediateField K L) := by
    rw [← hlast]
    exact hfin_step r (le_refl r)
  have _ : Module.Finite K L :=
    Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv
  exact (isFiniteExtension_iff_moduleFinite K L).mpr inferInstance

/-- Garling's prose definition that `f ∈ K[x]` is *solvable by radicals* (§14.1, printed p. 110 /
PDF p. 118):
*"Now suppose that `f ∈ K[x]`. We say that `f` is **solvable by radicals** if there is an extension
`L : K` by radicals such that `f` splits over `L`. It is important to note that `L` need not be a
splitting field for `f` – it may be considerably larger."* -/
def IsGarlingSolvableByRadicals {K : Type u} [Field K] (f : K[X]) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
    IsGarlingExtensionByRadicals K L ∧ GarlingSplitsOver K L f

/-- Fresh carrier wrapper over `Fin m → K` with zero pre-existing algebraic instances, used to
transport a finite-dimensional field extension `L : Type v` into `Type u` cleanly. -/
private structure RadVecCarrier (K : Type u) (m : ℕ) : Type u where
  ofVec ::
  toVec : Fin m → K

private def radVecCarrierEquiv (K : Type u) (m : ℕ) : RadVecCarrier K m ≃ (Fin m → K) where
  toFun x := x.toVec
  invFun v := ⟨v⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Universe-polymorphic descent for `IsGarlingSolvableByRadicals`: if `f ∈ K[x]` (`K : Type u`)
splits over an extension by radicals `L : Type v` in *any* universe `v`, then `f` splits over an
extension by radicals in `Type u`. -/
theorem isGarlingSolvableByRadicals_of_extension {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]}
    (hrad : IsGarlingExtensionByRadicals K L) (hspl : GarlingSplitsOver K L f) :
    IsGarlingSolvableByRadicals f := by
  have hfin : IsFiniteExtension K L := isFiniteExtension_of_isGarlingExtensionByRadicals hrad
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  let m := Module.finrank K L
  let b : Module.Basis (Fin m) K L := Module.finBasis K L
  let e : L ≃ RadVecCarrier K m := b.equivFun.toEquiv.trans (radVecCarrierEquiv K m).symm
  let fInst : Field (RadVecCarrier K m) := e.symm.field
  let _ : Field (RadVecCarrier K m) := fInst
  let φ : L ≃+* RadVecCarrier K m := e.symm.ringEquiv.symm
  let aInst : Algebra K (RadVecCarrier K m) :=
    RingHom.toAlgebra (φ.toRingHom.comp (algebraMap K L))
  let _ : Algebra K (RadVecCarrier K m) := aInst
  let ψ : L ≃ₐ[K] RadVecCarrier K m :=
    { φ with commutes' := fun _ => rfl }
  refine ⟨RadVecCarrier K m, fInst, aInst,
    isGarlingExtensionByRadicals_congr ψ hrad, ?_⟩
  rcases hspl with ⟨n, c, α, hexp⟩
  refine ⟨n, c, fun i => ψ (α i), ?_⟩
  unfold GarlingSplitsExplicit
  have hmap : f.map (algebraMap K (RadVecCarrier K m)) =
      (f.map (algebraMap K L)).map ψ.toRingHom := by
    rw [Polynomial.map_map]
    rfl
  rw [hmap, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- Adjoining a single `n`th root (`n ≥ 1`) of `c ∈ K` produces a `1`-step extension by radicals in
`Type u`. -/
theorem exists_radical_step_extension {K : Type u} [Field K] (c : K) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (β : L),
      β ^ n = algebraMap K L c ∧
      IntermediateField.adjoin K ({β} : Set L) = ⊤ ∧
      IsGarlingExtensionByRadicals K L := by
  let p : K[X] := Polynomial.X ^ n - Polynomial.C c
  have hp_deg : p.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hp_pos : 0 < p.natDegree := by omega
  let E := Polynomial.SplittingField p
  have hsplits : (p.map (algebraMap K E)).Splits := Polynomial.SplittingField.splits p
  have hdeg_ne : (p.map (algebraMap K E)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap K E).injective,
      Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_natDegree_gt hp_pos)]
    exact_mod_cast (Nat.ne_of_gt hp_pos)
  obtain ⟨β, hβ_root⟩ := hsplits.exists_eval_eq_zero hdeg_ne
  have hβ_pow : β ^ n = algebraMap K E c := by
    rw [Polynomial.eval_map, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, sub_eq_zero] at hβ_root
    exact hβ_root
  let L : IntermediateField K E := IntermediateField.adjoin K ({β} : Set E)
  let βL : L := ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
  have hβL_pow : βL ^ n = algebraMap K L c := by
    ext
    exact hβ_pow
  have hadjL : IntermediateField.adjoin K ({βL} : Set L) = ⊤ := by
    apply le_antisymm le_top
    let F_sub : IntermediateField K E := (IntermediateField.adjoin K ({βL} : Set L)).map L.val
    have hL_le : L ≤ F_sub := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨βL, IntermediateField.mem_adjoin_simple_self K βL, rfl⟩
    intro x _
    obtain ⟨y, hy, hy_eq⟩ := hL_le x.2
    have hxy : y = x := Subtype.ext hy_eq
    rw [← hxy]
    exact hy
  exact ⟨L, inferInstance, inferInstance, βL, hβL_pow, hadjL,
    isGarlingExtensionByRadicals_single ⟨n, hn, c, hβL_pow.symm⟩ hadjL⟩

/-- Helper converting `ringChar K ≠ p` (for prime `p`) to `(p : K) ≠ 0`. -/
theorem natCast_prime_ne_zero_of_ringChar_ne {K : Type*} [Field K] {p : ℕ}
    (hp : Nat.Prime p) (hchar : ringChar K ≠ p) : (p : K) ≠ 0 := by
  intro h0
  have hdvd : ringChar K ∣ p := (ringChar.spec K p).mp h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hz
  · exact hchar ((hp.dvd_iff_eq hq.ne_one).mp hdvd).symm
  · rw [hz] at hdvd
    exact absurd (zero_dvd_iff.mp hdvd) hp.ne_zero

/-- Motivating §14.1 remark (printed p. 110, ll. 1–3): every quadratic polynomial `f ∈ K[x]`
(`deg f = 2`) over a field `K` with `char K ≠ 2` is solvable by radicals (adjoining a single
square root). -/
theorem quadratic_solvable_by_radicals {K : Type u} [Field K] (hchar : ringChar K ≠ 2)
    {f : K[X]} (hdeg : f.natDegree = 2) :
    IsGarlingSolvableByRadicals f := by
  have h2ne : (2 : K) ≠ 0 := natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar
  let a₂ := f.coeff 2
  let a₁ := f.coeff 1
  let a₀ := f.coeff 0
  have ha₂ : a₂ ≠ 0 := by
    dsimp [a₂]
    rw [← hdeg, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega))
  let d : K := a₁ ^ 2 - 4 * a₂ * a₀
  obtain ⟨L, _, _, s, hs_sq, _, hrad⟩ := exists_radical_step_extension d (by decide : 1 ≤ 2)
  refine isGarlingSolvableByRadicals_of_extension hrad ?_
  have h2L : (2 : L) ≠ 0 := by
    have hmap2 : algebraMap K L (2 : K) = (2 : L) := map_ofNat (algebraMap K L) 2
    rw [← hmap2]
    exact (map_ne_zero (algebraMap K L)).mpr h2ne
  have ha₂L : algebraMap K L a₂ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr ha₂
  let r₁ : L := (-algebraMap K L a₁ + s) / (2 * algebraMap K L a₂)
  let r₂ : L := (-algebraMap K L a₁ - s) / (2 * algebraMap K L a₂)
  refine ⟨2, a₂, ![r₁, r₂], ?_⟩
  have hf_eq : f =
      Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀ := by
    ext k
    rcases k with _ | _ | _ | k
    · simp [a₀]
    · simp [a₁]
    · simp [a₂]
    · have hgt : f.natDegree < k + 3 := by omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
  rw [hf_eq]
  simp only [GarlingSplitsExplicit, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hdenom : 2 * algebraMap K L a₂ ≠ 0 := mul_ne_zero h2L ha₂L
  have hsum : r₁ + r₂ = -(algebraMap K L a₁ / algebraMap K L a₂) := by
    dsimp [r₁, r₂]
    field_simp
    ring
  have hmul : r₁ * r₂ = algebraMap K L a₀ / algebraMap K L a₂ := by
    dsimp [r₁, r₂]
    apply mul_right_cancel₀ (pow_ne_zero 2 hdenom)
    have h1 : ((-algebraMap K L a₁ + s) / (2 * algebraMap K L a₂) *
        ((-algebraMap K L a₁ - s) / (2 * algebraMap K L a₂))) * (2 * algebraMap K L a₂) ^ 2 =
        (algebraMap K L a₁) ^ 2 - s ^ 2 := by
      field_simp
      ring
    rw [h1, hs_sq]
    simp only [d, map_sub, map_pow, map_mul, map_ofNat]
    field_simp
    ring
  have hprod : (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) =
      Polynomial.X ^ 2 + Polynomial.C (algebraMap K L a₁ / algebraMap K L a₂) * Polynomial.X +
        Polynomial.C (algebraMap K L a₀ / algebraMap K L a₂) := by
    calc (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)
        = Polynomial.X ^ 2 - Polynomial.C (r₁ + r₂) * Polynomial.X + Polynomial.C (r₁ * r₂) := by
            simp only [map_add, map_mul]; ring
      _ = _ := by rw [hsum, hmul, map_neg]; ring
  rw [hprod]
  have hc1 : Polynomial.C (algebraMap K L a₂) *
      Polynomial.C (algebraMap K L a₁ / algebraMap K L a₂) =
      Polynomial.C (algebraMap K L a₁) := by
    rw [← map_mul, mul_div_cancel₀ _ ha₂L]
  have hc0 : Polynomial.C (algebraMap K L a₂) *
      Polynomial.C (algebraMap K L a₀ / algebraMap K L a₂) =
      Polynomial.C (algebraMap K L a₀) := by
    rw [← map_mul, mul_div_cancel₀ _ ha₂L]
  linear_combination -(hc1 * Polynomial.X) - hc0

/-! ## §14.2 The discriminant (printed pp. 111–113, PDF pp. 119–121) -/

/-- Root-difference product `δ = ∏_{1 ≤ i < j ≤ n} (α_j - α_i)` for an `n`-tuple `α` (§14.2,
printed p. 111 / PDF p. 119).
*(OCR warning verified against 200 DPI scan p. 111 / PDF p. 119: `garling1986_pages.txt` corrupts
`δ = ∏_{1 ≤ i < j ≤ n} (α_j - α_i)` to `b = fl (oci - oci)`.)* -/
def garlingDeltaTuple {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (α j - α i)

/-- Tuple-level discriminant `Δ = δ²` (§14.2, printed p. 111 / PDF p. 119). -/
def garlingDiscTuple {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) : R :=
  (garlingDeltaTuple α) ^ 2

theorem garlingDeltaTuple_two {R : Type*} [CommRing R] (α : Fin 2 → R) :
    garlingDeltaTuple α = α 1 - α 0 := by
  unfold garlingDeltaTuple
  rw [Fin.prod_univ_two]
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]

theorem garlingDeltaTuple_three {R : Type*} [CommRing R] (α : Fin 3 → R) :
    garlingDeltaTuple α = (α 1 - α 0) * (α 2 - α 0) * (α 2 - α 1) := by
  unfold garlingDeltaTuple
  rw [Fin.prod_univ_three]
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  rw [h0, h1, h2, Finset.prod_pair (by decide), Finset.prod_singleton, Finset.prod_empty]
  ring

/-- Garling's transposed Vandermonde matrix on p. 112 (`(i, k)`-entry `α_k ^ i`, with top row
`1, 1, …, 1` and columns `α₁, …, α_n`). -/
def garlingVandermondeMatrix {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  (Matrix.vandermonde α)ᵀ

@[simp]
theorem garlingVandermondeMatrix_apply {R : Type*} [CommRing R] {n : ℕ}
    (α : Fin n → R) (i k : Fin n) :
    garlingVandermondeMatrix α i k = α k ^ (i : ℕ) :=
  rfl

/-- **Vandermonde determinant identity** (§14.2, printed p. 112 / PDF p. 120):
`δ` equals the determinant of the Vandermonde matrix `(α_k^{i-1})_{1 ≤ i, k ≤ n}`. -/
theorem garlingDeltaTuple_eq_det_vandermonde {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    garlingDeltaTuple α = (garlingVandermondeMatrix α).det ∧
    garlingDeltaTuple α = (Matrix.vandermonde α).det := by
  rw [garlingVandermondeMatrix, Matrix.det_transpose, Matrix.det_vandermonde]
  exact ⟨rfl, rfl⟩

/-- Compatibility of `garlingDeltaTuple` with any ring homomorphism. -/
theorem map_garlingDeltaTuple {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {n : ℕ} (α : Fin n → R) :
    φ (garlingDeltaTuple α) = garlingDeltaTuple (φ ∘ α) := by
  simp [garlingDeltaTuple, map_prod, map_sub]

/-- Compatibility of `garlingDiscTuple` with any ring homomorphism. -/
theorem map_garlingDiscTuple {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {n : ℕ} (α : Fin n → R) :
    φ (garlingDiscTuple α) = garlingDiscTuple (φ ∘ α) := by
  rw [garlingDiscTuple, garlingDiscTuple, map_pow, map_garlingDeltaTuple]

/-- Permutation sign law (§14.2, printed p. 111 / PDF p. 119): permuting the root labels by
`π ∈ Σ_n` multiplies `δ` by the sign `ε_π ∈ {1, -1}`. -/
theorem garlingDeltaTuple_comp_perm {R : Type*} [CommRing R] {n : ℕ}
    (α : Fin n → R) (π : SigmaN n) :
    garlingDeltaTuple (α ∘ π) = ((Equiv.Perm.sign π : ℤ) : R) * garlingDeltaTuple α := by
  rw [(garlingDeltaTuple_eq_det_vandermonde (α ∘ π)).2,
    (garlingDeltaTuple_eq_det_vandermonde α).2]
  have hsub : Matrix.vandermonde (α ∘ π) = (Matrix.vandermonde α).submatrix π id := by
    ext i j
    rfl
  rw [hsub, Matrix.det_permute]

/-- Permutation invariance of `Δ = δ²` (§14.2, printed p. 111: *"although `δ` depends on the order
in which we label the roots of `f`, `Δ` does not"*). -/
theorem garlingDiscTuple_comp_perm {R : Type*} [CommRing R] {n : ℕ}
    (α : Fin n → R) (π : SigmaN n) :
    garlingDiscTuple (α ∘ π) = garlingDiscTuple α := by
  rw [garlingDiscTuple, garlingDeltaTuple_comp_perm, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | hm1
  · simp [h1, garlingDiscTuple]
  · simp [hm1, garlingDiscTuple]

/-- Over an integral domain, `δ = 0` iff the root tuple has a repeated entry (`i ≠ j` with
`α_i = α_j`). -/
theorem garlingDeltaTuple_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (α : Fin n → R) :
    garlingDeltaTuple α = 0 ↔ ¬ Function.Injective α := by
  rw [(garlingDeltaTuple_eq_det_vandermonde α).2, Matrix.det_vandermonde_eq_zero_iff]
  unfold Function.Injective
  push Not
  rfl

/-- Elementary inductive uniqueness of linear factorizations over an integral domain: if
`∏ i : Fin n, (X - C (α₁ i)) = ∏ i : Fin n, (X - C (α₂ i))`, then `α₂ = α₁ ∘ π` for some
permutation `π ∈ Σ_n`. -/
theorem prod_X_sub_C_eq_imp_perm {R : Type*} [CommRing R] [IsDomain R] :
    ∀ {n : ℕ} {α₁ α₂ : Fin n → R},
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (α₁ i))) =
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (α₂ i))) →
      ∃ π : SigmaN n, α₂ = α₁ ∘ π
  | 0, α₁, α₂, _ => ⟨1, funext fun x => Fin.elim0 x⟩
  | n + 1, α₁, α₂, hprod => by
    have heval := congrArg (Polynomial.eval (α₂ 0)) hprod
    rw [Polynomial.eval_prod, Polynomial.eval_prod, Fin.prod_univ_succ (f := fun i =>
      Polynomial.eval (α₂ 0) (Polynomial.X - Polynomial.C (α₂ i)))] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
      zero_mul] at heval
    obtain ⟨i₀, _, hi₀⟩ := Finset.prod_eq_zero_iff.mp heval
    have hα_eq : α₁ i₀ = α₂ 0 := (sub_eq_zero.mp hi₀).symm
    let β₁ : Fin (n + 1) → R := α₁ ∘ Equiv.swap 0 i₀
    have hβ0 : β₁ 0 = α₂ 0 := by simp [β₁, hα_eq]
    have hprod_β : (∏ k : Fin (n + 1), (Polynomial.X - Polynomial.C (β₁ k))) =
        (∏ k : Fin (n + 1), (Polynomial.X - Polynomial.C (α₂ k))) := by
      have hswap := Equiv.Perm.prod_comp (Equiv.swap (0 : Fin (n + 1)) i₀) Finset.univ
        (fun k => Polynomial.X - Polynomial.C (α₁ k)) (by simp)
      exact hswap.trans hprod
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, hβ0] at hprod_β
    have htail := mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (α₂ 0)) hprod_β
    obtain ⟨τ, hτ⟩ := prod_X_sub_C_eq_imp_perm htail
    let τ_ext : SigmaN (n + 1) :=
      { toFun := Fin.cases 0 (fun k => (τ k).succ)
        invFun := Fin.cases 0 (fun k => (τ.symm k).succ)
        left_inv := fun k => Fin.cases rfl (fun j => by simp) k
        right_inv := fun k => Fin.cases rfl (fun j => by simp) k }
    refine ⟨(Equiv.swap 0 i₀) * τ_ext, ?_⟩
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · change α₂ 0 = β₁ (τ_ext 0)
      simp [τ_ext, hβ0]
    · change α₂ j.succ = β₁ (τ_ext j.succ)
      have hj := congrFun hτ j
      simpa [τ_ext] using hj

/-- Any two explicit splitting factorizations `f = c₁ ∏ (x - α₁_i) = c₂ ∏ (x - α₂_i)` of a
non-zero polynomial `f ∈ K[x]` over a field extension `L : K` differ by a permutation of the root
tuple. -/
theorem garlingSplitsExplicit_perm_of_ne_zero {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    {n : ℕ} {c₁ c₂ : K} {α₁ α₂ : Fin n → L}
    (h₁ : GarlingSplitsExplicit K L f n c₁ α₁) (h₂ : GarlingSplitsExplicit K L f n c₂ α₂) :
    ∃ π : SigmaN n, α₂ = α₁ ∘ π := by
  have hc₁ : c₁ = f.leadingCoeff := (garlingSplitsExplicit_props hf0 h₁).1
  have hc₂ : c₂ = f.leadingCoeff := (garlingSplitsExplicit_props hf0 h₂).1
  have hc_ne : algebraMap K L f.leadingCoeff ≠ 0 :=
    (map_ne_zero (algebraMap K L)).mpr (Polynomial.leadingCoeff_ne_zero.mpr hf0)
  have hprod_eq : (∏ i : Fin n, (Polynomial.X - Polynomial.C (α₁ i))) =
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (α₂ i))) := by
    have heq := h₁.symm.trans h₂
    rw [hc₁, hc₂] at heq
    exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hc_ne) heq
  exact prod_X_sub_C_eq_imp_perm hprod_eq

/-- At `f = 0`, §7.1's `GarlingSplitsExplicit` allows `0 = 0 · (x - α₁)⋯(x - α_n)` for arbitrary
tuples `α`, yielding conflicting values of `∏_{i<j} (α_j - α_i)²` (e.g. `1` vs. `0` over `ℚ`). -/
theorem garlingDisc_zero_not_unique_of_splitsExplicit :
    GarlingSplitsExplicit ℚ ℚ 0 2 0 ![0, 1] ∧
    GarlingSplitsExplicit ℚ ℚ 0 2 0 ![0, 0] ∧
    garlingDiscTuple (![0, 1] : Fin 2 → ℚ) = 1 ∧
    garlingDiscTuple (![0, 0] : Fin 2 → ℚ) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [GarlingSplitsExplicit]
  · simp [GarlingSplitsExplicit]
  · rw [garlingDiscTuple, garlingDeltaTuple_two]; norm_num
  · rw [garlingDiscTuple, garlingDeltaTuple_two]; norm_num

/-- For any non-zero `f ∈ K[x]` and explicit splitting `f = c ∏ (x - α_i)` over `L : K`, injectivity
of `α` is equivalent to Mathlib's `f.Separable`, and negation of injectivity is equivalent to
`HasGarlingRepeatedRoot K L f`. -/
theorem injective_roots_iff_separable_and_not_repeated {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    {n : ℕ} {c : K} {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n c α) :
    (Function.Injective α ↔ f.Separable) ∧
    (¬ Function.Injective α ↔ HasGarlingRepeatedRoot K L f) := by
  have hc_ne : algebraMap K L c ≠ 0 :=
    (map_ne_zero (algebraMap K L)).mpr (garlingSplitsExplicit_props hf0 hexp).2.1
  have hass : Associated (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
      (f.map (algebraMap K L)) := by
    refine ⟨Units.map Polynomial.C.toMonoidHom (Units.mk0 (algebraMap K L c) hc_ne), ?_⟩
    rw [hexp, mul_comm]
    rfl
  have hsep_iff : Function.Injective α ↔ f.Separable := by
    rw [← Polynomial.separable_map (algebraMap K L), ← hass.separable_iff,
      Polynomial.separable_prod_X_sub_C_iff']
    simp [Function.Injective]
  have hrep_iff : ¬ Function.Injective α ↔ HasGarlingRepeatedRoot K L f := by
    constructor
    · intro hninj
      unfold Function.Injective at hninj
      push Not at hninj
      obtain ⟨i, j, heq, hij⟩ := hninj
      refine ⟨α i, 2, by decide, ?_⟩
      rw [hexp]
      refine dvd_mul_of_dvd_right ?_ _
      have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      have hprod_sub := Finset.prod_dvd_prod_of_subset _ _
        (fun k : Fin n => Polynomial.X - Polynomial.C (α k)) hsub
      rw [Finset.prod_pair hij, ← heq, ← sq] at hprod_sub
      exact hprod_sub
    · rintro ⟨r, k, hk, hdvd⟩ hinj
      have hsq : Squarefree (f.map (algebraMap K L)) :=
        ((Polynomial.separable_map (algebraMap K L)).mpr (hsep_iff.mp hinj)).squarefree
      have hk2 : 2 ≤ k := hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
      rw [pow_add, sq] at hdvd
      have hdvd2 : (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C r) ∣
          f.map (algebraMap K L) := dvd_of_mul_right_dvd hdvd
      exact Polynomial.not_isUnit_X_sub_C r (hsq (Polynomial.X - Polynomial.C r) hdvd2)
  exact ⟨hsep_iff, hrep_iff⟩

/-- For any non-zero `f ∈ K[x]` and splitting field extension `L : K` of `f` with explicit
factorization `f = c ∏_{i=1}^n (x - α_i)`, `garlingDiscTuple α` lies in `K`
(`Set.range (algebraMap K L)`), across **all** characteristics (including `char K = 2` and imperfect
fields). -/
theorem garlingDiscTuple_mem_base_of_splittingField {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    {n : ℕ} {c : K} {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n c α) :
    garlingDiscTuple α ∈ Set.range (algebraMap K L) := by
  by_cases hinj : Function.Injective α
  · have hf_sep : f.Separable := (injective_roots_iff_separable_and_not_repeated hf0 hexp).1.mp hinj
    have hgar_sep : IsGarlingSeparablePoly f :=
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
    have hfixed : (algebraMap K L).fieldRange =
        garlingPhi (garlingPolyGaloisSubgroup K L f : Set (GarlingAut L)) :=
      (theorem_11_5 hf0 hsf).1 hgar_sep |>.2.2
    change garlingDiscTuple α ∈ ((algebraMap K L).fieldRange : Set L)
    rw [hfixed]
    intro τ hτ
    let σ : GarlingPolyGaloisGroup K L f := (garlingGaloisGroupMulEquiv K L).symm ⟨τ, hτ⟩
    have hexp_σ : GarlingSplitsExplicit K L f n c (σ ∘ α) := by
      have hmap : (f.map (algebraMap K L)).map σ.toRingHom = f.map (algebraMap K L) := by
        rw [Polynomial.map_map]
        congr 1
        ext k
        exact σ.commutes k
      have h1 := congrArg (Polynomial.map σ.toRingHom) hexp
      rw [hmap, Polynomial.map_mul, Polynomial.map_C] at h1
      have hc_comm : σ.toRingHom (algebraMap K L c) = algebraMap K L c := σ.commutes c
      rw [hc_comm, Polynomial.map_prod] at h1
      simpa [GarlingSplitsExplicit] using h1
    obtain ⟨π, hπ⟩ := garlingSplitsExplicit_perm_of_ne_zero hf0 hexp hexp_σ
    change σ.toRingHom (garlingDiscTuple α) = garlingDiscTuple α
    have hcomp_σ : (σ.toRingHom ∘ α) = α ∘ π := hπ
    rw [map_garlingDiscTuple σ.toRingHom α, hcomp_σ, garlingDiscTuple_comp_perm]
  · have h0 : garlingDeltaTuple α = 0 := (garlingDeltaTuple_eq_zero_iff α).mpr hinj
    refine ⟨0, ?_⟩
    simp [garlingDiscTuple, h0]

/-- Garling's prose definition of the *discriminant* `Δ = δ²` of a polynomial `f ∈ K[x]` (§14.2,
printed p. 111 / PDF p. 119):
for `f ≠ 0`, `Δ ∈ K` is the unique element whose image in every splitting field extension `L : K` of
`f` equals `δ² = ∏_{1 ≤ i < j ≤ n} (α_j - α_i)²` for the roots `α₁, …, α_n` of `f` counted with
multiplicity (`garlingDiscriminant_eq_discTuple`); at `f = 0`, `garlingDiscriminant 0 = 0` (matching
`HasGarlingRepeatedRoot K L 0`). -/
noncomputable def garlingDiscriminant {K : Type u} [Field K] (f : K[X]) : K :=
  if hf0 : f = 0 then 0
  else
    let L₀ := Polynomial.SplittingField f
    have hsf₀ : IsGarlingSplittingFieldExtension K L₀ f :=
      (isGarlingSplittingFieldExtension_iff K L₀ f).mpr inferInstance
    let n₀ := Classical.choose hsf₀.1
    let c₀ := Classical.choose (Classical.choose_spec hsf₀.1)
    let α₀ := Classical.choose (Classical.choose_spec (Classical.choose_spec hsf₀.1))
    have hexp₀ : GarlingSplitsExplicit K L₀ f n₀ c₀ α₀ :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hsf₀.1))
    Classical.choose (garlingDiscTuple_mem_base_of_splittingField hf0 hsf₀ hexp₀)

@[simp]
theorem garlingDiscriminant_zero {K : Type u} [Field K] :
    garlingDiscriminant (0 : K[X]) = 0 := by
  simp [garlingDiscriminant]

/-- Universal specification of `garlingDiscriminant`: for **every** non-zero `f ∈ K[x]`, **every**
field extension `L : K` over which `f` splits as `f = c ∏_{i=1}^n (x - α_i)` (whether or not `L` is
minimal), `algebraMap K L (garlingDiscriminant f) = ∏_{1 ≤ i < j ≤ n} (α_j - α_i)²`. -/
theorem garlingDiscriminant_eq_discTuple {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    {n : ℕ} {c : K} {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n c α) :
    algebraMap K L (garlingDiscriminant f) = garlingDiscTuple α := by
  let L₀ := Polynomial.SplittingField f
  have hsf₀ : IsGarlingSplittingFieldExtension K L₀ f :=
    (isGarlingSplittingFieldExtension_iff K L₀ f).mpr inferInstance
  let n₀ := Classical.choose hsf₀.1
  let c₀ := Classical.choose (Classical.choose_spec hsf₀.1)
  let α₀ := Classical.choose (Classical.choose_spec (Classical.choose_spec hsf₀.1))
  have hexp₀ : GarlingSplitsExplicit K L₀ f n₀ c₀ α₀ :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hsf₀.1))
  have hd_spec : algebraMap K L₀ (garlingDiscriminant f) = garlingDiscTuple α₀ := by
    simp only [garlingDiscriminant, hf0, ↓reduceDIte]
    exact Classical.choose_spec (garlingDiscTuple_mem_base_of_splittingField hf0 hsf₀ hexp₀)
  let E : IntermediateField K L := IntermediateField.adjoin K (Set.range α)
  have hsfE : IsGarlingSplittingFieldExtension K E f := theorem_7_1 hf0 hexp
  let αE : Fin n → E := fun i => ⟨α i, IntermediateField.subset_adjoin K (Set.range α) ⟨i, rfl⟩⟩
  have hexpE : GarlingSplitsExplicit K E f n c αE := by
    have hinjE : Function.Injective (Polynomial.mapRingHom E.val.toRingHom) :=
      Polynomial.map_injective _ E.val.injective
    apply hinjE
    change (f.map (algebraMap K E)).map E.val.toRingHom = _
    rw [Polynomial.map_map]
    have hcomp : E.val.toRingHom.comp (algebraMap K E) = algebraMap K L := rfl
    rw [hcomp, hexp]
    simp [Polynomial.map_mul, Polynomial.map_prod, αE]
  obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf₀ hsfE
  have hn₀ : n₀ = garlingDegree f hf0 := (garlingSplitsExplicit_props hf0 hexp₀).2.2.1
  have hn : n = garlingDegree f hf0 := (garlingSplitsExplicit_props hf0 hexp).2.2.1
  have hnn : n₀ = n := hn₀.trans hn.symm
  subst hnn
  have hexp_push : GarlingSplitsExplicit K E f n₀ c₀ (e ∘ α₀) := by
    have h1 := congrArg (Polynomial.map e.toRingHom) hexp₀
    have hmap : (f.map (algebraMap K L₀)).map e.toRingHom = f.map (algebraMap K E) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun k => e.commutes k
    rw [hmap, Polynomial.map_mul, Polynomial.map_C] at h1
    have hc_comm : e.toRingHom (algebraMap K L₀ c₀) = algebraMap K E c₀ := e.commutes c₀
    rw [hc_comm, Polynomial.map_prod] at h1
    simpa [GarlingSplitsExplicit] using h1
  obtain ⟨π, hπ⟩ := garlingSplitsExplicit_perm_of_ne_zero hf0 hexp_push hexpE
  have hdiscE : algebraMap K E (garlingDiscriminant f) = garlingDiscTuple αE := by
    calc algebraMap K E (garlingDiscriminant f)
        = e (algebraMap K L₀ (garlingDiscriminant f)) := (e.commutes _).symm
      _ = e (garlingDiscTuple α₀) := by rw [hd_spec]
      _ = garlingDiscTuple (e ∘ α₀) := map_garlingDiscTuple e.toRingHom α₀
      _ = garlingDiscTuple αE := by rw [hπ, garlingDiscTuple_comp_perm]
  have hval := congrArg E.val.toRingHom hdiscE
  rw [map_garlingDiscTuple E.val.toRingHom αE] at hval
  exact hval

/-- Discriminant of any polynomial of degree `≤ 1` (`f ≠ 0`, `natDegree f ≤ 1`) is `1`. -/
theorem garlingDiscriminant_of_natDegree_le_one {K : Type u} [Field K] {f : K[X]}
    (hf0 : f ≠ 0) (hle : f.natDegree ≤ 1) :
    garlingDiscriminant f = 1 := by
  let L := Polynomial.SplittingField f
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hn : n ≤ 1 := by
    have h1 := (garlingSplitsExplicit_props hf0 hexp).2.2.1
    rw [garlingDegree] at h1
    omega
  apply (algebraMap K L).injective
  rw [garlingDiscriminant_eq_discTuple hf0 hexp, map_one, garlingDiscTuple, garlingDeltaTuple]
  have hprod1 : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (α j - α i)) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j hj => ?_
    have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
    omega
  rw [hprod1, one_pow]

/-- Unconditional repeated-root characterization across **all** `f ∈ K[x]` (including `f = 0`):
`garlingDiscriminant f = 0 ↔ HasGarlingRepeatedRoot K L f` in any splitting field extension `L : K`
of `f` (in every characteristic). -/
theorem garlingDiscriminant_eq_zero_iff_hasGarlingRepeatedRoot {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (f : K[X])
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    garlingDiscriminant f = 0 ↔ HasGarlingRepeatedRoot K L f := by
  by_cases hf0 : f = 0
  · subst hf0
    simp only [garlingDiscriminant_zero, true_iff]
    exact ⟨0, 2, by decide, by simp⟩
  · obtain ⟨n, c, α, hexp⟩ := hsf.1
    rw [← (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective),
      garlingDiscriminant_eq_discTuple hf0 hexp, garlingDiscTuple, sq_eq_zero_iff,
      garlingDeltaTuple_eq_zero_iff,
      (injective_roots_iff_separable_and_not_repeated hf0 hexp).2]

/-- Induced permutation action `Γ_K(f) →* Σ_n` determined by a root-labelling bijection
`e : Fin n ≃ garlingRootSet K L f` (§14.2, p. 111). -/
def garlingRootLabellingPermHom {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (e : Fin n ≃ garlingRootSet K L f) :
    GarlingPolyGaloisGroup K L f →* SigmaN n where
  toFun σ := e.trans ((garlingRootPermHom K L f σ).trans e.symm)
  map_one' := by
    ext i
    simp [Equiv.Perm.one_def]
  map_mul' σ₁ σ₂ := by
    ext i
    simp [Equiv.Perm.mul_apply]

@[simp]
theorem garlingRootLabellingPermHom_apply {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ}
    (e : Fin n ≃ garlingRootSet K L f) (σ : GarlingPolyGaloisGroup K L f) (i : Fin n) :
    (e (garlingRootLabellingPermHom e σ i) : L) = σ (e i : L) := by
  simp [garlingRootLabellingPermHom]

/-- Key Galois sign equation on `δ = ∏_{i < j} (α_j - α_i)` (§14.2, printed p. 111, l. 12:
`σ(δ) = ∏_{1 ≤ i < j ≤ n} (σ(α_j) - σ(α_i)) = ε_σ δ`). -/
theorem galois_apply_garlingDeltaTuple {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ}
    (e : Fin n ≃ garlingRootSet K L f) (σ : GarlingPolyGaloisGroup K L f) :
    σ (garlingDeltaTuple (fun i : Fin n => (e i : L))) =
      ((Equiv.Perm.sign (garlingRootLabellingPermHom e σ) : ℤ) : L) *
        garlingDeltaTuple (fun i : Fin n => (e i : L)) := by
  have hcomp : (fun i : Fin n => σ (e i : L)) =
      (fun i : Fin n => (e i : L)) ∘ garlingRootLabellingPermHom e σ := by
    funext i
    exact (garlingRootLabellingPermHom_apply e σ i).symm
  calc σ (garlingDeltaTuple (fun i : Fin n => (e i : L)))
      = garlingDeltaTuple (fun i : Fin n => σ (e i : L)) :=
          map_garlingDeltaTuple σ.toRingHom _
    _ = _ := by rw [hcomp, garlingDeltaTuple_comp_perm]

/-- Subgroup `Γ_K(f) ∩ A_n` inside `Γ_K(f)` via `garlingRootLabellingPermHom e` (independent of
the root labelling `e` because `A_n ◁ Σ_n` is the kernel of `Equiv.Perm.sign`, see
`garlingEvenGaloisSubgroup_indep`). -/
def garlingEvenGaloisSubgroup {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (e : Fin n ≃ garlingRootSet K L f) :
    Subgroup (GarlingPolyGaloisGroup K L f) :=
  (alternatingGroup (Fin n)).comap (garlingRootLabellingPermHom e)

@[simp]
theorem mem_garlingEvenGaloisSubgroup_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ}
    (e : Fin n ≃ garlingRootSet K L f) (σ : GarlingPolyGaloisGroup K L f) :
    σ ∈ garlingEvenGaloisSubgroup e ↔
      garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin n) :=
  Iff.rfl

/-- Independence of `Γ_K(f) ∩ A_n` from the choice of root labelling `e₁, e₂`. -/
theorem garlingEvenGaloisSubgroup_indep {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ}
    (e₁ e₂ : Fin n ≃ garlingRootSet K L f) :
    garlingEvenGaloisSubgroup e₁ = garlingEvenGaloisSubgroup e₂ := by
  ext σ
  simp only [mem_garlingEvenGaloisSubgroup_iff, Equiv.Perm.mem_alternatingGroup]
  let τ : SigmaN n := e₁.trans e₂.symm
  have hconj : garlingRootLabellingPermHom e₂ σ =
      τ * garlingRootLabellingPermHom e₁ σ * τ⁻¹ := by
    ext i
    simp [garlingRootLabellingPermHom, τ, Equiv.Perm.mul_apply]
  rw [hconj, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

/-- **Theorem 14.1** (§14.2, printed p. 111 / PDF p. 119):
*"Suppose that `char K ≠ 2` and that `f ∈ K[x]`. Let `Δ` be the discriminant of `f ∈ K[x]`, and let
`L : K` be a splitting field extension for `f`.
(i) If `Δ = 0`, `f` has a repeated root in `L`.
(ii) If `Δ ≠ 0` and `Δ` has a square root in `K`, then `Γ_K(f) ⊆ A_n`.
(iii) If `Δ` has no square root in `K`, it has a square root `δ` in `L`. `Γ_K(f) ⊄ A_n`, and
`K(δ)` is the fixed field of `Γ_K(f) ∩ A_n`."*

Proved literally for **all** `f ∈ K[x]` (including `f = 0` and degenerate degrees `n = 0, 1`, with
`n = f.natDegree`), across every root-labelling bijection `e : Fin n ≃ garlingRootSet K L f` (whose
existence `Nonempty (Fin n ≃ garlingRootSet K L f)` is also proved whenever `Δ ≠ 0`). -/
theorem theorem_14_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hchar : ringChar K ≠ 2) (f : K[X]) (hsf : IsGarlingSplittingFieldExtension K L f) :
    let Δ : K := garlingDiscriminant f
    let n : ℕ := f.natDegree
    -- (i) If `Δ = 0`, `f` has a repeated root in `L` (in fact `Δ = 0 ↔ repeated root`)
    (Δ = 0 → HasGarlingRepeatedRoot K L f) ∧
    -- (ii) If `Δ ≠ 0` and `Δ` has a square root in `K`, then `Γ_K(f) ⊆ A_n`
    (Δ ≠ 0 → (∃ d : K, d ^ 2 = Δ) →
      Nonempty (Fin n ≃ garlingRootSet K L f) ∧
      ∀ (e : Fin n ≃ garlingRootSet K L f) (σ : GarlingPolyGaloisGroup K L f),
        garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin n)) ∧
    -- (iii) If `Δ` has no square root in `K`, it has a square root `δ` in `L`, `Γ_K(f) ⊄ A_n`,
    -- and `K(δ)` is the fixed field of `Γ_K(f) ∩ A_n` (and `[K(δ) : K] = 2`)
    ((¬ ∃ d : K, d ^ 2 = Δ) →
      Nonempty (Fin n ≃ garlingRootSet K L f) ∧
      ∃ δ : L,
        δ ^ 2 = algebraMap K L Δ ∧
        Module.finrank K (IntermediateField.adjoin K ({δ} : Set L)) = 2 ∧
        ∀ e : Fin n ≃ garlingRootSet K L f,
          (¬ ∀ σ : GarlingPolyGaloisGroup K L f,
              garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin n)) ∧
          IntermediateField.adjoin K ({δ} : Set L) =
            IntermediateField.fixedField (garlingEvenGaloisSubgroup e)) := by
  intro Δ n
  have h2K : (2 : K) ≠ 0 := natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar
  have h2L : (2 : L) ≠ 0 := by
    have hm : algebraMap K L (2 : K) = (2 : L) := map_ofNat (algebraMap K L) 2
    rw [← hm]
    exact (map_ne_zero (algebraMap K L)).mpr h2K
  have h_one_ne_neg_one : (1 : L) ≠ -1 := by
    intro h1
    apply h2L
    linear_combination h1
  -- Helper when `Δ ≠ 0`: `f ≠ 0`, `f.Separable`, `L : K` Galois, and `Fin n ≃ garlingRootSet K L f`
  have h_of_disc_ne_zero : Δ ≠ 0 →
      ∃ (hf0 : f ≠ 0) (c : K) (α : Fin n → L),
        GarlingSplitsExplicit K L f n c α ∧
        Function.Injective α ∧
        f.Separable ∧
        IsGarlingGaloisExtension K L ∧
        ∃ e : Fin n ≃ garlingRootSet K L f, ∀ i : Fin n, (e i : L) = α i := by
    intro hΔ0
    have hf0 : f ≠ 0 := fun h => hΔ0 (by simp [Δ, h])
    obtain ⟨m, c, α', hexp'⟩ := hsf.1
    have hm : m = n := by
      have h1 := (garlingSplitsExplicit_props hf0 hexp').2.2.1
      simpa [garlingDegree, n] using h1
    subst hm
    have hdisc_eq : algebraMap K L Δ = garlingDiscTuple α' :=
      garlingDiscriminant_eq_discTuple hf0 hexp'
    have hδ0 : garlingDeltaTuple α' ≠ 0 := by
      intro h0
      apply hΔ0
      apply (algebraMap K L).injective
      rw [hdisc_eq, garlingDiscTuple, h0, zero_pow (by decide), map_zero]
    have hinj : Function.Injective α' := by
      by_contra hninj
      exact hδ0 ((garlingDeltaTuple_eq_zero_iff α').mpr hninj)
    have hf_sep : f.Separable :=
      (injective_roots_iff_separable_and_not_repeated hf0 hexp').1.mp hinj
    have hgar_sep : IsGarlingSeparablePoly f :=
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
    have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨f, hsf⟩
    have hsepL : IsGarlingSeparableExtension K L :=
      (isGarlingSeparableExtension_iff_poly_of_splittingField hf0 hsf).mpr hgar_sep
    have hgal : IsGarlingGaloisExtension K L := ⟨hfin, hnorm, hsepL⟩
    have hrange : Set.range α' = garlingRootSet K L f := by
      rw [garlingRootSet_eq_rootSet hf0]
      exact (garlingSplitsExplicit_props hf0 hexp').2.2.2
    let e_set : Set.range α' ≃ garlingRootSet K L f :=
      { toFun := fun x => ⟨x.1, hrange ▸ x.2⟩
        invFun := fun y => ⟨y.1, hrange.symm ▸ y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e : Fin n ≃ garlingRootSet K L f :=
      (Equiv.ofInjective α' hinj).trans e_set
    exact ⟨hf0, c, α', hexp', hinj, hf_sep, hgal, e, fun _ => rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Part (i)
    exact (garlingDiscriminant_eq_zero_iff_hasGarlingRepeatedRoot f hsf).mp
  · -- Part (ii)
    intro hΔ0 ⟨d, hd⟩
    obtain ⟨hf0, c, α, hexp, _, _, _, e₀, _⟩ := h_of_disc_ne_zero hΔ0
    refine ⟨⟨e₀⟩, fun e σ => ?_⟩
    let β : Fin n → L := fun i => (e i : L)
    have hβ_inj : Function.Injective β := fun i j hij => e.injective (Subtype.ext hij)
    have hperm_αβ : ∃ π : SigmaN n, β = α ∘ π := by
      have hsurj : ∀ i : Fin n, ∃ k : Fin n, α k = β i := by
        intro i
        have hmem : β i ∈ Set.range α := by
          rw [(garlingSplitsExplicit_props hf0 hexp).2.2.2, ← garlingRootSet_eq_rootSet hf0]
          exact (e i).2
        exact hmem
      choose π hπ using hsurj
      have hπ_inj : Function.Injective π := fun i j hij =>
        hβ_inj (by rw [← hπ i, ← hπ j, hij])
      exact ⟨Equiv.ofBijective π ((Finite.injective_iff_bijective).mp hπ_inj),
        funext fun i => (hπ i).symm⟩
    obtain ⟨π, hπ⟩ := hperm_αβ
    let δ := garlingDeltaTuple β
    have hδ_sq : δ ^ 2 = algebraMap K L Δ := by
      change garlingDiscTuple β = algebraMap K L Δ
      rw [hπ, garlingDiscTuple_comp_perm, ← garlingDiscriminant_eq_discTuple hf0 hexp]
    have hδ_ne0 : δ ≠ 0 := by
      intro h0
      apply hΔ0
      apply (algebraMap K L).injective
      rw [← hδ_sq, h0, zero_pow (by decide), map_zero]
    have hδ_mem : δ ∈ Set.range (algebraMap K L) := by
      have hmul0 : (δ - algebraMap K L d) * (δ + algebraMap K L d) = 0 := by
        calc (δ - algebraMap K L d) * (δ + algebraMap K L d)
            = δ ^ 2 - (algebraMap K L d) ^ 2 := by ring
          _ = algebraMap K L Δ - algebraMap K L (d ^ 2) := by rw [hδ_sq, map_pow]
          _ = 0 := by rw [hd, sub_self]
      rcases mul_eq_zero.mp hmul0 with hpos | hneg
      · exact ⟨d, (sub_eq_zero.mp hpos).symm⟩
      · exact ⟨-d, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hneg).symm⟩
    rcases hδ_mem with ⟨k, hk⟩
    have hσδ : σ δ = δ := by rw [← hk, σ.commutes k]
    have hsign_eq := galois_apply_garlingDeltaTuple e σ
    change σ δ = ((Equiv.Perm.sign (garlingRootLabellingPermHom e σ) : ℤ) : L) * δ at hsign_eq
    rw [hσδ] at hsign_eq
    rw [Equiv.Perm.mem_alternatingGroup]
    by_contra hne1
    rcases Int.units_eq_one_or (Equiv.Perm.sign (garlingRootLabellingPermHom e σ)) with h1 | hm1
    · exact hne1 h1
    · rw [hm1] at hsign_eq
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at hsign_eq
      exact h_one_ne_neg_one (mul_right_cancel₀ hδ_ne0 (by rw [one_mul]; exact hsign_eq))
  · -- Part (iii)
    intro hno_sq
    have hΔ0 : Δ ≠ 0 := fun h0 => hno_sq ⟨0, by rw [h0, zero_pow (by decide)]⟩
    obtain ⟨hf0, c, α, hexp, hinj, _, hgal, e₀, he₀⟩ := h_of_disc_ne_zero hΔ0
    have _ : IsGalois K L := (isGarlingGaloisExtension_iff K L).mp hgal |>.2
    have _ : FiniteDimensional K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
    let δ : L := garlingDeltaTuple α
    have hδ_sq : δ ^ 2 = algebraMap K L Δ :=
      (garlingDiscriminant_eq_discTuple hf0 hexp).symm
    have hδ_ne0 : δ ≠ 0 := fun h0 => (garlingDeltaTuple_eq_zero_iff α).mp h0 hinj
    have hδ_not_K : δ ∉ (⊥ : IntermediateField K L) := by
      intro hbot
      rcases IntermediateField.mem_bot.mp hbot with ⟨d, hd⟩
      apply hno_sq
      refine ⟨d, (algebraMap K L).injective ?_⟩
      rw [map_pow, hd, hδ_sq]
    have hfin2 : Module.finrank K (IntermediateField.adjoin K ({δ} : Set L)) = 2 := by
      let p : K[X] := Polynomial.X ^ 2 - Polynomial.C Δ
      have hp_mon : p.Monic := Polynomial.monic_X_pow_sub_C Δ (by decide)
      have hp_deg : p.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
      have hp_aeval : Polynomial.aeval δ p = 0 := by simp [p, hδ_sq]
      have hp_irr : Irreducible p := by
        have hnoroot : ∀ x : K, p.eval x ≠ 0 := by
          intro x hx
          simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero] at hx
          exact hno_sq ⟨x, hx⟩
        have hp_nu : ¬ IsUnit p := Polynomial.not_isUnit_of_natDegree_pos p (by omega)
        refine ⟨hp_nu, fun g h hgh => ?_⟩
        by_contra hboth
        push Not at hboth
        obtain ⟨hg_nu, hh_nu⟩ := hboth
        have hg0 : g ≠ 0 := fun h0 => hp_mon.ne_zero (by rw [hgh, h0, zero_mul])
        have hh0 : h ≠ 0 := fun h0 => hp_mon.ne_zero (by rw [hgh, h0, mul_zero])
        have hg_pos : 0 < g.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_ne_zero_of_nonunit hg0 hg_nu)
        have hh_pos : 0 < h.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_ne_zero_of_nonunit hh0 hh_nu)
        have hdeg_sum : g.natDegree + h.natDegree = 2 := by
          rw [← Polynomial.natDegree_mul hg0 hh0, ← hgh, hp_deg]
        have hg1 : g.natDegree = 1 := by omega
        obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one
          (Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide) |>.mpr hg1)
        exact hnoroot r (by rw [hgh, Polynomial.eval_mul, hr, zero_mul])
      have hmin : minpoly K δ = p :=
        (minpoly.eq_of_irreducible_of_monic hp_irr hp_aeval hp_mon).symm
      rw [IntermediateField.adjoin.finrank ⟨p, hp_mon, hp_aeval⟩, hmin, hp_deg]
    refine ⟨⟨e₀⟩, δ, hδ_sq, hfin2, fun e => ?_⟩
    let β : Fin n → L := fun i => (e i : L)
    have hβ_inj : Function.Injective β := fun i j hij => e.injective (Subtype.ext hij)
    have hperm_αβ : ∃ π : SigmaN n, β = α ∘ π := by
      have hsurj : ∀ i : Fin n, ∃ k : Fin n, α k = β i := by
        intro i
        have hmem : β i ∈ Set.range α := by
          rw [(garlingSplitsExplicit_props hf0 hexp).2.2.2, ← garlingRootSet_eq_rootSet hf0]
          exact (e i).2
        exact hmem
      choose π hπ using hsurj
      have hπ_inj : Function.Injective π := fun i j hij =>
        hβ_inj (by rw [← hπ i, ← hπ j, hij])
      exact ⟨Equiv.ofBijective π ((Finite.injective_iff_bijective).mp hπ_inj),
        funext fun i => (hπ i).symm⟩
    obtain ⟨π, hπ⟩ := hperm_αβ
    let δ_e : L := garlingDeltaTuple β
    have hδe_pm : δ_e = δ ∨ δ_e = -δ := by
      dsimp [δ_e, δ]
      rw [hπ, garlingDeltaTuple_comp_perm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | hm1
      · left; simp [h1]
      · right; simp [hm1]
    have hadj_eq : IntermediateField.adjoin K ({δ} : Set L) =
        IntermediateField.adjoin K ({δ_e} : Set L) := by
      rcases hδe_pm with heq | hneg
      · rw [heq]
      · rw [hneg]
        apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        · simpa using neg_mem (IntermediateField.mem_adjoin_simple_self K (-δ))
        · exact neg_mem (IntermediateField.mem_adjoin_simple_self K δ)
    have hfixing_eq : (IntermediateField.adjoin K ({δ} : Set L)).fixingSubgroup =
        garlingEvenGaloisSubgroup e := by
      rw [hadj_eq]
      ext σ
      rw [IntermediateField.mem_fixingSubgroup_iff, mem_garlingEvenGaloisSubgroup_iff,
        Equiv.Perm.mem_alternatingGroup]
      have hsign_eq := galois_apply_garlingDeltaTuple e σ
      change σ δ_e = ((Equiv.Perm.sign (garlingRootLabellingPermHom e σ) : ℤ) : L) * δ_e at hsign_eq
      have hδe_ne0 : δ_e ≠ 0 := by
        rcases hδe_pm with heq | hneg
        · rw [heq]; exact hδ_ne0
        · rw [hneg]; exact neg_ne_zero.mpr hδ_ne0
      constructor
      · intro hfix
        have hσδe : σ δ_e = δ_e := hfix δ_e (IntermediateField.mem_adjoin_simple_self K δ_e)
        rw [hσδe] at hsign_eq
        by_contra hne1
        rcases Int.units_eq_one_or (Equiv.Perm.sign (garlingRootLabellingPermHom e σ)) with h1 | hm1
        · exact hne1 h1
        · rw [hm1] at hsign_eq
          simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at hsign_eq
          exact h_one_ne_neg_one (mul_right_cancel₀ hδe_ne0 (by rw [one_mul]; exact hsign_eq))
      · intro h1
        rw [h1] at hsign_eq
        simp only [Units.val_one, Int.cast_one, one_mul] at hsign_eq
        let Fixσ : Subfield L := garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L))
        have hsub : (IntermediateField.adjoin K ({δ_e} : Set L)).toSubfield ≤ Fixσ := by
          rw [adjoin_toSubfield_eq_closure, Subfield.closure_le]
          rintro x (⟨k, rfl⟩ | rfl)
          · change algebraMap K L k ∈ garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L))
            rw [mem_garlingPhi_iff]
            rintro _ rfl
            exact σ.commutes k
          · change δ_e ∈ garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L))
            rw [mem_garlingPhi_iff]
            rintro _ rfl
            exact hsign_eq
        intro x hx
        exact (mem_garlingPhi_iff.mp (hsub hx)) σ.toRingEquiv rfl
    have hfixed_field : IntermediateField.adjoin K ({δ} : Set L) =
        IntermediateField.fixedField (garlingEvenGaloisSubgroup e) := by
      rw [← hfixing_eq, IsGalois.fixedField_fixingSubgroup]
    have hnot_sub : ¬ ∀ σ : GarlingPolyGaloisGroup K L f,
        garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin n) := by
      intro hall
      have htop : garlingEvenGaloisSubgroup e = ⊤ := by
        ext σ
        simp [mem_garlingEvenGaloisSubgroup_iff, hall σ]
      have hbot : IntermediateField.adjoin K ({δ} : Set L) = ⊥ := by
        rw [hfixed_field, htop, IsGalois.fixedField_top]
      apply hδ_not_K
      rw [← hbot]
      exact IntermediateField.mem_adjoin_simple_self K δ
    exact ⟨hnot_sub, hfixed_field⟩

/-! ### Power Sums, Hankel Determinant, and Quadratic & Cubic Discriminants (§14.2, p. 112) -/

/-- Power sums `λ_j = α₁^j + … + α_n^j` of an `n`-tuple `α` (§14.2, printed p. 112 / PDF p. 120).
At `j = 0`, `λ_0 = n` in `R`. -/
def garlingPowerSum {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) (j : ℕ) : R :=
  ∑ k : Fin n, (α k) ^ j

@[simp]
theorem garlingPowerSum_zero {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    garlingPowerSum α 0 = (n : R) := by
  simp [garlingPowerSum]

/-- Hankel power-sum matrix `(λ_{i+j-2})_{1 ≤ i, j ≤ n}` (`0`-indexed entry `λ_{i + j}`, with
`(0, 0)`-entry `n`) on printed p. 112 / PDF p. 120.
*(OCR warning verified against 200 DPI scan p. 112 / PDF p. 120: `garling1986_pages.txt`
obliterates this `n × n` matrix to `n / An-1 An A2n-2`.)* -/
def garlingHankelMatrix {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => garlingPowerSum α ((i : ℕ) + (j : ℕ))

/-- Multiplying Garling's Vandermonde matrix by its transpose gives the Hankel power-sum matrix,
and taking determinants yields `Δ = det(λ_{i+j-2})` (§14.2, printed p. 112 / PDF p. 120). -/
theorem garlingDiscTuple_eq_det_hankel {R : Type*} [CommRing R] {n : ℕ} (α : Fin n → R) :
    garlingVandermondeMatrix α * (garlingVandermondeMatrix α)ᵀ = garlingHankelMatrix α ∧
    garlingDiscTuple α = (garlingHankelMatrix α).det := by
  have hmul : garlingVandermondeMatrix α * (garlingVandermondeMatrix α)ᵀ =
      garlingHankelMatrix α := by
    ext i j
    simpa [garlingVandermondeMatrix, garlingHankelMatrix, garlingPowerSum] using
      Matrix.vandermonde_transpose_mul_vandermonde α i j
  refine ⟨hmul, ?_⟩
  rw [← hmul, Matrix.det_mul, Matrix.det_transpose,
    ← (garlingDeltaTuple_eq_det_vandermonde α).1, garlingDiscTuple, sq]

/-- Helper extracting coefficients of `X² + C b₁ X + C b₀` cleanly. -/
private theorem monic_quad_coeffs {R : Type*} [CommRing R] (b₁ b₀ : R) :
    (Polynomial.X ^ 2 + Polynomial.C b₁ * Polynomial.X + Polynomial.C b₀).coeff 1 = b₁ ∧
    (Polynomial.X ^ 2 + Polynomial.C b₁ * Polynomial.X + Polynomial.C b₀).coeff 0 = b₀ := by
  constructor <;> simp

/-- Helper extracting coefficients of `X³ + C b₂ X² + C b₁ X + C b₀` cleanly. -/
private theorem monic_cubic_coeffs {R : Type*} [CommRing R] (b₂ b₁ b₀ : R) :
    (Polynomial.X ^ 3 + Polynomial.C b₂ * Polynomial.X ^ 2 +
      Polynomial.C b₁ * Polynomial.X + Polynomial.C b₀).coeff 2 = b₂ ∧
    (Polynomial.X ^ 3 + Polynomial.C b₂ * Polynomial.X ^ 2 +
      Polynomial.C b₁ * Polynomial.X + Polynomial.C b₀).coeff 1 = b₁ ∧
    (Polynomial.X ^ 3 + Polynomial.C b₂ * Polynomial.X ^ 2 +
      Polynomial.C b₁ * Polynomial.X + Polynomial.C b₀).coeff 0 = b₀ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- **Quadratic discriminant formula** (§14.2, printed p. 112 / PDF p. 120):
For `f = x² + a₁ x + a₀ ∈ K[x]`, `Δ = a₁² - 4 a₀` (valid in **every** characteristic). -/
theorem garlingDiscriminant_monic_quadratic {K : Type u} [Field K] (a₁ a₀ : K) :
    garlingDiscriminant (Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀) =
      a₁ ^ 2 - 4 * a₀ := by
  let f : K[X] := Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀
  have hf_mon : f.Monic := by
    dsimp [f]
    monicity!
  have hf_deg : f.natDegree = 2 := by
    dsimp [f]
    compute_degree!
  let L := Polynomial.SplittingField f
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hc : c = 1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).1.trans hf_mon.leadingCoeff
  have hn : n = 2 := by
    have h1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).2.2.1
    simpa [garlingDegree, hf_deg] using h1
  subst hn hc
  apply (algebraMap K L).injective
  rw [garlingDiscriminant_eq_discTuple hf_mon.ne_zero hexp]
  have hpoly : Polynomial.X ^ 2 + Polynomial.C (algebraMap K L a₁) * Polynomial.X +
      Polynomial.C (algebraMap K L a₀) =
      Polynomial.X ^ 2 + Polynomial.C (-(α 0 + α 1)) * Polynomial.X +
        Polynomial.C (α 0 * α 1) := by
    have hexp' : Polynomial.X ^ 2 + Polynomial.C (algebraMap K L a₁) * Polynomial.X +
        Polynomial.C (algebraMap K L a₀) =
        (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) := by
      simpa [f, GarlingSplitsExplicit, Fin.prod_univ_two] using hexp
    rw [hexp']
    simp only [map_neg, map_add, map_mul]
    ring
  have hv1 : algebraMap K L a₁ = -(α 0 + α 1) := by
    have h := congrArg (fun p : L[X] => p.coeff 1) hpoly
    rwa [(monic_quad_coeffs _ _).1, (monic_quad_coeffs _ _).1] at h
  have hv0 : algebraMap K L a₀ = α 0 * α 1 := by
    have h := congrArg (fun p : L[X] => p.coeff 0) hpoly
    rwa [(monic_quad_coeffs _ _).2, (monic_quad_coeffs _ _).2] at h
  rw [garlingDiscTuple, garlingDeltaTuple_two]
  simp only [map_sub, map_pow, map_mul, map_ofNat, hv1, hv0]
  ring

/-- **Monic cubic discriminant formula** (§14.2, printed p. 112 / PDF p. 120):
For `f = x³ + a₂ x² + a₁ x + a₀ ∈ K[x]`,
`Δ = -4 a₂³ a₀ + a₂² a₁² + 18 a₂ a₁ a₀ - 4 a₁³ - 27 a₀²` (valid in **every** characteristic).
*(OCR warning verified against 200 DPI scan p. 112 / PDF p. 120: `garling1986_pages.txt` completely
drops this entire formula line after `f = x3 + a2x2 + a1x + a0, then`.)* -/
theorem garlingDiscriminant_monic_cubic {K : Type u} [Field K] (a₂ a₁ a₀ : K) :
    garlingDiscriminant
      (Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
        Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀) =
      -4 * a₂ ^ 3 * a₀ + a₂ ^ 2 * a₁ ^ 2 + 18 * a₂ * a₁ * a₀ - 4 * a₁ ^ 3 - 27 * a₀ ^ 2 := by
  let f : K[X] := Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
    Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀
  have hf_mon : f.Monic := by
    dsimp [f]
    monicity!
  have hf_deg : f.natDegree = 3 := by
    dsimp [f]
    compute_degree!
  let L := Polynomial.SplittingField f
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hc : c = 1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).1.trans hf_mon.leadingCoeff
  have hn : n = 3 := by
    have h1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).2.2.1
    simpa [garlingDegree, hf_deg] using h1
  subst hn hc
  apply (algebraMap K L).injective
  rw [garlingDiscriminant_eq_discTuple hf_mon.ne_zero hexp]
  have hpoly : Polynomial.X ^ 3 + Polynomial.C (algebraMap K L a₂) * Polynomial.X ^ 2 +
      Polynomial.C (algebraMap K L a₁) * Polynomial.X + Polynomial.C (algebraMap K L a₀) =
      Polynomial.X ^ 3 + Polynomial.C (-(α 0 + α 1 + α 2)) * Polynomial.X ^ 2 +
        Polynomial.C (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) * Polynomial.X +
        Polynomial.C (-(α 0 * α 1 * α 2)) := by
    have hexp' : Polynomial.X ^ 3 + Polynomial.C (algebraMap K L a₂) * Polynomial.X ^ 2 +
        Polynomial.C (algebraMap K L a₁) * Polynomial.X + Polynomial.C (algebraMap K L a₀) =
        (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) *
          (Polynomial.X - Polynomial.C (α 2)) := by
      simpa [f, GarlingSplitsExplicit, Fin.prod_univ_three, mul_assoc] using hexp
    rw [hexp']
    simp only [map_neg, map_add, map_mul]
    ring
  have hv2 : algebraMap K L a₂ = -(α 0 + α 1 + α 2) := by
    have h := congrArg (fun p : L[X] => p.coeff 2) hpoly
    rwa [(monic_cubic_coeffs _ _ _).1, (monic_cubic_coeffs _ _ _).1] at h
  have hv1 : algebraMap K L a₁ = α 0 * α 1 + α 0 * α 2 + α 1 * α 2 := by
    have h := congrArg (fun p : L[X] => p.coeff 1) hpoly
    rwa [(monic_cubic_coeffs _ _ _).2.1, (monic_cubic_coeffs _ _ _).2.1] at h
  have hv0 : algebraMap K L a₀ = -(α 0 * α 1 * α 2) := by
    have h := congrArg (fun p : L[X] => p.coeff 0) hpoly
    rwa [(monic_cubic_coeffs _ _ _).2.2, (monic_cubic_coeffs _ _ _).2.2] at h
  rw [garlingDiscTuple, garlingDeltaTuple_three]
  simp only [map_sub, map_add, map_neg, map_pow, map_mul, map_ofNat, hv2, hv1, hv0]
  ring

/-! ### Exercises 14.1–14.4 (§14.2, printed pp. 112–113 / PDF pp. 120–121) -/

/-- Sign factor `η_n = 1` if `n (mod 4) = 0` or `1` and `η_n = -1` otherwise (`Exercises 14.1` and
`14.3`, printed pp. 112–113). -/
def garlingEta (n : ℕ) : ℤ :=
  if n % 4 = 0 ∨ n % 4 = 1 then 1 else -1

@[simp] theorem garlingEta_zero : garlingEta 0 = 1 := rfl
@[simp] theorem garlingEta_one : garlingEta 1 = 1 := rfl
@[simp] theorem garlingEta_two : garlingEta 2 = -1 := rfl
@[simp] theorem garlingEta_three : garlingEta 3 = -1 := rfl
@[simp] theorem garlingEta_four : garlingEta 4 = 1 := rfl

theorem garlingEta_sq (n : ℕ) : (garlingEta n) ^ 2 = 1 := by
  unfold garlingEta
  split_ifs <;> norm_num

theorem garlingEta_succ (n : ℕ) : garlingEta (n + 1) = (-1 : ℤ) ^ n * garlingEta n := by
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · have heven : Even n := ⟨2 * (n / 4), by omega⟩
    have h1 : (n + 1) % 4 = 1 := by omega
    rw [heven.neg_one_pow]
    simp [garlingEta, h, h1]
  · have hodd : Odd n := ⟨2 * (n / 4), by omega⟩
    have h1 : (n + 1) % 4 = 2 := by omega
    rw [hodd.neg_one_pow]
    simp [garlingEta, h, h1]
  · have heven : Even n := ⟨2 * (n / 4) + 1, by omega⟩
    have h1 : (n + 1) % 4 = 3 := by omega
    rw [heven.neg_one_pow]
    simp [garlingEta, h, h1]
  · have hodd : Odd n := ⟨2 * (n / 4) + 1, by omega⟩
    have h1 : (n + 1) % 4 = 0 := by omega
    rw [hodd.neg_one_pow]
    simp [garlingEta, h, h1]

theorem garlingEta_eq_neg_one_pow (n : ℕ) :
    garlingEta n = (-1 : ℤ) ^ (n * (n - 1) / 2) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [garlingEta_succ, ih, ← pow_add]
    congr 1
    have htri : (m + 1) * m = 2 * (m * (m - 1) / 2 + m) := by
      rcases m with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · have hdiv : (r + r + 1) * (r + r) / 2 = (2 * r + 1) * r := by
            have : (r + r + 1) * (r + r) = 2 * ((2 * r + 1) * r) := by ring
            rw [this, Nat.mul_div_right _ (by decide)]
          rw [hdiv]; ring
        · have hdiv : (2 * r + 1 + 1) * (2 * r + 1) / 2 = (r + 1) * (2 * r + 1) := by
            have : (2 * r + 1 + 1) * (2 * r + 1) = 2 * ((r + 1) * (2 * r + 1)) := by ring
            rw [this, Nat.mul_div_right _ (by decide)]
          rw [hdiv]; ring
    simp only [Nat.add_sub_cancel]
    rw [htri, Nat.mul_div_right _ (by decide), add_comm]

/-- Evaluating the derivative of `∏ i : Fin n, (X - C (α i))` at `α j` yields
`∏ i ∈ Finset.univ.erase j, (α j - α i)`. -/
theorem eval_garlingDeriv_prod_X_sub_C {R : Type*} [CommRing R] {n : ℕ}
    (α : Fin n → R) (j : Fin n) :
    (garlingDeriv (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))).eval (α j) =
      ∏ i ∈ Finset.univ.erase j, (α j - α i) := by
  have hsplit : (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) =
      (Polynomial.X - Polynomial.C (α j)) *
        ∏ i ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (α i)) :=
    (Finset.mul_prod_erase Finset.univ (fun i => Polynomial.X - Polynomial.C (α i))
      (Finset.mem_univ j)).symm
  rw [hsplit, garlingDeriv_mul]
  have hd1 : garlingDeriv (Polynomial.X - Polynomial.C (α j)) = 1 := by
    rw [garlingDeriv_eq_derivative]
    simp
  rw [hd1, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- Core product identity over any commutative ring:
`∏_{j=1}^n ∏_{i ≠ j} (α_j - α_i) = η_n Δ(α)`. -/
theorem prod_erase_sub_eq_eta_mul_discTuple {R : Type*} [CommRing R] :
    ∀ {n : ℕ} (α : Fin n → R),
      (∏ j : Fin n, ∏ i ∈ Finset.univ.erase j, (α j - α i)) =
        (garlingEta n : R) * garlingDiscTuple α
  | 0, α => by simp [garlingDiscTuple, garlingDeltaTuple]
  | n + 1, α => by
    have hdelta_succ : garlingDeltaTuple α =
        (∏ k : Fin n, (α k.succ - α 0)) * garlingDeltaTuple (Fin.tail α) := by
      unfold garlingDeltaTuple
      rw [Fin.prod_univ_succ]
      congr 1
      · have hIoi0 : Finset.Ioi (0 : Fin (n + 1)) =
            Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩ := by
          ext x
          simp only [Finset.mem_Ioi, Finset.mem_map, Finset.mem_univ, true_and]
          constructor
          · intro hx
            exact ⟨x.pred (Fin.ne_of_gt hx), Fin.succ_pred x (Fin.ne_of_gt hx)⟩
          · rintro ⟨k, rfl⟩
            exact Fin.succ_pos k
        rw [hIoi0, Finset.prod_map]
        rfl
      · refine Finset.prod_congr rfl fun k _ => ?_
        have hIoik : Finset.Ioi k.succ =
            (Finset.Ioi k).map ⟨Fin.succ, Fin.succ_injective n⟩ := by
          ext x
          simp only [Finset.mem_Ioi, Finset.mem_map]
          constructor
          · intro hx
            have hx0 : x ≠ 0 := Fin.ne_of_gt ((Fin.succ_pos k).trans hx)
            refine ⟨x.pred hx0, ?_, Fin.succ_pred x hx0⟩
            rw [← Fin.succ_lt_succ_iff, Fin.succ_pred x hx0]
            exact hx
          · rintro ⟨m, hm, rfl⟩
            exact Fin.succ_lt_succ_iff.mpr hm
        rw [hIoik, Finset.prod_map]
        rfl
    have hdisc_succ : garlingDiscTuple α =
        (∏ k : Fin n, (α k.succ - α 0)) ^ 2 * garlingDiscTuple (Fin.tail α) := by
      rw [garlingDiscTuple, hdelta_succ, mul_pow, ← garlingDiscTuple]
    rw [Fin.prod_univ_succ]
    have hj0 : (∏ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (α 0 - α i)) =
        (-1 : R) ^ n * ∏ k : Fin n, (α k.succ - α 0) := by
      have her0 : Finset.univ.erase (0 : Fin (n + 1)) =
          Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩ := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_map, true_and]
        exact ⟨fun hx => ⟨x.pred hx, Fin.succ_pred x hx⟩,
          by rintro ⟨k, rfl⟩; exact Fin.succ_ne_zero k⟩
      rw [her0, Finset.prod_map]
      have hneg : ∀ k : Fin n, α 0 - α k.succ = (-1 : R) * (α k.succ - α 0) := fun k => by ring
      calc (∏ x : Fin n, (α 0 - α ((⟨Fin.succ, Fin.succ_injective n⟩ : Fin n ↪ Fin (n + 1)) x)))
          = ∏ k : Fin n, ((-1 : R) * (α k.succ - α 0)) := Finset.prod_congr rfl fun k _ => hneg k
        _ = (-1 : R) ^ n * ∏ k : Fin n, (α k.succ - α 0) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    have hjk : ∀ k : Fin n,
        (∏ i ∈ Finset.univ.erase k.succ, (α k.succ - α i)) =
          (α k.succ - α 0) * ∏ m ∈ Finset.univ.erase k, (Fin.tail α k - Fin.tail α m) := by
      intro k
      have herk : Finset.univ.erase k.succ =
          insert (0 : Fin (n + 1))
            ((Finset.univ.erase k).map ⟨Fin.succ, Fin.succ_injective n⟩) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
          Finset.mem_map]
        constructor
        · intro hne
          by_cases hx0 : x = 0
          · exact Or.inl hx0
          · right
            refine ⟨x.pred hx0, ?_, Fin.succ_pred x hx0⟩
            intro hpk
            apply hne
            rw [← hpk, Fin.succ_pred x hx0]
        · rintro (rfl | ⟨m, hmk, rfl⟩)
          · exact (Fin.succ_ne_zero k).symm
          · exact fun h => hmk (Fin.succ_injective n h)
      have h0_not_mem : (0 : Fin (n + 1)) ∉
          (Finset.univ.erase k).map ⟨Fin.succ, Fin.succ_injective n⟩ := by
        intro hmem
        rcases Finset.mem_map.mp hmem with ⟨m, _, hm⟩
        exact Fin.succ_ne_zero m hm
      rw [herk, Finset.prod_insert h0_not_mem, Finset.prod_map]
      rfl
    simp_rw [hjk]
    rw [Finset.prod_mul_distrib, prod_erase_sub_eq_eta_mul_discTuple (Fin.tail α),
      hj0, hdisc_succ, garlingEta_succ]
    push_cast
    ring

/-- **Counterexample to the literal unguarded statement of `Exercise 14.1` for non-monic `f`**
(`BRIEF.md` Flag 3 & `QUEUE.md`):
On `K = L = ℚ` and `f = 2x² - 2x = 2x(x - 1)` (`n = 2`, `α₁ = 0`, `α₂ = 1`), `Δ = (1 - 0)² = 1`,
whereas `η₂ ∏_{j=1}^2 Df(α_j) = (-1)(-2)(2) = 4 ≠ 1`. -/
theorem exercise_14_1_nonmonic_counterexample :
    let f : ℚ[X] := Polynomial.C 2 * Polynomial.X ^ 2 - Polynomial.C 2 * Polynomial.X
    let α : Fin 2 → ℚ := ![0, 1]
    IsGarlingSplittingFieldExtension ℚ ℚ f ∧
    GarlingSplitsExplicit ℚ ℚ f 2 2 α ∧
    garlingDiscriminant f = 1 ∧
    (garlingEta 2 : ℚ) * (∏ j : Fin 2, Polynomial.aeval (α j) (garlingDeriv f)) = 4 ∧
    algebraMap ℚ ℚ (garlingDiscriminant f) ≠
      (garlingEta 2 : ℚ) * (∏ j : Fin 2, Polynomial.aeval (α j) (garlingDeriv f)) := by
  intro f α
  have hexp : GarlingSplitsExplicit ℚ ℚ f 2 2 α := by
    change f.map (RingHom.id ℚ) =
      Polynomial.C (2 : ℚ) * ∏ j : Fin 2, (Polynomial.X - Polynomial.C (α j))
    rw [Polynomial.map_id, Fin.prod_univ_two]
    simp only [f, α, Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, map_one, sub_zero]
    ring
  have hf0 : f ≠ 0 := by
    intro h0
    have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h0
    simp [f] at hc
  have hsf : IsGarlingSplittingFieldExtension ℚ ℚ f :=
    ⟨⟨2, 2, α, hexp⟩, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
  have hdisc : garlingDiscriminant f = 1 := by
    have h := garlingDiscriminant_eq_discTuple hf0 hexp
    rw [garlingDiscTuple, garlingDeltaTuple_two] at h
    simpa [α] using h
  have hdf : garlingDeriv f = Polynomial.C 4 * Polynomial.X - Polynomial.C 2 := by
    rw [garlingDeriv_eq_derivative]
    dsimp [f]
    rw [map_ofNat Polynomial.C 2, map_ofNat Polynomial.C 4]
    simp
    ring
  have hrhs : (garlingEta 2 : ℚ) * (∏ j : Fin 2, Polynomial.aeval (α j) (garlingDeriv f)) = 4 := by
    rw [hdf, Fin.prod_univ_two]
    simp [α]
    norm_num
  refine ⟨hsf, hexp, hdisc, hrhs, ?_⟩
  rw [hdisc, hrhs]
  norm_num

/-- **Exercise 14.1 — General non-zero polynomial formula** (§14.2, printed p. 112 / PDF p. 120;
see `QUEUE.md` on the omitted `Monic` factor `a_n^n`):
For **every** non-zero polynomial `f ∈ K[x]` with roots `α₁, …, α_n` (counted with multiplicity,
`GarlingSplitsExplicit K L f n c α`) in an extension `L : K`,
`η_n ∏_{j=1}^n Df(α_j) = a_n^n Δ`. -/
theorem exercise_14_1_general {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) {n : ℕ} {c : K} {α : Fin n → L}
    (hexp : GarlingSplitsExplicit K L f n c α) :
    (garlingEta n : L) * (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) =
      algebraMap K L (f.leadingCoeff ^ n * garlingDiscriminant f) := by
  have hc_eq : c = f.leadingCoeff := (garlingSplitsExplicit_props hf0 hexp).1
  have hderiv_map : (garlingDeriv f).map (algebraMap K L) =
      Polynomial.C (algebraMap K L c) *
        garlingDeriv (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) := by
    rw [← garlingDeriv_map, hexp, garlingDeriv_C_mul]
  have heval_j : ∀ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f) =
      algebraMap K L c * ∏ i ∈ Finset.univ.erase j, (α j - α i) := by
    intro j
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hderiv_map, Polynomial.eval_mul,
      Polynomial.eval_C, eval_garlingDeriv_prod_X_sub_C]
  simp_rw [heval_j]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
    prod_erase_sub_eq_eta_mul_discTuple, ← garlingDiscriminant_eq_discTuple hf0 hexp,
    hc_eq, map_mul, map_pow]
  have heta_sq : (garlingEta n : L) * (garlingEta n : L) = 1 := by
    have hZ := garlingEta_sq n
    have hL : (((garlingEta n) ^ 2 : ℤ) : L) = (1 : L) := by rw [hZ]; simp
    simpa [sq] using hL
  calc (garlingEta n : L) *
        ((algebraMap K L f.leadingCoeff) ^ n *
          ((garlingEta n : L) * algebraMap K L (garlingDiscriminant f)))
      = ((garlingEta n : L) * (garlingEta n : L)) *
          ((algebraMap K L f.leadingCoeff) ^ n * algebraMap K L (garlingDiscriminant f)) := by ring
    _ = (algebraMap K L f.leadingCoeff) ^ n * algebraMap K L (garlingDiscriminant f) := by
          rw [heta_sq, one_mul]

/-- **Exercise 14.1 — Monic polynomial formula** (§14.2, printed p. 112 / PDF p. 120; `QUEUE.md`):
For every **monic** polynomial `f ∈ K[x]` (`a_n = 1`, across all degrees `n ≥ 0`) with roots
`α₁, …, α_n` in an extension `L : K`, `Δ = η_n ∏_{j=1}^n Df(α_j)` holds literally as printed. -/
theorem exercise_14_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hmon : f.Monic) {n : ℕ} {c : K} {α : Fin n → L}
    (hexp : GarlingSplitsExplicit K L f n c α) :
    algebraMap K L (garlingDiscriminant f) =
      (garlingEta n : L) * (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) := by
  have hgen := exercise_14_1_general hmon.ne_zero hexp
  rw [hmon.leadingCoeff, one_pow, one_mul] at hgen
  exact hgen.symm

/-- Necessary and sufficient condition for the literal printed formula of `Exercise 14.1` when
`Δ ≠ 0`: it holds if and only if `a_n^n = 1`. -/
theorem exercise_14_1_iff_of_disc_ne_zero {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf0 : f ≠ 0)
    (hΔ : garlingDiscriminant f ≠ 0) {n : ℕ} {c : K} {α : Fin n → L}
    (hexp : GarlingSplitsExplicit K L f n c α) :
    algebraMap K L (garlingDiscriminant f) =
      (garlingEta n : L) * (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) ↔
      f.leadingCoeff ^ n = 1 := by
  rw [exercise_14_1_general hf0 hexp]
  constructor
  · intro heq
    have hinj := (algebraMap K L).injective heq
    exact mul_right_cancel₀ hΔ (by rw [one_mul]; exact hinj.symm)
  · intro h1
    rw [h1, one_mul]

/-- Quotient polynomial `g_i = a₁ + a₂(x + α_i) + … + a_n(x^{n-1} + α_i x^{n-2} + … + α_i^{n-1})`
in `L[x]` from **Exercise 14.2 (i)** (§14.2, printed p. 112 / PDF p. 120). -/
noncomputable def garlingQuotPoly {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ) (α_i : L) : L[X] :=
  ∑ m ∈ Finset.Icc 1 n,
    Polynomial.C (algebraMap K L (f.coeff m)) *
      (∑ r ∈ Finset.range m, Polynomial.C (α_i ^ r) * Polynomial.X ^ (m - 1 - r))

/-- Geometric-sum factorization `(X - C a) * ∑_{r=0}^{m-1} a^r X^{m-1-r} = X^m - C (a^m)` for
`m ≥ 1`. -/
private theorem X_sub_C_mul_geom_sum {R : Type*} [CommRing R] (a : R) :
    ∀ {m : ℕ}, 1 ≤ m →
      (Polynomial.X - Polynomial.C a) *
        (∑ r ∈ Finset.range m, Polynomial.C (a ^ r) * Polynomial.X ^ (m - 1 - r)) =
        Polynomial.X ^ m - Polynomial.C (a ^ m)
  | 0, hm => absurd hm (by decide)
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := X_sub_C_mul_geom_sum a (m := k + 1) (by omega)
    rw [Finset.sum_range_succ, mul_add]
    have hshift : (∑ r ∈ Finset.range (k + 1),
        Polynomial.C (a ^ r) * Polynomial.X ^ (k + 2 - 1 - r)) =
        (∑ r ∈ Finset.range (k + 1),
          Polynomial.C (a ^ r) * Polynomial.X ^ (k + 1 - 1 - r)) * Polynomial.X := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_lt : r < k + 1 := Finset.mem_range.mp hr
      have hexp_eq : k + 2 - 1 - r = (k + 1 - 1 - r) + 1 := by omega
      rw [hexp_eq, pow_succ, mul_assoc]
    rw [hshift, ← mul_assoc, ih]
    have hlast : k + 2 - 1 - (k + 1) = 0 := by omega
    rw [hlast, pow_zero, mul_one]
    simp only [sub_mul, pow_succ, ← map_mul]
    ring

/-- **Exercise 14.2 (i)** (§14.2, printed p. 112 / PDF p. 120):
For any polynomial `f` of degree `≤ n` in `K[x]` and any root `α_i ∈ L` of `f`,
`f = (x - α_i) g_i` in `L[x]`. -/
theorem exercise_14_2_i {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (hdeg : f.natDegree ≤ n) {α_i : L}
    (hroot : Polynomial.aeval α_i f = 0) :
    f.map (algebraMap K L) = (Polynomial.X - Polynomial.C α_i) * garlingQuotPoly f n α_i := by
  unfold garlingQuotPoly
  rw [Finset.mul_sum]
  have hterm : ∀ m ∈ Finset.Icc 1 n,
      (Polynomial.X - Polynomial.C α_i) *
        (Polynomial.C (algebraMap K L (f.coeff m)) *
          ∑ r ∈ Finset.range m, Polynomial.C (α_i ^ r) * Polynomial.X ^ (m - 1 - r)) =
      Polynomial.C (algebraMap K L (f.coeff m)) *
        (Polynomial.X ^ m - Polynomial.C (α_i ^ m)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    calc (Polynomial.X - Polynomial.C α_i) *
          (Polynomial.C (algebraMap K L (f.coeff m)) *
            ∑ r ∈ Finset.range m, Polynomial.C (α_i ^ r) * Polynomial.X ^ (m - 1 - r))
        = Polynomial.C (algebraMap K L (f.coeff m)) *
            ((Polynomial.X - Polynomial.C α_i) *
              ∑ r ∈ Finset.range m, Polynomial.C (α_i ^ r) * Polynomial.X ^ (m - 1 - r)) := by ring
      _ = _ := by rw [X_sub_C_mul_geom_sum α_i hm1]
  rw [Finset.sum_congr rfl hterm]
  have hf_sum : f = ∑ m ∈ Finset.range (n + 1), Polynomial.C (f.coeff m) * Polynomial.X ^ m := by
    conv_lhs => rw [Polynomial.as_sum_range' f (n + 1) (Nat.lt_succ_of_le hdeg)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have haeval_sum : (0 : L) =
      ∑ m ∈ Finset.range (n + 1), algebraMap K L (f.coeff m) * α_i ^ m := by
    rw [← hroot]
    conv_lhs => rw [hf_sum]
    simp [map_sum]
  have hmap_sum : f.map (algebraMap K L) =
      ∑ m ∈ Finset.range (n + 1),
        Polynomial.C (algebraMap K L (f.coeff m)) * Polynomial.X ^ m := by
    conv_lhs => rw [hf_sum]
    simp [Polynomial.map_sum]
  have hIcc : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0_notin : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  rw [hmap_sum, hIcc, Finset.sum_insert h0_notin]
  have hc0 : Polynomial.C (0 : L) =
      Polynomial.C (algebraMap K L (f.coeff 0)) +
        ∑ m ∈ Finset.Icc 1 n, Polynomial.C (algebraMap K L (f.coeff m) * α_i ^ m) := by
    have h := congrArg Polynomial.C haeval_sum
    rw [hIcc, Finset.sum_insert h0_notin, map_add, map_sum] at h
    simpa using h
  simp only [pow_zero, mul_one]
  have hsub_sum : (∑ m ∈ Finset.Icc 1 n,
      Polynomial.C (algebraMap K L (f.coeff m)) * (Polynomial.X ^ m - Polynomial.C (α_i ^ m))) =
      (∑ m ∈ Finset.Icc 1 n, Polynomial.C (algebraMap K L (f.coeff m)) * Polynomial.X ^ m) -
      (∑ m ∈ Finset.Icc 1 n, Polynomial.C (algebraMap K L (f.coeff m) * α_i ^ m)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_sub, map_mul]
  rw [hsub_sum]
  have hzeroC : Polynomial.C (0 : L) = 0 := map_zero Polynomial.C
  rw [hzeroC] at hc0
  linear_combination -hc0

/-- **Exercise 14.2 (ii)** (§14.2, printed p. 113 / PDF p. 121):
For `f = a₀ + … + a_n x^n` of degree `n` splitting over `L` as `f = a_n ∏_{i=1}^n (x - α_i)`,
`Df = ∑_{i=1}^n g_i` in `L[x]`. -/
theorem exercise_14_2_ii {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) {n : ℕ} (hdeg : garlingDegree f hf0 = n)
    {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n (f.coeff n) α) :
    (garlingDeriv f).map (algebraMap K L) = ∑ i : Fin n, garlingQuotPoly f n (α i) := by
  have hn_nat : f.natDegree = n := hdeg
  have hgi_eq : ∀ i : Fin n, garlingQuotPoly f n (α i) =
      Polynomial.C (algebraMap K L (f.coeff n)) *
        ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j)) := by
    intro i
    have hroot_i : Polynomial.aeval (α i) f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
        Polynomial.eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      simp
    have h1 := exercise_14_2_i (le_of_eq hn_nat) hroot_i
    have h2 : f.map (algebraMap K L) = (Polynomial.X - Polynomial.C (α i)) *
        (Polynomial.C (algebraMap K L (f.coeff n)) *
          ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))) := by
      rw [hexp, ← Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (α j))
        (Finset.mem_univ i)]
      ring
    exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (α i)) (h1.symm.trans h2)
  simp_rw [hgi_eq, ← Finset.mul_sum]
  rw [← garlingDeriv_map, hexp, garlingDeriv_C_mul]
  congr 1
  -- Product Leibniz rule over `Fin n`: `D (∏_{i ∈ s} (X - C (α i))) = ∑_{i ∈ s} ∏_{j ∈ s.erase i} (X - C (α j))`
  have hleibniz : ∀ s : Finset (Fin n),
      garlingDeriv (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i))) =
        ∑ i ∈ s, ∏ j ∈ s.erase i, (Polynomial.X - Polynomial.C (α j)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [garlingDeriv_eq_derivative]
    | insert a t hat ih =>
      rw [Finset.prod_insert hat, garlingDeriv_mul, ih, Finset.sum_insert hat,
        Finset.erase_insert hat]
      have hda : garlingDeriv (Polynomial.X - Polynomial.C (α a)) = 1 := by
        rw [garlingDeriv_eq_derivative]; simp
      rw [hda, one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => hat (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,
        Finset.prod_insert (fun h => hat (Finset.mem_of_mem_erase h))]
  exact hleibniz Finset.univ

/-- **Exercise 14.2 (iii) — Newton's identities** (§14.2, printed p. 113 / PDF p. 121):
For `f = a₀ + a₁ x + … + a_n x^n` of degree `n` splitting over `L` as
`f = a_n ∏_{i=1}^n (x - α_i)`, and `λ_j = ∑_{i=1}^n α_i^j`:
1. For every `1 ≤ m ≤ n`: `m a_{n-m} + ∑_{j=1}^m a_{n-m+j} λ_j = 0`
   (giving `a_{n-1} + a_n λ₁ = 0` at `m = 1`, `2 a_{n-2} + a_{n-1} λ₁ + a_n λ₂ = 0` at `m = 2`,
   …, `n a₀ + a₁ λ₁ + … + a_n λ_n = 0` at `m = n`);
2. For every `k ≥ 1`: `a₀ λ_k + a₁ λ_{k+1} + … + a_{n-1} λ_{k+n-1} + a_n λ_{k+n} = 0`. -/
theorem exercise_14_2_iii {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) {n : ℕ} (hdeg : garlingDegree f hf0 = n)
    {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n (f.coeff n) α) :
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      (m : L) * algebraMap K L (f.coeff (n - m)) +
        ∑ j ∈ Finset.Icc 1 m, algebraMap K L (f.coeff (n - m + j)) * garlingPowerSum α j = 0) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ r ∈ Finset.range (n + 1),
        algebraMap K L (f.coeff r) * garlingPowerSum α (k + r) = 0) := by
  have hn_nat : f.natDegree = n := hdeg
  have hroot_all : ∀ i : Fin n, Polynomial.aeval (α i) f = 0 := by
    intro i
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
      Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp
  have hf_eval_sum : ∀ i : Fin n,
      ∑ r ∈ Finset.range (n + 1), algebraMap K L (f.coeff r) * (α i) ^ r = 0 := by
    intro i
    rw [← hroot_all i]
    conv_rhs => rw [Polynomial.as_sum_range' f (n + 1) (by omega)]
    simp [map_sum]
  constructor
  · intro m hm1 hmn
    by_cases hmn_eq : m = n
    · -- Case `m = n`: `n a₀ + ∑_{j=1}^n a_j λ_j = 0`, obtained by summing `f(α_i) = 0` over `i`
      subst m
      simp only [Nat.sub_self, zero_add]
      have hsum0 : ∑ i : Fin n,
          ∑ r ∈ Finset.range (n + 1), algebraMap K L (f.coeff r) * (α i) ^ r = 0 := by
        simp [hf_eval_sum]
      rw [Finset.sum_comm] at hsum0
      have hIcc : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
        ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hIcc, Finset.sum_insert (by simp)] at hsum0
      have h0term : (∑ i : Fin n, algebraMap K L (f.coeff 0) * (α i) ^ 0) =
          (n : L) * algebraMap K L (f.coeff 0) := by
        simp [mul_comm]
      have hrest : (∑ x ∈ Finset.Icc 1 n, ∑ i : Fin n, algebraMap K L (f.coeff x) * (α i) ^ x) =
          ∑ x ∈ Finset.Icc 1 n, algebraMap K L (f.coeff x) * garlingPowerSum α x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum]
        rfl
      rw [h0term, hrest] at hsum0
      exact hsum0
    · -- Case `1 ≤ m < n`: equate `coeff (n - 1 - m)` of `Df = ∑ g_i` from `exercise_14_2_ii`
      have hm_lt : m < n := Nat.lt_of_le_of_ne hmn hmn_eq
      let s : ℕ := n - 1 - m
      have hs_succ : s + 1 = n - m := by omega
      have hderiv_eq := congrArg (fun p : L[X] => p.coeff s) (exercise_14_2_ii hf0 hdeg hexp)
      have hlhs : ((garlingDeriv f).map (algebraMap K L)).coeff s =
          ((s : L) + 1) * algebraMap K L (f.coeff (n - m)) := by
        rw [Polynomial.coeff_map, garlingDeriv_eq_derivative, Polynomial.coeff_derivative,
          hs_succ, map_mul, map_add, map_natCast, map_one]
        ring
      have hgi_coeff : ∀ i : Fin n, (garlingQuotPoly f n (α i)).coeff s =
          ∑ k ∈ Finset.Icc (s + 1) n,
            algebraMap K L (f.coeff k) * (α i) ^ (k - 1 - s) := by
        intro i
        unfold garlingQuotPoly
        rw [Polynomial.finsetSum_coeff]
        have hsplit_Icc : Finset.Icc 1 n =
            Finset.Icc 1 s ∪ Finset.Icc (s + 1) n := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 1 s) (Finset.Icc (s + 1) n) := by
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp only [Finset.mem_Icc] at hk1 hk2
          omega
        rw [hsplit_Icc, Finset.sum_union hdisj]
        have hlow0 : ∑ k ∈ Finset.Icc 1 s,
            (Polynomial.C (algebraMap K L (f.coeff k)) *
              ∑ r ∈ Finset.range k, Polynomial.C ((α i) ^ r) * Polynomial.X ^ (k - 1 - r)).coeff s =
            0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
          have hk_bds := Finset.mem_Icc.mp hk
          have h0 : ∑ r ∈ Finset.range k,
              (Polynomial.C ((α i) ^ r) * Polynomial.X ^ (k - 1 - r)).coeff s = 0 := by
            refine Finset.sum_eq_zero fun r _ => ?_
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            have hne : s ≠ k - 1 - r := by omega
            simp [hne]
          rw [h0, mul_zero]
        rw [hlow0, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
        congr 1
        have hk_ge : s + 1 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [Finset.sum_eq_single (k - 1 - s)]
        · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          have heq_s : k - 1 - (k - 1 - s) = s := by omega
          simp [heq_s]
        · intro r hr hne
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          have hr_lt : r < k := Finset.mem_range.mp hr
          have hs_ne : s ≠ k - 1 - r := by omega
          simp [hs_ne]
        · intro habs
          exact absurd (Finset.mem_range.mpr (by omega)) habs
      rw [hlhs, Polynomial.finsetSum_coeff] at hderiv_eq
      simp_rw [hgi_coeff] at hderiv_eq
      rw [Finset.sum_comm] at hderiv_eq
      have hreindex : (∑ k ∈ Finset.Icc (s + 1) n,
          ∑ i : Fin n, algebraMap K L (f.coeff k) * (α i) ^ (k - 1 - s)) =
          (n : L) * algebraMap K L (f.coeff (n - m)) +
            ∑ j ∈ Finset.Icc 1 m, algebraMap K L (f.coeff (n - m + j)) * garlingPowerSum α j := by
        have hIcc_s : Finset.Icc (s + 1) n = insert (n - m) (Finset.Icc (n - m + 1) n) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot_in : n - m ∉ Finset.Icc (n - m + 1) n := by
          simp only [Finset.mem_Icc]; omega
        rw [hIcc_s, Finset.sum_insert hnot_in]
        congr 1
        · have hexp0 : n - m - 1 - s = 0 := by omega
          rw [hexp0]
          simp [mul_comm]
        · refine Finset.sum_bij (fun k _ => k - (n - m)) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
          · intro k₁ hk₁ k₂ hk₂ heq; simp only [Finset.mem_Icc] at hk₁ hk₂; omega
          · intro j hj
            simp only [Finset.mem_Icc] at hj
            exact ⟨n - m + j, by simp only [Finset.mem_Icc]; omega, by omega⟩
          · intro k hk
            simp only [Finset.mem_Icc] at hk
            have hk1 : n - m + (k - (n - m)) = k := by omega
            have hk2 : k - 1 - s = k - (n - m) := by omega
            rw [hk1, hk2, ← Finset.mul_sum]
            rfl
      rw [hreindex] at hderiv_eq
      have hnat_sub : (n : L) - ((s : L) + 1) = (m : L) := by
        have hnat : s + 1 + m = n := by omega
        have hcast : ((s + 1 + m : ℕ) : L) = (n : L) := congrArg Nat.cast hnat
        push_cast at hcast
        linear_combination -hcast
      linear_combination -hderiv_eq - hnat_sub * algebraMap K L (f.coeff (n - m))
  · -- Part 2: `k ≥ 1`: sum `α_i^k * f(α_i) = 0` over `i : Fin n`
    intro k _
    have hsum0 : ∑ i : Fin n,
        (α i) ^ k * (∑ r ∈ Finset.range (n + 1), algebraMap K L (f.coeff r) * (α i) ^ r) = 0 := by
      simp [hf_eval_sum]
    simp_rw [Finset.mul_sum] at hsum0
    rw [Finset.sum_comm] at hsum0
    have hcongr : (∑ r ∈ Finset.range (n + 1),
        ∑ i : Fin n, (α i) ^ k * (algebraMap K L (f.coeff r) * (α i) ^ r)) =
        ∑ r ∈ Finset.range (n + 1),
          algebraMap K L (f.coeff r) * garlingPowerSum α (k + r) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [garlingPowerSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]
      ring
    rwa [hcongr] at hsum0

/-- **Exercise 14.2** (§14.2, printed pp. 112–113 / PDF pp. 120–121):
Combined theorem packaging `(i)`, `(ii)`, and `(iii)` (*Newton's identities*, including explicit
first-line `a_{n-1} + a_n λ₁ = 0` for `1 ≤ n` and second-line `2a_{n-2} + a_{n-1} λ₁ + a_n λ₂ = 0`
for `2 ≤ n`). -/
theorem exercise_14_2 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf0 : f ≠ 0) {n : ℕ} (hdeg : garlingDegree f hf0 = n)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    {α : Fin n → L} (hexp : GarlingSplitsExplicit K L f n (f.coeff n) α) :
    -- (i) `f = (x - α_i) g_i` in `L[x]`
    (∀ i : Fin n,
      f.map (algebraMap K L) = (Polynomial.X - Polynomial.C (α i)) * garlingQuotPoly f n (α i)) ∧
    -- (ii) `Df = ∑_{i=1}^n g_i`
    ((garlingDeriv f).map (algebraMap K L) = ∑ i : Fin n, garlingQuotPoly f n (α i)) ∧
    -- (iii) Newton's identities (`1 ≤ m ≤ n` and `k ≥ 1`, plus explicit `m = 1` and `m = 2`)
    (∀ m : ℕ, 1 ≤ m → m ≤ n →
      (m : L) * algebraMap K L (f.coeff (n - m)) +
        ∑ j ∈ Finset.Icc 1 m, algebraMap K L (f.coeff (n - m + j)) * garlingPowerSum α j = 0) ∧
    (1 ≤ n →
      algebraMap K L (f.coeff (n - 1)) +
        algebraMap K L (f.coeff n) * garlingPowerSum α 1 = 0) ∧
    (2 ≤ n →
      2 * algebraMap K L (f.coeff (n - 2)) +
        algebraMap K L (f.coeff (n - 1)) * garlingPowerSum α 1 +
        algebraMap K L (f.coeff n) * garlingPowerSum α 2 = 0) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ r ∈ Finset.range (n + 1),
        algebraMap K L (f.coeff r) * garlingPowerSum α (k + r) = 0) := by
  have _ := hsf
  have hroot : ∀ i : Fin n, Polynomial.aeval (α i) f = 0 := by
    intro i
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
      Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp
  obtain ⟨hN1, hN2⟩ := exercise_14_2_iii hf0 hdeg hexp
  refine ⟨fun i => exercise_14_2_i (le_of_eq hdeg) (hroot i),
    exercise_14_2_ii hf0 hdeg hexp, hN1, ?_, ?_, hN2⟩
  · intro hn1
    have h1 := hN1 1 (le_refl 1) hn1
    have hIcc1 : Finset.Icc 1 1 = {1} := by decide
    have hn_sub : n - 1 + 1 = n := by omega
    rw [hIcc1, Finset.sum_singleton, hn_sub] at h1
    simpa using h1
  · intro hn2
    have h2 := hN1 2 (by decide) hn2
    have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
    have hsub1 : n - 2 + 1 = n - 1 := by omega
    have hsub2 : n - 2 + 2 = n := by omega
    rw [hIcc2, Finset.sum_pair (by decide), hsub1, hsub2] at h2
    push_cast at h2
    linear_combination h2

/-- Companion remark for `Exercise 14.2` (`PROGRESS.md` formulation note): repeating a single root
`α = ![0, 0]` of `f = x² - x ∈ ℚ[x]` (rather than listing the roots counted with multiplicity
`f = a_n ∏ (x - α_i)`) still satisfies `(i)`, but violates `(ii)` (`Df = 2x - 1 ≠ 2x - 2`). -/
theorem exercise_14_2_nonmultiplicity_remark :
    let f : ℚ[X] := Polynomial.X ^ 2 - Polynomial.X
    let α : Fin 2 → ℚ := ![0, 0]
    (∀ i : Fin 2, Polynomial.aeval (α i) f = 0) ∧
    (∀ i : Fin 2, f = (Polynomial.X - Polynomial.C (α i)) * garlingQuotPoly f 2 (α i)) ∧
    garlingDeriv f ≠ ∑ i : Fin 2, garlingQuotPoly f 2 (α i) := by
  intro f α
  have hdeg : f.natDegree ≤ 2 := by dsimp [f]; compute_degree!
  have hroot : ∀ i : Fin 2, Polynomial.aeval (α i) f = 0 := by
    intro i; fin_cases i <;> simp [f, α]
  refine ⟨hroot, fun i => by simpa using exercise_14_2_i (L := ℚ) hdeg (hroot i), ?_⟩
  intro heq
  have hc0 := congrArg (fun p : ℚ[X] => p.coeff 0) heq
  have hlhs : (garlingDeriv f).coeff 0 = -1 := by
    rw [garlingDeriv_eq_derivative]
    simp [f]
  have hrhs : (∑ i : Fin 2, garlingQuotPoly (L := ℚ) f 2 (α i)).coeff 0 = -2 := by
    have hg0 : garlingQuotPoly (L := ℚ) f 2 0 = Polynomial.X - 1 := by
      have hfac := exercise_14_2_i (L := ℚ) hdeg (hroot 0)
      change f.map (RingHom.id ℚ) = _ at hfac
      rw [Polynomial.map_id] at hfac
      simp only [α, Matrix.cons_val_zero, map_zero, sub_zero] at hfac
      have hfac2 : f = Polynomial.X * (Polynomial.X - 1) := by dsimp [f]; ring
      exact mul_left_cancel₀ Polynomial.X_ne_zero (hfac.symm.trans hfac2)
    rw [Fin.sum_univ_two]
    simp [α, hg0]
    norm_num
  linarith

/-! #### Exercise 14.3: Power Sums and Trinomial Discriminant (§14.2, p. 113; `QUEUE.md`) -/

/-- **Counterexample to the `n = 2` edge case of the power-sum identities in `Exercise 14.3`**
(`BRIEF.md` Flag 1 & `QUEUE.md`):
For `n = 2`, `f = x² + x + 1 ∈ ℚ[x]` (`p = 1, q = 1`), the indices `n = 2` and `2n - 2 = 2`
collide: `λ₂ = p² - 2q = -1`, which equals neither `-nq = -2` nor `(n - 1)p² = 1`. -/
theorem exercise_14_3_n2_powerSum_counterexample :
    let f : ℚ[X] := Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C 1
    let L := Polynomial.SplittingField f
    ∃ α : Fin 2 → L,
      GarlingSplitsExplicit ℚ L f 2 1 α ∧
      garlingPowerSum α 2 = -1 ∧
      garlingPowerSum α 2 ≠ -(2 : L) * algebraMap ℚ L 1 ∧
      garlingPowerSum α 2 ≠ ((2 - 1 : ℕ) : L) * (algebraMap ℚ L 1) ^ 2 := by
  intro f L
  let _ : Field L := Polynomial.SplittingField.instField f
  let _ : Algebra ℚ L := Polynomial.SplittingField.instAlgebra f
  have hf_mon : f.Monic := by dsimp [f]; monicity!
  have hf_deg : f.natDegree = 2 := by dsimp [f]; compute_degree!
  have hsf : IsGarlingSplittingFieldExtension ℚ L f :=
    (isGarlingSplittingFieldExtension_iff ℚ L f).mpr inferInstance
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hc : c = 1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).1.trans hf_mon.leadingCoeff
  have hn : n = 2 := by
    have h1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).2.2.1
    simpa [garlingDegree, hf_deg] using h1
  subst hn hc
  have hc0 : f.coeff 0 = 1 := by simp [f, Polynomial.coeff_one]
  have hc1 : f.coeff 1 = 1 := by simp [f, Polynomial.coeff_one]
  have hc2 : f.coeff 2 = 1 := by rw [← hf_deg, hf_mon.coeff_natDegree]
  have hexp' : GarlingSplitsExplicit ℚ L f 2 (f.coeff 2) α := by rwa [hc2]
  obtain ⟨hN1, _⟩ := exercise_14_2_iii hf_mon.ne_zero hf_deg hexp'
  have hm1 := hN1 1 (le_refl 1) (by decide)
  have hm2 := hN1 2 (by decide) (le_refl 2)
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc1, Finset.sum_singleton] at hm1
  rw [hIcc2, Finset.sum_pair (by decide)] at hm2
  have h1L : algebraMap ℚ L 1 = 1 := map_one (algebraMap ℚ L)
  simp only [Nat.reduceSub, Nat.reduceAdd, hc0, hc1, hc2, h1L, Nat.cast_one,
    Nat.cast_ofNat, one_mul] at hm1 hm2
  have hl1 : garlingPowerSum α 1 = -1 := by linear_combination hm1
  have hl2 : garlingPowerSum α 2 = -1 := by linear_combination hm2 - hl1
  have hchar0 : (1 : L) ≠ 0 := one_ne_zero
  refine ⟨α, hexp, hl2, ?_, ?_⟩
  · rw [hl2, h1L, mul_one]
    intro h
    apply hchar0
    linear_combination h
  · rw [hl2, h1L]
    norm_num

/-- **Exercise 14.3 — Power-sum identities for `n ≥ 3`** (§14.2, printed p. 113 / PDF p. 121;
`QUEUE.md`):
For `f = x^n + px + q ∈ K[x]` with `n ≥ 3` (in **every** characteristic) and roots `α₁, …, α_n`
in `L`:
- `λ_j = 0` for `1 ≤ j ≤ n - 2`;
- `λ_{n-1} = -(n - 1) p`;
- `λ_n = -n q`;
- `λ_j = 0` for `n + 1 ≤ j ≤ 2n - 3`;
- `λ_{2n-2} = (n - 1) p²`. -/
theorem exercise_14_3_powerSums {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hn3 : 3 ≤ n) (p q : K) {α : Fin n → L}
    (hexp : GarlingSplitsExplicit K L
      (Polynomial.X ^ n + Polynomial.C p * Polynomial.X + Polynomial.C q) n 1 α) :
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 2 → garlingPowerSum α j = 0) ∧
    garlingPowerSum α (n - 1) = -(((n - 1 : ℕ) : L) * algebraMap K L p) ∧
    garlingPowerSum α n = -((n : L) * algebraMap K L q) ∧
    (∀ j : ℕ, n + 1 ≤ j → j ≤ 2 * n - 3 → garlingPowerSum α j = 0) ∧
    garlingPowerSum α (2 * n - 2) = ((n - 1 : ℕ) : L) * (algebraMap K L p) ^ 2 := by
  let f : K[X] := Polynomial.X ^ n + Polynomial.C p * Polynomial.X + Polynomial.C q
  have hcoeff : ∀ k : ℕ, f.coeff k =
      if k = n then 1 else if k = 1 then p else if k = 0 then q else 0 := by
    intro k
    dsimp [f]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    have hn1 : n ≠ 1 := by omega
    have hn0 : n ≠ 0 := by omega
    by_cases hkn : k = n
    · subst k; simp [hn0, show (1 : ℕ) ≠ n by omega]
    · by_cases hk1 : k = 1
      · subst k; simp [hkn]
      · by_cases hk0 : k = 0
        · subst k; simp [hkn]
        · have h1k : 1 ≠ k := Ne.symm hk1
          simp [hkn, hk1, h1k, hk0]
  have hf_deg : f.natDegree = n := by
    apply le_antisymm
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
      rw [hcoeff k]
      have h1 : k ≠ n := by omega
      have h2 : k ≠ 1 := by omega
      have h3 : k ≠ 0 := by omega
      simp [h1, h2, h3]
    · refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [hcoeff n]
      simp
  have hf0 : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hc_top : f.coeff n = 1 := by rw [hcoeff n]; simp
  obtain ⟨hN1, hN2⟩ := exercise_14_2_iii hf0 hf_deg (hc_top.symm ▸ hexp)
  -- 1. `λ_j = 0` for `1 ≤ j ≤ n - 2` by strong induction on `j`
  have h1 : ∀ j : ℕ, 1 ≤ j → j ≤ n - 2 → garlingPowerSum α j = 0 := by
    intro j hj1 hjn
    induction j using Nat.strong_induction_on with
    | h j ih =>
      have hNj := hN1 j hj1 (by omega)
      have hcnj : f.coeff (n - j) = 0 := by
        rw [hcoeff (n - j)]
        have : n - j ≠ n := by omega
        have : n - j ≠ 1 := by omega
        have : n - j ≠ 0 := by omega
        simp [*]
      have hIcc_split : Finset.Icc 1 j = insert j (Finset.Icc 1 (j - 1)) := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hj_notin : j ∉ Finset.Icc 1 (j - 1) := by simp only [Finset.mem_Icc]; omega
      rw [hcnj, map_zero, mul_zero, zero_add, hIcc_split, Finset.sum_insert hj_notin] at hNj
      have hrest0 : ∑ x ∈ Finset.Icc 1 (j - 1),
          algebraMap K L (f.coeff (n - j + x)) * garlingPowerSum α x = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
        have hxj : x < j := by have := (Finset.mem_Icc.mp hx).2; omega
        rw [ih x hxj hx1 (by omega), mul_zero]
      have htop : n - j + j = n := by omega
      rw [hrest0, add_zero, htop, hc_top, map_one, one_mul] at hNj
      exact hNj
  -- 2. `λ_{n-1} = -(n - 1) p`
  have h2 : garlingPowerSum α (n - 1) = -(((n - 1 : ℕ) : L) * algebraMap K L p) := by
    have hNm := hN1 (n - 1) (by omega) (by omega)
    have hsub1 : n - (n - 1) = 1 := by omega
    have hc1 : f.coeff 1 = p := by rw [hcoeff 1]; simp [show (1 : ℕ) ≠ n by omega]
    have hIcc_split : Finset.Icc 1 (n - 1) = insert (n - 1) (Finset.Icc 1 (n - 2)) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotin : n - 1 ∉ Finset.Icc 1 (n - 2) := by simp only [Finset.mem_Icc]; omega
    rw [hsub1, hc1, hIcc_split, Finset.sum_insert hnotin] at hNm
    have hrest0 : ∑ x ∈ Finset.Icc 1 (n - 2),
        algebraMap K L (f.coeff (1 + x)) * garlingPowerSum α x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [h1 x (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2, mul_zero]
    have htop : 1 + (n - 1) = n := by omega
    rw [hrest0, add_zero, htop, hc_top, map_one, one_mul] at hNm
    linear_combination hNm
  -- 3. `λ_n = -n q`
  have h3 : garlingPowerSum α n = -((n : L) * algebraMap K L q) := by
    have hNn := hN1 n (by omega) (le_refl n)
    have hc0 : f.coeff 0 = q := by rw [hcoeff 0]; simp [show (0 : ℕ) ≠ n by omega]
    have hIcc_split : Finset.Icc 1 n = insert n (insert (n - 1) (Finset.Icc 1 (n - 2))) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotin1 : n ∉ insert (n - 1) (Finset.Icc 1 (n - 2)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnotin2 : n - 1 ∉ Finset.Icc 1 (n - 2) := by simp only [Finset.mem_Icc]; omega
    rw [Nat.sub_self, hc0] at hNn
    simp_rw [zero_add] at hNn
    rw [hIcc_split, Finset.sum_insert hnotin1, Finset.sum_insert hnotin2] at hNn
    have hcn1 : f.coeff (n - 1) = 0 := by
      rw [hcoeff (n - 1)]
      have : n - 1 ≠ n := by omega
      have : n - 1 ≠ 1 := by omega
      have : n - 1 ≠ 0 := by omega
      simp [*]
    have hrest0 : ∑ x ∈ Finset.Icc 1 (n - 2),
        algebraMap K L (f.coeff x) * garlingPowerSum α x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [h1 x (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2, mul_zero]
    rw [hc_top, hcn1, map_one, map_zero, zero_mul, one_mul, hrest0, add_zero, add_zero] at hNn
    linear_combination hNn
  -- Helper simplifying the `k ≥ 1` recurrence `q λ_k + p λ_{k+1} + λ_{k+n} = 0`
  have hrec : ∀ k : ℕ, 1 ≤ k →
      algebraMap K L q * garlingPowerSum α k +
        algebraMap K L p * garlingPowerSum α (k + 1) +
        garlingPowerSum α (k + n) = 0 := by
    intro k hk1
    have hNk := hN2 k hk1
    have hsplit_r : Finset.range (n + 1) = insert 0 (insert 1 (insert n (Finset.Icc 2 (n - 1)))) := by
      ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    have hn0 : (0 : ℕ) ∉ insert 1 (insert n (Finset.Icc 2 (n - 1))) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hn1 : (1 : ℕ) ∉ insert n (Finset.Icc 2 (n - 1)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnn : n ∉ Finset.Icc 2 (n - 1) := by simp only [Finset.mem_Icc]; omega
    rw [hsplit_r, Finset.sum_insert hn0, Finset.sum_insert hn1, Finset.sum_insert hnn] at hNk
    have hmid0 : ∑ x ∈ Finset.Icc 2 (n - 1),
        algebraMap K L (f.coeff x) * garlingPowerSum α (k + x) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx_bounds := Finset.mem_Icc.mp hx
      have hcx : f.coeff x = 0 := by
        rw [hcoeff x]
        have : x ≠ n := by omega
        have : x ≠ 1 := by omega
        have : x ≠ 0 := by omega
        simp [*]
      rw [hcx, map_zero, zero_mul]
    have hc0 : f.coeff 0 = q := by rw [hcoeff 0]; simp [show (0 : ℕ) ≠ n by omega]
    have hc1 : f.coeff 1 = p := by rw [hcoeff 1]; simp [show (1 : ℕ) ≠ n by omega]
    rw [hc0, hc1, hc_top, map_one, one_mul, hmid0, add_zero, add_zero] at hNk
    linear_combination hNk
  -- 4. `λ_j = 0` for `n + 1 ≤ j ≤ 2n - 3`
  have h4 : ∀ j : ℕ, n + 1 ≤ j → j ≤ 2 * n - 3 → garlingPowerSum α j = 0 := by
    intro j hj_lo hj_hi
    let k : ℕ := j - n
    have hk1 : 1 ≤ k := by omega
    have hkj : k + n = j := by omega
    have hr := hrec k hk1
    rw [hkj, h1 k hk1 (by omega), h1 (k + 1) (by omega) (by omega)] at hr
    simpa using hr
  -- 5. `λ_{2n-2} = (n - 1) p²`
  have h5 : garlingPowerSum α (2 * n - 2) = ((n - 1 : ℕ) : L) * (algebraMap K L p) ^ 2 := by
    have hr := hrec (n - 2) (by omega)
    have hsum_idx : n - 2 + n = 2 * n - 2 := by omega
    have hsucc_idx : n - 2 + 1 = n - 1 := by omega
    rw [hsum_idx, hsucc_idx, h1 (n - 2) (by omega) (le_refl (n - 2)), h2] at hr
    linear_combination hr
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Exercise 14.3 — True discriminant formula for `f = x^n + px + q` (`n ≥ 2`)**
(§14.2, printed p. 113 / PDF p. 121; `BRIEF.md` Flag 1 & `QUEUE.md`):
Across **every** field `K` (arbitrary characteristic) and **every** `n ≥ 2`, the discriminant of
`f = x^n + px + q` is
`Δ = η_n n^n q^{n-1} - η_{n+1} (n - 1)^{n-1} p^n`
(whereas Garling's printed formula swaps `η_n ↔ η_{n+1}`, negating `Δ` for every odd `n ≥ 3`). -/
theorem exercise_14_3_discriminant {K : Type u} [Field K] {n : ℕ} (hn2 : 2 ≤ n) (p q : K) :
    garlingDiscriminant (Polynomial.X ^ n + Polynomial.C p * Polynomial.X + Polynomial.C q) =
      (garlingEta n : K) * (n : K) ^ n * q ^ (n - 1) -
        (garlingEta (n + 1) : K) * ((n - 1 : ℕ) : K) ^ (n - 1) * p ^ n := by
  let f : K[X] := Polynomial.X ^ n + Polynomial.C p * Polynomial.X + Polynomial.C q
  have hf_mon : f.Monic := by
    dsimp [f]
    have hdeg_lt : (Polynomial.C p * Polynomial.X + Polynomial.C q).natDegree < n := by
      compute_degree!
    rw [add_assoc]
    exact Polynomial.monic_X_pow_add ( Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm => by
      have : (Polynomial.C p * Polynomial.X + Polynomial.C q).natDegree < m := by omega
      exact Polynomial.coeff_eq_zero_of_natDegree_lt this )
  have hf_deg : f.natDegree = n := by
    dsimp [f]
    rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow n
    · compute_degree!
  let L := Polynomial.SplittingField f
  let _ : Field L := Polynomial.SplittingField.instField f
  let _ : Algebra K L := Polynomial.SplittingField.instAlgebra f
  have hsf : IsGarlingSplittingFieldExtension K L f :=
    (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
  obtain ⟨m, c, α, hexp⟩ := hsf.1
  have hc : c = 1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).1.trans hf_mon.leadingCoeff
  have hm : m = n := by
    have h1 := (garlingSplitsExplicit_props hf_mon.ne_zero hexp).2.2.1
    simpa [garlingDegree, hf_deg] using h1
  subst m hc
  apply (algebraMap K L).injective
  rw [exercise_14_1 hf_mon hexp]
  have hdf : garlingDeriv f = Polynomial.C (n : K) * Polynomial.X ^ (n - 1) + Polynomial.C p := by
    rw [garlingDeriv_eq_derivative]
    dsimp [f]
    simp [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_mul]
  let pL : L := algebraMap K L p
  let qL : L := algebraMap K L q
  have hdf_eval : ∀ j : Fin n,
      Polynomial.aeval (α j) (garlingDeriv f) = (n : L) * (α j) ^ (n - 1) + pL := by
    intro j
    rw [hdf]
    simp [pL]
  have hroot_eq : ∀ j : Fin n, (α j) ^ n = -pL * (α j) - qL := by
    intro j
    have hr : Polynomial.aeval (α j) f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul,
        Polynomial.eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
      simp
    simp only [f, map_add, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hr
    linear_combination hr
  have hmul_df : ∀ j : Fin n,
      α j * Polynomial.aeval (α j) (garlingDeriv f) =
        -(((n - 1 : ℕ) : L) * pL) * α j - (n : L) * qL := by
    intro j
    rw [hdf_eval j]
    have hpow : α j * (α j) ^ (n - 1) = (α j) ^ n := by
      conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ']
    have hcast_n : (n : L) - ((n - 1 : ℕ) : L) = 1 := by
      have h1 : (n - 1) + 1 = n := by omega
      have hc : (((n - 1) + 1 : ℕ) : L) = (n : L) := congrArg Nat.cast h1
      push_cast at hc
      linear_combination -hc
    calc α j * ((n : L) * (α j) ^ (n - 1) + pL)
        = (n : L) * (α j * (α j) ^ (n - 1)) + pL * α j := by ring
      _ = (n : L) * (-pL * α j - qL) + pL * α j := by rw [hpow, hroot_eq j]
      _ = -(((n - 1 : ℕ) : L) * pL) * α j - (n : L) * qL := by
            linear_combination -hcast_n * pL * α j
  -- Product of roots: `∏ j, α j = (-1)^n * qL`
  have hprod_eval : ∀ x : L,
      (∏ j : Fin n, (x - α j)) = x ^ n + pL * x + qL := by
    intro x
    have he := congrArg (Polynomial.eval x) hexp
    simpa [f, GarlingSplitsExplicit, pL, qL, Polynomial.eval_prod] using he.symm
  have hprod_roots : ∏ j : Fin n, α j = (-1 : L) ^ n * qL := by
    have h0 := hprod_eval 0
    have hneg : (∏ j : Fin n, (0 - α j)) = (-1 : L) ^ n * ∏ j : Fin n, α j := by
      have : ∀ j : Fin n, (0 : L) - α j = (-1 : L) * α j := fun j => by ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    rw [hneg, zero_pow (by omega), mul_zero, add_zero, zero_add] at h0
    calc ∏ j : Fin n, α j
        = (-1 : L) ^ n * ((-1 : L) ^ n * ∏ j : Fin n, α j) := by
            rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
      _ = (-1 : L) ^ n * qL := by rw [h0]
  -- Three-way case split on `q = 0`, `q ≠ 0 ∧ (n - 1)p = 0`, `q ≠ 0 ∧ (n - 1)p ≠ 0`
  by_cases hq0 : q = 0
  · subst hq0
    have hqL0 : qL = 0 := map_zero _
    have h0_mem : ∃ j₀ : Fin n, α j₀ = 0 := by
      have hp0 : ∏ j : Fin n, α j = 0 := by rw [hprod_roots, hqL0, mul_zero]
      obtain ⟨j₀, _, hj₀⟩ := Finset.prod_eq_zero_iff.mp hp0
      exact ⟨j₀, hj₀⟩
    obtain ⟨j₀, hj₀⟩ := h0_mem
    -- Factor `(X - 0)` out of `X^n + pL * X = X * (X^{n-1} + pL)`
    have hrest_poly : ∏ j ∈ Finset.univ.erase j₀, (Polynomial.X - Polynomial.C (α j)) =
        Polynomial.X ^ (n - 1) + Polynomial.C pL := by
      have hfac1 : f.map (algebraMap K L) =
          Polynomial.X * ∏ j ∈ Finset.univ.erase j₀, (Polynomial.X - Polynomial.C (α j)) := by
        rw [hexp, map_one, map_one, one_mul,
          ← Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (α j))
            (Finset.mem_univ j₀), hj₀, map_zero, sub_zero]
      have hfac2 : f.map (algebraMap K L) =
          Polynomial.X * (Polynomial.X ^ (n - 1) + Polynomial.C pL) := by
        dsimp [f]
        simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, map_zero, add_zero]
        have hxn : (Polynomial.X : L[X]) ^ n = Polynomial.X * Polynomial.X ^ (n - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
          rw [pow_succ']
        rw [hxn]
        ring
      exact mul_left_cancel₀ Polynomial.X_ne_zero (hfac1.symm.trans hfac2)
    have hrest_pow : ∀ j ∈ Finset.univ.erase j₀, (α j) ^ (n - 1) = -pL := by
      intro j hj
      have hev := congrArg (Polynomial.eval (α j)) hrest_poly
      rw [Polynomial.eval_prod, Finset.prod_eq_zero hj (by simp)] at hev
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at hev
      linear_combination -hev
    rw [← Finset.mul_prod_erase Finset.univ (fun j => Polynomial.aeval (α j) (garlingDeriv f))
      (Finset.mem_univ j₀)]
    have hdf_j0 : Polynomial.aeval (α j₀) (garlingDeriv f) = pL := by
      rw [hdf_eval j₀, hj₀, zero_pow (by omega), mul_zero, zero_add]
    have hdf_other : ∀ j ∈ Finset.univ.erase j₀,
        Polynomial.aeval (α j) (garlingDeriv f) = -(((n - 1 : ℕ) : L) * pL) := by
      intro j hj
      rw [hdf_eval j, hrest_pow j hj]
      have hcast_n : (n : L) - ((n - 1 : ℕ) : L) = 1 := by
        have h1 : (n - 1) + 1 = n := by omega
        have hc : (((n - 1) + 1 : ℕ) : L) = (n : L) := congrArg Nat.cast h1
        push_cast at hc
        linear_combination -hc
      linear_combination -hcast_n * pL
    rw [hdf_j0, Finset.prod_congr rfl hdf_other, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_fin]
    have h0pow : (0 : K) ^ (n - 1) = 0 := zero_pow (by omega)
    rw [h0pow, mul_zero, zero_sub, garlingEta_succ]
    simp only [map_neg, map_mul, map_intCast, map_natCast, map_pow, pL]
    have hneg_pow : (-(((n - 1 : ℕ) : L) * algebraMap K L p)) ^ (n - 1) =
        (-1 : L) ^ (n - 1) * ((n - 1 : ℕ) : L) ^ (n - 1) * (algebraMap K L p) ^ (n - 1) := by
      calc (-(((n - 1 : ℕ) : L) * algebraMap K L p)) ^ (n - 1)
          = ((-1 : L) * ((n - 1 : ℕ) : L) * algebraMap K L p) ^ (n - 1) := by ring
        _ = _ := by rw [mul_pow, mul_pow]
    rw [hneg_pow]
    have hp_combine : algebraMap K L p * (algebraMap K L p) ^ (n - 1) = (algebraMap K L p) ^ n := by
      conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ']
    have hsign_n : (-1 : L) ^ (n - 1) = -((-1 : L) ^ n) := by
      conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ]
      ring
    push_cast
    rw [hsign_n]
    linear_combination -(garlingEta n : L) * (-1 : L) ^ n * ((n - 1 : ℕ) : L) ^ (n - 1) * hp_combine
  · have hqL_ne0 : qL ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hq0
    have hsign_ne0 : (-1 : L) ^ n ≠ 0 := pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)
    by_cases hnp0 : ((n - 1 : ℕ) : L) * pL = 0
    · -- Case `q ≠ 0` and `(n - 1)p = 0`: `((n - 1)^{n-1} p^n) = 0` and `∏ Df(α_j) = n^n q^{n-1}`
      have hterm2_zero : ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n = 0 := by
        rcases mul_eq_zero.mp hnp0 with hn10 | hp0
        · rw [hn10, zero_pow (by omega), zero_mul]
        · rw [hp0, zero_pow (by omega), mul_zero]
      have hprod_mul : (∏ j : Fin n, α j) *
          (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) =
          (-1 : L) ^ n * (n : L) ^ n * qL ^ n := by
        rw [← Finset.prod_mul_distrib]
        have heach : ∀ j : Fin n, α j * Polynomial.aeval (α j) (garlingDeriv f) = -(n : L) * qL := by
          intro j; rw [hmul_df j, hnp0]; ring
        simp_rw [heach]
        rw [Finset.prod_const, Finset.card_fin]
        calc (-(n : L) * qL) ^ n = ((-1 : L) * (n : L) * qL) ^ n := by ring
          _ = (-1 : L) ^ n * (n : L) ^ n * qL ^ n := by rw [mul_pow, mul_pow]
      have hqn : qL ^ n = qL * qL ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
        rw [pow_succ']
      rw [hprod_roots, hqn] at hprod_mul
      have hprod_df : (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) =
          (n : L) ^ n * qL ^ (n - 1) := by
        apply mul_left_cancel₀ (mul_ne_zero hsign_ne0 hqL_ne0)
        linear_combination hprod_mul
      rw [hprod_df]
      simp only [map_sub, map_mul, map_intCast, map_natCast, map_pow]
      dsimp only [pL] at hterm2_zero
      rw [mul_assoc (garlingEta (n + 1) : L), hterm2_zero, mul_zero, sub_zero]
      dsimp only [qL]
      ring
    · -- Generic case `q ≠ 0` and `(n - 1)p ≠ 0`
      let u : L := ((n - 1 : ℕ) : L) * pL
      let v : L := -(n : L) * qL
      have hu_ne0 : u ≠ 0 := hnp0
      have hprod_mul : (∏ j : Fin n, α j) *
          (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) =
          v ^ n + u ^ (n - 1) * pL * v + u ^ n * qL := by
        rw [← Finset.prod_mul_distrib]
        have heach : ∀ j : Fin n,
            α j * Polynomial.aeval (α j) (garlingDeriv f) = (-u) * (α j - (v / u)) := by
          intro j
          rw [hmul_df j]
          have h1 : (-u) * (α j - v / u) = -u * α j + u * (v / u) := by ring
          rw [h1, mul_div_cancel₀ v hu_ne0]
          dsimp [u, v]
          ring
        simp_rw [heach]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
        have hflip : (∏ j : Fin n, (α j - v / u)) = (-1 : L) ^ n * ∏ j : Fin n, (v / u - α j) := by
          have : ∀ j : Fin n, α j - v / u = (-1 : L) * (v / u - α j) := fun j => by ring
          simp_rw [this]
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
        rw [hflip, hprod_eval (v / u)]
        have hu_sign : (-u) ^ n * (-1 : L) ^ n = u ^ n := by
          rw [← mul_pow]
          congr 1
          ring
        calc (-u) ^ n * ((-1 : L) ^ n * ((v / u) ^ n + pL * (v / u) + qL))
            = u ^ n * ((v / u) ^ n + pL * (v / u) + qL) := by
                rw [← mul_assoc, hu_sign]
          _ = u ^ n * (v / u) ^ n + (u * u ^ (n - 1)) * (pL * (v / u)) + u ^ n * qL := by
                have hun : u ^ n = u * u ^ (n - 1) := by
                  conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
                  rw [pow_succ']
                conv_lhs => rw [mul_add, mul_add]
                congr 1; congr 1; rw [hun]
          _ = v ^ n + u ^ (n - 1) * pL * v + u ^ n * qL := by
                have hdiv_pow : u ^ n * (v / u) ^ n = v ^ n := by
                  rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n hu_ne0)]
                have hdiv_1 : (u * u ^ (n - 1)) * (pL * (v / u)) = u ^ (n - 1) * pL * v := by
                  calc (u * u ^ (n - 1)) * (pL * (v / u))
                      = u ^ (n - 1) * pL * (u * (v / u)) := by ring
                    _ = u ^ (n - 1) * pL * v := by rw [mul_div_cancel₀ v hu_ne0]
                rw [hdiv_pow, hdiv_1]
      -- Simplify RHS of `hprod_mul` in terms of `pL, qL`
      have hrhs_simp : v ^ n + u ^ (n - 1) * pL * v + u ^ n * qL =
          qL * ((-1 : L) ^ n * (n : L) ^ n * qL ^ (n - 1) -
            ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n) := by
        have hvn : v ^ n = (-1 : L) ^ n * (n : L) ^ n * (qL * qL ^ (n - 1)) := by
          dsimp [v]
          have hqn : qL ^ n = qL * qL ^ (n - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
            rw [pow_succ']
          calc (-(n : L) * qL) ^ n = ((-1 : L) * (n : L) * qL) ^ n := by ring
            _ = (-1 : L) ^ n * (n : L) ^ n * qL ^ n := by rw [mul_pow, mul_pow]
            _ = _ := by rw [hqn]
        have hu1 : u ^ (n - 1) * pL * v =
            -(n : L) * ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n * qL := by
          dsimp [u, v]
          rw [mul_pow]
          have hpn : pL ^ (n - 1) * pL = pL ^ n := by
            conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
            rw [pow_succ]
          linear_combination -(n : L) * ((n - 1 : ℕ) : L) ^ (n - 1) * qL * hpn
        have hu2 : u ^ n * qL =
            ((n - 1 : ℕ) : L) * ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n * qL := by
          dsimp [u]
          rw [mul_pow]
          have hn_eq : n = (n - 1) + 1 := by omega
          have hn1_pow : ((n - 1 : ℕ) : L) ^ n =
              ((n - 1 : ℕ) : L) * ((n - 1 : ℕ) : L) ^ (n - 1) := by
            conv_lhs => rhs; rw [hn_eq]
            rw [pow_succ']
          rw [hn1_pow]
        have hcast_n : ((n - 1 : ℕ) : L) - (n : L) = -1 := by
          have h1 : (n - 1) + 1 = n := by omega
          have hc : (((n - 1) + 1 : ℕ) : L) = (n : L) := congrArg Nat.cast h1
          push_cast at hc
          linear_combination hc
        rw [hvn, hu1, hu2]
        linear_combination ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n * qL * hcast_n
      rw [hprod_roots, hrhs_simp] at hprod_mul
      have hprod_df : (∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)) =
          (n : L) ^ n * qL ^ (n - 1) -
            (-1 : L) ^ n * ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n := by
        apply mul_left_cancel₀ (mul_ne_zero hsign_ne0 hqL_ne0)
        have hsq_neg1 : (-1 : L) ^ n * (-1 : L) ^ n = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; simp
        calc (-1 : L) ^ n * qL * ∏ j : Fin n, Polynomial.aeval (α j) (garlingDeriv f)
            = qL * ((-1 : L) ^ n * (n : L) ^ n * qL ^ (n - 1) -
                ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n) := hprod_mul
          _ = (-1 : L) ^ n * qL *
                ((n : L) ^ n * qL ^ (n - 1) -
                  (-1 : L) ^ n * ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n) := by
                rw [mul_sub, mul_sub]
                congr 1
                · ring
                · calc qL * (((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n)
                      = ((-1 : L) ^ n * (-1 : L) ^ n) *
                          (qL * (((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n)) := by
                          rw [hsq_neg1, one_mul]
                    _ = (-1 : L) ^ n * qL *
                          ((-1 : L) ^ n * ((n - 1 : ℕ) : L) ^ (n - 1) * pL ^ n) := by ring
      rw [hprod_df, garlingEta_succ]
      simp only [map_sub, map_mul, map_intCast, map_natCast, map_pow, pL, qL]
      push_cast
      ring

/-- Exact relationship between Garling's **printed** formula in `Exercise 14.3`
(`η_{n+1} n^n q^{n-1} - η_n (n - 1)^{n-1} p^n`) and the true discriminant (`n ≥ 2`):
`Δ_printed = (-1)^n Δ` — agreeing with `Δ` for all even `n ≥ 2` and negating `Δ` for all odd
`n ≥ 3`. -/
theorem exercise_14_3_printed_eq_neg_one_pow_mul_disc {K : Type u} [Field K] {n : ℕ}
    (hn2 : 2 ≤ n) (p q : K) :
    ((garlingEta (n + 1) : K) * (n : K) ^ n * q ^ (n - 1) -
        (garlingEta n : K) * ((n - 1 : ℕ) : K) ^ (n - 1) * p ^ n) =
      (-1 : K) ^ n *
        garlingDiscriminant (Polynomial.X ^ n + Polynomial.C p * Polynomial.X + Polynomial.C q) := by
  rw [exercise_14_3_discriminant hn2 p q, garlingEta_succ]
  have hsq : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  push_cast
  linear_combination ((garlingEta n : K) * ((n - 1 : ℕ) : K) ^ (n - 1) * p ^ n) * hsq

/-- **Kernel-proved counterexample to the printed discriminant formula of `Exercise 14.3` at odd
`n = 3`** (`BRIEF.md` Flag 1 & `QUEUE.md`):
For `n = 3` and `f = x³ + 1 ∈ ℚ[x]` (`p = 0, q = 1`), the true discriminant is `Δ = -27` (matching
p. 112's `garlingDiscriminant_monic_cubic`), whereas Garling's printed formula
`η₄ 3³ · 1² - η₃ 2² · 0³` evaluates to `+27 ≠ -27`. -/
theorem exercise_14_3_odd_counterexample :
    let f : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X + Polynomial.C 1
    let Δ_printed : ℚ :=
      (garlingEta (3 + 1) : ℚ) * (3 : ℚ) ^ 3 * (1 : ℚ) ^ (3 - 1) -
        (garlingEta 3 : ℚ) * ((3 - 1 : ℕ) : ℚ) ^ (3 - 1) * (0 : ℚ) ^ 3
    garlingDiscriminant f = -27 ∧
    Δ_printed = 27 ∧
    garlingDiscriminant f ≠ Δ_printed := by
  intro f Δ_printed
  have htrue : garlingDiscriminant f = -27 := by
    rw [exercise_14_3_discriminant (by decide : 2 ≤ 3) (0 : ℚ) (1 : ℚ)]
    norm_num [garlingEta]
  have hprint : Δ_printed = 27 := by
    dsimp [Δ_printed]
    norm_num [garlingEta]
  exact ⟨htrue, hprint, by rw [htrue, hprint]; norm_num⟩

/-! #### Exercise 14.4: Characteristic `2` Square Root & Counterexample to Theorem 14.1 (p. 113) -/

/-- **Exercise 14.4 — Part 1** (§14.2, printed p. 113 / PDF p. 121):
Over any field `K` of characteristic `2`, the discriminant of `f ∈ K[x]` always has a square root
in `K` (holding for all `f ∈ K[x]`, including every Garling-separable or Mathlib-separable `f`,
even over imperfect fields of characteristic `2`). -/
theorem exercise_14_4_sqrt_in_char_two {K : Type u} [Field K] (hchar2 : ringChar K = 2)
    (f : K[X]) :
    ∃ d : K, d ^ 2 = garlingDiscriminant f := by
  by_cases hf0 : f = 0
  · subst hf0
    exact ⟨0, by simp⟩
  · let L := Polynomial.SplittingField f
    have hsf : IsGarlingSplittingFieldExtension K L f :=
      (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
    obtain ⟨n, c, α, hexp⟩ := hsf.1
    by_cases hinj : Function.Injective α
    · have hf_sep : f.Separable :=
        (injective_roots_iff_separable_and_not_repeated hf0 hexp).1.mp hinj
      have hgar_sep : IsGarlingSeparablePoly f :=
        ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
      have hfixed : (algebraMap K L).fieldRange =
          garlingPhi (garlingPolyGaloisSubgroup K L f : Set (GarlingAut L)) :=
        (theorem_11_5 hf0 hsf).1 hgar_sep |>.2.2
      have h2K : (2 : K) = 0 := by
        have h := ringChar.Nat.cast_ringChar (R := K)
        rw [hchar2] at h
        simpa using h
      have h2L : (2 : L) = 0 := by
        have hm : algebraMap K L (2 : K) = (2 : L) := map_ofNat (algebraMap K L) 2
        rw [← hm, h2K, map_zero]
      have hneg1_eq_1 : (-1 : L) = 1 := by linear_combination -h2L
      have hδ_in_K : garlingDeltaTuple α ∈ (algebraMap K L).fieldRange := by
        rw [hfixed]
        intro τ hτ
        let σ : GarlingPolyGaloisGroup K L f := (garlingGaloisGroupMulEquiv K L).symm ⟨τ, hτ⟩
        have hexp_σ : GarlingSplitsExplicit K L f n c (σ ∘ α) := by
          have hmap : (f.map (algebraMap K L)).map σ.toRingHom = f.map (algebraMap K L) := by
            rw [Polynomial.map_map]
            congr 1
            exact RingHom.ext fun k => σ.commutes k
          have h1 := congrArg (Polynomial.map σ.toRingHom) hexp
          rw [hmap, Polynomial.map_mul, Polynomial.map_C] at h1
          have hc_comm : σ.toRingHom (algebraMap K L c) = algebraMap K L c := σ.commutes c
          rw [hc_comm, Polynomial.map_prod] at h1
          simpa [GarlingSplitsExplicit] using h1
        obtain ⟨π, hπ⟩ := garlingSplitsExplicit_perm_of_ne_zero hf0 hexp hexp_σ
        change σ.toRingHom (garlingDeltaTuple α) = garlingDeltaTuple α
        have hcomp_σ : (σ.toRingHom ∘ α) = α ∘ π := hπ
        rw [map_garlingDeltaTuple σ.toRingHom α, hcomp_σ, garlingDeltaTuple_comp_perm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | hm1
        · simp [h1]
        · simp [hm1, hneg1_eq_1]
      rcases hδ_in_K with ⟨d, hd⟩
      refine ⟨d, (algebraMap K L).injective ?_⟩
      rw [map_pow, hd, garlingDiscriminant_eq_discTuple hf0 hexp, garlingDiscTuple]
    · refine ⟨0, (algebraMap K L).injective ?_⟩
      rw [map_pow, map_zero, zero_pow (by decide),
        garlingDiscriminant_eq_discTuple hf0 hexp, garlingDiscTuple,
        (garlingDeltaTuple_eq_zero_iff α).mpr hinj, zero_pow (by decide)]

/-- **Exercise 14.4 — Part 2 concrete counterexample over `ℤ₂`** (§14.2, printed p. 113 /
PDF p. 121):
For `K = ZMod 2` (`char K = 2`) and `f = x² + x + 1 ∈ ℤ₂[x]` (`zmod2IrredQuad`), `f` is irreducible
and separable with discriminant `Δ = 1 ≠ 0` (`1 = 1² ∈ ℤ₂`), yet in its splitting field
`ZMod2QuadField` (`𝔽₄`), `|Γ_{ℤ₂}(f)| = 2` while `|A₂| = 1`, so `Γ_{ℤ₂}(f) ⊄ A₂` — refuting
conclusion `(ii)` of `Theorem 14.1` in characteristic `2`. -/
theorem exercise_14_4_counterexample_zmod2 :
    let K := ZMod 2
    let f : K[X] := zmod2IrredQuad
    let L := ZMod2QuadField
    ringChar K = 2 ∧
    IsGarlingSeparablePoly f ∧
    f.Separable ∧
    IsGarlingSplittingFieldExtension K L f ∧
    garlingDiscriminant f = 1 ∧
    garlingDiscriminant f ≠ 0 ∧
    (∃ d : K, d ^ 2 = garlingDiscriminant f) ∧
    ∀ e : Fin f.natDegree ≃ garlingRootSet K L f,
      ¬ ∀ σ : GarlingPolyGaloisGroup K L f,
          garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin f.natDegree) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K f L
  obtain ⟨_, _, _, _, _, hfin2, hsf, _⟩ := example_7_3_4_zmod2
  have hf_eq : f = Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C 1 := by
    simp [f, zmod2IrredQuad]
  have hf_deg : f.natDegree = 2 := by
    rw [hf_eq]
    compute_degree!
  have hdisc1 : garlingDiscriminant f = 1 := by
    rw [hf_eq, garlingDiscriminant_monic_quadratic]
    have h4 : (4 : ZMod 2) = 0 := rfl
    rw [h4]
    ring
  have hdisc_ne0 : garlingDiscriminant f ≠ 0 := by
    rw [hdisc1]
    exact one_ne_zero
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hf0 : f ≠ 0 := zmod2IrredQuad_irreducible.ne_zero
  have hinj : Function.Injective α := by
    by_contra hninj
    have h0 : garlingDeltaTuple α = 0 := (garlingDeltaTuple_eq_zero_iff α).mpr hninj
    have hd0 : algebraMap K L (garlingDiscriminant f) = 0 := by
      rw [garlingDiscriminant_eq_discTuple hf0 hexp, garlingDiscTuple, h0, zero_pow (by decide)]
    exact hdisc_ne0 ((map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp hd0)
  have hf_sep : f.Separable :=
    (injective_roots_iff_separable_and_not_repeated hf0 hexp).1.mp hinj
  have hgar_sep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hf_sep).2.2
  have hcardG : Nat.card (GarlingPolyGaloisGroup K L f) = 2 := by
    rw [(theorem_11_5 hf0 hsf).1 hgar_sep |>.2.1, hfin2]
  refine ⟨ZMod.ringChar_zmod_n 2, hgar_sep, hf_sep, hsf, hdisc1, hdisc_ne0,
    ⟨1, by rw [hdisc1, one_pow]⟩, fun e hall => ?_⟩
  have hinj_hom : Function.Injective (garlingRootLabellingPermHom e) := by
    intro σ₁ σ₂ h12
    apply theorem_11_6 hsf
    ext x
    have hx := Equiv.congr_fun h12 (e.symm x)
    have hx' := congrArg (fun k => (e k : L)) hx
    simpa [garlingRootLabellingPermHom] using hx'
  -- Every element of `alternatingGroup (Fin 2)` equals `1`
  have fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  have halt_sub : ∀ π : SigmaN 2, π ∈ alternatingGroup (Fin 2) → π = 1 := by
    intro π hπ
    have hsign : Equiv.Perm.sign π = 1 := Equiv.Perm.mem_alternatingGroup.mp hπ
    rcases fin2_cases (π 0) with h0 | h0
    · rcases fin2_cases (π 1) with h1 | h1
      · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
      · apply Equiv.ext; intro i; fin_cases i <;> assumption
    · rcases fin2_cases (π 1) with h1 | h1
      · have hswap : π = Equiv.swap 0 1 := by
          apply Equiv.ext; intro i; fin_cases i <;> simp [h0, h1]
        rw [hswap, Equiv.Perm.sign_swap (by decide)] at hsign
        exact absurd hsign (by decide)
      · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
  have hsubG : Subsingleton (GarlingPolyGaloisGroup K L f) := by
    refine ⟨fun σ₁ σ₂ => ?_⟩
    revert e hall hinj_hom
    rw [hf_deg]
    intro e hall hinj_hom
    exact hinj_hom ((halt_sub _ (hall σ₁)).trans (halt_sub _ (hall σ₂)).symm)
  have hcard1 : Nat.card (GarlingPolyGaloisGroup K L f) = 1 :=
    @Nat.card_unique (GarlingPolyGaloisGroup K L f) ⟨1⟩ hsubG
  omega

/-- **Exercise 14.4** (§14.2, printed p. 113 / PDF p. 121):
*"Suppose that `char K = 2` and that `f ∈ K[x]` is separable. Show that the discriminant of `f`
always has a square root in `K`. Give an example to show that Theorem 14.1 does not hold for fields
of characteristic `2`."* -/
theorem exercise_14_4 :
    (∀ (K : Type u) [Field K], ringChar K = 2 →
      ∀ f : K[X], IsGarlingSeparablePoly f → ∃ d : K, d ^ 2 = garlingDiscriminant f) ∧
    (∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (f : K[X]),
      ringChar K = 2 ∧
      IsGarlingSeparablePoly f ∧
      IsGarlingSplittingFieldExtension K L f ∧
      garlingDiscriminant f ≠ 0 ∧
      (∃ d : K, d ^ 2 = garlingDiscriminant f) ∧
      Nonempty (Fin f.natDegree ≃ garlingRootSet K L f) ∧
      ∀ e : Fin f.natDegree ≃ garlingRootSet K L f,
        ¬ ∀ σ : GarlingPolyGaloisGroup K L f,
            garlingRootLabellingPermHom e σ ∈ alternatingGroup (Fin f.natDegree)) := by
  refine ⟨fun K _ hchar2 f _ => exercise_14_4_sqrt_in_char_two hchar2 f, ?_⟩
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hchar, hsep, hf_sep, hsf, _, hdisc_ne, hsq, hnotA⟩ := exercise_14_4_counterexample_zmod2
  obtain ⟨m, c, α, hexp⟩ := hsf.1
  have hf0 : zmod2IrredQuad ≠ 0 := zmod2IrredQuad_irreducible.ne_zero
  have hm : m = zmod2IrredQuad.natDegree := by
    have h1 := (garlingSplitsExplicit_props hf0 hexp).2.2.1
    simpa [garlingDegree] using h1
  subst hm
  have hinj : Function.Injective α :=
    (injective_roots_iff_separable_and_not_repeated hf0 hexp).1.mpr hf_sep
  have hrange : Set.range α = garlingRootSet (ZMod 2) ZMod2QuadField zmod2IrredQuad := by
    rw [garlingRootSet_eq_rootSet hf0]
    exact (garlingSplitsExplicit_props hf0 hexp).2.2.2
  let e_set : Set.range α ≃ garlingRootSet (ZMod 2) ZMod2QuadField zmod2IrredQuad :=
    { toFun := fun x => ⟨x.1, hrange ▸ x.2⟩
      invFun := fun y => ⟨y.1, hrange.symm ▸ y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨ZMod 2, ZMod2QuadField, inferInstance, inferInstance, inferInstance, zmod2IrredQuad,
    hchar, hsep, hsf, hdisc_ne, hsq, ⟨(Equiv.ofInjective α hinj).trans e_set⟩, hnotA⟩

/-! ## §14.3 Cubic polynomials (printed pp. 113–115, PDF pp. 121–123)

Unnumbered main-text derivation solving cubics by radicals over fields of characteristic `≠ 2, 3`
(printed pp. 113–115), followed by **Exercise 14.5** (printed p. 115 / PDF p. 123). -/

/-! ### Prefix-Tower Builder and Linear-Shift / Scaling Helpers for §§14.3–14.4 -/

/-- Auxiliary recursive chain `F_k` of intermediate fields generated over `K` by the first `k`
entries of `γ : Fin r → N`. -/
noncomputable def garlingRadPrefixAux (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) : ∀ k : ℕ, k ≤ r → IntermediateField K N
  | 0, _ => ⊥
  | k + 1, hk =>
      IntermediateField.adjoin K
        ((garlingRadPrefixAux K γ k (Nat.le_of_succ_le hk) : Set N) ∪ {γ ⟨k, hk⟩})

/-- Canonical `Fin (r + 1)`-indexed tower of intermediate fields `K = F 0 ≤ F 1 ≤ … ≤ F r` for a
generator tuple `γ : Fin r → N`. -/
noncomputable def garlingRadPrefix (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) (j : Fin (r + 1)) : IntermediateField K N :=
  garlingRadPrefixAux K γ j.val j.is_le

@[simp]
theorem garlingRadPrefix_zero (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) :
    garlingRadPrefix K γ 0 = ⊥ := rfl

@[simp]
theorem garlingRadPrefix_succ (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) (i : Fin r) :
    garlingRadPrefix K γ i.succ =
      IntermediateField.adjoin K ((garlingRadPrefix K γ i.castSucc : Set N) ∪ {γ i}) := rfl

theorem garlingRadPrefix_mono (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) {j₁ j₂ : Fin (r + 1)} (h : j₁ ≤ j₂) :
    garlingRadPrefix K γ j₁ ≤ garlingRadPrefix K γ j₂ := by
  have haux : ∀ a b : ℕ, ∀ (ha : a ≤ r) (hb : b ≤ r), a ≤ b →
      garlingRadPrefixAux K γ a ha ≤ garlingRadPrefixAux K γ b hb := by
    intro a b
    induction b with
    | zero =>
      intro ha hb hab
      have ha0 : a = 0 := by omega
      subst ha0
      exact le_rfl
    | succ b ih =>
      intro ha hb hab
      by_cases hab_eq : a = b + 1
      · subst hab_eq
        exact le_rfl
      · have hab_lt : a ≤ b := by omega
        refine (ih ha (Nat.le_of_succ_le hb) hab_lt).trans ?_
        intro x hx
        exact IntermediateField.subset_adjoin K _ (Or.inl hx)
  exact haux j₁.val j₂.val j₁.is_le j₂.is_le h

theorem garlingRadPrefix_mem_succ (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) (i : Fin r) :
    γ i ∈ garlingRadPrefix K γ i.succ := by
  rw [garlingRadPrefix_succ]
  exact IntermediateField.subset_adjoin K _ (Or.inr rfl)

theorem garlingRadPrefix_mem_of_lt (K : Type u) {N : Type v} [Field K] [Field N] [Algebra K N]
    {r : ℕ} (γ : Fin r → N) {k : Fin r} {j : Fin (r + 1)} (hkj : k.val < j.val) :
    γ k ∈ garlingRadPrefix K γ j := by
  have hle : k.succ ≤ j := by
    change k.val + 1 ≤ j.val
    omega
  exact garlingRadPrefix_mono K γ hle (garlingRadPrefix_mem_succ K γ k)

/-- Tuple criterion for `IsGarlingExtensionByRadicals K N`: if `γ : Fin r → N` generates `N` over
`K` and each `γ i` has a positive power `(γ i) ^ (m i)` in `garlingRadPrefix K γ i.castSucc`, then
`N : K` is an extension by radicals. -/
theorem isGarlingExtensionByRadicals_of_tuple {K : Type u} {N : Type v}
    [Field K] [Field N] [Algebra K N] {r : ℕ} (γ : Fin r → N) (m : Fin r → ℕ)
    (hm_pos : ∀ i : Fin r, 1 ≤ m i)
    (hpow : ∀ i : Fin r, (γ i) ^ (m i) ∈ garlingRadPrefix K γ i.castSucc)
    (hadj : IntermediateField.adjoin K (Set.range γ) = ⊤) :
    IsGarlingExtensionByRadicals K N := by
  refine ⟨r, garlingRadPrefix K γ, γ, rfl, ?_, fun i => ⟨⟨m i, hm_pos i, hpow i⟩, rfl⟩⟩
  rw [eq_top_iff, ← hadj, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact garlingRadPrefix_mem_of_lt K γ i.isLt

/-- Subfield variant of `isGarlingExtensionByRadicals_of_tuple`: for any ambient extension `N : K`
and tuple `γ : Fin r → N` whose powers `(γ i) ^ (m i)` lie in `garlingRadPrefix K γ i.castSucc`,
the intermediate field `IntermediateField.adjoin K (Set.range γ)` itself is an extension of `K` by
radicals (without requiring `γ` to generate all of `N`). -/
theorem isGarlingExtensionByRadicals_adjoin_tuple {K : Type u} {N : Type v}
    [Field K] [Field N] [Algebra K N] {r : ℕ} (γ : Fin r → N) (m : Fin r → ℕ)
    (hm_pos : ∀ i : Fin r, 1 ≤ m i)
    (hpow : ∀ i : Fin r, (γ i) ^ (m i) ∈ garlingRadPrefix K γ i.castSucc) :
    IsGarlingExtensionByRadicals K (IntermediateField.adjoin K (Set.range γ)) := by
  let E : IntermediateField K N := IntermediateField.adjoin K (Set.range γ)
  let γE : Fin r → E := fun i => ⟨γ i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hprefix_le : ∀ k : ℕ, ∀ (hk : k ≤ r),
      garlingRadPrefixAux K γ k hk ≤ (garlingRadPrefixAux K γE k hk).map E.val := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact bot_le
    | succ k ih =>
      intro hk
      change IntermediateField.adjoin K
          ((garlingRadPrefixAux K γ k (Nat.le_of_succ_le hk) : Set N) ∪ {γ ⟨k, hk⟩}) ≤
        (garlingRadPrefixAux K γE (k + 1) hk).map E.val
      rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · rcases ih (Nat.le_of_succ_le hk) hx with ⟨z, hz, rfl⟩
        exact ⟨z, IntermediateField.subset_adjoin K _ (Or.inl hz), rfl⟩
      · exact ⟨γE ⟨k, hk⟩, IntermediateField.subset_adjoin K _ (Or.inr rfl), rfl⟩
  refine isGarlingExtensionByRadicals_of_tuple γE m hm_pos (fun i => ?_) ?_
  · have hmemN : ((γE i ^ m i : E) : N) ∈ garlingRadPrefix K γ i.castSucc := by
      simpa [γE] using hpow i
    rcases hprefix_le i.val i.isLt.le hmemN with ⟨z, hz, hzeq⟩
    have hz_eq : z = γE i ^ m i := E.val.injective hzeq
    rwa [← hz_eq]
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    have hle_map : E ≤ (IntermediateField.adjoin K (Set.range γE)).map E.val := by
      change IntermediateField.adjoin K (Set.range γ) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨γE i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩
    rcases hle_map hx with ⟨z, hz, hzeq⟩
    have hz_eq : z = ⟨x, hx⟩ := E.val.injective hzeq
    rwa [← hz_eq]

/-- Explicit splitting of `f.comp (X + C s)` from an explicit splitting of `f`. -/
theorem garlingSplitsExplicit_comp_X_add_C {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ} {c : K} {α : Fin n → L}
    (hexp : GarlingSplitsExplicit K L f n c α) (s : K) :
    GarlingSplitsExplicit K L (f.comp (Polynomial.X + Polynomial.C s)) n c
      (fun i => α i - algebraMap K L s) := by
  unfold GarlingSplitsExplicit at hexp ⊢
  have hmap_comp : (f.comp (Polynomial.X + Polynomial.C s)).map (algebraMap K L) =
      (f.map (algebraMap K L)).comp (Polynomial.X + Polynomial.C (algebraMap K L s)) := by
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rw [hmap_comp, hexp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
  ring

/-- Inverse identity `(f.comp (X + C s)).comp (X + C (-s)) = f`. -/
theorem comp_X_add_C_neg_cancel {R : Type*} [CommRing R] (f : R[X]) (s : R) :
    (f.comp (Polynomial.X + Polynomial.C s)).comp (Polynomial.X + Polynomial.C (-s)) = f := by
  rw [Polynomial.comp_assoc]
  have hid : (Polynomial.X + Polynomial.C s : R[X]).comp (Polynomial.X + Polynomial.C (-s)) =
      Polynomial.X := by
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_neg]
    ring
  rw [hid, Polynomial.comp_X]

/-- Linear substitution `x ↦ x + s` preserves `garlingDiscriminant` for **every** `f : K[X]`. -/
theorem garlingDiscriminant_comp_X_add_C {K : Type u} [Field K] (f : K[X]) (s : K) :
    garlingDiscriminant (f.comp (Polynomial.X + Polynomial.C s)) = garlingDiscriminant f := by
  by_cases hf0 : f = 0
  · subst hf0
    simp
  · have hg0 : f.comp (Polynomial.X + Polynomial.C s) ≠ 0 := fun h0 => by
      have h := congrArg (fun p : K[X] => p.comp (Polynomial.X + Polynomial.C (-s))) h0
      rw [comp_X_add_C_neg_cancel, Polynomial.zero_comp] at h
      exact hf0 h
    let L := Polynomial.SplittingField f
    let _ : Field L := Polynomial.SplittingField.instField f
    let _ : Algebra K L := Polynomial.SplittingField.instAlgebra f
    have hsf : IsGarlingSplittingFieldExtension K L f :=
      (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
    obtain ⟨n, c, α, hexp⟩ := hsf.1
    have hexp_s := garlingSplitsExplicit_comp_X_add_C hexp s
    apply (algebraMap K L).injective
    rw [garlingDiscriminant_eq_discTuple hg0 hexp_s, garlingDiscriminant_eq_discTuple hf0 hexp]
    have hdelta : garlingDeltaTuple (fun i => α i - algebraMap K L s) = garlingDeltaTuple α := by
      unfold garlingDeltaTuple
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      ring
    rw [garlingDiscTuple, garlingDiscTuple, hdelta]

/-- Linear substitution `x ↦ x + s` preserves `GarlingSplitsOver` and `IsGarlingSolvableByRadicals`. -/
theorem garlingSplitsOver_comp_X_add_C_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (f : K[X]) (s : K) :
    GarlingSplitsOver K L (f.comp (Polynomial.X + Polynomial.C s)) ↔ GarlingSplitsOver K L f := by
  constructor
  · rintro ⟨n, c, α, hexp⟩
    have h := garlingSplitsExplicit_comp_X_add_C hexp (-s)
    rw [comp_X_add_C_neg_cancel] at h
    exact ⟨n, c, _, h⟩
  · rintro ⟨n, c, α, hexp⟩
    exact ⟨n, c, _, garlingSplitsExplicit_comp_X_add_C hexp s⟩

theorem isGarlingSolvableByRadicals_comp_X_add_C_iff {K : Type u} [Field K] (f : K[X]) (s : K) :
    IsGarlingSolvableByRadicals (f.comp (Polynomial.X + Polynomial.C s)) ↔
      IsGarlingSolvableByRadicals f := by
  unfold IsGarlingSolvableByRadicals
  constructor
  · rintro ⟨L, iF, iA, hrad, hsp⟩
    let _ : Field L := iF
    let _ : Algebra K L := iA
    exact ⟨L, iF, iA, hrad, (garlingSplitsOver_comp_X_add_C_iff f s).mp hsp⟩
  · rintro ⟨L, iF, iA, hrad, hsp⟩
    let _ : Field L := iF
    let _ : Algebra K L := iA
    exact ⟨L, iF, iA, hrad, (garlingSplitsOver_comp_X_add_C_iff f s).mpr hsp⟩

/-- Non-zero scalar multiplication preserves `GarlingSplitsOver`, `garlingDiscriminant`, and
`IsGarlingSolvableByRadicals`. -/
theorem garlingSplitsExplicit_C_mul {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} {n : ℕ} {d : K} {α : Fin n → L}
    (c : K) (hexp : GarlingSplitsExplicit K L f n d α) :
    GarlingSplitsExplicit K L (Polynomial.C c * f) n (c * d) α := by
  unfold GarlingSplitsExplicit at hexp ⊢
  rw [Polynomial.map_mul, Polynomial.map_C, hexp, map_mul, Polynomial.C_mul, mul_assoc]

theorem garlingDiscriminant_C_mul {K : Type u} [Field K] {c : K} (hc : c ≠ 0) (f : K[X]) :
    garlingDiscriminant (Polynomial.C c * f) = garlingDiscriminant f := by
  by_cases hf0 : f = 0
  · subst hf0; simp
  · have hcf0 : Polynomial.C c * f ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hf0
    let L := Polynomial.SplittingField f
    let _ : Field L := Polynomial.SplittingField.instField f
    let _ : Algebra K L := Polynomial.SplittingField.instAlgebra f
    have hsf : IsGarlingSplittingFieldExtension K L f :=
      (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
    obtain ⟨n, d, α, hexp⟩ := hsf.1
    apply (algebraMap K L).injective
    rw [garlingDiscriminant_eq_discTuple hcf0 (garlingSplitsExplicit_C_mul c hexp),
      garlingDiscriminant_eq_discTuple hf0 hexp]

theorem isGarlingSolvableByRadicals_C_mul_iff {K : Type u} [Field K] {c : K} (hc : c ≠ 0)
    (f : K[X]) :
    IsGarlingSolvableByRadicals (Polynomial.C c * f) ↔ IsGarlingSolvableByRadicals f := by
  have hsp_mul : ∀ (L : Type u) [Field L] [Algebra K L] {d : K} (hd : d ≠ 0) (p : K[X]),
      GarlingSplitsOver K L p → GarlingSplitsOver K L (Polynomial.C d * p) := by
    intro L _ _ d _ p ⟨n, a, α, hexp⟩
    exact ⟨n, d * a, α, garlingSplitsExplicit_C_mul d hexp⟩
  unfold IsGarlingSolvableByRadicals
  constructor
  · rintro ⟨L, iF, iA, hrad, hsp⟩
    let _ : Field L := iF
    let _ : Algebra K L := iA
    refine ⟨L, iF, iA, hrad, ?_⟩
    have h := hsp_mul L (inv_ne_zero hc) (Polynomial.C c * f) hsp
    have hcancel : Polynomial.C c⁻¹ * (Polynomial.C c * f) = f := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rwa [hcancel] at h
  · rintro ⟨L, iF, iA, hrad, hsp⟩
    let _ : Field L := iF
    let _ : Algebra K L := iA
    exact ⟨L, iF, iA, hrad, hsp_mul L hc f hsp⟩

/-- Separability and non-vanishing discriminant of any irreducible polynomial `f ∈ K[X]` whose
degree `f.natDegree` is non-zero in `K` (in particular cubics when `char K ≠ 3` and quartics when
`char K ≠ 2`). -/
theorem irreducible_separable_of_natDegree_cast_ne_zero {K : Type u} [Field K] {f : K[X]}
    (hirr : Irreducible f) (hdeg_ne0 : (f.natDegree : K) ≠ 0) :
    f.Separable ∧ IsGarlingSeparablePoly f ∧ garlingDiscriminant f ≠ 0 := by
  have hpos : 1 ≤ f.natDegree := hirr.natDegree_pos
  have hderiv_ne0 : Polynomial.derivative f ≠ 0 := by
    intro hd0
    have hc := congrArg (fun p : K[X] => p.coeff (f.natDegree - 1)) hd0
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero,
      Nat.sub_add_cancel hpos] at hc
    have hlc : f.coeff f.natDegree ≠ 0 := by
      rw [← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    have hcast : ((f.natDegree - 1 : ℕ) + 1 : K) = (f.natDegree : K) := by
      have hnat : (f.natDegree - 1) + 1 = f.natDegree := Nat.sub_add_cancel hpos
      have hc' := congrArg (Nat.cast (R := K)) hnat
      simpa using hc'
    rw [hcast] at hc
    exact mul_ne_zero hlc hdeg_ne0 hc
  have hsep : f.Separable := by
    rw [Polynomial.Separable]
    refine (Irreducible.coprime_iff_not_dvd hirr).mpr fun hdvd => ?_
    have hle := Polynomial.natDegree_le_of_dvd hdvd hderiv_ne0
    have hlt : (Polynomial.derivative f).natDegree < f.natDegree :=
      Polynomial.natDegree_derivative_lt (by omega)
    omega
  have hgar_sep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep).2.2
  have hdisc_ne0 : garlingDiscriminant f ≠ 0 := by
    intro h0
    let L := Polynomial.SplittingField f
    let _ : Field L := Polynomial.SplittingField.instField f
    let _ : Algebra K L := Polynomial.SplittingField.instAlgebra f
    have hsf : IsGarlingSplittingFieldExtension K L f :=
      (isGarlingSplittingFieldExtension_iff K L f).mpr inferInstance
    have hrep := (garlingDiscriminant_eq_zero_iff_hasGarlingRepeatedRoot f hsf).mp h0
    obtain ⟨n, c, α, hexp⟩ := hsf.1
    have hinj := (injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).1.mpr hsep
    exact (injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).2.mpr hrep hinj
  exact ⟨hsep, hgar_sep, hdisc_ne0⟩

/-! ### §14.3 Main-Text Derivation: Depressing Cubics, 6-Field Diagram, and Radical Solution -/

/-- Coefficient `p = a₁ - a₂² / 3` of `y³ + py + q` obtained from `x³ + a₂ x² + a₁ x + a₀` via
`y = x + a₂ / 3` (§14.3, printed p. 114 / PDF p. 122). -/
noncomputable def depressedCubicP {K : Type u} [Field K] (a₂ a₁ : K) : K :=
  a₁ - a₂ ^ 2 / 3

/-- Coefficient `q = a₀ + 2 a₂³ / 27 - a₂ a₁ / 3` of `y³ + py + q` obtained from
`x³ + a₂ x² + a₁ x + a₀` via `y = x + a₂ / 3` (§14.3, printed p. 114 / PDF p. 122). -/
noncomputable def depressedCubicQ {K : Type u} [Field K] (a₂ a₁ a₀ : K) : K :=
  a₀ + 2 * a₂ ^ 3 / 27 - a₂ * a₁ / 3

/-- **§14.3 Cubic Depression Identity** (printed pp. 113–114 / PDF pp. 121–122):
When `char K ≠ 3`, substituting `x = y - a₂ / 3` into `f = x³ + a₂ x² + a₁ x + a₀` yields
`y³ + p y + q` with `p = a₁ - a₂² / 3` and `q = a₀ + 2 a₂³ / 27 - a₂ a₁ / 3`, and preserves
`garlingDiscriminant`. -/
theorem section_14_3_depress_cubic {K : Type u} [Field K] (hchar3 : ringChar K ≠ 3)
    (a₂ a₁ a₀ : K) :
    let f : K[X] :=
      Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
        Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀
    let g : K[X] :=
      Polynomial.X ^ 3 + Polynomial.C (depressedCubicP a₂ a₁) * Polynomial.X +
        Polynomial.C (depressedCubicQ a₂ a₁ a₀)
    f.comp (Polynomial.X + Polynomial.C (-a₂ / 3)) = g ∧
    garlingDiscriminant g = garlingDiscriminant f := by
  intro f g
  have h3 : (3 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  have h27 : (27 : K) ≠ 0 := by
    have h27_eq : (27 : K) = 3 ^ 3 := by norm_num
    rw [h27_eq]
    exact pow_ne_zero 3 h3
  have hcomp : f.comp (Polynomial.X + Polynomial.C (-a₂ / 3)) = g := by
    have hcoeff_eq : ∀ k : ℕ,
        (f.comp (Polynomial.X + Polynomial.C (-a₂ / 3))).coeff k = g.coeff k := by
      intro k
      dsimp [f, g, depressedCubicP, depressedCubicQ]
      simp only [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp]
      have expand_lhs :
          (Polynomial.X + Polynomial.C (-a₂ / 3)) ^ 3 +
            Polynomial.C a₂ * (Polynomial.X + Polynomial.C (-a₂ / 3)) ^ 2 +
            Polynomial.C a₁ * (Polynomial.X + Polynomial.C (-a₂ / 3)) + Polynomial.C a₀ =
          Polynomial.X ^ 3 +
            Polynomial.C (3 * (-a₂ / 3) + a₂) * Polynomial.X ^ 2 +
            Polynomial.C (3 * (-a₂ / 3) ^ 2 + 2 * a₂ * (-a₂ / 3) + a₁) * Polynomial.X +
            Polynomial.C ((-a₂ / 3) ^ 3 + a₂ * (-a₂ / 3) ^ 2 + a₁ * (-a₂ / 3) + a₀) := by
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      rw [expand_lhs]
      have hc2 : 3 * (-a₂ / 3) + a₂ = 0 := by field_simp [h3]; ring
      have hc1 : 3 * (-a₂ / 3) ^ 2 + 2 * a₂ * (-a₂ / 3) + a₁ = a₁ - a₂ ^ 2 / 3 := by
        field_simp [h3]; ring
      have hc0 : (-a₂ / 3) ^ 3 + a₂ * (-a₂ / 3) ^ 2 + a₁ * (-a₂ / 3) + a₀ =
          a₀ + 2 * a₂ ^ 3 / 27 - a₂ * a₁ / 3 := by
        field_simp [h3, h27]; ring
      rw [hc2, hc1, hc0, map_zero, zero_mul, add_zero]
    exact Polynomial.ext hcoeff_eq
  refine ⟨hcomp, ?_⟩
  rw [← hcomp, garlingDiscriminant_comp_X_add_C]

/-- **§14.3 True Discriminant of `g = x³ + px + q`** (printed p. 114 / PDF p. 122; see note on
p. 114 l. 5's printed sign typo `4p³ - 27q²`):
For **every** field `K` and `p, q : K`, `garlingDiscriminant (x³ + px + q) = -4p³ - 27q²`. -/
theorem garlingDiscriminant_depressed_cubic {K : Type u} [Field K] (p q : K) :
    garlingDiscriminant (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) =
      -4 * p ^ 3 - 27 * q ^ 2 := by
  have heq : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]) =
      Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 +
        Polynomial.C p * Polynomial.X + Polynomial.C q := by
    simp
  rw [heq, garlingDiscriminant_monic_cubic]
  ring

/-- Counterexample documenting p. 114 l. 5's printed sign slip `4p³ - 27q²`: for `g = x³ + x ∈ ℚ[x]`
(`p = 1, q = 0`), `garlingDiscriminant g = -4`, whereas `4p³ - 27q² = +4 ≠ -4`. -/
theorem section_14_3_printed_disc_sign_typo_remark :
    let g : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C 1 * Polynomial.X + Polynomial.C 0
    garlingDiscriminant g = -4 ∧
    (4 * (1 : ℚ) ^ 3 - 27 * (0 : ℚ) ^ 2) = 4 ∧
    garlingDiscriminant g ≠ 4 * (1 : ℚ) ^ 3 - 27 * (0 : ℚ) ^ 2 := by
  intro g
  have hd : garlingDiscriminant g = -4 := by
    rw [garlingDiscriminant_depressed_cubic]
    norm_num
  exact ⟨hd, by norm_num, by rw [hd]; norm_num⟩

/-- **§14.3 Galois Group over `K(δ)` for an Irreducible Cubic** (printed p. 114 / PDF p. 122):
If `char K ≠ 2, 3`, `g ∈ K[X]` is an irreducible cubic (`g.natDegree = 3`), `L : K` is a splitting
field extension for `g`, and `δ ∈ L` satisfies `δ² = Δ`, then `[L : K(δ)] = 3`, `|Γ(L : K(δ))| = 3`,
and `Γ(L : K(δ)) ≃* alternatingGroup (Fin 3)` (`A₃ ≅ C₃`). -/
theorem section_14_3_splitting_over_K_delta {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {g : K[X]} (hirr : Irreducible g) (hdeg : g.natDegree = 3)
    (hsf : IsGarlingSplittingFieldExtension K L g)
    {δ : L} (hδ_sq : δ ^ 2 = algebraMap K L (garlingDiscriminant g)) :
    open scoped IntermediateField in
    IsGarlingGaloisExtension K L ∧
    Module.finrank K⟮δ⟯ L = 3 ∧
    Nat.card (L ≃ₐ[K⟮δ⟯] L) = 3 ∧
    Nonempty ((L ≃ₐ[K⟮δ⟯] L) ≃* Multiplicative (ZMod 3)) := by
  open scoped IntermediateField in
  have h3_ne0 : (g.natDegree : K) ≠ 0 := by
    rw [hdeg]
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  obtain ⟨hsep, hgar_sep, hdisc_ne0⟩ := irreducible_separable_of_natDegree_cast_ne_zero hirr h3_ne0
  have hfinKL : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsf).1
  have hnormKL : IsGarlingNormal K L := (corollary_1_to_theorem_9_1 hfinKL).mpr ⟨g, hsf⟩
  have hsepKL : IsGarlingSeparableExtension K L := corollary_3_to_theorem_10_3 hgar_sep hsf
  have hgalKL : IsGarlingGaloisExtension K L := ⟨hfinKL, hnormKL, hsepKL⟩
  have ⟨_, _⟩ := (isGarlingGaloisExtension_iff K L).mp hgalKL
  have _ : FiniteDimensional K⟮δ⟯ L := FiniteDimensional.right K K⟮δ⟯ L
  have _ : IsGalois K⟮δ⟯ L := IsGalois.tower_top_of_isGalois K K⟮δ⟯ L
  -- `3 ∣ [L : K]` because `L` contains a root `r` of irreducible degree-`3` polynomial `g`.
  obtain ⟨n, c, α, hexp⟩ := hsf.1
  have hn3 : n = 3 := ((garlingSplitsExplicit_props hirr.ne_zero hexp).2.2.1).trans hdeg
  subst hn3
  have hr_root : Polynomial.aeval (α 0) g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp, Polynomial.eval_mul, Polynomial.eval_prod]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ 0) (by simp))
  have hr_int : IsIntegral K (α 0) := Algebra.IsIntegral.isIntegral (α 0)
  have hmin_eq : minpoly K (α 0) = Polynomial.C g.leadingCoeff⁻¹ * g := by
    have hlc_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    have hmon : (Polynomial.C g.leadingCoeff⁻¹ * g).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hlc_ne]
    have hirr' : Irreducible (Polynomial.C g.leadingCoeff⁻¹ * g) := by
      have hu : IsUnit (Polynomial.C g.leadingCoeff⁻¹ : K[X]) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc_ne))
      exact (irreducible_isUnit_mul hu).mpr hirr
    have haev' : Polynomial.aeval (α 0) (Polynomial.C g.leadingCoeff⁻¹ * g) = 0 := by
      rw [map_mul, hr_root, mul_zero]
    exact (minpoly.eq_of_irreducible_of_monic hirr' haev' hmon).symm
  have hfin_r : Module.finrank K K⟮α 0⟯ = 3 := by
    rw [IntermediateField.adjoin.finrank hr_int, hmin_eq,
      Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero)),
      hdeg]
  have hdvd3 : 3 ∣ Module.finrank K L := by
    have hmul := (Module.finrank_mul_finrank K K⟮α 0⟯ L).symm
    rw [hfin_r] at hmul
    exact ⟨Module.finrank K⟮α 0⟯ L, hmul⟩
  have hcardG_eq_deg : Nat.card (GarlingPolyGaloisGroup K L g) = Module.finrank K L :=
    (theorem_11_5 hirr.ne_zero hsf).1 hgar_sep |>.2.1
  -- Root labelling `e : Fin g.natDegree ≃ garlingRootSet K L g`
  have hinj_α : Function.Injective α :=
    (injective_roots_iff_separable_and_not_repeated hirr.ne_zero hexp).1.mpr hsep
  have hrange_α : Set.range α = garlingRootSet K L g := by
    rw [garlingRootSet_eq_rootSet hirr.ne_zero]
    exact (garlingSplitsExplicit_props hirr.ne_zero hexp).2.2.2
  let e_fin3 : Fin 3 ≃ garlingRootSet K L g :=
    (Equiv.ofInjective α hinj_α).trans
      { toFun := fun x => ⟨x.1, hrange_α ▸ x.2⟩
        invFun := fun y => ⟨y.1, hrange_α.symm ▸ y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let e_deg : Fin g.natDegree ≃ garlingRootSet K L g :=
    (finCongr hdeg).trans e_fin3
  have hinj_perm3 : Function.Injective (garlingRootLabellingPermHom e_fin3) := by
    intro σ₁ σ₂ h12
    apply theorem_11_6 hsf
    ext x
    have hx := Equiv.congr_fun h12 (e_fin3.symm x)
    have hx' := congrArg (fun k => (e_fin3 k : L)) hx
    simpa [garlingRootLabellingPermHom] using hx'
  have hthm141 := theorem_14_1 hchar2 g hsf
  have hfin3 : Module.finrank K⟮δ⟯ L = 3 := by
    by_cases hsqK : ∃ d : K, d ^ 2 = garlingDiscriminant g
    · -- Case 1: `Δ = d²` in `K`: `K(δ) = ⊥` (`[K(δ) : K] = 1`) and `Γ_K(g) ⊆ A₃` (`|A₃| = 3`).
      rcases hsqK with ⟨d, hd⟩
      have hδ_pm : δ = algebraMap K L d ∨ δ = -algebraMap K L d := by
        have h0 : (δ - algebraMap K L d) * (δ + algebraMap K L d) = 0 := by
          calc (δ - algebraMap K L d) * (δ + algebraMap K L d)
              = δ ^ 2 - (algebraMap K L d) ^ 2 := by ring
            _ = 0 := by rw [hδ_sq, ← map_pow, hd, sub_self]
        rcases mul_eq_zero.mp h0 with h1 | h2
        · exact Or.inl (sub_eq_zero.mp h1)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
      have hKδ_bot : K⟮δ⟯ = ⊥ := by
        rw [eq_bot_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        rcases hδ_pm with rfl | rfl
        · exact (⊥ : IntermediateField K L).algebraMap_mem d
        · exact neg_mem ((⊥ : IntermediateField K L).algebraMap_mem d)
      have hfin_Kδ : Module.finrank K K⟮δ⟯ = 1 := by
        rw [hKδ_bot]; exact IntermediateField.finrank_bot
      have hallA := (hthm141.2.1 hdisc_ne0 ⟨d, hd⟩).2 e_deg
      -- Transfer `hallA` along `hdeg : g.natDegree = 3` to `e_fin3`:
      have hallA3 : ∀ σ : GarlingPolyGaloisGroup K L g,
          garlingRootLabellingPermHom e_fin3 σ ∈ alternatingGroup (Fin 3) := by
        intro σ
        have hmem := hallA σ
        dsimp [e_deg] at hmem
        -- `garlingRootLabellingPermHom ((finCongr hdeg).trans e_fin3) σ` is conjugate via `finCongr hdeg`
        have hconj_sign : Equiv.Perm.sign (garlingRootLabellingPermHom e_fin3 σ) =
            Equiv.Perm.sign (garlingRootLabellingPermHom ((finCongr hdeg).trans e_fin3) σ) := by
          have heq_perm : garlingRootLabellingPermHom ((finCongr hdeg).trans e_fin3) σ =
              (finCongr hdeg).trans
                ((garlingRootLabellingPermHom e_fin3 σ).trans (finCongr hdeg).symm) := by
            ext i; rfl
          rw [heq_perm]
          exact (Equiv.Perm.sign_permCongr (finCongr hdeg).symm _).symm
        rw [Equiv.Perm.mem_alternatingGroup] at hmem ⊢
        exact hconj_sign.trans hmem
      let toA3 : GarlingPolyGaloisGroup K L g → alternatingGroup (Fin 3) :=
        fun σ => ⟨garlingRootLabellingPermHom e_fin3 σ, hallA3 σ⟩
      have htoA3_inj : Function.Injective toA3 :=
        fun σ₁ σ₂ h => hinj_perm3 (congrArg Subtype.val h)
      have hcardA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; decide
      let _ : Finite (alternatingGroup (Fin 3)) :=
        Nat.finite_of_card_ne_zero (by rw [hcardA3]; decide)
      have hle3 : Nat.card (GarlingPolyGaloisGroup K L g) ≤ 3 := by
        rw [← hcardA3]
        exact Nat.card_le_card_of_injective toA3 htoA3_inj
      rw [hcardG_eq_deg] at hle3
      have hpos_deg : 0 < Module.finrank K L := Module.finrank_pos
      have hdeg_KL3 : Module.finrank K L = 3 := by
        rcases hdvd3 with ⟨k, hk⟩; omega
      have hmul := Module.finrank_mul_finrank K K⟮δ⟯ L
      rw [hfin_Kδ, one_mul, hdeg_KL3] at hmul
      exact hmul
    · -- Case 2: `Δ` has no square root in `K`: `Theorem 14.1 (iii)` gives `K(δ) = fixedField (G ∩ A₃)`!
      obtain ⟨_, δ₀, hδ₀_sq, _, he_all⟩ := hthm141.2.2 hsqK
      obtain ⟨hnotA_deg, hfixed_deg⟩ := he_all e_deg
      have hδ_pm : δ = δ₀ ∨ δ = -δ₀ := by
        have h0 : (δ - δ₀) * (δ + δ₀) = 0 := by
          linear_combination hδ_sq - hδ₀_sq
        rcases mul_eq_zero.mp h0 with h1 | h2
        · exact Or.inl (sub_eq_zero.mp h1)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
      have hKδ_eq : K⟮δ⟯ = K⟮δ₀⟯ := by
        rcases hδ_pm with rfl | rfl
        · rfl
        · apply le_antisymm
          · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
            exact neg_mem (IntermediateField.mem_adjoin_simple_self K δ₀)
          · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
            simpa using neg_mem (IntermediateField.mem_adjoin_simple_self K (-δ₀))
      rw [hKδ_eq, hfixed_deg, IntermediateField.finrank_fixedField_eq_card]
      change Nat.card ((alternatingGroup (Fin g.natDegree)).comap (garlingRootLabellingPermHom e_deg)) = 3
      have hcomap_eq : (alternatingGroup (Fin g.natDegree)).comap (garlingRootLabellingPermHom e_deg) =
          (alternatingGroup (Fin 3)).comap (garlingRootLabellingPermHom e_fin3) := by
        ext σ
        simp only [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
        have heq_perm : garlingRootLabellingPermHom e_deg σ =
            (finCongr hdeg).symm.permCongr (garlingRootLabellingPermHom e_fin3 σ) := by
          ext i; rfl
        rw [heq_perm, Equiv.Perm.sign_permCongr]
      rw [hcomap_eq]
      -- Image `H := (garlingRootLabellingPermHom e_fin3).range ≤ SigmaN 3` has `3 ∣ |H|`, `|H| ≤ 6`, and `H ⊄ A₃`!
      let φ3 := garlingRootLabellingPermHom e_fin3
      have hnot_le_A3 : ¬ φ3.range ≤ alternatingGroup (Fin 3) := by
        intro hle
        apply hnotA_deg
        intro σ
        have hmemA3 : φ3 σ ∈ alternatingGroup (Fin 3) := hle ⟨σ, rfl⟩
        have hmem_comap : σ ∈ (alternatingGroup (Fin 3)).comap φ3 := hmemA3
        rw [← hcomap_eq] at hmem_comap
        exact hmem_comap
      let eRange : GarlingPolyGaloisGroup K L g ≃* φ3.range :=
        MulEquiv.ofBijective φ3.rangeRestrict
          ⟨fun a b hab => hinj_perm3 (congrArg Subtype.val hab), φ3.rangeRestrict_surjective⟩
      have hcard_range_dvd6 : Nat.card φ3.range ∣ 6 := by
        have hd := φ3.range.card_subgroup_dvd_card
        have hcS3 : Nat.card (SigmaN 3) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
        rwa [hcS3] at hd
      have h3_dvd_range : 3 ∣ Nat.card φ3.range := by
        rw [← Nat.card_congr eRange.toEquiv, hcardG_eq_deg]
        exact hdvd3
      have hpos_r : 0 < Nat.card φ3.range := Nat.card_pos
      have hle6_r : Nat.card φ3.range ≤ 6 := Nat.le_of_dvd (by decide) hcard_range_dvd6
      -- If `|φ3.range| = 3`, then since `[Σ₃ : φ3.range] = 2`, `φ3.range = A₃`, contradiction!
      have hcard_range_6 : Nat.card φ3.range = 6 := by
        rcases h3_dvd_range with ⟨k, hk⟩
        have hk_cases : k = 1 ∨ k = 2 := by omega
        rcases hk_cases with rfl | rfl
        · exfalso
          have hidx2 : φ3.range.index = 2 := by
            have hm := φ3.range.card_mul_index
            have hcS3 : Nat.card (SigmaN 3) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
            rw [hcS3, hk] at hm; omega
          have heqA3 := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx2
          exact hnot_le_A3 (le_of_eq heqA3)
        · exact hk
      have htop_S3 : φ3.range = ⊤ := by
        have hidx1 : φ3.range.index = 1 := by
          have hm := φ3.range.card_mul_index
          have hcS3 : Nat.card (SigmaN 3) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
          rw [hcS3, hcard_range_6] at hm; omega
        exact Subgroup.index_eq_one.mp hidx1
      have hbij_φ3 : Function.Bijective φ3 :=
        ⟨hinj_perm3, fun π => by
          have hmem : π ∈ φ3.range := by rw [htop_S3]; trivial
          exact hmem⟩
      let eS3 : GarlingPolyGaloisGroup K L g ≃* SigmaN 3 := MulEquiv.ofBijective φ3 hbij_φ3
      have hcard_comap : Nat.card ((alternatingGroup (Fin 3)).comap φ3) =
          Nat.card (alternatingGroup (Fin 3)) := by
        refine Nat.card_congr
          { toFun := fun x => ⟨φ3 x.1, x.2⟩
            invFun := fun y => ⟨eS3.symm y.1, by
              change φ3 (eS3.symm y.1) ∈ alternatingGroup (Fin 3)
              have : φ3 (eS3.symm y.1) = y.1 := eS3.apply_symm_apply y.1
              rw [this]; exact y.2⟩
            left_inv := fun x => Subtype.ext (eS3.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (eS3.apply_symm_apply y.1) }
      rw [hcard_comap, nat_card_alternatingGroup, Nat.card_fin]
      decide
  have hcardGal : Nat.card (L ≃ₐ[K⟮δ⟯] L) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, hfin3]
  -- Any group of prime cardinality `3` is cyclic of order `3` (`Multiplicative (ZMod 3)`):
  have hiso3 : Nonempty ((L ≃ₐ[K⟮δ⟯] L) ≃* Multiplicative (ZMod 3)) := by
    let G3 := (L ≃ₐ[K⟮δ⟯] L)
    let _ : Finite G3 := Nat.finite_of_card_ne_zero (by rw [hcardGal]; decide)
    let _ : Fintype G3 := Fintype.ofFinite G3
    have hf3 : Fintype.card G3 = 3 := Nat.card_eq_fintype_card.symm.trans hcardGal
    have _ : Nontrivial G3 := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨σ, hσ1⟩ := exists_ne (1 : G3)
    have hdvd : orderOf σ ∣ 3 := by
      have hd := orderOf_dvd_natCard σ
      rwa [hcardGal] at hd
    have hpos : 0 < orderOf σ := orderOf_pos σ
    have hle : orderOf σ ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    have hord3 : orderOf σ = 3 := by
      interval_cases ho : orderOf σ
      · exfalso; exact hσ1 (orderOf_eq_one_iff.mp ho)
      · exfalso; norm_num at hdvd
      · rfl
    exact mulEquivMultiplicativeZModOfOrderOfEqNatCard σ hord3 hcardGal
  exact ⟨hgalKL, hfin3, hcardGal, hiso3⟩

/-- **§14.3 6-Field Cube-Root-of-Unity Dichotomy** (printed p. 114 / PDF p. 122):
In the 6-field diagram `K → K(δ), K(ω) → K(ω, δ) → L(ω)` and `K(δ) → L → L(ω)` where `N : L` is a
splitting field extension for `x³ - 1` (`char K ≠ 2, 3`) and `[L : K(δ)] = 3`:
- Either `x³ - 1` splits over `K(δ)`, in which case `[N : L] = 1` (`L = L(ω)`);
- Or `x³ - 1` does not split over `K(δ)`, in which case `[K(ω, δ) : K(δ)] = 2` vs. `[L : K(δ)] = 3`,
  forcing `[N : L] = 2` (so `L` and `L(ω)` are distinct). -/
theorem section_14_3_cube_root_dichotomy {K : Type u} {L : Type v} {N : Type w}
    [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    (hchar3 : ringChar K ≠ 3)
    {δ : L} (hfin_Kδ_L : Module.finrank (IntermediateField.adjoin K ({δ} : Set L)) L = 3)
    (hsf_LN : IsGarlingSplittingFieldExtension L N (Polynomial.X ^ 3 - 1)) :
    let Kδ : IntermediateField K L := IntermediateField.adjoin K ({δ} : Set L)
    (∃ ω : N, ω ^ 2 + ω + 1 = 0 ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      IntermediateField.adjoin L ({ω} : Set N) = ⊤) ∧
    ((GarlingSplitsOver Kδ Kδ (Polynomial.X ^ 3 - 1) ∧ Module.finrank L N = 1) ∨
     (¬ GarlingSplitsOver Kδ Kδ (Polynomial.X ^ 3 - 1) ∧ Module.finrank L N = 2)) := by
  intro Kδ
  have h3K : (3 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  have h3L : (3 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 3]
    exact (map_ne_zero (algebraMap K L)).mpr h3K
  have h3N : (3 : N) ≠ 0 := by
    rw [← map_ofNat (algebraMap K N) 3]
    exact (map_ne_zero (algebraMap K N)).mpr h3K
  -- Extract a root `ω ∈ N` of `X^2 + X + 1` from `hsf_LN`:
  have hc3_mon : (Polynomial.X ^ 3 - 1 : L[X]).Monic := by
    have : (Polynomial.X ^ 3 - 1 : L[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.monic_X_pow_sub_C 1 (by decide)
  have hc3_deg : (Polynomial.X ^ 3 - 1 : L[X]).natDegree = 3 := by
    have : (Polynomial.X ^ 3 - 1 : L[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.natDegree_X_pow_sub_C
  obtain ⟨m, c₀, ρ, hexp_LN⟩ := hsf_LN.1
  have hm3 : m = 3 := ((garlingSplitsExplicit_props hc3_mon.ne_zero hexp_LN).2.2.1).trans hc3_deg
  subst hm3
  have hdisc_c3 : garlingDiscriminant (Polynomial.X ^ 3 - 1 : L[X]) ≠ 0 := by
    have heq : (Polynomial.X ^ 3 - 1 : L[X]) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1) := by
      simp [sub_eq_add_neg]
    rw [heq, garlingDiscriminant_depressed_cubic]
    have h27L : (27 : L) ≠ 0 := by
      have : (27 : L) = 3 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h3L
    intro h0
    apply h27L
    linear_combination -h0
  have hinj_ρ : Function.Injective ρ := by
    by_contra hninj
    have hd0 : garlingDeltaTuple ρ = 0 := (garlingDeltaTuple_eq_zero_iff ρ).mpr hninj
    have hdisc0 : algebraMap L N (garlingDiscriminant (Polynomial.X ^ 3 - 1 : L[X])) = 0 := by
      rw [garlingDiscriminant_eq_discTuple hc3_mon.ne_zero hexp_LN, garlingDiscTuple, hd0,
        zero_pow (by decide)]
    exact hdisc_c3 ((map_eq_zero_iff (algebraMap L N) (algebraMap L N).injective).mp hdisc0)
  have hρ_cube : ∀ i : Fin 3, (ρ i) ^ 3 - 1 = 0 := by
    intro i
    have hev : ((Polynomial.X ^ 3 - 1 : L[X]).map (algebraMap L N)).eval (ρ i) = 0 := by
      rw [hexp_LN, Polynomial.eval_mul, Polynomial.eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    simpa using hev
  have hex_ω : ∃ ω : N, ω ^ 2 + ω + 1 = 0 := by
    by_cases h0 : ρ 0 = 1
    · have h1_ne : ρ 1 ≠ 1 := fun h1 =>
        absurd (hinj_ρ (h1.trans h0.symm)) (by decide)
      refine ⟨ρ 1, ?_⟩
      have hmul : (ρ 1 - 1) * ((ρ 1) ^ 2 + ρ 1 + 1) = 0 := by linear_combination hρ_cube 1
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1_ne)
    · refine ⟨ρ 0, ?_⟩
      have hmul : (ρ 0 - 1) * ((ρ 0) ^ 2 + ρ 0 + 1) = 0 := by linear_combination hρ_cube 0
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h0)
  obtain ⟨ω, hω_quad⟩ := hex_ω
  have hfac_cyclo : (Polynomial.X ^ 3 - 1 : N[X]) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) := by ring
  have hω_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω_quad
  have hω_ne1 : ω ≠ 1 := by
    intro h1
    rw [h1] at hω_quad
    norm_num at hω_quad
    exact h3N hω_quad
  have hfac_N : (Polynomial.X ^ 3 - 1 : N[X]) =
      (Polynomial.X - 1) * (Polynomial.X - Polynomial.C ω) *
        (Polynomial.X - Polynomial.C (ω ^ 2)) := by
    have hq_fac : (Polynomial.X ^ 2 + Polynomial.X + 1 : N[X]) =
        (Polynomial.X - Polynomial.C ω) * (Polynomial.X - Polynomial.C (ω ^ 2)) := by
      have hc0 : Polynomial.C (0 : N) = 0 := map_zero Polynomial.C
      have hc_rel : Polynomial.C (ω ^ 2 + ω + 1) = (0 : N[X]) := by rw [hω_quad, hc0]
      simp only [map_add, map_pow, map_one] at hc_rel ⊢
      linear_combination (Polynomial.X + 1 - Polynomial.C ω) * hc_rel
    rw [hfac_cyclo, hq_fac, mul_assoc]
  have hadj_ω : IntermediateField.adjoin L ({ω} : Set N) = ⊤ := by
    by_contra hne_top
    refine hsf_LN.2 (IntermediateField.adjoin L ({ω} : Set N)) hne_top ?_
    let E := IntermediateField.adjoin L ({ω} : Set N)
    let ωE : E := ⟨ω, IntermediateField.mem_adjoin_simple_self L ω⟩
    refine ⟨3, 1, ![1, ωE, ωE ^ 2], ?_⟩
    unfold GarlingSplitsExplicit
    apply Polynomial.map_injective E.val.toRingHom E.val.injective
    rw [Polynomial.map_map]
    have hmap1 : ((Polynomial.X ^ 3 - 1 : L[X]).map
        (E.val.toRingHom.comp (algebraMap L E))) = (Polynomial.X ^ 3 - 1 : N[X]) := by simp
    rw [hmap1, hfac_N, Fin.prod_univ_three]
    simp [ωE, mul_assoc]
  have hω_int_L : IsIntegral L ω := ⟨Polynomial.X ^ 2 + Polynomial.X + 1, by monicity!, by
    simp [hω_quad]⟩
  have hdeg_LN_le2 : Module.finrank L N ≤ 2 := by
    have h1 : Module.finrank L (IntermediateField.adjoin L ({ω} : Set N)) ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hω_int_L]
      have hdvd := minpoly.dvd L ω (show Polynomial.aeval ω (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]) = 0 by
        simp [hω_quad])
      have hq_deg : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]).natDegree = 2 := by compute_degree!
      have hq_mon : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]).Monic := by monicity!
      exact (Polynomial.natDegree_le_of_dvd hdvd hq_mon.ne_zero).trans_eq hq_deg
    have htop_eq : Module.finrank L (IntermediateField.adjoin L ({ω} : Set N)) = Module.finrank L N := by
      rw [hadj_ω]
      exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq
    omega
  have hdeg_LN_pos : 1 ≤ Module.finrank L N := by
    have _ : FiniteDimensional L N :=
      (isFiniteExtension_iff_moduleFinite L N).mp (corollary_to_theorem_7_1 hsf_LN).1
    exact Module.finrank_pos
  refine ⟨⟨ω, hω_quad, hω_cube, hω_ne1, hadj_ω⟩, ?_⟩
  by_cases hsp_Kδ : GarlingSplitsOver Kδ Kδ (Polynomial.X ^ 3 - 1)
  · left
    refine ⟨hsp_Kδ, ?_⟩
    -- `X^3 - 1` splits over `K(δ)`, hence splits over `L`, so `⊥ : IntermediateField L N` splits it!
    have hsp_LL : GarlingSplitsOver L L (Polynomial.X ^ 3 - 1) := by
      rw [garlingSplitsOver_iff_splits] at hsp_Kδ ⊢
      have hmap_id : (Polynomial.X ^ 3 - 1 : Kδ[X]).map (algebraMap Kδ Kδ) =
          (Polynomial.X ^ 3 - 1 : Kδ[X]) := by simp
      rw [hmap_id] at hsp_Kδ
      have hsp_map := hsp_Kδ.map Kδ.val.toRingHom
      have hmap_L : (Polynomial.X ^ 3 - 1 : Kδ[X]).map Kδ.val.toRingHom =
          (Polynomial.X ^ 3 - 1 : L[X]) := by simp
      rw [hmap_L] at hsp_map
      simpa using hsp_map
    have hbot_sp : GarlingSplitsOver L (⊥ : IntermediateField L N) (Polynomial.X ^ 3 - 1) := by
      rw [garlingSplitsOver_iff_splits] at hsp_LL ⊢
      have hmap_id : (Polynomial.X ^ 3 - 1 : L[X]).map (algebraMap L L) =
          (Polynomial.X ^ 3 - 1 : L[X]) := by simp
      rw [hmap_id] at hsp_LL
      have hsp_b := hsp_LL.map (algebraMap L (⊥ : IntermediateField L N))
      exact hsp_b
    have hbot_top : (⊥ : IntermediateField L N) = ⊤ := by
      by_contra hne
      exact hsf_LN.2 ⊥ hne hbot_sp
    have h1 : Module.finrank L (⊥ : IntermediateField L N) = 1 := IntermediateField.finrank_bot
    have h2 : Module.finrank L (⊤ : IntermediateField L N) = Module.finrank L N :=
      IntermediateField.topEquiv.toLinearEquiv.finrank_eq
    rw [hbot_top] at h1
    exact h2.symm.trans h1
  · right
    refine ⟨hsp_Kδ, ?_⟩
    -- If `[N : L] = 1`, then `ω ∈ L`, so `[K(δ)(ω) : K(δ)] ∣ [L : K(δ)] = 3`, while `[K(δ)(ω) : K(δ)] ≤ 2`,
    -- forcing `ω ∈ K(δ)` and `X^3 - 1` splitting over `K(δ)`, contradiction!
    by_contra hne2
    have hfin1 : Module.finrank L N = 1 := by omega
    have _ : FiniteDimensional L N :=
      (isFiniteExtension_iff_moduleFinite L N).mp (corollary_to_theorem_7_1 hsf_LN).1
    have hbot_top : (⊥ : IntermediateField L N) = ⊤ :=
      (IntermediateField.finrank_eq_one_iff.mp
        (IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans hfin1)).symm
    have hω_bot : ω ∈ (⊥ : IntermediateField L N) := hbot_top.symm ▸ IntermediateField.mem_top
    obtain ⟨ωL, hωL⟩ := IntermediateField.mem_bot.mp hω_bot
    have hωL_quad : ωL ^ 2 + ωL + 1 = 0 :=
      (algebraMap L N).injective (by simp [map_add, map_pow, hωL, hω_quad])
    -- Consider `Kδ⟮ωL⟯` inside `L` over `Kδ`:
    have hωL_aev : Polynomial.aeval ωL (Polynomial.X ^ 2 + Polynomial.X + 1 : Kδ[X]) = 0 := by
      simp [hωL_quad]
    have hωL_int : IsIntegral Kδ ωL := ⟨Polynomial.X ^ 2 + Polynomial.X + 1, by monicity!, hωL_aev⟩
    let d_ω : ℕ := Module.finrank Kδ (IntermediateField.adjoin Kδ ({ωL} : Set L))
    have hdvd_3 : d_ω ∣ 3 := by
      have _ : FiniteDimensional Kδ L := FiniteDimensional.of_finrank_pos (by rw [hfin_Kδ_L]; decide)
      refine ⟨Module.finrank (IntermediateField.adjoin Kδ ({ωL} : Set L)) L, ?_⟩
      rw [← hfin_Kδ_L]
      exact (Module.finrank_mul_finrank Kδ (IntermediateField.adjoin Kδ ({ωL} : Set L)) L).symm
    have hle_2 : d_ω ≤ 2 := by
      dsimp [d_ω]
      rw [IntermediateField.adjoin.finrank hωL_int]
      have hdvd_q := minpoly.dvd Kδ ωL hωL_aev
      have hq_deg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Kδ[X]).natDegree = 2 := by compute_degree!
      have hq_mon : (Polynomial.X ^ 2 + Polynomial.X + 1 : Kδ[X]).Monic := by monicity!
      exact (Polynomial.natDegree_le_of_dvd hdvd_q hq_mon.ne_zero).trans_eq hq_deg
    have hpos_d : 1 ≤ d_ω := by
      have _ : FiniteDimensional Kδ L := FiniteDimensional.of_finrank_pos (by rw [hfin_Kδ_L]; decide)
      exact Module.finrank_pos
    have hd1 : d_ω = 1 := by
      rcases hdvd_3 with ⟨k, hk⟩
      change 3 = d_ω * k at hk
      interval_cases d_ω
      · rfl
      · omega
    have hbot_Kδ : IntermediateField.adjoin Kδ ({ωL} : Set L) = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp hd1
    have hωL_in_Kδ : ωL ∈ (⊥ : IntermediateField Kδ L) :=
      hbot_Kδ ▸ IntermediateField.mem_adjoin_simple_self Kδ ωL
    obtain ⟨ω₀, hω₀⟩ := IntermediateField.mem_bot.mp hωL_in_Kδ
    have hω₀_quad : ω₀ ^ 2 + ω₀ + 1 = 0 := by
      apply Subtype.ext
      change (algebraMap Kδ L ω₀) ^ 2 + algebraMap Kδ L ω₀ + 1 = 0
      rw [hω₀]
      exact hωL_quad
    apply hsp_Kδ
    refine ⟨3, 1, ![1, ω₀, ω₀ ^ 2], ?_⟩
    unfold GarlingSplitsExplicit
    have hmap_id : (Polynomial.X ^ 3 - 1 : Kδ[X]).map (algebraMap Kδ Kδ) =
        Polynomial.X ^ 3 - 1 := by simp
    rw [hmap_id, Fin.prod_univ_three]
    have hv0 : (![1, ω₀, ω₀ ^ 2] : Fin 3 → Kδ) 0 = 1 := rfl
    have hv1 : (![1, ω₀, ω₀ ^ 2] : Fin 3 → Kδ) 1 = ω₀ := rfl
    have hv2 : (![1, ω₀, ω₀ ^ 2] : Fin 3 → Kδ) 2 = ω₀ ^ 2 := rfl
    rw [hv0, hv1, hv2]
    have hc0 : Polynomial.C (0 : Kδ) = 0 := map_zero Polynomial.C
    have hc_rel : Polynomial.C (ω₀ ^ 2 + ω₀ + 1) = (0 : Kδ[X]) := by rw [hω₀_quad, hc0]
    simp only [map_add, map_pow, map_one, one_mul] at hc_rel ⊢
    linear_combination (Polynomial.X - 1) * (Polynomial.X + 1 - Polynomial.C ω₀) * hc_rel

/-- **§14.3 Cubic Resolvent Elements `β, γ` and Root-Recovery Identities**
(printed pp. 114–115 / PDF pp. 122–123):
For any roots `α₀, α₁, α₂` of `x³ + px + q = (x - α₀)(x - α₁)(x - α₂)` and primitive cube root of
unity `ω` (`ω² + ω + 1 = 0`) in a field `E` of characteristic `≠ 2, 3`, setting
`β = α₀ + ω α₁ + ω² α₂`, `γ = α₀ + ω² α₁ + ω α₂`, and `δ = (α₁ - α₀)(α₂ - α₀)(α₂ - α₁)`:
1. `(2ω + 1)² = -3` and `((2ω + 1) δ)² = -3 (-4p³ - 27q²)`;
2. `β γ = -3p`, `β³ γ³ = -27p³`, and `β³ + γ³ = -27q`;
3. `(x - β³)(x - γ³) = x² + 27qx - 27p³`;
4. `β³ = -(27/2)q - (3/2)(2ω + 1)δ` and `γ³ = -(27/2)q + (3/2)(2ω + 1)δ`
   *(showing the true `-27/2 q` sign vs. p. 115 l. 7's dropped minus sign on the RHS)*;
5. `α₀ = (β + γ)/3`, `α₁ = (ω² β + ω γ)/3`, and `α₂ = (ω β + ω² γ)/3`. -/
theorem section_14_3_resolvent_identities {E : Type*} [Field E]
    (h2 : (2 : E) ≠ 0) (h3 : (3 : E) ≠ 0)
    {p q α₀ α₁ α₂ ω : E}
    (hfac : (Polynomial.X - Polynomial.C α₀) * (Polynomial.X - Polynomial.C α₁) *
        (Polynomial.X - Polynomial.C α₂) =
      Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hω : ω ^ 2 + ω + 1 = 0) :
    let β : E := α₀ + ω * α₁ + ω ^ 2 * α₂
    let γ : E := α₀ + ω ^ 2 * α₁ + ω * α₂
    let δ : E := (α₁ - α₀) * (α₂ - α₀) * (α₂ - α₁)
    (2 * ω + 1) ^ 2 = -3 ∧
    ((2 * ω + 1) * δ) ^ 2 = -3 * (-4 * p ^ 3 - 27 * q ^ 2) ∧
    β * γ = -3 * p ∧
    β ^ 3 * γ ^ 3 = -27 * p ^ 3 ∧
    β ^ 3 + γ ^ 3 = -27 * q ∧
    (Polynomial.X - Polynomial.C (β ^ 3)) * (Polynomial.X - Polynomial.C (γ ^ 3)) =
      Polynomial.X ^ 2 + Polynomial.C (27 * q) * Polynomial.X - Polynomial.C (27 * p ^ 3) ∧
    β ^ 3 = -(27 / 2 : E) * q - (3 / 2 : E) * (2 * ω + 1) * δ ∧
    γ ^ 3 = -(27 / 2 : E) * q + (3 / 2 : E) * (2 * ω + 1) * δ ∧
    α₀ = (β + γ) / 3 ∧
    α₁ = (ω ^ 2 * β + ω * γ) / 3 ∧
    α₂ = (ω * β + ω ^ 2 * γ) / 3 := by
  intro β γ δ
  -- Extract Vieta relations `α₀ + α₁ + α₂ = 0`, `α₀α₁ + α₀α₂ + α₁α₂ = p`, `α₀α₁α₂ = -q`:
  have hexpand : (Polynomial.X - Polynomial.C α₀) * (Polynomial.X - Polynomial.C α₁) *
      (Polynomial.X - Polynomial.C α₂) =
      Polynomial.X ^ 3 - Polynomial.C (α₀ + α₁ + α₂) * Polynomial.X ^ 2 +
        Polynomial.C (α₀ * α₁ + α₀ * α₂ + α₁ * α₂) * Polynomial.X -
        Polynomial.C (α₀ * α₁ * α₂) := by
    simp only [map_add, map_mul]
    ring
  rw [hexpand] at hfac
  have hs1 : α₀ + α₁ + α₂ = 0 := by
    have h := congrArg (fun P : E[X] => P.coeff 2) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination -h
  have hs2 : α₀ * α₁ + α₀ * α₂ + α₁ * α₂ = p := by
    have h := congrArg (fun P : E[X] => P.coeff 1) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination h
  have hs3 : α₀ * α₁ * α₂ = -q := by
    have h := congrArg (fun P : E[X] => P.coeff 0) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination -h
  have hω_sq3 : (2 * ω + 1) ^ 2 = -3 := by linear_combination 4 * hω
  have hα0 : α₀ = -α₁ - α₂ := by linear_combination hs1
  have hp_eq : p = α₀ * α₁ + α₀ * α₂ + α₁ * α₂ := hs2.symm
  have hq_eq : q = -(α₀ * α₁ * α₂) := by linear_combination hs3
  have hδ_sq : δ ^ 2 = -4 * p ^ 3 - 27 * q ^ 2 := by
    dsimp [δ]
    rw [hp_eq, hq_eq, hα0]
    ring
  have hωδ_sq : ((2 * ω + 1) * δ) ^ 2 = -3 * (-4 * p ^ 3 - 27 * q ^ 2) := by
    rw [mul_pow, hω_sq3, hδ_sq]
  have hω2 : ω ^ 2 = -ω - 1 := by linear_combination hω
  have hβ_lin : β = (-α₁ - 2 * α₂) + (α₁ - α₂) * ω := by
    dsimp [β]; rw [hα0, hω2]; ring
  have hγ_lin : γ = (-2 * α₁ - α₂) + (α₂ - α₁) * ω := by
    dsimp [γ]; rw [hα0, hω2]; ring
  have hcube_ω : ∀ u v : E,
      (u + v * ω) ^ 3 = (u ^ 3 - 3 * u * v ^ 2 + v ^ 3) + (3 * u ^ 2 * v - 3 * u * v ^ 2) * ω := by
    intro u v
    linear_combination (v ^ 3 * (ω - 1) + 3 * u * v ^ 2) * hω
  have hβγ : β * γ = -3 * p := by
    rw [hβ_lin, hγ_lin, hp_eq, hα0]
    linear_combination -(α₁ - α₂) ^ 2 * hω
  have hβγ_cube : β ^ 3 * γ ^ 3 = -27 * p ^ 3 := by
    calc β ^ 3 * γ ^ 3 = (β * γ) ^ 3 := (mul_pow β γ 3).symm
      _ = (-3 * p) ^ 3 := by rw [hβγ]
      _ = -27 * p ^ 3 := by ring
  have hsum_cube : β ^ 3 + γ ^ 3 = -27 * q := by
    rw [hβ_lin, hγ_lin, hcube_ω, hcube_ω, hq_eq, hα0]
    ring
  have hquad_poly : (Polynomial.X - Polynomial.C (β ^ 3)) * (Polynomial.X - Polynomial.C (γ ^ 3)) =
      Polynomial.X ^ 2 + Polynomial.C (27 * q) * Polynomial.X - Polynomial.C (27 * p ^ 3) := by
    have h1 : (Polynomial.X - Polynomial.C (β ^ 3)) * (Polynomial.X - Polynomial.C (γ ^ 3)) =
        Polynomial.X ^ 2 - Polynomial.C (β ^ 3 + γ ^ 3) * Polynomial.X +
          Polynomial.C (β ^ 3 * γ ^ 3) := by
      simp only [map_add, map_mul]
      ring
    rw [h1, hsum_cube, hβγ_cube]
    simp only [map_neg, map_mul, map_pow, map_ofNat]
    ring
  have hdiff_cube : β ^ 3 - γ ^ 3 = -3 * (2 * ω + 1) * δ := by
    rw [hβ_lin, hγ_lin, hcube_ω, hcube_ω]
    dsimp [δ]
    rw [hα0]
    ring
  have hβ_cube : β ^ 3 = -(27 / 2 : E) * q - (3 / 2 : E) * (2 * ω + 1) * δ := by
    apply mul_left_cancel₀ h2
    calc 2 * β ^ 3 = (β ^ 3 + γ ^ 3) + (β ^ 3 - γ ^ 3) := by ring
      _ = -27 * q + (-3 * (2 * ω + 1) * δ) := by rw [hsum_cube, hdiff_cube]
      _ = 2 * (-(27 / 2 : E) * q - (3 / 2 : E) * (2 * ω + 1) * δ) := by field_simp [h2]; ring
  have hγ_cube : γ ^ 3 = -(27 / 2 : E) * q + (3 / 2 : E) * (2 * ω + 1) * δ := by
    apply mul_left_cancel₀ h2
    calc 2 * γ ^ 3 = (β ^ 3 + γ ^ 3) - (β ^ 3 - γ ^ 3) := by ring
      _ = -27 * q - (-3 * (2 * ω + 1) * δ) := by rw [hsum_cube, hdiff_cube]
      _ = 2 * (-(27 / 2 : E) * q + (3 / 2 : E) * (2 * ω + 1) * δ) := by field_simp [h2]; ring
  have hrec0 : α₀ = (β + γ) / 3 := by
    apply mul_left_cancel₀ h3
    rw [mul_div_cancel₀ _ h3, hβ_lin, hγ_lin, hα0]
    ring
  have hrec1 : α₁ = (ω ^ 2 * β + ω * γ) / 3 := by
    apply mul_left_cancel₀ h3
    rw [mul_div_cancel₀ _ h3, hβ_lin, hγ_lin]
    linear_combination (3 * α₁ - (α₁ - α₂) * ω) * hω
  have hrec2 : α₂ = (ω * β + ω ^ 2 * γ) / 3 := by
    apply mul_left_cancel₀ h3
    rw [mul_div_cancel₀ _ h3, hβ_lin, hγ_lin]
    linear_combination (3 * α₂ - (α₂ - α₁) * ω) * hω
  exact ⟨hω_sq3, hωδ_sq, hβγ, hβγ_cube, hsum_cube, hquad_poly, hβ_cube, hγ_cube,
    hrec0, hrec1, hrec2⟩

/-- Restricting an explicit linear factorization `GarlingSplitsExplicit K N f n c α` to any
intermediate field `E : IntermediateField K N` containing all roots `α i`. -/
theorem garlingSplitsExplicit_of_mem_intermediateField {K : Type u} {N : Type v}
    [Field K] [Field N] [Algebra K N] (E : IntermediateField K N)
    {f : K[X]} {n : ℕ} {c : K} {α : Fin n → N}
    (hexp : GarlingSplitsExplicit K N f n c α)
    (hmem : ∀ i : Fin n, α i ∈ E) :
    GarlingSplitsExplicit K E f n c (fun i => ⟨α i, hmem i⟩) := by
  unfold GarlingSplitsExplicit
  apply Polynomial.map_injective E.val.toRingHom E.val.injective
  rw [Polynomial.map_map]
  have hcomp_K : E.val.toRingHom.comp (algebraMap K E) = algebraMap K N :=
    RingHom.ext fun _ => rfl
  rw [hcomp_K, hexp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  have hc : E.val.toRingHom (algebraMap K E c) = algebraMap K N c := rfl
  have hprod : (∏ i : Fin n,
      (Polynomial.X - Polynomial.C (⟨α i, hmem i⟩ : E) : E[X]).map E.val.toRingHom) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hc, hprod]

/-- Auxiliary solver for `g = X^3 + C p * X + C q` inside an arbitrary opaque ambient extension
`N : Type u` over `K` in which both `g` and `X^3 - 1` split. -/
private theorem depressed_cubic_solvable_in_ambient {K N : Type u} [Field K] [Field N]
    [Algebra K N] (h2K : (2 : K) ≠ 0) (h3K : (3 : K) ≠ 0) (p q : K)
    (hsp_g : ((Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]).map
      (algebraMap K N)).Splits)
    (hsp_c3 : ((Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N)).Splits) :
    IsGarlingSolvableByRadicals
      (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]) := by
  let g : K[X] := Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q
  have hg_mon : g.Monic := by
    dsimp [g]
    rw [add_assoc]
    refine Polynomial.monic_X_pow_add ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
  have hg_deg : g.natDegree = 3 := by
    dsimp [g]
    rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 3
    · compute_degree!
  obtain ⟨m, c, α, hexpN⟩ := (garlingSplitsOver_iff_splits K N g).mpr hsp_g
  have hc1 : c = 1 := (garlingSplitsExplicit_props hg_mon.ne_zero hexpN).1.trans hg_mon.leadingCoeff
  have hm3 : m = 3 := ((garlingSplitsExplicit_props hg_mon.ne_zero hexpN).2.2.1).trans hg_deg
  subst hm3 hc1
  have hfacN : (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) *
      (Polynomial.X - Polynomial.C (α 2)) =
      Polynomial.X ^ 3 + Polynomial.C (algebraMap K N p) * Polynomial.X +
        Polynomial.C (algebraMap K N q) := by
    have heq := hexpN.symm
    rw [Fin.prod_univ_three] at heq
    simp only [g, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, map_one, one_mul, mul_assoc] at heq ⊢
    exact heq
  have h2N : (2 : N) ≠ 0 := by
    rw [← map_ofNat (algebraMap K N) 2]; exact (map_ne_zero (algebraMap K N)).mpr h2K
  have h3N : (3 : N) ≠ 0 := by
    rw [← map_ofNat (algebraMap K N) 3]; exact (map_ne_zero (algebraMap K N)).mpr h3K
  have hc3_mon : (Polynomial.X ^ 3 - 1 : K[X]).Monic := by
    have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.monic_X_pow_sub_C 1 (by decide)
  have hc3_deg : (Polynomial.X ^ 3 - 1 : K[X]).natDegree = 3 := by
    have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.natDegree_X_pow_sub_C
  obtain ⟨m_c, c_c, ρ_c, hexp_c⟩ :=
    (garlingSplitsOver_iff_splits K N (Polynomial.X ^ 3 - 1)).mpr hsp_c3
  have hm_c3 : m_c = 3 :=
    ((garlingSplitsExplicit_props hc3_mon.ne_zero hexp_c).2.2.1).trans hc3_deg
  subst hm_c3
  have hdisc_c3 : garlingDiscriminant (Polynomial.X ^ 3 - 1 : K[X]) ≠ 0 := by
    have heq : (Polynomial.X ^ 3 - 1 : K[X]) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1) := by
      simp [sub_eq_add_neg]
    rw [heq, garlingDiscriminant_depressed_cubic]
    have h27K : (27 : K) ≠ 0 := by
      have : (27 : K) = 3 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h3K
    intro h0; apply h27K; linear_combination -h0
  have hinj_ρc : Function.Injective ρ_c := by
    by_contra hninj
    have hd0 : garlingDeltaTuple ρ_c = 0 := (garlingDeltaTuple_eq_zero_iff ρ_c).mpr hninj
    have hdisc0 : algebraMap K N (garlingDiscriminant (Polynomial.X ^ 3 - 1 : K[X])) = 0 := by
      rw [garlingDiscriminant_eq_discTuple hc3_mon.ne_zero hexp_c, garlingDiscTuple, hd0,
        zero_pow (by decide)]
    exact hdisc_c3 ((map_eq_zero_iff (algebraMap K N) (algebraMap K N).injective).mp hdisc0)
  have hρc_cube : ∀ i : Fin 3, (ρ_c i) ^ 3 - 1 = 0 := by
    intro i
    have hev : ((Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N)).eval (ρ_c i) = 0 := by
      rw [hexp_c, Polynomial.eval_mul, Polynomial.eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    simpa using hev
  have hex_ω : ∃ ω : N, ω ^ 2 + ω + 1 = 0 := by
    by_cases h0 : ρ_c 0 = 1
    · have h1_ne : ρ_c 1 ≠ 1 := fun h1 =>
        absurd (hinj_ρc (h1.trans h0.symm)) (by decide)
      refine ⟨ρ_c 1, ?_⟩
      have hmul : (ρ_c 1 - 1) * ((ρ_c 1) ^ 2 + ρ_c 1 + 1) = 0 := by linear_combination hρc_cube 1
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1_ne)
    · refine ⟨ρ_c 0, ?_⟩
      have hmul : (ρ_c 0 - 1) * ((ρ_c 0) ^ 2 + ρ_c 0 + 1) = 0 := by linear_combination hρc_cube 0
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h0)
  obtain ⟨ω, hω⟩ := hex_ω
  have hω_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hres := section_14_3_resolvent_identities h2N h3N hfacN hω
  let δ : N := (α 1 - α 0) * (α 2 - α 0) * (α 2 - α 1)
  let β : N := α 0 + ω * α 1 + ω ^ 2 * α 2
  let γ : N := α 0 + ω ^ 2 * α 1 + ω * α 2
  have hδ_eq_tuple : δ = garlingDeltaTuple α := by
    rw [garlingDeltaTuple_three]
  have hδ_sq_K : δ ^ 2 = algebraMap K N (garlingDiscriminant g) := by
    rw [hδ_eq_tuple, ← garlingDiscTuple, garlingDiscriminant_eq_discTuple hg_mon.ne_zero hexpN]
  let rad_tup : Fin 4 → N := ![δ, ω, β, γ]
  let exp_tup : Fin 4 → ℕ := ![2, 3, 3, 3]
  let E : IntermediateField K N := IntermediateField.adjoin K (Set.range rad_tup)
  have hrad_KE : IsGarlingExtensionByRadicals K E := by
    refine isGarlingExtensionByRadicals_adjoin_tuple rad_tup exp_tup
      (fun i => by fin_cases i <;> decide) (fun i => ?_)
    fin_cases i
    · change δ ^ 2 ∈ garlingRadPrefix K rad_tup 0
      rw [garlingRadPrefix_zero, hδ_sq_K]
      exact (⊥ : IntermediateField K N).algebraMap_mem _
    · change ω ^ 3 ∈ garlingRadPrefix K rad_tup 1
      rw [hω_cube]
      exact (garlingRadPrefix K rad_tup 1).one_mem
    · change β ^ 3 ∈ garlingRadPrefix K rad_tup 2
      rw [hres.2.2.2.2.2.2.1]
      let F2 := garlingRadPrefix K rad_tup 2
      have hδ_F2 : δ ∈ F2 :=
        garlingRadPrefix_mem_of_lt K rad_tup (k := 0) (j := 2) (by decide)
      have hω_F2 : ω ∈ F2 :=
        garlingRadPrefix_mem_of_lt K rad_tup (k := 1) (j := 2) (by decide)
      have hq_F2 : algebraMap K N q ∈ F2 := F2.algebraMap_mem q
      have hc1_F2 : -(27 / 2 : N) ∈ F2 := by
        have : -(27 / 2 : N) = algebraMap K N (-(27 / 2 : K)) := by
          simp only [map_neg, map_div₀, map_ofNat]
        rw [this]; exact F2.algebraMap_mem _
      have hc2_F2 : (3 / 2 : N) ∈ F2 := by
        have : (3 / 2 : N) = algebraMap K N (3 / 2 : K) := by
          simp only [map_div₀, map_ofNat]
        rw [this]; exact F2.algebraMap_mem _
      have h2_F2 : (2 : N) ∈ F2 := by
        have : (2 : N) = algebraMap K N 2 := by simp only [map_ofNat]
        rw [this]; exact F2.algebraMap_mem 2
      exact F2.sub_mem (F2.mul_mem hc1_F2 hq_F2)
        (F2.mul_mem (F2.mul_mem hc2_F2 (F2.add_mem (F2.mul_mem h2_F2 hω_F2) F2.one_mem)) hδ_F2)
    · change γ ^ 3 ∈ garlingRadPrefix K rad_tup 3
      rw [hres.2.2.2.2.2.2.2.1]
      let F3 := garlingRadPrefix K rad_tup 3
      have hδ_F3 : δ ∈ F3 :=
        garlingRadPrefix_mem_of_lt K rad_tup (k := 0) (j := 3) (by decide)
      have hω_F3 : ω ∈ F3 :=
        garlingRadPrefix_mem_of_lt K rad_tup (k := 1) (j := 3) (by decide)
      have hq_F3 : algebraMap K N q ∈ F3 := F3.algebraMap_mem q
      have hc1_F3 : -(27 / 2 : N) ∈ F3 := by
        have : -(27 / 2 : N) = algebraMap K N (-(27 / 2 : K)) := by
          simp only [map_neg, map_div₀, map_ofNat]
        rw [this]; exact F3.algebraMap_mem _
      have hc2_F3 : (3 / 2 : N) ∈ F3 := by
        have : (3 / 2 : N) = algebraMap K N (3 / 2 : K) := by
          simp only [map_div₀, map_ofNat]
        rw [this]; exact F3.algebraMap_mem _
      have h2_F3 : (2 : N) ∈ F3 := by
        have : (2 : N) = algebraMap K N 2 := by simp only [map_ofNat]
        rw [this]; exact F3.algebraMap_mem 2
      exact F3.add_mem (F3.mul_mem hc1_F3 hq_F3)
        (F3.mul_mem (F3.mul_mem hc2_F3 (F3.add_mem (F3.mul_mem h2_F3 hω_F3) F3.one_mem)) hδ_F3)
  have hω_E : ω ∈ E := IntermediateField.subset_adjoin K _ ⟨1, rfl⟩
  have hβ_E : β ∈ E := IntermediateField.subset_adjoin K _ ⟨2, rfl⟩
  have hγ_E : γ ∈ E := IntermediateField.subset_adjoin K _ ⟨3, rfl⟩
  have h3_E : (3 : N) ∈ E := by
    have : (3 : N) = algebraMap K N 3 := by simp only [map_ofNat]
    rw [this]; exact E.algebraMap_mem 3
  have hα0_E : α 0 ∈ E := by
    rw [hres.2.2.2.2.2.2.2.2.1]
    exact E.div_mem (E.add_mem hβ_E hγ_E) h3_E
  have hα1_E : α 1 ∈ E := by
    rw [hres.2.2.2.2.2.2.2.2.2.1]
    exact E.div_mem
      (E.add_mem (E.mul_mem (pow_mem hω_E 2) hβ_E) (E.mul_mem hω_E hγ_E)) h3_E
  have hα2_E : α 2 ∈ E := by
    rw [hres.2.2.2.2.2.2.2.2.2.2]
    exact E.div_mem
      (E.add_mem (E.mul_mem hω_E hβ_E) (E.mul_mem (pow_mem hω_E 2) hγ_E)) h3_E
  have hα_mem : ∀ i : Fin 3, α i ∈ E := by
    intro i; fin_cases i
    · exact hα0_E
    · exact hα1_E
    · exact hα2_E
  exact ⟨E, inferInstance, inferInstance, hrad_KE,
    ⟨3, 1, _, garlingSplitsExplicit_of_mem_intermediateField E hexpN hα_mem⟩⟩

/-- **§14.3 Main-Text Solvability of Cubics by Radicals** (printed pp. 113–115 / PDF pp. 121–123):
Over **every** field `K` with `char K ≠ 2` and `char K ≠ 3`, **every** non-zero polynomial
`f ∈ K[x]` of degree `≤ 3` (in particular every cubic polynomial of degree `3`, reducible or
irreducible, monic or non-monic) is solvable by radicals (`IsGarlingSolvableByRadicals f`), via
Garling's 4-step radical tower `K ≤ K(δ) ≤ K(δ, ω) ≤ K(δ, ω, β) ≤ K(δ, ω, β, γ)`. -/
theorem cubic_solvable_by_radicals {K : Type u} [Field K]
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {f : K[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree ≤ 3) :
    IsGarlingSolvableByRadicals f := by
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h3K : (3 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  by_cases hle2 : f.natDegree ≤ 2
  · by_cases hdeg2 : f.natDegree = 2
    · exact quadratic_solvable_by_radicals hchar2 hdeg2
    · have hle1 : f.natDegree ≤ 1 := by omega
      refine ⟨K, inferInstance, inferInstance, isGarlingExtensionByRadicals_self K, ?_⟩
      rw [garlingSplitsOver_iff_splits, Algebra.algebraMap_self, Polynomial.map_id]
      exact Polynomial.Splits.of_natDegree_le_one hle1
  · have hdeg3 : f.natDegree = 3 := by omega
    have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    let f_mon : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
    have hf_eq : f = Polynomial.C f.leadingCoeff * f_mon := by
      dsimp [f_mon]
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne, map_one, one_mul]
    rw [hf_eq, isGarlingSolvableByRadicals_C_mul_iff hlc_ne]
    have hf_mon_mon : f_mon.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hlc_ne]
    have hf_mon_deg : f_mon.natDegree = 3 := by
      dsimp [f_mon]
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_ne), hdeg3]
    let a₂ : K := f_mon.coeff 2
    let a₁ : K := f_mon.coeff 1
    let a₀ : K := f_mon.coeff 0
    have hf_mon_expand : f_mon =
        Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
          Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀ := by
      rw [f_mon.as_sum_range' 4 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
      have hc3 : f_mon.coeff 3 = 1 := by
        rw [← hf_mon_deg, ← Polynomial.leadingCoeff, hf_mon_mon.leadingCoeff]
      simp only [hc3, a₂, a₁, a₀, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
        map_one, one_mul, mul_one]
      ring
    rw [hf_mon_expand]
    let p : K := depressedCubicP a₂ a₁
    let q : K := depressedCubicQ a₂ a₁ a₀
    let g : K[X] := Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q
    have hdep := (section_14_3_depress_cubic hchar3 a₂ a₁ a₀).1
    rw [← isGarlingSolvableByRadicals_comp_X_add_C_iff _ (-a₂ / 3), hdep]
    have hg_mon : g.Monic := by
      dsimp [g]
      rw [add_assoc]
      refine Polynomial.monic_X_pow_add ?_
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
    have hc3_mon : (Polynomial.X ^ 3 - 1 : K[X]).Monic := by
      have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
      rw [this]; exact Polynomial.monic_X_pow_sub_C 1 (by decide)
    let P : K[X] := g * (Polynomial.X ^ 3 - 1)
    let N : Type u := Polynomial.SplittingField P
    let _ : Field N := Polynomial.SplittingField.instField P
    let _ : Algebra K N := Polynomial.SplittingField.instAlgebra P
    have hsp_P : (P.map (algebraMap K N)).Splits := Polynomial.SplittingField.splits P
    rw [Polynomial.map_mul] at hsp_P
    have hg_map_ne0 : g.map (algebraMap K N) ≠ 0 := (hg_mon.map (algebraMap K N)).ne_zero
    have hc3_map_ne0 : (Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N) ≠ 0 :=
      (hc3_mon.map (algebraMap K N)).ne_zero
    obtain ⟨hsp_g, hsp_c3⟩ := (Polynomial.splits_mul hg_map_ne0 hc3_map_ne0).mp hsp_P
    exact depressed_cubic_solvable_in_ambient (N := N) h2K h3K p q hsp_g hsp_c3

/-! ### Exercise 14.5: Auxiliary Quadratic `g = 3x² - 3αx - p` & Repaired `h` (§14.3, p. 115; `QUEUE.md`) -/

/-- **Counterexamples to the printed polynomial `h = 27x⁶ + 27q³ - p³` and `β = 0` edge case in
`Exercise 14.5`** (`BRIEF.md` Flag 2 & `QUEUE.md`):
1. At `p = 0, q = -8` (`f = x³ - 8 ∈ ℚ[x]`, root `α = 2`, `g = 3x² - 6x`), `g` splits over `ℚ`
   with roots `β = 2` and `β = 0`:
   - `h_printed(2) = -12096 ≠ 0` and `h_printed(0) = -13824 ≠ 0`, while `h_repaired(2) = 0` and
     `h_repaired(0) = 0`;
   - at the root `β = 0` of `g`, `3β = 0` is non-invertible and `β - p/(3β) = 0 ≠ α = 2`.
2. At `p = -3, q = 2` (`f = x³ - 3x + 2 ∈ ℚ[x]`, root `α = 1`, `g = 3x² - 3x + 3`), in any
   splitting field `E` of `g`, every root `β` of `g` has `β ≠ 0`, `β³ = -1`, and
   `h_repaired(β) = 0`, yet `h_printed(β) = 270 ≠ 0` (refuting `h_printed` even when `p ≠ 0`). -/
theorem exercise_14_5_counterexamples :
    -- 1. `p = 0, q = -8, α = 2`: both roots `β ∈ {2, 0}` of `g` refute `h_printed`, and `β = 0` refutes `α = β - p/(3β)`
    (let f₁ : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-8)
     let g₁ : ℚ[X] := Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C (3 * 2) * Polynomial.X - Polynomial.C 0
     let h₁_printed : ℚ[X] := Polynomial.C 27 * Polynomial.X ^ 6 + Polynomial.C (27 * (-8) ^ 3 - 0 ^ 3)
     let h₁_repaired : ℚ[X] :=
       Polynomial.C 27 * Polynomial.X ^ 6 + Polynomial.C (27 * (-8)) * Polynomial.X ^ 3 - Polynomial.C (0 ^ 3)
     Polynomial.aeval (2 : ℚ) f₁ = 0 ∧
     IsGarlingSplittingFieldExtension ℚ ℚ g₁ ∧
     Polynomial.aeval (2 : ℚ) g₁ = 0 ∧
     Polynomial.aeval (0 : ℚ) g₁ = 0 ∧
     Polynomial.aeval (2 : ℚ) h₁_printed = -12096 ∧
     Polynomial.aeval (2 : ℚ) h₁_printed ≠ 0 ∧
     Polynomial.aeval (0 : ℚ) h₁_printed = -13824 ∧
     Polynomial.aeval (0 : ℚ) h₁_printed ≠ 0 ∧
     Polynomial.aeval (2 : ℚ) h₁_repaired = 0 ∧
     Polynomial.aeval (0 : ℚ) h₁_repaired = 0 ∧
     ((0 : ℚ) - 0 / (3 * 0)) ≠ (2 : ℚ)) ∧
    -- 2. `p = -3, q = 2, α = 1`: `p ≠ 0`, every root `β` of `g` in `SplittingField g` has `h_printed(β) = 270 ≠ 0`
    (let f₂ : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C (-3) * Polynomial.X + Polynomial.C 2
     let g₂ : ℚ[X] := Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C (3 * 1) * Polynomial.X - Polynomial.C (-3)
     let h₂_printed : ℚ[X] := Polynomial.C 27 * Polynomial.X ^ 6 + Polynomial.C (27 * 2 ^ 3 - (-3) ^ 3)
     let h₂_repaired : ℚ[X] :=
       Polynomial.C 27 * Polynomial.X ^ 6 + Polynomial.C (27 * 2) * Polynomial.X ^ 3 - Polynomial.C ((-3) ^ 3)
     let E := Polynomial.SplittingField g₂
     Polynomial.aeval (1 : ℚ) f₂ = 0 ∧
     (∃ β : E, Polynomial.aeval β g₂ = 0) ∧
     (∀ β : E, Polynomial.aeval β g₂ = 0 →
       β ≠ 0 ∧
       Polynomial.aeval β h₂_repaired = 0 ∧
       Polynomial.aeval β h₂_printed = 270 ∧
       Polynomial.aeval β h₂_printed ≠ 0)) := by
  refine ⟨?_, ?_⟩
  · intro f₁ g₁ h₁_printed h₁_repaired
    have hsf_g₁ : IsGarlingSplittingFieldExtension ℚ ℚ g₁ := by
      refine ⟨⟨2, 3, ![0, 2], ?_⟩, fun M hM _ => hM (Subsingleton.elim M ⊤)⟩
      change g₁.map (RingHom.id ℚ) = _
      rw [Polynomial.map_id, Fin.prod_univ_two]
      dsimp [g₁]
      norm_num
      simp only [map_ofNat]
      ring
    refine ⟨by simp [f₁]; norm_num, hsf_g₁, by simp [g₁]; norm_num, by simp [g₁],
      by simp [h₁_printed]; norm_num, by simp [h₁_printed]; norm_num,
      by simp [h₁_printed]; norm_num, by simp [h₁_printed],
      by simp [h₁_repaired]; norm_num, by simp [h₁_repaired], by norm_num⟩
  · intro f₂ g₂ h₂_printed h₂_repaired E
    let _ : Field E := Polynomial.SplittingField.instField g₂
    let _ : Algebra ℚ E := Polynomial.SplittingField.instAlgebra g₂
    have hg₂_deg : g₂.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (by
        intro h0; have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h0; simp [g₂] at hc)]
      have hd : g₂.natDegree = 2 := by dsimp [g₂]; compute_degree!
      rw [hd]; decide
    have hsp_g₂ : (g₂.map (algebraMap ℚ E)).Splits := Polynomial.SplittingField.splits g₂
    obtain ⟨β₀, hβ₀⟩ := Polynomial.Splits.exists_eval_eq_zero hsp_g₂
      (by rwa [Polynomial.degree_map])
    have hβ₀_aev : Polynomial.aeval β₀ g₂ = 0 := by
      rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
    refine ⟨by simp [f₂]; norm_num, ⟨β₀, hβ₀_aev⟩, fun β hβ => ?_⟩
    have hquad : 3 * β ^ 2 - 3 * β + 3 = 0 := by
      dsimp [g₂] at hβ
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        Polynomial.aeval_X] at hβ
      linear_combination hβ
    have hβ_cube : β ^ 3 = -1 := by
      have h3 : 3 * (β ^ 3 + 1) = 0 := by linear_combination (β + 1) * hquad
      have h3_ne0 : (3 : E) ≠ 0 := by norm_num
      have h1 := (mul_eq_zero.mp h3).resolve_left h3_ne0
      linear_combination h1
    have hβ_ne0 : β ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by decide)] at hβ_cube
      norm_num at hβ_cube
    have hβ6 : β ^ 6 = 1 := by
      calc β ^ 6 = (β ^ 3) ^ 2 := by ring
        _ = (-1) ^ 2 := by rw [hβ_cube]
        _ = 1 := by norm_num
    have hrep0 : Polynomial.aeval β h₂_repaired = 0 := by
      dsimp [h₂_repaired]
      simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat,
        Polynomial.aeval_X]
      rw [hβ6, hβ_cube]
      norm_num
    have hprt270 : Polynomial.aeval β h₂_printed = 270 := by
      dsimp [h₂_printed]
      simp only [map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat,
        Polynomial.aeval_X]
      rw [hβ6]
      norm_num
    exact ⟨hβ_ne0, hrep0, hprt270, by rw [hprt270]; norm_num⟩

/-- **Exercise 14.5 — Repaired Characterization** (§14.3, printed p. 115 / PDF p. 123;
`BRIEF.md` Flag 2 & `QUEUE.md`):
Suppose `char K ≠ 2, 3`, `f = x³ + px + q ∈ K[x]`, `α` is a root of `f` in an extension `L : K`
(such as a splitting field for `f`), `g = 3x² - 3αx - p ∈ K(α)[x]`, and `E : K(α)` is a splitting
field extension for `g`:
1. **Every** root `β ∈ E` of `g` (including `β = 0` when `p = 0`) is a root of the repaired sextic
   `h_repaired = 27x⁶ + 27qx³ - p³ ∈ K[x]`;
2. Whenever `β ≠ 0` (which holds automatically for every root `β` of `g` when `p ≠ 0`, and is
   realized by `β = α ∈ E` when `p = 0` and `α ≠ 0`), `3β ≠ 0`, `α = β - p / (3β)` in `E`, and
   `δ := β³ + q/2` satisfies `β³ = -q/2 + δ` and `δ² = q²/4 + p³/27`;
3. `g` always has a root `β ∈ E` (and a non-zero root `β ≠ 0` whenever `p ≠ 0 ∨ α ≠ 0`), and `f`
   is solvable by radicals over `K` (`IsGarlingSolvableByRadicals f`). -/
theorem exercise_14_5_repaired {K : Type u} {L : Type v} {E : Type w}
    [Field K] [Field L] [Field E] [Algebra K L]
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (p q : K) {α : L}
    (hα_root : Polynomial.aeval α
      (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) = 0)
    [Algebra (IntermediateField.adjoin K ({α} : Set L)) E]
    [Algebra K E]
    [IsScalarTower K (IntermediateField.adjoin K ({α} : Set L)) E]
    (hsf_g :
      let Kα := IntermediateField.adjoin K ({α} : Set L)
      let α₀ : Kα := ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
      IsGarlingSplittingFieldExtension Kα E
        (Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C (3 * α₀) * Polynomial.X -
          Polynomial.C (algebraMap K Kα p))) :
    let Kα := IntermediateField.adjoin K ({α} : Set L)
    let α₀ : Kα := ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
    let αE : E := algebraMap Kα E α₀
    let g : Kα[X] :=
      Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C (3 * α₀) * Polynomial.X -
        Polynomial.C (algebraMap K Kα p)
    let h_repaired : K[X] :=
      Polynomial.C 27 * Polynomial.X ^ 6 + Polynomial.C (27 * q) * Polynomial.X ^ 3 -
        Polynomial.C (p ^ 3)
    -- 1. Every root `β` of `g` in `E` satisfies `h_repaired(β) = 0`
    (∀ β : E, Polynomial.aeval β g = 0 → Polynomial.aeval β h_repaired = 0) ∧
    -- 2. For every non-zero root `β` of `g` in `E`, `3β ≠ 0`, `α = β - p/(3β)`, `β³ = -q/2 + δ`, `δ² = q²/4 + p³/27`
    (∀ β : E, Polynomial.aeval β g = 0 → β ≠ 0 →
      3 * β ≠ 0 ∧
      αE = β - algebraMap K E p / (3 * β) ∧
      ∃ δ : E,
        β ^ 3 = -algebraMap K E (q / 2) + δ ∧
        δ ^ 2 = algebraMap K E (q ^ 2 / 4 + p ^ 3 / 27)) ∧
    -- 3. Automatic non-vanishing when `p ≠ 0`, existence of root `β` (and `β ≠ 0` if `p ≠ 0 ∨ α ≠ 0`), and solvability
    (∀ β : E, Polynomial.aeval β g = 0 → p ≠ 0 → β ≠ 0) ∧
    (∃ β : E, Polynomial.aeval β g = 0) ∧
    ((p ≠ 0 ∨ α ≠ 0) → ∃ β : E, Polynomial.aeval β g = 0 ∧ β ≠ 0) ∧
    IsGarlingSolvableByRadicals
      (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) := by
  intro Kα α₀ αE g h_repaired
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h3K : (3 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap K E) 2]; exact (map_ne_zero (algebraMap K E)).mpr h2K
  have h3E : (3 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap K E) 3]; exact (map_ne_zero (algebraMap K E)).mpr h3K
  have h4E : (4 : E) ≠ 0 := by
    have : (4 : E) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2E
  have h27E : (27 : E) ≠ 0 := by
    have : (27 : E) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3E
  -- Lift `α^3 + p*α + q = 0` from `L` to `Kα` and then to `E`:
  have hα₀_cubic : α₀ ^ 3 + algebraMap K Kα p * α₀ + algebraMap K Kα q = 0 := by
    apply Subtype.ext
    change α ^ 3 + algebraMap K L p * α + algebraMap K L q = 0
    simpa using hα_root
  have hαE_cubic : αE ^ 3 + algebraMap K E p * αE + algebraMap K E q = 0 := by
    have h := congrArg (algebraMap Kα E) hα₀_cubic
    simp only [map_add, map_pow, map_mul, map_zero, ← IsScalarTower.algebraMap_apply K Kα E] at h
    exact h
  have hg_rel : ∀ β : E, Polynomial.aeval β g = 0 ↔
      3 * β ^ 2 - 3 * αE * β - algebraMap K E p = 0 := by
    intro β
    dsimp [g]
    simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X, Polynomial.aeval_C, αE,
      ← IsScalarTower.algebraMap_apply K Kα E]
  have hpart1 : ∀ β : E, Polynomial.aeval β g = 0 → Polynomial.aeval β h_repaired = 0 := by
    intro β hβ
    have hg0 := (hg_rel β).mp hβ
    have h3αβ : 3 * αE * β = 3 * β ^ 2 - algebraMap K E p := by linear_combination -hg0
    have hcube_id : (3 * αE * β) ^ 3 + 9 * algebraMap K E p * (3 * αE * β) * β ^ 2 +
        27 * algebraMap K E q * β ^ 3 = 0 := by
      calc (3 * αE * β) ^ 3 + 9 * algebraMap K E p * (3 * αE * β) * β ^ 2 +
            27 * algebraMap K E q * β ^ 3
          = 27 * (αE ^ 3 + algebraMap K E p * αE + algebraMap K E q) * β ^ 3 := by ring
        _ = 0 := by simp [hαE_cubic]
    rw [h3αβ] at hcube_id
    dsimp [h_repaired]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination hcube_id
  have hpart2 : ∀ β : E, Polynomial.aeval β g = 0 → β ≠ 0 →
      3 * β ≠ 0 ∧
      αE = β - algebraMap K E p / (3 * β) ∧
      ∃ δ : E,
        β ^ 3 = -algebraMap K E (q / 2) + δ ∧
        δ ^ 2 = algebraMap K E (q ^ 2 / 4 + p ^ 3 / 27) := by
    intro β hβ hβ0
    have h3β : 3 * β ≠ 0 := mul_ne_zero h3E hβ0
    have hg0 := (hg_rel β).mp hβ
    have hα_expr : αE = β - algebraMap K E p / (3 * β) := by
      apply mul_right_cancel₀ h3β
      have hdiv : (β - algebraMap K E p / (3 * β)) * (3 * β) =
          3 * β ^ 2 - algebraMap K E p := by
        rw [sub_mul, div_mul_cancel₀ _ h3β]
        ring
      rw [hdiv]
      linear_combination -hg0
    have hsextic : 27 * β ^ 6 + 27 * algebraMap K E q * β ^ 3 - (algebraMap K E p) ^ 3 = 0 := by
      have h := hpart1 β hβ
      dsimp [h_repaired] at h
      simpa [map_sub, map_add, map_mul, map_pow, map_ofNat] using h
    let δ : E := β ^ 3 + algebraMap K E (q / 2)
    have hβ3_eq : β ^ 3 = -algebraMap K E (q / 2) + δ := by dsimp [δ]; ring
    have hδ_sq : δ ^ 2 = algebraMap K E (q ^ 2 / 4 + p ^ 3 / 27) := by
      have h108 : (108 : E) ≠ 0 := by
        have : (108 : E) = 4 * 27 := by norm_num
        rw [this]; exact mul_ne_zero h4E h27E
      apply mul_left_cancel₀ h108
      dsimp [δ]
      simp only [map_add, map_div₀, map_pow, map_ofNat]
      have hlhs : 108 * (β ^ 3 + algebraMap K E q / 2) ^ 2 =
          108 * β ^ 6 + 108 * algebraMap K E q * β ^ 3 + 27 * (algebraMap K E q) ^ 2 := by
        field_simp [h2E]; ring
      have hrhs : 108 * ((algebraMap K E q) ^ 2 / 4 + (algebraMap K E p) ^ 3 / 27) =
          27 * (algebraMap K E q) ^ 2 + 4 * (algebraMap K E p) ^ 3 := by
        field_simp [h4E, h27E]; ring
      rw [hlhs, hrhs]
      linear_combination 4 * hsextic
    exact ⟨h3β, hα_expr, ⟨δ, hβ3_eq, hδ_sq⟩⟩
  have hp_ne0_imp : ∀ β : E, Polynomial.aeval β g = 0 → p ≠ 0 → β ≠ 0 := by
    intro β hβ hp0 hβ0
    have hg0 := (hg_rel β).mp hβ
    rw [hβ0] at hg0
    simp at hg0
    exact hp0 hg0
  -- Existence of a root `β ∈ E` of `g` (since `g` has degree `2` and splits over `E`):
  have h3Kα : (3 : Kα) ≠ 0 := by
    rw [← map_ofNat (algebraMap K Kα) 3]; exact (map_ne_zero (algebraMap K Kα)).mpr h3K
  have hg_deg : g.natDegree = 2 := by
    dsimp [g]
    have hlead : (Polynomial.C (3 : Kα) * Polynomial.X ^ 2).natDegree = 2 := by
      rw [Polynomial.natDegree_C_mul h3Kα, Polynomial.natDegree_X_pow]
    have hlow : (Polynomial.C (3 * α₀) * Polynomial.X +
        Polynomial.C (algebraMap K Kα p)).natDegree < 2 := by
      compute_degree!
    have heq_sub : Polynomial.C (3 : Kα) * Polynomial.X ^ 2 -
        Polynomial.C (3 * α₀) * Polynomial.X - Polynomial.C (algebraMap K Kα p) =
        Polynomial.C (3 : Kα) * Polynomial.X ^ 2 -
          (Polynomial.C (3 * α₀) * Polynomial.X + Polynomial.C (algebraMap K Kα p)) := by ring
    rw [heq_sub, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (hlow.trans_eq hlead.symm)]
    exact hlead
  have hsp_gE : (g.map (algebraMap Kα E)).Splits :=
    ((isGarlingSplittingFieldExtension_iff Kα E g).mp hsf_g).1
  obtain ⟨β₁, hβ₁_ev⟩ := Polynomial.Splits.exists_eval_eq_zero hsp_gE (by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (by
      intro h0; rw [h0] at hg_deg; simp at hg_deg), hg_deg]
    decide)
  have hβ₁_aev : Polynomial.aeval β₁ g = 0 := by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hex_nz : (p ≠ 0 ∨ α ≠ 0) → ∃ β : E, Polynomial.aeval β g = 0 ∧ β ≠ 0 := by
    intro hpa
    by_cases hp0 : p = 0
    · rcases hpa with hp_ne | hα_ne0
      · exact absurd hp0 hp_ne
      · have hα₀_ne0 : α₀ ≠ 0 := fun h => hα_ne0 (congrArg Subtype.val h)
        have hαE_ne0 : αE ≠ 0 := (map_ne_zero (algebraMap Kα E)).mpr hα₀_ne0
        refine ⟨αE, ?_, hαE_ne0⟩
        rw [hg_rel, hp0, map_zero]
        ring
    · exact ⟨β₁, hβ₁_aev, hp_ne0_imp β₁ hβ₁_aev hp0⟩
  have hf_mon : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]).Monic := by
    rw [add_assoc]
    refine Polynomial.monic_X_pow_add ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
  have hf_deg_le3 :
      (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]).natDegree ≤ 3 := by
    compute_degree!
  exact ⟨hpart1, hpart2, hp_ne0_imp, ⟨β₁, hβ₁_aev⟩, hex_nz,
    cubic_solvable_by_radicals hchar2 hchar3 hf_mon.ne_zero hf_deg_le3⟩

/-! ## §14.4 Quartic polynomials (printed pp. 115–117, PDF pp. 123–125)

Unnumbered main-text derivation solving quartics by radicals over fields of characteristic `≠ 2, 3`
via the Viergruppe fixed field `M = K(β², γ², δ²)` and the *cubic resolvent*
`x³ + 2px² + (p² - 4r)x - q²` (printed pp. 115–117), followed by **Exercises 14.6–14.8**
(printed p. 117 / PDF p. 125). -/

/-! ### Group-Theoretic Preliminaries: `viergruppe`, `s4ToS3Hom`, and `G ⊓ viergruppe` (§14.4, p. 116) -/

theorem garlingDeltaTuple_four {R : Type*} [CommRing R] (α : Fin 4 → R) :
    garlingDeltaTuple α =
      (α 1 - α 0) * (α 2 - α 0) * (α 3 - α 0) *
      (α 2 - α 1) * (α 3 - α 1) * (α 3 - α 2) := by
  unfold garlingDeltaTuple
  rw [Fin.prod_univ_four]
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  rw [h0, h1, h2, h3, Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    Finset.prod_pair (by decide), Finset.prod_singleton, Finset.prod_empty]
  ring

/-- Equality between Chapter 1's `viergruppe` (§1.1, p. 7) and Chapter 11's `s4V4`. -/
theorem viergruppe_eq_s4V4 : viergruppe = s4V4 := by
  ext σ
  change σ ∈ viergruppeFinset ↔ σ ∈ s4V4Finset
  revert σ
  decide

theorem natCard_viergruppe : Nat.card viergruppe = 4 := by
  rw [viergruppe_eq_s4V4]
  exact exercise_11_5_s4.1 0

theorem viergruppe_actsTransitively : SubgroupActsTransitively viergruppe := by
  rw [viergruppe_eq_s4V4]
  exact exercise_11_5_s4.2.1 0

theorem viergruppe_le_alternatingGroup : viergruppe ≤ alternatingGroup (Fin 4) := by
  intro σ hσ
  rw [Equiv.Perm.mem_alternatingGroup]
  change σ ∈ viergruppeFinset at hσ
  revert σ hσ
  decide

theorem viergruppe_le_s4D4 : viergruppe ≤ s4D4 := by
  intro σ hσ
  change σ ∈ viergruppeFinset at hσ
  rcases Finset.mem_insert.mp hσ with rfl | hσ
  · exact s4D4.one_mem
  · rcases Finset.mem_insert.mp hσ with rfl | hσ
    · refine ⟨DihedralGroup.sr 1, ?_⟩
      decide
    · rcases Finset.mem_insert.mp hσ with rfl | hσ
      · refine ⟨DihedralGroup.r 2, ?_⟩
        decide
      · rw [Finset.mem_singleton.mp hσ]
        refine ⟨DihedralGroup.sr 3, ?_⟩
        decide

/-- Explicit group isomorphism `viergruppe ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`
(`N ≅ ℤ₂ × ℤ₂`). -/
def zmod2ProdToViergruppePerm (p : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : SigmaN 4 :=
  (match p.1.toAdd.val with
    | 0 => (1 : SigmaN 4)
    | _ => Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) *
  (match p.2.toAdd.val with
    | 0 => (1 : SigmaN 4)
    | _ => Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3)

noncomputable def viergruppeMulEquivZMod2Prod :
    viergruppe ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := by
  have hmem : ∀ p, zmod2ProdToViergruppePerm p ∈ viergruppeFinset := by decide
  have hmul : ∀ p q,
      zmod2ProdToViergruppePerm (p * q) =
        zmod2ProdToViergruppePerm p * zmod2ProdToViergruppePerm q := by decide
  have hinj : Function.Injective zmod2ProdToViergruppePerm := by decide
  have hsurj : ∀ σ ∈ viergruppeFinset, ∃ p, zmod2ProdToViergruppePerm p = σ := by decide
  have hone : zmod2ProdToViergruppePerm 1 = 1 := by decide
  let hom : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* viergruppe :=
    { toFun := fun p => (⟨zmod2ProdToViergruppePerm p, hmem p⟩ : viergruppe)
      map_one' := Subtype.ext hone
      map_mul' := fun p q => Subtype.ext (hmul p q) }
  exact (MulEquiv.ofBijective hom
    ⟨fun p q hpq => hinj (congrArg Subtype.val hpq),
     fun ⟨σ, hσ⟩ => by
       obtain ⟨p, hp⟩ := hsurj σ hσ
       exact ⟨p, Subtype.ext hp⟩⟩).symm

/-- The three non-identity double transpositions of `viergruppe`. -/
def vPair : Fin 3 → SigmaN 4
  | 0 => Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3
  | 1 => Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3
  | 2 => Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2

/-- Ordered index quadruples `(a, b, c, d)` for the three pair products `-(α_a + α_b)(α_c + α_d)`. -/
def quarticPairIdx : Fin 3 → Fin 4 × Fin 4 × Fin 4 × Fin 4
  | 0 => (0, 1, 2, 3)
  | 1 => (0, 2, 1, 3)
  | 2 => (0, 3, 1, 2)

/-- Action of `σ ∈ Σ₄` on `Fin 3` by conjugating `vPair`, realizing §1.1's epimorphism
`φ : Σ₄ → Σ₃` (printed p. 7 & p. 116). -/
def s4ToS3Fun (σ : SigmaN 4) (i : Fin 3) : Fin 3 :=
  ⟨((σ * vPair i * σ⁻¹) 0).val - 1, by revert σ i; decide⟩

theorem vPair_injective : Function.Injective vPair := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert hij; decide)

/-- Permutation in `Σ₃` induced by conjugating `vPair` by `σ ∈ Σ₄`. -/
def s4ToS3Perm (σ : SigmaN 4) : SigmaN 3 where
  toFun := s4ToS3Fun σ
  invFun := s4ToS3Fun σ⁻¹
  left_inv := by intro i; revert σ i; decide
  right_inv := by intro i; revert σ i; decide

theorem s4ToS3Perm_spec (σ : SigmaN 4) (i : Fin 3) :
    σ * vPair i * σ⁻¹ = vPair (s4ToS3Perm σ i) := by
  revert σ i; decide

/-- Chapter 1 §1.1's epimorphism `φ : Σ₄ →* Σ₃` with kernel `viergruppe` (printed p. 7, cited on
printed p. 116). -/
def s4ToS3Hom : SigmaN 4 →* SigmaN 3 where
  toFun := s4ToS3Perm
  map_one' := by ext i; revert i; decide
  map_mul' := by
    intro σ τ
    ext i
    have h : vPair (s4ToS3Perm (σ * τ) i) = vPair (s4ToS3Perm σ (s4ToS3Perm τ i)) := by
      rw [← s4ToS3Perm_spec, ← s4ToS3Perm_spec, ← s4ToS3Perm_spec]
      group
    exact congrArg Fin.val (vPair_injective h)

theorem s4ToS3Hom_spec (σ : SigmaN 4) (i : Fin 3) :
    σ * vPair i * σ⁻¹ = vPair (s4ToS3Hom σ i) :=
  s4ToS3Perm_spec σ i

def quarticPairIdxPermCheck (σ : SigmaN 4) (i : Fin 3) : Bool :=
  let q := quarticPairIdx i
  let q' := quarticPairIdx (s4ToS3Hom σ i)
  (((σ q.1 == q'.1 && σ q.2.1 == q'.2.1) || (σ q.1 == q'.2.1 && σ q.2.1 == q'.1)) &&
    ((σ q.2.2.1 == q'.2.2.1 && σ q.2.2.2 == q'.2.2.2) ||
      (σ q.2.2.1 == q'.2.2.2 && σ q.2.2.2 == q'.2.2.1))) ||
  (((σ q.1 == q'.2.2.1 && σ q.2.1 == q'.2.2.2) || (σ q.1 == q'.2.2.2 && σ q.2.1 == q'.2.2.1)) &&
    ((σ q.2.2.1 == q'.1 && σ q.2.2.2 == q'.2.1) ||
      (σ q.2.2.1 == q'.2.1 && σ q.2.2.2 == q'.1)))

theorem quarticPairIdx_perm_cases (σ : SigmaN 4) (i : Fin 3) :
    let q := quarticPairIdx i
    let q' := quarticPairIdx (s4ToS3Hom σ i)
    (((σ q.1 = q'.1 ∧ σ q.2.1 = q'.2.1) ∨ (σ q.1 = q'.2.1 ∧ σ q.2.1 = q'.1)) ∧
      ((σ q.2.2.1 = q'.2.2.1 ∧ σ q.2.2.2 = q'.2.2.2) ∨
        (σ q.2.2.1 = q'.2.2.2 ∧ σ q.2.2.2 = q'.2.2.1))) ∨
    (((σ q.1 = q'.2.2.1 ∧ σ q.2.1 = q'.2.2.2) ∨ (σ q.1 = q'.2.2.2 ∧ σ q.2.1 = q'.2.2.1)) ∧
      ((σ q.2.2.1 = q'.1 ∧ σ q.2.2.2 = q'.2.1) ∨
        (σ q.2.2.1 = q'.2.1 ∧ σ q.2.2.2 = q'.1))) := by
  have hb : quarticPairIdxPermCheck σ i = true := by revert σ i; decide
  unfold quarticPairIdxPermCheck at hb
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hb

theorem s4ToS3Hom_surjective : Function.Surjective s4ToS3Hom := by
  intro τ; revert τ; decide

theorem s4ToS3Hom_ker : s4ToS3Hom.ker = viergruppe := by
  ext σ
  rw [MonoidHom.mem_ker]
  change s4ToS3Hom σ = 1 ↔ σ ∈ viergruppeFinset
  revert σ; decide

/-- Quotient isomorphism `(Σ₄ ⧸ viergruppe) ≃* Σ₃` (§1.1, p. 7 & §14.4, p. 116). -/
theorem s4_quot_viergruppe_mulEquiv_s3 :
    let _ : viergruppe.Normal := viergruppe_normal
    Nonempty ((SigmaN 4 ⧸ viergruppe) ≃* SigmaN 3) := by
  intro _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq s4ToS3Hom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s4ToS3Hom s4ToS3Hom_surjective)⟩

/-- Cardinalities `|(s4TransitiveModel i) ⊓ viergruppe| = ![4, 2, 4, 4, 4] i`. -/
theorem natCard_s4TransitiveModel_inf_viergruppe (i : Fin 5) :
    Nat.card (s4TransitiveModel i ⊓ viergruppe : Subgroup (SigmaN 4)) =
      (![4, 2, 4, 4, 4] : Fin 5 → ℕ) i := by
  fin_cases i
  · change Nat.card (s4V4 ⊓ viergruppe : Subgroup (SigmaN 4)) = 4
    rw [← viergruppe_eq_s4V4, inf_idem]
    exact natCard_viergruppe
  · change Nat.card (s4C4 ⊓ viergruppe : Subgroup (SigmaN 4)) = 2
    let H2 : Finset (SigmaN 4) := {1, Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3}
    have hmem_iff : ∀ σ : SigmaN 4, σ ∈ (s4C4 ⊓ viergruppe : Subgroup (SigmaN 4)) ↔ σ ∈ H2 := by
      intro σ
      constructor
      · rintro ⟨hC, hV⟩
        change σ ∈ viergruppeFinset at hV
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hC
        have h4 : (finRotate 4 : SigmaN 4) ^ 4 = 1 := by decide
        have hk_mod : (finRotate 4 : SigmaN 4) ^ k =
            (finRotate 4 : SigmaN 4) ^ ((k % 4).toNat) := by
          have hk_eq : k = 4 * (k / 4) + (k % 4).toNat := by omega
          conv_lhs => rw [hk_eq]
          rw [zpow_add, zpow_mul, zpow_ofNat, h4, one_zpow, one_mul, zpow_natCast]
        rw [hk_mod] at hV ⊢
        have hlt4 : (k % 4).toNat < 4 := by omega
        set r := (k % 4).toNat
        interval_cases r
        · decide
        · exfalso; revert hV; decide
        · decide
        · exfalso; revert hV; decide
      · intro hH2
        rcases Finset.mem_insert.mp hH2 with rfl | hH2
        · exact (s4C4 ⊓ viergruppe).one_mem
        · rw [Finset.mem_singleton.mp hH2]
          refine ⟨⟨2, by decide⟩, ?_⟩
          change Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 ∈ viergruppeFinset
          decide
    have heq_fintype : Nat.card (s4C4 ⊓ viergruppe : Subgroup (SigmaN 4)) = H2.card := by
      let e : (s4C4 ⊓ viergruppe : Subgroup (SigmaN 4)) ≃ {σ : SigmaN 4 // σ ∈ H2} :=
        { toFun := fun ⟨σ, hσ⟩ => ⟨σ, (hmem_iff σ).mp hσ⟩
          invFun := fun ⟨σ, hσ⟩ => ⟨σ, (hmem_iff σ).mpr hσ⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [heq_fintype]
    decide
  · change Nat.card (s4D4 ⊓ viergruppe : Subgroup (SigmaN 4)) = 4
    rw [inf_of_le_right viergruppe_le_s4D4]
    exact natCard_viergruppe
  · change Nat.card (alternatingGroup (Fin 4) ⊓ viergruppe : Subgroup (SigmaN 4)) = 4
    rw [inf_of_le_right viergruppe_le_alternatingGroup]
    exact natCard_viergruppe
  · change Nat.card ((⊤ : Subgroup (SigmaN 4)) ⊓ viergruppe : Subgroup (SigmaN 4)) = 4
    rw [top_inf_eq]
    exact natCard_viergruppe

/-- **§14.4 Main-Text Group Lemma** (printed p. 116 / PDF p. 124):
For every transitive subgroup `G ≤ Σ₄`, setting `H := G ⊓ viergruppe`, we have
`|H| = 2 ∨ |H| = 4` (so `|H| ≠ 1`, answering Garling's parenthetical *"why cannot `|H| = 1`?"*),
and `|G| = |H| * |G.map s4ToS3Hom|` with `G.map s4ToS3Hom ≤ Σ₃`. -/
theorem transitive_s4_inter_viergruppe_card {G : Subgroup (SigmaN 4)}
    (htr : SubgroupActsTransitively G) :
    (Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 2 ∨
      Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 4) ∧
    Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) ≠ 1 ∧
    Nat.card G =
      Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) * Nat.card (G.map s4ToS3Hom) := by
  obtain ⟨i, ⟨g, rfl⟩⟩ := (exercise_11_5_s4.2.2.1 G).mp htr
  have hnorm := viergruppe_normal
  have hmap_V : viergruppe.map (MulAut.conj g).toMonoidHom = viergruppe := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hnorm.conj_mem y hy g,
      fun hx => ⟨g⁻¹ * x * g, hnorm.conj_mem x hx g⁻¹, by group⟩⟩
  have hinf_eq : ((s4TransitiveModel i).map (MulAut.conj g).toMonoidHom ⊓ viergruppe) =
      (s4TransitiveModel i ⊓ viergruppe).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxV⟩
      have hyV : y ∈ viergruppe := by
        have h := hnorm.conj_mem (g * y * g⁻¹) hxV g⁻¹
        simpa [mul_assoc] using h
      exact ⟨y, ⟨hy, hyV⟩, rfl⟩
    · rintro ⟨y, ⟨hyM, hyV⟩, rfl⟩
      exact ⟨⟨y, hyM, rfl⟩, hnorm.conj_mem y hyV g⟩
  have hcard_inf :
      Nat.card ((s4TransitiveModel i).map (MulAut.conj g).toMonoidHom ⊓ viergruppe : Subgroup (SigmaN 4)) =
        Nat.card (s4TransitiveModel i ⊓ viergruppe : Subgroup (SigmaN 4)) := by
    rw [hinf_eq]
    exact (isConjugateSubgroup_natCard_eq ⟨g, rfl⟩).symm
  have h24 : Nat.card ((s4TransitiveModel i).map (MulAut.conj g).toMonoidHom ⊓ viergruppe :
      Subgroup (SigmaN 4)) = 2 ∨
      Nat.card ((s4TransitiveModel i).map (MulAut.conj g).toMonoidHom ⊓ viergruppe :
      Subgroup (SigmaN 4)) = 4 := by
    rw [hcard_inf, natCard_s4TransitiveModel_inf_viergruppe i]
    fin_cases i <;> decide
  have hne1 : Nat.card ((s4TransitiveModel i).map (MulAut.conj g).toMonoidHom ⊓ viergruppe :
      Subgroup (SigmaN 4)) ≠ 1 := by
    rcases h24 with h2 | h4 <;> omega
  -- Restrict `s4ToS3Hom` to `G' := (s4TransitiveModel i).map (MulAut.conj g).toMonoidHom`:
  set G' : Subgroup (SigmaN 4) := (s4TransitiveModel i).map (MulAut.conj g).toMonoidHom
  let ψ : G' →* G'.map s4ToS3Hom :=
    { toFun := fun x => ⟨s4ToS3Hom x.1, x.1, x.2, rfl⟩
      map_one' := Subtype.ext (map_one s4ToS3Hom)
      map_mul' := fun x y => Subtype.ext (map_mul s4ToS3Hom x.1 y.1) }
  have hψ_surj : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker_equiv : Nonempty (ψ.ker ≃ (G' ⊓ viergruppe : Subgroup (SigmaN 4))) := by
    refine ⟨{
      toFun := fun ⟨⟨x, hxG⟩, hxker⟩ => ⟨x, hxG, by
        have h0 : s4ToS3Hom x = 1 := congrArg Subtype.val hxker
        have hmem_ker : x ∈ s4ToS3Hom.ker := MonoidHom.mem_ker.mpr h0
        rwa [s4ToS3Hom_ker] at hmem_ker⟩
      invFun := fun ⟨x, hxG, hxV⟩ => ⟨⟨x, hxG⟩, Subtype.ext (by
        have hmem_ker : x ∈ s4ToS3Hom.ker := s4ToS3Hom_ker.symm ▸ hxV
        exact MonoidHom.mem_ker.mp hmem_ker)⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }⟩
  obtain ⟨eker⟩ := hker_equiv
  have hquot_equiv := QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj
  have hcard_prod : Nat.card G' = Nat.card (G' ⊓ viergruppe : Subgroup (SigmaN 4)) *
      Nat.card (G'.map s4ToS3Hom) := by
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr hquot_equiv.toEquiv, Nat.card_congr eker, mul_comm] at hlag
    exact hlag
  exact ⟨h24, hne1, hcard_prod⟩

/-! ### Depressing Quartics, the *Cubic Resolvent*, and Resolvent Identities (§14.4, pp. 115–117) -/

/-- Coefficient `p = a₂ - 3 a₃² / 8` of `f(x - a₃/4) = x⁴ + px² + qx + r` (§14.4, p. 115). -/
noncomputable def depressedQuarticP {K : Type*} [Field K] (a₃ a₂ : K) : K :=
  a₂ - 3 * a₃ ^ 2 / 8

/-- Coefficient `q = a₁ - a₃ a₂ / 2 + a₃³ / 8` of `f(x - a₃/4) = x⁴ + px² + qx + r` (§14.4, p. 115). -/
noncomputable def depressedQuarticQ {K : Type*} [Field K] (a₃ a₂ a₁ : K) : K :=
  a₁ - a₃ * a₂ / 2 + a₃ ^ 3 / 8

/-- Constant term `r = a₀ - a₃ a₁ / 4 + a₃² a₂ / 16 - 3 a₃⁴ / 256` of
`f(x - a₃/4) = x⁴ + px² + qx + r` (§14.4, p. 115). -/
noncomputable def depressedQuarticR {K : Type*} [Field K] (a₃ a₂ a₁ a₀ : K) : K :=
  a₀ - a₃ * a₁ / 4 + a₃ ^ 2 * a₂ / 16 - 3 * a₃ ^ 4 / 256

/-- **§14.4 Quartic Depression Identity** (printed p. 115 / PDF p. 123):
Over any field `K` with `char K ≠ 2`, substituting `x ↦ x - a₃ / 4` (`y = x + a₃ / 4`) transforms
`f = x⁴ + a₃ x³ + a₂ x² + a₁ x + a₀` into `g = x⁴ + px² + qx + r` while preserving the discriminant. -/
theorem section_14_4_depress_quartic {K : Type*} [Field K] (hchar2 : ringChar K ≠ 2)
    (a₃ a₂ a₁ a₀ : K) :
    let f : K[X] := Polynomial.X ^ 4 + Polynomial.C a₃ * Polynomial.X ^ 3 +
      Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀
    let g : K[X] := Polynomial.X ^ 4 + Polynomial.C (depressedQuarticP a₃ a₂) * Polynomial.X ^ 2 +
      Polynomial.C (depressedQuarticQ a₃ a₂ a₁) * Polynomial.X +
      Polynomial.C (depressedQuarticR a₃ a₂ a₁ a₀)
    f.comp (Polynomial.X + Polynomial.C (-a₃ / 4)) = g ∧
    garlingDiscriminant f = garlingDiscriminant g := by
  intro f g
  have h2 : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h2
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h2
  have h256 : (256 : K) ≠ 0 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero 8 h2
  have hcomp : f.comp (Polynomial.X + Polynomial.C (-a₃ / 4)) = g := by
    let s : K := -a₃ / 4
    have ha₃ : a₃ = -4 * s := by dsimp [s]; field_simp [h4]
    have hp : depressedQuarticP a₃ a₂ = a₂ - 6 * s ^ 2 := by
      unfold depressedQuarticP; rw [ha₃]; field_simp [h8]; ring
    have hq : depressedQuarticQ a₃ a₂ a₁ = a₁ + 2 * s * a₂ - 8 * s ^ 3 := by
      unfold depressedQuarticQ; rw [ha₃]; field_simp [h2, h8]; ring
    have hr : depressedQuarticR a₃ a₂ a₁ a₀ = a₀ + s * a₁ + s ^ 2 * a₂ - 3 * s ^ 4 := by
      unfold depressedQuarticR; rw [ha₃]; field_simp [h4, h16, h256]; ring
    change f.comp (Polynomial.X + Polynomial.C s) = g
    dsimp [f, g]
    rw [hp, hq, hr, ha₃]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    ring
  refine ⟨hcomp, ?_⟩
  rw [← hcomp, garlingDiscriminant_comp_X_add_C]

/-- Garling's prose definition of the ***cubic resolvent*** `x³ + 2px² + (p² - 4r)x - q²` for a
quartic `g = x⁴ + px² + qx + r ∈ K[x]` (§14.4, printed p. 116 / PDF p. 124). -/
noncomputable def depressedQuarticResolvent {K : Type*} [CommRing K] (p q r : K) : K[X] :=
  Polynomial.X ^ 3 + Polynomial.C (2 * p) * Polynomial.X ^ 2 +
    Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X - Polynomial.C (q ^ 2)

/-- General quartic *cubic resolvent* for an arbitrary quartic `f ∈ K[x]`: normalizes `f` by
`f.leadingCoeff⁻¹` to monic `x⁴ + a₃ x³ + a₂ x² + a₁ x + a₀`, depresses via `x ↦ x - a₃ / 4`
to `x⁴ + px² + qx + r` (§14.4, p. 115), and returns `depressedQuarticResolvent p q r` (§14.4,
p. 116; used for general quartics in `Exercise 14.7` and `Exercise 14.8(iv)`). -/
noncomputable def quarticCubicResolvent {K : Type*} [Field K] (f : K[X]) : K[X] :=
  let fm := Polynomial.C f.leadingCoeff⁻¹ * f
  let a₃ := fm.coeff 3
  let a₂ := fm.coeff 2
  let a₁ := fm.coeff 1
  let a₀ := fm.coeff 0
  depressedQuarticResolvent
    (depressedQuarticP a₃ a₂)
    (depressedQuarticQ a₃ a₂ a₁)
    (depressedQuarticR a₃ a₂ a₁ a₀)

theorem depressedQuarticResolvent_monic {K : Type*} [CommRing K] [Nontrivial K] (p q r : K) :
    (depressedQuarticResolvent p q r).Monic := by
  unfold depressedQuarticResolvent
  have heq : Polynomial.X ^ 3 + Polynomial.C (2 * p) * Polynomial.X ^ 2 +
      Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X - Polynomial.C (q ^ 2) =
      Polynomial.X ^ 3 + (Polynomial.C (2 * p) * Polynomial.X ^ 2 +
        Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X - Polynomial.C (q ^ 2)) := by ring
  rw [heq]
  refine Polynomial.monic_X_pow_add ?_
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!)

theorem depressedQuarticResolvent_natDegree {K : Type*} [CommRing K] [Nontrivial K] (p q r : K) :
    (depressedQuarticResolvent p q r).natDegree = 3 := by
  unfold depressedQuarticResolvent
  have heq : Polynomial.X ^ 3 + Polynomial.C (2 * p) * Polynomial.X ^ 2 +
      Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X - Polynomial.C (q ^ 2) =
      Polynomial.X ^ 3 + (Polynomial.C (2 * p) * Polynomial.X ^ 2 +
        Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X - Polynomial.C (q ^ 2)) := by ring
  rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 3
  · compute_degree!

theorem quarticCubicResolvent_monic {K : Type*} [Field K] (f : K[X]) :
    (quarticCubicResolvent f).Monic :=
  depressedQuarticResolvent_monic _ _ _

theorem quarticCubicResolvent_natDegree {K : Type*} [Field K] (f : K[X]) :
    (quarticCubicResolvent f).natDegree = 3 :=
  depressedQuarticResolvent_natDegree _ _ _

@[simp]
theorem quarticCubicResolvent_depressed {K : Type*} [Field K] (p q r : K) :
    quarticCubicResolvent
      (Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r) =
      depressedQuarticResolvent p q r := by
  let g : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
    Polynomial.C q * Polynomial.X + Polynomial.C r
  have hg_deg : g.natDegree = 4 := by
    dsimp [g]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  have hg_lc : g.leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hg_deg]
    dsimp [g]
    simp
  unfold quarticCubicResolvent
  change (let fm := Polynomial.C g.leadingCoeff⁻¹ * g; _) = _
  rw [hg_lc, inv_one, map_one, one_mul]
  have hc3 : g.coeff 3 = 0 := by dsimp [g]; simp
  have hc2 : g.coeff 2 = p := by dsimp [g]; simp
  have hc1 : g.coeff 1 = q := by dsimp [g]; simp
  have hc0 : g.coeff 0 = r := by dsimp [g]; simp
  simp [hc3, hc2, hc1, hc0, depressedQuarticP, depressedQuarticQ, depressedQuarticR]

/-- **§14.4 Quartic Resolvent Elements `β, γ, δ`, *Cubic Resolvent* Factorization, Discriminant
Identity, and Root Recovery** (printed pp. 116–117 / PDF pp. 124–125):
For any roots `α₀, α₁, α₂, α₃` of `x⁴ + px² + qx + r = (x - α₀)(x - α₁)(x - α₂)(x - α₃)` in a field
`E` with `(2 : E) ≠ 0`, setting `β = α₀ + α₁`, `γ = α₀ + α₂`, `δ = α₀ + α₃`:
1. `α₀ + α₁ + α₂ + α₃ = 0`, `β² = -(α₀ + α₁)(α₂ + α₃)`, `γ² = -(α₀ + α₂)(α₁ + α₃)`, and
   `δ² = -(α₀ + α₃)(α₁ + α₂)`;
2. `β² + γ² + δ² = -2p`, `β²γ² + β²δ² + γ²δ² = p² - 4r`, and `βγδ = -q`;
3. `(x - β²)(x - γ²)(x - δ²) = depressedQuarticResolvent p q r`;
4. `garlingDeltaTuple ![β², γ², δ²] = -garlingDeltaTuple ![α₀, α₁, α₂, α₃]` and
   `garlingDiscTuple ![β², γ², δ²] = garlingDiscTuple ![α₀, α₁, α₂, α₃]`;
5. `α₀ = (β + γ + δ)/2`, `α₁ = (β - γ - δ)/2`, `α₂ = (-β + γ - δ)/2`, `α₃ = (-β - γ + δ)/2`. -/
theorem section_14_4_resolvent_identities {E : Type*} [Field E] (h2 : (2 : E) ≠ 0)
    {p q r α₀ α₁ α₂ α₃ : E}
    (hfac : (Polynomial.X - Polynomial.C α₀) * (Polynomial.X - Polynomial.C α₁) *
        (Polynomial.X - Polynomial.C α₂) * (Polynomial.X - Polynomial.C α₃) =
      Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r) :
    let β : E := α₀ + α₁
    let γ : E := α₀ + α₂
    let δ : E := α₀ + α₃
    (α₀ + α₁ + α₂ + α₃ = 0 ∧
      β ^ 2 = -(α₀ + α₁) * (α₂ + α₃) ∧
      γ ^ 2 = -(α₀ + α₂) * (α₁ + α₃) ∧
      δ ^ 2 = -(α₀ + α₃) * (α₁ + α₂)) ∧
    (β ^ 2 + γ ^ 2 + δ ^ 2 = -2 * p ∧
      β ^ 2 * γ ^ 2 + β ^ 2 * δ ^ 2 + γ ^ 2 * δ ^ 2 = p ^ 2 - 4 * r ∧
      β * γ * δ = -q) ∧
    (Polynomial.X - Polynomial.C (β ^ 2)) * (Polynomial.X - Polynomial.C (γ ^ 2)) *
        (Polynomial.X - Polynomial.C (δ ^ 2)) =
      depressedQuarticResolvent p q r ∧
    (garlingDeltaTuple ![β ^ 2, γ ^ 2, δ ^ 2] = -garlingDeltaTuple ![α₀, α₁, α₂, α₃] ∧
      garlingDiscTuple ![β ^ 2, γ ^ 2, δ ^ 2] = garlingDiscTuple ![α₀, α₁, α₂, α₃]) ∧
    (α₀ = (β + γ + δ) / 2 ∧
      α₁ = (β - γ - δ) / 2 ∧
      α₂ = (-β + γ - δ) / 2 ∧
      α₃ = (-β - γ + δ) / 2) := by
  intro β γ δ
  have hexpand : (Polynomial.X - Polynomial.C α₀) * (Polynomial.X - Polynomial.C α₁) *
      (Polynomial.X - Polynomial.C α₂) * (Polynomial.X - Polynomial.C α₃) =
      Polynomial.X ^ 4 -
        Polynomial.C (α₀ + α₁ + α₂ + α₃) * Polynomial.X ^ 3 +
        Polynomial.C (α₀ * α₁ + α₀ * α₂ + α₀ * α₃ + α₁ * α₂ + α₁ * α₃ + α₂ * α₃) *
          Polynomial.X ^ 2 -
        Polynomial.C (α₀ * α₁ * α₂ + α₀ * α₁ * α₃ + α₀ * α₂ * α₃ + α₁ * α₂ * α₃) *
          Polynomial.X +
        Polynomial.C (α₀ * α₁ * α₂ * α₃) := by
    simp only [map_add, map_mul]
    ring
  rw [hexpand] at hfac
  have hs1 : α₀ + α₁ + α₂ + α₃ = 0 := by
    have h := congrArg (fun P : E[X] => P.coeff 3) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination -h
  have hs2 : α₀ * α₁ + α₀ * α₂ + α₀ * α₃ + α₁ * α₂ + α₁ * α₃ + α₂ * α₃ = p := by
    have h := congrArg (fun P : E[X] => P.coeff 2) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination h
  have hs3 : -(α₀ * α₁ * α₂ + α₀ * α₁ * α₃ + α₀ * α₂ * α₃ + α₁ * α₂ * α₃) = q := by
    have h := congrArg (fun P : E[X] => P.coeff 1) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination h
  have hs4 : α₀ * α₁ * α₂ * α₃ = r := by
    have h := congrArg (fun P : E[X] => P.coeff 0) hfac
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C] at h
    norm_num at h
    linear_combination h
  have hα0 : α₀ = -α₁ - α₂ - α₃ := by linear_combination hs1
  have hβ2_pair : β ^ 2 = -(α₀ + α₁) * (α₂ + α₃) := by dsimp [β]; rw [hα0]; ring
  have hγ2_pair : γ ^ 2 = -(α₀ + α₂) * (α₁ + α₃) := by dsimp [γ]; rw [hα0]; ring
  have hδ2_pair : δ ^ 2 = -(α₀ + α₃) * (α₁ + α₂) := by dsimp [δ]; rw [hα0]; ring
  have he1_res : β ^ 2 + γ ^ 2 + δ ^ 2 = -2 * p := by
    dsimp [β, γ, δ]; rw [← hs2, hα0]; ring
  have he2_res : β ^ 2 * γ ^ 2 + β ^ 2 * δ ^ 2 + γ ^ 2 * δ ^ 2 = p ^ 2 - 4 * r := by
    dsimp [β, γ, δ]; rw [← hs2, ← hs4, hα0]; ring
  have he3_res : β * γ * δ = -q := by
    dsimp [β, γ, δ]; rw [← hs3, hα0]; ring
  have hprod_sq : β ^ 2 * γ ^ 2 * δ ^ 2 = q ^ 2 := by
    calc β ^ 2 * γ ^ 2 * δ ^ 2 = (β * γ * δ) ^ 2 := by ring
      _ = (-q) ^ 2 := by rw [he3_res]
      _ = q ^ 2 := by ring
  have hres_poly : (Polynomial.X - Polynomial.C (β ^ 2)) *
      (Polynomial.X - Polynomial.C (γ ^ 2)) * (Polynomial.X - Polynomial.C (δ ^ 2)) =
      depressedQuarticResolvent p q r := by
    unfold depressedQuarticResolvent
    have hc : (Polynomial.X - Polynomial.C (β ^ 2)) *
        (Polynomial.X - Polynomial.C (γ ^ 2)) * (Polynomial.X - Polynomial.C (δ ^ 2)) =
        Polynomial.X ^ 3 - Polynomial.C (β ^ 2 + γ ^ 2 + δ ^ 2) * Polynomial.X ^ 2 +
          Polynomial.C (β ^ 2 * γ ^ 2 + β ^ 2 * δ ^ 2 + γ ^ 2 * δ ^ 2) * Polynomial.X -
          Polynomial.C (β ^ 2 * γ ^ 2 * δ ^ 2) := by
      simp only [map_add, map_mul]
      ring
    rw [hc, he1_res, he2_res, hprod_sq]
    simp only [map_neg, map_mul, map_ofNat]
    ring
  have hdelta_eq : garlingDeltaTuple ![β ^ 2, γ ^ 2, δ ^ 2] =
      -garlingDeltaTuple ![α₀, α₁, α₂, α₃] := by
    rw [garlingDeltaTuple_three, garlingDeltaTuple_four]
    have u0 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → E) 0 = β ^ 2 := rfl
    have u1 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → E) 1 = γ ^ 2 := rfl
    have u2 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → E) 2 = δ ^ 2 := rfl
    have v0 : (![α₀, α₁, α₂, α₃] : Fin 4 → E) 0 = α₀ := rfl
    have v1 : (![α₀, α₁, α₂, α₃] : Fin 4 → E) 1 = α₁ := rfl
    have v2 : (![α₀, α₁, α₂, α₃] : Fin 4 → E) 2 = α₂ := rfl
    have v3 : (![α₀, α₁, α₂, α₃] : Fin 4 → E) 3 = α₃ := rfl
    rw [u0, u1, u2, v0, v1, v2, v3]
    dsimp [β, γ, δ]
    rw [hα0]
    ring
  have hdisc_eq : garlingDiscTuple ![β ^ 2, γ ^ 2, δ ^ 2] =
      garlingDiscTuple ![α₀, α₁, α₂, α₃] := by
    unfold garlingDiscTuple
    rw [hdelta_eq, neg_sq]
  have hr0 : α₀ = (β + γ + δ) / 2 := by
    apply mul_left_cancel₀ h2; rw [mul_div_cancel₀ _ h2]; dsimp [β, γ, δ]; rw [hα0]; ring
  have hr1 : α₁ = (β - γ - δ) / 2 := by
    apply mul_left_cancel₀ h2; rw [mul_div_cancel₀ _ h2]; dsimp [β, γ, δ]; rw [hα0]; ring
  have hr2 : α₂ = (-β + γ - δ) / 2 := by
    apply mul_left_cancel₀ h2; rw [mul_div_cancel₀ _ h2]; dsimp [β, γ, δ]; rw [hα0]; ring
  have hr3 : α₃ = (-β - γ + δ) / 2 := by
    apply mul_left_cancel₀ h2; rw [mul_div_cancel₀ _ h2]; dsimp [β, γ, δ]; rw [hα0]; ring
  exact ⟨⟨hs1, hβ2_pair, hγ2_pair, hδ2_pair⟩, ⟨he1_res, he2_res, he3_res⟩,
    hres_poly, ⟨hdelta_eq, hdisc_eq⟩, ⟨hr0, hr1, hr2, hr3⟩⟩

/-- **Discriminant Preservation for the Cubic Resolvent:**
Over any field `K` with `char K ≠ 2`, every quartic `f ∈ K[x]` (`f.natDegree = 4`) has the exact
same Garling discriminant as its cubic resolvent `quarticCubicResolvent f`! -/
theorem garlingDiscriminant_quarticCubicResolvent {K : Type u} [Field K]
    (hchar2 : ringChar K ≠ 2) {f : K[X]} (hdeg : f.natDegree = 4) :
    garlingDiscriminant (quarticCubicResolvent f) = garlingDiscriminant f := by
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have hf0 : f ≠ 0 := by intro h0; rw [h0] at hdeg; simp at hdeg
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  let fm : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hf_eq : f = Polynomial.C f.leadingCoeff * fm := by
    dsimp [fm]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc, map_one, one_mul]
  have hfm_mon : fm.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc]
  have hfm_deg : fm.natDegree = 4 := by
    dsimp [fm]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc), hdeg]
  let a₃ : K := fm.coeff 3
  let a₂ : K := fm.coeff 2
  let a₁ : K := fm.coeff 1
  let a₀ : K := fm.coeff 0
  have hfm_expand : fm = Polynomial.X ^ 4 + Polynomial.C a₃ * Polynomial.X ^ 3 +
      Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀ := by
    rw [fm.as_sum_range' 5 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have hc4 : fm.coeff 4 = 1 := by
      rw [← hfm_deg, ← Polynomial.leadingCoeff, hfm_mon.leadingCoeff]
    simp only [hc4, a₃, a₂, a₁, a₀, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
      map_one, one_mul, mul_one]
    ring
  let p : K := depressedQuarticP a₃ a₂
  let q : K := depressedQuarticQ a₃ a₂ a₁
  let r : K := depressedQuarticR a₃ a₂ a₁ a₀
  let g : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
    Polynomial.C q * Polynomial.X + Polynomial.C r
  have hres_def : quarticCubicResolvent f = depressedQuarticResolvent p q r := rfl
  have hdisc_f_eq_g : garlingDiscriminant f = garlingDiscriminant g := by
    rw [hf_eq, garlingDiscriminant_C_mul hlc, hfm_expand]
    exact (section_14_4_depress_quartic hchar2 a₃ a₂ a₁ a₀).2
  rw [hres_def, hdisc_f_eq_g]
  -- Compare discriminants of `depressedQuarticResolvent p q r` and `g` inside `SplittingField g`:
  let L : Type u := Polynomial.SplittingField g
  let _ : Field L := Polynomial.SplittingField.instField g
  let _ : Algebra K L := Polynomial.SplittingField.instAlgebra g
  have hg_mon : g.Monic := by
    dsimp [g]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq]
    refine Polynomial.monic_X_pow_add ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
  have hg_deg : g.natDegree = 4 := by
    dsimp [g]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  obtain ⟨m, c, α, hexp⟩ :=
    (garlingSplitsOver_iff_splits K L g).mpr (Polynomial.SplittingField.splits g)
  have hc1 : c = 1 := (garlingSplitsExplicit_props hg_mon.ne_zero hexp).1.trans hg_mon.leadingCoeff
  have hm4 : m = 4 := ((garlingSplitsExplicit_props hg_mon.ne_zero hexp).2.2.1).trans hg_deg
  subst hm4 hc1
  have hfacL : (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) *
      (Polynomial.X - Polynomial.C (α 2)) * (Polynomial.X - Polynomial.C (α 3)) =
      Polynomial.X ^ 4 + Polynomial.C (algebraMap K L p) * Polynomial.X ^ 2 +
        Polynomial.C (algebraMap K L q) * Polynomial.X +
        Polynomial.C (algebraMap K L r) := by
    have heq := hexp.symm
    rw [Fin.prod_univ_four] at heq
    simp only [g, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, map_one, one_mul, mul_assoc] at heq ⊢
    exact heq
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]; exact (map_ne_zero (algebraMap K L)).mpr h2K
  have hid := section_14_4_resolvent_identities h2L hfacL
  let β : L := α 0 + α 1
  let γ : L := α 0 + α 2
  let δ : L := α 0 + α 3
  have hexp_res : GarlingSplitsExplicit K L (depressedQuarticResolvent p q r) 3 1
      ![β ^ 2, γ ^ 2, δ ^ 2] := by
    unfold GarlingSplitsExplicit
    rw [Fin.prod_univ_three]
    have u0 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → L) 0 = β ^ 2 := rfl
    have u1 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → L) 1 = γ ^ 2 := rfl
    have u2 : (![β ^ 2, γ ^ 2, δ ^ 2] : Fin 3 → L) 2 = δ ^ 2 := rfl
    rw [u0, u1, u2]
    have hmap_res : (depressedQuarticResolvent p q r).map (algebraMap K L) =
        depressedQuarticResolvent (algebraMap K L p) (algebraMap K L q) (algebraMap K L r) := by
      unfold depressedQuarticResolvent
      simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_ofNat]
    rw [hmap_res, map_one, map_one, one_mul]
    simpa only [mul_assoc] using hid.2.2.1.symm
  have hα_eta : ![α 0, α 1, α 2, α 3] = α := by
    ext i; fin_cases i <;> rfl
  apply (algebraMap K L).injective
  rw [garlingDiscriminant_eq_discTuple (depressedQuarticResolvent_monic p q r).ne_zero hexp_res,
    garlingDiscriminant_eq_discTuple hg_mon.ne_zero hexp, hid.2.2.2.1.2, hα_eta]

/-- Auxiliary solver for `g = X^4 + C p * X^2 + C q * X + C r` inside an opaque ambient extension
`N : Type u` over `K` in which both `g` and `X^3 - 1` split. -/
private theorem depressed_quartic_solvable_in_ambient {K N : Type u} [Field K] [Field N]
    [Algebra K N] (hchar3 : ringChar K ≠ 3) (h2K : (2 : K) ≠ 0) (h3K : (3 : K) ≠ 0) (p q r : K)
    (hsp_g : ((Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r : K[X]).map (algebraMap K N)).Splits)
    (hsp_c3 : ((Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N)).Splits) :
    IsGarlingSolvableByRadicals
      (Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r : K[X]) := by
  let g : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
    Polynomial.C q * Polynomial.X + Polynomial.C r
  have hg_mon : g.Monic := by
    dsimp [g]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq]
    refine Polynomial.monic_X_pow_add ?_
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
  have hg_deg : g.natDegree = 4 := by
    dsimp [g]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  obtain ⟨m, c, α, hexpN⟩ := (garlingSplitsOver_iff_splits K N g).mpr hsp_g
  have hc1 : c = 1 := (garlingSplitsExplicit_props hg_mon.ne_zero hexpN).1.trans hg_mon.leadingCoeff
  have hm4 : m = 4 := ((garlingSplitsExplicit_props hg_mon.ne_zero hexpN).2.2.1).trans hg_deg
  subst hm4 hc1
  have hfacN : (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) *
      (Polynomial.X - Polynomial.C (α 2)) * (Polynomial.X - Polynomial.C (α 3)) =
      Polynomial.X ^ 4 + Polynomial.C (algebraMap K N p) * Polynomial.X ^ 2 +
        Polynomial.C (algebraMap K N q) * Polynomial.X +
        Polynomial.C (algebraMap K N r) := by
    have heq := hexpN.symm
    rw [Fin.prod_univ_four] at heq
    simp only [g, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, map_one, one_mul, mul_assoc] at heq ⊢
    exact heq
  have h2N : (2 : N) ≠ 0 := by
    rw [← map_ofNat (algebraMap K N) 2]; exact (map_ne_zero (algebraMap K N)).mpr h2K
  have h3N : (3 : N) ≠ 0 := by
    rw [← map_ofNat (algebraMap K N) 3]; exact (map_ne_zero (algebraMap K N)).mpr h3K
  -- Extract `ω ∈ N` with `ω^2 + ω + 1 = 0`:
  have hc3_mon : (Polynomial.X ^ 3 - 1 : K[X]).Monic := by
    have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.monic_X_pow_sub_C 1 (by decide)
  have hc3_deg : (Polynomial.X ^ 3 - 1 : K[X]).natDegree = 3 := by
    have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
    rw [this]; exact Polynomial.natDegree_X_pow_sub_C
  obtain ⟨m_c, c_c, ρ_c, hexp_c⟩ :=
    (garlingSplitsOver_iff_splits K N (Polynomial.X ^ 3 - 1)).mpr hsp_c3
  have hm_c3 : m_c = 3 :=
    ((garlingSplitsExplicit_props hc3_mon.ne_zero hexp_c).2.2.1).trans hc3_deg
  subst hm_c3
  have hdisc_c3 : garlingDiscriminant (Polynomial.X ^ 3 - 1 : K[X]) ≠ 0 := by
    have heq : (Polynomial.X ^ 3 - 1 : K[X]) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1) := by
      simp [sub_eq_add_neg]
    rw [heq, garlingDiscriminant_depressed_cubic]
    have h27K : (27 : K) ≠ 0 := by
      have : (27 : K) = 3 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h3K
    intro h0; apply h27K; linear_combination -h0
  have hinj_ρc : Function.Injective ρ_c := by
    by_contra hninj
    have hd0 : garlingDeltaTuple ρ_c = 0 := (garlingDeltaTuple_eq_zero_iff ρ_c).mpr hninj
    have hdisc0 : algebraMap K N (garlingDiscriminant (Polynomial.X ^ 3 - 1 : K[X])) = 0 := by
      rw [garlingDiscriminant_eq_discTuple hc3_mon.ne_zero hexp_c, garlingDiscTuple, hd0,
        zero_pow (by decide)]
    exact hdisc_c3 ((map_eq_zero_iff (algebraMap K N) (algebraMap K N).injective).mp hdisc0)
  have hρc_cube : ∀ i : Fin 3, (ρ_c i) ^ 3 - 1 = 0 := by
    intro i
    have hev : ((Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N)).eval (ρ_c i) = 0 := by
      rw [hexp_c, Polynomial.eval_mul, Polynomial.eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    simpa using hev
  have hex_ω : ∃ ω : N, ω ^ 2 + ω + 1 = 0 := by
    by_cases h0 : ρ_c 0 = 1
    · have h1_ne : ρ_c 1 ≠ 1 := fun h1 =>
        absurd (hinj_ρc (h1.trans h0.symm)) (by decide)
      refine ⟨ρ_c 1, ?_⟩
      have hmul : (ρ_c 1 - 1) * ((ρ_c 1) ^ 2 + ρ_c 1 + 1) = 0 := by linear_combination hρc_cube 1
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1_ne)
    · refine ⟨ρ_c 0, ?_⟩
      have hmul : (ρ_c 0 - 1) * ((ρ_c 0) ^ 2 + ρ_c 0 + 1) = 0 := by linear_combination hρc_cube 0
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h0)
  obtain ⟨ω, hω⟩ := hex_ω
  have hω_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  -- Quartic resolvent elements `β, γ, δ` and depressed cubic resolvent roots `u₀, u₁, u₂`:
  have hid4 := section_14_4_resolvent_identities h2N hfacN
  let β : N := α 0 + α 1
  let γ : N := α 0 + α 2
  let δ : N := α 0 + α 3
  let P_c : K := depressedCubicP (2 * p) (p ^ 2 - 4 * r)
  let Q_c : K := depressedCubicQ (2 * p) (p ^ 2 - 4 * r) (-(q ^ 2))
  let s_c : K := -(2 * p) / 3
  let u₀ : N := β ^ 2 - algebraMap K N s_c
  let u₁ : N := γ ^ 2 - algebraMap K N s_c
  let u₂ : N := δ ^ 2 - algebraMap K N s_c
  have hfac_u : (Polynomial.X - Polynomial.C u₀) * (Polynomial.X - Polynomial.C u₁) *
      (Polynomial.X - Polynomial.C u₂) =
      Polynomial.X ^ 3 + Polynomial.C (algebraMap K N P_c) * Polynomial.X +
        Polynomial.C (algebraMap K N Q_c) := by
    have hdep_c := (section_14_3_depress_cubic hchar3 (2 * p) (p ^ 2 - 4 * r) (-(q ^ 2))).1
    have hmap_dep := congrArg (Polynomial.map (algebraMap K N)) hdep_c
    rw [Polynomial.map_comp] at hmap_dep
    have hshift_map : (Polynomial.X + Polynomial.C (-(2 * p) / 3) : K[X]).map (algebraMap K N) =
        Polynomial.X + Polynomial.C (algebraMap K N (-2 * p / 3)) := by
      have hneg2 : -(2 * p) / 3 = -2 * p / 3 := by ring
      rw [hneg2, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    rw [hshift_map] at hmap_dep
    have hres_eq : (Polynomial.X ^ 3 + Polynomial.C (2 * p) * Polynomial.X ^ 2 +
        Polynomial.C (p ^ 2 - 4 * r) * Polynomial.X + Polynomial.C (-(q ^ 2)) : K[X]).map
        (algebraMap K N) =
        (Polynomial.X - Polynomial.C (β ^ 2)) * (Polynomial.X - Polynomial.C (γ ^ 2)) *
          (Polynomial.X - Polynomial.C (δ ^ 2)) := by
      rw [hid4.2.2.1]
      unfold depressedQuarticResolvent
      simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_ofNat, sub_eq_add_neg]
    rw [hres_eq] at hmap_dep
    simp only [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp] at hmap_dep
    have hs0 : Polynomial.X + Polynomial.C (algebraMap K N (-2 * p / 3)) - Polynomial.C (β ^ 2) =
        Polynomial.X - Polynomial.C u₀ := by
      dsimp [u₀, s_c]; simp only [map_sub, map_neg, map_div₀, map_mul, map_ofNat]; ring
    have hs1 : Polynomial.X + Polynomial.C (algebraMap K N (-2 * p / 3)) - Polynomial.C (γ ^ 2) =
        Polynomial.X - Polynomial.C u₁ := by
      dsimp [u₁, s_c]; simp only [map_sub, map_neg, map_div₀, map_mul, map_ofNat]; ring
    have hs2 : Polynomial.X + Polynomial.C (algebraMap K N (-2 * p / 3)) - Polynomial.C (δ ^ 2) =
        Polynomial.X - Polynomial.C u₂ := by
      dsimp [u₂, s_c]; simp only [map_sub, map_neg, map_div₀, map_mul, map_ofNat]; ring
    rw [hs0, hs1, hs2] at hmap_dep
    simpa only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C] using hmap_dep
  have hres3 := section_14_3_resolvent_identities h2N h3N hfac_u hω
  let δ_c : N := (u₁ - u₀) * (u₂ - u₀) * (u₂ - u₁)
  let β_c : N := u₀ + ω * u₁ + ω ^ 2 * u₂
  let γ_c : N := u₀ + ω ^ 2 * u₁ + ω * u₂
  have hδc_sq_K : δ_c ^ 2 = algebraMap K N (-4 * P_c ^ 3 - 27 * Q_c ^ 2) := by
    have h1 : δ_c ^ 2 = -4 * (algebraMap K N P_c) ^ 3 - 27 * (algebraMap K N Q_c) ^ 2 := by
      have hw := hres3.2.1
      have hw3 := hres3.1
      change ((2 * ω + 1) * δ_c) ^ 2 = _ at hw
      rw [mul_pow, hw3] at hw
      apply mul_left_cancel₀ (neg_ne_zero.mpr h3N)
      exact hw
    rw [h1]
    simp only [map_sub, map_neg, map_mul, map_pow, map_ofNat]
  -- 7-step radical generator tuple `![δ_c, ω, β_c, γ_c, β, γ, δ]` with exponents `![2, 3, 3, 3, 2, 2, 2]`:
  let rad_tup : Fin 7 → N := ![δ_c, ω, β_c, γ_c, β, γ, δ]
  let exp_tup : Fin 7 → ℕ := ![2, 3, 3, 3, 2, 2, 2]
  let E : IntermediateField K N := IntermediateField.adjoin K (Set.range rad_tup)
  -- Helper: `β^2, γ^2, δ^2 ∈ garlingRadPrefix K rad_tup 4`
  have hsquares_F4 :
      β ^ 2 ∈ garlingRadPrefix K rad_tup 4 ∧
      γ ^ 2 ∈ garlingRadPrefix K rad_tup 4 ∧
      δ ^ 2 ∈ garlingRadPrefix K rad_tup 4 := by
    let F4 := garlingRadPrefix K rad_tup 4
    have hω_F4 : ω ∈ F4 := garlingRadPrefix_mem_of_lt K rad_tup (k := 1) (j := 4) (by decide)
    have hβc_F4 : β_c ∈ F4 := garlingRadPrefix_mem_of_lt K rad_tup (k := 2) (j := 4) (by decide)
    have hγc_F4 : γ_c ∈ F4 := garlingRadPrefix_mem_of_lt K rad_tup (k := 3) (j := 4) (by decide)
    have h3_F4 : (3 : N) ∈ F4 := by
      have : (3 : N) = algebraMap K N 3 := by simp only [map_ofNat]
      rw [this]; exact F4.algebraMap_mem 3
    have hs_F4 : algebraMap K N s_c ∈ F4 := F4.algebraMap_mem s_c
    have hu0_F4 : u₀ ∈ F4 := by
      rw [hres3.2.2.2.2.2.2.2.2.1]
      exact F4.div_mem (F4.add_mem hβc_F4 hγc_F4) h3_F4
    have hu1_F4 : u₁ ∈ F4 := by
      rw [hres3.2.2.2.2.2.2.2.2.2.1]
      exact F4.div_mem
        (F4.add_mem (F4.mul_mem (pow_mem hω_F4 2) hβc_F4) (F4.mul_mem hω_F4 hγc_F4)) h3_F4
    have hu2_F4 : u₂ ∈ F4 := by
      rw [hres3.2.2.2.2.2.2.2.2.2.2]
      exact F4.div_mem
        (F4.add_mem (F4.mul_mem hω_F4 hβc_F4) (F4.mul_mem (pow_mem hω_F4 2) hγc_F4)) h3_F4
    have hb2 : β ^ 2 = u₀ + algebraMap K N s_c := by dsimp [u₀]; ring
    have hg2 : γ ^ 2 = u₁ + algebraMap K N s_c := by dsimp [u₁]; ring
    have hd2 : δ ^ 2 = u₂ + algebraMap K N s_c := by dsimp [u₂]; ring
    exact ⟨hb2 ▸ F4.add_mem hu0_F4 hs_F4,
      hg2 ▸ F4.add_mem hu1_F4 hs_F4,
      hd2 ▸ F4.add_mem hu2_F4 hs_F4⟩
  have hrad_KE : IsGarlingExtensionByRadicals K E := by
    refine isGarlingExtensionByRadicals_adjoin_tuple rad_tup exp_tup
      (fun i => by fin_cases i <;> decide) (fun i => ?_)
    fin_cases i
    · change δ_c ^ 2 ∈ garlingRadPrefix K rad_tup 0
      rw [garlingRadPrefix_zero, hδc_sq_K]
      exact (⊥ : IntermediateField K N).algebraMap_mem _
    · change ω ^ 3 ∈ garlingRadPrefix K rad_tup 1
      rw [hω_cube]
      exact (garlingRadPrefix K rad_tup 1).one_mem
    · change β_c ^ 3 ∈ garlingRadPrefix K rad_tup 2
      rw [hres3.2.2.2.2.2.2.1]
      let F2 := garlingRadPrefix K rad_tup 2
      have hδ_F2 : δ_c ∈ F2 := garlingRadPrefix_mem_of_lt K rad_tup (k := 0) (j := 2) (by decide)
      have hω_F2 : ω ∈ F2 := garlingRadPrefix_mem_of_lt K rad_tup (k := 1) (j := 2) (by decide)
      have hq_F2 : algebraMap K N Q_c ∈ F2 := F2.algebraMap_mem Q_c
      have hc1_F2 : -(27 / 2 : N) ∈ F2 := by
        have : -(27 / 2 : N) = algebraMap K N (-(27 / 2 : K)) := by
          simp only [map_neg, map_div₀, map_ofNat]
        rw [this]; exact F2.algebraMap_mem _
      have hc2_F2 : (3 / 2 : N) ∈ F2 := by
        have : (3 / 2 : N) = algebraMap K N (3 / 2 : K) := by
          simp only [map_div₀, map_ofNat]
        rw [this]; exact F2.algebraMap_mem _
      have h2_F2 : (2 : N) ∈ F2 := by
        have : (2 : N) = algebraMap K N 2 := by simp only [map_ofNat]
        rw [this]; exact F2.algebraMap_mem 2
      exact F2.sub_mem (F2.mul_mem hc1_F2 hq_F2)
        (F2.mul_mem (F2.mul_mem hc2_F2 (F2.add_mem (F2.mul_mem h2_F2 hω_F2) F2.one_mem)) hδ_F2)
    · change γ_c ^ 3 ∈ garlingRadPrefix K rad_tup 3
      rw [hres3.2.2.2.2.2.2.2.1]
      let F3 := garlingRadPrefix K rad_tup 3
      have hδ_F3 : δ_c ∈ F3 := garlingRadPrefix_mem_of_lt K rad_tup (k := 0) (j := 3) (by decide)
      have hω_F3 : ω ∈ F3 := garlingRadPrefix_mem_of_lt K rad_tup (k := 1) (j := 3) (by decide)
      have hq_F3 : algebraMap K N Q_c ∈ F3 := F3.algebraMap_mem Q_c
      have hc1_F3 : -(27 / 2 : N) ∈ F3 := by
        have : -(27 / 2 : N) = algebraMap K N (-(27 / 2 : K)) := by
          simp only [map_neg, map_div₀, map_ofNat]
        rw [this]; exact F3.algebraMap_mem _
      have hc2_F3 : (3 / 2 : N) ∈ F3 := by
        have : (3 / 2 : N) = algebraMap K N (3 / 2 : K) := by
          simp only [map_div₀, map_ofNat]
        rw [this]; exact F3.algebraMap_mem _
      have h2_F3 : (2 : N) ∈ F3 := by
        have : (2 : N) = algebraMap K N 2 := by simp only [map_ofNat]
        rw [this]; exact F3.algebraMap_mem 2
      exact F3.add_mem (F3.mul_mem hc1_F3 hq_F3)
        (F3.mul_mem (F3.mul_mem hc2_F3 (F3.add_mem (F3.mul_mem h2_F3 hω_F3) F3.one_mem)) hδ_F3)
    · change β ^ 2 ∈ garlingRadPrefix K rad_tup 4
      exact hsquares_F4.1
    · change γ ^ 2 ∈ garlingRadPrefix K rad_tup 5
      exact garlingRadPrefix_mono K rad_tup (by decide : (4 : Fin 8) ≤ 5) hsquares_F4.2.1
    · change δ ^ 2 ∈ garlingRadPrefix K rad_tup 6
      exact garlingRadPrefix_mono K rad_tup (by decide : (4 : Fin 8) ≤ 6) hsquares_F4.2.2
  -- Show `α 0, α 1, α 2, α 3 ∈ E`:
  have hβ_E : β ∈ E := IntermediateField.subset_adjoin K _ ⟨4, rfl⟩
  have hγ_E : γ ∈ E := IntermediateField.subset_adjoin K _ ⟨5, rfl⟩
  have hδ_E : δ ∈ E := IntermediateField.subset_adjoin K _ ⟨6, rfl⟩
  have h2_E : (2 : N) ∈ E := by
    have : (2 : N) = algebraMap K N 2 := by simp only [map_ofNat]
    rw [this]; exact E.algebraMap_mem 2
  have hα_mem : ∀ i : Fin 4, α i ∈ E := by
    intro i; fin_cases i
    · change α 0 ∈ E
      rw [hid4.2.2.2.2.1]
      exact E.div_mem (E.add_mem (E.add_mem hβ_E hγ_E) hδ_E) h2_E
    · change α 1 ∈ E
      rw [hid4.2.2.2.2.2.1]
      exact E.div_mem (E.sub_mem (E.sub_mem hβ_E hγ_E) hδ_E) h2_E
    · change α 2 ∈ E
      rw [hid4.2.2.2.2.2.2.1]
      exact E.div_mem (E.sub_mem (E.add_mem (E.neg_mem hβ_E) hγ_E) hδ_E) h2_E
    · change α 3 ∈ E
      rw [hid4.2.2.2.2.2.2.2]
      exact E.div_mem (E.add_mem (E.sub_mem (E.neg_mem hβ_E) hγ_E) hδ_E) h2_E
  exact ⟨E, inferInstance, inferInstance, hrad_KE,
    ⟨4, 1, _, garlingSplitsExplicit_of_mem_intermediateField E hexpN hα_mem⟩⟩

/-- **§14.4 Main-Text Solvability of Quartics by Radicals** (printed pp. 115–117 / PDF pp. 123–125):
Over **every** field `K` with `char K ≠ 2` and `char K ≠ 3`, **every** non-zero polynomial
`f ∈ K[x]` of degree `≤ 4` (in particular every quartic polynomial of degree `4`, reducible or
irreducible, monic or non-monic) is solvable by radicals (`IsGarlingSolvableByRadicals f`), by
extracting square roots and cube roots via the *cubic resolvent*. -/
theorem quartic_solvable_by_radicals {K : Type u} [Field K]
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {f : K[X]} (hf0 : f ≠ 0) (hdeg : f.natDegree ≤ 4) :
    IsGarlingSolvableByRadicals f := by
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h3K : (3 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_three hchar3
  by_cases hle3 : f.natDegree ≤ 3
  · exact cubic_solvable_by_radicals hchar2 hchar3 hf0 hle3
  · have hdeg4 : f.natDegree = 4 := by omega
    have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    let fm : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
    have hf_eq : f = Polynomial.C f.leadingCoeff * fm := by
      dsimp [fm]
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne, map_one, one_mul]
    rw [hf_eq, isGarlingSolvableByRadicals_C_mul_iff hlc_ne]
    have hfm_mon : fm.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hlc_ne]
    have hfm_deg : fm.natDegree = 4 := by
      dsimp [fm]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_ne), hdeg4]
    let a₃ : K := fm.coeff 3
    let a₂ : K := fm.coeff 2
    let a₁ : K := fm.coeff 1
    let a₀ : K := fm.coeff 0
    have hfm_expand : fm = Polynomial.X ^ 4 + Polynomial.C a₃ * Polynomial.X ^ 3 +
        Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀ := by
      rw [fm.as_sum_range' 5 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      have hc4 : fm.coeff 4 = 1 := by
        rw [← hfm_deg, ← Polynomial.leadingCoeff, hfm_mon.leadingCoeff]
      simp only [hc4, a₃, a₂, a₁, a₀, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
        map_one, one_mul, mul_one]
      ring
    rw [hfm_expand]
    let p : K := depressedQuarticP a₃ a₂
    let q : K := depressedQuarticQ a₃ a₂ a₁
    let r : K := depressedQuarticR a₃ a₂ a₁ a₀
    let g : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
      Polynomial.C q * Polynomial.X + Polynomial.C r
    have hdep := (section_14_4_depress_quartic hchar2 a₃ a₂ a₁ a₀).1
    rw [← isGarlingSolvableByRadicals_comp_X_add_C_iff _ (-a₃ / 4), hdep]
    have hg_mon : g.Monic := by
      dsimp [g]
      have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r =
          Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
            Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
      rw [heq]
      refine Polynomial.monic_X_pow_add ?_
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree!; omega)
    have hc3_mon : (Polynomial.X ^ 3 - 1 : K[X]).Monic := by
      have : (Polynomial.X ^ 3 - 1 : K[X]) = Polynomial.X ^ 3 - Polynomial.C 1 := by simp
      rw [this]; exact Polynomial.monic_X_pow_sub_C 1 (by decide)
    let P : K[X] := g * (Polynomial.X ^ 3 - 1)
    let N : Type u := Polynomial.SplittingField P
    let _ : Field N := Polynomial.SplittingField.instField P
    let _ : Algebra K N := Polynomial.SplittingField.instAlgebra P
    have hsp_P : (P.map (algebraMap K N)).Splits := Polynomial.SplittingField.splits P
    rw [Polynomial.map_mul] at hsp_P
    have hg_map_ne0 : g.map (algebraMap K N) ≠ 0 := (hg_mon.map (algebraMap K N)).ne_zero
    have hc3_map_ne0 : (Polynomial.X ^ 3 - 1 : K[X]).map (algebraMap K N) ≠ 0 :=
      (hc3_mon.map (algebraMap K N)).ne_zero
    obtain ⟨hsp_g, hsp_c3⟩ := (Polynomial.splits_mul hg_map_ne0 hc3_map_ne0).mp hsp_P
    exact depressed_quartic_solvable_in_ambient (N := N) hchar3 h2K h3K p q r hsp_g hsp_c3

/-! ### Viergruppe Fixed Field `M = K(β², γ², δ²)` as Splitting Subfield of the Cubic Resolvent -/

/-- Combinatorial pair-sum product `-(α_a + α_b)(α_c + α_d)` realizing `β², γ², δ²`. -/
def quarticPairProd {R : Type*} [CommRing R] (i : Fin 3) (α : Fin 4 → R) : R :=
  let q := quarticPairIdx i;
  -(α q.1 + α q.2.1) * (α q.2.2.1 + α q.2.2.2)

theorem quarticPairProd_comp_perm {R : Type*} [CommRing R] (i : Fin 3)
    (α : Fin 4 → R) (π : SigmaN 4) :
    quarticPairProd i (α ∘ π) = quarticPairProd (s4ToS3Hom π i) α := by
  unfold quarticPairProd
  change (let q := quarticPairIdx i; -(α (π q.1) + α (π q.2.1)) * (α (π q.2.2.1) + α (π q.2.2.2))) =
    (let q' := quarticPairIdx (s4ToS3Hom π i); -(α q'.1 + α q'.2.1) * (α q'.2.2.1 + α q'.2.2.2))
  have hcases := quarticPairIdx_perm_cases π i
  dsimp only at hcases ⊢
  rcases hcases with
    ⟨⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩⟩ |
    ⟨⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩⟩ <;>
    rw [h1, h2, h3, h4]
  all_goals ring

theorem quarticPairProd_vals {R : Type*} [CommRing R] (α : Fin 4 → R) :
    quarticPairProd 0 α = -(α 0 + α 1) * (α 2 + α 3) ∧
    quarticPairProd 1 α = -(α 0 + α 2) * (α 1 + α 3) ∧
    quarticPairProd 2 α = -(α 0 + α 3) * (α 1 + α 2) :=
  ⟨rfl, rfl, rfl⟩

/-- **§14.4 Main-Text Galois Subfield Theorem for the Cubic Resolvent**
(printed p. 116 / PDF p. 124):
For any separable quartic `f ∈ K[x]` (`f.natDegree = 4`, `char K ≠ 2`), splitting field extension
`L : K` of `f`, and root labelling `e : Fin 4 ≃ garlingRootSet K L f`, let
`M₀ := IntermediateField.fixedField (viergruppe.comap (garlingRootLabellingPermHom e))` and
`g := quarticCubicResolvent f`. Then:
1. `IsGarlingSplittingFieldExtension K M₀ g`, and **every** intermediate field
   `M : IntermediateField K L` satisfying `IsGarlingSplittingFieldExtension K M g` equals `M₀`
   (in particular `M₀` is independent of the root labelling `e`);
2. Setting `G := (garlingRootLabellingPermHom e).range ≤ Σ₄`, we have
   `Module.finrank M₀ L = Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4))` and
   `Module.finrank K M₀ * Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = Nat.card G`! -/
theorem section_14_4_resolvent_splitting_subfield {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (hchar2 : ringChar K ≠ 2)
    {f : K[X]} (hdeg : f.natDegree = 4) (hsep : f.Separable)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (e : Fin 4 ≃ garlingRootSet K L f) :
    let φ := garlingRootLabellingPermHom e
    let H := viergruppe.comap φ
    let M₀ : IntermediateField K L := IntermediateField.fixedField H
    let g := quarticCubicResolvent f
    let G := φ.range
    IsGarlingSplittingFieldExtension K M₀ g ∧
    (∀ M : IntermediateField K L, IsGarlingSplittingFieldExtension K M g → M = M₀) ∧
    Module.finrank M₀ L = Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) ∧
    Module.finrank K M₀ * Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = Nat.card G ∧
    Function.Injective φ := by
  intro φ H M₀ g G
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]; exact (map_ne_zero (algebraMap K L)).mpr h2K
  have hf0 : f ≠ 0 := hsep.ne_zero
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hgar_sep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep).2.2
  have ⟨hfin, hnorm⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨f, hsf⟩
  have hsepL : IsGarlingSeparableExtension K L :=
    (isGarlingSeparableExtension_iff_poly_of_splittingField hf0 hsf).mpr hgar_sep
  have hgal : IsGarlingGaloisExtension K L := ⟨hfin, hnorm, hsepL⟩
  have _ : IsGalois K L := ((isGarlingGaloisExtension_iff K L).mp hgal).2
  have _ : FiniteDimensional K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
  -- Express `f` via monic `fm` and depressed `g_dep = X^4 + p X^2 + q X + r`:
  let fm : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hf_eq : f = Polynomial.C f.leadingCoeff * fm := by
    dsimp [fm]; rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc, map_one, one_mul]
  have hfm_mon : fm.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc]
  have hfm_deg : fm.natDegree = 4 := by
    dsimp [fm]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc), hdeg]
  let a₃ : K := fm.coeff 3
  let a₂ : K := fm.coeff 2
  let a₁ : K := fm.coeff 1
  let a₀ : K := fm.coeff 0
  have hfm_expand : fm = Polynomial.X ^ 4 + Polynomial.C a₃ * Polynomial.X ^ 3 +
      Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀ := by
    rw [fm.as_sum_range' 5 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have hc4 : fm.coeff 4 = 1 := by
      rw [← hfm_deg, ← Polynomial.leadingCoeff, hfm_mon.leadingCoeff]
    simp only [hc4, a₃, a₂, a₁, a₀, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
      map_one, one_mul, mul_one]
    ring
  let p : K := depressedQuarticP a₃ a₂
  let q : K := depressedQuarticQ a₃ a₂ a₁
  let r : K := depressedQuarticR a₃ a₂ a₁ a₀
  let g_dep : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
    Polynomial.C q * Polynomial.X + Polynomial.C r
  have hdep_eq : fm.comp (Polynomial.X + Polynomial.C (-a₃ / 4)) = g_dep := by
    rw [hfm_expand]
    exact (section_14_4_depress_quartic hchar2 a₃ a₂ a₁ a₀).1
  -- Roots `r_f i := (e i : L)` of `f` (and `fm`) in `L`:
  let r_f : Fin 4 → L := fun i => (e i : L)
  have hr_inj : Function.Injective r_f := fun i j hij => e.injective (Subtype.ext hij)
  obtain ⟨m_s, c_s, ρ_s, hexp_f⟩ := hsf.1
  have hm_s4 : m_s = 4 := ((garlingSplitsExplicit_props hf0 hexp_f).2.2.1).trans hdeg
  have hc_s : c_s = f.leadingCoeff := (garlingSplitsExplicit_props hf0 hexp_f).1
  subst hm_s4 hc_s
  have hρ_inj : Function.Injective ρ_s :=
    (injective_roots_iff_separable_and_not_repeated hf0 hexp_f).1.mpr hsep
  -- Since `Set.range r_f = garlingRootSet K L f = Set.range ρ_s`, `r_f` is a permutation of `ρ_s`!
  have hperm_rf : ∃ τ : SigmaN 4, ∀ i : Fin 4, ρ_s i = r_f (τ i) := by
    have hmem_rf : ∀ i : Fin 4, ρ_s i ∈ garlingRootSet K L f := by
      intro i
      rw [mem_garlingRootSet_iff, Polynomial.aeval_def, ← Polynomial.eval_map,
        hexp_f, Polynomial.eval_mul, Polynomial.eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    let τ_fun : Fin 4 → Fin 4 := fun i => e.symm ⟨ρ_s i, hmem_rf i⟩
    have hτ_inj : Function.Injective τ_fun := fun i j hij =>
      hρ_inj (congrArg Subtype.val (e.symm.injective hij))
    refine ⟨Equiv.ofBijective τ_fun ⟨hτ_inj, Finite.injective_iff_surjective.mp hτ_inj⟩, fun i => ?_⟩
    change ρ_s i = (e (e.symm ⟨ρ_s i, hmem_rf i⟩) : L)
    rw [e.apply_symm_apply]
  obtain ⟨τ_rf, hτ_rf⟩ := hperm_rf
  have hexp_rf : GarlingSplitsExplicit K L f 4 f.leadingCoeff r_f := by
    unfold GarlingSplitsExplicit at hexp_f ⊢
    rw [hexp_f]
    congr 1
    simp_rw [hτ_rf]
    exact Fintype.prod_equiv τ_rf
      (fun i => Polynomial.X - Polynomial.C (r_f (τ_rf i)))
      (fun i => Polynomial.X - Polynomial.C (r_f i))
      (fun _ => rfl)
  have hexp_fm : GarlingSplitsExplicit K L fm 4 1 r_f := by
    have h := garlingSplitsExplicit_C_mul f.leadingCoeff⁻¹ hexp_rf
    rwa [inv_mul_cancel₀ hlc] at h
  -- Shifted roots `α i := r_f i - algebraMap K L (-a₃ / 4)` of `g_dep`:
  let α : Fin 4 → L := fun i => r_f i - algebraMap K L (-a₃ / 4)
  have hexp_gdep : GarlingSplitsExplicit K L g_dep 4 1 α := by
    rw [← hdep_eq]
    exact garlingSplitsExplicit_comp_X_add_C hexp_fm (-a₃ / 4)
  have hfac_α : (Polynomial.X - Polynomial.C (α 0)) * (Polynomial.X - Polynomial.C (α 1)) *
      (Polynomial.X - Polynomial.C (α 2)) * (Polynomial.X - Polynomial.C (α 3)) =
      Polynomial.X ^ 4 + Polynomial.C (algebraMap K L p) * Polynomial.X ^ 2 +
        Polynomial.C (algebraMap K L q) * Polynomial.X +
        Polynomial.C (algebraMap K L r) := by
    have heq := hexp_gdep.symm
    rw [Fin.prod_univ_four] at heq
    simp only [g_dep, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, map_one, one_mul, mul_assoc] at heq ⊢
    exact heq
  have hid := section_14_4_resolvent_identities h2L hfac_α
  let β : L := α 0 + α 1
  let γ : L := α 0 + α 2
  let δ : L := α 0 + α 3
  let θ : Fin 3 → L := ![β ^ 2, γ ^ 2, δ ^ 2]
  have hθ_eq_part : ∀ i : Fin 3, θ i = quarticPairProd i α := by
    have hp := quarticPairProd_vals α
    intro i; fin_cases i
    · exact hid.1.2.1.trans hp.1.symm
    · exact hid.1.2.2.1.trans hp.2.1.symm
    · exact hid.1.2.2.2.trans hp.2.2.symm
  have hexp_g : GarlingSplitsExplicit K L g 3 1 θ := by
    unfold GarlingSplitsExplicit
    have hg_map : g.map (algebraMap K L) =
        depressedQuarticResolvent (algebraMap K L p) (algebraMap K L q) (algebraMap K L r) := by
      change (depressedQuarticResolvent p q r).map (algebraMap K L) = _
      unfold depressedQuarticResolvent
      simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        map_ofNat]
    rw [hg_map, Fin.prod_univ_three, map_one, map_one, one_mul]
    have u0 : θ 0 = β ^ 2 := rfl
    have u1 : θ 1 = γ ^ 2 := rfl
    have u2 : θ 2 = δ ^ 2 := rfl
    rw [u0, u1, u2]
    simpa only [mul_assoc] using hid.2.2.1.symm
  -- Distinctness of `θ 0, θ 1, θ 2`:
  have hα_inj : Function.Injective α := fun i j hij => hr_inj (sub_left_inj.mp hij)
  have hθ_inj : Function.Injective θ := by
    by_contra hninj
    have hd0 : garlingDeltaTuple θ = 0 := (garlingDeltaTuple_eq_zero_iff θ).mpr hninj
    have hdisc0 : garlingDiscTuple θ = 0 := by unfold garlingDiscTuple; rw [hd0, zero_pow (by decide)]
    have hα_eta : ![α 0, α 1, α 2, α 3] = α := by ext i; fin_cases i <;> rfl
    rw [hid.2.2.2.1.2, hα_eta] at hdisc0
    have hdα0 : garlingDeltaTuple α = 0 := sq_eq_zero_iff.mp hdisc0
    exact (garlingDeltaTuple_eq_zero_iff α).mp hdα0 hα_inj
  -- Galois action on `α` and `θ`:
  have hσ_α : ∀ (σ : GarlingPolyGaloisGroup K L f) (i : Fin 4), σ (α i) = α (φ σ i) := by
    intro σ i
    dsimp [α, r_f]
    rw [map_sub, AlgEquiv.commutes, ← garlingRootLabellingPermHom_apply e σ i]
  have hσ_θ : ∀ (σ : GarlingPolyGaloisGroup K L f) (i : Fin 3),
      σ (θ i) = θ (s4ToS3Hom (φ σ) i) := by
    intro σ i
    rw [hθ_eq_part i]
    unfold quarticPairProd
    simp only [map_mul, map_neg, map_add, hσ_α σ]
    change quarticPairProd i (α ∘ φ σ) = _
    rw [quarticPairProd_comp_perm i α (φ σ), ← hθ_eq_part (s4ToS3Hom (φ σ) i)]
  -- Show `K(θ 0, θ 1, θ 2)` has fixing subgroup `H = viergruppe.comap φ`, hence equals `M₀`:
  let Kθ : IntermediateField K L := IntermediateField.adjoin K (Set.range θ)
  have hfixing_Kθ : Kθ.fixingSubgroup = H := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    change (∀ x ∈ Kθ, σ x = x) ↔ φ σ ∈ viergruppe
    rw [← s4ToS3Hom_ker, MonoidHom.mem_ker]
    constructor
    · intro hfix
      apply Equiv.ext
      intro i
      have hfix_i : σ (θ i) = θ i := hfix (θ i) (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      rw [hσ_θ σ i] at hfix_i
      exact hθ_inj hfix_i
    · intro hker
      let Fixσ : IntermediateField K L :=
        { carrier := {x : L | σ x = x}
          mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
            change σ (a * b) = a * b; rw [map_mul, ha, hb]
          one_mem' := map_one σ
          add_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
            change σ (a + b) = a + b; rw [map_add, ha, hb]
          zero_mem' := map_zero σ
          inv_mem' := fun {a} (ha : σ a = a) => by
            change σ a⁻¹ = a⁻¹; rw [map_inv₀, ha]
          algebraMap_mem' := σ.commutes }
      have hle : Kθ ≤ Fixσ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        change σ (θ i) = θ i
        rw [hσ_θ σ i, hker]
        rfl
      exact fun x hx => hle hx
  have hKθ_eq_M₀ : Kθ = M₀ := by
    dsimp [M₀]
    rw [← hfixing_Kθ, IsGalois.fixedField_fixingSubgroup]
  -- 1. `IsGarlingSplittingFieldExtension K M₀ g`:
  have hg_mon : g.Monic := quarticCubicResolvent_monic f
  have hsf_M₀ : IsGarlingSplittingFieldExtension K M₀ g := by
    have hθ_M₀ : ∀ i : Fin 3, θ i ∈ M₀ := fun i =>
      hKθ_eq_M₀ ▸ IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    refine ⟨⟨3, 1, _, garlingSplitsExplicit_of_mem_intermediateField M₀ hexp_g hθ_M₀⟩, ?_⟩
    intro E' hne hsp_E'
    obtain ⟨m', c', ρ', hexp'⟩ := hsp_E'
    have hm'3 : m' = 3 :=
      ((garlingSplitsExplicit_props hg_mon.ne_zero hexp').2.2.1).trans (quarticCubicResolvent_natDegree f)
    have hc'1 : c' = 1 :=
      (garlingSplitsExplicit_props hg_mon.ne_zero hexp').1.trans hg_mon.leadingCoeff
    subst hm'3 hc'1
    have hexp'_L : ∏ j : Fin 3, (Polynomial.X - Polynomial.C (M₀.val (E'.val (ρ' j)))) =
        ∏ j : Fin 3, (Polynomial.X - Polynomial.C (θ j)) := by
      have hmap := congrArg (Polynomial.map (M₀.val.toRingHom.comp E'.val.toRingHom)) hexp'.symm
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_map] at hmap
      have hcomp : (M₀.val.toRingHom.comp E'.val.toRingHom).comp (algebraMap K E') =
          algebraMap K L := RingHom.ext fun _ => rfl
      rw [hcomp, hexp_g] at hmap
      simp only [map_one, one_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at hmap
      exact hmap
    obtain ⟨π', hπ'⟩ := prod_X_sub_C_eq_imp_perm hexp'_L
    have hθ_in_map : Set.range θ ⊆ ((E'.map M₀.val : IntermediateField K L) : Set L) := by
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_map]
      exact ⟨E'.val (ρ' (π' i)), (ρ' (π' i)).2, (congrFun hπ' i).symm⟩
    have hM₀_le : M₀ ≤ E'.map M₀.val :=
      calc M₀ = Kθ := hKθ_eq_M₀.symm
        _ ≤ E'.map M₀.val := IntermediateField.adjoin_le_iff.mpr hθ_in_map
    apply hne
    rw [eq_top_iff]
    rintro x _
    have hx_map : (x : L) ∈ E'.map M₀.val := hM₀_le x.2
    rw [IntermediateField.mem_map] at hx_map
    rcases hx_map with ⟨y, hyE', hy_eq⟩
    have hyx : y = x := M₀.val.injective hy_eq
    rwa [← hyx]
  -- 2. Every `M : IntermediateField K L` with `IsGarlingSplittingFieldExtension K M g` equals `M₀`:
  have huniq_M : ∀ M : IntermediateField K L, IsGarlingSplittingFieldExtension K M g → M = M₀ := by
    intro M hsf_M
    obtain ⟨m_M, c_M, ρ_M, hexp_M⟩ := hsf_M.1
    have hm_M3 : m_M = 3 :=
      ((garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).2.2.1).trans (quarticCubicResolvent_natDegree f)
    have hc_M1 : c_M = 1 :=
      (garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).1.trans hg_mon.leadingCoeff
    subst hm_M3 hc_M1
    have hexp_ML : ∏ j : Fin 3, (Polynomial.X - Polynomial.C (M.val (ρ_M j))) =
        ∏ j : Fin 3, (Polynomial.X - Polynomial.C (θ j)) := by
      have hmap := congrArg (Polynomial.map M.val.toRingHom) hexp_M.symm
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_map] at hmap
      have hcomp : M.val.toRingHom.comp (algebraMap K M) = algebraMap K L := RingHom.ext fun _ => rfl
      rw [hcomp, hexp_g] at hmap
      simp only [map_one, one_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at hmap
      exact hmap
    obtain ⟨π_M, hπ_M⟩ := prod_X_sub_C_eq_imp_perm hexp_ML
    have hM₀_le_M : M₀ ≤ M := by
      rw [← hKθ_eq_M₀, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      rw [congrFun hπ_M i]
      exact (ρ_M (π_M i)).2
    have hadj_top_M : IntermediateField.adjoin K (Set.range ρ_M) = ⊤ := by
      by_contra hne
      let A_M : IntermediateField K M := IntermediateField.adjoin K (Set.range ρ_M)
      exact hsf_M.2 A_M hne
        ⟨3, 1, _, garlingSplitsExplicit_of_mem_intermediateField A_M hexp_M
          (fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)⟩
    have hM_le_M₀ : M ≤ M₀ := by
      intro x hx
      have hx_adj : (⟨x, hx⟩ : M) ∈ IntermediateField.adjoin K (Set.range ρ_M) :=
        hadj_top_M.symm ▸ IntermediateField.mem_top
      have hle_sub : IntermediateField.adjoin K (Set.range ρ_M) ≤ M₀.comap M.val := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        change M.val (ρ_M j) ∈ M₀
        have hj : θ (π_M.symm j) = M.val (ρ_M j) := by
          simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun hπ_M (π_M.symm j)
        rw [← hj, ← hKθ_eq_M₀]
        exact IntermediateField.subset_adjoin K _ ⟨π_M.symm j, rfl⟩
      exact hle_sub hx_adj
    exact le_antisymm hM_le_M₀ hM₀_le_M
  -- 3. Injectivity of `φ` and degree relations `[L : M₀] = |G ⊓ N|`, `[M₀ : K] * |G ⊓ N| = |G|`:
  have hφ_inj : Function.Injective φ := by
    intro σ₁ σ₂ hφ_eq
    have heq_rf : ∀ i : Fin 4, σ₁ (r_f i) = σ₂ (r_f i) := by
      intro i
      dsimp [r_f]
      rw [← garlingRootLabellingPermHom_apply e σ₁ i,
        ← garlingRootLabellingPermHom_apply e σ₂ i]
      change (e (φ σ₁ i) : L) = (e (φ σ₂ i) : L)
      rw [hφ_eq]
    let EqField : IntermediateField K L :=
      { carrier := {x : L | σ₁ x = σ₂ x}
        mul_mem' := fun {a b} (ha : σ₁ a = σ₂ a) (hb : σ₁ b = σ₂ b) => by
          change σ₁ (a * b) = σ₂ (a * b); rw [map_mul, map_mul, ha, hb]
        one_mem' := by change σ₁ 1 = σ₂ 1; rw [map_one, map_one]
        add_mem' := fun {a b} (ha : σ₁ a = σ₂ a) (hb : σ₁ b = σ₂ b) => by
          change σ₁ (a + b) = σ₂ (a + b); rw [map_add, map_add, ha, hb]
        zero_mem' := by change σ₁ 0 = σ₂ 0; rw [map_zero, map_zero]
        inv_mem' := fun {a} (ha : σ₁ a = σ₂ a) => by
          change σ₁ a⁻¹ = σ₂ a⁻¹; rw [map_inv₀, map_inv₀, ha]
        algebraMap_mem' := fun k => by
          change σ₁ (algebraMap K L k) = σ₂ (algebraMap K L k)
          rw [AlgEquiv.commutes, AlgEquiv.commutes] }
    have hEq_top : EqField = ⊤ := by
      by_contra hne
      exact hsf.2 EqField hne
        ⟨4, f.leadingCoeff, _, garlingSplitsExplicit_of_mem_intermediateField EqField hexp_rf heq_rf⟩
    ext x
    have hx : x ∈ EqField := hEq_top.symm ▸ IntermediateField.mem_top
    exact hx
  let eG : GarlingPolyGaloisGroup K L f ≃* G :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
  let eH : H ≃ (G ⊓ viergruppe : Subgroup (SigmaN 4)) :=
    { toFun := fun ⟨σ, hσ⟩ => ⟨φ σ, ⟨σ, rfl⟩, hσ⟩
      invFun := fun ⟨π, ⟨hG, hV⟩⟩ => ⟨hG.choose, by
        change φ hG.choose ∈ viergruppe
        rwa [hG.choose_spec]⟩
      left_inv := fun ⟨σ, _⟩ => Subtype.ext (hφ_inj (Exists.choose_spec (⟨σ, rfl⟩ : φ σ ∈ G)))
      right_inv := fun ⟨π, ⟨hG, _⟩⟩ => Subtype.ext hG.choose_spec }
  have hfin_M₀_L : Module.finrank M₀ L = Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) := by
    dsimp [M₀]
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_congr eH]
  have hfin_prod : Module.finrank K M₀ * Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) =
      Nat.card G := by
    rw [← hfin_M₀_L, Module.finrank_mul_finrank K M₀ L, ← IsGalois.card_aut_eq_finrank K L]
    exact Nat.card_congr eG.toEquiv
  exact ⟨hsf_M₀, huniq_M, hfin_M₀_L, hfin_prod, hφ_inj⟩

/-! ### Exercise 14.6: Classification of Transitive Subgroups of `Σ₄` (§14.4, p. 117) -/

/-- **Exercise 14.6** (§14.4, printed p. 117 / PDF p. 125):
*"Suppose that `G` is a transitive subgroup of `Σ₄`. Show that `G` is either (i) `Σ₄`, (ii) `A₄`,
(iii) the Viergruppe `N`, (iv) cyclic of order `4` or (v) a non-abelian group of order `8`,
isomorphic to the group of rotations and reflections of a square."*

Proved as an exact bidirectional equivalence (`↔`), together with a companion theorem showing that
the five branches `(i)`–`(v)` are pairwise mutually exclusive! -/
theorem exercise_14_6 (G : Subgroup (SigmaN 4)) :
    SubgroupActsTransitively G ↔
      G = ⊤ ∨
      G = alternatingGroup (Fin 4) ∨
      G = viergruppe ∨
      (IsCyclic G ∧ Nat.card G = 4) ∨
      ((∃ x y : G, x * y ≠ y * x) ∧ Nat.card G = 8 ∧ Nonempty (G ≃* DihedralGroup 4)) := by
  constructor
  · intro htr
    obtain ⟨i, ⟨g, rfl⟩⟩ := (exercise_11_5_s4.2.2.1 G).mp htr
    fin_cases i
    · right; right; left
      change (s4V4.map (MulAut.conj g).toMonoidHom) = viergruppe
      rw [← viergruppe_eq_s4V4]
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact ⟨by rintro ⟨y, hy, rfl⟩; exact viergruppe_normal.conj_mem y hy g,
        fun hx => ⟨g⁻¹ * x * g, viergruppe_normal.conj_mem x hx g⁻¹, by group⟩⟩
    · right; right; right; left
      let eConj : s4C4 ≃* (s4C4.map (MulAut.conj g).toMonoidHom) :=
        (MulAut.conj g).subgroupMap s4C4
      have hcyc_s4C4 : IsCyclic s4C4 := by
        unfold s4C4; infer_instance
      have hcyc : IsCyclic (s4C4.map (MulAut.conj g).toMonoidHom) :=
        isCyclic_of_surjective eConj eConj.surjective
      have hc4 : Nat.card (s4C4.map (MulAut.conj g).toMonoidHom) = 4 := by
        rw [← Nat.card_congr eConj.toEquiv]
        exact exercise_11_5_s4.1 1
      exact ⟨hcyc, hc4⟩
    · right; right; right; right
      let G' := s4D4.map (MulAut.conj g).toMonoidHom
      have hc8 : Nat.card G' = 8 := by
        rw [← isConjugateSubgroup_natCard_eq ⟨g, rfl⟩]
        exact natCard_s4D4
      obtain ⟨_, ⟨eD⟩⟩ := s4_subgroup_card_eight_conj_d4 G' hc8
      have hnonab : ∃ x y : G', x * y ≠ y * x := by
        have hne_D : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 ≠
            DihedralGroup.sr 0 * DihedralGroup.r 1 := by decide
        refine ⟨eD.symm (DihedralGroup.r 1), eD.symm (DihedralGroup.sr 0), fun heq => hne_D ?_⟩
        simpa [map_mul] using congrArg eD heq
      exact ⟨hnonab, hc8, ⟨eD⟩⟩
    · right; left
      change (alternatingGroup (Fin 4)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 4)
      have hnormA : (alternatingGroup (Fin 4)).Normal := inferInstance
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact ⟨by rintro ⟨y, hy, rfl⟩; exact hnormA.conj_mem y hy g,
        fun hx => ⟨g⁻¹ * x * g, hnormA.conj_mem x hx g⁻¹, by group⟩⟩
    · left
      change (⊤ : Subgroup (SigmaN 4)).map (MulAut.conj g).toMonoidHom = ⊤
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, iff_true,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact ⟨g⁻¹ * x * g, by group⟩
  · rintro (rfl | rfl | rfl | ⟨hcyc, hc4⟩ | ⟨_, hc8, _⟩)
    · exact exercise_11_5_s4.2.1 4
    · exact exercise_11_5_s4.2.1 3
    · exact viergruppe_actsTransitively
    · obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hzpow_top : Subgroup.zpowers g = ⊤ := by
        ext x; simp [hg x]
      have hord_g : orderOf g = 4 := by
        rw [← Nat.card_zpowers, hzpow_top, Subgroup.card_top, hc4]
      have hord_coe : orderOf (g : SigmaN 4) = 4 := (Subgroup.orderOf_coe g).trans hord_g
      let σ : SigmaN 4 := (g : SigmaN 4)
      have hσ4 : σ ^ 4 = 1 :=
        calc σ ^ 4 = σ ^ orderOf σ := by rw [hord_coe]
          _ = 1 := pow_orderOf_eq_one σ
      have hσ2 : σ ^ 2 ≠ 1 := by
        intro h2
        have hdvd := orderOf_dvd_of_pow_eq_one h2
        rw [hord_coe] at hdvd
        omega
      -- Since `σ ^ 2 ≠ 1`, choose `x₀ : Fin 4` with `(σ ^ 2) x₀ ≠ x₀`; then `k ↦ (σ ^ k) x₀`
      -- is injective `Fin 4 → Fin 4`, hence surjective, so `G` acts transitively on `Fin 4`!
      have hex_x₀ : ∃ x₀ : Fin 4, (σ ^ 2) x₀ ≠ x₀ := by
        by_contra hall
        push Not at hall
        exact hσ2 (Equiv.ext hall)
      obtain ⟨x₀, hx₀⟩ := hex_x₀
      have hσ1_ne : σ x₀ ≠ x₀ := by
        intro h1
        apply hx₀
        calc (σ ^ 2) x₀ = σ (σ x₀) := by rw [sq, Equiv.Perm.mul_apply]
          _ = x₀ := by rw [h1, h1]
      have hσ3_ne' : (σ ^ 3) x₀ ≠ x₀ := by
        intro h3
        apply hσ1_ne
        calc σ x₀ = σ ((σ ^ 3) x₀) := by rw [h3]
          _ = (σ ^ 4) x₀ := by
              change σ ((σ * (σ * σ)) x₀) = (σ * (σ * (σ * σ))) x₀
              simp [Equiv.Perm.mul_apply]
          _ = x₀ := by rw [hσ4]; rfl
      let orb : Fin 4 → Fin 4 := fun k => (σ ^ (k : ℕ)) x₀
      have horb_inj : Function.Injective orb := by
        intro a b hab
        dsimp [orb] at hab
        have hstep : ∀ d : ℕ, d ∈ ({1, 2, 3} : Set ℕ) → (σ ^ d) x₀ ≠ x₀ := by
          rintro d (rfl | rfl | rfl)
          · simpa using hσ1_ne
          · exact hx₀
          · exact hσ3_ne'
        fin_cases a <;> fin_cases b
        · rfl
        · exfalso; exact hstep 1 (by simp) (by simpa using hab.symm)
        · exfalso; exact hstep 2 (by simp) (by simpa using hab.symm)
        · exfalso; exact hstep 3 (by simp) (by simpa using hab.symm)
        · exfalso; exact hstep 1 (by simp) (by simpa using hab)
        · rfl
        · exfalso
          apply hstep 1 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) z) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h.symm
        · exfalso
          apply hstep 2 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) z) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h.symm
        · exfalso; exact hstep 2 (by simp) (by simpa using hab)
        · exfalso
          apply hstep 1 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) z) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h
        · rfl
        · exfalso
          apply hstep 1 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) ((σ⁻¹ : SigmaN 4) z)) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h.symm
        · exfalso; exact hstep 3 (by simp) (by simpa using hab)
        · exfalso
          apply hstep 2 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) z) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h
        · exfalso
          apply hstep 1 (by simp)
          have h := congrArg (fun z => (σ⁻¹ : SigmaN 4) ((σ⁻¹ : SigmaN 4) z)) hab
          simpa [pow_succ, mul_assoc, Equiv.Perm.mul_apply] using h
        · rfl
      have horb_surj : Function.Surjective orb := Finite.injective_iff_surjective.mp horb_inj
      intro x y
      obtain ⟨a, rfl⟩ := horb_surj x
      obtain ⟨b, rfl⟩ := horb_surj y
      refine ⟨((g ^ (b : ℕ)) * (g ^ (a : ℕ))⁻¹ : G), ((g ^ (b : ℕ)) * (g ^ (a : ℕ))⁻¹).2, ?_⟩
      dsimp [orb]
      change ((σ ^ (b : ℕ)) * (σ ^ (a : ℕ))⁻¹) ((σ ^ (a : ℕ)) x₀) = (σ ^ (b : ℕ)) x₀
      simp [Equiv.Perm.mul_apply]
    · exact (exercise_11_5_s4.2.2.1 G).mpr ⟨2, (s4_subgroup_card_eight_conj_d4 G hc8).1⟩

/-- Pairwise mutual exclusivity of the five subgroup classes `(i)`–`(v)` in `Exercise 14.6`. -/
theorem exercise_14_6_mutually_exclusive (G : Subgroup (SigmaN 4)) :
    let P₁ := G = ⊤
    let P₂ := G = alternatingGroup (Fin 4)
    let P₃ := G = viergruppe
    let P₄ := IsCyclic G ∧ Nat.card G = 4
    let P₅ := (∃ x y : G, x * y ≠ y * x) ∧ Nat.card G = 8 ∧ Nonempty (G ≃* DihedralGroup 4)
    ¬ (P₁ ∧ P₂) ∧ ¬ (P₁ ∧ P₃) ∧ ¬ (P₁ ∧ P₄) ∧ ¬ (P₁ ∧ P₅) ∧
    ¬ (P₂ ∧ P₃) ∧ ¬ (P₂ ∧ P₄) ∧ ¬ (P₂ ∧ P₅) ∧
    ¬ (P₃ ∧ P₄) ∧ ¬ (P₃ ∧ P₅) ∧ ¬ (P₄ ∧ P₅) := by
  dsimp only
  have hc_top : Nat.card (⊤ : Subgroup (SigmaN 4)) = 24 := exercise_11_5_s4.1 4
  have hc_A4 : Nat.card (alternatingGroup (Fin 4)) = 12 := exercise_11_5_s4.1 3
  have hc_V4 : Nat.card viergruppe = 4 := natCard_viergruppe
  have hnot34 : ¬ (G = viergruppe ∧ IsCyclic G ∧ Nat.card G = 4) := by
    rintro ⟨rfl, hcyc, hc4⟩
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hzpow_top : Subgroup.zpowers g = ⊤ := by ext x; simp [hg x]
    have hord : orderOf (g : SigmaN 4) = 4 := by
      rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hzpow_top, Subgroup.card_top, hc4]
    have hsq_V4 : ∀ σ : SigmaN 4, σ ∈ viergruppeFinset → σ * σ = 1 := by decide
    have hg_sq1 : (g : SigmaN 4) ^ 2 = 1 := by
      rw [sq]; exact hsq_V4 g.1 g.2
    have hdvd := orderOf_dvd_of_pow_eq_one hg_sq1
    rw [hord] at hdvd
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hnot34, ?_, ?_⟩
  · rintro ⟨rfl, h⟩; have hc := hc_top; rw [h, hc_A4] at hc; omega
  · rintro ⟨rfl, h⟩; have hc := hc_top; rw [h, hc_V4] at hc; omega
  · rintro ⟨rfl, _, hc4⟩; rw [hc_top] at hc4; omega
  · rintro ⟨rfl, _, hc8, _⟩; rw [hc_top] at hc8; omega
  · rintro ⟨rfl, h⟩; have hc := hc_A4; rw [h, hc_V4] at hc; omega
  · rintro ⟨rfl, _, hc4⟩; rw [hc_A4] at hc4; omega
  · rintro ⟨rfl, _, hc8, _⟩; rw [hc_A4] at hc8; omega
  · rintro ⟨rfl, _, hc8, _⟩; rw [hc_V4] at hc8; omega
  · rintro ⟨⟨_, hc4⟩, _, hc8, _⟩; omega

/-! ### Exercise 14.7: Quartic Galois Group Decision Table & Repaired Rows 4–5 (§14.4, p. 117; `QUEUE.md`) -/

theorem ringChar_rat_ne_two : ringChar ℚ ≠ 2 := by
  rw [ringChar.eq_zero]; decide

theorem ringChar_rat_ne_three : ringChar ℚ ≠ 3 := by
  rw [ringChar.eq_zero]; decide

/-- **Impossibility of Printed Rows 4–5 and Non-Exhaustiveness Counterexample in `Exercise 14.7`**
(`BRIEF.md` Flag 3 & `QUEUE.md`):
1. For **every** field `K` (`char K ≠ 2, 3`), **every** irreducible quartic `f ∈ K[x]`
   (`f.natDegree = 4`), **every** splitting field extension `L : K` of `f`, `g := quarticCubicResolvent f`,
   and **every** intermediate field `M : IntermediateField K L` with `IsGarlingSplittingFieldExtension K M g`:
   - If `g` splits over `K` (`GarlingSplitsOver K K g`), then `garlingDiscriminant f` **has a square
     root in `K`**, `M = ⊥`, and `f` remains **irreducible** in `M[x]`;
   - Consequently, **printed Row 4** (`(¬ ∃ d : K, d ^ 2 = Δ) ∧ GarlingSplitsOver K K g ∧ ¬ Irreducible f_M`)
     and **printed Row 5** (`(¬ ∃ d : K, d ^ 2 = Δ) ∧ GarlingSplitsOver K K g ∧ Irreducible f_M`)
     are **mathematically impossible** (satisfied by zero irreducible quartics)!
2. Over `K = ℚ`, the irreducible quartic `f = x⁴ - 2` (`Exercise 14.8(v)`, `Γ_ℚ(f) ≃* DihedralGroup 4`)
   has `garlingDiscriminant f = -2048` (no square root in `ℚ`) and cubic resolvent `g = x³ + 8x`,
   which is neither irreducible over `ℚ` nor splits over `ℚ`, so `x⁴ - 2` satisfies **none** of the
   five printed rows, refuting *"Verify that the following table includes all possibilities"* as printed. -/
theorem exercise_14_7_printed_rows_4_5_impossible :
    (∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L],
      ringChar K ≠ 2 →
      ∀ {f : K[X]}, Irreducible f → f.natDegree = 4 →
      IsGarlingSplittingFieldExtension K L f →
      ∀ (M : IntermediateField K L),
      IsGarlingSplittingFieldExtension K M (quarticCubicResolvent f) →
      let Δ := garlingDiscriminant f
      let g := quarticCubicResolvent f
      (GarlingSplitsOver K K g →
        (∃ d : K, d ^ 2 = Δ) ∧ M = ⊥ ∧ Irreducible (f.map (algebraMap K M))) ∧
      ¬ ((¬ ∃ d : K, d ^ 2 = Δ) ∧ GarlingSplitsOver K K g ∧
          ¬ Irreducible (f.map (algebraMap K M))) ∧
      ¬ ((¬ ∃ d : K, d ^ 2 = Δ) ∧ GarlingSplitsOver K K g ∧
          Irreducible (f.map (algebraMap K M)))) ∧
    (let f : ℚ[X] := Polynomial.X ^ 4 - 2
     let g : ℚ[X] := quarticCubicResolvent f
     Irreducible f ∧
     f.natDegree = 4 ∧
     g = Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X ∧
     garlingDiscriminant f = -2048 ∧
     (¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ∧
     ¬ Irreducible g ∧
     ¬ GarlingSplitsOver ℚ ℚ g) := by
  refine ⟨?_, ?_⟩
  · intro K L _ _ _ hchar2 f hirr hdeg _ M hsf_M Δ g
    have himp : GarlingSplitsOver K K g →
        (∃ d : K, d ^ 2 = Δ) ∧ M = ⊥ ∧ Irreducible (f.map (algebraMap K M)) := by
      intro hsp_K
      have hg_mon : g.Monic := quarticCubicResolvent_monic f
      obtain ⟨m, c, ρ, hexp_K⟩ := hsp_K
      have hm3 : m = 3 :=
        ((garlingSplitsExplicit_props hg_mon.ne_zero hexp_K).2.2.1).trans
          (quarticCubicResolvent_natDegree f)
      have hc1 : c = 1 :=
        (garlingSplitsExplicit_props hg_mon.ne_zero hexp_K).1.trans hg_mon.leadingCoeff
      subst hm3 hc1
      -- 1. `Δ = garlingDiscriminant g = (garlingDeltaTuple ρ)^2` in `K`!
      have hsq : ∃ d : K, d ^ 2 = Δ := by
        refine ⟨garlingDeltaTuple ρ, ?_⟩
        have h1 : algebraMap K K (garlingDiscriminant g) = garlingDiscTuple ρ :=
          garlingDiscriminant_eq_discTuple hg_mon.ne_zero hexp_K
        simp only [Algebra.algebraMap_self, RingHom.id_apply, garlingDiscTuple] at h1
        dsimp [Δ, g] at h1 ⊢
        rw [← garlingDiscriminant_quarticCubicResolvent hchar2 hdeg, h1]
      -- 2. `M = ⊥` because `g` splits over `(⊥ : IntermediateField K M)` (`⊥ = ⊤` in `M`):
      have hbot_top_M : (⊥ : IntermediateField K M) = ⊤ := by
        by_contra hne
        let ρ_bot : Fin 3 → (⊥ : IntermediateField K M) :=
          fun i => algebraMap K (⊥ : IntermediateField K M) (ρ i)
        have hexp_bot : GarlingSplitsExplicit K (⊥ : IntermediateField K M) g 3 1 ρ_bot := by
          unfold GarlingSplitsExplicit at hexp_K ⊢
          simp only [Algebra.algebraMap_self, Polynomial.map_id] at hexp_K
          have hmap := congrArg (Polynomial.map (algebraMap K (⊥ : IntermediateField K M))) hexp_K
          simpa only [Polynomial.map_mul, Polynomial.map_one, Polynomial.map_C, Polynomial.map_prod,
            Polynomial.map_sub, Polynomial.map_X, map_one] using hmap
        exact hsf_M.2 ⊥ hne ⟨3, 1, ρ_bot, hexp_bot⟩
      have hM_eq_bot : M = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx_top : (⟨x, hx⟩ : M) ∈ (⊤ : IntermediateField K M) := IntermediateField.mem_top
        rw [← hbot_top_M, IntermediateField.mem_bot] at hx_top
        rcases hx_top with ⟨k, hk⟩
        rw [IntermediateField.mem_bot]
        exact ⟨k, congrArg Subtype.val hk⟩
      -- 3. Since `M = ⊥`, `algebraMap K M` is bijective (`RingEquiv`), so `f.map (algebraMap K M)` is irreducible!
      have hirr_M : Irreducible (f.map (algebraMap K M)) := by
        have hsurj : Function.Surjective (algebraMap K M) := by
          intro y
          let yL : L := y.1
          have hy : yL ∈ M := y.2
          rw [hM_eq_bot, IntermediateField.mem_bot] at hy
          rcases hy with ⟨k, hk⟩
          exact ⟨k, Subtype.ext hk⟩
        let eKM : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) ⟨(algebraMap K M).injective, hsurj⟩
        let ePoly : K[X] ≃+* M[X] := Polynomial.mapEquiv eKM
        have hmap_eq : f.map (algebraMap K M) = ePoly f := rfl
        rw [hmap_eq]
        exact (MulEquiv.irreducible_iff ePoly.toMulEquiv).mpr hirr
      exact ⟨hsq, hM_eq_bot, hirr_M⟩
    exact ⟨himp,
      fun ⟨hno, hsp, _⟩ => hno (himp hsp).1,
      fun ⟨hno, hsp, _⟩ => hno (himp hsp).1⟩
  · -- Concrete counterexample `f = X^4 - 2 ∈ ℚ[X]`:
    dsimp only
    let f : ℚ[X] := Polynomial.X ^ 4 - 2
    have hf_deg : f.natDegree = 4 := by
      dsimp [f]
      rw [← Polynomial.C_ofNat, Polynomial.natDegree_X_pow_sub_C]
    -- `Irreducible f` (Eisenstein at `2`, or `[ℚ(2^(1/4)) : ℚ]` / `exercise_11_6`):
    have hf_irr : Irreducible f := by
      let fZ : ℤ[X] := Polynomial.X ^ 4 - Polynomial.C 2
      have hfZ_deg : fZ.natDegree = 4 := Polynomial.natDegree_X_pow_sub_C
      have hfZ_mon : fZ.Monic := Polynomial.monic_X_pow_sub_C 2 (by decide)
      have hcopZ : IsGarlingRelativelyPrime (Set.range fun i : Fin 5 => fZ.coeff i) :=
        isGarlingRelativelyPrime_coeffs_of_monic hfZ_mon hfZ_deg
      have hdvdZ : ∀ i < 4, (2 : ℤ) ∣ fZ.coeff i := by
        intro i hi
        dsimp [fZ]
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        interval_cases i <;> decide
      have hndvd_top : ¬ ((2 : ℤ) ∣ fZ.coeff 4) := by
        dsimp [fZ]
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        decide
      have hndvd_sq : ¬ ((2 : ℤ) ^ 2 ∣ fZ.coeff 0) := by
        dsimp [fZ]
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        decide
      have hirrZ : Irreducible fZ :=
        (theorem_5_2 (by decide : 1 ≤ 4) (le_of_eq hfZ_deg) hcopZ Int.prime_two
          hdvdZ hndvd_top hndvd_sq).2.1
      have hmap_fZ : fZ.map (algebraMap ℤ ℚ) = f := by simp [fZ, f]
      rcases (corollary_gauss_lemma ℚ fZ).mp hirrZ with ⟨a, _, hC⟩ | ⟨_, hmap_irr⟩
      · exfalso
        have hd := congrArg Polynomial.natDegree hC
        rw [hfZ_deg, Polynomial.natDegree_C] at hd
        omega
      · rwa [hmap_fZ] at hmap_irr
    have hf_form : f =
        Polynomial.X ^ 4 + Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C 0 * Polynomial.X + Polynomial.C (-2) := by
      dsimp [f]
      rw [← Polynomial.C_ofNat]
      simp [sub_eq_add_neg]
    have hg_eq : quarticCubicResolvent f = Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X := by
      rw [hf_form, quarticCubicResolvent_depressed]
      unfold depressedQuarticResolvent
      simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero, map_zero, zero_mul,
        add_zero, map_neg]
      norm_num
    have hdisc_eq : garlingDiscriminant f = -2048 := by
      rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg, hg_eq]
      have hcub : (Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X : ℚ[X]) =
          Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X + Polynomial.C 0 := by simp
      rw [hcub, garlingDiscriminant_depressed_cubic]
      norm_num
    have hno_sq : ¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := by
      rw [hdisc_eq]
      rintro ⟨d, hd⟩
      linarith [sq_nonneg d]
    have hg_not_irr : ¬ Irreducible (quarticCubicResolvent f) := by
      rw [hg_eq]
      intro hirr_g
      have hfac : (Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X : ℚ[X]) =
          Polynomial.X * (Polynomial.X ^ 2 + Polynomial.C 8) := by ring
      have hnu1 : ¬ IsUnit (Polynomial.X : ℚ[X]) := Polynomial.not_isUnit_X
      have hnu2 : ¬ IsUnit (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]) := by
        intro hu
        have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have hd2 : (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]).natDegree = 2 := by compute_degree!
        omega
      rcases hirr_g.isUnit_or_isUnit hfac with h1 | h2
      · exact hnu1 h1
      · exact hnu2 h2
    have hg_not_sp : ¬ GarlingSplitsOver ℚ ℚ (quarticCubicResolvent f) := by
      rw [hg_eq, garlingSplitsOver_iff_splits, Algebra.algebraMap_self, Polynomial.map_id]
      intro hsp
      have hfac : (Polynomial.X ^ 3 + Polynomial.C 8 * Polynomial.X : ℚ[X]) =
          Polynomial.X * (Polynomial.X ^ 2 + Polynomial.C 8) := by ring
      rw [hfac] at hsp
      have hq_ne0 : (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]) ≠ 0 := by
        intro h0
        have hd := congrArg Polynomial.natDegree h0
        have hd2 : (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]).natDegree = 2 := by compute_degree!
        rw [hd2, Polynomial.natDegree_zero] at hd
        omega
      have hsp_q : (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]).Splits :=
        (Polynomial.splits_mul Polynomial.X_ne_zero hq_ne0).mp hsp |>.2
      obtain ⟨r, hr⟩ := Polynomial.Splits.exists_eval_eq_zero hsp_q (by
        rw [Polynomial.degree_eq_natDegree hq_ne0]
        have hd2 : (Polynomial.X ^ 2 + Polynomial.C 8 : ℚ[X]).natDegree = 2 := by compute_degree!
        rw [hd2]; decide)
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at hr
      linarith [sq_nonneg r]
    exact ⟨hf_irr, hf_deg, hg_eq, hdisc_eq, hno_sq, hg_not_irr, hg_not_sp⟩

/-- **Repaired Complete 5-Way Quartic Galois Group Classification for `Exercise 14.7`**
(§14.4, printed p. 117 / PDF p. 125; `BRIEF.md` Flag 3 & `QUEUE.md`):
Replacing the impossible `Splits over K` entry in Rows 4 and 5 of Garling's printed table by
`¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g` (equivalently `[M : K] = 2`), for **every** field `K`
with `char K ≠ 2, 3`, **every** irreducible quartic `f ∈ K[x]` (`f.natDegree = 4`), **every**
splitting field extension `L : K` of `f`, `g := quarticCubicResolvent f`, and **every**
`M : IntermediateField K L` with `IsGarlingSplittingFieldExtension K M g`:
1. The five repaired input conditions `C₁, C₂, C₃, C₄, C₅` are **exhaustive** and **pairwise
   mutually exclusive** (and `[M : K] = 2 ↔ ¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g`);
2. A root labelling `e : Fin 4 ≃ garlingRootSet K L f` exists, and for **every** such `e` (setting
   `G := (garlingRootLabellingPermHom e).range ≤ Σ₄`, with `Γ_K(f) ≃* G`), each `C_k` holds **if and
   only if** `G` falls into the corresponding transitive subgroup class, uniquely determining the
   isomorphism type and order of `Γ_K(f)` in all five cases (`Σ₄`, `A₄`, `viergruppe`, cyclic `C₄`,
   and dihedral `D₈` = `DihedralGroup 4`). -/
theorem exercise_14_7_repaired {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hchar2 : ringChar K ≠ 2) (_hchar3 : ringChar K ≠ 3)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = 4)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (M : IntermediateField K L)
    (hsf_M : IsGarlingSplittingFieldExtension K M (quarticCubicResolvent f)) :
    let Δ := garlingDiscriminant f
    let g := quarticCubicResolvent f
    let C₁ := (¬ ∃ d : K, d ^ 2 = Δ) ∧ Irreducible g
    let C₂ := (∃ d : K, d ^ 2 = Δ) ∧ Irreducible g
    let C₃ := (∃ d : K, d ^ 2 = Δ) ∧ GarlingSplitsOver K K g
    let C₄ := (¬ ∃ d : K, d ^ 2 = Δ) ∧ (¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g) ∧
      ¬ Irreducible (f.map (algebraMap K M))
    let C₅ := (¬ ∃ d : K, d ^ 2 = Δ) ∧ (¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g) ∧
      Irreducible (f.map (algebraMap K M))
    (C₁ ∨ C₂ ∨ C₃ ∨ C₄ ∨ C₅) ∧
    (¬ (C₁ ∧ C₂) ∧ ¬ (C₁ ∧ C₃) ∧ ¬ (C₁ ∧ C₄) ∧ ¬ (C₁ ∧ C₅) ∧
      ¬ (C₂ ∧ C₃) ∧ ¬ (C₂ ∧ C₄) ∧ ¬ (C₂ ∧ C₅) ∧
      ¬ (C₃ ∧ C₄) ∧ ¬ (C₃ ∧ C₅) ∧ ¬ (C₄ ∧ C₅)) ∧
    (Module.finrank K M = 2 ↔ ¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g) ∧
    Nonempty (Fin 4 ≃ garlingRootSet K L f) ∧
    ∀ e : Fin 4 ≃ garlingRootSet K L f,
      let G := (garlingRootLabellingPermHom e).range
      Nonempty (GarlingPolyGaloisGroup K L f ≃* G) ∧
      (C₁ ↔ G = ⊤) ∧
      (C₂ ↔ G = alternatingGroup (Fin 4)) ∧
      (C₃ ↔ G = viergruppe) ∧
      (C₄ ↔ IsCyclic G ∧ Nat.card G = 4) ∧
      (C₅ ↔ Nat.card G = 8) ∧
      (C₁ → Nat.card (GarlingPolyGaloisGroup K L f) = 24 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* SigmaN 4)) ∧
      (C₂ → Nat.card (GarlingPolyGaloisGroup K L f) = 12 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* alternatingGroup (Fin 4))) ∧
      (C₃ → Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* viergruppe)) ∧
      (C₄ → IsCyclic (GarlingPolyGaloisGroup K L f) ∧
        Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* Multiplicative (ZMod 4))) ∧
      (C₅ → Nat.card (GarlingPolyGaloisGroup K L f) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* DihedralGroup 4)) := by
  intro Δ g C₁ C₂ C₃ C₄ C₅
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h4K : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2K
  have hf0 : f ≠ 0 := hirr.ne_zero
  obtain ⟨hsep, _, hΔ0⟩ :=
    irreducible_separable_of_natDegree_cast_ne_zero hirr (by rw [hdeg]; exact_mod_cast h4K)
  -- Existence of `e₀ : Fin 4 ≃ garlingRootSet K L f`:
  have hcard_roots : (garlingRootSet K L f).ncard = 4 :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsf).trans hdeg
  have hfin_roots : (garlingRootSet K L f).Finite := by
    by_contra hinf
    rw [Set.Infinite.ncard hinf] at hcard_roots
    omega
  have _ : Fintype (garlingRootSet K L f) := hfin_roots.fintype
  have hfintype_card : Fintype.card (garlingRootSet K L f) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_roots
  let e₀ : Fin 4 ≃ garlingRootSet K L f := (Fintype.equivFinOfCardEq hfintype_card).symm
  -- Degree characterizations of `g` via `M`:
  have hg_mon : g.Monic := quarticCubicResolvent_monic f
  have hg_deg : g.natDegree = 3 := quarticCubicResolvent_natDegree f
  have _ : FiniteDimensional K M :=
    (isFiniteExtension_iff_moduleFinite K M).mp (corollary_to_theorem_7_1 hsf_M).1
  have hM_pos : 1 ≤ Module.finrank K M := Module.finrank_pos
  -- (A) `GarlingSplitsOver K K g ↔ Module.finrank K M = 1`
  have hsp_iff_fin1 : GarlingSplitsOver K K g ↔ Module.finrank K M = 1 := by
    constructor
    · intro hsp_K
      have hM_bot : M = ⊥ :=
        ((exercise_14_7_printed_rows_4_5_impossible.1 hchar2 hirr hdeg hsf M hsf_M).1 hsp_K).2.1
      rw [hM_bot]
      exact IntermediateField.finrank_bot
    · intro hfin1
      have hbot_top : (⊥ : IntermediateField K M) = ⊤ :=
        (IntermediateField.finrank_eq_one_iff.mp
          (IntermediateField.topEquiv.toLinearEquiv.finrank_eq.trans hfin1)).symm
      obtain ⟨m_M, c_M, ρ_M, hexp_M⟩ := hsf_M.1
      have hm_M3 : m_M = 3 :=
        ((garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).2.2.1).trans hg_deg
      have hc_M1 : c_M = 1 :=
        (garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).1.trans hg_mon.leadingCoeff
      subst hm_M3 hc_M1
      have hρ_in_bot : ∀ i : Fin 3, ∃ k : K, algebraMap K M k = ρ_M i := by
        intro i
        have hi : ρ_M i ∈ (⊥ : IntermediateField K M) := hbot_top.symm ▸ IntermediateField.mem_top
        exact IntermediateField.mem_bot.mp hi
      choose ρ_K hρ_K using hρ_in_bot
      refine ⟨3, 1, ρ_K, ?_⟩
      unfold GarlingSplitsExplicit at hexp_M ⊢
      apply Polynomial.map_injective (algebraMap K M) (algebraMap K M).injective
      rw [Polynomial.map_map, show (algebraMap K M).comp (algebraMap K K) = algebraMap K M from rfl,
        hexp_M, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
      simp only [map_one, one_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact Finset.prod_congr rfl fun i _ => by rw [hρ_K i]
  -- (B) `Irreducible g ↔ 3 ≤ Module.finrank K M`
  have hirr_iff_ge3 : Irreducible g ↔ 3 ≤ Module.finrank K M := by
    obtain ⟨m_M, c_M, ρ_M, hexp_M⟩ := hsf_M.1
    have hm_M3 : m_M = 3 :=
      ((garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).2.2.1).trans hg_deg
    have hc_M1 : c_M = 1 :=
      (garlingSplitsExplicit_props hg_mon.ne_zero hexp_M).1.trans hg_mon.leadingCoeff
    subst hm_M3 hc_M1
    constructor
    · intro hirr_g
      have haev0 : Polynomial.aeval (ρ_M 0) g = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp_M, Polynomial.eval_mul,
          Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ 0) (by simp))
      have hmin0 : minpoly K (ρ_M 0) = g :=
        (minpoly.eq_of_irreducible_of_monic hirr_g haev0 hg_mon).symm
      have hfin_adj : Module.finrank K (IntermediateField.adjoin K ({ρ_M 0} : Set M)) = 3 := by
        rw [IntermediateField.adjoin.finrank ⟨g, hg_mon, haev0⟩, hmin0, hg_deg]
      have hdvd := Module.finrank_mul_finrank K (IntermediateField.adjoin K ({ρ_M 0} : Set M)) M
      rw [hfin_adj] at hdvd
      have hpos_top : 0 < Module.finrank K M := by omega
      omega
    · intro hge3
      by_contra hred
      -- Monic degree-`3` reducible `g` has a root `r₀ ∈ K`!
      have hex_root_K : ∃ r₀ : K, g.eval r₀ = 0 := by
        rw [irreducible_iff] at hred
        push Not at hred
        have hnot_u : ¬ IsUnit g := fun hu => by
          have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
        obtain ⟨u, v, huv, hnu, hnv⟩ := hred hnot_u
        have hu0 : u ≠ 0 := fun h0 => hg_mon.ne_zero (by rw [huv, h0, zero_mul])
        have hv0 : v ≠ 0 := fun h0 => hg_mon.ne_zero (by rw [huv, h0, mul_zero])
        have hdu_pos : 0 < u.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_ne_zero_of_nonunit hu0 hnu)
        have hdv_pos : 0 < v.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_ne_zero_of_nonunit hv0 hnv)
        have hd_sum : u.natDegree + v.natDegree = 3 := by
          rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hg_deg]
        have hlin_eval : ∀ w : K[X], w.natDegree = 1 → ∃ r₀ : K, w.eval r₀ = 0 := by
          intro w hw1
          have hw_eq : w = Polynomial.C (w.coeff 1) * Polynomial.X + Polynomial.C (w.coeff 0) :=
            Polynomial.eq_X_add_C_of_natDegree_le_one hw1.le
          have hc1_ne : w.coeff 1 ≠ 0 := by
            rw [← hw1, ← Polynomial.leadingCoeff]
            exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; rw [h0] at hw1; simp at hw1)
          let r₀ : K := -w.coeff 0 / w.coeff 1
          refine ⟨r₀, ?_⟩
          rw [hw_eq]
          dsimp [r₀]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          field_simp [hc1_ne]; ring
        have hcases : u.natDegree = 1 ∨ v.natDegree = 1 := by omega
        rcases hcases with hu1 | hv1
        · obtain ⟨r₀, hr₀⟩ := hlin_eval u hu1
          exact ⟨r₀, by rw [huv, Polynomial.eval_mul, hr₀, zero_mul]⟩
        · obtain ⟨r₀, hr₀⟩ := hlin_eval v hv1
          exact ⟨r₀, by rw [huv, Polynomial.eval_mul, hr₀, mul_zero]⟩
      obtain ⟨r₀, hr₀⟩ := hex_root_K
      -- Factor `g = (X - C r₀) * q_g` in `K[X]` where `q_g` is monic of degree `2`:
      have hdvd_lin : (Polynomial.X - Polynomial.C r₀) ∣ g := Polynomial.dvd_iff_isRoot.mpr hr₀
      obtain ⟨q_g, hq_g⟩ := hdvd_lin
      have hlin_mon : (Polynomial.X - Polynomial.C r₀).Monic := Polynomial.monic_X_sub_C r₀
      have hqg_mon : q_g.Monic := by
        have hm := hg_mon
        rw [hq_g] at hm
        exact hlin_mon.of_mul_monic_left hm
      have hqg_deg : q_g.natDegree = 2 := by
        have hd := hg_deg
        rw [hq_g, Polynomial.natDegree_mul hlin_mon.ne_zero hqg_mon.ne_zero,
          Polynomial.natDegree_X_sub_C] at hd
        omega
      -- In `M[X]`, `q_g.map (algebraMap K M)` splits into two linear factors `(X - β₁)(X - β₂)`!
      have hsp_M : (g.map (algebraMap K M)).Splits :=
        (garlingSplitsOver_iff_splits K M g).mp ⟨3, 1, ρ_M, hexp_M⟩
      rw [hq_g, Polynomial.map_mul] at hsp_M
      have hsp_qg : (q_g.map (algebraMap K M)).Splits :=
        (Polynomial.splits_mul (hlin_mon.map _).ne_zero (hqg_mon.map _).ne_zero).mp hsp_M |>.2
      obtain ⟨m_q, c_q, τ_q, hexp_q⟩ := (garlingSplitsOver_iff_splits K M q_g).mpr hsp_qg
      have hm_q2 : m_q = 2 :=
        ((garlingSplitsExplicit_props hqg_mon.ne_zero hexp_q).2.2.1).trans hqg_deg
      have hc_q1 : c_q = 1 :=
        (garlingSplitsExplicit_props hqg_mon.ne_zero hexp_q).1.trans hqg_mon.leadingCoeff
      subst hm_q2 hc_q1
      -- Notice `τ_q 0 + τ_q 1 = -q_g.coeff 1 ∈ K`, so `K⟮τ_q 0⟯` contains `τ_q 0`, `τ_q 1`, AND `r₀`,
      -- hence `g` splits over `K⟮τ_q 0⟯`, forcing `K⟮τ_q 0⟯ = ⊤` and `[M : K] ≤ 2`!
      let F_q : IntermediateField K M := IntermediateField.adjoin K ({τ_q 0} : Set M)
      have hsum_τ : τ_q 0 + τ_q 1 = -algebraMap K M (q_g.coeff 1) := by
        have hq_exp : q_g.map (algebraMap K M) =
            Polynomial.X ^ 2 - Polynomial.C (τ_q 0 + τ_q 1) * Polynomial.X +
              Polynomial.C (τ_q 0 * τ_q 1) := by
          have heq := hexp_q
          unfold GarlingSplitsExplicit at heq
          rw [Fin.prod_univ_two, map_one, map_one, one_mul] at heq
          rw [heq]
          simp only [map_add, map_mul]
          ring
        have hc1 := congrArg (fun P : M[X] => P.coeff 1) hq_exp
        simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
          Polynomial.coeff_C] at hc1
        norm_num at hc1
        linear_combination hc1
      have hτ0_Fq : τ_q 0 ∈ F_q := IntermediateField.mem_adjoin_simple_self K (τ_q 0)
      have hτ1_Fq : τ_q 1 ∈ F_q := by
        have h : τ_q 1 = -algebraMap K M (q_g.coeff 1) - τ_q 0 := by linear_combination hsum_τ
        rw [h]
        exact F_q.sub_mem (F_q.neg_mem (F_q.algebraMap_mem _)) hτ0_Fq
      have hr0_Fq : algebraMap K M r₀ ∈ F_q := F_q.algebraMap_mem r₀
      have hFq_top : F_q = ⊤ := by
        by_contra hne
        let ν : Fin 3 → M := ![algebraMap K M r₀, τ_q 0, τ_q 1]
        have hexp_ν : GarlingSplitsExplicit K M g 3 1 ν := by
          unfold GarlingSplitsExplicit
          rw [hq_g, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
            hexp_q, Fin.prod_univ_two, Fin.prod_univ_three]
          have v0 : ν 0 = algebraMap K M r₀ := rfl
          have v1 : ν 1 = τ_q 0 := rfl
          have v2 : ν 2 = τ_q 1 := rfl
          rw [v0, v1, v2]
          simp [mul_assoc]
        have hν_mem : ∀ i : Fin 3, ν i ∈ F_q := by
          intro i; fin_cases i
          · exact hr0_Fq
          · exact hτ0_Fq
          · exact hτ1_Fq
        exact hsf_M.2 F_q hne ⟨3, 1, _, garlingSplitsExplicit_of_mem_intermediateField F_q hexp_ν hν_mem⟩
      have haev_τ0 : Polynomial.aeval (τ_q 0) q_g = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp_q, Polynomial.eval_mul,
          Polynomial.eval_prod]
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ 0) (by simp))
      have hdvd_min := minpoly.dvd K (τ_q 0) haev_τ0
      have hdeg_le2 : (minpoly K (τ_q 0)).natDegree ≤ 2 :=
        (Polynomial.natDegree_le_of_dvd hdvd_min hqg_mon.ne_zero).trans_eq hqg_deg
      have hfin_Fq : Module.finrank K F_q ≤ 2 := by
        dsimp [F_q]
        rw [IntermediateField.adjoin.finrank ⟨q_g, hqg_mon, haev_τ0⟩]
        exact hdeg_le2
      have hfin_M_eq : Module.finrank K M = Module.finrank K F_q := by
        rw [hFq_top]
        exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq.symm
      omega
  have hfin2_iff : Module.finrank K M = 2 ↔ ¬ Irreducible g ∧ ¬ GarlingSplitsOver K K g := by
    rw [hirr_iff_ge3, hsp_iff_fin1]
    omega
  have hmut_C :
      ¬ (C₁ ∧ C₂) ∧ ¬ (C₁ ∧ C₃) ∧ ¬ (C₁ ∧ C₄) ∧ ¬ (C₁ ∧ C₅) ∧
      ¬ (C₂ ∧ C₃) ∧ ¬ (C₂ ∧ C₄) ∧ ¬ (C₂ ∧ C₅) ∧
      ¬ (C₃ ∧ C₄) ∧ ¬ (C₃ ∧ C₅) ∧ ¬ (C₄ ∧ C₅) := by
    have hnot_irr_sp : ¬ (Irreducible g ∧ GarlingSplitsOver K K g) := by
      rw [hirr_iff_ge3, hsp_iff_fin1]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩; exact h1 h2
    · rintro ⟨⟨_, hi⟩, ⟨_, hs⟩⟩; exact hnot_irr_sp ⟨hi, hs⟩
    · rintro ⟨⟨_, hi⟩, ⟨_, ⟨hni, _⟩, _⟩⟩; exact hni hi
    · rintro ⟨⟨_, hi⟩, ⟨_, ⟨hni, _⟩, _⟩⟩; exact hni hi
    · rintro ⟨⟨_, hi⟩, ⟨_, hs⟩⟩; exact hnot_irr_sp ⟨hi, hs⟩
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩; exact h2 h1
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩; exact h2 h1
    · rintro ⟨⟨_, hs⟩, ⟨_, ⟨_, hns⟩, _⟩⟩; exact hns hs
    · rintro ⟨⟨_, hs⟩, ⟨_, ⟨_, hns⟩, _⟩⟩; exact hns hs
    · rintro ⟨⟨_, _, hnf⟩, ⟨_, _, hf⟩⟩; exact hnf hf
  -- Core per-labelling classification:
  have hper_e : ∀ e : Fin 4 ≃ garlingRootSet K L f,
      let G := (garlingRootLabellingPermHom e).range
      Nonempty (GarlingPolyGaloisGroup K L f ≃* G) ∧
      (C₁ ∨ C₂ ∨ C₃ ∨ C₄ ∨ C₅) ∧
      (C₁ ↔ G = ⊤) ∧
      (C₂ ↔ G = alternatingGroup (Fin 4)) ∧
      (C₃ ↔ G = viergruppe) ∧
      (C₄ ↔ IsCyclic G ∧ Nat.card G = 4) ∧
      (C₅ ↔ Nat.card G = 8) ∧
      (C₁ → Nat.card (GarlingPolyGaloisGroup K L f) = 24 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* SigmaN 4)) ∧
      (C₂ → Nat.card (GarlingPolyGaloisGroup K L f) = 12 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* alternatingGroup (Fin 4))) ∧
      (C₃ → Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* viergruppe)) ∧
      (C₄ → IsCyclic (GarlingPolyGaloisGroup K L f) ∧
        Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* Multiplicative (ZMod 4))) ∧
      (C₅ → Nat.card (GarlingPolyGaloisGroup K L f) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* DihedralGroup 4)) := by
    intro e
    let φ := garlingRootLabellingPermHom e
    let G := φ.range
    have hgar_sep : IsGarlingSeparablePoly f :=
      ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep).2.2
    have ⟨hfinL, hnormL⟩ := (corollary_1_to_theorem_9_1_iff K L).mpr ⟨f, hsf⟩
    have hsepL : IsGarlingSeparableExtension K L :=
      (isGarlingSeparableExtension_iff_poly_of_splittingField hf0 hsf).mpr hgar_sep
    have hgal : IsGarlingGaloisExtension K L := ⟨hfinL, hnormL, hsepL⟩
    have _ : IsGalois K L := ((isGarlingGaloisExtension_iff K L).mp hgal).2
    have _ : FiniteDimensional K L := (isFiniteExtension_iff_moduleFinite K L).mp hgal.1
    -- Subfield identification `M = M₀` and injectivity of `φ` (`GarlingPolyGaloisGroup K L f ≃* G`):
    obtain ⟨_, huniq_M, hfin_M₀_L, hfin_prod, hφ_inj⟩ :=
      section_14_4_resolvent_splitting_subfield hchar2 hdeg hsep hsf e
    let eG : GarlingPolyGaloisGroup K L f ≃* G :=
      MulEquiv.ofBijective φ.rangeRestrict
        ⟨fun a b hab => hφ_inj (congrArg Subtype.val hab), φ.rangeRestrict_surjective⟩
    have htr_G : SubgroupActsTransitively G := by
      have htr_root := irreducible_imp_galoisGroup_actsTransitively hirr hsf
      intro i j
      obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := htr_root (e i) (e j)
      refine ⟨φ σ, ⟨σ, rfl⟩, ?_⟩
      dsimp [φ, garlingRootLabellingPermHom]
      rw [hσ, e.symm_apply_apply]
    have hM_eq_M₀ : M = IntermediateField.fixedField (viergruppe.comap φ) := huniq_M M hsf_M
    have hfin_ML : Module.finrank M L = Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) := by
      rw [hM_eq_M₀]; exact hfin_M₀_L
    have hprod_MK : Module.finrank K M * Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) =
        Nat.card G := by
      rw [hM_eq_M₀]; exact hfin_prod
    -- Discriminant criterion (`Theorem 14.1`): `(∃ d : K, d ^ 2 = Δ) ↔ G ≤ alternatingGroup (Fin 4)`
    let e_deg : Fin f.natDegree ≃ garlingRootSet K L f := (finCongr hdeg).trans e
    have hG_le_A4_iff : (∃ d : K, d ^ 2 = Δ) ↔ G ≤ alternatingGroup (Fin 4) := by
      have ht := theorem_14_1 hchar2 f hsf
      constructor
      · intro hsq
        have hall := (ht.2.1 hΔ0 hsq).2 e_deg
        rintro _ ⟨σ, rfl⟩
        have hmem := hall σ
        rw [Equiv.Perm.mem_alternatingGroup] at hmem
        rw [Equiv.Perm.mem_alternatingGroup]
        have heq_p : garlingRootLabellingPermHom e_deg σ =
            (finCongr hdeg).symm.permCongr (φ σ) := by ext i; rfl
        rw [heq_p, Equiv.Perm.sign_permCongr] at hmem
        exact hmem
      · intro hle
        by_contra hno
        obtain ⟨_, _, _, _, hnotA⟩ := ht.2.2 hno
        apply (hnotA e_deg).1
        intro σ
        rw [Equiv.Perm.mem_alternatingGroup]
        have heq_p : garlingRootLabellingPermHom e_deg σ =
            (finCongr hdeg).symm.permCongr (φ σ) := by ext i; rfl
        rw [heq_p, Equiv.Perm.sign_permCongr]
        exact Equiv.Perm.mem_alternatingGroup.mp (hle ⟨σ, rfl⟩)
    -- Prove the 5 forward implications `G_k → C_k`:
    have himp1 : G = ⊤ → C₁ := by
      intro hG
      have hnotA : ¬ G ≤ alternatingGroup (Fin 4) := by
        rw [hG]
        intro hle
        have hswap : Equiv.swap (0 : Fin 4) 1 ∈ alternatingGroup (Fin 4) :=
          hle (Subgroup.mem_top _)
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hswap
        norm_num at hswap
      have hno_sq : ¬ ∃ d : K, d ^ 2 = Δ := fun hsq => hnotA (hG_le_A4_iff.mp hsq)
      have hcG : Nat.card G = 24 := by rw [hG]; exact exercise_11_5_s4.1 4
      have hcInf : Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 4 := by
        rw [hG, top_inf_eq]; exact natCard_viergruppe
      have hfinM : Module.finrank K M = 6 := by rw [hcG, hcInf] at hprod_MK; omega
      exact ⟨hno_sq, hirr_iff_ge3.mpr (by omega)⟩
    have himp2 : G = alternatingGroup (Fin 4) → C₂ := by
      intro hG
      have hsq : ∃ d : K, d ^ 2 = Δ := hG_le_A4_iff.mpr (by rw [hG])
      have hcG : Nat.card G = 12 := by rw [hG]; exact exercise_11_5_s4.1 3
      have hcInf : Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 4 := by
        rw [hG, inf_of_le_right viergruppe_le_alternatingGroup]; exact natCard_viergruppe
      have hfinM : Module.finrank K M = 3 := by rw [hcG, hcInf] at hprod_MK; omega
      exact ⟨hsq, hirr_iff_ge3.mpr (by omega)⟩
    have himp3 : G = viergruppe → C₃ := by
      intro hG
      have hsq : ∃ d : K, d ^ 2 = Δ :=
        hG_le_A4_iff.mpr (by rw [hG]; exact viergruppe_le_alternatingGroup)
      have hcG : Nat.card G = 4 := by rw [hG]; exact natCard_viergruppe
      have hcInf : Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 4 := by
        rw [hG, inf_idem]; exact natCard_viergruppe
      have hfinM : Module.finrank K M = 1 := by rw [hcG, hcInf] at hprod_MK; omega
      exact ⟨hsq, hsp_iff_fin1.mpr hfinM⟩
    have himp4 : IsCyclic G ∧ Nat.card G = 4 → C₄ := by
      rintro ⟨hcyc, hcG⟩
      -- Since `G` is transitive, cyclic, of order `4`, `G` is conjugate to `s4C4 = s4TransitiveModel 1`!
      obtain ⟨i_m, hi_conj⟩ := (exercise_11_5_s4.2.2.1 G).mp htr_G
      have hi1 : i_m = 1 := by
        have hc_i : (![4, 4, 8, 12, 24] : Fin 5 → ℕ) i_m = 4 :=
          (exercise_11_5_s4.1 i_m).symm.trans ((isConjugateSubgroup_natCard_eq hi_conj).trans hcG)
        fin_cases i_m
        · exfalso
          obtain ⟨g_c, hg_c⟩ := hi_conj
          have hGV : G = viergruppe := by
            rw [← hg_c]
            change s4V4.map (MulAut.conj g_c).toMonoidHom = viergruppe
            rw [← viergruppe_eq_s4V4]
            ext x
            simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            exact ⟨by rintro ⟨y, hy, rfl⟩; exact viergruppe_normal.conj_mem y hy g_c,
              fun hx => ⟨g_c⁻¹ * x * g_c, viergruppe_normal.conj_mem x hx g_c⁻¹, by group⟩⟩
          exact (exercise_14_6_mutually_exclusive G).2.2.2.2.2.2.2.1 ⟨hGV, hcyc, hcG⟩
        · rfl
        · norm_num at hc_i
        · norm_num at hc_i
        · norm_num at hc_i
      subst hi1
      obtain ⟨g_c, hg_c⟩ := hi_conj
      have hnotA : ¬ G ≤ alternatingGroup (Fin 4) := by
        intro hle
        have hrot_in_G : g_c * finRotate 4 * g_c⁻¹ ∈ G := by
          rw [← hg_c]
          exact ⟨finRotate 4, Subgroup.mem_zpowers _, rfl⟩
        have hmemA := Equiv.Perm.mem_alternatingGroup.mp (hle hrot_in_G)
        have hnormA : (alternatingGroup (Fin 4)).Normal := inferInstance
        have hrot_A : finRotate 4 ∈ alternatingGroup (Fin 4) := by
          have h := hnormA.conj_mem _ (hle hrot_in_G) g_c⁻¹
          simpa [mul_assoc] using h
        rw [Equiv.Perm.mem_alternatingGroup] at hrot_A
        have hrot_false : (Equiv.Perm.sign (finRotate 4) == 1) = false := by decide
        have hrot_true : (Equiv.Perm.sign (finRotate 4) == 1) = true := beq_iff_eq.mpr hrot_A
        rw [hrot_false] at hrot_true
        cases hrot_true
      have hno_sq : ¬ ∃ d : K, d ^ 2 = Δ := fun hsq => hnotA (hG_le_A4_iff.mp hsq)
      have hcInf : Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 2 := by
        have hinf_eq : G ⊓ viergruppe =
            (s4C4 ⊓ viergruppe).map (MulAut.conj g_c).toMonoidHom := by
          rw [← hg_c]
          ext x
          simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact ⟨by
              rintro ⟨⟨y, hy, rfl⟩, hxV⟩
              exact ⟨y, ⟨hy, by simpa [mul_assoc] using viergruppe_normal.conj_mem _ hxV g_c⁻¹⟩, rfl⟩,
            by rintro ⟨y, ⟨hyC, hyV⟩, rfl⟩; exact ⟨⟨y, hyC, rfl⟩, viergruppe_normal.conj_mem y hyV g_c⟩⟩
        rw [hinf_eq, ← isConjugateSubgroup_natCard_eq ⟨g_c, rfl⟩]
        exact natCard_s4TransitiveModel_inf_viergruppe 1
      have hfinM : Module.finrank K M = 2 := by rw [hcG, hcInf] at hprod_MK; omega
      have hfinML2 : Module.finrank M L = 2 := hfin_ML.trans hcInf
      -- If `f_M := f.map (algebraMap K M)` were irreducible in `M[X]`, then `4 ∣ [L : M] = 2`, impossible!
      have hnot_irr_fM : ¬ Irreducible (f.map (algebraMap K M)) := by
        intro hirr_fM
        let f_M : M[X] := f.map (algebraMap K M)
        have hfM_deg : f_M.natDegree = 4 := (Polynomial.natDegree_map (algebraMap K M)).trans hdeg
        have hlc_M : f_M.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; rw [h0] at hfM_deg; simp at hfM_deg)
        let f_M_mon : M[X] := Polynomial.C f_M.leadingCoeff⁻¹ * f_M
        have hfM_mon_mon : f_M_mon.Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            inv_mul_cancel₀ hlc_M]
        have hfM_mon_deg : f_M_mon.natDegree = 4 := by
          dsimp [f_M_mon]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_M), hfM_deg]
        let u_lc : (M[X])ˣ :=
          Units.map Polynomial.C.toMonoidHom (Units.mk0 f_M.leadingCoeff⁻¹ (inv_ne_zero hlc_M))
        have hfM_mon_irr : Irreducible f_M_mon :=
          (Associated.irreducible_iff ⟨u_lc, by dsimp [f_M_mon, f_M, u_lc]; simp [mul_comm]⟩).mp hirr_fM
        let α₀ : L := (e 0 : L)
        have haev_α₀ : Polynomial.aeval α₀ f_M_mon = 0 := by
          have haev_K : Polynomial.aeval α₀ f = 0 := (mem_garlingRootSet_iff.mp (e 0).2)
          dsimp [f_M_mon, f_M]
          rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_map_algebraMap, haev_K, mul_zero]
        have hmin_α₀ : minpoly M α₀ = f_M_mon :=
          (minpoly.eq_of_irreducible_of_monic hfM_mon_irr haev_α₀ hfM_mon_mon).symm
        have hfin_adj4 : Module.finrank M (IntermediateField.adjoin M ({α₀} : Set L)) = 4 := by
          rw [IntermediateField.adjoin.finrank ⟨f_M_mon, hfM_mon_mon, haev_α₀⟩, hmin_α₀, hfM_mon_deg]
        have hdvd := Module.finrank_mul_finrank M (IntermediateField.adjoin M ({α₀} : Set L)) L
        rw [hfin_adj4, hfinML2] at hdvd
        omega
      exact ⟨hno_sq, hfin2_iff.mp hfinM, hnot_irr_fM⟩
    have himp5 : Nat.card G = 8 → C₅ := by
      intro hcG
      have hnotA : ¬ G ≤ alternatingGroup (Fin 4) := by
        intro hle
        have hdvd := Subgroup.card_dvd_of_le hle
        rw [hcG] at hdvd
        change 8 ∣ Nat.card (s4TransitiveModel 3) at hdvd
        rw [exercise_11_5_s4.1 3] at hdvd
        norm_num at hdvd
      have hno_sq : ¬ ∃ d : K, d ^ 2 = Δ := fun hsq => hnotA (hG_le_A4_iff.mp hsq)
      obtain ⟨⟨g_c, hg_c⟩, _⟩ := s4_subgroup_card_eight_conj_d4 G hcG
      have hV_le_G : viergruppe ≤ G := by
        rw [← hg_c]
        intro x hx
        refine ⟨g_c⁻¹ * x * g_c, viergruppe_le_s4D4 (viergruppe_normal.conj_mem x hx g_c⁻¹), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hcInf : Nat.card (G ⊓ viergruppe : Subgroup (SigmaN 4)) = 4 := by
        rw [inf_of_le_right hV_le_G]; exact natCard_viergruppe
      have hfinM : Module.finrank K M = 2 := by rw [hcG, hcInf] at hprod_MK; omega
      -- Show `f.map (algebraMap K M)` is irreducible over `M` because `viergruppe` acts transitively on the 4 roots!
      have hirr_fM : Irreducible (f.map (algebraMap K M)) := by
        let f_M : M[X] := f.map (algebraMap K M)
        have hfM_deg : f_M.natDegree = 4 := (Polynomial.natDegree_map (algebraMap K M)).trans hdeg
        have hfM0 : f_M ≠ 0 := by intro h0; rw [h0] at hfM_deg; simp at hfM_deg
        -- Explicit 4 distinct roots `r_f i := (e i : L)` of `f_M` in `L`:
        let r_f : Fin 4 → L := fun i => (e i : L)
        have hr_inj : Function.Injective r_f := fun i j hij => e.injective (Subtype.ext hij)
        obtain ⟨m_s, c_s, ρ_s, hexp_f⟩ := hsf.1
        have hm_s4 : m_s = 4 := ((garlingSplitsExplicit_props hf0 hexp_f).2.2.1).trans hdeg
        have hc_s : c_s = f.leadingCoeff := (garlingSplitsExplicit_props hf0 hexp_f).1
        subst hm_s4 hc_s
        have hρ_inj : Function.Injective ρ_s :=
          (injective_roots_iff_separable_and_not_repeated hf0 hexp_f).1.mpr hsep
        have hmem_rf : ∀ i : Fin 4, ρ_s i ∈ garlingRootSet K L f := by
          intro i
          rw [mem_garlingRootSet_iff, Polynomial.aeval_def, ← Polynomial.eval_map,
            hexp_f, Polynomial.eval_mul, Polynomial.eval_prod]
          exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
        let τ_fun : Fin 4 → Fin 4 := fun i => e.symm ⟨ρ_s i, hmem_rf i⟩
        have hτ_inj : Function.Injective τ_fun := fun i j hij =>
          hρ_inj (congrArg Subtype.val (e.symm.injective hij))
        let τ_rf : SigmaN 4 := Equiv.ofBijective τ_fun ⟨hτ_inj, Finite.injective_iff_surjective.mp hτ_inj⟩
        have hτ_rf : ∀ i : Fin 4, ρ_s i = r_f (τ_rf i) := fun i => by
          change ρ_s i = (e (e.symm ⟨ρ_s i, hmem_rf i⟩) : L)
          rw [e.apply_symm_apply]
        have hfM_map_L : f_M.map (algebraMap M L) =
            Polynomial.C (algebraMap K L f.leadingCoeff) *
              ∏ i : Fin 4, (Polynomial.X - Polynomial.C (r_f i)) := by
          dsimp [f_M]
          rw [Polynomial.map_map, show (algebraMap M L).comp (algebraMap K M) = algebraMap K L from rfl]
          unfold GarlingSplitsExplicit at hexp_f
          rw [hexp_f]
          congr 1
          simp_rw [hτ_rf]
          exact Fintype.prod_equiv τ_rf
            (fun i => Polynomial.X - Polynomial.C (r_f (τ_rf i)))
            (fun i => Polynomial.X - Polynomial.C (r_f i))
            (fun _ => rfl)
        -- For any `i, j : Fin 4`, since `viergruppe ≤ G`, there is `σ ∈ Γ_K(f)` fixing `M` pointwise
        -- with `σ (r_f i) = r_f j`!
        have hex_aut_M : ∀ i j : Fin 4, ∃ σ : GarlingPolyGaloisGroup K L f,
            (∀ m : M, σ m.1 = m.1) ∧ σ (r_f i) = r_f j := by
          intro i j
          obtain ⟨π, hπV, hπij⟩ := viergruppe_actsTransitively i j
          obtain ⟨σ, hφσ⟩ := hV_le_G hπV
          have hσ_in_H : σ ∈ viergruppe.comap φ := by
            change φ σ ∈ viergruppe; rwa [hφσ]
          have hfix_M : ∀ m : M, σ m.1 = m.1 := by
            intro ⟨x, hx⟩
            rw [hM_eq_M₀] at hx
            exact hx ⟨σ, hσ_in_H⟩
          have hσ_ij : σ (r_f i) = r_f j := by
            dsimp [r_f]
            rw [← garlingRootLabellingPermHom_apply e σ i]
            change (e (φ σ i) : L) = (e j : L)
            rw [hφσ, hπij]
          exact ⟨σ, hfix_M, hσ_ij⟩
        -- Prove `Irreducible f_M`:
        refine ⟨fun hu => ?_, fun u v huv => ?_⟩
        · change IsUnit f_M at hu
          have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
        · change f_M = u * v at huv
          by_contra hboth
          push Not at hboth
          rcases hboth with ⟨hnu, hnv⟩
          have hu0 : u ≠ 0 := fun h0 => hfM0 (by rw [huv, h0, zero_mul])
          have hv0 : v ≠ 0 := fun h0 => hfM0 (by rw [huv, h0, mul_zero])
          have hdu_pos : 0 < u.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_ne_zero_of_nonunit hu0 hnu)
          have hdv_pos : 0 < v.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
            (Polynomial.degree_pos_of_ne_zero_of_nonunit hv0 hnv)
          have hd_sum : u.natDegree + v.natDegree = 4 := by
            rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hfM_deg]
          -- `u.map (algebraMap M L)` divides `f_M.map (algebraMap M L)` and has positive degree `< 4`,
          -- so it has at least one root `r_f i₀`, hence by `hex_aut_M` has ALL 4 distinct roots `r_f 0..3`!
          have huL_deg : (u.map (algebraMap M L)).natDegree = u.natDegree :=
            Polynomial.natDegree_map (algebraMap M L)
          have huL0 : u.map (algebraMap M L) ≠ 0 := by
            intro h0; rw [h0, Polynomial.natDegree_zero] at huL_deg; omega
          have hsp_uL : (u.map (algebraMap M L)).Splits := by
            have hsp_fML : (f_M.map (algebraMap M L)).Splits := by
              rw [hfM_map_L]
              exact Polynomial.Splits.mul (Polynomial.Splits.C _)
                (Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _)
            rw [huv, Polynomial.map_mul] at hsp_fML
            have hvL0 : v.map (algebraMap M L) ≠ 0 := by
              intro h0
              have := Polynomial.natDegree_map (algebraMap M L) (p := v)
              rw [h0, Polynomial.natDegree_zero] at this; omega
            exact (Polynomial.splits_mul huL0 hvL0).mp hsp_fML |>.1
          obtain ⟨z, hz⟩ := Polynomial.Splits.exists_eval_eq_zero hsp_uL (by
            rw [Polynomial.degree_eq_natDegree huL0, huL_deg]
            exact (Nat.cast_pos.mpr hdu_pos).ne')
          have hz_fML : (f_M.map (algebraMap M L)).eval z = 0 := by
            rw [huv, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]
          rw [hfM_map_L, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hz_fML
          have hlc_L_ne0 : algebraMap K L f.leadingCoeff ≠ 0 :=
            (map_ne_zero (algebraMap K L)).mpr (Polynomial.leadingCoeff_ne_zero.mpr hf0)
          have hprod0 := (mul_eq_zero.mp hz_fML).resolve_left hlc_L_ne0
          rw [Finset.prod_eq_zero_iff] at hprod0
          obtain ⟨i₀, _, hi₀⟩ := hprod0
          simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi₀
          subst hi₀
          -- Now every `r_f j` (`j : Fin 4`) is a root of `u.map (algebraMap M L)`!
          have hall_roots : ∀ j : Fin 4, r_f j ∈ (u.map (algebraMap M L)).roots := by
            intro j
            rw [Polynomial.mem_roots huL0, Polynomial.IsRoot.def]
            obtain ⟨σ, hfix_M, hσ_ij⟩ := hex_aut_M i₀ j
            have hmap_σ : (u.map (algebraMap M L)).map σ.toRingHom = u.map (algebraMap M L) := by
              rw [Polynomial.map_map]
              congr 1
              ext m
              exact hfix_M m
            have hev2 : ((u.map (algebraMap M L)).map σ.toRingHom).eval (σ (r_f i₀)) =
                σ ((u.map (algebraMap M L)).eval (r_f i₀)) := by
              have hh := Polynomial.hom_eval₂ (u.map (algebraMap M L)) (RingHom.id L) σ.toRingHom (r_f i₀)
              simp only [RingHom.comp_id, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at hh
              exact hh.symm
            rw [hmap_σ, hσ_ij, hz, map_zero] at hev2
            exact hev2
          have hsub_multiset : (Finset.univ.image r_f).val ≤ (u.map (algebraMap M L)).roots := by
            rw [Finset.val_le_iff_val_subset]
            intro x hx
            rw [Finset.mem_val, Finset.mem_image] at hx
            obtain ⟨j, _, rfl⟩ := hx
            exact hall_roots j
          have hcard4 : (Finset.univ.image r_f).card = 4 := by
            rw [Finset.card_image_of_injective _ hr_inj, Finset.card_fin]
          have hle_deg : 4 ≤ u.natDegree := by
            calc 4 = (Finset.univ.image r_f).val.card := hcard4.symm
              _ ≤ (u.map (algebraMap M L)).roots.card := Multiset.card_le_card hsub_multiset
              _ ≤ (u.map (algebraMap M L)).natDegree := Polynomial.card_roots' _
              _ = u.natDegree := huL_deg
          omega
      exact ⟨hno_sq, hfin2_iff.mp hfinM, hirr_fM⟩
    -- Combine `(exercise_14_6 G).mp htr_G` with `himp1..himp5` + `hmut_C`!
    have h5G := (exercise_14_6 G).mp htr_G
    have hexh : C₁ ∨ C₂ ∨ C₃ ∨ C₄ ∨ C₅ := by
      rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
      · exact Or.inl (himp1 h1)
      · exact Or.inr (Or.inl (himp2 h2))
      · exact Or.inr (Or.inr (Or.inl (himp3 h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (himp4 h4))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (himp5 hc8))))
    have hiff1 : C₁ ↔ G = ⊤ :=
      ⟨fun hc => by
        rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
        · exact h1
        · exact absurd ⟨hc, himp2 h2⟩ hmut_C.1
        · exact absurd ⟨hc, himp3 h3⟩ hmut_C.2.1
        · exact absurd ⟨hc, himp4 h4⟩ hmut_C.2.2.1
        · exact absurd ⟨hc, himp5 hc8⟩ hmut_C.2.2.2.1, himp1⟩
    have hiff2 : C₂ ↔ G = alternatingGroup (Fin 4) :=
      ⟨fun hc => by
        rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
        · exact absurd ⟨himp1 h1, hc⟩ hmut_C.1
        · exact h2
        · exact absurd ⟨hc, himp3 h3⟩ hmut_C.2.2.2.2.1
        · exact absurd ⟨hc, himp4 h4⟩ hmut_C.2.2.2.2.2.1
        · exact absurd ⟨hc, himp5 hc8⟩ hmut_C.2.2.2.2.2.2.1, himp2⟩
    have hiff3 : C₃ ↔ G = viergruppe :=
      ⟨fun hc => by
        rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
        · exact absurd ⟨himp1 h1, hc⟩ hmut_C.2.1
        · exact absurd ⟨himp2 h2, hc⟩ hmut_C.2.2.2.2.1
        · exact h3
        · exact absurd ⟨hc, himp4 h4⟩ hmut_C.2.2.2.2.2.2.2.1
        · exact absurd ⟨hc, himp5 hc8⟩ hmut_C.2.2.2.2.2.2.2.2.1, himp3⟩
    have hiff4 : C₄ ↔ IsCyclic G ∧ Nat.card G = 4 :=
      ⟨fun hc => by
        rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
        · exact absurd ⟨himp1 h1, hc⟩ hmut_C.2.2.1
        · exact absurd ⟨himp2 h2, hc⟩ hmut_C.2.2.2.2.2.1
        · exact absurd ⟨himp3 h3, hc⟩ hmut_C.2.2.2.2.2.2.2.1
        · exact h4
        · exact absurd ⟨hc, himp5 hc8⟩ hmut_C.2.2.2.2.2.2.2.2.2, himp4⟩
    have hiff5 : C₅ ↔ Nat.card G = 8 :=
      ⟨fun hc => by
        rcases h5G with h1 | h2 | h3 | h4 | ⟨_, hc8, _⟩
        · exact absurd ⟨himp1 h1, hc⟩ hmut_C.2.2.2.1
        · exact absurd ⟨himp2 h2, hc⟩ hmut_C.2.2.2.2.2.2.1
        · exact absurd ⟨himp3 h3, hc⟩ hmut_C.2.2.2.2.2.2.2.2.1
        · exact absurd ⟨himp4 h4, hc⟩ hmut_C.2.2.2.2.2.2.2.2.2
        · exact hc8, himp5⟩
    have hgal1 : C₁ → Nat.card (GarlingPolyGaloisGroup K L f) = 24 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* SigmaN 4) := by
      intro hc
      have hG := hiff1.mp hc
      refine ⟨?_, ⟨eG.trans ((MulEquiv.subgroupCongr hG).trans Subgroup.topEquiv)⟩⟩
      rw [Nat.card_congr eG.toEquiv, hG]
      exact exercise_11_5_s4.1 4
    have hgal2 : C₂ → Nat.card (GarlingPolyGaloisGroup K L f) = 12 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* alternatingGroup (Fin 4)) := by
      intro hc
      have hG := hiff2.mp hc
      refine ⟨?_, ⟨eG.trans (MulEquiv.subgroupCongr hG)⟩⟩
      rw [Nat.card_congr eG.toEquiv, hG]
      exact exercise_11_5_s4.1 3
    have hgal3 : C₃ → Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* viergruppe) := by
      intro hc
      have hG := hiff3.mp hc
      refine ⟨?_, ⟨eG.trans (MulEquiv.subgroupCongr hG)⟩⟩
      rw [Nat.card_congr eG.toEquiv, hG]
      exact natCard_viergruppe
    have hgal4 : C₄ → IsCyclic (GarlingPolyGaloisGroup K L f) ∧
        Nat.card (GarlingPolyGaloisGroup K L f) = 4 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* Multiplicative (ZMod 4)) := by
      intro hc
      obtain ⟨hcycG, hc4⟩ := hiff4.mp hc
      have hcyc_Gal : IsCyclic (GarlingPolyGaloisGroup K L f) :=
        isCyclic_of_surjective eG.symm eG.symm.surjective
      have hcard_Gal : Nat.card (GarlingPolyGaloisGroup K L f) = 4 :=
        (Nat.card_congr eG.toEquiv).trans hc4
      obtain ⟨g0, hg0⟩ := hcyc_Gal.exists_generator
      have hzpow_top : Subgroup.zpowers g0 = ⊤ := by ext x; simp [hg0 x]
      have hord_g0 : orderOf g0 = 4 := by
        rw [← Nat.card_zpowers, hzpow_top, Subgroup.card_top, hcard_Gal]
      exact ⟨hcyc_Gal, hcard_Gal,
        mulEquivMultiplicativeZModOfOrderOfEqNatCard g0 hord_g0 hcard_Gal⟩
    have hgal5 : C₅ → Nat.card (GarlingPolyGaloisGroup K L f) = 8 ∧
        Nonempty (GarlingPolyGaloisGroup K L f ≃* DihedralGroup 4) := by
      intro hc
      have hc8 := hiff5.mp hc
      obtain ⟨_, ⟨eD4⟩⟩ := s4_subgroup_card_eight_conj_d4 G hc8
      exact ⟨(Nat.card_congr eG.toEquiv).trans hc8, ⟨eG.trans eD4⟩⟩
    exact ⟨⟨eG⟩, hexh, hiff1, hiff2, hiff3, hiff4, hiff5, hgal1, hgal2, hgal3, hgal4, hgal5⟩
  exact ⟨(hper_e e₀).2.1, hmut_C, hfin2_iff, ⟨e₀⟩, fun e =>
    ⟨(hper_e e).1, (hper_e e).2.2⟩⟩

/-! ### Exercise 14.8: Galois Groups of Five Concrete Quartics over `ℚ` (§14.4, p. 117; `QUEUE.md`) -/

/-- Rational-root test for monic integer polynomials: if `pZ ∈ ℤ[x]` is monic and has no integer
root `r ∈ ℤ`, then `pZ.map (algebraMap ℤ ℚ)` has no rational root `x ∈ ℚ`. -/
theorem rat_eval_ne_zero_of_monic_int_eval_ne_zero {pZ : ℤ[X]} (hmon : pZ.Monic)
    (hno_int : ∀ r : ℤ, pZ.eval r ≠ 0) (x : ℚ) :
    (pZ.map (algebraMap ℤ ℚ)).eval x ≠ 0 := by
  intro hev0
  let k := pZ.natDegree
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · have hp1 : pZ = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hk0
    rw [hp1, Polynomial.map_one, Polynomial.eval_one] at hev0
    exact one_ne_zero hev0
  · let n : ℤ := x.num
    let d : ℤ := x.den
    have hd_pos : 0 < x.den := x.pos
    have hd_ne0_Q : (d : ℚ) ≠ 0 := by dsimp [d]; exact_mod_cast x.den_nz
    have hx_eq : x = (n : ℚ) / (d : ℚ) := (Rat.num_div_den x).symm
    have hp_sum : pZ =
        (∑ i ∈ Finset.range k, Polynomial.C (pZ.coeff i) * Polynomial.X ^ i) +
          Polynomial.X ^ k := by
      have h1 := pZ.as_sum_range' (k + 1) (Nat.lt_succ_self k)
      rw [Finset.sum_range_succ] at h1
      have hck : pZ.coeff k = 1 := hmon.coeff_natDegree
      simpa only [ ← Polynomial.C_mul_X_pow_eq_monomial, hck, map_one, one_mul] using h1
    have hev_sum :
        (∑ i ∈ Finset.range k, (pZ.coeff i : ℚ) * ((n : ℚ) / (d : ℚ)) ^ i) +
          ((n : ℚ) / (d : ℚ)) ^ k = 0 := by
      have h := hev0
      rw [hp_sum, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X,
        hx_eq] at h
      simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_intCast,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_intCast, Polynomial.eval_pow, Polynomial.eval_X, eq_intCast] using h
    have hclear :
        (d : ℚ) * (∑ i ∈ Finset.range k,
            (pZ.coeff i : ℚ) * (n : ℚ) ^ i * (d : ℚ) ^ (k - 1 - i)) +
          (n : ℚ) ^ k = 0 := by
      have hmul := congrArg (fun z : ℚ => z * (d : ℚ) ^ k) hev_sum
      simp only [zero_mul, add_mul, Finset.sum_mul, Finset.mul_sum] at hmul ⊢
      have hlast : ((n : ℚ) / (d : ℚ)) ^ k * (d : ℚ) ^ k = (n : ℚ) ^ k := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero k hd_ne0_Q)]
      rw [hlast] at hmul
      have hterms : ∑ i ∈ Finset.range k,
          (pZ.coeff i : ℚ) * ((n : ℚ) / (d : ℚ)) ^ i * (d : ℚ) ^ k =
          ∑ i ∈ Finset.range k,
            (d : ℚ) * ((pZ.coeff i : ℚ) * (n : ℚ) ^ i * (d : ℚ) ^ (k - 1 - i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt : i < k := Finset.mem_range.mp hi
        have hexp : k = (k - 1 - i) + 1 + i := by omega
        calc (pZ.coeff i : ℚ) * ((n : ℚ) / (d : ℚ)) ^ i * (d : ℚ) ^ k
            = (pZ.coeff i : ℚ) * ((n : ℚ) ^ i / (d : ℚ) ^ i) *
                ((d : ℚ) ^ ((k - 1 - i) + 1) * (d : ℚ) ^ i) := by
              rw [div_pow, ← pow_add, ← hexp]
          _ = (pZ.coeff i : ℚ) * (n : ℚ) ^ i * (d : ℚ) ^ ((k - 1 - i) + 1) := by
              field_simp [hd_ne0_Q]
          _ = (d : ℚ) * ((pZ.coeff i : ℚ) * (n : ℚ) ^ i * (d : ℚ) ^ (k - 1 - i)) := by
              rw [pow_succ]; ring
      rwa [hterms] at hmul
    let S : ℤ := ∑ i ∈ Finset.range k, pZ.coeff i * n ^ i * d ^ (k - 1 - i)
    have hclear_Z : d * S + n ^ k = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast [S]
      exact hclear
    have hd_dvd : d ∣ n ^ k := ⟨-S, by linarith⟩
    have hd_dvd_nat : x.den ∣ x.num.natAbs ^ k := by
      have habs := Int.natAbs_dvd_natAbs.mpr hd_dvd
      simpa only [d, n, Int.natAbs_natCast, Int.natAbs_pow] using habs
    have hcop : x.den.Coprime (x.num.natAbs ^ k) :=
      Nat.Coprime.pow_right k x.reduced.symm
    have hden1 : x.den = 1 :=
      Nat.eq_one_of_dvd_one (hcop.dvd_of_dvd_mul_left (by simpa using hd_dvd_nat))
    have hx_int : x = (n : ℚ) := by
      rw [hx_eq]; dsimp [d]; rw [hden1]; simp
    rw [hx_int] at hev0
    have hev_Z : ((pZ.eval n : ℤ) : ℚ) = 0 := by
      have hhom := Polynomial.hom_eval₂ pZ (RingHom.id ℤ) (algebraMap ℤ ℚ) n
      simp only [RingHom.comp_id, Polynomial.eval₂_eq_eval_map, Polynomial.map_id,
        eq_intCast] at hhom
      exact hhom.trans hev0
    exact hno_int n (Int.cast_eq_zero.mp hev_Z)

private theorem monic_X_pow_add_of_natDegree_le {R : Type*} [CommRing R] {n : ℕ} {q : R[X]}
    (hq : q.natDegree ≤ n) : (Polynomial.X ^ (n + 1) + q).Monic :=
  Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hq)))

/-- Irreducibility criterion for a depressed quartic `f = x⁴ + px² + qx + r ∈ K[x]` (`char K ≠ 2`):
if `f` has no root in `K` and its cubic resolvent `g = depressedQuarticResolvent p q r` has no root
in `K`, then **both** `g` and `f` are irreducible in `K[x]`! -/
theorem irreducible_depressed_quartic_of_no_roots_and_resolvent_no_roots {K : Type*} [Field K]
    (hchar2 : ringChar K ≠ 2) {p q r : K}
    (hf_no_root : ∀ x : K,
      (Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r : K[X]).eval x ≠ 0)
    (hg_no_root : ∀ y : K, (depressedQuarticResolvent p q r).eval y ≠ 0) :
    Irreducible (depressedQuarticResolvent p q r) ∧
    Irreducible (Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
      Polynomial.C q * Polynomial.X + Polynomial.C r : K[X]) := by
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  let f : K[X] := Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
    Polynomial.C q * Polynomial.X + Polynomial.C r
  let g : K[X] := depressedQuarticResolvent p q r
  have hg_mon : g.Monic := depressedQuarticResolvent_monic p q r
  have hg_deg : g.natDegree = 3 := depressedQuarticResolvent_natDegree p q r
  have hf_mon : f.Monic := by
    dsimp [f]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    have heq : Polynomial.X ^ 4 + Polynomial.C p * Polynomial.X ^ 2 +
        Polynomial.C q * Polynomial.X + Polynomial.C r =
        Polynomial.X ^ 4 + (Polynomial.C p * Polynomial.X ^ 2 +
          Polynomial.C q * Polynomial.X + Polynomial.C r) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  have hlin_root : ∀ w : K[X], w.natDegree = 1 → ∃ x₀ : K, w.eval x₀ = 0 := by
    intro w hw1
    have hw_eq : w = Polynomial.C (w.coeff 1) * Polynomial.X + Polynomial.C (w.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one hw1.le
    have hc1_ne : w.coeff 1 ≠ 0 := by
      rw [← hw1, ← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; rw [h0] at hw1; simp at hw1)
    let x₀ : K := -w.coeff 0 / w.coeff 1
    refine ⟨x₀, ?_⟩
    rw [hw_eq]
    dsimp [x₀]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    field_simp [hc1_ne]; ring
  -- 1. `Irreducible g` (degree `3` with no root in `K`):
  have hirr_g : Irreducible g := by
    refine ⟨fun hu => ?_, fun u v huv => ?_⟩
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hnu, hnv⟩
      have hu0 : u ≠ 0 := fun h0 => hg_mon.ne_zero (by rw [huv, h0, zero_mul])
      have hv0 : v ≠ 0 := fun h0 => hg_mon.ne_zero (by rw [huv, h0, mul_zero])
      have hdu : 0 < u.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hu0 hnu)
      have hdv : 0 < v.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hv0 hnv)
      have hsum : u.natDegree + v.natDegree = 3 := by
        rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hg_deg]
      have hc : u.natDegree = 1 ∨ v.natDegree = 1 := by omega
      rcases hc with hu1 | hv1
      · obtain ⟨y₀, hy₀⟩ := hlin_root u hu1
        exact hg_no_root y₀ (by change g.eval y₀ = 0; rw [huv, Polynomial.eval_mul, hy₀, zero_mul])
      · obtain ⟨y₀, hy₀⟩ := hlin_root v hv1
        exact hg_no_root y₀ (by change g.eval y₀ = 0; rw [huv, Polynomial.eval_mul, hy₀, mul_zero])
  -- 2. `Irreducible f`:
  have hirr_f : Irreducible f := by
    refine ⟨fun hu => ?_, fun u v huv => ?_⟩
    · have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    · by_contra hboth
      push Not at hboth
      rcases hboth with ⟨hnu, hnv⟩
      have hu0 : u ≠ 0 := fun h0 => hf_mon.ne_zero (by rw [huv, h0, zero_mul])
      have hv0 : v ≠ 0 := fun h0 => hf_mon.ne_zero (by rw [huv, h0, mul_zero])
      have hdu : 0 < u.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hu0 hnu)
      have hdv : 0 < v.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_ne_zero_of_nonunit hv0 hnv)
      have hsum : u.natDegree + v.natDegree = 4 := by
        rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hf_deg]
      have hc : u.natDegree = 1 ∨ v.natDegree = 1 ∨ (u.natDegree = 2 ∧ v.natDegree = 2) := by omega
      rcases hc with hu1 | hv1 | ⟨hu2, hv2⟩
      · obtain ⟨x₀, hx₀⟩ := hlin_root u hu1
        exact hf_no_root x₀ (by change f.eval x₀ = 0; rw [huv, Polynomial.eval_mul, hx₀, zero_mul])
      · obtain ⟨x₀, hx₀⟩ := hlin_root v hv1
        exact hf_no_root x₀ (by change f.eval x₀ = 0; rw [huv, Polynomial.eval_mul, hx₀, mul_zero])
      · -- Normalize `u` and `v` to monic quadratics `X^2 + a X + b` and `X^2 + a' X + c`:
        have hlc_u : u.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu0
        have hlc_v : v.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hv0
        have hlc_uv : u.leadingCoeff * v.leadingCoeff = 1 := by
          rw [← Polynomial.leadingCoeff_mul, ← huv, hf_mon.leadingCoeff]
        let um : K[X] := Polynomial.C u.leadingCoeff⁻¹ * u
        let vm : K[X] := Polynomial.C u.leadingCoeff * v
        have hum_mon : um.Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            inv_mul_cancel₀ hlc_u]
        have hvm_mon : vm.Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlc_uv]
        have hum_deg : um.natDegree = 2 := by
          dsimp [um]; rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_u), hu2]
        have hvm_deg : vm.natDegree = 2 := by
          dsimp [vm]; rw [Polynomial.natDegree_C_mul hlc_u, hv2]
        have huvm : f = um * vm := by
          dsimp [um, vm]
          calc f = u * v := huv
            _ = (Polynomial.C u.leadingCoeff⁻¹ * Polynomial.C u.leadingCoeff) * (u * v) := by
                rw [← Polynomial.C_mul, inv_mul_cancel₀ hlc_u, map_one, one_mul]
            _ = (Polynomial.C u.leadingCoeff⁻¹ * u) * (Polynomial.C u.leadingCoeff * v) := by ring
        let a : K := um.coeff 1
        let b : K := um.coeff 0
        let a' : K := vm.coeff 1
        let c : K := vm.coeff 0
        have hum_eq : um = Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b := by
          rw [um.as_sum_range' 3 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_one]
          have hc2 : um.coeff 2 = 1 := by rw [← hum_deg, ← Polynomial.leadingCoeff, hum_mon.leadingCoeff]
          simp only [hc2, a, b, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
            map_one, one_mul, mul_one]; ring
        have hvm_eq : vm = Polynomial.X ^ 2 + Polynomial.C a' * Polynomial.X + Polynomial.C c := by
          rw [vm.as_sum_range' 3 (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_one]
          have hc2 : vm.coeff 2 = 1 := by rw [← hvm_deg, ← Polynomial.leadingCoeff, hvm_mon.leadingCoeff]
          simp only [hc2, a', c, ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, pow_one,
            map_one, one_mul, mul_one]; ring
        have hprod_expand : um * vm =
            Polynomial.X ^ 4 + Polynomial.C (a + a') * Polynomial.X ^ 3 +
              Polynomial.C (b + c + a * a') * Polynomial.X ^ 2 +
              Polynomial.C (a * c + a' * b) * Polynomial.X +
              Polynomial.C (b * c) := by
          rw [hum_eq, hvm_eq]; simp only [map_add, map_mul]; ring
        rw [hprod_expand] at huvm
        have hc3 : a + a' = 0 := by
          have h := congrArg (fun P : K[X] => P.coeff 3) huvm
          dsimp [f] at h
          simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
            Polynomial.coeff_X, Polynomial.coeff_C] at h
          norm_num at h; exact h.symm
        have ha' : a' = -a := by linear_combination hc3
        have hc2 : b + c + a * a' = p := by
          have h := congrArg (fun P : K[X] => P.coeff 2) huvm
          dsimp [f] at h
          simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
            Polynomial.coeff_X, Polynomial.coeff_C] at h
          norm_num at h; exact h.symm
        have hc1 : a * c + a' * b = q := by
          have h := congrArg (fun P : K[X] => P.coeff 1) huvm
          dsimp [f] at h
          simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
            Polynomial.coeff_X, Polynomial.coeff_C] at h
          norm_num at h; exact h.symm
        have hc0 : b * c = r := by
          have h := congrArg (fun P : K[X] => P.coeff 0) huvm
          dsimp [f] at h
          simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
            Polynomial.coeff_X, Polynomial.coeff_C] at h
          norm_num at h; exact h.symm
        rw [ha'] at hc2 hc1
        -- Either way (`a = 0` or `a ≠ 0`), `a^2 ∈ K` is a root of `g = depressedQuarticResolvent p q r`!
        have hg_root_a2 : g.eval (a ^ 2) = 0 := by
          dsimp [g, depressedQuarticResolvent]
          simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          rw [← hc2, ← hc1, ← hc0]
          ring
        exact hg_no_root (a ^ 2) hg_root_a2
  exact ⟨hirr_g, hirr_f⟩

/-- Universal Row-1 / Row-2 corollary of `exercise_14_7_repaired` (no mention of `M` needed!):
if `f ∈ K[x]` (`char K ≠ 2, 3`) is an irreducible quartic whose cubic resolvent `g` is irreducible
over `K`, then for **every** splitting field `L : K` of `f`:
- if `garlingDiscriminant f` has no square root in `K`, `Γ_K(f) ≃* Σ₄` (`|Γ_K(f)| = 24`);
- if `garlingDiscriminant f` has a square root in `K`, `Γ_K(f) ≃* A₄` (`|Γ_K(f)| = 12`). -/
theorem quartic_galoisGroup_of_irreducible_resolvent {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    {f : K[X]} (hirr : Irreducible f) (hdeg : f.natDegree = 4)
    (hsf : IsGarlingSplittingFieldExtension K L f)
    (hirr_g : Irreducible (quarticCubicResolvent f)) :
    ((¬ ∃ d : K, d ^ 2 = garlingDiscriminant f) →
      Nat.card (GarlingPolyGaloisGroup K L f) = 24 ∧
      Nonempty (GarlingPolyGaloisGroup K L f ≃* SigmaN 4)) ∧
    ((∃ d : K, d ^ 2 = garlingDiscriminant f) →
      Nat.card (GarlingPolyGaloisGroup K L f) = 12 ∧
      Nonempty (GarlingPolyGaloisGroup K L f ≃* alternatingGroup (Fin 4))) := by
  have h2K : (2 : K) ≠ 0 := by
    simpa using natCast_prime_ne_zero_of_ringChar_ne Nat.prime_two hchar2
  have h4K : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2K
  have hsep : f.Separable :=
    (irreducible_separable_of_natDegree_cast_ne_zero hirr (by rw [hdeg]; exact_mod_cast h4K)).1
  have hcard_roots : (garlingRootSet K L f).ncard = 4 :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsf).trans hdeg
  have hfin_roots : (garlingRootSet K L f).Finite := by
    by_contra hinf; rw [Set.Infinite.ncard hinf] at hcard_roots; omega
  have _ : Fintype (garlingRootSet K L f) := hfin_roots.fintype
  have hfintype_card : Fintype.card (garlingRootSet K L f) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_roots
  let e₀ : Fin 4 ≃ garlingRootSet K L f := (Fintype.equivFinOfCardEq hfintype_card).symm
  obtain ⟨hsf_M₀, _, _, _, _⟩ := section_14_4_resolvent_splitting_subfield hchar2 hdeg hsep hsf e₀
  let M₀ := IntermediateField.fixedField (viergruppe.comap (garlingRootLabellingPermHom e₀))
  have hex7 := (exercise_14_7_repaired hchar2 hchar3 hirr hdeg hsf M₀ hsf_M₀).2.2.2.2 e₀
  exact ⟨fun hno => hex7.2.2.2.2.2.2.1 ⟨hno, hirr_g⟩,
    fun hsq => hex7.2.2.2.2.2.2.2.1 ⟨hsq, hirr_g⟩⟩

/-- **Exercise 14.8(i)** (§14.4, printed p. 117 / PDF p. 125):
For `f₁ = x⁴ + 4x + 2 ∈ ℚ[x]`, `f₁` and its cubic resolvent `x³ - 8x - 16` are irreducible over `ℚ`,
`garlingDiscriminant f₁ = -4864` has no square root in `ℚ`, and for **every** splitting field
extension `L : ℚ` of `f₁`, `|Γ_ℚ(f₁)| = 24` and `Γ_ℚ(f₁) ≃* Σ₄`. -/
theorem exercise_14_8_i :
    let f : ℚ[X] := Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X + Polynomial.C 2
    Irreducible f ∧
    Irreducible (quarticCubicResolvent f) ∧
    garlingDiscriminant f = -4864 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 24 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* SigmaN 4) := by
  intro f
  have hf_eq : f = Polynomial.X ^ 4 + Polynomial.C 0 * Polynomial.X ^ 2 +
      Polynomial.C 4 * Polynomial.X + Polynomial.C 2 := by
    dsimp [f]; simp
  have hf_deg : f.natDegree = 4 := by
    rw [hf_eq]
    have heq : Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 4 * Polynomial.X + Polynomial.C 2 =
        Polynomial.X ^ 4 + (Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C 4 * Polynomial.X + Polynomial.C 2) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  -- Show neither `f` nor `depressedQuarticResolvent 0 4 2 = X^3 - 8*X - 16` has a root in `ℚ`:
  let fZ : ℤ[X] := Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X + Polynomial.C 2
  have hfZ_mon : fZ.Monic := by
    dsimp [fZ]
    have heq : Polynomial.X ^ 4 + Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C 2 =
        Polynomial.X ^ 4 + (Polynomial.C 4 * Polynomial.X + Polynomial.C 2) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hfZ_no_int : ∀ r : ℤ, fZ.eval r ≠ 0 := by
    intro r hr
    dsimp [fZ] at hr
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at hr
    by_cases h1 : r ≤ -3
    · have hr2 : 9 ≤ r ^ 2 := by nlinarith
      nlinarith
    · by_cases h2 : 2 ≤ r
      · have hr2 : 4 ≤ r ^ 2 := by nlinarith
        nlinarith
      · have hb : -2 ≤ r ∧ r ≤ 1 := by omega
        rcases hb with ⟨_, _⟩
        interval_cases r <;> omega
  have hf_no_rat : ∀ x : ℚ,
      (Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 4 * Polynomial.X + Polynomial.C 2 : ℚ[X]).eval x ≠ 0 := by
    intro x
    rw [← hf_eq]
    have hmap : fZ.map (algebraMap ℤ ℚ) = f := by dsimp [fZ, f]; simp [map_ofNat]
    rw [← hmap]
    exact rat_eval_ne_zero_of_monic_int_eval_ne_zero hfZ_mon hfZ_no_int x
  let gZ : ℤ[X] := Polynomial.X ^ 3 - Polynomial.C 8 * Polynomial.X - Polynomial.C 16
  have hgZ_mon : gZ.Monic := by
    dsimp [gZ]
    have heq : Polynomial.X ^ 3 - Polynomial.C (8 : ℤ) * Polynomial.X - Polynomial.C 16 =
        Polynomial.X ^ 3 + (-Polynomial.C 8 * Polynomial.X - Polynomial.C 16) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hgZ_no_int : ∀ r : ℤ, gZ.eval r ≠ 0 := by
    intro r hr
    dsimp [gZ] at hr
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at hr
    by_cases h1 : r ≤ -4
    · have hfac : (r + 4) * (r ^ 2 - 4 * r + 8) ≤ 0 := by
        have hpos : 0 ≤ r ^ 2 - 4 * r + 8 := by nlinarith
        nlinarith
      nlinarith
    · by_cases h2 : 4 ≤ r
      · have hfac : 0 ≤ (r - 4) * (r ^ 2 + 4 * r + 8) := by
          have hpos : 0 ≤ r ^ 2 + 4 * r + 8 := by nlinarith
          nlinarith
        nlinarith
      · have hb : -3 ≤ r ∧ r ≤ 3 := by omega
        rcases hb with ⟨_, _⟩
        interval_cases r <;> omega
  have hg_eq_map : depressedQuarticResolvent (0 : ℚ) 4 2 = gZ.map (algebraMap ℤ ℚ) := by
    unfold depressedQuarticResolvent
    dsimp [gZ]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      eq_intCast]
    norm_num
    simp only [Polynomial.C_ofNat]
    ring
  have hg_no_rat : ∀ y : ℚ, (depressedQuarticResolvent (0 : ℚ) 4 2).eval y ≠ 0 := by
    intro y
    rw [hg_eq_map]
    exact rat_eval_ne_zero_of_monic_int_eval_ne_zero hgZ_mon hgZ_no_int y
  obtain ⟨hirr_g0, hirr_f0⟩ :=
    irreducible_depressed_quartic_of_no_roots_and_resolvent_no_roots
      ringChar_rat_ne_two hf_no_rat hg_no_rat
  have hirr_f : Irreducible f := by rw [hf_eq]; exact hirr_f0
  have hirr_g : Irreducible (quarticCubicResolvent f) := by
    rw [hf_eq, quarticCubicResolvent_depressed]; exact hirr_g0
  have hdisc : garlingDiscriminant f = -4864 := by
    rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg,
      hf_eq, quarticCubicResolvent_depressed]
    unfold depressedQuarticResolvent
    have hcub : Polynomial.X ^ 3 + Polynomial.C (2 * (0 : ℚ)) * Polynomial.X ^ 2 +
        Polynomial.C ((0 : ℚ) ^ 2 - 4 * 2) * Polynomial.X - Polynomial.C ((4 : ℚ) ^ 2) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C (-8) * Polynomial.X + Polynomial.C (-16) := by
      norm_num; simp [sub_eq_add_neg]
    rw [hcub, garlingDiscriminant_monic_cubic]
    norm_num
  have hno_sq : ¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := by
    rw [hdisc]; rintro ⟨d, hd⟩; linarith [sq_nonneg d]
  refine ⟨hirr_f, hirr_g, hdisc, fun L _ _ hsf => ?_⟩
  exact (quartic_galoisGroup_of_irreducible_resolvent
    ringChar_rat_ne_two ringChar_rat_ne_three
    hirr_f hf_deg hsf hirr_g).1 hno_sq

/-- **Exercise 14.8(ii)** (§14.4, printed p. 117 / PDF p. 125):
For the literal printed polynomial `f₂ = x⁴ + 8x - 12 ∈ ℚ[x]`, `f₂` and its cubic resolvent
`x³ + 48x - 64` are irreducible over `ℚ`, `garlingDiscriminant f₂ = -552960 < 0` has no square
root in `ℚ`, and for **every** splitting field extension `L : ℚ` of `f₂`, `|Γ_ℚ(f₂)| = 24` and
`Γ_ℚ(f₂) ≃* Σ₄`. -/
theorem exercise_14_8_ii :
    let f : ℚ[X] := Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X - Polynomial.C 12
    Irreducible f ∧
    Irreducible (quarticCubicResolvent f) ∧
    garlingDiscriminant f = -552960 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 24 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* SigmaN 4) := by
  intro f
  have hf_eq : f = Polynomial.X ^ 4 + Polynomial.C 0 * Polynomial.X ^ 2 +
      Polynomial.C 8 * Polynomial.X + Polynomial.C (-12) := by
    dsimp [f]; simp [sub_eq_add_neg]
  have hf_deg : f.natDegree = 4 := by
    rw [hf_eq]
    have heq : Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 8 * Polynomial.X + Polynomial.C (-12) =
        Polynomial.X ^ 4 + (Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C 8 * Polynomial.X + Polynomial.C (-12)) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  let fZ : ℤ[X] := Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X - Polynomial.C 12
  have hfZ_mon : fZ.Monic := by
    dsimp [fZ]
    have heq : Polynomial.X ^ 4 + Polynomial.C (8 : ℤ) * Polynomial.X - Polynomial.C 12 =
        Polynomial.X ^ 4 + (Polynomial.C 8 * Polynomial.X - Polynomial.C 12) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hfZ_no_int : ∀ r : ℤ, fZ.eval r ≠ 0 := by
    intro r hr
    dsimp [fZ] at hr
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at hr
    by_cases h1 : r ≤ -3
    · have hr2 : 9 ≤ r ^ 2 := by nlinarith
      have hpos : 0 ≤ (r ^ 2 - 4) ^ 2 := sq_nonneg _
      have hpr : 6 ≤ r * (r + 1) := by nlinarith
      nlinarith
    · by_cases h2 : 2 ≤ r
      · have hr2 : 4 ≤ r ^ 2 := by nlinarith
        nlinarith
      · have hb : -2 ≤ r ∧ r ≤ 1 := by omega
        rcases hb with ⟨_, _⟩
        interval_cases r <;> omega
  have hf_no_rat : ∀ x : ℚ,
      (Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 8 * Polynomial.X + Polynomial.C (-12) : ℚ[X]).eval x ≠ 0 := by
    intro x
    rw [← hf_eq]
    have hmap : fZ.map (algebraMap ℤ ℚ) = f := by dsimp [fZ, f]; simp [map_ofNat]
    rw [← hmap]
    exact rat_eval_ne_zero_of_monic_int_eval_ne_zero hfZ_mon hfZ_no_int x
  let gZ : ℤ[X] := Polynomial.X ^ 3 + Polynomial.C 48 * Polynomial.X - Polynomial.C 64
  have hgZ_mon : gZ.Monic := by
    dsimp [gZ]
    have heq : Polynomial.X ^ 3 + Polynomial.C (48 : ℤ) * Polynomial.X - Polynomial.C 64 =
        Polynomial.X ^ 3 + (Polynomial.C 48 * Polynomial.X - Polynomial.C 64) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hgZ_no_int : ∀ r : ℤ, gZ.eval r ≠ 0 := by
    intro r hr
    dsimp [gZ] at hr
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at hr
    by_cases h1 : r ≤ 1
    · have hfac : 0 ≤ (1 - r) * (r ^ 2 + r + 49) := by
        have hpos : 0 ≤ (2 * r + 1) ^ 2 := sq_nonneg _
        have hq : 0 ≤ r ^ 2 + r + 49 := by nlinarith
        nlinarith
      nlinarith
    · have h2 : 2 ≤ r := by omega
      have hfac : 0 ≤ (r - 2) * (r ^ 2 + 2 * r + 52) := by
        have hq : 0 ≤ r ^ 2 + 2 * r + 52 := by nlinarith [sq_nonneg (r + 1)]
        nlinarith
      nlinarith
  have hg_eq_map : depressedQuarticResolvent (0 : ℚ) 8 (-12) = gZ.map (algebraMap ℤ ℚ) := by
    unfold depressedQuarticResolvent
    dsimp [gZ]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, eq_intCast]
    norm_num
    simp only [Polynomial.C_ofNat]
  have hg_no_rat : ∀ y : ℚ, (depressedQuarticResolvent (0 : ℚ) 8 (-12)).eval y ≠ 0 := by
    intro y
    rw [hg_eq_map]
    exact rat_eval_ne_zero_of_monic_int_eval_ne_zero hgZ_mon hgZ_no_int y
  obtain ⟨hirr_g0, hirr_f0⟩ :=
    irreducible_depressed_quartic_of_no_roots_and_resolvent_no_roots
      ringChar_rat_ne_two hf_no_rat hg_no_rat
  have hirr_f : Irreducible f := by rw [hf_eq]; exact hirr_f0
  have hirr_g : Irreducible (quarticCubicResolvent f) := by
    rw [hf_eq, quarticCubicResolvent_depressed]; exact hirr_g0
  have hdisc : garlingDiscriminant f = -552960 := by
    rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg,
      hf_eq, quarticCubicResolvent_depressed]
    unfold depressedQuarticResolvent
    have hcub : Polynomial.X ^ 3 + Polynomial.C (2 * (0 : ℚ)) * Polynomial.X ^ 2 +
        Polynomial.C ((0 : ℚ) ^ 2 - 4 * (-12)) * Polynomial.X - Polynomial.C ((8 : ℚ) ^ 2) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C 48 * Polynomial.X + Polynomial.C (-64) := by
      norm_num; simp [sub_eq_add_neg]
    rw [hcub, garlingDiscriminant_monic_cubic]
    norm_num
  have hno_sq : ¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := by
    rw [hdisc]; rintro ⟨d, hd⟩; linarith [sq_nonneg d]
  refine ⟨hirr_f, hirr_g, hdisc, fun L _ _ hsf => ?_⟩
  exact (quartic_galoisGroup_of_irreducible_resolvent
    ringChar_rat_ne_two ringChar_rat_ne_three
    hirr_f hf_deg hsf hirr_g).1 hno_sq

/-- **Companion Remark on `x⁴ + 8x + 12` for `Exercise 14.8(ii)`** (`BRIEF.md` Flag 4):
With `+ 12` in place of `- 12`, `x⁴ + 8x + 12 ∈ ℚ[x]` and its resolvent `x³ - 48x - 64` are
irreducible over `ℚ` with discriminant `331776 = 576²`, realizing Row 2 (`Γ_ℚ(x⁴ + 8x + 12) ≃* A₄`,
order `12`). -/
theorem exercise_14_8_ii_plus_twelve_remark :
    let f : ℚ[X] := Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X + Polynomial.C 12
    Irreducible f ∧
    Irreducible (quarticCubicResolvent f) ∧
    garlingDiscriminant f = 331776 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 12 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* alternatingGroup (Fin 4)) := by
  intro f
  have hf_eq : f = Polynomial.X ^ 4 + Polynomial.C 0 * Polynomial.X ^ 2 +
      Polynomial.C 8 * Polynomial.X + Polynomial.C 12 := by
    dsimp [f]; simp
  have hf_deg : f.natDegree = 4 := by
    rw [hf_eq]
    have heq : Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 8 * Polynomial.X + Polynomial.C 12 =
        Polynomial.X ^ 4 + (Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C 8 * Polynomial.X + Polynomial.C 12) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  have hf_no_rat : ∀ x : ℚ,
      (Polynomial.X ^ 4 + Polynomial.C (0 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C 8 * Polynomial.X + Polynomial.C 12 : ℚ[X]).eval x ≠ 0 := by
    intro x hx
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, zero_mul, add_zero] at hx
    have h1 : 0 ≤ (x ^ 2 - 2) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (x + 1) ^ 2 := sq_nonneg _
    linarith
  let gZ : ℤ[X] := Polynomial.X ^ 3 - Polynomial.C 48 * Polynomial.X - Polynomial.C 64
  have hgZ_mon : gZ.Monic := by
    dsimp [gZ]
    have heq : Polynomial.X ^ 3 - Polynomial.C (48 : ℤ) * Polynomial.X - Polynomial.C 64 =
        Polynomial.X ^ 3 + (-Polynomial.C 48 * Polynomial.X - Polynomial.C 64) := by ring
    rw [heq]
    exact monic_X_pow_add_of_natDegree_le (by compute_degree!)
  have hgZ_no_int : ∀ r : ℤ, gZ.eval r ≠ 0 := by
    intro r hr
    dsimp [gZ] at hr
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at hr
    by_cases h1 : r ≤ -8
    · have hfac : (r + 8) * (r ^ 2 - 8 * r + 16) ≤ 0 := by
        have hpos : 0 ≤ (r - 4) ^ 2 := sq_nonneg _
        have hq : 0 ≤ r ^ 2 - 8 * r + 16 := by linarith
        nlinarith
      nlinarith
    · by_cases h2 : 8 ≤ r
      · have hfac : 0 ≤ (r - 8) * (r ^ 2 + 8 * r + 16) := by
          have hpos : 0 ≤ (r + 4) ^ 2 := sq_nonneg _
          have hq : 0 ≤ r ^ 2 + 8 * r + 16 := by linarith
          nlinarith
        nlinarith
      · have hb : -7 ≤ r ∧ r ≤ 7 := by omega
        rcases hb with ⟨_, _⟩
        interval_cases r <;> omega
  have hg_eq_map : depressedQuarticResolvent (0 : ℚ) 8 12 = gZ.map (algebraMap ℤ ℚ) := by
    unfold depressedQuarticResolvent
    dsimp [gZ]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      eq_intCast]
    norm_num
    simp only [Polynomial.C_ofNat]
    ring
  have hg_no_rat : ∀ y : ℚ, (depressedQuarticResolvent (0 : ℚ) 8 12).eval y ≠ 0 := by
    intro y
    rw [hg_eq_map]
    exact rat_eval_ne_zero_of_monic_int_eval_ne_zero hgZ_mon hgZ_no_int y
  obtain ⟨hirr_g0, hirr_f0⟩ :=
    irreducible_depressed_quartic_of_no_roots_and_resolvent_no_roots
      ringChar_rat_ne_two hf_no_rat hg_no_rat
  have hirr_f : Irreducible f := by rw [hf_eq]; exact hirr_f0
  have hirr_g : Irreducible (quarticCubicResolvent f) := by
    rw [hf_eq, quarticCubicResolvent_depressed]; exact hirr_g0
  have hdisc : garlingDiscriminant f = 331776 := by
    rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg,
      hf_eq, quarticCubicResolvent_depressed]
    unfold depressedQuarticResolvent
    have hcub : Polynomial.X ^ 3 + Polynomial.C (2 * (0 : ℚ)) * Polynomial.X ^ 2 +
        Polynomial.C ((0 : ℚ) ^ 2 - 4 * 12) * Polynomial.X - Polynomial.C ((8 : ℚ) ^ 2) =
        Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 +
          Polynomial.C (-48) * Polynomial.X + Polynomial.C (-64) := by
      norm_num; simp [sub_eq_add_neg]
    rw [hcub, garlingDiscriminant_monic_cubic]
    norm_num
  have hsq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := ⟨576, by rw [hdisc]; norm_num⟩
  refine ⟨hirr_f, hirr_g, hdisc, fun L _ _ hsf => ?_⟩
  exact (quartic_galoisGroup_of_irreducible_resolvent
    ringChar_rat_ne_two ringChar_rat_ne_three
    hirr_f hf_deg hsf hirr_g).2 hsq

/-- **Exercise 14.8(iii)** (§14.4, printed p. 117 / PDF p. 125):
For `f₃ = x⁴ + 1 ∈ ℚ[x]`, `f₃` is irreducible over `ℚ`, its cubic resolvent `x³ - 4x = x(x - 2)(x + 2)`
splits over `ℚ`, `garlingDiscriminant f₃ = 256 = 16²`, and for **every** splitting field extension
`L : ℚ` of `f₃`, `|Γ_ℚ(f₃)| = 4`, `Γ_ℚ(f₃) ≃* viergruppe`, and
`Γ_ℚ(f₃) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)` (`N ≅ ℤ₂ × ℤ₂`). -/
theorem exercise_14_8_iii :
    let f : ℚ[X] := Polynomial.X ^ 4 + 1
    Irreducible f ∧
    GarlingSplitsOver ℚ ℚ (quarticCubicResolvent f) ∧
    garlingDiscriminant f = 256 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 4 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* viergruppe) ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  intro f
  have hf_mon : f.Monic := by
    dsimp [f]; rw [← map_one Polynomial.C]; exact Polynomial.monic_X_pow_add_C 1 (by decide)
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]; rw [← map_one Polynomial.C]; exact Polynomial.natDegree_X_pow_add_C
  -- `Irreducible (X^4 + 1)` from `[ℚ(ζ₈) : ℚ] = 4` (`exercise_7_8`):
  have hirr_f : Irreducible f := by
    have hfin4 : Module.finrank ℚ ℚ⟮zeta8⟯ = 4 := exercise_7_8.2.1.2.1
    have hζ_sq : zeta8 ^ 2 = Complex.I := by
      unfold zeta8
      have hs2 : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
      rw [div_pow, hs2]
      calc (1 + Complex.I) ^ 2 / 2 = (1 + 2 * Complex.I + Complex.I ^ 2) / 2 := by ring
        _ = Complex.I := by rw [Complex.I_sq]; ring
    have haev : Polynomial.aeval zeta8 f = 0 := by
      dsimp [f]
      rw [map_add, map_pow, Polynomial.aeval_X, map_one]
      calc zeta8 ^ 4 + 1 = (zeta8 ^ 2) ^ 2 + 1 := by ring
        _ = Complex.I ^ 2 + 1 := by rw [hζ_sq]
        _ = 0 := by rw [Complex.I_sq]; ring
    have hint : IsIntegral ℚ zeta8 := ⟨f, hf_mon, haev⟩
    have hdvd : minpoly ℚ zeta8 ∣ f := minpoly.dvd ℚ zeta8 haev
    have hdeg_min : (minpoly ℚ zeta8).natDegree = 4 := by
      rw [← IntermediateField.adjoin.finrank hint, hfin4]
    obtain ⟨q, hq⟩ := hdvd
    have hq0 : q ≠ 0 := fun h0 => hf_mon.ne_zero (by rw [hq, h0, mul_zero])
    have hdeg_q : q.natDegree = 0 := by
      have hs := Polynomial.natDegree_mul (minpoly.ne_zero hint) hq0
      rw [← hq, hf_deg, hdeg_min] at hs; omega
    have hq_mon : q.Monic := (minpoly.monic hint).of_mul_monic_left (hq ▸ hf_mon)
    have hq1 : q = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg_q]
      have hc0 : q.coeff 0 = 1 := by rw [← hdeg_q, ← Polynomial.leadingCoeff, hq_mon.leadingCoeff]
      rw [hc0, map_one]
    rw [hq, hq1, mul_one]
    exact minpoly.irreducible hint
  have hf_eq : f = Polynomial.X ^ 4 + Polynomial.C 0 * Polynomial.X ^ 2 +
      Polynomial.C 0 * Polynomial.X + Polynomial.C 1 := by
    dsimp [f]; simp
  have hg_eq : quarticCubicResolvent f = Polynomial.X ^ 3 - Polynomial.C 4 * Polynomial.X := by
    rw [hf_eq, quarticCubicResolvent_depressed]
    unfold depressedQuarticResolvent
    norm_num
    simp only [Polynomial.C_ofNat]
    ring
  have hsp_g : GarlingSplitsOver ℚ ℚ (quarticCubicResolvent f) := by
    rw [hg_eq]
    refine ⟨3, 1, ![0, 2, -2], ?_⟩
    unfold GarlingSplitsExplicit
    rw [Algebra.algebraMap_self, Polynomial.map_id, Fin.prod_univ_three]
    have v0 : (![0, 2, -2] : Fin 3 → ℚ) 0 = 0 := rfl
    have v1 : (![0, 2, -2] : Fin 3 → ℚ) 1 = 2 := rfl
    have v2 : (![0, 2, -2] : Fin 3 → ℚ) 2 = -2 := rfl
    rw [v0, v1, v2]
    simp only [map_one, map_zero, map_neg, map_ofNat, one_mul, sub_zero, sub_neg_eq_add]
    ring
  have hdisc : garlingDiscriminant f = 256 := by
    rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg, hg_eq]
    have hcub : (Polynomial.X ^ 3 - Polynomial.C 4 * Polynomial.X : ℚ[X]) =
        Polynomial.X ^ 3 + Polynomial.C (-4) * Polynomial.X + Polynomial.C 0 := by
      simp [sub_eq_add_neg]
    rw [hcub, garlingDiscriminant_depressed_cubic]
    norm_num
  have hsq : ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := ⟨16, by rw [hdisc]; norm_num⟩
  refine ⟨hirr_f, hsp_g, hdisc, fun L _ _ hsf => ?_⟩
  have hsep : f.Separable := hirr_f.separable
  have hcard_roots : (garlingRootSet ℚ L f).ncard = 4 :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsf).trans hf_deg
  have hfin_roots : (garlingRootSet ℚ L f).Finite := by
    by_contra hinf; rw [Set.Infinite.ncard hinf] at hcard_roots; omega
  have _ : Fintype (garlingRootSet ℚ L f) := hfin_roots.fintype
  have hfintype_card : Fintype.card (garlingRootSet ℚ L f) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_roots
  let e₀ : Fin 4 ≃ garlingRootSet ℚ L f := (Fintype.equivFinOfCardEq hfintype_card).symm
  obtain ⟨hsf_M₀, _, _, _, _⟩ :=
    section_14_4_resolvent_splitting_subfield ringChar_rat_ne_two hf_deg hsep hsf e₀
  let M₀ := IntermediateField.fixedField (viergruppe.comap (garlingRootLabellingPermHom e₀))
  have hex7 := (exercise_14_7_repaired ringChar_rat_ne_two ringChar_rat_ne_three
    hirr_f hf_deg hsf M₀ hsf_M₀).2.2.2.2 e₀
  obtain ⟨hc4, ⟨eV⟩⟩ := hex7.2.2.2.2.2.2.2.2.1 ⟨hsq, hsp_g⟩
  exact ⟨hc4, ⟨eV⟩, ⟨eV.trans viergruppeMulEquivZMod2Prod⟩⟩

/-- **Exercise 14.8(iv)** (§14.4, printed p. 117 / PDF p. 125):
For `f₄ = x⁴ + x³ + x² + x + 1 ∈ ℚ[x]` (`Φ₅`), `f₄` is irreducible over `ℚ` (`Exercise 5.11`),
`garlingDiscriminant f₄ = 125` has no square root in `ℚ`, `f₄` splits over `AdjoinRoot f₄` of
degree `4`, and for **every** splitting field extension `L : ℚ` of `f₄`, `Γ_ℚ(f₄)` is cyclic of
order `4` (`Γ_ℚ(f₄) ≃* Multiplicative (ZMod 4)`). -/
theorem exercise_14_8_iv :
    let f : ℚ[X] := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1
    Irreducible f ∧
    garlingDiscriminant f = 125 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      IsCyclic (GarlingPolyGaloisGroup ℚ L f) ∧
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 4 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* Multiplicative (ZMod 4)) := by
  intro f
  have hf_cyc5 : f = garlingPrimeCyclotomicRat 5 := by
    unfold garlingPrimeCyclotomicRat
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, pow_one]
    ring
  have hirr_f : Irreducible f := hf_cyc5 ▸ (exercise_5_11 (by decide : Nat.Prime 5)).1
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    have heq : Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + (1 : ℚ[X]) =
        Polynomial.X ^ 4 + (Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1) := by ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 4
    · compute_degree!
  have hf_mon : f.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf_deg]
    dsimp [f]
    simp [Polynomial.coeff_one, Polynomial.coeff_X]
  -- Discriminant `Δ(f₄) = 125`, which has no square root in `ℚ`:
  have hg_eq : quarticCubicResolvent f =
      Polynomial.X ^ 3 + Polynomial.C (5 / 4 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (-45 / 16 : ℚ) * Polynomial.X + Polynomial.C (-25 / 64 : ℚ) := by
    unfold quarticCubicResolvent
    have hlc1 : f.leadingCoeff = 1 := hf_mon.leadingCoeff
    change (let fm := Polynomial.C f.leadingCoeff⁻¹ * f; _) = _
    rw [hlc1, inv_one, map_one, one_mul]
    dsimp only
    have hc3 : f.coeff 3 = 1 := by dsimp [f]; simp [Polynomial.coeff_one, Polynomial.coeff_X]
    have hc2 : f.coeff 2 = 1 := by dsimp [f]; simp [Polynomial.coeff_one, Polynomial.coeff_X]
    have hc1 : f.coeff 1 = 1 := by dsimp [f]; simp [Polynomial.coeff_one, Polynomial.coeff_X]
    have hc0 : f.coeff 0 = 1 := by dsimp [f]; simp [Polynomial.coeff_one, Polynomial.coeff_X]
    rw [hc3, hc2, hc1, hc0]
    unfold depressedQuarticResolvent depressedQuarticP depressedQuarticQ depressedQuarticR
    norm_num
    simp [sub_eq_add_neg]
  have hdisc : garlingDiscriminant f = 125 := by
    rw [← garlingDiscriminant_quarticCubicResolvent ringChar_rat_ne_two hf_deg,
      hg_eq, garlingDiscriminant_monic_cubic]
    norm_num
  have hno_sq : ¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f := by
    rw [hdisc]
    rintro ⟨d, hd⟩
    let qZ : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C 125
    have hqZ_mon : qZ.Monic := Polynomial.monic_X_pow_sub_C 125 (by decide)
    have hqZ_no_int : ∀ r : ℤ, qZ.eval r ≠ 0 := by
      intro r hr
      dsimp [qZ] at hr
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
      by_cases h1 : r ≤ -12
      · nlinarith
      · by_cases h2 : 12 ≤ r
        · nlinarith
        · have hb : -11 ≤ r ∧ r ≤ 11 := by omega
          rcases hb with ⟨_, _⟩
          interval_cases r <;> omega
    refine rat_eval_ne_zero_of_monic_int_eval_ne_zero hqZ_mon hqZ_no_int d ?_
    dsimp [qZ]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eq_intCast,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    norm_num
    linarith
  -- In every splitting field `L : ℚ` of `f`, pick a root `ζ ∈ L` of `f`: then `f` splits as
  -- `(X - ζ)(X - ζ²)(X - ζ³)(X - ζ⁴)` inside `ℚ⟮ζ⟯`, so `ℚ⟮ζ⟯ = ⊤` and `[L : ℚ] = 4`!
  refine ⟨hirr_f, hdisc, fun L _ _ hsf => ?_⟩
  have hsep : f.Separable := hirr_f.separable
  have hgar_sep : IsGarlingSeparablePoly f :=
    ((mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly f).mp hsep).2.2
  have ⟨hfinL, hnormL⟩ := (corollary_1_to_theorem_9_1_iff ℚ L).mpr ⟨f, hsf⟩
  have hsepL : IsGarlingSeparableExtension ℚ L :=
    (isGarlingSeparableExtension_iff_poly_of_splittingField hf_mon.ne_zero hsf).mpr hgar_sep
  have hgal : IsGarlingGaloisExtension ℚ L := ⟨hfinL, hnormL, hsepL⟩
  have _ : IsGalois ℚ L := ((isGarlingGaloisExtension_iff ℚ L).mp hgal).2
  have _ : FiniteDimensional ℚ L := (isFiniteExtension_iff_moduleFinite ℚ L).mp hgal.1
  obtain ⟨m_L, c_L, ρ_L, hexp_L⟩ := hsf.1
  have hm_L4 : m_L = 4 := ((garlingSplitsExplicit_props hf_mon.ne_zero hexp_L).2.2.1).trans hf_deg
  subst hm_L4
  let ζ : L := ρ_L 0
  have haev_ζ : Polynomial.aeval ζ f = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hexp_L, Polynomial.eval_mul,
      Polynomial.eval_prod]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [ζ]))
  have hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    dsimp [f] at haev_ζ; simpa using haev_ζ
  have hζ5 : ζ ^ 5 = 1 := by linear_combination (ζ - 1) * hζ
  have hζ6 : ζ ^ 6 = ζ := by calc ζ ^ 6 = ζ ^ 5 * ζ := by ring
    _ = ζ := by rw [hζ5, one_mul]
  have hζ7 : ζ ^ 7 = ζ ^ 2 := by calc ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    _ = ζ ^ 2 := by rw [hζ5, one_mul]
  have hζ8 : ζ ^ 8 = ζ ^ 3 := by calc ζ ^ 8 = ζ ^ 5 * ζ ^ 3 := by ring
    _ = ζ ^ 3 := by rw [hζ5, one_mul]
  have hζ9 : ζ ^ 9 = ζ ^ 4 := by calc ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    _ = ζ ^ 4 := by rw [hζ5, one_mul]
  have hζ10 : ζ ^ 10 = 1 := by calc ζ ^ 10 = (ζ ^ 5) ^ 2 := by ring
    _ = 1 := by rw [hζ5, one_pow]
  let ν : Fin 4 → L := ![ζ, ζ ^ 2, ζ ^ 3, ζ ^ 4]
  have hexp_ν : GarlingSplitsExplicit ℚ L f 4 1 ν := by
    unfold GarlingSplitsExplicit
    rw [Fin.prod_univ_four, map_one, map_one, one_mul]
    have v0 : ν 0 = ζ := rfl
    have v1 : ν 1 = ζ ^ 2 := rfl
    have v2 : ν 2 = ζ ^ 3 := rfl
    have v3 : ν 3 = ζ ^ 4 := rfl
    rw [v0, v1, v2, v3]
    have hexpand : (Polynomial.X - Polynomial.C ζ) * (Polynomial.X - Polynomial.C (ζ ^ 2)) *
        (Polynomial.X - Polynomial.C (ζ ^ 3)) * (Polynomial.X - Polynomial.C (ζ ^ 4)) =
        Polynomial.X ^ 4 -
          Polynomial.C (ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) * Polynomial.X ^ 3 +
          Polynomial.C (ζ ^ 3 + ζ ^ 4 + 2 * ζ ^ 5 + ζ ^ 6 + ζ ^ 7) * Polynomial.X ^ 2 -
          Polynomial.C (ζ ^ 6 + ζ ^ 7 + ζ ^ 8 + ζ ^ 9) * Polynomial.X +
          Polynomial.C (ζ ^ 10) := by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
    have he1 : ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = -1 := by linear_combination hζ
    have he2 : ζ ^ 3 + ζ ^ 4 + 2 * ζ ^ 5 + ζ ^ 6 + ζ ^ 7 = 1 := by
      rw [hζ5, hζ6, hζ7]; linear_combination hζ
    have he3 : ζ ^ 6 + ζ ^ 7 + ζ ^ 8 + ζ ^ 9 = -1 := by
      rw [hζ6, hζ7, hζ8, hζ9]; linear_combination hζ
    rw [hexpand, he1, he2, he3, hζ10]
    dsimp [f]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      map_neg, map_one, one_mul]
    ring
  let Fζ : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have hζ_mem : ζ ∈ Fζ := IntermediateField.mem_adjoin_simple_self ℚ ζ
  have hν_mem : ∀ i : Fin 4, ν i ∈ Fζ := by
    intro i; fin_cases i
    · exact hζ_mem
    · exact pow_mem hζ_mem 2
    · exact pow_mem hζ_mem 3
    · exact pow_mem hζ_mem 4
  have hFζ_top : Fζ = ⊤ := by
    by_contra hne
    exact hsf.2 Fζ hne ⟨4, 1, _, garlingSplitsExplicit_of_mem_intermediateField Fζ hexp_ν hν_mem⟩
  have hmin_ζ : minpoly ℚ ζ = f :=
    (minpoly.eq_of_irreducible_of_monic hirr_f haev_ζ hf_mon).symm
  have hfin_Fζ : Module.finrank ℚ Fζ = 4 := by
    dsimp [Fζ]
    rw [IntermediateField.adjoin.finrank ⟨f, hf_mon, haev_ζ⟩, hmin_ζ, hf_deg]
  have hfin_QL : Module.finrank ℚ L = 4 := by
    rw [← IntermediateField.topEquiv.toLinearEquiv.finrank_eq, ← hFζ_top, hfin_Fζ]
  have hcard_Gal : Nat.card (GarlingPolyGaloisGroup ℚ L f) = 4 :=
    (IsGalois.card_aut_eq_finrank ℚ L).trans hfin_QL
  -- Use `exercise_14_7_repaired` (`|Γ_ℚ(f)| = 4` + `¬ ∃ d : ℚ, d ^ 2 = Δ` forces Row 4 `C₄`!):
  have hcard_roots : (garlingRootSet ℚ L f).ncard = 4 :=
    (ncard_garlingRootSet_eq_natDegree_of_separable hsep hsf).trans hf_deg
  have hfin_roots : (garlingRootSet ℚ L f).Finite := by
    by_contra hinf; rw [Set.Infinite.ncard hinf] at hcard_roots; omega
  have _ : Fintype (garlingRootSet ℚ L f) := hfin_roots.fintype
  have hfintype_card : Fintype.card (garlingRootSet ℚ L f) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_roots
  let e₀ : Fin 4 ≃ garlingRootSet ℚ L f := (Fintype.equivFinOfCardEq hfintype_card).symm
  obtain ⟨hsf_M₀, _, _, _, _⟩ :=
    section_14_4_resolvent_splitting_subfield ringChar_rat_ne_two hf_deg hsep hsf e₀
  let M₀ := IntermediateField.fixedField (viergruppe.comap (garlingRootLabellingPermHom e₀))
  have hex7_full := exercise_14_7_repaired ringChar_rat_ne_two
    ringChar_rat_ne_three hirr_f hf_deg hsf M₀ hsf_M₀
  have hex7 := hex7_full.2.2.2.2 e₀
  have hC4 : (¬ ∃ d : ℚ, d ^ 2 = garlingDiscriminant f) ∧
      (¬ Irreducible (quarticCubicResolvent f) ∧ ¬ GarlingSplitsOver ℚ ℚ (quarticCubicResolvent f)) ∧
      ¬ Irreducible (f.map (algebraMap ℚ M₀)) := by
    rcases hex7_full.1 with hc1 | hc2 | hc3 | hc4 | hc5
    · have := (hex7.2.2.2.2.2.2.1 hc1).1; omega
    · exact absurd hc2.1 hno_sq
    · exact absurd hc3.1 hno_sq
    · exact hc4
    · have := (hex7.2.2.2.2.2.2.2.2.2.2 hc5).1; omega
  exact hex7.2.2.2.2.2.2.2.2.2.1 hC4

/-- **Exercise 14.8(v)** (§14.4, printed p. 117 / PDF p. 125):
For `f₅ = x⁴ - 2 ∈ ℚ[x]`, `f₅` is irreducible over `ℚ`, `garlingDiscriminant f₅ = -2048`, and for
**every** splitting field extension `L : ℚ` of `f₅`, `|Γ_ℚ(f₅)| = 8` and
`Γ_ℚ(f₅) ≃* DihedralGroup 4` (`D₈`, the dihedral group of order `8`, `Exercise 11.6(a)`). -/
theorem exercise_14_8_v :
    let f : ℚ[X] := Polynomial.X ^ 4 - 2
    Irreducible f ∧
    garlingDiscriminant f = -2048 ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L f →
      Module.finrank ℚ L = 8 ∧
      Nat.card (GarlingPolyGaloisGroup ℚ L f) = 8 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L f ≃* DihedralGroup 4) := by
  intro f
  exact ⟨exercise_14_7_printed_rows_4_5_impossible.{0, 0}.2.1,
    exercise_14_7_printed_rows_4_5_impossible.{0, 0}.2.2.2.2.1,
    exercise_11_6.1.2⟩

/-- **Exercise 14.8** (§14.4, printed p. 117 / PDF p. 125; see `QUEUE.md` on `"Determine..."` prompt):
*"Determine the Galois groups of the following quartics in `ℚ[x]`:
(i) `x⁴ + 4x + 2`; (ii) `x⁴ + 8x - 12`; (iii) `x⁴ + 1`; (iv) `x⁴ + x³ + x² + x + 1`; (v) `x⁴ - 2`."*

- **(i) `x⁴ + 4x + 2`:** `Γ_ℚ ≃* SigmaN 4` (`Σ₄`, order `24`);
- **(ii) `x⁴ + 8x - 12`:** `Γ_ℚ ≃* SigmaN 4` (`Σ₄`, order `24`; see also
  `exercise_14_8_ii_plus_twelve_remark` for `x⁴ + 8x + 12` giving `A₄`, order `12`);
- **(iii) `x⁴ + 1`:** `Γ_ℚ ≃* viergruppe ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`
  (`N ≅ ℤ₂ × ℤ₂`, order `4`);
- **(iv) `x⁴ + x³ + x² + x + 1`:** `Γ_ℚ ≃* Multiplicative (ZMod 4)` (`C₄`, cyclic of order `4`);
- **(v) `x⁴ - 2`:** `Γ_ℚ ≃* DihedralGroup 4` (`D₈`, dihedral of order `8`). -/
theorem exercise_14_8 :
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X + Polynomial.C 2) →
      Nat.card (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X + Polynomial.C 2)) = 24 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X + Polynomial.C 2) ≃* SigmaN 4)) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X - Polynomial.C 12) →
      Nat.card (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X - Polynomial.C 12)) = 24 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X - Polynomial.C 12) ≃* SigmaN 4)) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 + 1) →
      Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1)) = 4 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1) ≃* viergruppe) ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 + 1) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L
        (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1) →
      IsCyclic (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1)) ∧
      Nat.card (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1)) = 4 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L
        (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1) ≃*
        Multiplicative (ZMod 4))) ∧
    (∀ (L : Type u) [Field L] [Algebra ℚ L],
      IsGarlingSplittingFieldExtension ℚ L (Polynomial.X ^ 4 - 2) →
      Module.finrank ℚ L = 8 ∧
      Nat.card (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2)) = 8 ∧
      Nonempty (GarlingPolyGaloisGroup ℚ L (Polynomial.X ^ 4 - 2) ≃* DihedralGroup 4)) :=
  ⟨exercise_14_8_i.2.2.2,
    exercise_14_8_ii.2.2.2,
    exercise_14_8_iii.2.2.2,
    exercise_14_8_iv.2.2,
    exercise_14_8_v.2.2⟩

end Garling.Chapter14
