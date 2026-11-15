import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Chapter 13: The theorem of the primitive element

Formalization of Chapter 13 (*The theorem of the primitive element*, printed pp. 107–109 /
PDF pp. 115–117) of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press,
1986), covering all numbered theorems, corollaries, exercises, and worked examples across §§13.1–13.3
in source order:

- **Cross-chapter supporting definitions (Chapters 7, 9, 10, 11):** literal Garling definitions and
  Mathlib equivalences for `SplitsOver` and `IsGarlingSplittingField` (§7.1, p. 60),
  `IsGarlingNormalExtension` (§9.1, p. 78), `IsGarlingSeparableIrreducible`,
  `IsGarlingSeparablePoly`, `IsGarlingSeparableElement`, and `IsGarlingSeparableExtension`
  (§10.1, p. 82), `IsGarlingGaloisExtension` (§10.3, p. 84), and `GarlingGaloisGroup`,
  `garlingFixedField`, and `GarlingPolyGaloisGroup` (§§11.1–11.2, pp. 91, 94).
- **§13.1 A criterion in terms of intermediate fields** (printed pp. 107–108, PDF pp. 115–116):
  `Theorem 13.1`, `Exercise 13.1` (proved directly via `Garling.Chapter01.exercise_1_17`), and
  `Exercise 13.2`.
- **§13.2 The theorem of the primitive element** (printed pp. 108–109, PDF pp. 116–117):
  `Theorem 13.2`, `Corollary` [to `Theorem 13.2`], `Exercise 13.3` (parts `(i)`–`(iv)`, including
  the full projective-plane classification `ℙ²(K)` for `p = 2`), `Exercise 13.4` (`if` direction,
  counterexamples to the false printed `only if` direction, and repaired characterizations), and
  `Exercise 13.5`.
- **§13.3 An example** (printed p. 109, PDF p. 117): worked biquadratic example
  `ℚ(√2, √3) : ℚ` as a splitting field extension for `f = x⁴ - 5x² + 6 = (x² - 2)(x² - 3)`, the
  `2 × 4` Galois-action table, `Γ_ℚ(f) ≅ ℤ₂ × ℤ₂`, the three order-`2` subgroups and fixed fields
  `ℚ(√3)`, `ℚ(√2)`, `ℚ(√6)`, and the primitive-element characterization.
-/

namespace Garling.Chapter13

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03 Garling.Chapter04 Garling.Chapter05
open scoped BigOperators Polynomial IntermediateField LinearAlgebra.Projectivization

/-! ## Cross-Chapter Supporting Definitions (Chapters 7, 9, 10, 11) -/

/-- Garling's definition that `f ∈ K[x]` *splits over `L`* (§7.1, printed p. 60 / PDF p. 68):
we can write `f = λ(x - α₁)⋯(x - α_n)` where `α₁, …, α_n ∈ L` and `λ ∈ K`. -/
def SplitsOver (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) : Prop :=
  ∃ (n : ℕ) (α : Fin n → L) (lam : K),
    f.map (algebraMap K L) =
      Polynomial.C (algebraMap K L lam) * ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))

private lemma list_linear_prod_eq_fin_prod {L : Type*} [CommRing L] :
    ∀ l : List L,
      ∃ (n : ℕ) (α : Fin n → L),
        (l.map fun a => Polynomial.X - Polynomial.C a).prod =
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))
  | [] => ⟨0, Fin.elim0, by simp⟩
  | a :: l => by
    obtain ⟨n, α, hα⟩ := list_linear_prod_eq_fin_prod l
    refine ⟨n + 1, Fin.cons a α, ?_⟩
    rw [List.map_cons, List.prod_cons, Fin.prod_univ_succ, hα]
    simp

/-- Equivalence between Garling's `SplitsOver K L f` (§7.1, p. 60) and Mathlib's
`(f.map (algebraMap K L)).Splits`, unconditionally across all `f ∈ K[X]` (including `0` and
constants). -/
theorem splitsOver_iff_splits (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) :
    SplitsOver K L f ↔ (f.map (algebraMap K L)).Splits := by
  constructor
  · rintro ⟨n, α, lam, hmap⟩
    rw [hmap]
    exact Polynomial.Splits.mul (Polynomial.Splits.C _)
      (Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C (α i))
  · intro hsp
    by_cases hf0 : f = 0
    · refine ⟨0, Fin.elim0, 0, ?_⟩
      simp [hf0]
    · have heq := Polynomial.Splits.eq_prod_roots hsp
      have hlc : (f.map (algebraMap K L)).leadingCoeff = algebraMap K L f.leadingCoeff :=
        Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective f
      obtain ⟨l, hl⟩ := Quotient.exists_rep ((f.map (algebraMap K L)).roots)
      obtain ⟨n, α, hα⟩ := list_linear_prod_eq_fin_prod l
      refine ⟨n, α, f.leadingCoeff, ?_⟩
      rw [heq, hlc, ← hα]
      congr 1
      rw [← hl]
      rfl

/-- Garling's definition of a *splitting field extension* `L : K` for `f ∈ K[x]` over `K`
(§7.1, printed p. 60 / PDF p. 68): `f` splits over `L`, and there is no proper subfield `L'` of `L`
containing `K` such that `f` splits over `L'`. -/
def IsGarlingSplittingField (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) : Prop :=
  SplitsOver K L f ∧ ∀ L' : IntermediateField K L, L' ≠ ⊤ → ¬ SplitsOver K L' f

/-- Equivalence between `IntermediateField K L` and subfields of `L` containing the image of `K`. -/
def intermediateFieldOrderIsoSubfieldsContaining (K L : Type*) [Field K] [Field L]
    [Algebra K L] :
    IntermediateField K L ≃o {F : Subfield L // Set.range (algebraMap K L) ⊆ (F : Set L)} where
  toFun M := ⟨M.toSubfield, by rintro _ ⟨k, rfl⟩; exact M.algebraMap_mem k⟩
  invFun F :=
    { F.1 with
      algebraMap_mem' := fun k => F.2 ⟨k, rfl⟩ }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_rel_iff' := Iff.rfl

/-- Unconditional equivalence between Garling's `IsGarlingSplittingField K L f` (§7.1, p. 60) and
Mathlib's `Polynomial.IsSplittingField K L f` across all `f ∈ K[X]`. -/
theorem isGarlingSplittingField_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (f : K[X]) :
    IsGarlingSplittingField K L f ↔ Polynomial.IsSplittingField K L f := by
  rw [isSplittingField_iff_intermediateField]
  constructor
  · rintro ⟨hsp, hmin⟩
    have hsp' : (f.map (algebraMap K L)).Splits := (splitsOver_iff_splits K L f).mp hsp
    refine ⟨hsp', ?_⟩
    by_contra hne
    have hsub_sp : (f.map (algebraMap K (IntermediateField.adjoin K (f.rootSet L)))).Splits :=
      (IntermediateField.adjoin_rootSet_isSplittingField hsp').splits
    exact hmin (IntermediateField.adjoin K (f.rootSet L)) hne
      ((splitsOver_iff_splits K _ f).mpr hsub_sp)
  · rintro ⟨hsp', hadj⟩
    refine ⟨(splitsOver_iff_splits K L f).mpr hsp', fun L' hne hspL' => hne ?_⟩
    have hspL'' : (f.map (algebraMap K L')).Splits := (splitsOver_iff_splits K L' f).mp hspL'
    have hmem : ∀ x ∈ f.rootSet L, x ∈ L' := (IntermediateField.splits_iff_mem hsp').mp hspL''
    rw [eq_top_iff, ← hadj, IntermediateField.adjoin_le_iff]
    exact hmem

/-- Garling's definition of a *normal* extension `L : K` (§9.1, printed p. 78 / PDF p. 86):
`L : K` is algebraic and whenever `f` is an irreducible polynomial in `K[x]`, either `f` splits over
`L` or `f` has no roots in `L`. -/
def IsGarlingNormalExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsAlgebraicExtension K L ∧
    ∀ f : K[X], Irreducible f → SplitsOver K L f ∨ ¬ ∃ α : L, Polynomial.aeval α f = 0

/-- Equivalence between Garling's `IsGarlingNormalExtension K L` (§9.1, p. 78) and Mathlib's
`Normal K L`. -/
theorem isGarlingNormalExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingNormalExtension K L ↔ Normal K L := by
  constructor
  · rintro ⟨halg, hnorm⟩
    rw [normal_iff]
    intro x
    have hx_int : IsIntegral K x := (isGarlingAlgebraic_iff_isIntegral K x).mp (halg x)
    refine ⟨hx_int, ?_⟩
    have hirr : Irreducible (minpoly K x) := minpoly.irreducible hx_int
    rcases hnorm (minpoly K x) hirr with hsp | hno
    · exact (splitsOver_iff_splits K L (minpoly K x)).mp hsp
    · exfalso
      exact hno ⟨x, minpoly.aeval K x⟩
  · intro hN
    refine ⟨fun x => (hN.isIntegral x).isAlgebraic, fun f hfirr => ?_⟩
    by_cases hroot : ∃ α : L, Polynomial.aeval α f = 0
    · left
      obtain ⟨α, hα⟩ := hroot
      have hα_int : IsIntegral K α := hN.isIntegral α
      have hdvd : minpoly K α ∣ f := minpoly.dvd K α hα
      have hirr_m : Irreducible (minpoly K α) := minpoly.irreducible hα_int
      have hassoc : Associated (minpoly K α) f := hirr_m.associated_of_dvd hfirr hdvd
      obtain ⟨u, rfl⟩ := hassoc
      have hu_poly : ∃ c : Kˣ, (u : K[X]) = Polynomial.C (c : K) := by
        obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp u.isUnit
        obtain ⟨cu, hcu⟩ := hc.1
        exact ⟨cu, by rw [← hc.2, hcu]⟩
      obtain ⟨c, hc⟩ := hu_poly
      rw [splitsOver_iff_splits, hc, Polynomial.map_mul, Polynomial.map_C]
      exact Polynomial.Splits.mul (hN.splits α) (Polynomial.Splits.C _)
    · exact Or.inr hroot

/-- Garling's definition that an irreducible polynomial `f ∈ K[x]` of degree `n` is *separable*
over `K` (§10.1, printed p. 82 / PDF p. 90): `f` has `n` distinct roots in its splitting field. -/
def IsGarlingSeparableIrreducible {K : Type*} [Field K] (f : K[X]) : Prop :=
  Irreducible f ∧ Fintype.card (f.rootSet f.SplittingField) = f.natDegree

/-- Equivalence between Garling's distinct-roots criterion for irreducible `f ∈ K[X]`
(§10.1, p. 82) and Mathlib's `Polynomial.Separable f` (verified simultaneously across *every*
splitting field extension `L` of `f`). -/
theorem isGarlingSeparableIrreducible_iff_separable {K : Type*} [Field K] {f : K[X]}
    (hf : Irreducible f) :
    IsGarlingSeparableIrreducible f ↔ f.Separable := by
  classical
  let S := f.SplittingField
  have hf0 : f ≠ 0 := hf.ne_zero
  have hsp : (f.map (algebraMap K S)).Splits := Polynomial.SplittingField.splits f
  have hmap0 : f.map (algebraMap K S) ≠ 0 := Polynomial.map_ne_zero hf0
  have hcard_roots : (f.map (algebraMap K S)).roots.card = f.natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap K S)]
    exact hsp.natDegree_eq_card_roots.symm
  have hcard_rootSet :
      Fintype.card (f.rootSet S) = (f.map (algebraMap K S)).roots.toFinset.card := by
    rw [← Nat.card_eq_fintype_card, Polynomial.rootSet_def, Polynomial.aroots_def,
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  constructor
  · rintro ⟨_, hcard⟩
    rw [hcard_rootSet, ← hcard_roots] at hcard
    have hnodup : (f.map (algebraMap K S)).roots.Nodup :=
      Multiset.toFinset_card_eq_card_iff_nodup.mp hcard
    have heq := Polynomial.Splits.eq_prod_roots hsp
    have hsep_prod :
        (((f.map (algebraMap K S)).roots).map fun a : S => Polynomial.X - Polynomial.C a).prod.Separable := by
      have hfin_prod :
          (∏ a ∈ (f.map (algebraMap K S)).roots.toFinset, (Polynomial.X - Polynomial.C a)) =
            (((f.map (algebraMap K S)).roots).map fun a : S => Polynomial.X - Polynomial.C a).prod := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
      rw [← hfin_prod]
      refine Polynomial.separable_prod' (fun x _ y _ hxy => ?_) (fun x _ => Polynomial.separable_X_sub_C)
      exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy
    have hlc_unit : IsUnit (Polynomial.C (f.map (algebraMap K S)).leadingCoeff) :=
      (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hmap0)).map Polynomial.C
    have hsep_map : (f.map (algebraMap K S)).Separable := by
      rw [heq]
      exact Polynomial.Separable.unit_mul hlc_unit hsep_prod
    exact (Polynomial.separable_map (algebraMap K S)).mp hsep_map
  · intro hsep
    refine ⟨hf, ?_⟩
    rw [hcard_rootSet, ← hcard_roots]
    exact Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap K S)).mpr hsep))

/-- Garling's definition that an arbitrary polynomial `f ∈ K[x]` is *separable* over `K`
(§10.1, printed p. 82 / PDF p. 90): each of its irreducible factors in `K[x]` is separable.
Note (`BRIEF.md` Flag 5): unlike Mathlib's `Polynomial.Separable`, this allows repeated separable
irreducible factors (such as `g = m_{α₁}⋯m_{α_n}` in the proof of `Theorem 13.2`). -/
def IsGarlingSeparablePoly {K : Type*} [Field K] (f : K[X]) : Prop :=
  ∀ p : K[X], Irreducible p → p ∣ f → IsGarlingSeparableIrreducible p

theorem isGarlingSeparablePoly_iff {K : Type*} [Field K] (f : K[X]) :
    IsGarlingSeparablePoly f ↔ ∀ p : K[X], Irreducible p → p ∣ f → p.Separable := by
  refine forall_congr' fun p => imp_congr_right fun hp => forall_congr' fun _ => ?_
  exact isGarlingSeparableIrreducible_iff_separable hp

theorem isGarlingSeparablePoly_of_irreducible_iff {K : Type*} [Field K] {f : K[X]}
    (hf : Irreducible f) :
    IsGarlingSeparablePoly f ↔ f.Separable := by
  rw [isGarlingSeparablePoly_iff]
  constructor
  · intro h
    exact h f hf dvd_rfl
  · intro hsep p hp hdvd
    exact (hp.associated_of_dvd hf hdvd).symm.separable hsep

/-- Exact relationship between Mathlib's `Polynomial.Separable` and Garling's §10.1
`IsGarlingSeparablePoly` (`BRIEF.md` Flag 5): `f.Separable` holds if and only if `f ≠ 0`, `f` is
squarefree, and `IsGarlingSeparablePoly f`. -/
theorem mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly {K : Type*} [Field K]
    (f : K[X]) :
    f.Separable ↔ f ≠ 0 ∧ Squarefree f ∧ IsGarlingSeparablePoly f := by
  rw [isGarlingSeparablePoly_iff]
  constructor
  · intro hsep
    exact ⟨hsep.ne_zero, hsep.squarefree, fun p _ hdvd => hsep.of_dvd hdvd⟩
  · rintro ⟨hf0, hsq, hfactors⟩
    induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n ih =>
      by_cases hunit : IsUnit f
      · obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hunit
        rw [← hc.2]
        exact (Polynomial.separable_C c).mpr hc.1
      · obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hunit hf0
        obtain ⟨q, rfl⟩ := hp_dvd
        have hp0 : p ≠ 0 := hp_irr.ne_zero
        have hq0 : q ≠ 0 := right_ne_zero_of_mul hf0
        have hp_sep : p.Separable := hfactors p hp_irr (dvd_mul_right p q)
        have hq_sq : Squarefree q := hsq.of_mul_right
        have hq_factors : ∀ r : K[X], Irreducible r → r ∣ q → r.Separable :=
          fun r hr hrdvd => hfactors r hr (dvd_mul_of_dvd_right hrdvd p)
        have hp_deg : 0 < p.natDegree := hp_irr.natDegree_pos
        have hq_lt : q.natDegree < n := by
          have hmul : (p * q).natDegree = p.natDegree + q.natDegree :=
            Polynomial.natDegree_mul hp0 hq0
          omega
        have hq_sep : q.Separable := ih q.natDegree hq_lt q hq0 hq_sq hq_factors rfl
        have hcop : IsCoprime p q := by
          refine (Irreducible.coprime_iff_not_dvd hp_irr).mpr fun hdvd => hp_irr.not_isUnit ?_
          obtain ⟨r, rfl⟩ := hdvd
          exact hsq p ⟨r, by ring⟩
        exact hp_sep.mul hq_sep hcop

/-- Concrete witness for `BRIEF.md` Flag 5: `(x : ℚ[X]) ^ 2` is separable in Garling's §10.1 sense
(`IsGarlingSeparablePoly`) because its sole monic irreducible factor `x` is separable, whereas it is
**not** separable in Mathlib's squarefree sense (`¬ ((X : ℚ[X]) ^ 2).Separable`). -/
theorem x_sq_garlingSeparable_not_mathlibSeparable :
    IsGarlingSeparablePoly ((Polynomial.X : ℚ[X]) ^ 2) ∧
      ¬ ((Polynomial.X : ℚ[X]) ^ 2).Separable := by
  refine ⟨?_, ?_⟩
  · rw [isGarlingSeparablePoly_iff]
    intro p hp _
    exact hp.separable
  · intro hsep
    have h1 := (hsep.of_pow Polynomial.not_isUnit_X (by decide : (2 : ℕ) ≠ 0)).2
    omega

/-- Garling's definition that an element `α ∈ L` is *separable* over `K` (§10.1, printed p. 82 /
PDF p. 90): `α` is algebraic over `K` and its minimal polynomial over `K` is separable. -/
def IsGarlingSeparableElement (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : Prop :=
  IsGarlingAlgebraic K α ∧ IsGarlingSeparablePoly (minpoly K α)

theorem isGarlingSeparableElement_iff (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) :
    IsGarlingSeparableElement K α ↔ IsSeparable K α := by
  constructor
  · rintro ⟨halg, hsep⟩
    have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp halg
    exact (isGarlingSeparablePoly_of_irreducible_iff (minpoly.irreducible hint)).mp hsep
  · intro hsep
    have hint : IsIntegral K α := hsep.isIntegral
    exact ⟨hint.isAlgebraic,
      (isGarlingSeparablePoly_of_irreducible_iff (minpoly.irreducible hint)).mpr hsep⟩

/-- Garling's definition that an extension `L : K` is *separable* (§10.1, printed p. 82 /
PDF p. 90): every element `α ∈ L` is separable over `K`. -/
def IsGarlingSeparableExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ α : L, IsGarlingSeparableElement K α

theorem isGarlingSeparableExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingSeparableExtension K L ↔ Algebra.IsSeparable K L := by
  rw [Algebra.isSeparable_def]
  exact forall_congr' fun α => isGarlingSeparableElement_iff K α

/-- Garling's definition of a *Galois extension* `L : K` (§10.3, printed p. 84 / PDF p. 92):
an extension which is **finite**, normal, and separable (`BRIEF.md` Flag 2). -/
def IsGarlingGaloisExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsFiniteExtension K L ∧ IsGarlingNormalExtension K L ∧ IsGarlingSeparableExtension K L

/-- Equivalence between Garling's `IsGarlingGaloisExtension K L` (§10.3, p. 84) and
`FiniteDimensional K L ∧ IsGalois K L`. -/
theorem isGarlingGaloisExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingGaloisExtension K L ↔ FiniteDimensional K L ∧ IsGalois K L := by
  rw [IsGarlingGaloisExtension, isFiniteExtension_iff_moduleFinite, isGarlingNormalExtension_iff,
    isGarlingSeparableExtension_iff, isGalois_iff]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨h1, h2, h3⟩⟩

/-- Garling's *Galois group* `Γ(L : K)` of an extension `L : K` (§11.1, printed p. 91 / PDF p. 99):
the group of automorphisms of `L` fixing `K`. -/
abbrev GarlingGaloisGroup (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- Garling's *fixed field* `ϕ(A)` of a subset `A ⊆ Γ(L : K)` (§11.1, printed p. 91 / PDF p. 99),
viewed as an `IntermediateField K L`. -/
def garlingFixedField {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set (GarlingGaloisGroup K L)) : IntermediateField K L :=
  { ({ carrier := {x : L | ∀ σ ∈ A, σ x = x}
       add_mem' := fun ha hb σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]
       zero_mem' := fun _ _ => map_zero _
       neg_mem' := fun ha σ hσ => by rw [map_neg, ha σ hσ]
       mul_mem' := fun ha hb σ hσ => by rw [map_mul, ha σ hσ, hb σ hσ]
       one_mem' := fun _ _ => map_one _
       inv_mem' := fun _ ha σ hσ => by rw [map_inv₀, ha σ hσ] } : Subfield L) with
    algebraMap_mem' := fun k σ _ => σ.commutes k }

theorem garlingFixedField_coe_subgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (GarlingGaloisGroup K L)) :
    garlingFixedField (H : Set (GarlingGaloisGroup K L)) = IntermediateField.fixedField H := by
  ext x
  simp [garlingFixedField, IntermediateField.mem_fixedField_iff]

/-! ## §13.1 A criterion in terms of intermediate fields (printed pp. 107–108, PDF pp. 115–116) -/

/-- Degenerate `r = 0` base case overlooked in Garling's p. 107 proof (`BRIEF.md` Flag 3):
any trivial extension (`(⊥ : IntermediateField K L) = ⊤`, e.g. `L = K`) is simple, witnessed by
`K(0) = L`. -/
theorem isSimpleExtension_of_bot_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : (⊥ : IntermediateField K L) = ⊤) : IsSimpleExtension K L :=
  ⟨0, by rw [IntermediateField.adjoin_zero, h]⟩

theorem isSimpleExtension_self (K : Type*) [Field K] : IsSimpleExtension K K :=
  isSimpleExtension_of_bot_eq_top (Subsingleton.elim _ _)

/-- Garling's linear-combination reduction in the proof of `Theorem 13.1` (printed p. 107 /
PDF p. 115): over an infinite field `K`, if there are only finitely many intermediate fields between
`K` and `L`, then for any `α₁, α₂ ∈ L` there exist `β ≠ γ` in `K` with
`K(α₁ + β α₂) = K(α₁ + γ α₂)` and hence `K(α₁, α₂) = K(α₁ + β α₂)`. -/
theorem adjoin_pair_eq_linear_comb_of_finite_intermediateField
    {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    [Finite (IntermediateField K L)] (α₁ α₂ : L) :
    ∃ β : K,
      IntermediateField.adjoin K ({α₁, α₂} : Set L) =
        IntermediateField.adjoin K ({α₁ + algebraMap K L β * α₂} : Set L) := by
  let F : K → IntermediateField K L :=
    fun β => IntermediateField.adjoin K ({α₁ + algebraMap K L β * α₂} : Set L)
  obtain ⟨β, γ, hne, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  refine ⟨β, le_antisymm ?_ ?_⟩
  · rw [IntermediateField.adjoin_le_iff]
    have hβ_mem : α₁ + algebraMap K L β * α₂ ∈ F β :=
      IntermediateField.mem_adjoin_simple_self K _
    have hγ_mem : α₁ + algebraMap K L γ * α₂ ∈ F β := by
      rw [hF]
      exact IntermediateField.mem_adjoin_simple_self K _
    have hdiff : algebraMap K L (β - γ) * α₂ ∈ F β := by
      have hsub := (F β).sub_mem hβ_mem hγ_mem
      convert hsub using 1
      rw [map_sub]
      ring
    have hne_map : algebraMap K L (β - γ) ≠ 0 := by
      rw [map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective]
      exact sub_ne_zero.mpr hne
    have hα₂_mem : α₂ ∈ F β := by
      have hmul := (F β).mul_mem ((F β).inv_mem ((F β).algebraMap_mem (β - γ))) hdiff
      rwa [inv_mul_cancel_left₀ hne_map] at hmul
    have hα₁_mem : α₁ ∈ F β := by
      have hsub := (F β).sub_mem hβ_mem ((F β).mul_mem ((F β).algebraMap_mem β) hα₂_mem)
      convert hsub using 1
      ring
    rintro x (rfl | rfl)
    · exact hα₁_mem
    · exact hα₂_mem
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h1 : α₁ ∈ IntermediateField.adjoin K ({α₁, α₂} : Set L) :=
      IntermediateField.subset_adjoin K {α₁, α₂} (Set.mem_insert α₁ {α₂})
    have h2 : α₂ ∈ IntermediateField.adjoin K ({α₁, α₂} : Set L) :=
      IntermediateField.subset_adjoin K {α₁, α₂} (Set.mem_insert_of_mem α₁ rfl)
    exact (IntermediateField.adjoin K ({α₁, α₂} : Set L)).add_mem h1
      ((IntermediateField.adjoin K ({α₁, α₂} : Set L)).mul_mem
        ((IntermediateField.adjoin K ({α₁, α₂} : Set L)).algebraMap_mem β) h2)

/-- Garling's coefficient-determination lemma in the converse direction of `Theorem 13.1`
(printed p. 108 / PDF p. 116): if `L = K(α)` is simple and algebraic over `K`, then every
intermediate field `F` equals `K(a₀, …, a_r)` where `m_F = ∑ a_i x^i` is the minimal polynomial of
`α` over `F`. -/
theorem intermediateField_eq_adjoin_minpoly_coeffs
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {α : L} (hα : IntermediateField.adjoin K ({α} : Set L) = ⊤) (F : IntermediateField K L) :
    F = IntermediateField.adjoin K (((minpoly F α).map (algebraMap F L)).coeffs : Set L) := by
  classical
  have _ : FiniteDimensional K L := Field.FiniteDimensional.of_exists_primitive_element K L ⟨α, hα⟩
  exact (IntermediateField.adjoin_minpoly_coeff_of_exists_primitive_element K hα F).symm

/-- **Theorem 13.1** (§13.1, printed p. 107 / PDF p. 115; proof pp. 107–108 / PDF pp. 115–116):
An algebraic extension `L : K` is simple if and only if there are only finitely many intermediate
fields. -/
theorem theorem_13_1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) :
    IsSimpleExtension K L ↔ Finite (IntermediateField K L) := by
  have _ : Algebra.IsAlgebraic K L := (isAlgebraicExtension_iff K L).mp halg
  constructor
  · intro hsimple
    exact Field.finite_intermediateField_of_exists_primitive_element K L hsimple
  · intro _
    exact Field.exists_primitive_element_of_finite_intermediateField K L ⊤

/-- Typeclass-idiomatic companion to `theorem_13_1` under `[Algebra.IsAlgebraic K L]`. -/
theorem theorem_13_1_algebraic (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    IsSimpleExtension K L ↔ Finite (IntermediateField K L) :=
  theorem_13_1 ((isAlgebraicExtension_iff K L).mpr inferInstance)

/-- Subfield-lattice companion to `theorem_13_1`: `L : K` algebraic is simple iff the set of
subfields of `L` containing `K` (`Set.range (algebraMap K L)`) is finite. -/
theorem theorem_13_1_subfields {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) :
    IsSimpleExtension K L ↔
      ({F : Subfield L | Set.range (algebraMap K L) ⊆ (F : Set L)}).Finite := by
  rw [theorem_13_1 halg, ← Set.finite_coe_iff]
  exact Equiv.finite_iff (intermediateFieldOrderIsoSubfieldsContaining K L).toEquiv

/-- **Exercise 13.1** (§13.1, printed p. 108 / PDF p. 116):
Use `Exercise 1.17` (`Garling.Chapter01.exercise_1_17`) to give another proof that `L : K` is
simple if `K` is infinite and there are only finitely many intermediate fields.
(Note `BRIEF.md` Flag 4: holds literally as printed without any algebraicity assumption.) -/
theorem exercise_13_1 {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
    (hfin : Finite (IntermediateField K L)) :
    IsSimpleExtension K L := by
  classical
  have _ : Finite {F : IntermediateField K L // F ≠ ⊤} := Subtype.finite
  let _ : Fintype {F : IntermediateField K L // F ≠ ⊤} := Fintype.ofFinite _
  let n := Fintype.card {F : IntermediateField K L // F ≠ ⊤}
  let e : Fin n ≃ {F : IntermediateField K L // F ≠ ⊤} := (Fintype.equivFin _).symm
  let U : Fin n → Submodule K L := fun i => (e i).1.toSubmodule
  have hproper : ∀ i : Fin n, U i ≠ ⊤ := by
    intro i htop
    apply (e i).2
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ U i := by rw [htop]; trivial
    exact hx
  have hnot_univ := Garling.Chapter01.exercise_1_17 n U hproper
  have hex : ∃ α : L, ∀ i : Fin n, α ∉ U i := by
    by_contra hall
    push Not at hall
    apply hnot_univ
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
    exact hall x
  obtain ⟨α, hα⟩ := hex
  refine ⟨α, ?_⟩
  by_contra hne
  let idx : Fin n := e.symm ⟨IntermediateField.adjoin K ({α} : Set L), hne⟩
  have hmem : α ∈ U idx := by
    have heq : (e idx).1 = IntermediateField.adjoin K ({α} : Set L) := by
      simp [idx]
    change α ∈ (e idx).1
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self K α
  exact hα idx hmem

/-- Garling's phrasing that `L : K` (`K(t) : K`) is a *simple transcendental extension*
(§13.1, Exercise 13.2, p. 108; cf. Exercise 7.3, p. 62 and `BRIEF.md` Flag 6): `L = K(t)` for some
`t ∈ L` transcendental over `K`. -/
def IsSimpleTranscendentalExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ t : L, IsGarlingTranscendental K t ∧ IntermediateField.adjoin K ({t} : Set L) = ⊤

/-- **Exercise 13.2** (§13.1, printed p. 108 / PDF p. 116):
Suppose that `L = K(t) : K` is a simple transcendental extension. Then there are infinitely many
intermediate fields. (More generally, any extension containing a transcendental element over `K`
has infinitely many intermediate fields `K(t^n)`.) -/
theorem exercise_13_2_of_transcendental {K L : Type*} [Field K] [Field L] [Algebra K L]
    {t : L} (ht : IsGarlingTranscendental K t) :
    Infinite (IntermediateField K L) := by
  refine Infinite.of_injective (fun n : ℕ => IntermediateField.adjoin K ({t ^ n} : Set L)) ?_
  intro m n heq
  by_contra hmn
  exact ht (Field.isAlgebraic_of_adjoin_eq_adjoin K L hmn heq)

theorem exercise_13_2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (htrans : IsSimpleTranscendentalExtension K L) :
    Infinite (IntermediateField K L) := by
  obtain ⟨t, ht, _⟩ := htrans
  exact exercise_13_2_of_transcendental ht

/-- Intermediate-field form of `Exercise 13.2`: for any transcendental element `t ∈ L` over `K`,
the simple transcendental extension `K(t) : K` (`K⟮t⟯`) has infinitely many intermediate fields. -/
theorem exercise_13_2_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    {t : L} (ht : IsGarlingTranscendental K t) :
    Infinite (IntermediateField K K⟮t⟯) := by
  have ht' : IsGarlingTranscendental K (IntermediateField.AdjoinSimple.gen K t) := by
    intro halg
    have hinj : Function.Injective (algebraMap K⟮t⟯ L) := K⟮t⟯.val.injective
    have halgL : IsAlgebraic K (algebraMap K⟮t⟯ L (IntermediateField.AdjoinSimple.gen K t)) :=
      (isAlgebraic_algebraMap_iff hinj).mpr halg
    rw [IntermediateField.AdjoinSimple.algebraMap_gen] at halgL
    exact ht halgL
  exact exercise_13_2_of_transcendental ht'

/-- Concrete `RatFunc K` form of `Exercise 13.2`: over *every* field `K`, `RatFunc K` (`K(X)`) is a
simple transcendental extension of `K` and has infinitely many intermediate fields. -/
theorem exercise_13_2_ratFunc (K : Type*) [Field K] :
    IsSimpleTranscendentalExtension K (RatFunc K) ∧
      Infinite (IntermediateField K (RatFunc K)) := by
  have ht : IsGarlingTranscendental K (RatFunc.X : RatFunc K) := by
    rintro ⟨p, hp0, hev⟩
    apply hp0
    have hX : (RatFunc.X : RatFunc K) = algebraMap K[X] (RatFunc K) Polynomial.X :=
      RatFunc.algebraMap_X.symm
    rw [hX, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply] at hev
    exact RatFunc.algebraMap_injective K (hev.trans (map_zero _).symm)
  exact ⟨⟨RatFunc.X, ht, RatFunc.adjoin_X⟩, exercise_13_2_of_transcendental ht⟩

/-! ## §13.2 The theorem of the primitive element (printed pp. 108–109, PDF pp. 116–117) -/

/-- Garling's *Galois group of a polynomial* `Γ_K(f)` (§11.2, printed p. 94 / PDF p. 102): when
`L : K` is a splitting field extension for `f ∈ K[x]` over `K`, `Γ_K(f) = Γ(L : K)`. -/
abbrev GarlingPolyGaloisGroup (K L : Type*) [Field K] [Field L] [Algebra K L] (_f : K[X]) :=
  GarlingGaloisGroup K L

/-- Step 1 of Garling's proof of `Theorem 13.2` (printed p. 108 / PDF p. 116): if `α₁, …, α_n`
are separable over `K`, then `g = m_{α₁}⋯m_{α_n}` is monic (hence `g ≠ 0`) and separable over `K`
in Garling's §10.1 sense (`IsGarlingSeparablePoly g`), even when conjugate generators repeat minimal
polynomials (`BRIEF.md` Flag 5). -/
theorem isGarlingSeparablePoly_prod_minpoly {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {α : Fin n → L} (hsep : ∀ i : Fin n, IsGarlingSeparableElement K (α i)) :
    (∏ i : Fin n, minpoly K (α i)).Monic ∧
      IsGarlingSeparablePoly (∏ i : Fin n, minpoly K (α i)) := by
  have hint : ∀ i : Fin n, IsIntegral K (α i) :=
    fun i => ((isGarlingSeparableElement_iff K (α i)).mp (hsep i)).isIntegral
  refine ⟨Polynomial.monic_prod_of_monic _ _ fun i _ => minpoly.monic (hint i), ?_⟩
  rw [isGarlingSeparablePoly_iff]
  intro p hp hdvd
  obtain ⟨i, _, hi⟩ := hp.prime.exists_mem_finset_dvd hdvd
  have hmi_irr : Irreducible (minpoly K (α i)) := minpoly.irreducible (hint i)
  have hmi_sep : (minpoly K (α i)).Separable := (isGarlingSeparableElement_iff K (α i)).mp (hsep i)
  exact (hp.associated_of_dvd hmi_irr hi).symm.separable hmi_sep

/-- Step 2 of Garling's proof of `Theorem 13.2` (printed p. 108 / PDF p. 116): if `α₁, …, α_n`
generate `L` over `K` and are roots of `g ∈ K[X]` (`g ≠ 0`), and `N : L` is a splitting field
extension for `g` over `L`, then `N : K` is a splitting field extension for `g` over `K`. -/
theorem isGarlingSplittingField_tower_of_generators
    {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    {n : ℕ} {α : Fin n → L} (hgen : IntermediateField.adjoin K (Set.range α) = ⊤)
    {g : K[X]} (hg0 : g ≠ 0) (hroots : ∀ i : Fin n, Polynomial.aeval (α i) g = 0)
    (hNL : IsGarlingSplittingField L N (g.map (algebraMap K L))) :
    IsGarlingSplittingField K N g := by
  have hNL' : Polynomial.IsSplittingField L N (g.map (algebraMap K L)) :=
    (isGarlingSplittingField_iff L N _).mp hNL
  rw [isGarlingSplittingField_iff, isSplittingField_iff_intermediateField]
  have hspN : (g.map (algebraMap K N)).Splits := by
    rw [IsScalarTower.algebraMap_eq K L N, ← Polynomial.map_map]
    exact hNL'.splits
  refine ⟨hspN, ?_⟩
  let M : IntermediateField K N := IntermediateField.adjoin K (g.rootSet N)
  have hα_in_M : ∀ i : Fin n, algebraMap L N (α i) ∈ M := by
    intro i
    apply IntermediateField.subset_adjoin K (g.rootSet N)
    rw [Polynomial.mem_rootSet_of_ne hg0]
    have haev : Polynomial.aeval (algebraMap L N (α i)) g =
        algebraMap L N (Polynomial.aeval (α i) g) := by
      simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K L N) (α i) g)
    rw [haev, hroots i, map_zero]
  have hL_in_M : ∀ x : L, algebraMap L N x ∈ M := by
    let M_pre : IntermediateField K L :=
      M.comap (IsScalarTower.toAlgHom K L N)
    have htop : M_pre = ⊤ := by
      rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact hα_in_M i
    intro x
    have hx : x ∈ M_pre := by rw [htop]; trivial
    exact hx
  let M_L : IntermediateField L N :=
    { M.toSubfield with
      algebraMap_mem' := hL_in_M }
  have hrootSet_eq : (g.map (algebraMap K L)).rootSet N = g.rootSet N := by
    ext z
    simp [Polynomial.mem_rootSet_of_ne hg0]
  have hML_top : M_L = ⊤ := by
    have hadjL : IntermediateField.adjoin L ((g.map (algebraMap K L)).rootSet N) = ⊤ :=
      (isSplittingField_iff_intermediateField.mp hNL').2
    rw [eq_top_iff, ← hadjL, IntermediateField.adjoin_le_iff, hrootSet_eq]
    intro z hz
    exact IntermediateField.subset_adjoin K (g.rootSet N) hz
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ M_L := by rw [hML_top]; trivial
  exact hz

/-- Step 3 of Garling's proof of `Theorem 13.2` (printed p. 108 / PDF p. 116, citing `Theorem 9.1`
and `Corollary 3 to Theorem 10.3`): if `g ∈ K[X]` (`g ≠ 0`) is separable over `K` in Garling's §10.1
sense and `N : K` is a splitting field extension for `g` over `K`, then `N : K` is a Galois
extension (`IsGarlingGaloisExtension K N`). -/
theorem isGarlingGaloisExtension_of_splittingField
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    {g : K[X]} (hg0 : g ≠ 0) (hgsep : IsGarlingSeparablePoly g)
    (hsplit : IsGarlingSplittingField K N g) :
    IsGarlingGaloisExtension K N := by
  have hsp : Polynomial.IsSplittingField K N g := (isGarlingSplittingField_iff K N g).mp hsplit
  have _ : FiniteDimensional K N := Polynomial.IsSplittingField.finiteDimensional N g
  have hnorm : Normal K N := Normal.of_isSplittingField g
  have hroot_sep : ∀ x ∈ (g.rootSet N : Set N), IsSeparable K x := by
    intro x hx
    have haev : Polynomial.aeval x g = 0 := (Polynomial.mem_rootSet_of_ne hg0).mp hx
    have hx_int : IsIntegral K x := Normal.isIntegral hnorm x
    have hdvd : minpoly K x ∣ g := minpoly.dvd K x haev
    have hirr : Irreducible (minpoly K x) := minpoly.irreducible hx_int
    exact ((isGarlingSeparablePoly_iff g).mp hgsep) (minpoly K x) hirr hdvd
  have hsep_adj : Algebra.IsSeparable K (IntermediateField.adjoin K (g.rootSet N : Set N)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K N).mpr hroot_sep
  have hadj_top : IntermediateField.adjoin K (g.rootSet N : Set N) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp hsp).2
  let e : IntermediateField.adjoin K (g.rootSet N : Set N) ≃ₐ[K] N :=
    (IntermediateField.equivOfEq hadj_top).trans IntermediateField.topEquiv
  have hsepN : Algebra.IsSeparable K N := AlgEquiv.Algebra.isSeparable e
  rw [isGarlingGaloisExtension_iff]
  exact ⟨inferInstance, @IsGalois.mk K _ N _ _ hsepN hnorm⟩

/-- Step 4 of Garling's proof of `Theorem 13.2` (printed p. 108 / PDF p. 116): in any Galois
extension `N : K`, `Γ(N : K)` is finite, has finitely many subgroups, and by the Fundamental Theorem
of Galois Theory `IntermediateField K N` is finite. -/
theorem finite_intermediateField_of_isGarlingGaloisExtension
    {K N : Type*} [Field K] [Field N] [Algebra K N]
    (hgal : IsGarlingGaloisExtension K N) :
    Finite (GarlingGaloisGroup K N) ∧
      Finite (Subgroup (GarlingGaloisGroup K N)) ∧
      Finite (IntermediateField K N) := by
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff K N).mp hgal
  have hfin_aut : Finite (GarlingGaloisGroup K N) := inferInstance
  have hfin_sub : Finite (Subgroup (GarlingGaloisGroup K N)) := inferInstance
  have hfin_int : Finite (IntermediateField K N) :=
    Equiv.finite_iff IsGalois.intermediateFieldEquivSubgroup.toEquiv |>.mpr
      (Equiv.finite_iff OrderDual.toDual |>.mpr hfin_sub)
  exact ⟨hfin_aut, hfin_sub, hfin_int⟩

/-- **Theorem 13.2** (§13.2, printed p. 108 / PDF p. 116):
Suppose that `L : K` is finite and separable. Then `L : K` is simple.
(Proved directly along Garling's Galois-closure + Fundamental Theorem of Galois Theory +
`Theorem 13.1` proof on p. 108.) -/
theorem theorem_13_2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (hsep : IsGarlingSeparableExtension K L) :
    IsSimpleExtension K L := by
  obtain ⟨halg, hfg⟩ := (theorem_4_6 K L).1.mp hfin
  obtain ⟨n, α, _, hgen⟩ := (theorem_4_6 K L).2.1.mp ⟨halg, hfg⟩
  let g : K[X] := ∏ i : Fin n, minpoly K (α i)
  obtain ⟨hg_monic, hg_sep⟩ := isGarlingSeparablePoly_prod_minpoly (fun i => hsep (α i))
  have hg0 : g ≠ 0 := hg_monic.ne_zero
  have hroots : ∀ i : Fin n, Polynomial.aeval (α i) g = 0 := by
    intro i
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (α i))
  let N := (g.map (algebraMap K L)).SplittingField
  have hNL : IsGarlingSplittingField L N (g.map (algebraMap K L)) :=
    (isGarlingSplittingField_iff L N _).mpr inferInstance
  have hNK : IsGarlingSplittingField K N g :=
    isGarlingSplittingField_tower_of_generators hgen hg0 hroots hNL
  have hgal : IsGarlingGaloisExtension K N :=
    isGarlingGaloisExtension_of_splittingField hg0 hg_sep hNK
  have hfinN : Finite (IntermediateField K N) :=
    (finite_intermediateField_of_isGarlingGaloisExtension hgal).2.2
  let ι : L →ₐ[K] N := IsScalarTower.toAlgHom K L N
  have hinj_map : Function.Injective (fun M : IntermediateField K L => M.map ι) := by
    intro M₁ M₂ heq
    dsimp at heq
    ext x
    have hx : ι x ∈ M₁.map ι ↔ ι x ∈ M₂.map ι := by rw [heq]
    simp only [IntermediateField.mem_map] at hx
    constructor
    · intro hx1
      obtain ⟨y, hy2, hyx⟩ := hx.mp ⟨x, hx1, rfl⟩
      rwa [ι.injective hyx] at hy2
    · intro hx2
      obtain ⟨y, hy1, hyx⟩ := hx.mpr ⟨x, hx2, rfl⟩
      rwa [ι.injective hyx] at hy1
  have hfinL : Finite (IntermediateField K L) := Finite.of_injective _ hinj_map
  exact (theorem_13_1 halg).mpr hfinL

/-- Typeclass-idiomatic companion to `theorem_13_2` under `[FiniteDimensional K L]` and
`[Algebra.IsSeparable K L]`. -/
theorem theorem_13_2_separable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsSimpleExtension K L :=
  theorem_13_2 ((isFiniteExtension_iff_moduleFinite K L).mpr inferInstance)
    ((isGarlingSeparableExtension_iff K L).mpr inferInstance)

/-- **Corollary** [to Theorem 13.2] (§13.2, printed p. 108 / PDF p. 116):
If `L : K` is a Galois extension (`IsGarlingGaloisExtension K L`, finite, normal, and separable per
§10.3, p. 84), there exists an irreducible polynomial `f` in `K[x]` such that `L : K` is a splitting
field extension for `f` over `K` (including `L = K`, witnessed by `f = x`). -/
theorem corollary_to_theorem_13_2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hgal : IsGarlingGaloisExtension K L) :
    ∃ f : K[X], Irreducible f ∧ IsGarlingIrreducible f ∧ IsGarlingSplittingField K L f := by
  obtain ⟨hfin, hnorm, hsep⟩ := hgal
  obtain ⟨α, hα⟩ := theorem_13_2 hfin hsep
  have hN : Normal K L := (isGarlingNormalExtension_iff K L).mp hnorm
  have hint : IsIntegral K α := hN.isIntegral α
  let f : K[X] := minpoly K α
  have hirr : Irreducible f := minpoly.irreducible hint
  have hgirr : IsGarlingIrreducible f := (isGarlingIrreducible_iff f).mpr hirr
  have hsp : (f.map (algebraMap K L)).Splits := hN.splits α
  have hadj : IntermediateField.adjoin K (f.rootSet L) = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    apply IntermediateField.subset_adjoin K (f.rootSet L)
    rw [Polynomial.mem_rootSet_of_ne hirr.ne_zero]
    exact minpoly.aeval K α
  exact ⟨f, hirr, hgirr,
    (isGarlingSplittingField_iff K L f).mpr (isSplittingField_iff_intermediateField.mpr ⟨hsp, hadj⟩)⟩

/-- Typeclass-idiomatic companion to `corollary_to_theorem_13_2` under `[FiniteDimensional K L]` and
`[IsGalois K L]`. -/
theorem corollary_to_theorem_13_2_galois (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ f : K[X], Irreducible f ∧ Polynomial.IsSplittingField K L f := by
  obtain ⟨f, hf, _, hsp⟩ :=
    corollary_to_theorem_13_2 ((isGarlingGaloisExtension_iff K L).mpr ⟨inferInstance, inferInstance⟩)
  exact ⟨f, hf, (isGarlingSplittingField_iff K L f).mp hsp⟩

/-- Justification for `BRIEF.md` Flag 2: Mathlib's `IsGalois ℚ (AlgebraicClosure ℚ)` omits
Garling's §10.3 finiteness condition (`IsFiniteExtension`), and `AlgebraicClosure ℚ : ℚ` is **not**
a splitting field extension for any single polynomial `f ∈ ℚ[X]`. -/
theorem infinite_isGalois_not_splittingField :
    IsGalois ℚ (AlgebraicClosure ℚ) ∧
      ¬ IsFiniteExtension ℚ (AlgebraicClosure ℚ) ∧
      ¬ ∃ f : ℚ[X], IsGarlingSplittingField ℚ (AlgebraicClosure ℚ) f := by
  have hgal : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  have hnot_fin : ¬ FiniteDimensional ℚ (AlgebraicClosure ℚ) := by
    intro hfd
    let m : ℕ := Module.finrank ℚ (AlgebraicClosure ℚ) + 1
    have hm1 : 1 ≤ m := Nat.le_add_left 1 _
    have hirr : Irreducible (Polynomial.X ^ m - Polynomial.C (2 : ℚ) : ℚ[X]) :=
      (Garling.Chapter05.exercise_5_7 (p := 2) Nat.prime_two hm1).1
    let p : ℚ[X] := Polynomial.X ^ m - Polynomial.C (2 : ℚ)
    have hp_monic : p.Monic := Polynomial.monic_X_pow_sub_C (2 : ℚ) (by omega)
    have hdeg : p.natDegree = m := Polynomial.natDegree_X_pow_sub_C
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure ℚ) p hirr.degree_pos.ne'
    have hmin : minpoly ℚ r = p := (minpoly.eq_of_irreducible_of_monic hirr hr hp_monic).symm
    have hsub_le : Module.finrank ℚ ℚ⟮r⟯ ≤ Module.finrank ℚ (AlgebraicClosure ℚ) :=
      Submodule.finrank_le ℚ⟮r⟯.toSubmodule
    rw [IntermediateField.adjoin.finrank ⟨p, hp_monic, hr⟩, hmin, hdeg] at hsub_le
    omega
  refine ⟨hgal, ?_, ?_⟩
  · rw [isFiniteExtension_iff_moduleFinite]
    exact hnot_fin
  · rintro ⟨f, hf⟩
    have hsp : Polynomial.IsSplittingField ℚ (AlgebraicClosure ℚ) f :=
      (isGarlingSplittingField_iff ℚ (AlgebraicClosure ℚ) f).mp hf
    exact hnot_fin (Polynomial.IsSplittingField.finiteDimensional (AlgebraicClosure ℚ) f)

/-! ### Exercise 13.3 (§13.2, printed p. 109, PDF p. 117) -/

/-- The polynomial `(x^p - α)(x^p - β) ∈ K[x]` of `Exercise 13.3` (§13.2, printed p. 109 /
PDF p. 117), where `α ∈ J` is mapped into `K` via `algebraMap J K`. -/
noncomputable def exercise_13_3_poly {J K : Type*} [Field J] [Field K] [Algebra J K]
    (p : ℕ) (α : J) (β : K) : K[X] :=
  (Polynomial.X ^ p - Polynomial.C (algebraMap J K α)) * (Polynomial.X ^ p - Polynomial.C β)

private lemma coeff_pow_charP_mul {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (f : R[X]) (k : ℕ) :
    (f ^ p).coeff (p * k) = (f.coeff k) ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Polynomial.map_frobenius_expand p f, Polynomial.coeff_map,
    Polynomial.coeff_expand_mul' hp, frobenius_def]

private lemma coeff_pow_charP_of_not_dvd {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (f : R[X]) {m : ℕ} (hm : ¬ p ∣ m) :
    (f ^ p).coeff m = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Polynomial.map_frobenius_expand p f, Polynomial.coeff_map,
    Polynomial.coeff_expand hp, ite_eq_right hm, map_zero]

private lemma not_dvd_mul_add_one {p : ℕ} (hp : p.Prime) (d : ℕ) : ¬ p ∣ p * d + 1 := by
  intro hdvd
  have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p d)).mp hdvd
  exact hp.not_dvd_one h1

private lemma mem_adjoin_simple_exists_div_ne_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    {t : E} {x : E} (hx : x ∈ F⟮t⟯) :
    ∃ r s : F[X], s ≠ 0 ∧ x = Polynomial.aeval t r / Polynomial.aeval t s := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F x).mp hx
  by_cases hs : s = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    simp [hrs, hs]
  · exact ⟨r, s, hs, hrs⟩

private lemma aeval_ne_zero_of_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    {t : E} (ht : IsGarlingTranscendental F t) {s : F[X]} (hs : s ≠ 0) :
    Polynomial.aeval t s ≠ 0 := by
  have hinj : Function.Injective (evalRingHom F t) := (evalRingHom_injective_iff F t).1.mpr ht
  intro h0
  exact hs (hinj (by simpa [evalRingHom] using h0))

private lemma not_exists_pow_charP_eq_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] {t : E}
    (ht : IsGarlingTranscendental F t) (hadj : F⟮t⟯ = ⊤) :
    ¬ ∃ c : E, c ^ p = t := by
  have _ : CharP E p := charP_of_injective_algebraMap (algebraMap F E).injective p
  have hp : p.Prime := Fact.out
  rintro ⟨c, hc⟩
  have hc_mem : c ∈ F⟮t⟯ := by rw [hadj]; trivial
  obtain ⟨r, s, hs0, hrs⟩ := mem_adjoin_simple_exists_div_ne_zero hc_mem
  have has0 : Polynomial.aeval t s ≠ 0 := aeval_ne_zero_of_transcendental ht hs0
  have heval : Polynomial.aeval t (r ^ p) = Polynomial.aeval t (Polynomial.X * s ^ p) := by
    rw [map_pow, map_mul, Polynomial.aeval_X, map_pow]
    have hdiv : (Polynomial.aeval t r) ^ p / (Polynomial.aeval t s) ^ p = t := by
      rw [← div_pow, ← hrs, hc]
    exact (div_eq_iff (pow_ne_zero p has0)).mp hdiv
  have hinj : Function.Injective (evalRingHom F t) := (evalRingHom_injective_iff F t).1.mpr ht
  have hpoly : r ^ p = Polynomial.X * s ^ p := hinj heval
  have hcoeff := congrArg (fun q : F[X] => q.coeff (p * s.natDegree + 1)) hpoly
  rw [coeff_pow_charP_of_not_dvd r (not_dvd_mul_add_one hp s.natDegree),
    Polynomial.coeff_X_mul, coeff_pow_charP_mul s s.natDegree, ← Polynomial.leadingCoeff] at hcoeff
  have hlc0 : s.leadingCoeff = 0 := (pow_eq_zero_iff hp.ne_zero).mp hcoeff.symm
  exact hs0 (Polynomial.leadingCoeff_eq_zero.mp hlc0)

private lemma not_exists_pow_charP_eq_algebraMap_of_transcendental
    {J K : Type*} [Field J] [Field K] [Algebra J K] {p : ℕ} [Fact p.Prime] [CharP J p]
    {α : J} (hα : ¬ ∃ c : J, c ^ p = α)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤) :
    ¬ ∃ c : K, c ^ p = algebraMap J K α := by
  have _ : CharP K p := charP_of_injective_algebraMap (algebraMap J K).injective p
  rintro ⟨c, hc⟩
  have hc_mem : c ∈ J⟮β⟯ := by rw [hK]; trivial
  obtain ⟨r, s, hs0, hrs⟩ := mem_adjoin_simple_exists_div_ne_zero hc_mem
  have has0 : Polynomial.aeval β s ≠ 0 := aeval_ne_zero_of_transcendental hβ hs0
  have heval : Polynomial.aeval β (r ^ p) = Polynomial.aeval β (Polynomial.C α * s ^ p) := by
    rw [map_pow, map_mul, Polynomial.aeval_C, map_pow]
    have hdiv : (Polynomial.aeval β r) ^ p / (Polynomial.aeval β s) ^ p = algebraMap J K α := by
      rw [← div_pow, ← hrs, hc]
    exact (div_eq_iff (pow_ne_zero p has0)).mp hdiv
  have hinj : Function.Injective (evalRingHom J β) := (evalRingHom_injective_iff J β).1.mpr hβ
  have hpoly : r ^ p = Polynomial.C α * s ^ p := hinj heval
  have hcoeff := congrArg (fun q : J[X] => q.coeff (p * s.natDegree)) hpoly
  rw [coeff_pow_charP_mul r s.natDegree, Polynomial.coeff_C_mul,
    coeff_pow_charP_mul s s.natDegree, ← Polynomial.leadingCoeff] at hcoeff
  have hlc0 : s.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hs0
  refine hα ⟨r.coeff s.natDegree / s.leadingCoeff, ?_⟩
  rw [div_pow, hcoeff, mul_div_cancel_right₀ α (pow_ne_zero p hlc0)]

private lemma not_exists_pow_charP_eq_beta_over_adjoin_root
    {J K L : Type*} [Field J] [Field K] [Field L] [Algebra J K] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP J p]
    {α : J} {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    {u : L} (hu : u ^ p = algebraMap K L (algebraMap J K α)) :
    ¬ ∃ w : K⟮u⟯, (w : L) ^ p = algebraMap K L β := by
  classical
  have hp : p.Prime := Fact.out
  have _ : CharP K p := charP_of_injective_algebraMap (algebraMap J K).injective p
  have _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hu_alg : IsAlgebraic K u := by
    refine ⟨Polynomial.X ^ p - Polynomial.C (algebraMap J K α), ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C _ hp.ne_zero).ne_zero
    · simp [hu]
  rintro ⟨w, hw⟩
  have hw_sub : (w : L) ∈ (K⟮u⟯).toSubalgebra := w.2
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hu_alg,
    Algebra.adjoin_singleton_eq_range_aeval] at hw_sub
  obtain ⟨P, hP⟩ := hw_sub
  change Polynomial.aeval u P = (w : L) at hP
  have hw_pow : (w : L) ^ p =
      algebraMap K L
        (∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i) ^ p * (algebraMap J K α) ^ i) := by
    rw [← hP, Polynomial.aeval_eq_sum_range, ← frobenius_def p, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ((P.coeff i • u ^ i) : L) ^ p =
        algebraMap K L ((P.coeff i) ^ p * (algebraMap J K α) ^ i) := by
      rw [Algebra.smul_def, mul_pow, ← map_pow (algebraMap K L), pow_right_comm, hu,
        ← map_pow (algebraMap K L), ← map_mul (algebraMap K L)]
    simpa [frobenius_def] using hterm
  have hβ_eq : β =
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i) ^ p * (algebraMap J K α) ^ i :=
    (algebraMap K L).injective (hw.symm.trans hw_pow)
  let n : ℕ := P.natDegree + 1
  have hmem : ∀ i : Fin n, P.coeff i ∈ J⟮β⟯ := fun _ => by rw [hK]; trivial
  choose r s hs0 hrs using fun i : Fin n => mem_adjoin_simple_exists_div_ne_zero (hmem i)
  let S : J[X] := ∏ i : Fin n, s i
  have hS0 : S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
  have hdvd : ∀ i : Fin n, s i ∣ S := fun i => Finset.dvd_prod_of_mem s (Finset.mem_univ i)
  choose q hq using hdvd
  have hclear : ∀ i : Fin n,
      P.coeff i * Polynomial.aeval β S = Polynomial.aeval β (r i * q i) := by
    intro i
    have hasi : Polynomial.aeval β (s i) ≠ 0 := aeval_ne_zero_of_transcendental hβ (hs0 i)
    rw [hrs i, hq i, map_mul, map_mul]
    field_simp [hasi]
  have heval : Polynomial.aeval β (Polynomial.X * S ^ p) =
      Polynomial.aeval β
        (∑ i : Fin n, Polynomial.C (α ^ (i : ℕ)) * (r i * q i) ^ p) := by
    rw [map_mul, Polynomial.aeval_X, map_pow]
    nth_rw 1 [hβ_eq]
    rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (P.coeff i) ^ p * (Polynomial.aeval β S) ^ p =
        (Polynomial.aeval β (r i * q i)) ^ p := by
      rw [← mul_pow, hclear i]
    rw [map_mul, Polynomial.aeval_C, map_pow, map_pow, ← hc]
    ring
  have hinj : Function.Injective (evalRingHom J β) := (evalRingHom_injective_iff J β).1.mpr hβ
  have hpoly : Polynomial.X * S ^ p =
      ∑ i : Fin n, Polynomial.C (α ^ (i : ℕ)) * (r i * q i) ^ p := hinj heval
  have hcoeff := congrArg (fun t : J[X] => t.coeff (p * S.natDegree + 1)) hpoly
  rw [Polynomial.coeff_X_mul, coeff_pow_charP_mul S S.natDegree, ← Polynomial.leadingCoeff,
    Polynomial.finsetSum_coeff] at hcoeff
  have hrhs : (∑ i : Fin n,
      (Polynomial.C (α ^ (i : ℕ)) * (r i * q i) ^ p).coeff (p * S.natDegree + 1)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul,
      coeff_pow_charP_of_not_dvd (r i * q i) (not_dvd_mul_add_one hp S.natDegree), mul_zero]
  rw [hrhs] at hcoeff
  exact hS0 (Polynomial.leadingCoeff_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp hcoeff))

private lemma monic_dvd_X_sub_C_pow {E : Type*} [Field E] (u : E) :
    ∀ (m : ℕ) {q : E[X]}, q.Monic → q ∣ (Polynomial.X - Polynomial.C u) ^ m →
      q = (Polynomial.X - Polynomial.C u) ^ q.natDegree
  | 0, q, hq, hdvd => by
    rw [pow_zero] at hdvd
    have hu : IsUnit q := isUnit_of_dvd_one hdvd
    have hdeg : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hdeg, pow_zero]
    exact Polynomial.eq_one_of_monic_natDegree_zero hq hdeg
  | m + 1, q, hq, hdvd => by
    by_cases hdeg0 : q.natDegree = 0
    · rw [hdeg0, pow_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hq hdeg0
    · have hdvd_lin : Polynomial.X - Polynomial.C u ∣ q := by
        by_contra hndvd
        have hcop : IsCoprime (Polynomial.X - Polynomial.C u) q :=
          (Polynomial.irreducible_X_sub_C u).coprime_iff_not_dvd.mpr hndvd
        have hcop_pow : IsCoprime ((Polynomial.X - Polynomial.C u) ^ (m + 1)) q :=
          hcop.pow_left
        obtain ⟨k, hk⟩ := hdvd
        have hcop_self : IsCoprime q q := by
          rw [hk] at hcop_pow
          exact hcop_pow.of_mul_left_left
        have hunit : IsUnit q := isCoprime_self.mp hcop_self
        exact hdeg0 (Polynomial.natDegree_eq_zero_of_isUnit hunit)
      obtain ⟨q₁, rfl⟩ := hdvd_lin
      have hmon_lin : (Polynomial.X - Polynomial.C u).Monic := Polynomial.monic_X_sub_C u
      have hq₁_monic : q₁.Monic := hmon_lin.of_mul_monic_left hq
      have hne_lin : Polynomial.X - Polynomial.C u ≠ 0 := Polynomial.X_sub_C_ne_zero u
      rw [pow_succ'] at hdvd
      have hq₁_dvd : q₁ ∣ (Polynomial.X - Polynomial.C u) ^ m :=
        (mul_dvd_mul_iff_left hne_lin).mp hdvd
      have ih := monic_dvd_X_sub_C_pow u m hq₁_monic hq₁_dvd
      have hdeg_mul : ((Polynomial.X - Polynomial.C u) * q₁).natDegree = q₁.natDegree + 1 := by
        rw [Polynomial.natDegree_mul hne_lin hq₁_monic.ne_zero, Polynomial.natDegree_X_sub_C,
          add_comm]
      rw [hdeg_mul, pow_succ']
      exact congrArg ((Polynomial.X - Polynomial.C u) * ·) ih

private lemma irreducible_X_pow_charP_sub_C {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] {a : F} {u : E}
    (hu : u ^ p = algebraMap F E a) (ha : ¬ ∃ c : F, c ^ p = a) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a : F[X]) := by
  have hp : p.Prime := Fact.out
  have _ : CharP E p := charP_of_injective_algebraMap (algebraMap F E).injective p
  let P : F[X] := Polynomial.X ^ p - Polynomial.C a
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C a hp.ne_zero
  have hP_deg : P.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  have hP_not_unit : ¬ IsUnit P := by
    intro hunit
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [hP_deg] at h0
    exact hp.ne_zero h0
  rw [Polynomial.irreducible_iff_lt_natDegree_lt hP_monic.ne_zero hP_not_unit]
  intro q hq_monic hq_mem hdvd
  rw [Finset.mem_Ioc, hP_deg] at hq_mem
  have hk_pos : 0 < q.natDegree := hq_mem.1
  have hk_lt : q.natDegree < p := lt_of_le_of_lt hq_mem.2 (Nat.div_lt_self hp.pos (by decide))
  set k := q.natDegree
  have hmap_P : P.map (algebraMap F E) = (Polynomial.X - Polynomial.C u) ^ p := by
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [sub_pow_char, ← Polynomial.C_pow, hu]
  have hdvd_E : q.map (algebraMap F E) ∣ (Polynomial.X - Polynomial.C u) ^ p := by
    rw [← hmap_P]
    exact Polynomial.map_dvd (algebraMap F E) hdvd
  have hqE_monic : (q.map (algebraMap F E)).Monic := hq_monic.map (algebraMap F E)
  have hqE_deg : (q.map (algebraMap F E)).natDegree = k := hq_monic.natDegree_map (algebraMap F E)
  have hqE_eq : q.map (algebraMap F E) = (Polynomial.X - Polynomial.C u) ^ k := by
    have h := monic_dvd_X_sub_C_pow u p hqE_monic hdvd_E
    rwa [hqE_deg] at h
  have hcoeff := congrArg (fun t : E[X] => t.coeff (k - 1)) hqE_eq
  have hsub_add : (Polynomial.X - Polynomial.C u : E[X]) = Polynomial.X + Polynomial.C (-u) := by
    rw [sub_eq_add_neg, Polynomial.C_neg]
  rw [Polynomial.coeff_map, hsub_add, Polynomial.coeff_X_add_C_pow] at hcoeff
  have hk_sub : k - (k - 1) = 1 := by omega
  have hchoose : k.choose (k - 1) = k := by
    have hk1 : k - 1 ≤ k := Nat.sub_le k 1
    rw [← Nat.choose_symm hk1, hk_sub, Nat.choose_one_right]
  rw [hk_sub, pow_one, hchoose] at hcoeff
  have hkF_ne : (k : F) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff F p k]
    exact Nat.not_dvd_of_pos_of_lt hk_pos hk_lt
  have hkE_eq : (k : E) = algebraMap F E (k : F) := (map_natCast (algebraMap F E) k).symm
  rw [hkE_eq] at hcoeff
  have hkE_ne : algebraMap F E (k : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap F E) (algebraMap F E).injective).mpr hkF_ne
  have hu_eq : u = algebraMap F E (-q.coeff (k - 1) / (k : F)) := by
    rw [map_div₀, map_neg]
    apply eq_div_of_mul_eq hkE_ne
    linear_combination hcoeff
  refine ha ⟨-q.coeff (k - 1) / (k : F), ?_⟩
  apply (algebraMap F E).injective
  rw [map_pow, ← hu_eq, hu]

private lemma exercise_13_3_roots_and_tower
    {p : ℕ} [Fact p.Prime] {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod p) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod p) α) (hJ : (ZMod p)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β)) :
    ∃ u v : L,
      u ^ p = algebraMap K L (algebraMap J K α) ∧
      v ^ p = algebraMap K L β ∧
      (∀ x : L, x ^ p = algebraMap K L (algebraMap J K α) → x = u) ∧
      (∀ x : L, x ^ p = algebraMap K L β → x = v) ∧
      Module.finrank K K⟮u⟯ = p ∧
      Module.finrank K⟮u⟯ L = p ∧
      Module.finrank K L = p ^ 2 ∧
      K⟮u, v⟯ = ⊤ := by
  have hp : p.Prime := Fact.out
  have _ : CharP J p := charP_of_injective_algebraMap (algebraMap (ZMod p) J).injective p
  have _ : CharP K p := charP_of_injective_algebraMap (algebraMap J K).injective p
  have _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hsp : Polynomial.IsSplittingField K L (exercise_13_3_poly p α β) :=
    (isGarlingSplittingField_iff K L _).mp hL
  obtain ⟨hsplit, hadj⟩ := isSplittingField_iff_intermediateField.mp hsp
  let f₁ : K[X] := Polynomial.X ^ p - Polynomial.C (algebraMap J K α)
  let f₂ : K[X] := Polynomial.X ^ p - Polynomial.C β
  have hf₁_monic : f₁.Monic := Polynomial.monic_X_pow_sub_C _ hp.ne_zero
  have hf₂_monic : f₂.Monic := Polynomial.monic_X_pow_sub_C _ hp.ne_zero
  have hf₁L_monic : (f₁.map (algebraMap K L)).Monic := hf₁_monic.map (algebraMap K L)
  have hf₂L_monic : (f₂.map (algebraMap K L)).Monic := hf₂_monic.map (algebraMap K L)
  have hsplit_mul :
      ((f₁.map (algebraMap K L)) * (f₂.map (algebraMap K L))).Splits := by
    have hmap_mul : (exercise_13_3_poly p α β).map (algebraMap K L) =
        f₁.map (algebraMap K L) * f₂.map (algebraMap K L) := by
      simp [exercise_13_3_poly, f₁, f₂]
    rwa [hmap_mul] at hsplit
  obtain ⟨hsp₁, hsp₂⟩ := (Polynomial.splits_mul hf₁L_monic.ne_zero hf₂L_monic.ne_zero).mp hsplit_mul
  have hdeg₁ : (f₁.map (algebraMap K L)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf₁L_monic.ne_zero, hf₁_monic.natDegree_map]
    have hd : f₁.natDegree = p := Polynomial.natDegree_X_pow_sub_C
    rw [hd]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  have hdeg₂ : (f₂.map (algebraMap K L)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf₂L_monic.ne_zero, hf₂_monic.natDegree_map]
    have hd : f₂.natDegree = p := Polynomial.natDegree_X_pow_sub_C
    rw [hd]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨u, hu_eval⟩ := hsp₁.exists_eval_eq_zero hdeg₁
  obtain ⟨v, hv_eval⟩ := hsp₂.exists_eval_eq_zero hdeg₂
  have hu : u ^ p = algebraMap K L (algebraMap J K α) := by
    simp only [f₁, Polynomial.eval_map, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hu_eval
    exact hu_eval
  have hv : v ^ p = algebraMap K L β := by
    simp only [f₂, Polynomial.eval_map, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hv_eval
    exact hv_eval
  have hu_uniq : ∀ x : L, x ^ p = algebraMap K L (algebraMap J K α) → x = u := by
    intro x hx
    have hsub : (x - u) ^ p = 0 := by rw [sub_pow_char, hx, hu, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp hsub)
  have hv_uniq : ∀ x : L, x ^ p = algebraMap K L β → x = v := by
    intro x hx
    have hsub : (x - v) ^ p = 0 := by rw [sub_pow_char, hx, hv, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp hsub)
  have hno_α_J : ¬ ∃ c : J, c ^ p = α :=
    not_exists_pow_charP_eq_transcendental hα hJ
  have hno_α_K : ¬ ∃ c : K, c ^ p = algebraMap J K α :=
    not_exists_pow_charP_eq_algebraMap_of_transcendental hno_α_J hβ hK
  have hf₁_irr : Irreducible f₁ := irreducible_X_pow_charP_sub_C hu hno_α_K
  have hu_aeval : Polynomial.aeval u f₁ = 0 := by
    simp [f₁, hu]
  have hmin_u : minpoly K u = f₁ :=
    (minpoly.eq_of_irreducible_of_monic hf₁_irr hu_aeval hf₁_monic).symm
  have hfin_u : Module.finrank K K⟮u⟯ = p := by
    rw [IntermediateField.adjoin.finrank ⟨f₁, hf₁_monic, hu_aeval⟩, hmin_u]
    exact Polynomial.natDegree_X_pow_sub_C
  have hno_β_Ku : ¬ ∃ w : K⟮u⟯, w ^ p = algebraMap K K⟮u⟯ β := by
    rintro ⟨w, hw⟩
    refine not_exists_pow_charP_eq_beta_over_adjoin_root hβ hK hu ⟨w, ?_⟩
    have hmap := congrArg (algebraMap K⟮u⟯ L) hw
    rwa [map_pow, ← IsScalarTower.algebraMap_apply K K⟮u⟯ L] at hmap
  let g₂ : (K⟮u⟯)[X] := Polynomial.X ^ p - Polynomial.C (algebraMap K K⟮u⟯ β)
  have hg₂_monic : g₂.Monic := Polynomial.monic_X_pow_sub_C _ hp.ne_zero
  have hv_Ku : v ^ p = algebraMap K⟮u⟯ L (algebraMap K K⟮u⟯ β) := by
    rwa [← IsScalarTower.algebraMap_apply K K⟮u⟯ L]
  have hg₂_irr : Irreducible g₂ := irreducible_X_pow_charP_sub_C hv_Ku hno_β_Ku
  have hv_aeval : Polynomial.aeval v g₂ = 0 := by
    simp [g₂, hv_Ku]
  have hmin_v : minpoly K⟮u⟯ v = g₂ :=
    (minpoly.eq_of_irreducible_of_monic hg₂_irr hv_aeval hg₂_monic).symm
  have hfin_v : Module.finrank K⟮u⟯ (K⟮u⟯⟮v⟯) = p := by
    rw [IntermediateField.adjoin.finrank ⟨g₂, hg₂_monic, hv_aeval⟩, hmin_v]
    exact Polynomial.natDegree_X_pow_sub_C
  have hrootSet : (exercise_13_3_poly p α β).rootSet L = {u, v} := by
    ext x
    have hf_ne : exercise_13_3_poly p α β ≠ 0 := mul_ne_zero hf₁_monic.ne_zero hf₂_monic.ne_zero
    rw [Polynomial.mem_rootSet_of_ne hf_ne]
    simp only [exercise_13_3_poly, map_mul, map_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, mul_eq_zero, sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · exact Or.inl (hu_uniq x hx)
      · exact Or.inr (hv_uniq x hx)
    · rintro (rfl | rfl)
      · exact Or.inl hu
      · exact Or.inr hv
  have hadj_uv : K⟮u, v⟯ = ⊤ := by rwa [← hrootSet]
  have huv_top : K⟮u⟯⟮v⟯ = (⊤ : IntermediateField K⟮u⟯ L) := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    have hx : x ∈ (K⟮u⟯⟮v⟯).restrictScalars K := by
      rw [IntermediateField.adjoin_simple_adjoin_simple, hadj_uv]
      trivial
    exact hx
  have hfin_Ku_L : Module.finrank K⟮u⟯ L = p := by
    rw [← IntermediateField.topEquiv.toLinearEquiv.finrank_eq (R := K⟮u⟯), ← huv_top, hfin_v]
  have hfin_KL : Module.finrank K L = p ^ 2 := by
    rw [← Module.finrank_mul_finrank K K⟮u⟯ L, hfin_u, hfin_Ku_L, sq]
  exact ⟨u, v, hu, hv, hu_uniq, hv_uniq, hfin_u, hfin_Ku_L, hfin_KL, hadj_uv⟩

/-- **Exercise 13.3(i)** (§13.2, printed p. 109 / PDF p. 117):
Let `p` be a prime, `J = ℤ_p(α)` with `α` transcendental over `ℤ_p`, `K = J(β)` with `β`
transcendental over `J`, and `L : K` a splitting field extension for `(x^p - α)(x^p - β)`. Then
`[L : K] = p²` (both in Garling's `extDegree K L` and in `Module.finrank K L`). -/
theorem exercise_13_3_i {p : ℕ} [Fact p.Prime] {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod p) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod p) α) (hJ : (ZMod p)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β)) :
    extDegree K L = (p ^ 2 : ℕ) ∧ Module.finrank K L = p ^ 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, hfin_KL, _⟩ :=
    exercise_13_3_roots_and_tower hα hJ hβ hK hL
  have hsp : Polynomial.IsSplittingField K L (exercise_13_3_poly p α β) :=
    (isGarlingSplittingField_iff K L _).mp hL
  have _ : FiniteDimensional K L :=
    Polynomial.IsSplittingField.finiteDimensional L (exercise_13_3_poly p α β)
  refine ⟨?_, hfin_KL⟩
  rw [extDegree_eq_finrank K L, hfin_KL]

/-- **Exercise 13.3(ii)** (§13.2, printed p. 109 / PDF p. 117):
Under the hypotheses of `Exercise 13.3`, for every `γ ∈ L` we have `γ^p ∈ K`
(`γ ^ p ∈ Set.range (algebraMap K L)`). -/
theorem exercise_13_3_ii {p : ℕ} [Fact p.Prime] {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod p) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod p) α) (hJ : (ZMod p)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β)) :
    ∀ γ : L, γ ^ p ∈ Set.range (algebraMap K L) := by
  have _ : CharP J p := charP_of_injective_algebraMap (algebraMap (ZMod p) J).injective p
  have _ : CharP K p := charP_of_injective_algebraMap (algebraMap J K).injective p
  have _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨u, v, hu, hv, _, _, _, _, _, hadj_uv⟩ :=
    exercise_13_3_roots_and_tower hα hJ hβ hK hL
  let S : Subfield L := (⊥ : IntermediateField K L).toSubfield.comap (frobenius L p)
  let M : IntermediateField K L :=
    { S with
      algebraMap_mem' := fun c => by
        change (algebraMap K L c) ^ p ∈ (⊥ : IntermediateField K L)
        rw [← map_pow]
        exact (⊥ : IntermediateField K L).algebraMap_mem (c ^ p) }
  have hu_mem : u ∈ M := by
    change u ^ p ∈ (⊥ : IntermediateField K L)
    rw [hu]
    exact (⊥ : IntermediateField K L).algebraMap_mem _
  have hv_mem : v ∈ M := by
    change v ^ p ∈ (⊥ : IntermediateField K L)
    rw [hv]
    exact (⊥ : IntermediateField K L).algebraMap_mem _
  have htop : M = ⊤ := by
    rw [eq_top_iff, ← hadj_uv, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact hu_mem
    · exact hv_mem
  intro γ
  have hγ : γ ∈ M := by rw [htop]; trivial
  change γ ^ p ∈ (⊥ : IntermediateField K L) at hγ
  rwa [IntermediateField.mem_bot] at hγ

/-- **Exercise 13.3(iii)** (§13.2, printed p. 109 / PDF p. 117):
Under the hypotheses of `Exercise 13.3`, `L : K` is not simple (and hence, being finite and
algebraic, has infinitely many intermediate fields by `Theorem 13.1`). -/
theorem exercise_13_3_iii {p : ℕ} [Fact p.Prime] {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod p) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod p) α) (hJ : (ZMod p)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β)) :
    ¬ IsSimpleExtension K L := by
  have hp : p.Prime := Fact.out
  obtain ⟨_, hfin_KL⟩ := exercise_13_3_i hα hJ hβ hK hL
  have hpow := exercise_13_3_ii hα hJ hβ hK hL
  rintro ⟨γ, hγ_top⟩
  obtain ⟨c, hc⟩ := hpow γ
  let P : K[X] := Polynomial.X ^ p - Polynomial.C c
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C c hp.ne_zero
  have hP_eval : Polynomial.aeval γ P = 0 := by
    simp [P, hc]
  have hdvd : minpoly K γ ∣ P := minpoly.dvd K γ hP_eval
  have hdeg_le : (minpoly K γ).natDegree ≤ p := by
    have hle := Polynomial.natDegree_le_of_dvd hdvd hP_monic.ne_zero
    have hP_deg : P.natDegree = p := Polynomial.natDegree_X_pow_sub_C
    omega
  have hfin_γ : Module.finrank K K⟮γ⟯ = (minpoly K γ).natDegree :=
    IntermediateField.adjoin.finrank ⟨P, hP_monic, hP_eval⟩
  have hfin_eq : Module.finrank K L = Module.finrank K K⟮γ⟯ := by
    rw [← IntermediateField.topEquiv.toLinearEquiv.finrank_eq (R := K), ← hγ_top]
  have hp2_le : p ^ 2 ≤ p := by omega
  have hp_ge2 : 2 ≤ p := hp.two_le
  nlinarith

/-- Complete projective-plane classification of intermediate fields for degree-`4` height-`1`
inseparable extensions (`Exercise 13.3(iv)`, §13.2, printed p. 109 / PDF p. 117):
whenever `[L : K] = 4` and `γ² ∈ K` for every `γ ∈ L`, every intermediate field `M` satisfies
`M = ⊥ ∨ M = ⊤ ∨ (M ≠ ⊥ ∧ M ≠ ⊤ ∧ [M : K] = 2)`, and the proper non-trivial intermediate fields
stand in canonical bijection with `ℙ K (L ⧸ K)` via `[γ mod K] ↦ K(γ)`. -/
noncomputable def intermediateFieldEquivProjQuotOfSqMem
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hfin : Module.finrank K L = 4)
    (hsq : ∀ γ : L, γ ^ 2 ∈ Set.range (algebraMap K L)) :
    ℙ K (L ⧸ (⊥ : IntermediateField K L).toSubmodule) ≃
      {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} := by
  let B₀ : Submodule K L := (⊥ : IntermediateField K L).toSubmodule
  let π : L →ₗ[K] L ⧸ B₀ := B₀.mkQ
  have hB₀_range : B₀ = LinearMap.range (Algebra.linearMap K L) := by
    ext x
    change x ∈ (⊥ : IntermediateField K L) ↔ x ∈ LinearMap.range (Algebra.linearMap K L)
    rw [IntermediateField.mem_bot, LinearMap.mem_range]
    rfl
  have hfin_B₀ : Module.finrank K B₀ = 1 := by
    rw [hB₀_range]
    have e : K ≃ₗ[K] LinearMap.range (Algebra.linearMap K L) :=
      LinearEquiv.ofInjective (Algebra.linearMap K L) (algebraMap K L).injective
    rw [← e.finrank_eq, Module.finrank_self]
  have hfin_adjoin_two : ∀ {γ : L}, γ ∉ B₀ → Module.finrank K K⟮γ⟯ = 2 := by
    intro γ hγ_not
    obtain ⟨c, hc⟩ := hsq γ
    let P : K[X] := Polynomial.X ^ 2 - Polynomial.C c
    have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C c (by decide)
    have hP_eval : Polynomial.aeval γ P = 0 := by simp [P, hc]
    have hdvd : minpoly K γ ∣ P := minpoly.dvd K γ hP_eval
    have hle2 : Module.finrank K K⟮γ⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank ⟨P, hP_monic, hP_eval⟩]
      have hle := Polynomial.natDegree_le_of_dvd hdvd hP_monic.ne_zero
      have hdeg : P.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
      omega
    have hlt : B₀ < (K⟮γ⟯).toSubmodule := by
      refine lt_of_le_of_ne (bot_le : (⊥ : IntermediateField K L) ≤ K⟮γ⟯) ?_
      intro heq
      apply hγ_not
      rw [heq]
      exact IntermediateField.mem_adjoin_simple_self K γ
    have hgt1 : 1 < Module.finrank K (K⟮γ⟯).toSubmodule := by
      rw [← hfin_B₀]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    change 1 < Module.finrank K K⟮γ⟯ at hgt1
    omega
  have hsub_adjoin : ∀ {γ : L}, γ ∉ B₀ → (K⟮γ⟯).toSubmodule = B₀ ⊔ Submodule.span K {γ} := by
    intro γ hγ_not
    have hle : B₀ ⊔ Submodule.span K {γ} ≤ (K⟮γ⟯).toSubmodule := by
      refine sup_le (bot_le : (⊥ : IntermediateField K L) ≤ K⟮γ⟯) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact IntermediateField.mem_adjoin_simple_self K γ
    have hlt : B₀ < B₀ ⊔ Submodule.span K {γ} := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply hγ_not
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self γ)
    have hgt1 : 1 < Module.finrank K ↥(B₀ ⊔ Submodule.span K {γ}) := by
      rw [← hfin_B₀]
      exact Submodule.finrank_lt_finrank_of_lt hlt
    have hfin2 : Module.finrank K (K⟮γ⟯).toSubmodule = 2 := hfin_adjoin_two hγ_not
    have hle2 : Module.finrank K ↥(B₀ ⊔ Submodule.span K {γ}) ≤ 2 :=
      (Submodule.finrank_mono hle).trans_eq hfin2
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hproper_finrank : ∀ M : IntermediateField K L, (M ≠ ⊥ ∧ M ≠ ⊤) ↔ Module.finrank K M = 2 := by
    intro M
    constructor
    · rintro ⟨hne_bot, hne_top⟩
      have hmul : Module.finrank K M * Module.finrank M L = 4 := by
        rw [Module.finrank_mul_finrank K M L, hfin]
      have hposM : 0 < Module.finrank K M := Module.finrank_pos
      have hposML : 0 < Module.finrank M L := Module.finrank_pos
      have hle4 : Module.finrank K M ≤ 4 := by nlinarith
      have hne1 : Module.finrank K M ≠ 1 := by
        intro h1
        apply hne_bot
        have heq : B₀ = M.toSubmodule :=
          Submodule.eq_of_le_of_finrank_eq (bot_le : (⊥ : IntermediateField K L) ≤ M)
            (hfin_B₀.trans h1.symm)
        ext x
        exact SetLike.ext_iff.mp heq.symm x
      have hne4 : Module.finrank K M ≠ 4 := by
        intro h4
        apply hne_top
        have heq : M.toSubmodule = ⊤ :=
          Submodule.eq_of_le_of_finrank_eq le_top (by
            change Module.finrank K ↥M = _
            rw [h4, finrank_top, hfin])
        ext x
        exact SetLike.ext_iff.mp heq x
      interval_cases hM : Module.finrank K M <;> omega
    · intro h2
      refine ⟨?_, ?_⟩
      · rintro rfl
        change Module.finrank K B₀ = 2 at h2
        omega
      · rintro rfl
        have htop : Module.finrank K (⊤ : IntermediateField K L) = 4 := by
          rw [IntermediateField.topEquiv.toLinearEquiv.finrank_eq (R := K), hfin]
        omega
  let fromProj : ℙ K (L ⧸ B₀) → {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} := fun p =>
    let γ : L := Classical.choose (Submodule.Quotient.mk_surjective B₀ p.rep)
    have hγ : Submodule.Quotient.mk (p := B₀) γ = p.rep :=
      Classical.choose_spec (Submodule.Quotient.mk_surjective B₀ p.rep)
    have hγ_not : γ ∉ B₀ := fun hmem =>
      p.rep_nonzero (hγ.symm.trans ((Submodule.Quotient.mk_eq_zero B₀).mpr hmem))
    ⟨K⟮γ⟯, (hproper_finrank K⟮γ⟯).mpr (hfin_adjoin_two hγ_not)⟩
  have hmap_finrank : ∀ {M : IntermediateField K L},
      (M ≠ ⊥ ∧ M ≠ ⊤) → Module.finrank K (Submodule.map π M.toSubmodule) = 1 := by
    intro M hM
    have hne_bot : M ≠ ⊥ := hM.1
    have hex : ∃ γ ∈ M, γ ∉ B₀ := by
      by_contra hall
      push Not at hall
      apply hne_bot
      refine le_antisymm ?_ bot_le
      intro x hx
      exact hall x hx
    obtain ⟨γ, hγM, hγ_not⟩ := hex
    have hle : K⟮γ⟯ ≤ M := IntermediateField.adjoin_simple_le_iff.mpr hγM
    have hfinM : Module.finrank K M = 2 := (hproper_finrank M).mp hM
    have hfinγ : Module.finrank K K⟮γ⟯ = 2 := hfin_adjoin_two hγ_not
    have hMeq : K⟮γ⟯ = M := IntermediateField.eq_of_le_of_finrank_eq hle (hfinγ.trans hfinM.symm)
    rw [← hMeq, hsub_adjoin hγ_not, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
      Submodule.map_span, Set.image_singleton]
    have hπγ : π γ ≠ 0 := fun h0 =>
      hγ_not ((Submodule.Quotient.mk_eq_zero B₀).mp h0)
    exact finrank_span_singleton hπγ
  let toProj : {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} → ℙ K (L ⧸ B₀) := fun ⟨M, hM⟩ =>
    (Projectivization.equivSubmodule K (L ⧸ B₀)).symm
      ⟨Submodule.map π M.toSubmodule, hmap_finrank hM⟩
  have hleft : Function.LeftInverse toProj fromProj := by
    intro p
    let γ : L := Classical.choose (Submodule.Quotient.mk_surjective B₀ p.rep)
    have hγ : Submodule.Quotient.mk (p := B₀) γ = p.rep :=
      Classical.choose_spec (Submodule.Quotient.mk_surjective B₀ p.rep)
    have hγ_not : γ ∉ B₀ := fun hmem =>
      p.rep_nonzero (hγ.symm.trans ((Submodule.Quotient.mk_eq_zero B₀).mpr hmem))
    apply Projectivization.submodule_injective
    have happ : (toProj (fromProj p)).submodule =
        Submodule.map π (fromProj p).1.toSubmodule :=
      congrArg Subtype.val
        ((Projectivization.equivSubmodule K (L ⧸ B₀)).apply_symm_apply
          ⟨Submodule.map π (fromProj p).1.toSubmodule, hmap_finrank (fromProj p).2⟩)
    change (toProj (fromProj p)).submodule = p.submodule
    rw [happ]
    change Submodule.map π (K⟮γ⟯).toSubmodule = p.submodule
    rw [hsub_adjoin hγ_not, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
      Submodule.map_span, Set.image_singleton]
    have hπγ_eq : π γ = p.rep := hγ
    rw [hπγ_eq, ← p.submodule_eq]
  have hright : Function.RightInverse toProj fromProj := by
    rintro ⟨M, hM⟩
    have hsub_eq : Submodule.map π (fromProj (toProj ⟨M, hM⟩)).1.toSubmodule =
        Submodule.map π M.toSubmodule := by
      have h1 : (toProj ⟨M, hM⟩).submodule = Submodule.map π M.toSubmodule :=
        congrArg Subtype.val
          ((Projectivization.equivSubmodule K (L ⧸ B₀)).apply_symm_apply
            ⟨Submodule.map π M.toSubmodule, hmap_finrank hM⟩)
      have h2 : (toProj (fromProj (toProj ⟨M, hM⟩))).submodule =
          Submodule.map π (fromProj (toProj ⟨M, hM⟩)).1.toSubmodule :=
        congrArg Subtype.val
          ((Projectivization.equivSubmodule K (L ⧸ B₀)).apply_symm_apply
            ⟨Submodule.map π (fromProj (toProj ⟨M, hM⟩)).1.toSubmodule,
              hmap_finrank (fromProj (toProj ⟨M, hM⟩)).2⟩)
      rw [← h2, hleft (toProj ⟨M, hM⟩), h1]
    have hcomap := congrArg (Submodule.comap π) hsub_eq
    have hsup₁ : (fromProj (toProj ⟨M, hM⟩)).1.toSubmodule ⊔ B₀ =
        (fromProj (toProj ⟨M, hM⟩)).1.toSubmodule :=
      sup_eq_left.mpr (fun _ hx => bot_le (a := (fromProj (toProj ⟨M, hM⟩)).1) hx)
    have hsup₂ : M.toSubmodule ⊔ B₀ = M.toSubmodule :=
      sup_eq_left.mpr (fun _ hx => bot_le (a := M) hx)
    rw [Submodule.comap_map_eq, Submodule.comap_map_eq, Submodule.ker_mkQ, hsup₁, hsup₂] at hcomap
    apply Subtype.ext
    ext x
    exact SetLike.ext_iff.mp hcomap x
  exact ⟨fromProj, toProj, hleft, hright⟩

/-- Explicit characterization of `intermediateFieldEquivProjQuotOfSqMem`: for every `γ ∈ L ∖ K`,
the projective point `[γ mod K] ∈ ℙ K (L ⧸ K)` corresponds to the quadratic intermediate field
`K(γ)`. -/
theorem intermediateFieldEquivProjQuotOfSqMem_mk
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hfin : Module.finrank K L = 4)
    (hsq : ∀ γ : L, γ ^ 2 ∈ Set.range (algebraMap K L))
    (γ : L) (hγ : (⊥ : IntermediateField K L).toSubmodule.mkQ γ ≠ 0) :
    ((intermediateFieldEquivProjQuotOfSqMem hfin hsq)
      (Projectivization.mk K ((⊥ : IntermediateField K L).toSubmodule.mkQ γ) hγ)).1 = K⟮γ⟯ := by
  let B₀ : Submodule K L := (⊥ : IntermediateField K L).toSubmodule
  let p : ℙ K (L ⧸ B₀) := Projectivization.mk K (B₀.mkQ γ) hγ
  let γ₀ : L := Classical.choose (Submodule.Quotient.mk_surjective B₀ p.rep)
  have hγ₀ : Submodule.Quotient.mk (p := B₀) γ₀ = p.rep :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective B₀ p.rep)
  unfold intermediateFieldEquivProjQuotOfSqMem
  change K⟮γ₀⟯ = K⟮γ⟯
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K (B₀.mkQ γ) hγ
  have hquot_eq : Submodule.Quotient.mk (p := B₀) ((a : K) • γ - γ₀) = 0 := by
    rw [Submodule.Quotient.mk_sub, hγ₀]
    change B₀.mkQ ((a : K) • γ) - p.rep = 0
    rw [map_smul, ← Units.smul_def, ha, sub_self]
  have hmem_B₀ : (a : K) • γ - γ₀ ∈ B₀ := (Submodule.Quotient.mk_eq_zero B₀).mp hquot_eq
  change (a : K) • γ - γ₀ ∈ (⊥ : IntermediateField K L) at hmem_B₀
  rw [IntermediateField.mem_bot] at hmem_B₀
  obtain ⟨b, hb⟩ := hmem_B₀
  rw [Algebra.smul_def] at hb
  have hγ₀_eq : γ₀ = algebraMap K L a * γ - algebraMap K L b := by linear_combination hb
  have ha0 : algebraMap K L (a : K) ≠ 0 :=
    (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr a.ne_zero
  have hγ_eq : γ = (algebraMap K L (a : K))⁻¹ * (γ₀ + algebraMap K L b) := by
    rw [hγ₀_eq, sub_add_cancel, inv_mul_cancel_left₀ ha0]
  refine le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr ?_)
    (IntermediateField.adjoin_simple_le_iff.mpr ?_)
  · rw [hγ₀_eq]
    exact sub_mem (mul_mem (K⟮γ⟯.algebraMap_mem _) (IntermediateField.mem_adjoin_simple_self K γ))
      (K⟮γ⟯.algebraMap_mem _)
  · rw [hγ_eq]
    exact mul_mem (inv_mem (K⟮γ₀⟯.algebraMap_mem _))
      (add_mem (IntermediateField.mem_adjoin_simple_self K γ₀) (K⟮γ₀⟯.algebraMap_mem _))

/-- **Exercise 13.3(iv)** (§13.2, printed p. 109 / PDF p. 117):
In the case where `p = 2` (`J = ℤ₂(α)` with `α` transcendental over `ℤ₂`, `K = J(β)` with `β`
transcendental over `J`, and `L : K` a splitting field extension for `(x² - α)(x² - β)`), find all
the intermediate fields `L : M : K`:
1. Every intermediate field `M` is either `K` (`⊥`, `[M : K] = 1`), `L` (`⊤`, `[M : K] = 4`), or a
   proper non-trivial quadratic intermediate field (`M ≠ ⊥ ∧ M ≠ ⊤`, `[M : K] = 2`).
2. There exist unique square roots `u, v ∈ L` with `u² = α` and `v² = β`; `(1, u, v, uv)` is a
   `K`-basis of `L`; and the proper non-trivial intermediate fields stand in explicit bijection
   `e : ℙ K (Fin 3 → K) ≃ {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤}` with the projective plane
   `ℙ²(K)`, sending `[c₀ : c₁ : c₂]` (`c ≠ 0`) to `K(c₀ u + c₁ v + c₂ uv)` (and canonically with
   `ℙ K (L ⧸ K)` via `intermediateFieldEquivProjQuotOfSqMem`).
3. There are infinitely many proper non-trivial intermediate fields. -/
theorem exercise_13_3_iv {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod 2) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod 2) α) (hJ : (ZMod 2)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly 2 α β)) :
    (∀ M : IntermediateField K L,
      M = ⊥ ∨ M = ⊤ ∨ (M ≠ ⊥ ∧ M ≠ ⊤ ∧ Module.finrank K M = 2 ∧ extDegree K M = 2)) ∧
    (∃ (u v : L) (_ : Module.Basis (Fin 4) K L)
        (e : ℙ K (Fin 3 → K) ≃ {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤}),
      u ^ 2 = algebraMap K L (algebraMap J K α) ∧
      v ^ 2 = algebraMap K L β ∧
      (∀ x : L, x ^ 2 = algebraMap K L (algebraMap J K α) → x = u) ∧
      (∀ x : L, x ^ 2 = algebraMap K L β → x = v) ∧
      (∀ (c : Fin 3 → K) (hc : c ≠ 0),
        (e (Projectivization.mk K c hc)).1 =
          K⟮c 0 • u + c 1 • v + c 2 • (u * v)⟯)) ∧
    Infinite {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} := by
  have hsp : Polynomial.IsSplittingField K L (exercise_13_3_poly 2 α β) :=
    (isGarlingSplittingField_iff K L _).mp hL
  have _ : FiniteDimensional K L :=
    Polynomial.IsSplittingField.finiteDimensional L (exercise_13_3_poly 2 α β)
  obtain ⟨u, v, hu, hv, hu_uniq, hv_uniq, hfin_u, hfin_Ku_L, hfin_KL, hadj_uv⟩ :=
    exercise_13_3_roots_and_tower (p := 2) hα hJ hβ hK hL
  have hfin4 : Module.finrank K L = 4 := by simpa using hfin_KL
  have hsq : ∀ γ : L, γ ^ 2 ∈ Set.range (algebraMap K L) :=
    exercise_13_3_ii (p := 2) hα hJ hβ hK hL
  let B₀ : Submodule K L := (⊥ : IntermediateField K L).toSubmodule
  let π : L →ₗ[K] L ⧸ B₀ := B₀.mkQ
  have hfin_B₀ : Module.finrank K B₀ = 1 := by
    have hB₀_range : B₀ = LinearMap.range (Algebra.linearMap K L) := by
      ext x; change x ∈ (⊥ : IntermediateField K L) ↔ _; rw [IntermediateField.mem_bot]; rfl
    rw [hB₀_range, ← (LinearEquiv.ofInjective (Algebra.linearMap K L)
      (algebraMap K L).injective).finrank_eq, Module.finrank_self]
  have htrichotomy : ∀ M : IntermediateField K L,
      M = ⊥ ∨ M = ⊤ ∨ (M ≠ ⊥ ∧ M ≠ ⊤ ∧ Module.finrank K M = 2 ∧ extDegree K M = 2) := by
    intro M
    by_cases hbot : M = ⊥
    · exact Or.inl hbot
    · by_cases htop : M = ⊤
      · exact Or.inr (Or.inl htop)
      · right; right
        have hmul : Module.finrank K M * Module.finrank M L = 4 := by
          rw [Module.finrank_mul_finrank K M L, hfin4]
        have hposM : 0 < Module.finrank K M := Module.finrank_pos
        have hposML : 0 < Module.finrank M L := Module.finrank_pos
        have hle4 : Module.finrank K M ≤ 4 := by nlinarith
        have hne1 : Module.finrank K M ≠ 1 := by
          intro h1; apply hbot
          have heq : B₀ = M.toSubmodule :=
            Submodule.eq_of_le_of_finrank_eq (bot_le : (⊥ : IntermediateField K L) ≤ M)
              (hfin_B₀.trans h1.symm)
          ext x; exact SetLike.ext_iff.mp heq.symm x
        have hne4 : Module.finrank K M ≠ 4 := by
          intro h4; apply htop
          have heq : M.toSubmodule = ⊤ :=
            Submodule.eq_of_le_of_finrank_eq le_top (by
              change Module.finrank K ↥M = _
              rw [h4, finrank_top, hfin4])
          ext x; exact SetLike.ext_iff.mp heq x
        have hfin2 : Module.finrank K M = 2 := by
          interval_cases hm : Module.finrank K M <;> omega
        have hext2 : extDegree K M = 2 := by
          rw [extDegree_eq_finrank K M, hfin2]; rfl
        exact ⟨hbot, htop, hfin2, hext2⟩
  -- Build the `K`-basis `(1, u, v, u * v)` of `L`
  have hu_not_B₀ : u ∉ B₀ := by
    intro hm
    have h1 : Module.finrank K K⟮u⟯ = 1 := by
      have heq : K⟮u⟯ = ⊥ := IntermediateField.adjoin_simple_le_iff.mpr hm |>.antisymm bot_le
      rw [heq]; exact hfin_B₀
    omega
  have hKu_sub : (K⟮u⟯).toSubmodule = B₀ ⊔ Submodule.span K {u} := by
    have hle : B₀ ⊔ Submodule.span K {u} ≤ (K⟮u⟯).toSubmodule := by
      refine sup_le (bot_le : (⊥ : IntermediateField K L) ≤ K⟮u⟯) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact IntermediateField.mem_adjoin_simple_self K u
    have hlt : B₀ < B₀ ⊔ Submodule.span K {u} :=
      lt_of_le_of_ne le_sup_left fun heq =>
        hu_not_B₀ (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    have hgt1 : 1 < Module.finrank K ↥(B₀ ⊔ Submodule.span K {u}) := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt; rwa [hfin_B₀] at h
    have hfin_u' : Module.finrank K (K⟮u⟯).toSubmodule = 2 := hfin_u
    have hle2 : Module.finrank K ↥(B₀ ⊔ Submodule.span K {u}) ≤ 2 :=
      (Submodule.finrank_mono hle).trans_eq hfin_u'
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  let B_Ku : Submodule K⟮u⟯ L := (⊥ : IntermediateField K⟮u⟯ L).toSubmodule
  have hfin_B_Ku : Module.finrank K⟮u⟯ B_Ku = 1 := by
    have hrange : B_Ku = LinearMap.range (Algebra.linearMap K⟮u⟯ L) := by
      ext x; change x ∈ (⊥ : IntermediateField K⟮u⟯ L) ↔ _; rw [IntermediateField.mem_bot]; rfl
    rw [hrange, ← (LinearEquiv.ofInjective (Algebra.linearMap K⟮u⟯ L)
      (algebraMap K⟮u⟯ L).injective).finrank_eq, Module.finrank_self]
  have huv_top : K⟮u⟯⟮v⟯ = (⊤ : IntermediateField K⟮u⟯ L) := by
    ext x; simp only [IntermediateField.mem_top, iff_true]
    have hx : x ∈ (K⟮u⟯⟮v⟯).restrictScalars K := by
      rw [IntermediateField.adjoin_simple_adjoin_simple, hadj_uv]; trivial
    exact hx
  have hv_not_Ku : v ∉ B_Ku := by
    intro hm
    have heq : K⟮u⟯⟮v⟯ = ⊥ :=
      (IntermediateField.adjoin_simple_le_iff.mpr hm).antisymm bot_le
    have h1 : Module.finrank K⟮u⟯ L = 1 := by
      rw [← IntermediateField.topEquiv.toLinearEquiv.finrank_eq (R := K⟮u⟯), ← huv_top, heq]
      exact hfin_B_Ku
    omega
  have hL_Ku_sub : (⊤ : Submodule K⟮u⟯ L) = B_Ku ⊔ Submodule.span K⟮u⟯ {v} := by
    have hlt : B_Ku < B_Ku ⊔ Submodule.span K⟮u⟯ {v} :=
      lt_of_le_of_ne le_sup_left fun heq =>
        hv_not_Ku (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    have hgt1 : 1 < Module.finrank K⟮u⟯ ↥(B_Ku ⊔ Submodule.span K⟮u⟯ {v}) := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt; rwa [hfin_B_Ku] at h
    have hle2 : Module.finrank K⟮u⟯ ↥(B_Ku ⊔ Submodule.span K⟮u⟯ {v}) ≤ 2 := by
      have h := Submodule.finrank_le (B_Ku ⊔ Submodule.span K⟮u⟯ {v})
      rwa [hfin_Ku_L] at h
    exact (Submodule.eq_of_le_of_finrank_eq le_top
      (by rw [finrank_top, hfin_Ku_L]; omega)).symm
  let bvec : Fin 4 → L
    | 0 => 1
    | 1 => u
    | 2 => v
    | 3 => u * v
  have hspan_top : (⊤ : Submodule K L) ≤ Submodule.span K (Set.range bvec) := by
    intro z _
    have hz : z ∈ B_Ku ⊔ Submodule.span K⟮u⟯ {v} := by rw [← hL_Ku_sub]; trivial
    rw [Submodule.mem_sup] at hz
    obtain ⟨x, hx, yv, hyv, rfl⟩ := hz
    change x ∈ (⊥ : IntermediateField K⟮u⟯ L) at hx
    rw [IntermediateField.mem_bot] at hx
    obtain ⟨x₀, rfl⟩ := hx
    rw [Submodule.mem_span_singleton] at hyv
    obtain ⟨y₀, rfl⟩ := hyv
    have hx₀_mem : (x₀ : L) ∈ B₀ ⊔ Submodule.span K {u} := by rw [← hKu_sub]; exact x₀.2
    have hy₀_mem : (y₀ : L) ∈ B₀ ⊔ Submodule.span K {u} := by rw [← hKu_sub]; exact y₀.2
    rw [Submodule.mem_sup] at hx₀_mem hy₀_mem
    obtain ⟨a₀L, ha₀, a₁u, ha₁, hx₀_eq⟩ := hx₀_mem
    obtain ⟨b₀L, hb₀, b₁u, hb₁, hy₀_eq⟩ := hy₀_mem
    change a₀L ∈ (⊥ : IntermediateField K L) at ha₀
    change b₀L ∈ (⊥ : IntermediateField K L) at hb₀
    rw [IntermediateField.mem_bot] at ha₀ hb₀
    obtain ⟨a₀, rfl⟩ := ha₀
    obtain ⟨b₀, rfl⟩ := hb₀
    rw [Submodule.mem_span_singleton] at ha₁ hb₁
    obtain ⟨a₁, rfl⟩ := ha₁
    obtain ⟨b₁, rfl⟩ := hb₁
    have hexpr : (algebraMap K⟮u⟯ L x₀) + y₀ • v =
        a₀ • bvec 0 + a₁ • bvec 1 + b₀ • bvec 2 + b₁ • bvec 3 := by
      have hx_coe : (algebraMap K⟮u⟯ L x₀) = (x₀ : L) := rfl
      have hy_smul : y₀ • v = (y₀ : L) * v := rfl
      rw [hx_coe, hy_smul, ← hx₀_eq, ← hy₀_eq]
      change (algebraMap K L a₀ + a₁ • u) + (algebraMap K L b₀ + b₁ • u) * v =
        a₀ • (1 : L) + a₁ • u + b₀ • v + b₁ • (u * v)
      simp only [Algebra.smul_def]
      ring
    rw [hexpr]
    have hm : ∀ i : Fin 4, bvec i ∈ Submodule.span K (Set.range bvec) := fun i =>
      Submodule.subset_span ⟨i, rfl⟩
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (hm 0))
      (Submodule.smul_mem _ _ (hm 1))) (Submodule.smul_mem _ _ (hm 2)))
      (Submodule.smul_mem _ _ (hm 3))
  let B : Module.Basis (Fin 4) K L :=
    basisOfTopLeSpanOfCardEqFinrank bvec hspan_top (by rw [Fintype.card_fin, hfin4])
  have hB_apply : ⇑B = bvec := coe_basisOfTopLeSpanOfCardEqFinrank bvec hspan_top _
  let φ : (Fin 3 → K) →ₗ[K] L :=
    { toFun := fun c => c 0 • u + c 1 • v + c 2 • (u * v)
      map_add' := fun c d => by simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul] }
  let ψ : (Fin 3 → K) →ₗ[K] L ⧸ B₀ := π.comp φ
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hmem_B₀ : φ c ∈ B₀ := (Submodule.Quotient.mk_eq_zero B₀).mp hc
    change φ c ∈ (⊥ : IntermediateField K L) at hmem_B₀
    rw [IntermediateField.mem_bot] at hmem_B₀
    obtain ⟨d, hd⟩ := hmem_B₀
    have hlin : d • B 0 + (-c 0) • B 1 + (-c 1) • B 2 + (-c 2) • B 3 = 0 := by
      rw [hB_apply]
      change d • (1 : L) + (-c 0) • u + (-c 1) • v + (-c 2) • (u * v) = 0
      simp only [neg_smul]
      have hd' : d • (1 : L) = c 0 • u + c 1 • v + c 2 • (u * v) := by
        rw [Algebra.smul_def, mul_one, hd]; rfl
      linear_combination hd'
    let g : Fin 4 → K := ![d, -c 0, -c 1, -c 2]
    have hsum : ∑ i : Fin 4, g i • B i = 0 := by
      rw [Fin.sum_univ_four]
      simpa [g, add_assoc] using hlin
    have hg0 := Fintype.linearIndependent_iff.mp B.linearIndependent g hsum
    funext i
    fin_cases i
    · have h1 := hg0 1; simp [g] at h1; exact h1
    · have h2 := hg0 2; simp [g] at h2; exact h2
    · have h3 := hg0 3; simp [g] at h3; exact h3
  have hfin_quot : Module.finrank K (L ⧸ B₀) = 3 := by
    have hq := Submodule.finrank_quotient_add_finrank B₀
    rw [hfin_B₀, hfin4] at hq
    omega
  have hfin_eq_quot : Module.finrank K (Fin 3 → K) = Module.finrank K (L ⧸ B₀) := by
    rw [Module.finrank_fin_fun, hfin_quot]
  have hψ_surj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq_quot).mp hψ_inj
  let eLin : (Fin 3 → K) ≃ₗ[K] L ⧸ B₀ := LinearEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
  let eProj : ℙ K (Fin 3 → K) ≃ ℙ K (L ⧸ B₀) :=
    { toFun := Projectivization.map eLin.toLinearMap eLin.injective
      invFun := Projectivization.map eLin.symm.toLinearMap eLin.symm.injective
      left_inv := fun p => by
        have hcomp := Projectivization.map_comp eLin.toLinearMap eLin.injective
          eLin.symm.toLinearMap eLin.symm.injective
        have hid : eLin.symm.toLinearMap.comp eLin.toLinearMap = LinearMap.id :=
          eLin.symm_comp
        have h := congrFun hcomp.symm p
        simpa [Function.comp, hid] using h
      right_inv := fun p => by
        have hcomp := Projectivization.map_comp eLin.symm.toLinearMap eLin.symm.injective
          eLin.toLinearMap eLin.injective
        have hid : eLin.toLinearMap.comp eLin.symm.toLinearMap = LinearMap.id :=
          eLin.comp_symm
        have h := congrFun hcomp.symm p
        simpa [Function.comp, hid] using h }
  let eQuot := intermediateFieldEquivProjQuotOfSqMem hfin4 hsq
  let eCoord : ℙ K (Fin 3 → K) ≃ {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} :=
    eProj.trans eQuot
  have heCoord_mk : ∀ (c : Fin 3 → K) (hc : c ≠ 0),
      (eCoord (Projectivization.mk K c hc)).1 =
        K⟮c 0 • u + c 1 • v + c 2 • (u * v)⟯ := by
    intro c hc
    change (eQuot (Projectivization.map eLin.toLinearMap eLin.injective
      (Projectivization.mk K c hc))).1 = _
    rw [Projectivization.map_mk]
    exact intermediateFieldEquivProjQuotOfSqMem_mk hfin4 hsq (φ c) _
  have _ : Infinite K :=
    Infinite.of_injective (evalRingHom J β) ((evalRingHom_injective_iff J β).1.mpr hβ)
  have _ : Infinite (ℙ K (Fin 3 → K)) := by
    refine Infinite.of_injective
      (fun x : K => Projectivization.mk K ![1, x, 0] (fun h0 => one_ne_zero (congrFun h0 0))) ?_
    intro x y hxy
    rw [Projectivization.mk_eq_mk_iff'] at hxy
    obtain ⟨a, ha⟩ := hxy
    have h0 := congrFun ha 0
    simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one] at h0
    have h1 := congrFun ha 1
    simp only [Pi.smul_apply, Matrix.cons_val_one, smul_eq_mul, h0, one_mul] at h1
    exact h1.symm
  have hM_inf : Infinite {M : IntermediateField K L // M ≠ ⊥ ∧ M ≠ ⊤} :=
    Infinite.of_injective eCoord eCoord.injective
  exact ⟨htrichotomy, ⟨u, v, B, eCoord, hu, hv, hu_uniq, hv_uniq, heCoord_mk⟩, hM_inf⟩

/-- Combined statement of **Exercise 13.3** `(i)`–`(iii)` for every prime `p` (§13.2, printed
p. 109 / PDF p. 117), paired with `exercise_13_3_iv` for `p = 2`. -/
theorem exercise_13_3 {p : ℕ} [Fact p.Prime] {J K L : Type*} [Field J] [Field K] [Field L]
    [Algebra (ZMod p) J] [Algebra J K] [Algebra K L]
    {α : J} (hα : IsGarlingTranscendental (ZMod p) α) (hJ : (ZMod p)⟮α⟯ = ⊤)
    {β : K} (hβ : IsGarlingTranscendental J β) (hK : J⟮β⟯ = ⊤)
    (hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β)) :
    (extDegree K L = (p ^ 2 : ℕ) ∧ Module.finrank K L = p ^ 2) ∧
    (∀ γ : L, γ ^ p ∈ Set.range (algebraMap K L)) ∧
    ¬ IsSimpleExtension K L :=
  ⟨exercise_13_3_i hα hJ hβ hK hL,
   exercise_13_3_ii hα hJ hβ hK hL,
   exercise_13_3_iii hα hJ hβ hK hL⟩

/-- Non-vacuity witness for `Exercise 13.3`: for every prime `p`, the concrete tower
`J = RatFunc (ZMod p)` (`α = X`), `K = RatFunc J` (`β = X`), and
`L = Polynomial.SplittingField (exercise_13_3_poly p α β)` satisfies all hypotheses of
`Exercise 13.3`. -/
theorem exercise_13_3_tower_exists (p : ℕ) [Fact p.Prime] :
    let J := RatFunc (ZMod p)
    let α : J := RatFunc.X
    let K := RatFunc J
    let β : K := RatFunc.X
    let L := Polynomial.SplittingField (exercise_13_3_poly p α β)
    IsGarlingTranscendental (ZMod p) α ∧
    (ZMod p)⟮α⟯ = ⊤ ∧
    IsGarlingTranscendental J β ∧
    J⟮β⟯ = ⊤ ∧
    IsGarlingSplittingField K L (exercise_13_3_poly p α β) ∧
    extDegree K L = (p ^ 2 : ℕ) ∧
    (∀ γ : L, γ ^ p ∈ Set.range (algebraMap K L)) ∧
    ¬ IsSimpleExtension K L := by
  dsimp only
  let J := RatFunc (ZMod p)
  let α : J := RatFunc.X
  let K := RatFunc J
  let β : K := RatFunc.X
  let L := Polynomial.SplittingField (exercise_13_3_poly p α β)
  have hα : IsGarlingTranscendental (ZMod p) α := by
    rintro ⟨q, hq0, hev⟩
    apply hq0
    change Polynomial.aeval (RatFunc.X : J) q = 0 at hev
    have hX : (RatFunc.X : J) = algebraMap (ZMod p)[X] J Polynomial.X :=
      RatFunc.algebraMap_X.symm
    rw [hX, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply] at hev
    exact RatFunc.algebraMap_injective (ZMod p) (hev.trans (map_zero _).symm)
  have hJ : (ZMod p)⟮α⟯ = ⊤ := RatFunc.adjoin_X
  have hβ : IsGarlingTranscendental J β := by
    rintro ⟨q, hq0, hev⟩
    apply hq0
    change Polynomial.aeval (RatFunc.X : K) q = 0 at hev
    have hX : (RatFunc.X : K) = algebraMap J[X] K Polynomial.X :=
      RatFunc.algebraMap_X.symm
    rw [hX, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply] at hev
    exact RatFunc.algebraMap_injective J (hev.trans (map_zero _).symm)
  have hK : J⟮β⟯ = ⊤ := RatFunc.adjoin_X
  have hL : IsGarlingSplittingField K L (exercise_13_3_poly p α β) :=
    (isGarlingSplittingField_iff K L _).mpr inferInstance
  obtain ⟨⟨hext, _⟩, hpow, hnsimp⟩ := exercise_13_3 hα hJ hβ hK hL
  exact ⟨hα, hJ, hβ, hK, hL, hext, hpow, hnsimp⟩

/-! ### Exercise 13.4 (§13.2, printed p. 109 / PDF p. 117 — Fidelity Hold on `only if`) -/

/-- True companion characterization for **Exercise 13.4** (§13.2, printed p. 109 / PDF p. 117):
for a Galois extension `L : K` with Galois group `{σ₁, …, σ_n}` (`σ : Fin n ≃ Γ(L : K)`) and
`α ∈ L`, `L = K(α)` (`K⟮α⟯ = ⊤`) holds if and only if the Galois conjugates `σ₁(α), …, σ_n(α)` are
pairwise distinct (`Function.Injective (fun i => σ i α)`). -/
theorem exercise_13_4_iff_injective {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hGal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) (α : L) :
    K⟮α⟯ = ⊤ ↔ Function.Injective (fun i : Fin n => σ i α) := by
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff K L).mp hGal
  constructor
  · intro hadj i j hij
    let E : IntermediateField K L :=
      { carrier := {x : L | σ i x = σ j x}
        add_mem' := fun {a b} ha hb => by
          change σ i (a + b) = σ j (a + b); rw [map_add, map_add, ha, hb]
        zero_mem' := by change σ i 0 = σ j 0; rw [map_zero, map_zero]
        mul_mem' := fun {a b} ha hb => by
          change σ i (a * b) = σ j (a * b); rw [map_mul, map_mul, ha, hb]
        one_mem' := by change σ i 1 = σ j 1; rw [map_one, map_one]
        inv_mem' := fun {a} ha => by
          change σ i a⁻¹ = σ j a⁻¹; rw [map_inv₀, map_inv₀, ha]
        algebraMap_mem' := fun c => by
          change σ i (algebraMap K L c) = σ j (algebraMap K L c)
          rw [(σ i).commutes, (σ j).commutes] }
    have hle : K⟮α⟯ ≤ E := IntermediateField.adjoin_simple_le_iff.mpr hij
    rw [hadj] at hle
    have hσ_eq : σ i = σ j := AlgEquiv.ext fun x => hle (IntermediateField.mem_top (x := x))
    exact σ.injective hσ_eq
  · intro hinj
    have hbot : K⟮α⟯.fixingSubgroup = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      have hα_fix : α ∈ IntermediateField.fixedField K⟮α⟯.fixingSubgroup := by
        rw [IsGalois.fixedField_fixingSubgroup K⟮α⟯]
        exact IntermediateField.mem_adjoin_simple_self K α
      have hτα : τ α = α := (IntermediateField.mem_fixedField_iff _ α).mp hα_fix τ hτ
      have hij : σ (σ.symm τ) α = σ (σ.symm 1) α := by
        simp only [Equiv.apply_symm_apply, AlgEquiv.one_apply, hτα]
      have heq := congrArg σ (hinj hij)
      simpa only [Equiv.apply_symm_apply] using heq
    rw [← IsGalois.fixedField_fixingSubgroup K⟮α⟯, hbot, IntermediateField.fixedField_bot]

/-- Cardinality form of `exercise_13_4_iff_injective`: `L = K(α)` holds if and only if the set of
Galois conjugates `{σ₁(α), …, σ_n(α)}` has cardinality `n`. -/
theorem exercise_13_4_iff_ncard_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hGal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) (α : L) :
    K⟮α⟯ = ⊤ ↔ (Set.range (fun i : Fin n => σ i α)).ncard = n := by
  classical
  rw [exercise_13_4_iff_injective hGal σ α]
  let f : Fin n → L := fun i => σ i α
  have hrange : Set.range f = ((Finset.univ.image f : Finset L) : Set L) := by
    ext x; simp
  have hncard : (Set.range f).ncard = (Finset.univ.image f).card := by
    rw [hrange, Set.ncard_coe_finset]
  rw [show (Set.range (fun i : Fin n => σ i α)).ncard = (Finset.univ.image f).card from hncard]
  have hcard_eq :
      ((Finset.univ.image f).card = n) ↔
        ((Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card) := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard_eq, Finset.card_image_iff, Finset.coe_univ, Set.injOn_univ]

/-- **Exercise 13.4 — `if` (`⇐`) direction for indexed bases** (§13.2, printed p. 109 / PDF p. 117):
if `L : K` is a Galois extension with Galois group `{σ₁, …, σ_n}` (`σ : Fin n ≃ Γ(L : K)`) and
`(σ₁(α), …, σ_n(α))` is a `K`-basis for `L` (`Module.Basis (Fin n) K L`), then `L = K(α)`
(`K⟮α⟯ = ⊤`). -/
theorem exercise_13_4_if_basis {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hGal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) {α : L}
    (B : Module.Basis (Fin n) K L) (hB : ∀ i : Fin n, B i = σ i α) :
    K⟮α⟯ = ⊤ := by
  have hB_eq : (⇑B : Fin n → L) = fun i => σ i α := funext hB
  exact (exercise_13_4_iff_injective hGal σ α).mpr (hB_eq ▸ B.injective)

/-- **Exercise 13.4 — `if` (`⇐`) direction for subset bases (`Garling.Chapter01.IsBasis`)**
(§13.2, printed p. 109 / PDF p. 117): if `L : K` is a Galois extension with Galois group
`{σ₁, …, σ_n}` (`σ : Fin n ≃ Γ(L : K)`) and `{σ₁(α), …, σ_n(α)}` is a subset basis for `L` over `K`
in Garling's §1.3 sense (`IsBasis K L`), then `L = K(α)` (`K⟮α⟯ = ⊤`). -/
theorem exercise_13_4_if_isBasis_set {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hGal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) {α : L}
    (hB : IsBasis K L (Set.range (fun i : Fin n => σ i α))) :
    K⟮α⟯ = ⊤ := by
  classical
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff K L).mp hGal
  have hn : Module.finrank K L = n := by
    rw [← IsGalois.card_aut_eq_finrank K L]
    exact (Nat.card_congr σ.symm).trans (Nat.card_fin n)
  let S : Set L := Set.range (fun i : Fin n => σ i α)
  let _ : Fintype S := Fintype.ofFinite S
  have hli : LinearIndependent K ((↑) : S → L) := (isLinearlyIndependent_iff S).mp hB.1
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → L)) := by
    rw [Subtype.range_coe, hB.2]
  let Bset : Module.Basis S K L := Module.Basis.mk hli hsp
  have hcardS : Fintype.card S = n := by
    rw [← Module.finrank_eq_card_basis Bset, hn]
  have hsurj : Function.Surjective (Set.rangeFactorization (fun i : Fin n => σ i α)) :=
    fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩
  have hbij : Function.Bijective (Set.rangeFactorization (fun i : Fin n => σ i α)) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨hsurj, by rw [Fintype.card_fin, hcardS]⟩
  have hinj : Function.Injective (fun i : Fin n => σ i α) :=
    Subtype.val_injective.comp hbij.1
  exact (exercise_13_4_iff_injective hGal σ α).mpr hinj

/-- Companion power-basis theorem for **Exercise 13.4** (via Garling's `Theorem 4.4`): if `L : K` is
a Galois extension with Galois group `{σ₁, …, σ_n}` (`σ : Fin n ≃ Γ(L : K)`) and `L = K(α)`, then
`(1, α, …, α^{n-1})` (rather than `(σ₁(α), …, σ_n(α))`) is always a `K`-basis for `L`. -/
theorem exercise_13_4_power_basis {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hGal : IsGarlingGaloisExtension K L) {n : ℕ}
    (σ : Fin n ≃ GarlingGaloisGroup K L) {α : L} (hadj : K⟮α⟯ = ⊤) :
    ∃ B : Module.Basis (Fin n) K L, ∀ i : Fin n, B i = α ^ (i : ℕ) := by
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff K L).mp hGal
  have hn : Module.finrank K L = n := by
    rw [← IsGalois.card_aut_eq_finrank K L]
    exact (Nat.card_congr σ.symm).trans (Nat.card_fin n)
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  let pb := IntermediateField.adjoin.powerBasis hint
  let eAlg : K⟮α⟯ ≃ₐ[K] L := (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
  have hdim : pb.dim = n := by
    have hfin_adj : Module.finrank K K⟮α⟯ = pb.dim := pb.finrank
    rw [← hfin_adj, eAlg.toLinearEquiv.finrank_eq, hn]
  let B : Module.Basis (Fin n) K L :=
    (pb.basis.map eAlg.toLinearEquiv).reindex (finCongr hdim)
  refine ⟨B, fun i => ?_⟩
  have hegen : eAlg pb.gen = α := rfl
  simp only [B, Module.Basis.reindex_apply, Module.Basis.map_apply, PowerBasis.basis_eq_pow,
    finCongr_symm, finCongr_apply, Fin.val_cast, AlgEquiv.toLinearEquiv_apply, map_pow, hegen]

/-- Degenerate (`n = 1`, `L = K = ℚ`, `α = 0`) counterexample to the printed `only if` (`⇒`)
direction of **Exercise 13.4** (§13.2, printed p. 109 / PDF p. 117): `ℚ : ℚ` is a Galois extension
with `1`-element Galois group, and `ℚ(0) = ℚ`, yet `(σ₁(0)) = (0)` is neither linearly independent
nor a basis for `ℚ` over `ℚ` (either as an indexed tuple or as a subset). -/
theorem exercise_13_4_only_if_degenerate_counterexample :
    IsGarlingGaloisExtension ℚ ℚ ∧
    ∃ σ : Fin 1 ≃ GarlingGaloisGroup ℚ ℚ,
      (ℚ⟮(0 : ℚ)⟯ : IntermediateField ℚ ℚ) = ⊤ ∧
      ¬ LinearIndependent ℚ (fun i : Fin 1 => σ i (0 : ℚ)) ∧
      ¬ (∃ B : Module.Basis (Fin 1) ℚ ℚ, ∀ i : Fin 1, B i = σ i (0 : ℚ)) ∧
      ¬ IsBasis ℚ ℚ (Set.range (fun i : Fin 1 => σ i (0 : ℚ))) := by
  have hGal : IsGarlingGaloisExtension ℚ ℚ :=
    (isGarlingGaloisExtension_iff ℚ ℚ).mpr ⟨inferInstance, inferInstance⟩
  let σ : Fin 1 ≃ GarlingGaloisGroup ℚ ℚ :=
    { toFun := fun _ => 1
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun τ => AlgEquiv.ext fun q => by simp }
  have hadj : (ℚ⟮(0 : ℚ)⟯ : IntermediateField ℚ ℚ) = ⊤ := by
    ext q
    simp only [IntermediateField.mem_top, iff_true]
    exact (ℚ⟮(0 : ℚ)⟯ : IntermediateField ℚ ℚ).algebraMap_mem q
  have hnot_li : ¬ LinearIndependent ℚ (fun i : Fin 1 => σ i (0 : ℚ)) := by
    intro hli
    exact hli.ne_zero 0 (map_zero (σ 0))
  have hnot_B : ¬ (∃ B : Module.Basis (Fin 1) ℚ ℚ, ∀ i : Fin 1, B i = σ i (0 : ℚ)) := by
    rintro ⟨B, hB⟩
    exact hnot_li (funext hB ▸ B.linearIndependent)
  have hnot_set : ¬ IsBasis ℚ ℚ (Set.range (fun i : Fin 1 => σ i (0 : ℚ))) := by
    intro hBset
    apply hBset.1
    refine ⟨1, fun _ => 0, fun _ => 1, Function.injective_of_subsingleton _,
      fun _ => ⟨0, map_zero (σ 0)⟩, ⟨0, one_ne_zero⟩, ?_⟩
    simp
  exact ⟨hGal, σ, hadj, hnot_li, hnot_B, hnot_set⟩

/-- Non-degenerate (`n = 2`, `L = ℚ(√2)`, `K = ℚ`, `α = √2`) counterexample to the printed `only if`
(`⇒`) direction of **Exercise 13.4** (§13.2, printed p. 109 / PDF p. 117): `ℚ(√2) : ℚ` is a
degree-`2` Galois extension and `ℚ(√2) = ℚ(α)` for `α = √2`, yet for every enumeration
`σ : Fin 2 ≃ Γ(ℚ(√2) : ℚ)` of the Galois group, `σ₀(α) + σ₁(α) = 0`, so `(σ₀(α), σ₁(α))` is
linearly dependent over `ℚ` and is neither an indexed basis nor a subset basis for `ℚ(√2)` over `ℚ`
— refuting the literal printed biconditional in both formulations. -/
theorem exercise_13_4_only_if_counterexample_qSqrtTwo :
    let L := qSqrtTwoSubfield
    let α : L := ⟨Real.sqrt 2, 0, 1, by simp⟩
    IsGarlingGaloisExtension ℚ L ∧
    extDegree ℚ L = 2 ∧
    (ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ ∧
    Nonempty (Fin 2 ≃ GarlingGaloisGroup ℚ L) ∧
    ∀ σ : Fin 2 ≃ GarlingGaloisGroup ℚ L,
      σ 0 α + σ 1 α = 0 ∧
      ¬ LinearIndependent ℚ (fun i : Fin 2 => σ i α) ∧
      ¬ (∃ B : Module.Basis (Fin 2) ℚ L, ∀ i : Fin 2, B i = σ i α) ∧
      ¬ IsBasis ℚ L (Set.range (fun i : Fin 2 => σ i α)) ∧
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ ↔
          ∃ B : Module.Basis (Fin 2) ℚ L, ∀ i : Fin 2, B i = σ i α) ∧
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ ↔
          IsBasis ℚ L (Set.range (fun i : Fin 2 => σ i α))) := by
  dsimp only
  let L := qSqrtTwoSubfield
  let α : L := ⟨Real.sqrt 2, 0, 1, by simp⟩
  have hdeg : extDegree ℚ L = 2 := examples_4_2_degrees.2.2
  have hα_sq : α ^ 2 = 2 := by
    ext
    change (Real.sqrt 2) ^ 2 = (2 : ℝ)
    exact Real.sq_sqrt (by norm_num)
  have hadj : (ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ := by
    ext ⟨x, r, s, rfl⟩
    simp only [IntermediateField.mem_top, iff_true]
    have hx : (⟨(r : ℝ) + (s : ℝ) * Real.sqrt 2, r, s, rfl⟩ : L) =
        algebraMap ℚ L r + algebraMap ℚ L s * α := by
      ext
      simp [α]
    rw [hx]
    exact add_mem (ℚ⟮α⟯.algebraMap_mem r)
      (mul_mem (ℚ⟮α⟯.algebraMap_mem s) (IntermediateField.mem_adjoin_simple_self ℚ α))
  let g : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 2
  have hg_monic : g.Monic := Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide)
  have hg0 : g ≠ 0 := hg_monic.ne_zero
  have hg_sep : IsGarlingSeparablePoly g :=
    (isGarlingSeparablePoly_iff g).mpr fun q hq _ => hq.separable
  have hfacL : g.map (algebraMap ℚ L) =
      (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (-α)) := by
    have h2 : (algebraMap ℚ L 2 : L) = 2 := map_ofNat _ 2
    calc
      g.map (algebraMap ℚ L) = Polynomial.X ^ 2 - Polynomial.C (2 : L) := by
        simp [g, Polynomial.map_sub, h2]
      _ = Polynomial.X ^ 2 - (Polynomial.C α) ^ 2 := by
        rw [← map_pow, hα_sq]
      _ = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C (-α)) := by
        rw [map_neg, sub_neg_eq_add]
        ring
  have hsplit : IsGarlingSplittingField ℚ L g := by
    rw [isGarlingSplittingField_iff, isSplittingField_iff_intermediateField]
    refine ⟨?_, ?_⟩
    · rw [hfacL]
      exact Polynomial.Splits.mul (Polynomial.Splits.X_sub_C α) (Polynomial.Splits.X_sub_C (-α))
    · rw [eq_top_iff, ← hadj, IntermediateField.adjoin_simple_le_iff]
      apply IntermediateField.subset_adjoin ℚ (g.rootSet L)
      rw [Polynomial.mem_rootSet_of_ne hg0]
      simp [g, hα_sq]
  have hGal : IsGarlingGaloisExtension ℚ L :=
    isGarlingGaloisExtension_of_splittingField hg0 hg_sep hsplit
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff ℚ L).mp hGal
  have hfin2 : Module.finrank ℚ L = 2 := by
    have h := hdeg
    rw [extDegree_eq_finrank ℚ L] at h
    exact Nat.cast_injective h
  have hcard2 : Fintype.card (GarlingGaloisGroup ℚ L) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ L, hfin2]
  have hnonempty : Nonempty (Fin 2 ≃ GarlingGaloisGroup ℚ L) :=
    ⟨(Fintype.equivFinOfCardEq hcard2).symm⟩
  refine ⟨hGal, hdeg, hadj, hnonempty, fun σ => ?_⟩
  have hinj : Function.Injective (fun i : Fin 2 => σ i α) :=
    (exercise_13_4_iff_injective hGal σ α).mp hadj
  have hne01 : σ 0 α ≠ σ 1 α := fun h => by
    have h01 : (0 : Fin 2) = 1 := hinj h
    omega
  have hsq0 : (σ 0 α) ^ 2 = 2 := by
    rw [← map_pow, hα_sq, map_ofNat]
  have hsq1 : (σ 1 α) ^ 2 = 2 := by
    rw [← map_pow, hα_sq, map_ofNat]
  have hprod0 : (σ 0 α - σ 1 α) * (σ 0 α + σ 1 α) = 0 := by
    linear_combination hsq0 - hsq1
  have hsum0 : σ 0 α + σ 1 α = 0 :=
    (mul_eq_zero.mp hprod0).resolve_left (sub_ne_zero.mpr hne01)
  have hnot_li : ¬ LinearIndependent ℚ (fun i : Fin 2 => σ i α) := by
    intro hli
    have h := Fintype.linearIndependent_iff.mp hli (fun _ => (1 : ℚ))
      (by simp [Fin.sum_univ_two, hsum0]) 0
    exact one_ne_zero h
  have hnot_B : ¬ (∃ B : Module.Basis (Fin 2) ℚ L, ∀ i : Fin 2, B i = σ i α) := by
    rintro ⟨B, hB⟩
    exact hnot_li (funext hB ▸ B.linearIndependent)
  have hnot_set : ¬ IsBasis ℚ L (Set.range (fun i : Fin 2 => σ i α)) := by
    intro hBset
    apply hBset.1
    refine ⟨2, fun i => σ i α, fun _ => 1, hinj, fun i => ⟨i, rfl⟩, ⟨0, one_ne_zero⟩, ?_⟩
    simp [Fin.sum_univ_two, hsum0]
  have hnot_iff_B :
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ ↔
          ∃ B : Module.Basis (Fin 2) ℚ L, ∀ i : Fin 2, B i = σ i α) :=
    fun hiff => hnot_B (hiff.mp hadj)
  have hnot_iff_set :
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ L) = ⊤ ↔
          IsBasis ℚ L (Set.range (fun i : Fin 2 => σ i α))) :=
    fun hiff => hnot_set (hiff.mp hadj)
  exact ⟨hsum0, hnot_li, hnot_B, hnot_set, hnot_iff_B, hnot_iff_set⟩

/-! ### Exercise 13.5 (§13.2, printed p. 109 / PDF p. 117) -/

section Exercise135Aux

open Module Polynomial IntermediateField

/-- Generalization of `Field.primitive_element_inf_aux` requiring only `IsIntegral F α` and
`IsSeparable F β` (rather than full separability of `E / F`), used for `Exercise 13.5` when `K` is
infinite. -/
private theorem adjoin_pair_eq_simple_of_isIntegral_of_isSeparable
    {F E : Type*} [Field F] [Infinite F] [Field E] [Algebra F E]
    {α β : E} (hα : IsIntegral F α) (hβ_sep : IsSeparable F β) :
    ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  have hβ : IsIntegral F β := hβ_sep.isIntegral
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := Field.primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯ by
    use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel_right α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (Polynomial.Separable.map hβ_sep)
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map_algebraMap, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map_algebraMap, minpoly.aeval]
  have h_splits : Splits (h.map ιEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).of_dvd (map_ne_zero map_g_ne_zero)
      (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, Algebra.smul_def, map_add, map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert! (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, Polynomial.map_mul, map_X]
    congr

end Exercise135Aux

/-- **Exercise 13.5** (§13.2, printed p. 109 / PDF p. 117) in Mathlib's `FiniteDimensional` +
`Algebra.IsSeparable` formulation: suppose that `L : K` is a finite separable extension and that
`M : L` is a finite simple extension. Then `M : K` is a simple extension. -/
theorem exercise_13_5_separable {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional L M] (hML : IsSimpleExtension L M) :
    IsSimpleExtension K M := by
  have _ : FiniteDimensional K M := Module.Finite.trans L M
  by_cases hfinK : Finite K
  · exact Field.exists_primitive_element_of_finite_bot K M
  · have _ : Infinite K := not_finite_iff_infinite.mp hfinK
    obtain ⟨β₀, hL_top⟩ := Field.exists_primitive_element K L
    obtain ⟨α, hM_top⟩ := hML
    let ι : L →ₐ[K] M := IsScalarTower.toAlgHom K L M
    let β : M := ι β₀
    have hα_int : IsIntegral K α := Algebra.IsIntegral.isIntegral α
    have hβ₀_sep : IsSeparable K β₀ := Algebra.IsSeparable.isSeparable K β₀
    have hmin_eq : minpoly K β = minpoly K β₀ :=
      minpoly.algHom_eq ι ι.injective β₀
    have hβ_sep : IsSeparable K β := by
      unfold IsSeparable at hβ₀_sep ⊢
      rwa [hmin_eq]
    obtain ⟨γ, hγ⟩ := adjoin_pair_eq_simple_of_isIntegral_of_isSeparable hα_int hβ_sep
    refine ⟨γ, ?_⟩
    rw [← hγ]
    let F : IntermediateField K M := K⟮α, β⟯
    have hβ_in_F : β ∈ F :=
      IntermediateField.subset_adjoin K {α, β} (Set.mem_insert_of_mem α rfl)
    have hα_in_F : α ∈ F :=
      IntermediateField.subset_adjoin K {α, β} (Set.mem_insert α {β})
    have hL_in_F : ∀ x : L, algebraMap L M x ∈ F := by
      let F_pre : IntermediateField K L := F.comap ι
      have htop : F_pre = ⊤ := by
        rw [eq_top_iff, ← hL_top, IntermediateField.adjoin_simple_le_iff]
        exact hβ_in_F
      intro x
      have hx : x ∈ F_pre := by rw [htop]; trivial
      exact hx
    let F_L : IntermediateField L M :=
      { F.toSubfield with
        algebraMap_mem' := hL_in_F }
    have hFL_top : F_L = ⊤ := by
      rw [eq_top_iff, ← hM_top, IntermediateField.adjoin_simple_le_iff]
      exact hα_in_F
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ F_L := by rw [hFL_top]; trivial
    exact hx

/-- **Exercise 13.5** (§13.2, printed p. 109 / PDF p. 117) in Garling's literal `IsFiniteExtension`
and `IsGarlingSeparableExtension` vocabulary: suppose that `L : K` is a finite separable extension
and that `M : L` is a finite simple extension. Then `M : K` is a simple extension. -/
theorem exercise_13_5 {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hfinKL : IsFiniteExtension K L) (hsepKL : IsGarlingSeparableExtension K L)
    (hfinLM : IsFiniteExtension L M) (hsimpLM : IsSimpleExtension L M) :
    IsSimpleExtension K M := by
  have _ : FiniteDimensional K L := (isFiniteExtension_iff_moduleFinite K L).mp hfinKL
  have _ : FiniteDimensional L M := (isFiniteExtension_iff_moduleFinite L M).mp hfinLM
  have _ : Algebra.IsSeparable K L :=
    (isGarlingSeparableExtension_iff K L).mp hsepKL
  exact exercise_13_5_separable hsimpLM

/-! ## §13.3 An example (printed p. 109, PDF p. 117) -/

private lemma int_three_dvd_of_dvd_sq {x : ℤ} (h : (3 : ℤ) ∣ x ^ 2) : (3 : ℤ) ∣ x := by
  obtain ⟨k, hk⟩ := h
  have hdiv : x = 3 * (x / 3) + x % 3 := by omega
  have hr0 : 0 ≤ x % 3 := by omega
  have hr3 : x % 3 < 3 := by omega
  set q := x / 3
  set r := x % 3
  interval_cases r
  · exact ⟨q, by omega⟩
  · have h1 : 3 * (3 * q ^ 2 + 2 * q) + 1 = 3 * k := by
      calc
        3 * (3 * q ^ 2 + 2 * q) + 1 = (3 * q + 1) ^ 2 := by ring
        _ = x ^ 2 := by rw [← hdiv]
        _ = 3 * k := hk
    omega
  · have h2 : 3 * (3 * q ^ 2 + 4 * q + 1) + 1 = 3 * k := by
      calc
        3 * (3 * q ^ 2 + 4 * q + 1) + 1 = (3 * q + 2) ^ 2 := by ring
        _ = x ^ 2 := by rw [← hdiv]
        _ = 3 * k := hk
    omega

private lemma int_three_dvd_of_dvd_two_mul_sq {x : ℤ} (h : (3 : ℤ) ∣ 2 * x ^ 2) : (3 : ℤ) ∣ x := by
  obtain ⟨k, hk⟩ := h
  have hdiv : x = 3 * (x / 3) + x % 3 := by omega
  have hr0 : 0 ≤ x % 3 := by omega
  have hr3 : x % 3 < 3 := by omega
  set q := x / 3
  set r := x % 3
  interval_cases r
  · exact ⟨q, by omega⟩
  · have h1 : 3 * (6 * q ^ 2 + 4 * q) + 2 = 3 * k := by
      calc
        3 * (6 * q ^ 2 + 4 * q) + 2 = 2 * (3 * q + 1) ^ 2 := by ring
        _ = 2 * x ^ 2 := by rw [← hdiv]
        _ = 3 * k := hk
    omega
  · have h2 : 3 * (6 * q ^ 2 + 8 * q + 2) + 2 = 3 * k := by
      calc
        3 * (6 * q ^ 2 + 8 * q + 2) + 2 = 2 * (3 * q + 2) ^ 2 := by ring
        _ = 2 * x ^ 2 := by rw [← hdiv]
        _ = 3 * k := hk
    omega

private lemma rat_sq_ne_three (q : ℚ) : q ^ 2 ≠ 3 := by
  intro hq
  have hden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hfrac : ((q.num : ℚ) / (q.den : ℚ)) ^ 2 = 3 := by rw [Rat.num_div_den, hq]
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hden0)] at hfrac
  have hint : q.num ^ 2 = 3 * (q.den : ℤ) ^ 2 := by exact_mod_cast hfrac
  obtain ⟨a₁, ha₁⟩ := int_three_dvd_of_dvd_sq ⟨(q.den : ℤ) ^ 2, hint⟩
  have hb_sq : (q.den : ℤ) ^ 2 = 3 * a₁ ^ 2 := by
    have h9 : 9 * a₁ ^ 2 = 3 * (q.den : ℤ) ^ 2 := by
      calc
        9 * a₁ ^ 2 = (3 * a₁) ^ 2 := by ring
        _ = q.num ^ 2 := by rw [← ha₁]
        _ = 3 * (q.den : ℤ) ^ 2 := hint
    omega
  obtain ⟨b₁, hb₁⟩ := int_three_dvd_of_dvd_sq ⟨a₁ ^ 2, hb_sq⟩
  have hdvd_num : 3 ∣ q.num.natAbs := ⟨a₁.natAbs, by omega⟩
  have hdvd_den : 3 ∣ q.den := ⟨b₁.toNat, by omega⟩
  have hdvd_gcd : 3 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hdvd_num hdvd_den
  rw [q.reduced] at hdvd_gcd
  omega

private lemma rat_sq_ne_six (q : ℚ) : q ^ 2 ≠ 6 := by
  intro hq
  have hden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hfrac : ((q.num : ℚ) / (q.den : ℚ)) ^ 2 = 6 := by rw [Rat.num_div_den, hq]
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hden0)] at hfrac
  have hint : q.num ^ 2 = 6 * (q.den : ℤ) ^ 2 := by exact_mod_cast hfrac
  obtain ⟨a₁, ha₁⟩ :=
    int_three_dvd_of_dvd_sq (x := q.num) ⟨2 * (q.den : ℤ) ^ 2, by linear_combination hint⟩
  have hb_sq : 2 * (q.den : ℤ) ^ 2 = 3 * a₁ ^ 2 := by
    have h9 : 9 * a₁ ^ 2 = 6 * (q.den : ℤ) ^ 2 := by
      calc
        9 * a₁ ^ 2 = (3 * a₁) ^ 2 := by ring
        _ = q.num ^ 2 := by rw [← ha₁]
        _ = 6 * (q.den : ℤ) ^ 2 := hint
    omega
  obtain ⟨b₁, hb₁⟩ := int_three_dvd_of_dvd_two_mul_sq ⟨a₁ ^ 2, hb_sq⟩
  have hdvd_num : 3 ∣ q.num.natAbs := ⟨a₁.natAbs, by omega⟩
  have hdvd_den : 3 ∣ q.den := ⟨b₁.toNat, by omega⟩
  have hdvd_gcd : 3 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hdvd_num hdvd_den
  rw [q.reduced] at hdvd_gcd
  omega

/-- The polynomial `f = x⁴ - 5x² + 6` over `ℚ` in §13.3 (*An example*, printed p. 109 /
PDF p. 117). -/
noncomputable def example_13_3_poly : ℚ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 5 * Polynomial.X ^ 2 + Polynomial.C 6

/-- Factorization `x⁴ - 5x² + 6 = (x² - 2)(x² - 3)` in `ℚ[x]` (§13.3, printed p. 109 /
PDF p. 117). -/
theorem example_13_3_poly_eq_mul :
    example_13_3_poly =
      (Polynomial.X ^ 2 - Polynomial.C 2) * (Polynomial.X ^ 2 - Polynomial.C 3) := by
  unfold example_13_3_poly
  simp only [map_ofNat]
  ring

/-- The biquadratic field `ℚ(√2, √3) ⊆ ℝ` in §13.3 (*An example*, printed p. 109 / PDF p. 117). -/
noncomputable abbrev qSqrtTwoSqrtThree : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({Real.sqrt 2, Real.sqrt 3} : Set ℝ)

/-- `√2` as an element of `ℚ(√2, √3)`. -/
noncomputable def qSqrt2 : qSqrtTwoSqrtThree :=
  ⟨Real.sqrt 2,
    IntermediateField.subset_adjoin ℚ ({Real.sqrt 2, Real.sqrt 3} : Set ℝ) (Set.mem_insert _ _)⟩

/-- `√3` as an element of `ℚ(√2, √3)`. -/
noncomputable def qSqrt3 : qSqrtTwoSqrtThree :=
  ⟨Real.sqrt 3,
    IntermediateField.subset_adjoin ℚ ({Real.sqrt 2, Real.sqrt 3} : Set ℝ)
      (Set.mem_insert_of_mem _ rfl)⟩

/-- `√6 = √2 · √3` as an element of `ℚ(√2, √3)`. -/
noncomputable def qSqrt6 : qSqrtTwoSqrtThree :=
  qSqrt2 * qSqrt3

theorem qSqrt6_coe : (qSqrt6 : ℝ) = Real.sqrt 6 := by
  change Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem qSqrt2_sq : qSqrt2 ^ 2 = 2 := by
  ext
  change (Real.sqrt 2) ^ 2 = 2
  exact Real.sq_sqrt (by norm_num)

theorem qSqrt3_sq : qSqrt3 ^ 2 = 3 := by
  ext
  change (Real.sqrt 3) ^ 2 = 3
  exact Real.sq_sqrt (by norm_num)

theorem qSqrt6_sq : qSqrt6 ^ 2 = 6 := by
  ext
  change (qSqrt6 : ℝ) ^ 2 = 6
  rw [qSqrt6_coe]
  exact Real.sq_sqrt (by norm_num)

theorem qSqrt2_ne_zero : qSqrt2 ≠ 0 := by
  intro h
  have h0 : Real.sqrt 2 = 0 := congrArg Subtype.val h
  linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]

theorem qSqrt3_ne_zero : qSqrt3 ≠ 0 := by
  intro h
  have h0 : Real.sqrt 3 = 0 := congrArg Subtype.val h
  linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]

/-- `ℚ(√2, √3) : ℚ` is a splitting field extension for `f = x⁴ - 5x² + 6 = (x² - 2)(x² - 3)` over
`ℚ`, and hence is a Galois extension (§13.3, printed p. 109 / PDF p. 117). -/
theorem example_13_3_isSplittingField_and_galois :
    IsGarlingSplittingField ℚ qSqrtTwoSqrtThree example_13_3_poly ∧
    IsGarlingGaloisExtension ℚ qSqrtTwoSqrtThree := by
  have hf_monic : example_13_3_poly.Monic := by
    rw [example_13_3_poly_eq_mul]
    exact (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide)).mul
      (Polynomial.monic_X_pow_sub_C (3 : ℚ) (by decide))
  have hf0 : example_13_3_poly ≠ 0 := hf_monic.ne_zero
  have hfac : example_13_3_poly.map (algebraMap ℚ qSqrtTwoSqrtThree) =
      (Polynomial.X - Polynomial.C qSqrt2) * (Polynomial.X - Polynomial.C (-qSqrt2)) *
        ((Polynomial.X - Polynomial.C qSqrt3) * (Polynomial.X - Polynomial.C (-qSqrt3))) := by
    have h2 : (algebraMap ℚ qSqrtTwoSqrtThree 2 : qSqrtTwoSqrtThree) = 2 := map_ofNat _ 2
    have h3 : (algebraMap ℚ qSqrtTwoSqrtThree 3 : qSqrtTwoSqrtThree) = 3 := map_ofNat _ 3
    have hf2 : (Polynomial.X ^ 2 - Polynomial.C (2 : qSqrtTwoSqrtThree)) =
        (Polynomial.X - Polynomial.C qSqrt2) * (Polynomial.X - Polynomial.C (-qSqrt2)) := by
      calc
        Polynomial.X ^ 2 - Polynomial.C (2 : qSqrtTwoSqrtThree)
            = Polynomial.X ^ 2 - (Polynomial.C qSqrt2) ^ 2 := by rw [← map_pow, qSqrt2_sq]
        _ = (Polynomial.X - Polynomial.C qSqrt2) * (Polynomial.X - Polynomial.C (-qSqrt2)) := by
            rw [map_neg, sub_neg_eq_add]; ring
    have hf3 : (Polynomial.X ^ 2 - Polynomial.C (3 : qSqrtTwoSqrtThree)) =
        (Polynomial.X - Polynomial.C qSqrt3) * (Polynomial.X - Polynomial.C (-qSqrt3)) := by
      calc
        Polynomial.X ^ 2 - Polynomial.C (3 : qSqrtTwoSqrtThree)
            = Polynomial.X ^ 2 - (Polynomial.C qSqrt3) ^ 2 := by rw [← map_pow, qSqrt3_sq]
        _ = (Polynomial.X - Polynomial.C qSqrt3) * (Polynomial.X - Polynomial.C (-qSqrt3)) := by
            rw [map_neg, sub_neg_eq_add]; ring
    rw [example_13_3_poly_eq_mul, Polynomial.map_mul]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, h2, h3]
    rw [hf2, hf3]
  have hsp : (example_13_3_poly.map (algebraMap ℚ qSqrtTwoSqrtThree)).Splits := by
    rw [hfac]
    exact Polynomial.Splits.mul
      (Polynomial.Splits.mul (Polynomial.Splits.X_sub_C _) (Polynomial.Splits.X_sub_C _))
      (Polynomial.Splits.mul (Polynomial.Splits.X_sub_C _) (Polynomial.Splits.X_sub_C _))
  have hr2 : qSqrt2 ∈ example_13_3_poly.rootSet qSqrtTwoSqrtThree := by
    rw [Polynomial.mem_rootSet_of_ne hf0, example_13_3_poly_eq_mul]
    simp [qSqrt2_sq]
  have hr3 : qSqrt3 ∈ example_13_3_poly.rootSet qSqrtTwoSqrtThree := by
    rw [Polynomial.mem_rootSet_of_ne hf0, example_13_3_poly_eq_mul]
    simp [qSqrt3_sq]
  have hadj_top :
      IntermediateField.adjoin ℚ (example_13_3_poly.rootSet qSqrtTwoSqrtThree) = ⊤ := by
    let M := IntermediateField.adjoin ℚ (example_13_3_poly.rootSet qSqrtTwoSqrtThree)
    let M_R : IntermediateField ℚ ℝ := M.map qSqrtTwoSqrtThree.val
    have hle : qSqrtTwoSqrtThree ≤ M_R := by
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · exact ⟨qSqrt2, IntermediateField.subset_adjoin _ _ hr2, rfl⟩
      · exact ⟨qSqrt3, IntermediateField.subset_adjoin _ _ hr3, rfl⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hyM, hyx⟩ := hle x.2
    have hy_eq : y = x := Subtype.ext hyx
    exact hy_eq ▸ hyM
  have hsplit : IsGarlingSplittingField ℚ qSqrtTwoSqrtThree example_13_3_poly := by
    rw [isGarlingSplittingField_iff, isSplittingField_iff_intermediateField]
    exact ⟨hsp, hadj_top⟩
  have hsep : IsGarlingSeparablePoly example_13_3_poly :=
    (isGarlingSeparablePoly_iff _).mpr fun q hq _ => hq.separable
  exact ⟨hsplit, isGarlingGaloisExtension_of_splittingField hf0 hsep hsplit⟩

private noncomputable def biquadraticBasisVec : Fin 4 → qSqrtTwoSqrtThree
  | 0 => 1
  | 1 => qSqrt2
  | 2 => qSqrt3
  | 3 => qSqrt6

private lemma rat_add_sqrt2_eq_zero {a b : ℚ}
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb0
    apply sqrt_two_irrational
    refine ⟨-a / b, ?_⟩
    have hbR : (b : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hb0
    push_cast
    field_simp [hbR]
    linarith
  have ha : a = 0 := by
    rw [hb, Rat.cast_zero, zero_mul, add_zero] at h
    exact Rat.cast_eq_zero.mp h
  exact ⟨ha, hb⟩

private lemma biquadraticBasisVec_linearIndependent :
    LinearIndependent ℚ biquadraticBasisVec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hreal : (c 0 : ℝ) + (c 1 : ℝ) * Real.sqrt 2 +
      (c 2 : ℝ) * Real.sqrt 3 + (c 3 : ℝ) * Real.sqrt 6 = 0 := by
    have hsub := congrArg Subtype.val hc
    rw [Fin.sum_univ_four] at hsub
    simpa [biquadraticBasisVec, Algebra.smul_def, qSqrt2, qSqrt3, qSqrt6_coe, add_assoc] using hsub
  have hmul23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrel : (c 0 : ℝ) + (c 1 : ℝ) * Real.sqrt 2 =
      -((c 2 : ℝ) + (c 3 : ℝ) * Real.sqrt 2) * Real.sqrt 3 := by
    linear_combination hreal + (c 3 : ℝ) * hmul23
  have hsq_rel : (((c 0 ^ 2 + 2 * c 1 ^ 2 - 3 * c 2 ^ 2 - 6 * c 3 ^ 2 : ℚ) : ℝ) +
      ((2 * c 0 * c 1 - 6 * c 2 * c 3 : ℚ) : ℝ) * Real.sqrt 2) = 0 := by
    have hsq_both : ((c 0 : ℝ) + (c 1 : ℝ) * Real.sqrt 2) ^ 2 =
        (-((c 2 : ℝ) + (c 3 : ℝ) * Real.sqrt 2) * Real.sqrt 3) ^ 2 :=
      congrArg (· ^ 2) hrel
    have hsq_exp : (c 0 : ℝ) ^ 2 + 2 * (c 0 : ℝ) * (c 1 : ℝ) * Real.sqrt 2 +
        (c 1 : ℝ) ^ 2 * Real.sqrt 2 ^ 2 =
        ((c 2 : ℝ) ^ 2 + 2 * (c 2 : ℝ) * (c 3 : ℝ) * Real.sqrt 2 +
          (c 3 : ℝ) ^ 2 * Real.sqrt 2 ^ 2) * Real.sqrt 3 ^ 2 := by
      linear_combination hsq_both
    rw [hsq2, hsq3] at hsq_exp
    push_cast
    linear_combination hsq_exp
  obtain ⟨heq1_sub, heq2_sub⟩ := rat_add_sqrt2_eq_zero hsq_rel
  have heq1 : c 0 ^ 2 + 2 * c 1 ^ 2 = 3 * c 2 ^ 2 + 6 * c 3 ^ 2 := by linarith
  have heq2 : c 0 * c 1 = 3 * c 2 * c 3 := by linarith
  have hnorm_sq : (c 0 ^ 2 - 2 * c 1 ^ 2) ^ 2 = (3 * c 2 ^ 2 - 6 * c 3 ^ 2) ^ 2 := by
    calc
      (c 0 ^ 2 - 2 * c 1 ^ 2) ^ 2
          = (c 0 ^ 2 + 2 * c 1 ^ 2) ^ 2 - 8 * (c 0 * c 1) ^ 2 := by ring
      _ = (3 * c 2 ^ 2 + 6 * c 3 ^ 2) ^ 2 - 8 * (3 * c 2 * c 3) ^ 2 := by rw [heq1, heq2]
      _ = (3 * c 2 ^ 2 - 6 * c 3 ^ 2) ^ 2 := by ring
  have hc23 : c 2 = 0 ∧ c 3 = 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hnorm_sq with hpos | hneg
    · have hc0_3 : c 0 ^ 2 = 3 * c 2 ^ 2 := by linarith
      have hc1_3 : c 1 ^ 2 = 3 * c 3 ^ 2 := by linarith
      have hc2 : c 2 = 0 := by
        by_contra h2
        apply rat_sq_ne_three (c 0 / c 2)
        rw [div_pow, hc0_3, mul_div_cancel_right₀ _ (pow_ne_zero 2 h2)]
      have hc3 : c 3 = 0 := by
        by_contra h3
        apply rat_sq_ne_three (c 1 / c 3)
        rw [div_pow, hc1_3, mul_div_cancel_right₀ _ (pow_ne_zero 2 h3)]
      exact ⟨hc2, hc3⟩
    · have hc0_6 : c 0 ^ 2 = 6 * c 3 ^ 2 := by linarith
      have hc1_6 : (2 * c 1) ^ 2 = 6 * c 2 ^ 2 := by linear_combination heq1 - hneg
      have hc3 : c 3 = 0 := by
        by_contra h3
        apply rat_sq_ne_six (c 0 / c 3)
        rw [div_pow, hc0_6, mul_div_cancel_right₀ _ (pow_ne_zero 2 h3)]
      have hc2 : c 2 = 0 := by
        by_contra h2
        apply rat_sq_ne_six (2 * c 1 / c 2)
        rw [div_pow, hc1_6, mul_div_cancel_right₀ _ (pow_ne_zero 2 h2)]
      exact ⟨hc2, hc3⟩
  have h01_real : (c 0 : ℝ) + (c 1 : ℝ) * Real.sqrt 2 = 0 := by
    rw [hc23.1, hc23.2] at hrel
    simpa using hrel
  obtain ⟨hc0, hc1⟩ := rat_add_sqrt2_eq_zero h01_real
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc23.1
  · exact hc23.2

/-- `[ℚ(√2, √3) : ℚ] = 4` (§13.3, printed p. 109 / PDF p. 117). -/
theorem example_13_3_finrank_and_degree :
    Module.finrank ℚ qSqrtTwoSqrtThree = 4 ∧ extDegree ℚ qSqrtTwoSqrtThree = 4 := by
  have _ : FiniteDimensional ℚ qSqrtTwoSqrtThree :=
    ((isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp
      example_13_3_isSplittingField_and_galois.2).1
  have hle_two_s2 : Module.finrank ℚ ℚ⟮Real.sqrt 2⟯ ≤ 2 := by
    let p2 : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 2
    have hm2 : p2.Monic := Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide)
    have he2 : Polynomial.aeval (Real.sqrt 2) p2 = 0 := by
      simp [p2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [IntermediateField.adjoin.finrank ⟨p2, hm2, he2⟩]
    have hdvd := minpoly.dvd ℚ (Real.sqrt 2) he2
    exact (Polynomial.natDegree_le_of_dvd hdvd hm2.ne_zero).trans_eq
      (Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (2 : ℚ)))
  have hle_two_s3 : Module.finrank ℚ⟮Real.sqrt 2⟯ ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯ ≤ 2 := by
    let p3 : (ℚ⟮Real.sqrt 2⟯)[X] := Polynomial.X ^ 2 - Polynomial.C 3
    have hm3 : p3.Monic := Polynomial.monic_X_pow_sub_C (3 : ℚ⟮Real.sqrt 2⟯) (by decide)
    have h3coe : ((3 : ℚ⟮Real.sqrt 2⟯) : ℝ) = 3 := map_ofNat (ℚ⟮Real.sqrt 2⟯).val 3
    have he3 : Polynomial.aeval (Real.sqrt 3) p3 = 0 := by
      simp [p3, h3coe, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [IntermediateField.adjoin.finrank ⟨p3, hm3, he3⟩]
    have hdvd := minpoly.dvd ℚ⟮Real.sqrt 2⟯ (Real.sqrt 3) he3
    exact (Polynomial.natDegree_le_of_dvd hdvd hm3.ne_zero).trans_eq
      (Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (3 : ℚ⟮Real.sqrt 2⟯)))
  have hle4 : Module.finrank ℚ qSqrtTwoSqrtThree ≤ 4 := by
    have heq_set : (ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯).restrictScalars ℚ = qSqrtTwoSqrtThree :=
      IntermediateField.adjoin_simple_adjoin_simple ℚ (Real.sqrt 2) (Real.sqrt 3)
    let eLin : (ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯) ≃ₗ[ℚ] qSqrtTwoSqrtThree :=
      (IntermediateField.equivOfEq heq_set).toLinearEquiv
    have hmul : Module.finrank ℚ ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯ =
        Module.finrank ℚ ℚ⟮Real.sqrt 2⟯ *
          Module.finrank ℚ⟮Real.sqrt 2⟯ ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯ :=
      (Module.finrank_mul_finrank ℚ ℚ⟮Real.sqrt 2⟯ ℚ⟮Real.sqrt 2⟯⟮Real.sqrt 3⟯).symm
    rw [← eLin.finrank_eq, hmul]
    exact Nat.mul_le_mul hle_two_s2 hle_two_s3
  have hge4 : 4 ≤ Module.finrank ℚ qSqrtTwoSqrtThree := by
    have hspan_card :
        Module.finrank ℚ (Submodule.span ℚ (Set.range biquadraticBasisVec)) = 4 := by
      rw [finrank_span_eq_card biquadraticBasisVec_linearIndependent, Fintype.card_fin]
    rw [← hspan_card]
    exact Submodule.finrank_le _
  have hfin4 : Module.finrank ℚ qSqrtTwoSqrtThree = 4 := le_antisymm hle4 hge4
  have hdeg4 : extDegree ℚ qSqrtTwoSqrtThree = 4 := by
    rw [extDegree_eq_finrank ℚ qSqrtTwoSqrtThree, hfin4]
    rfl
  exact ⟨hfin4, hdeg4⟩

private lemma biquadraticBasisVec_span :
    ⊤ ≤ Submodule.span ℚ (Set.range biquadraticBasisVec) := by
  have _ : FiniteDimensional ℚ qSqrtTwoSqrtThree :=
    ((isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp
      example_13_3_isSplittingField_and_galois.2).1
  have hspan_top : Submodule.span ℚ (Set.range biquadraticBasisVec) = ⊤ := by
    refine Submodule.eq_of_le_of_finrank_eq le_top ?_
    rw [finrank_span_eq_card biquadraticBasisVec_linearIndependent, Fintype.card_fin,
      finrank_top, example_13_3_finrank_and_degree.1]
  rw [hspan_top]

/-- The `ℚ`-basis `(1, √2, √3, √6)` of `ℚ(√2, √3)` (§13.3, p. 109). -/
noncomputable def biquadraticBasis : Module.Basis (Fin 4) ℚ qSqrtTwoSqrtThree :=
  Module.Basis.mk biquadraticBasisVec_linearIndependent biquadraticBasisVec_span

@[simp]
theorem biquadraticBasis_zero : biquadraticBasis 0 = 1 := by
  rw [biquadraticBasis, Module.Basis.mk_apply]; rfl

@[simp]
theorem biquadraticBasis_one : biquadraticBasis 1 = qSqrt2 := by
  rw [biquadraticBasis, Module.Basis.mk_apply]; rfl

@[simp]
theorem biquadraticBasis_two : biquadraticBasis 2 = qSqrt3 := by
  rw [biquadraticBasis, Module.Basis.mk_apply]; rfl

@[simp]
theorem biquadraticBasis_three : biquadraticBasis 3 = qSqrt6 := by
  rw [biquadraticBasis, Module.Basis.mk_apply]; rfl

private lemma biquadraticBasis_expand (x : qSqrtTwoSqrtThree) :
    x = biquadraticBasis.repr x 0 • (1 : qSqrtTwoSqrtThree) +
      biquadraticBasis.repr x 1 • qSqrt2 +
      biquadraticBasis.repr x 2 • qSqrt3 +
      biquadraticBasis.repr x 3 • qSqrt6 := by
  have h := (biquadraticBasis.sum_repr x).symm
  rw [Fin.sum_univ_four, biquadraticBasis_zero, biquadraticBasis_one, biquadraticBasis_two,
    biquadraticBasis_three] at h
  exact h

private noncomputable def biquadraticAutLinear (s₁ s₂ : ℚ) :
    qSqrtTwoSqrtThree →ₗ[ℚ] qSqrtTwoSqrtThree :=
  biquadraticBasis.constr ℚ ![1, s₁ • qSqrt2, s₂ • qSqrt3, (s₁ * s₂) • qSqrt6]

private lemma biquadraticAutLinear_one (s₁ s₂ : ℚ) :
    biquadraticAutLinear s₁ s₂ 1 = 1 := by
  conv_lhs => rw [← biquadraticBasis_zero]
  rw [biquadraticAutLinear, Module.Basis.constr_basis]; rfl

private lemma biquadraticAutLinear_qSqrt2 (s₁ s₂ : ℚ) :
    biquadraticAutLinear s₁ s₂ qSqrt2 = s₁ • qSqrt2 := by
  conv_lhs => rw [← biquadraticBasis_one]
  rw [biquadraticAutLinear, Module.Basis.constr_basis]; rfl

private lemma biquadraticAutLinear_qSqrt3 (s₁ s₂ : ℚ) :
    biquadraticAutLinear s₁ s₂ qSqrt3 = s₂ • qSqrt3 := by
  conv_lhs => rw [← biquadraticBasis_two]
  rw [biquadraticAutLinear, Module.Basis.constr_basis]; rfl

private lemma biquadraticAutLinear_qSqrt6 (s₁ s₂ : ℚ) :
    biquadraticAutLinear s₁ s₂ qSqrt6 = (s₁ * s₂) • qSqrt6 := by
  conv_lhs => rw [← biquadraticBasis_three]
  rw [biquadraticAutLinear, Module.Basis.constr_basis]; rfl

private lemma biquadraticAutLinear_comp (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) :
    (biquadraticAutLinear s₁ s₂).comp (biquadraticAutLinear s₁ s₂) = LinearMap.id := by
  refine biquadraticBasis.ext fun i => ?_
  fin_cases i
  · simp [biquadraticAutLinear_one]
  · simp [biquadraticAutLinear_qSqrt2, smul_smul, ← sq, hs₁]
  · simp [biquadraticAutLinear_qSqrt3, smul_smul, ← sq, hs₂]
  · have hs12 : (s₁ * s₂) * (s₁ * s₂) = 1 := by linear_combination s₂ ^ 2 * hs₁ + hs₂
    simp [biquadraticAutLinear_qSqrt6, smul_smul, hs12]

private lemma biquadraticAutLinear_map_mul (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1)
    (x y : qSqrtTwoSqrtThree) :
    biquadraticAutLinear s₁ s₂ (x * y) =
      biquadraticAutLinear s₁ s₂ x * biquadraticAutLinear s₁ s₂ y := by
  let f := biquadraticAutLinear s₁ s₂
  let c := biquadraticBasis.repr x
  let d := biquadraticBasis.repr y
  have hx : x = c 0 • (1 : qSqrtTwoSqrtThree) + c 1 • qSqrt2 + c 2 • qSqrt3 + c 3 • qSqrt6 :=
    biquadraticBasis_expand x
  have hy : y = d 0 • (1 : qSqrtTwoSqrtThree) + d 1 • qSqrt2 + d 2 • qSqrt3 + d 3 • qSqrt6 :=
    biquadraticBasis_expand y
  have hf_expand : ∀ a₀ a₁ a₂ a₃ : ℚ,
      f (a₀ • (1 : qSqrtTwoSqrtThree) + a₁ • qSqrt2 + a₂ • qSqrt3 + a₃ • qSqrt6) =
        a₀ • (1 : qSqrtTwoSqrtThree) + (s₁ * a₁) • qSqrt2 +
          (s₂ * a₂) • qSqrt3 + (s₁ * s₂ * a₃) • qSqrt6 := by
    intro a₀ a₁ a₂ a₃
    simp only [f, map_add, map_smul, biquadraticAutLinear_one, biquadraticAutLinear_qSqrt2,
      biquadraticAutLinear_qSqrt3, biquadraticAutLinear_qSqrt6, smul_smul]
    congr 1; congr 1; congr 1
    · ring_nf
    · ring_nf
    · congr 1; ring
  let A₀ : ℚ := c 0 * d 0 + 2 * c 1 * d 1 + 3 * c 2 * d 2 + 6 * c 3 * d 3
  let A₁ : ℚ := c 0 * d 1 + c 1 * d 0 + 3 * c 2 * d 3 + 3 * c 3 * d 2
  let A₂ : ℚ := c 0 * d 2 + c 2 * d 0 + 2 * c 1 * d 3 + 2 * c 3 * d 1
  let A₃ : ℚ := c 0 * d 3 + c 3 * d 0 + c 1 * d 2 + c 2 * d 1
  have hxy : x * y =
      A₀ • (1 : qSqrtTwoSqrtThree) + A₁ • qSqrt2 + A₂ • qSqrt3 + A₃ • qSqrt6 := by
    rw [hx, hy]
    simp only [A₀, A₁, A₂, A₃, qSqrt6, Algebra.smul_def, map_add, map_mul, map_ofNat]
    linear_combination
      ((algebraMap ℚ qSqrtTwoSqrtThree (c 1) * algebraMap ℚ qSqrtTwoSqrtThree (d 1)) +
        3 * (algebraMap ℚ qSqrtTwoSqrtThree (c 3) * algebraMap ℚ qSqrtTwoSqrtThree (d 3)) +
        (algebraMap ℚ qSqrtTwoSqrtThree (c 1) * algebraMap ℚ qSqrtTwoSqrtThree (d 3) +
          algebraMap ℚ qSqrtTwoSqrtThree (c 3) * algebraMap ℚ qSqrtTwoSqrtThree (d 1)) * qSqrt3) *
        qSqrt2_sq +
      ((algebraMap ℚ qSqrtTwoSqrtThree (c 2) * algebraMap ℚ qSqrtTwoSqrtThree (d 2)) +
        (algebraMap ℚ qSqrtTwoSqrtThree (c 3) * algebraMap ℚ qSqrtTwoSqrtThree (d 3)) *
          qSqrt2 ^ 2 +
        (algebraMap ℚ qSqrtTwoSqrtThree (c 2) * algebraMap ℚ qSqrtTwoSqrtThree (d 3) +
          algebraMap ℚ qSqrtTwoSqrtThree (c 3) * algebraMap ℚ qSqrtTwoSqrtThree (d 2)) * qSqrt2) *
        qSqrt3_sq
  have hs₁L : (algebraMap ℚ qSqrtTwoSqrtThree s₁) ^ 2 = 1 := by
    rw [← map_pow, hs₁, map_one]
  have hs₂L : (algebraMap ℚ qSqrtTwoSqrtThree s₂) ^ 2 = 1 := by
    rw [← map_pow, hs₂, map_one]
  change f (x * y) = f x * f y
  rw [hxy, hf_expand]
  conv_rhs => rw [hx, hy, hf_expand, hf_expand]
  simp only [A₀, A₁, A₂, A₃, qSqrt6, Algebra.smul_def, map_add, map_mul, map_ofNat]
  ring_nf
  rw [qSqrt2_sq, qSqrt3_sq, hs₁L, hs₂L]
  ring

/-- General constructor for the four `ℚ`-automorphisms of `ℚ(√2, √3)` sending `√2 ↦ s₁ √2`,
`√3 ↦ s₂ √3`, and `√6 ↦ s₁ s₂ √6` for `s₁, s₂ ∈ {1, -1}`. -/
noncomputable def biquadraticAut (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) :
    GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
  AlgEquiv.ofLinearEquiv
    ({ biquadraticAutLinear s₁ s₂ with
       invFun := biquadraticAutLinear s₁ s₂
       left_inv := fun x => congrArg (· x) (biquadraticAutLinear_comp s₁ s₂ hs₁ hs₂)
       right_inv := fun x => congrArg (· x) (biquadraticAutLinear_comp s₁ s₂ hs₁ hs₂) } :
      qSqrtTwoSqrtThree ≃ₗ[ℚ] qSqrtTwoSqrtThree)
    (biquadraticAutLinear_one s₁ s₂)
    (biquadraticAutLinear_map_mul s₁ s₂ hs₁ hs₂)

@[simp]
theorem biquadraticAut_qSqrt2 (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) :
    biquadraticAut s₁ s₂ hs₁ hs₂ qSqrt2 = s₁ • qSqrt2 :=
  biquadraticAutLinear_qSqrt2 s₁ s₂

@[simp]
theorem biquadraticAut_qSqrt3 (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) :
    biquadraticAut s₁ s₂ hs₁ hs₂ qSqrt3 = s₂ • qSqrt3 :=
  biquadraticAutLinear_qSqrt3 s₁ s₂

@[simp]
theorem biquadraticAut_qSqrt6 (s₁ s₂ : ℚ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) :
    biquadraticAut s₁ s₂ hs₁ hs₂ qSqrt6 = (s₁ * s₂) • qSqrt6 :=
  biquadraticAutLinear_qSqrt6 s₁ s₂

private lemma algEquiv_smul_rat (σ : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)
    (r : ℚ) (y : qSqrtTwoSqrtThree) : σ (r • y) = r • σ y :=
  σ.toLinearMap.map_smul r y

private lemma biquadratic_algEquiv_ext {φ ψ : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree}
    (h2 : φ qSqrt2 = ψ qSqrt2) (h3 : φ qSqrt3 = ψ qSqrt3) : φ = ψ := by
  have hlin : φ.toLinearMap = ψ.toLinearMap := by
    refine biquadraticBasis.ext fun i => ?_
    fin_cases i
    · simp
    · simpa using h2
    · simpa using h3
    · simp [qSqrt6, map_mul, h2, h3]
  exact AlgEquiv.ext fun x => congrArg (· x) hlin

theorem biquadraticAut_mul (s₁ s₂ t₁ t₂ : ℚ)
    (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) (ht₁ : t₁ ^ 2 = 1) (ht₂ : t₂ ^ 2 = 1) :
    biquadraticAut s₁ s₂ hs₁ hs₂ * biquadraticAut t₁ t₂ ht₁ ht₂ =
      biquadraticAut (s₁ * t₁) (s₂ * t₂)
        (by rw [mul_pow, hs₁, ht₁, one_mul]) (by rw [mul_pow, hs₂, ht₂, one_mul]) := by
  refine biquadratic_algEquiv_ext ?_ ?_
  · simp [AlgEquiv.mul_apply, algEquiv_smul_rat, smul_smul]; rw [mul_comm]
  · simp [AlgEquiv.mul_apply, algEquiv_smul_rat, smul_smul]; rw [mul_comm]

/-- `σ₀ = e`, `σ₁`, `σ₂`, `σ₃ ∈ Γ(ℚ(√2, √3) : ℚ)` in the exact column order of Garling's `2 × 4`
Galois-action table on printed p. 109 (PDF p. 117):
- `σ₀ = e`: `√2 ↦ √2`, `√3 ↦ √3`
- `σ₁`: `√2 ↦ -√2`, `√3 ↦ √3`
- `σ₂`: `√2 ↦ √2`, `√3 ↦ -√3`
- `σ₃`: `√2 ↦ -√2`, `√3 ↦ -√3` -/
noncomputable def example_13_3_sigma0 : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
  biquadraticAut 1 1 (by norm_num) (by norm_num)

noncomputable def example_13_3_sigma1 : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
  biquadraticAut (-1) 1 (by norm_num) (by norm_num)

noncomputable def example_13_3_sigma2 : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
  biquadraticAut 1 (-1) (by norm_num) (by norm_num)

noncomputable def example_13_3_sigma3 : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
  biquadraticAut (-1) (-1) (by norm_num) (by norm_num)

/-- Verification of Garling's `2 × 4` Galois-action table on `√2` and `√3` (plus `√6` and
`σ₀ = 1`) in §13.3 (printed p. 109 / PDF p. 117). -/
theorem example_13_3_action_table :
    example_13_3_sigma0 = 1 ∧
    example_13_3_sigma0 qSqrt2 = qSqrt2 ∧ example_13_3_sigma0 qSqrt3 = qSqrt3 ∧
    example_13_3_sigma1 qSqrt2 = -qSqrt2 ∧ example_13_3_sigma1 qSqrt3 = qSqrt3 ∧
    example_13_3_sigma2 qSqrt2 = qSqrt2 ∧ example_13_3_sigma2 qSqrt3 = -qSqrt3 ∧
    example_13_3_sigma3 qSqrt2 = -qSqrt2 ∧ example_13_3_sigma3 qSqrt3 = -qSqrt3 ∧
    example_13_3_sigma1 qSqrt6 = -qSqrt6 ∧ example_13_3_sigma2 qSqrt6 = -qSqrt6 ∧
    example_13_3_sigma3 qSqrt6 = qSqrt6 := by
  have hσ0 : example_13_3_sigma0 = 1 := by
    refine biquadratic_algEquiv_ext ?_ ?_ <;> simp [example_13_3_sigma0]
  refine ⟨hσ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [example_13_3_sigma0, example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3]

private lemma example_13_3_sigmas_pairwise_ne :
    example_13_3_sigma0 ≠ example_13_3_sigma1 ∧
    example_13_3_sigma0 ≠ example_13_3_sigma2 ∧
    example_13_3_sigma0 ≠ example_13_3_sigma3 ∧
    example_13_3_sigma1 ≠ example_13_3_sigma2 ∧
    example_13_3_sigma1 ≠ example_13_3_sigma3 ∧
    example_13_3_sigma2 ≠ example_13_3_sigma3 := by
  have h2_ne_neg : qSqrt2 ≠ -qSqrt2 := fun h =>
    qSqrt2_ne_zero (by
      have hval : (qSqrt2 : ℝ) = -(qSqrt2 : ℝ) := congrArg Subtype.val h
      ext; change (qSqrt2 : ℝ) = 0; linarith)
  have h3_ne_neg : qSqrt3 ≠ -qSqrt3 := fun h =>
    qSqrt3_ne_zero (by
      have hval : (qSqrt3 : ℝ) = -(qSqrt3 : ℝ) := congrArg Subtype.val h
      ext; change (qSqrt3 : ℝ) = 0; linarith)
  obtain ⟨_, h0_2, h0_3, h1_2, h1_3, h2_2, h2_3, h3_2, h3_3, _, _, _⟩ := example_13_3_action_table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h2_ne_neg (h0_2.symm.trans ((congrArg (· qSqrt2) h).trans h1_2))
  · intro h; exact h3_ne_neg (h0_3.symm.trans ((congrArg (· qSqrt3) h).trans h2_3))
  · intro h; exact h2_ne_neg (h0_2.symm.trans ((congrArg (· qSqrt2) h).trans h3_2))
  · intro h; exact h2_ne_neg (h2_2.symm.trans ((congrArg (· qSqrt2) h.symm).trans h1_2))
  · intro h; exact h3_ne_neg (h1_3.symm.trans ((congrArg (· qSqrt3) h).trans h3_3))
  · intro h; exact h2_ne_neg (h2_2.symm.trans ((congrArg (· qSqrt2) h).trans h3_2))

/-- The Galois group `Γ_ℚ(f) = Γ(ℚ(√2, √3) : ℚ)` consists of the four distinct elements
`{σ₀, σ₁, σ₂, σ₃}` (§13.3, printed p. 109 / PDF p. 117). -/
theorem example_13_3_galoisGroup_univ :
    (Set.univ : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) =
      {example_13_3_sigma0, example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3} := by
  classical
  obtain ⟨hfd, hG⟩ :=
    (isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp example_13_3_isSplittingField_and_galois.2
  have hcard : Fintype.card (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) = 4 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ qSqrtTwoSqrtThree,
      example_13_3_finrank_and_degree.1]
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := example_13_3_sigmas_pairwise_ne
  let S : Finset (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
    {example_13_3_sigma0, example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3}
  have hS_card : S.card = 4 := by
    simp [S, h01, h02, h03, h12, h13, h23]
  have hS_univ : S = Finset.univ := Finset.eq_univ_of_card S (hS_card.trans hcard.symm)
  ext τ
  have hmem : τ ∈ S := by rw [hS_univ]; exact Finset.mem_univ τ
  simpa [S] using hmem

/-- Explicit group isomorphism `Γ_ℚ(f) ≅ ℤ₂ × ℤ₂` (§13.3, printed p. 109 / PDF p. 117), sending
`σ₀ ↦ (0, 0)`, `σ₁ ↦ (1, 0)`, `σ₂ ↦ (0, 1)`, `σ₃ ↦ (1, 1)`. -/
noncomputable def example_13_3_galoisGroupIso :
    GarlingGaloisGroup ℚ qSqrtTwoSqrtThree ≃* Multiplicative (ZMod 2 × ZMod 2) := by
  let signOfZMod2 : ZMod 2 → ℚ := fun x => if x = 0 then 1 else -1
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hs0 : signOfZMod2 0 = 1 := by simp [signOfZMod2]
  have hs1_val : signOfZMod2 1 = -1 := by simp [signOfZMod2, h10]
  have hsign_sq : ∀ x : ZMod 2, (signOfZMod2 x) ^ 2 = 1 := by
    intro x
    rcases hz2 x with rfl | rfl <;> norm_num [hs0, hs1_val]
  have hsign_add : ∀ x y : ZMod 2, signOfZMod2 (x + y) = signOfZMod2 x * signOfZMod2 y := by
    intro x y
    rcases hz2 x with rfl | rfl <;> rcases hz2 y with rfl | rfl <;>
      simp [h11, hs0, hs1_val]
  have hsign_inj : Function.Injective signOfZMod2 := by
    intro a b hab
    rcases hz2 a with rfl | rfl <;> rcases hz2 b with rfl | rfl
    · rfl
    · exfalso; norm_num [hs0, hs1_val] at hab
    · exfalso; norm_num [hs0, hs1_val] at hab
    · rfl
  let invMap : Multiplicative (ZMod 2 × ZMod 2) → GarlingGaloisGroup ℚ qSqrtTwoSqrtThree :=
    fun p =>
      biquadraticAut (signOfZMod2 (Multiplicative.toAdd p).1)
        (signOfZMod2 (Multiplicative.toAdd p).2)
        (hsign_sq _) (hsign_sq _)
  have hinv_mul : ∀ p q : Multiplicative (ZMod 2 × ZMod 2),
      invMap (p * q) = invMap p * invMap q := by
    intro p q
    dsimp only [invMap]
    rw [biquadraticAut_mul]
    congr 1 <;> exact hsign_add _ _
  have hinv_inj : Function.Injective invMap := by
    intro p q hpq
    have h2 := congrArg (· qSqrt2) hpq
    have h3 := congrArg (· qSqrt3) hpq
    simp only [invMap, biquadraticAut_qSqrt2, biquadraticAut_qSqrt3] at h2 h3
    have hs1 : signOfZMod2 (Multiplicative.toAdd p).1 = signOfZMod2 (Multiplicative.toAdd q).1 := by
      have hsub : (signOfZMod2 (Multiplicative.toAdd p).1 -
          signOfZMod2 (Multiplicative.toAdd q).1) • qSqrt2 = 0 := by
        rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right qSqrt2_ne_zero)
    have hs2 : signOfZMod2 (Multiplicative.toAdd p).2 = signOfZMod2 (Multiplicative.toAdd q).2 := by
      have hsub : (signOfZMod2 (Multiplicative.toAdd p).2 -
          signOfZMod2 (Multiplicative.toAdd q).2) • qSqrt3 = 0 := by
        rw [sub_smul, h3, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right qSqrt3_ne_zero)
    exact Multiplicative.toAdd.injective (Prod.ext (hsign_inj hs1) (hsign_inj hs2))
  obtain ⟨hfd, hG⟩ :=
    (isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp example_13_3_isSplittingField_and_galois.2
  have hcard_gal : Fintype.card (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) = 4 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ qSqrtTwoSqrtThree,
      example_13_3_finrank_and_degree.1]
  have hcard_eq : Fintype.card (Multiplicative (ZMod 2 × ZMod 2)) =
      Fintype.card (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) := by
    rw [hcard_gal]; decide
  have hinv_bij : Function.Bijective invMap :=
    (Fintype.bijective_iff_injective_and_card invMap).mpr ⟨hinv_inj, hcard_eq⟩
  exact (MulEquiv.ofBijective
    ({ toFun := invMap
       map_one' := by
         change biquadraticAut 1 1 _ _ = 1
         exact example_13_3_action_table.1
       map_mul' := hinv_mul } :
      Multiplicative (ZMod 2 × ZMod 2) →* GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)
    hinv_bij).symm

/-- Additive form `Additive Γ_ℚ(f) ≃+ ℤ₂ × ℤ₂` of `example_13_3_galoisGroupIso`. -/
noncomputable def example_13_3_galoisGroupAddEquiv :
    Additive (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) ≃+ ZMod 2 × ZMod 2 :=
  MulEquiv.toAdditive example_13_3_galoisGroupIso

/-- The three order-`2` subgroups `{σ₀, σ₁}`, `{σ₀, σ₂}`, and `{σ₀, σ₃}` of `Γ_ℚ(f)` (§13.3,
printed p. 109 / PDF p. 117). -/
noncomputable def example_13_3_subgroup1 : Subgroup (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
  Subgroup.zpowers example_13_3_sigma1

noncomputable def example_13_3_subgroup2 : Subgroup (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
  Subgroup.zpowers example_13_3_sigma2

noncomputable def example_13_3_subgroup3 : Subgroup (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
  Subgroup.zpowers example_13_3_sigma3

private lemma zpowers_involution_carrier {G : Type*} [Group G] {g : G}
    (hsq : g * g = 1) :
    (Subgroup.zpowers g : Set G) = {1, g} := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have hpow2 : g ^ (2 : ℤ) = 1 := by
      rw [zpow_two, hsq]
    have hdiv : n = 2 * (n / 2) + n % 2 := by omega
    have hr0 : 0 ≤ n % 2 := by omega
    have hr2 : n % 2 < 2 := by omega
    rw [hdiv, zpow_add, zpow_mul, hpow2, one_zpow, one_mul]
    set r := n % 2
    interval_cases r
    · exact Or.inl (zpow_zero g)
    · exact Or.inr (zpow_one g)
  · rintro (rfl | hxg)
    · exact ⟨0, zpow_zero g⟩
    · exact ⟨1, hxg ▸ zpow_one g⟩

/-- Classification of the proper non-trivial subgroups of `Γ_ℚ(f)` (§13.3, printed p. 109 /
PDF p. 117): `Γ_ℚ(f)` has exactly three proper non-trivial subgroups, with underlying sets
`{σ₀, σ₁}`, `{σ₀, σ₂}`, and `{σ₀, σ₃}`. -/
theorem example_13_3_nontrivial_subgroups :
    (example_13_3_subgroup1 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) =
      {example_13_3_sigma0, example_13_3_sigma1} ∧
    (example_13_3_subgroup2 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) =
      {example_13_3_sigma0, example_13_3_sigma2} ∧
    (example_13_3_subgroup3 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) =
      {example_13_3_sigma0, example_13_3_sigma3} ∧
    ∀ H : Subgroup (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree),
      (H ≠ ⊥ ∧ H ≠ ⊤) ↔
        (H = example_13_3_subgroup1 ∨ H = example_13_3_subgroup2 ∨ H = example_13_3_subgroup3) := by
  have h0_eq : example_13_3_sigma0 = 1 := example_13_3_action_table.1
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := example_13_3_sigmas_pairwise_ne
  have h1_sq : example_13_3_sigma1 * example_13_3_sigma1 = 1 :=
    biquadratic_algEquiv_ext (by simp [example_13_3_sigma1, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma1, AlgEquiv.mul_apply])
  have h2_sq : example_13_3_sigma2 * example_13_3_sigma2 = 1 :=
    biquadratic_algEquiv_ext (by simp [example_13_3_sigma2, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma2, AlgEquiv.mul_apply])
  have h3_sq : example_13_3_sigma3 * example_13_3_sigma3 = 1 :=
    biquadratic_algEquiv_ext (by simp [example_13_3_sigma3, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma3, AlgEquiv.mul_apply])
  have h12_mul : example_13_3_sigma1 * example_13_3_sigma2 = example_13_3_sigma3 :=
    biquadratic_algEquiv_ext
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
  have h13_mul : example_13_3_sigma1 * example_13_3_sigma3 = example_13_3_sigma2 :=
    biquadratic_algEquiv_ext
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
  have h23_mul : example_13_3_sigma2 * example_13_3_sigma3 = example_13_3_sigma1 :=
    biquadratic_algEquiv_ext
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
      (by simp [example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3, AlgEquiv.mul_apply])
  have hc1 : (example_13_3_subgroup1 : Set _) = {example_13_3_sigma0, example_13_3_sigma1} := by
    rw [example_13_3_subgroup1, zpowers_involution_carrier h1_sq, h0_eq]
  have hc2 : (example_13_3_subgroup2 : Set _) = {example_13_3_sigma0, example_13_3_sigma2} := by
    rw [example_13_3_subgroup2, zpowers_involution_carrier h2_sq, h0_eq]
  have hc3 : (example_13_3_subgroup3 : Set _) = {example_13_3_sigma0, example_13_3_sigma3} := by
    rw [example_13_3_subgroup3, zpowers_involution_carrier h3_sq, h0_eq]
  refine ⟨hc1, hc2, hc3, fun H => ⟨?_, ?_⟩⟩
  · rintro ⟨hne_bot, hne_top⟩
    have hall_mem_or :
        example_13_3_sigma1 ∈ H ∨ example_13_3_sigma2 ∈ H ∨ example_13_3_sigma3 ∈ H := by
      by_contra hnone
      push Not at hnone
      apply hne_bot
      rw [eq_bot_iff]
      intro τ hτ
      have huniv : τ ∈ (Set.univ : Set _) := trivial
      rw [example_13_3_galoisGroup_univ] at huniv
      rcases huniv with rfl | rfl | rfl | rfl
      · rw [Subgroup.mem_bot, h0_eq]
      · exact (hnone.1 hτ).elim
      · exact (hnone.2.1 hτ).elim
      · exact (hnone.2.2 hτ).elim
    have hnot_two : ¬ (example_13_3_sigma1 ∈ H ∧ example_13_3_sigma2 ∈ H) ∧
        ¬ (example_13_3_sigma1 ∈ H ∧ example_13_3_sigma3 ∈ H) ∧
        ¬ (example_13_3_sigma2 ∈ H ∧ example_13_3_sigma3 ∈ H) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hm1, hm2⟩
        apply hne_top; rw [eq_top_iff]; intro τ _
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · rw [h0_eq]; exact H.one_mem
        · exact hm1
        · exact hm2
        · rw [← h12_mul]; exact H.mul_mem hm1 hm2
      · rintro ⟨hm1, hm3⟩
        apply hne_top; rw [eq_top_iff]; intro τ _
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · rw [h0_eq]; exact H.one_mem
        · exact hm1
        · rw [← h13_mul]; exact H.mul_mem hm1 hm3
        · exact hm3
      · rintro ⟨hm2, hm3⟩
        apply hne_top; rw [eq_top_iff]; intro τ _
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · rw [h0_eq]; exact H.one_mem
        · rw [← h23_mul]; exact H.mul_mem hm2 hm3
        · exact hm2
        · exact hm3
    rcases hall_mem_or with hm1 | hm2 | hm3
    · left
      apply SetLike.coe_injective; rw [hc1]; ext τ; constructor
      · intro hτ
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hnot_two.1 ⟨hm1, hτ⟩).elim
        · exact (hnot_two.2.1 ⟨hm1, hτ⟩).elim
      · rintro (rfl | rfl)
        · rw [h0_eq]; exact H.one_mem
        · exact hm1
    · right; left
      apply SetLike.coe_injective; rw [hc2]; ext τ; constructor
      · intro hτ
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hnot_two.1 ⟨hτ, hm2⟩).elim
        · exact Or.inr rfl
        · exact (hnot_two.2.2 ⟨hm2, hτ⟩).elim
      · rintro (rfl | rfl)
        · rw [h0_eq]; exact H.one_mem
        · exact hm2
    · right; right
      apply SetLike.coe_injective; rw [hc3]; ext τ; constructor
      · intro hτ
        have huniv : τ ∈ (Set.univ : Set _) := trivial
        rw [example_13_3_galoisGroup_univ] at huniv
        rcases huniv with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hnot_two.2.1 ⟨hτ, hm3⟩).elim
        · exact (hnot_two.2.2 ⟨hτ, hm3⟩).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · rw [h0_eq]; exact H.one_mem
        · exact hm3
  · rintro (rfl | rfl | rfl)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hm : example_13_3_sigma1 ∈ (⊥ : Subgroup _) := h ▸ Subgroup.mem_zpowers _
        exact h01 (h0_eq.trans (Subgroup.mem_bot.mp hm).symm)
      · have hm : example_13_3_sigma2 ∈ (example_13_3_subgroup1 : Set _) :=
          h.symm ▸ Subgroup.mem_top _
        rw [hc1] at hm
        rcases hm with hm | hm
        · exact h02 hm.symm
        · exact h12 hm.symm
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hm : example_13_3_sigma2 ∈ (⊥ : Subgroup _) := h ▸ Subgroup.mem_zpowers _
        exact h02 (h0_eq.trans (Subgroup.mem_bot.mp hm).symm)
      · have hm : example_13_3_sigma1 ∈ (example_13_3_subgroup2 : Set _) :=
          h.symm ▸ Subgroup.mem_top _
        rw [hc2] at hm
        rcases hm with hm | hm
        · exact h01 hm.symm
        · exact h12 hm
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have hm : example_13_3_sigma3 ∈ (⊥ : Subgroup _) := h ▸ Subgroup.mem_zpowers _
        exact h03 (h0_eq.trans (Subgroup.mem_bot.mp hm).symm)
      · have hm : example_13_3_sigma1 ∈ (example_13_3_subgroup3 : Set _) :=
          h.symm ▸ Subgroup.mem_top _
        rw [hc3] at hm
        rcases hm with hm | hm
        · exact h01 hm.symm
        · exact h13 hm

/-- Fixed fields of `{σ₀, σ₁}`, `{σ₀, σ₂}`, and `{σ₀, σ₃}` (§13.3, printed p. 109 / PDF p. 117):
the corresponding fixed fields are `ℚ(√3)`, `ℚ(√2)`, and `ℚ(√6)` (verified both inside
`ℚ(√2, √3)` and as intermediate fields of `ℝ / ℚ`). -/
theorem example_13_3_fixedFields :
    garlingFixedField {example_13_3_sigma0, example_13_3_sigma1} = ℚ⟮qSqrt3⟯ ∧
    garlingFixedField {example_13_3_sigma0, example_13_3_sigma2} = ℚ⟮qSqrt2⟯ ∧
    garlingFixedField {example_13_3_sigma0, example_13_3_sigma3} = ℚ⟮qSqrt6⟯ ∧
    (garlingFixedField {example_13_3_sigma0, example_13_3_sigma1}).map qSqrtTwoSqrtThree.val =
      ℚ⟮Real.sqrt 3⟯ ∧
    (garlingFixedField {example_13_3_sigma0, example_13_3_sigma2}).map qSqrtTwoSqrtThree.val =
      ℚ⟮Real.sqrt 2⟯ ∧
    (garlingFixedField {example_13_3_sigma0, example_13_3_sigma3}).map qSqrtTwoSqrtThree.val =
      ℚ⟮Real.sqrt 6⟯ := by
  let B := biquadraticBasis
  obtain ⟨h0_eq, _, _, h1_2, h1_3, h2_2, h2_3, h3_2, h3_3, h1_6, h2_6, h3_6⟩ :=
    example_13_3_action_table
  have hf1 : garlingFixedField {example_13_3_sigma0, example_13_3_sigma1} = ℚ⟮qSqrt3⟯ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx1 : example_13_3_sigma1 x = x := hx example_13_3_sigma1 (Or.inr rfl)
      let c := B.repr x
      have hx_eq : x = c 0 • (1 : qSqrtTwoSqrtThree) + c 1 • qSqrt2 +
          c 2 • qSqrt3 + c 3 • qSqrt6 :=
        biquadraticBasis_expand x
      have hσx : example_13_3_sigma1 x = c 0 • (1 : qSqrtTwoSqrtThree) + (-c 1) • qSqrt2 +
          c 2 • qSqrt3 + (-c 3) • qSqrt6 := by
        conv_lhs => rw [hx_eq]
        simp only [map_add, algEquiv_smul_rat, map_one, h1_2, h1_3, h1_6, smul_neg, neg_smul]
      have hdiff : (0 : ℚ) • B 0 + (2 * c 1) • B 1 + (0 : ℚ) • B 2 + (2 * c 3) • B 3 = 0 := by
        simp only [B, biquadraticBasis_zero, biquadraticBasis_one, biquadraticBasis_two,
          biquadraticBasis_three, zero_smul, zero_add, add_zero]
        have hsub : x - example_13_3_sigma1 x = 0 := sub_eq_zero.mpr hx1.symm
        rw [hσx, hx_eq] at hsub
        have h21 : (2 * c 1) • qSqrt2 = c 1 • qSqrt2 - (-c 1) • qSqrt2 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        have h23 : (2 * c 3) • qSqrt6 = c 3 • qSqrt6 - (-c 3) • qSqrt6 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        rw [h21, h23]
        abel_nf at hsub ⊢
        exact hsub
      let g : Fin 4 → ℚ := ![0, 2 * c 1, 0, 2 * c 3]
      have hsum : ∑ i : Fin 4, g i • B i = 0 := by
        rw [Fin.sum_univ_four]; simpa [g, add_assoc] using hdiff
      have hg0 := Fintype.linearIndependent_iff.mp B.linearIndependent g hsum
      have hc1 : c 1 = 0 := by have h := hg0 1; simp [g] at h; exact h
      have hc3 : c 3 = 0 := by have h := hg0 3; simp [g] at h; exact h
      rw [hx_eq, hc1, hc3, zero_smul, zero_smul, add_zero, add_zero, Algebra.smul_def, mul_one,
        Algebra.smul_def]
      exact add_mem (ℚ⟮qSqrt3⟯.algebraMap_mem _)
        (mul_mem (ℚ⟮qSqrt3⟯.algebraMap_mem _) (IntermediateField.mem_adjoin_simple_self ℚ qSqrt3))
    · rw [IntermediateField.adjoin_simple_le_iff]
      rintro σ (rfl | rfl)
      · rw [h0_eq]; rfl
      · exact h1_3
  have hf2 : garlingFixedField {example_13_3_sigma0, example_13_3_sigma2} = ℚ⟮qSqrt2⟯ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx2 : example_13_3_sigma2 x = x := hx example_13_3_sigma2 (Or.inr rfl)
      let c := B.repr x
      have hx_eq : x = c 0 • (1 : qSqrtTwoSqrtThree) + c 1 • qSqrt2 +
          c 2 • qSqrt3 + c 3 • qSqrt6 :=
        biquadraticBasis_expand x
      have hσx : example_13_3_sigma2 x = c 0 • (1 : qSqrtTwoSqrtThree) + c 1 • qSqrt2 +
          (-c 2) • qSqrt3 + (-c 3) • qSqrt6 := by
        conv_lhs => rw [hx_eq]
        simp only [map_add, algEquiv_smul_rat, map_one, h2_2, h2_3, h2_6, smul_neg, neg_smul]
      have hdiff : (0 : ℚ) • B 0 + (0 : ℚ) • B 1 + (2 * c 2) • B 2 + (2 * c 3) • B 3 = 0 := by
        simp only [B, biquadraticBasis_zero, biquadraticBasis_one, biquadraticBasis_two,
          biquadraticBasis_three, zero_smul, zero_add]
        have hsub : x - example_13_3_sigma2 x = 0 := sub_eq_zero.mpr hx2.symm
        rw [hσx, hx_eq] at hsub
        have h22 : (2 * c 2) • qSqrt3 = c 2 • qSqrt3 - (-c 2) • qSqrt3 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        have h23 : (2 * c 3) • qSqrt6 = c 3 • qSqrt6 - (-c 3) • qSqrt6 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        rw [h22, h23]
        abel_nf at hsub ⊢
        exact hsub
      let g : Fin 4 → ℚ := ![0, 0, 2 * c 2, 2 * c 3]
      have hsum : ∑ i : Fin 4, g i • B i = 0 := by
        rw [Fin.sum_univ_four]; simpa [g, add_assoc] using hdiff
      have hg0 := Fintype.linearIndependent_iff.mp B.linearIndependent g hsum
      have hc2 : c 2 = 0 := by have h := hg0 2; simp [g] at h; exact h
      have hc3 : c 3 = 0 := by have h := hg0 3; simp [g] at h; exact h
      rw [hx_eq, hc2, hc3, zero_smul, zero_smul, add_zero, add_zero, Algebra.smul_def, mul_one,
        Algebra.smul_def]
      exact add_mem (ℚ⟮qSqrt2⟯.algebraMap_mem _)
        (mul_mem (ℚ⟮qSqrt2⟯.algebraMap_mem _) (IntermediateField.mem_adjoin_simple_self ℚ qSqrt2))
    · rw [IntermediateField.adjoin_simple_le_iff]
      rintro σ (rfl | rfl)
      · rw [h0_eq]; rfl
      · exact h2_2
  have hf3 : garlingFixedField {example_13_3_sigma0, example_13_3_sigma3} = ℚ⟮qSqrt6⟯ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx3 : example_13_3_sigma3 x = x := hx example_13_3_sigma3 (Or.inr rfl)
      let c := B.repr x
      have hx_eq : x = c 0 • (1 : qSqrtTwoSqrtThree) + c 1 • qSqrt2 +
          c 2 • qSqrt3 + c 3 • qSqrt6 :=
        biquadraticBasis_expand x
      have hσx : example_13_3_sigma3 x = c 0 • (1 : qSqrtTwoSqrtThree) + (-c 1) • qSqrt2 +
          (-c 2) • qSqrt3 + c 3 • qSqrt6 := by
        conv_lhs => rw [hx_eq]
        simp only [map_add, algEquiv_smul_rat, map_one, h3_2, h3_3, h3_6, smul_neg, neg_smul]
      have hdiff : (0 : ℚ) • B 0 + (2 * c 1) • B 1 + (2 * c 2) • B 2 + (0 : ℚ) • B 3 = 0 := by
        simp only [B, biquadraticBasis_zero, biquadraticBasis_one, biquadraticBasis_two,
          biquadraticBasis_three, zero_smul, zero_add, add_zero]
        have hsub : x - example_13_3_sigma3 x = 0 := sub_eq_zero.mpr hx3.symm
        rw [hσx, hx_eq] at hsub
        have h21 : (2 * c 1) • qSqrt2 = c 1 • qSqrt2 - (-c 1) • qSqrt2 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        have h22 : (2 * c 2) • qSqrt3 = c 2 • qSqrt3 - (-c 2) • qSqrt3 := by
          rw [neg_smul, sub_neg_eq_add, ← add_smul]; ring_nf
        rw [h21, h22]
        abel_nf at hsub ⊢
        exact hsub
      let g : Fin 4 → ℚ := ![0, 2 * c 1, 2 * c 2, 0]
      have hsum : ∑ i : Fin 4, g i • B i = 0 := by
        rw [Fin.sum_univ_four]; simpa [g, add_assoc] using hdiff
      have hg0 := Fintype.linearIndependent_iff.mp B.linearIndependent g hsum
      have hc1 : c 1 = 0 := by have h := hg0 1; simp [g] at h; exact h
      have hc2 : c 2 = 0 := by have h := hg0 2; simp [g] at h; exact h
      rw [hx_eq, hc1, hc2, zero_smul, zero_smul, add_zero, add_zero, Algebra.smul_def, mul_one,
        Algebra.smul_def]
      exact add_mem (ℚ⟮qSqrt6⟯.algebraMap_mem _)
        (mul_mem (ℚ⟮qSqrt6⟯.algebraMap_mem _) (IntermediateField.mem_adjoin_simple_self ℚ qSqrt6))
    · rw [IntermediateField.adjoin_simple_le_iff]
      rintro σ (rfl | rfl)
      · rw [h0_eq]; rfl
      · exact h3_6
  have hmap_adjoin : ∀ z : qSqrtTwoSqrtThree,
      (ℚ⟮z⟯ : IntermediateField ℚ qSqrtTwoSqrtThree).map qSqrtTwoSqrtThree.val =
        ℚ⟮(z : ℝ)⟯ := fun z => by
    simpa using IntermediateField.adjoin_map ℚ {z} qSqrtTwoSqrtThree.val
  refine ⟨hf1, hf2, hf3, ?_, ?_, ?_⟩
  · rw [hf1, hmap_adjoin]; rfl
  · rw [hf2, hmap_adjoin]; rfl
  · rw [hf3, hmap_adjoin, qSqrt6_coe]

/-- Final assertion of §13.3 (*An example*, printed p. 109 / PDF p. 117): if `α` is any element of
`ℚ(√2, √3)` which does not belong to any of the three intermediate fields `ℚ(√3)`, `ℚ(√2)`, or
`ℚ(√6)`, then `ℚ(√2, √3) = ℚ(α)` (and conversely). -/
theorem example_13_3_primitive_element_iff (α : qSqrtTwoSqrtThree) :
    (ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ↔
      α ∉ ℚ⟮qSqrt3⟯ ∧ α ∉ ℚ⟮qSqrt2⟯ ∧ α ∉ ℚ⟮qSqrt6⟯ := by
  obtain ⟨hfd, hG⟩ :=
    (isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp example_13_3_isSplittingField_and_galois.2
  obtain ⟨hf1, hf2, hf3, _, _, _⟩ := example_13_3_fixedFields
  obtain ⟨hc1, hc2, hc3, hclass⟩ := example_13_3_nontrivial_subgroups
  constructor
  · intro htop
    refine ⟨fun hm3 => ?_, fun hm2 => ?_, fun hm6 => ?_⟩
    · have hsub_top : ℚ⟮qSqrt3⟯ = ⊤ :=
        top_unique (htop ▸ IntermediateField.adjoin_simple_le_iff.mpr hm3)
      have hfix_top :
          (example_13_3_subgroup1 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) ⊆ {1} := by
        intro σ hσ
        rw [hc1] at hσ
        have hfix : garlingFixedField {example_13_3_sigma0, example_13_3_sigma1} = ⊤ :=
          hf1.trans hsub_top
        exact Set.mem_singleton_iff.mpr (AlgEquiv.ext fun x => by
          have hx : x ∈ garlingFixedField {example_13_3_sigma0, example_13_3_sigma1} := by
            rw [hfix]; trivial
          exact hx σ hσ)
      have hbot : example_13_3_subgroup1 = ⊥ :=
        le_antisymm (fun σ hσ => Subgroup.mem_bot.mpr (hfix_top hσ)) bot_le
      exact ((hclass example_13_3_subgroup1).mpr (Or.inl rfl)).1 hbot
    · have hsub_top : ℚ⟮qSqrt2⟯ = ⊤ :=
        top_unique (htop ▸ IntermediateField.adjoin_simple_le_iff.mpr hm2)
      have hfix_top :
          (example_13_3_subgroup2 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) ⊆ {1} := by
        intro σ hσ
        rw [hc2] at hσ
        have hfix : garlingFixedField {example_13_3_sigma0, example_13_3_sigma2} = ⊤ :=
          hf2.trans hsub_top
        exact Set.mem_singleton_iff.mpr (AlgEquiv.ext fun x => by
          have hx : x ∈ garlingFixedField {example_13_3_sigma0, example_13_3_sigma2} := by
            rw [hfix]; trivial
          exact hx σ hσ)
      have hbot : example_13_3_subgroup2 = ⊥ :=
        le_antisymm (fun σ hσ => Subgroup.mem_bot.mpr (hfix_top hσ)) bot_le
      exact ((hclass example_13_3_subgroup2).mpr (Or.inr (Or.inl rfl))).1 hbot
    · have hsub_top : ℚ⟮qSqrt6⟯ = ⊤ :=
        top_unique (htop ▸ IntermediateField.adjoin_simple_le_iff.mpr hm6)
      have hfix_top :
          (example_13_3_subgroup3 : Set (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree)) ⊆ {1} := by
        intro σ hσ
        rw [hc3] at hσ
        have hfix : garlingFixedField {example_13_3_sigma0, example_13_3_sigma3} = ⊤ :=
          hf3.trans hsub_top
        exact Set.mem_singleton_iff.mpr (AlgEquiv.ext fun x => by
          have hx : x ∈ garlingFixedField {example_13_3_sigma0, example_13_3_sigma3} := by
            rw [hfix]; trivial
          exact hx σ hσ)
      have hbot : example_13_3_subgroup3 = ⊥ :=
        le_antisymm (fun σ hσ => Subgroup.mem_bot.mpr (hfix_top hσ)) bot_le
      exact ((hclass example_13_3_subgroup3).mpr (Or.inr (Or.inr rfl))).1 hbot
  · rintro ⟨hn3, hn2, hn6⟩
    have h0_eq : example_13_3_sigma0 = 1 := example_13_3_action_table.1
    have hbot : (ℚ⟮α⟯).fixingSubgroup = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      have hα_fix : α ∈ IntermediateField.fixedField (ℚ⟮α⟯).fixingSubgroup := by
        rw [IsGalois.fixedField_fixingSubgroup]
        exact IntermediateField.mem_adjoin_simple_self ℚ α
      have hτα : τ α = α := (IntermediateField.mem_fixedField_iff _ α).mp hα_fix τ hτ
      have huniv : τ ∈ (Set.univ : Set _) := trivial
      rw [example_13_3_galoisGroup_univ] at huniv
      rcases huniv with rfl | rfl | rfl | rfl
      · exact h0_eq
      · exfalso; apply hn3; rw [← hf1]
        rintro σ (rfl | rfl)
        · rw [h0_eq]; rfl
        · exact hτα
      · exfalso; apply hn2; rw [← hf2]
        rintro σ (rfl | rfl)
        · rw [h0_eq]; rfl
        · exact hτα
      · exfalso; apply hn6; rw [← hf3]
        rintro σ (rfl | rfl)
        · rw [h0_eq]; rfl
        · exact hτα
    rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮α⟯, hbot, IntermediateField.fixedField_bot]

/-- §13.3's own biquadratic example `ℚ(√2, √3) : ℚ` at `α = √2 + √3` refutes the printed `only if`
(`⇒`) direction of **Exercise 13.4** on the very same page (printed p. 109 / PDF p. 117):
`ℚ(√2, √3) = ℚ(√2 + √3)`, yet for every enumeration `σ : Fin 4 ≃ Γ(ℚ(√2, √3) : ℚ)`,
`∑ i, σ_i(√2 + √3) = 0`, so `(σ₁(α), …, σ₄(α))` is linearly dependent over `ℚ` and is neither an
indexed basis nor a subset basis for `ℚ(√2, √3)` over `ℚ`. -/
theorem exercise_13_4_only_if_counterexample_biquadratic :
    let α : qSqrtTwoSqrtThree := qSqrt2 + qSqrt3
    IsGarlingGaloisExtension ℚ qSqrtTwoSqrtThree ∧
    extDegree ℚ qSqrtTwoSqrtThree = 4 ∧
    (ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ∧
    Nonempty (Fin 4 ≃ GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) ∧
    ∀ σ : Fin 4 ≃ GarlingGaloisGroup ℚ qSqrtTwoSqrtThree,
      ∑ i : Fin 4, σ i α = 0 ∧
      ¬ LinearIndependent ℚ (fun i : Fin 4 => σ i α) ∧
      ¬ (∃ B : Module.Basis (Fin 4) ℚ qSqrtTwoSqrtThree, ∀ i : Fin 4, B i = σ i α) ∧
      ¬ IsBasis ℚ qSqrtTwoSqrtThree (Set.range (fun i : Fin 4 => σ i α)) ∧
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ↔
          ∃ B : Module.Basis (Fin 4) ℚ qSqrtTwoSqrtThree, ∀ i : Fin 4, B i = σ i α) ∧
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ↔
          IsBasis ℚ qSqrtTwoSqrtThree (Set.range (fun i : Fin 4 => σ i α))) := by
  dsimp only
  let α : qSqrtTwoSqrtThree := qSqrt2 + qSqrt3
  have hGal : IsGarlingGaloisExtension ℚ qSqrtTwoSqrtThree :=
    example_13_3_isSplittingField_and_galois.2
  have hdeg : extDegree ℚ qSqrtTwoSqrtThree = 4 := example_13_3_finrank_and_degree.2
  obtain ⟨hf1, hf2, hf3, _, _, _⟩ := example_13_3_fixedFields
  obtain ⟨_, h0_2, h0_3, h1_2, h1_3, h2_2, h2_3, h3_2, h3_3, _, _, _⟩ := example_13_3_action_table
  have h2_ne_neg : qSqrt2 ≠ -qSqrt2 := fun h =>
    qSqrt2_ne_zero (by
      have hval : (qSqrt2 : ℝ) = -(qSqrt2 : ℝ) := congrArg Subtype.val h
      ext; change (qSqrt2 : ℝ) = 0; linarith)
  have h3_ne_neg : qSqrt3 ≠ -qSqrt3 := fun h =>
    qSqrt3_ne_zero (by
      have hval : (qSqrt3 : ℝ) = -(qSqrt3 : ℝ) := congrArg Subtype.val h
      ext; change (qSqrt3 : ℝ) = 0; linarith)
  have hadj : (ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ := by
    rw [example_13_3_primitive_element_iff]
    refine ⟨fun hm3 => ?_, fun hm2 => ?_, fun hm6 => ?_⟩
    · rw [← hf1] at hm3
      have hfix := hm3 example_13_3_sigma1 (Or.inr rfl)
      simp only [α, map_add, h1_2, h1_3] at hfix
      exact h2_ne_neg (add_right_cancel hfix).symm
    · rw [← hf2] at hm2
      have hfix := hm2 example_13_3_sigma2 (Or.inr rfl)
      simp only [α, map_add, h2_2, h2_3] at hfix
      exact h3_ne_neg (add_left_cancel hfix).symm
    · rw [← hf3] at hm6
      have hfix := hm6 example_13_3_sigma3 (Or.inr rfl)
      simp only [α, map_add, h3_2, h3_3] at hfix
      have hval : -Real.sqrt 2 + -Real.sqrt 3 = Real.sqrt 2 + Real.sqrt 3 :=
        congrArg Subtype.val hfix
      linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2),
        Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
  obtain ⟨hfd, hG⟩ := (isGarlingGaloisExtension_iff ℚ qSqrtTwoSqrtThree).mp hGal
  have hcard4 : Fintype.card (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) = 4 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ qSqrtTwoSqrtThree,
      example_13_3_finrank_and_degree.1]
  have hnonempty : Nonempty (Fin 4 ≃ GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
    ⟨(Fintype.equivFinOfCardEq hcard4).symm⟩
  refine ⟨hGal, hdeg, hadj, hnonempty, fun σ => ?_⟩
  classical
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := example_13_3_sigmas_pairwise_ne
  let S : Finset (GarlingGaloisGroup ℚ qSqrtTwoSqrtThree) :=
    {example_13_3_sigma0, example_13_3_sigma1, example_13_3_sigma2, example_13_3_sigma3}
  have hS_univ : S = Finset.univ := by
    refine Finset.eq_univ_of_card S ?_
    rw [hcard4]
    simp [S, h01, h02, h03, h12, h13, h23]
  have hsum_univ : ∑ τ : GarlingGaloisGroup ℚ qSqrtTwoSqrtThree, τ α = 0 := by
    rw [← hS_univ]
    dsimp only [S]
    rw [Finset.sum_insert (by simp [h01, h02, h03]),
      Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
    simp only [α, map_add, h0_2, h0_3, h1_2, h1_3, h2_2, h2_3, h3_2, h3_3]
    abel
  have hsum0 : ∑ i : Fin 4, σ i α = 0 := by
    rw [Equiv.sum_comp σ (fun τ => τ α), hsum_univ]
  have hinj : Function.Injective (fun i : Fin 4 => σ i α) :=
    (exercise_13_4_iff_injective hGal σ α).mp hadj
  have hnot_li : ¬ LinearIndependent ℚ (fun i : Fin 4 => σ i α) := by
    intro hli
    have h := Fintype.linearIndependent_iff.mp hli (fun _ => (1 : ℚ))
      (by simpa using hsum0) 0
    exact one_ne_zero h
  have hnot_B : ¬ (∃ B : Module.Basis (Fin 4) ℚ qSqrtTwoSqrtThree, ∀ i : Fin 4, B i = σ i α) := by
    rintro ⟨B, hB⟩
    exact hnot_li (funext hB ▸ B.linearIndependent)
  have hnot_set : ¬ IsBasis ℚ qSqrtTwoSqrtThree (Set.range (fun i : Fin 4 => σ i α)) := by
    intro hBset
    apply hBset.1
    refine ⟨4, fun i => σ i α, fun _ => 1, hinj, fun i => ⟨i, rfl⟩, ⟨0, one_ne_zero⟩, ?_⟩
    simpa using hsum0
  have hnot_iff_B :
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ↔
          ∃ B : Module.Basis (Fin 4) ℚ qSqrtTwoSqrtThree, ∀ i : Fin 4, B i = σ i α) :=
    fun hiff => hnot_B (hiff.mp hadj)
  have hnot_iff_set :
      ¬ ((ℚ⟮α⟯ : IntermediateField ℚ qSqrtTwoSqrtThree) = ⊤ ↔
          IsBasis ℚ qSqrtTwoSqrtThree (Set.range (fun i : Fin 4 => σ i α))) :=
    fun hiff => hnot_set (hiff.mp hadj)
  exact ⟨hsum0, hnot_li, hnot_B, hnot_set, hnot_iff_B, hnot_iff_set⟩

end Garling.Chapter13
