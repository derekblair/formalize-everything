import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter06
import Garling.Chapter07
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Data.PNat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Chapter 8: The algebraic closure of a field

Formalization of Chapter 8 (*The algebraic closure of a field*, printed pp. 71–77 / PDF pp. 79–85)
of D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), following the
chapter's four sections and all 13 scope-of-record items in exact source order:

- **§8.1 Introduction** (printed pp. 71–72 / PDF pp. 79–80):
  prose definitions of *algebraically closed* field and *algebraic closure* of a field, bridges to
  Mathlib's `IsAlgClosed` and `IsAlgClosure`, `ℂ` is algebraically closed while `ℂ : ℚ` is not an
  algebraic closure (`Exercise 4.7`), `Theorem 8.1`, `Corollary` [to Theorem 8.1], and the subfield
  `A : ℚ` of algebraic numbers in `ℂ`.
- **§8.2 The existence of an algebraic closure** (printed pp. 72–75 / PDF pp. 80–83):
  `Theorem 8.2` (proved via Garling's explicit Artin polynomial-ring construction `K[X_U] / J`
  using Chapter 3's `Theorem 3.14` and `Theorem 3.16`, Chapter 7's `Theorem 7.3`, and Chapter 4's
  `Corollary 2` to `Theorem 4.6`), `Exercise 8.1`, `Exercise 8.2`, and `Exercise 8.3` (constructing
  an algebraic closure inside `P(K[x] × ℤ⁺)` via Zorn's lemma).
- **§8.3 The uniqueness of an algebraic closure** (printed pp. 75–76 / PDF pp. 83–84):
  `Theorem 8.3` (monomorphism extension via Zorn's lemma and `Theorem 7.4`), `Theorem 8.4`
  (uniqueness of algebraic closures up to `K`-isomorphism), prose notation `K̄ : K`, and
  `Exercises 8.4`–`8.8`.
- **§8.4 Conclusions** (printed p. 77 / PDF p. 85):
  prose commentary (`0` numbered theorems, `0` corollaries, `0` exercises; motivating remark on
  `ℂ : ℝ` as a splitting field for `x² + 1` recorded as a supporting declaration).
-/

namespace Garling.Chapter08

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06 Garling.Chapter07
open scoped BigOperators Polynomial

universe u v w

/-! ## §8.1 Introduction (printed pp. 71–72, PDF pp. 79–80) -/

/-- Garling's prose definition of an *algebraically closed* field (§8.1, printed p. 71 / PDF p. 79):
*"A field `L` is said to be algebraically closed if every `f` in `L[x]` splits over `L`."* -/
def IsGarlingAlgebraicallyClosed (L : Type*) [Field L] : Prop :=
  ∀ f : L[X], GarlingSplitsOver L L f

/-- Exact equivalence between Garling's `IsGarlingAlgebraicallyClosed L` and Mathlib's
`IsAlgClosed L` across all polynomials `f ∈ L[X]` (including `f = 0` and degree-`0` constants). -/
theorem isGarlingAlgebraicallyClosed_iff (L : Type*) [Field L] :
    IsGarlingAlgebraicallyClosed L ↔ IsAlgClosed L := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have hf := (garlingSplitsOver_iff_splits L L f).mp (h f)
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using hf
  · intro h f
    rw [garlingSplitsOver_iff_splits]
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using h.splits f

/-- Prose remark (§8.1, printed p. 71 / PDF p. 79): the 'fundamental theorem of algebra' states
that `ℂ` is algebraically closed. -/
theorem complex_isGarlingAlgebraicallyClosed : IsGarlingAlgebraicallyClosed ℂ :=
  (isGarlingAlgebraicallyClosed_iff ℂ).mpr inferInstance

/-- Garling's prose definition of an *algebraic closure* of a field `K` (§8.1, printed p. 71 /
PDF p. 79): *"An extension `L : K` is called an algebraic closure of `K` if `L : K` is algebraic
and `L` is algebraically closed."* -/
def IsGarlingAlgebraicClosure (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsAlgebraicExtension K L ∧ IsGarlingAlgebraicallyClosed L

/-- Exact equivalence between Garling's `IsGarlingAlgebraicClosure K L` and Mathlib's
`IsAlgClosure K L`. -/
theorem isGarlingAlgebraicClosure_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingAlgebraicClosure K L ↔ IsAlgClosure K L := by
  rw [IsGarlingAlgebraicClosure, isAlgebraicExtension_iff, isGarlingAlgebraicallyClosed_iff,
    isAlgClosure_iff, and_comm]

/-- Extension-triple formulation of an *algebraic closure* `(i, K, L)` (§4.2, p. 40; §8.1, p. 71;
§8.2, p. 74; §8.3, p. 76): `(i, K, L)` is an extension triple whose induced extension is algebraic
and `L` is algebraically closed. -/
def IsGarlingAlgebraicClosureTriple {K L : Type*} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : Prop :=
  letI : Algebra K L := ext.hom.toAlgebra
  IsGarlingAlgebraicClosure K L

/-- Ring-homomorphism shorthand for `(i, K, L)` being an algebraic closure of `K`. -/
def IsGarlingAlgebraicClosureHom {K L : Type*} [Field K] [Field L] (i : K →+* L) : Prop :=
  IsGarlingAlgebraicClosureTriple (FieldExtensionTriple.ofRingHom i)

/-- Prose remark (§8.1, printed p. 71 / PDF p. 79): `ℂ : ℚ` is *not* an algebraic closure of `ℚ`
since `ℂ : ℚ` is not algebraic (citing `Exercise 4.7`). -/
theorem complex_not_isGarlingAlgebraicClosure_rat :
    ¬ IsAlgebraicExtension ℚ ℂ ∧ ¬ IsGarlingAlgebraicClosure ℚ ℂ := by
  have hnot_alg : ¬ IsAlgebraicExtension ℚ ℂ := by
    intro halg
    obtain ⟨x, hx⟩ := exercise_4_7_exists_transcendental_real.1
    exact ((isGarlingTranscendental_rat_ofReal_iff x).mpr hx) (halg (x : ℂ))
  exact ⟨hnot_alg, fun h => hnot_alg h.1⟩

/-- Equivalence of the two standard Lean formulations of *"L = L'"* for an extension `L' : L`:
`(⊥ : IntermediateField L L') = ⊤` holds if and only if `algebraMap L L'` is surjective. -/
theorem bot_eq_top_iff_surjective_algebraMap (L L' : Type*) [Field L] [Field L'] [Algebra L L'] :
    (⊥ : IntermediateField L L') = ⊤ ↔ Function.Surjective (algebraMap L L') := by
  constructor
  · intro h y
    have hy : y ∈ (⊥ : IntermediateField L L') := h ▸ IntermediateField.mem_top
    exact IntermediateField.mem_bot.mp hy
  · intro hsurj
    ext y
    simp only [IntermediateField.mem_top, iff_true, IntermediateField.mem_bot]
    exact hsurj y

/-- Core implication `(ii) ⟹ (iii)` of **Theorem 8.1** across *arbitrary* extension universes
`{L' : Type w}`, proved directly following Garling's minimal-polynomial argument on printed p. 71
via `Theorem 4.7`. -/
theorem theorem_8_1_ii_imp_iii_univ {K : Type u} {L : Type v} {L' : Type w}
    [Field K] [Field L] [Algebra K L] [Field L'] [Algebra L L']
    (halgKL : IsAlgebraicExtension K L)
    (hsplitK : ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f)
    (halgLL' : IsAlgebraicExtension L L') :
    Function.Surjective (algebraMap L L') ∧ (⊥ : IntermediateField L L') = ⊤ := by
  let _ : Algebra K L' := ((algebraMap L L').comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgKL' : IsAlgebraicExtension K L' := theorem_4_7 halgLL' halgKL
  have hsurj : Function.Surjective (algebraMap L L') := by
    intro α'
    have hα'_int : IsIntegral K α' := (isGarlingAlgebraic_iff_isIntegral K α').mp (halgKL' α')
    let m : K[X] := minpoly K α'
    have hm_irr : Irreducible m := minpoly.irreducible hα'_int
    obtain ⟨n, c, lam, hexp⟩ := hsplitK m hm_irr
    obtain ⟨hc_eq, _, _, _⟩ := garlingSplitsExplicit_props hm_irr.ne_zero hexp
    have hm_monic : m.Monic := minpoly.monic hα'_int
    have hc1 : c = 1 := hc_eq.trans hm_monic.leadingCoeff
    have hmap_L' :
        (m.map (algebraMap K L)).map (algebraMap L L') = m.map (algebraMap K L') := by
      rw [Polynomial.map_map]
      rfl
    have hfac_L' :
        m.map (algebraMap K L') =
          ∏ j : Fin n, (Polynomial.X - Polynomial.C (algebraMap L L' (lam j))) := by
      rw [← hmap_L', hexp, hc1]
      simp [Polynomial.map_prod]
    have hev0 : (m.map (algebraMap K L')).eval α' = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval K α'
    rw [hfac_L', Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev0
    obtain ⟨j, _, hj⟩ := hev0
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    exact ⟨lam j, hj.symm⟩
  exact ⟨hsurj, (bot_eq_top_iff_surjective_algebraMap L L').mpr hsurj⟩

/-- **Theorem 8.1** (§8.1, printed p. 71 / PDF p. 79; proof pp. 71–72 / PDF pp. 79–80):
*"Suppose that `L : K` is an extension. The following are equivalent:
(i) `L : K` is an algebraic closure of `K`.
(ii) `L : K` is algebraic, and every irreducible `f` in `K[x]` splits over `L`.
(iii) `L : K` is algebraic, and if `L' : L` is algebraic then `L = L'`."*

Proved step-by-step following Garling's `(i) ⟹ (ii) ⟹ (iii) ⟹ (i)` argument via `Theorem 4.7`,
`Theorem 7.3`, and `Corollary` [to `Theorem 7.1`]. -/
theorem theorem_8_1 (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    (IsGarlingAlgebraicClosure K L ↔
      (IsAlgebraicExtension K L ∧ ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f)) ∧
    ((IsAlgebraicExtension K L ∧ ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f) ↔
      (IsAlgebraicExtension K L ∧
        ∀ (L' : Type v) [Field L'] [Algebra L L'],
          IsAlgebraicExtension L L' → (⊥ : IntermediateField L L') = ⊤)) ∧
    (IsGarlingAlgebraicClosure K L ↔
      (IsAlgebraicExtension K L ∧
        ∀ (L' : Type v) [Field L'] [Algebra L L'],
          IsAlgebraicExtension L L' → (⊥ : IntermediateField L L') = ⊤)) := by
  have h12 :
      IsGarlingAlgebraicClosure K L →
        IsAlgebraicExtension K L ∧ ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f := by
    rintro ⟨halg, hclosed⟩
    refine ⟨halg, fun f _ => ?_⟩
    rw [garlingSplitsOver_iff_splits]
    have hf := (garlingSplitsOver_iff_splits L L (f.map (algebraMap K L))).mp
      (hclosed (f.map (algebraMap K L)))
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using hf
  have h23 :
      (IsAlgebraicExtension K L ∧ ∀ f : K[X], Irreducible f → GarlingSplitsOver K L f) →
        IsAlgebraicExtension K L ∧
          ∀ (L' : Type v) [Field L'] [Algebra L L'],
            IsAlgebraicExtension L L' → (⊥ : IntermediateField L L') = ⊤ := by
    rintro ⟨halg, hsplit⟩
    exact ⟨halg, fun L' _ _ halg' => (theorem_8_1_ii_imp_iii_univ halg hsplit halg').2⟩
  have h31 :
      (IsAlgebraicExtension K L ∧
        ∀ (L' : Type v) [Field L'] [Algebra L L'],
          IsAlgebraicExtension L L' → (⊥ : IntermediateField L L') = ⊤) →
        IsGarlingAlgebraicClosure K L := by
    rintro ⟨halg, hmax⟩
    refine ⟨halg, fun f => ?_⟩
    -- By Theorem 7.3 (`theorem_7_3_natDegree`), `f ∈ L[X]` has a splitting field `L' : L`.
    obtain ⟨L', instFieldL', instAlgLL', hsf, _⟩ := theorem_7_3_natDegree f
    let _ : Field L' := instFieldL'
    let _ : Algebra L L' := instAlgLL'
    -- By the Corollary to Theorem 7.1, `L' : L` is algebraic, so `L' = L` by (iii).
    have halgLL' : IsAlgebraicExtension L L' := (corollary_to_theorem_7_1 hsf).2
    have hsurj : Function.Surjective (algebraMap L L') :=
      (bot_eq_top_iff_surjective_algebraMap L L').mp (hmax L' halgLL')
    obtain ⟨n, c, α', hexp'⟩ := hsf.1
    choose α hα using fun j : Fin n => hsurj (α' j)
    refine ⟨n, c, α, ?_⟩
    unfold GarlingSplitsExplicit at hexp' ⊢
    apply Polynomial.map_injective (algebraMap L L') (algebraMap L L').injective
    simp only [Algebra.algebraMap_self, Polynomial.map_id, RingHom.id_apply]
    rw [hexp']
    simp [Polynomial.map_mul, Polynomial.map_prod, hα]
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h => h12 (h31 h)⟩, ⟨fun h => h23 (h12 h), h31⟩⟩

/-- **Theorem 8.1 (`IsGarlingIrreducible` & `Function.Surjective` formulation)** (§8.1, p. 71):
Equivalent phrasing using Chapter 3's `IsGarlingIrreducible` in `(ii)` and
`Function.Surjective (algebraMap L L')` in `(iii)`. -/
theorem theorem_8_1_garling (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    (IsGarlingAlgebraicClosure K L ↔
      (IsAlgebraicExtension K L ∧
        ∀ f : K[X], IsGarlingIrreducible f → GarlingSplitsOver K L f)) ∧
    (IsGarlingAlgebraicClosure K L ↔
      (IsAlgebraicExtension K L ∧
        ∀ (L' : Type v) [Field L'] [Algebra L L'],
          IsAlgebraicExtension L L' → Function.Surjective (algebraMap L L'))) := by
  have h := theorem_8_1 K L
  refine ⟨h.1.trans (and_congr_right fun _ => ?_), h.2.2.trans (and_congr_right fun _ => ?_)⟩
  · constructor
    · intro h1 f hfg
      exact h1 f ((isGarlingIrreducible_iff f).mp hfg)
    · intro h1 f hf
      exact h1 f ((isGarlingIrreducible_iff f).mpr hf)
  · refine forall_congr' fun L' => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    exact bot_eq_top_iff_surjective_algebraMap L L'

/-- Universe-polymorphic consequence of **Theorem 8.1 `(i) ⟹ (iii)`**: if `L` is algebraically
closed (in particular if `L : K` is an algebraic closure of `K`), then *every* algebraic extension
`L' : L` in *any* universe `w` satisfies `Function.Surjective (algebraMap L L')` and
`(⊥ : IntermediateField L L') = ⊤`. -/
theorem isGarlingAlgebraicallyClosed_surjective_of_algebraic {L : Type v} {L' : Type w}
    [Field L] [Field L'] [Algebra L L']
    (hL : IsGarlingAlgebraicallyClosed L) (halg : IsAlgebraicExtension L L') :
    Function.Surjective (algebraMap L L') ∧ (⊥ : IntermediateField L L') = ⊤ := by
  have halgLL : IsAlgebraicExtension L L := fun x =>
    ⟨Polynomial.X - Polynomial.C x, Polynomial.X_sub_C_ne_zero x, by simp⟩
  exact theorem_8_1_ii_imp_iii_univ halgLL (fun f _ => hL f) halg

/-- Ambient-subfield formulation of **Theorem 8.1** (§8.1, p. 71): for subfields `K ≤ L` inside an
algebraically closed ambient field `Ω`, `L` is an algebraic closure of `K` if and only if `L : K`
is algebraic and for every subfield `L'` of `Ω` with `L ≤ L'`, if `L' : L` is algebraic then
literally `L = L'`. -/
theorem theorem_8_1_subfields {Ω : Type u} [Field Ω] (hΩ : IsGarlingAlgebraicallyClosed Ω)
    {K L : Subfield Ω} (hKL : K ≤ L) :
    letI : Algebra K L := (Subfield.inclusion hKL).toAlgebra
    IsGarlingAlgebraicClosure K L ↔
      (IsAlgebraicExtension K L ∧
        ∀ (L' : Subfield Ω) (hLL' : L ≤ L'),
          letI : Algebra L L' := (Subfield.inclusion hLL').toAlgebra
          IsAlgebraicExtension L L' → L = L') := by
  let _ : Algebra K L := (Subfield.inclusion hKL).toAlgebra
  constructor
  · rintro ⟨halgKL, hclosedL⟩
    refine ⟨halgKL, fun L' hLL' halgLL' => ?_⟩
    let _ : Algebra L L' := (Subfield.inclusion hLL').toAlgebra
    have hsurj := (isGarlingAlgebraicallyClosed_surjective_of_algebraic hclosedL halgLL').1
    apply le_antisymm hLL'
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hyval : (y : Ω) = x := congrArg Subtype.val hy
    exact hyval ▸ y.2
  · rintro ⟨halgKL, hmax⟩
    have _ : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine (theorem_8_1 K L).1.mpr ⟨halgKL, fun f hirr => ?_⟩
    have hfΩ : GarlingSplitsOver K Ω f := by
      rw [garlingSplitsOver_iff_splits]
      have h1 := (garlingSplitsOver_iff_splits Ω Ω (f.map (algebraMap K Ω))).mp
        (hΩ (f.map (algebraMap K Ω)))
      simpa [Algebra.algebraMap_self, Polynomial.map_id] using h1
    obtain ⟨n, c, α, hexp⟩ := hfΩ
    have halg_α : ∀ j : Fin n, IsGarlingAlgebraic L (α j) := by
      intro j
      have hroot : α j ∈ f.rootSet Ω :=
        (garlingSplitsExplicit_props hirr.ne_zero hexp).2.2.2 ▸ ⟨j, rfl⟩
      rw [Polynomial.mem_rootSet] at hroot
      refine ⟨f.map (algebraMap K L),
        (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hirr.ne_zero, ?_⟩
      rw [Polynomial.aeval_map_algebraMap]
      exact hroot.2
    let E : IntermediateField L Ω := IntermediateField.adjoin L (Set.range α)
    have halg_E : IsAlgebraicExtension L E :=
      corollary_2_to_theorem_4_6 (by rintro _ ⟨j, rfl⟩; exact halg_α j)
    let L' : Subfield Ω := E.toSubfield
    have hLL' : L ≤ L' := by
      intro x hx
      exact E.algebraMap_mem ⟨x, hx⟩
    let _ : Algebra L L' := (Subfield.inclusion hLL').toAlgebra
    have hLL'_eq : L = L' := hmax L' hLL' halg_E
    have hαL : ∀ j : Fin n, α j ∈ L := by
      intro j
      rw [hLL'_eq]
      exact IntermediateField.subset_adjoin L (Set.range α) ⟨j, rfl⟩
    refine ⟨n, c, fun j => ⟨α j, hαL j⟩, ?_⟩
    unfold GarlingSplitsExplicit at hexp ⊢
    apply Polynomial.map_injective (algebraMap L Ω) (algebraMap L Ω).injective
    have hmap : (f.map (algebraMap K L)).map (algebraMap L Ω) = f.map (algebraMap K Ω) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, hexp]
    simp [Polynomial.map_mul, Polynomial.map_prod]
    rfl

/-- **Corollary [to Theorem 8.1]** (§8.1, printed p. 72 / PDF p. 80):
*"Suppose that `L : K` is an extension and that `L` is algebraically closed. Let `L_a` be the field
of elements of `L` which are algebraic over `K`. Then `L_a : K` is an algebraic closure of `K`."* -/
theorem corollary_to_theorem_8_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hL : IsGarlingAlgebraicallyClosed L) :
    IsGarlingAlgebraicClosure K (algebraicIntermediateField K L) := by
  let La := algebraicIntermediateField K L
  have halg : IsAlgebraicExtension K La := by
    intro x
    have hx : IsAlgebraic K (x : L) := x.2
    exact (isAlgebraic_algebraMap_iff (R := K) La.val.injective).mp hx
  refine (theorem_8_1 K La).1.mpr ⟨halg, fun f hirr => ?_⟩
  have hfL : GarlingSplitsOver K L f := by
    rw [garlingSplitsOver_iff_splits]
    have h1 := (garlingSplitsOver_iff_splits L L (f.map (algebraMap K L))).mp
      (hL (f.map (algebraMap K L)))
    simpa [Algebra.algebraMap_self, Polynomial.map_id] using h1
  obtain ⟨n, c, α, hexp⟩ := hfL
  have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hirr.ne_zero hexp).2.2.2
  have hαLa : ∀ j : Fin n, α j ∈ La := by
    intro j
    have hj : α j ∈ f.rootSet L := hroots ▸ ⟨j, rfl⟩
    rw [Polynomial.mem_rootSet] at hj
    exact ⟨f, hj.1, hj.2⟩
  exact (garlingSplitsOver_intermediateField_iff La f).mpr ⟨n, c, α, hαLa, hexp⟩

/-- Prose specialization after **Corollary [to Theorem 8.1]** (§8.1, printed p. 72 / PDF p. 80):
if `A` (`GarlingAlgebraicNumbers = algebraicSubfield ℚ ℂ`) is the field of complex numbers which
are algebraic over `ℚ`, then `A : ℚ` is an algebraic closure for `ℚ`. -/
theorem garlingAlgebraicNumbers_isGarlingAlgebraicClosure :
    IsGarlingAlgebraicClosure ℚ GarlingAlgebraicNumbers ∧
    IsGarlingAlgebraicClosure ℚ (algebraicIntermediateField ℚ ℂ) := by
  have hcor := corollary_to_theorem_8_1 (K := ℚ) complex_isGarlingAlgebraicallyClosed
  -- Note `GarlingAlgebraicNumbers` and `algebraicIntermediateField ℚ ℂ` share the exact same
  -- underlying field and `ℚ`-algebra structure.
  refine ⟨⟨garlingAlgebraicNumbers_isAlgebraicExtension, ?_⟩, hcor⟩
  exact hcor.2

/-! ## §8.2 The existence of an algebraic closure (printed pp. 72–75, PDF pp. 80–83) -/

/-- Garling's index set `U` in the proof of **Theorem 8.2** (§8.2, printed p. 73 / PDF p. 81):
all pairs `(f, j)` where `f` is a non-constant monic polynomial in `K[x]` and `1 ≤ j ≤ degree f`. -/
abbrev ArtinIndex (K : Type u) [Field K] : Type u :=
  {p : K[X] × ℕ // p.1.Monic ∧ 0 < p.1.natDegree ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1.natDegree}

/-- The multivariate polynomial ring `K[X_U]` with indeterminates `x_j(f)` indexed by
`(f, j) ∈ U` (§8.2, printed p. 73 / PDF p. 81). -/
abbrev ArtinPolyRing (K : Type u) [Field K] : Type u :=
  MvPolynomial (ArtinIndex K) K

/-- Indeterminate `x_{j+1}(f) ∈ K[X_U]` corresponding to the `j`-th formal root of a non-constant
monic polynomial `f ∈ K[x]` (§8.2, printed p. 73 / PDF p. 81). -/
noncomputable def artinVar {K : Type u} [Field K] {f : K[X]}
    (hmon : f.Monic) (hpos : 0 < f.natDegree) (j : Fin f.natDegree) : ArtinPolyRing K :=
  MvPolynomial.X ⟨(f, j.1 + 1), hmon, hpos, by dsimp; omega, by dsimp; omega⟩

/-- Formal monic split polynomial `g(f) = ∏_{j=1}^n (x - x_j(f)) ∈ K[X_U][x]` (§8.2, printed p. 73 /
PDF p. 81). -/
noncomputable def artinG {K : Type u} [Field K] {f : K[X]}
    (hmon : f.Monic) (hpos : 0 < f.natDegree) : (ArtinPolyRing K)[X] :=
  ∏ j : Fin f.natDegree, (Polynomial.X - Polynomial.C (artinVar hmon hpos j))

/-- The `j`-th elementary symmetric polynomial `s_j(f) = ∑_{i₁ < ⋯ < i_j} x_{i₁}(f) ⋯ x_{i_j}(f)`
in `x₁(f), …, x_n(f)` inside `K[X_U]` (§8.2, printed p. 73 / PDF p. 81). -/
noncomputable def artinS {K : Type u} [Field K] {f : K[X]}
    (hmon : f.Monic) (hpos : 0 < f.natDegree) (j : ℕ) : ArtinPolyRing K :=
  ∑ s ∈ (Finset.univ : Finset (Fin f.natDegree)).powersetCard j,
    ∏ r ∈ s, artinVar hmon hpos r

/-- Signed coefficient `a_i(f) = (-1)^i f_{n - i}` from Garling's alternating expansion
`f = x^n - a₁(f) x^{n-1} + ⋯ + (-1)^n a_n(f)` (§8.2, printed p. 73 / PDF p. 81). -/
noncomputable def artinA {K : Type u} [Field K] (f : K[X]) (i : ℕ) : K :=
  (-1 : K) ^ i * f.coeff (f.natDegree - i)

/-- Relation generator `t_i(f) = s_i(f) - a_i(f) ∈ K[X_U]` identifying the coefficients of `f` and
`g(f)` for `1 ≤ i ≤ degree f` (§8.2, printed p. 73 / PDF p. 81). -/
noncomputable def artinT {K : Type u} [Field K] {f : K[X]}
    (hmon : f.Monic) (hpos : 0 < f.natDegree) (i : ℕ) : ArtinPolyRing K :=
  artinS hmon hpos i - MvPolynomial.C (artinA f i)

/-- Vieta expansion of `g(f)` (§8.2, printed p. 73 / PDF p. 81 — including the displayed equation
line `= x^n - s_1(f)x^{n-1} + ⋯ + (-1)^n s_n(f)` omitted by `garling1986_pages.txt` OCR):
for `0 ≤ i ≤ degree f`, the degree-`(n - i)` coefficient of `g(f)` is `(-1)^i s_i(f)`, so
`t_i(f) = (-1)^i * ((g(f)).coeff (n - i) - C (f.coeff (n - i)))`. -/
theorem artinG_coeff_and_artinT {K : Type u} [Field K] {f : K[X]}
    (hmon : f.Monic) (hpos : 0 < f.natDegree) {i : ℕ} (hi : i ≤ f.natDegree) :
    (artinG hmon hpos).coeff (f.natDegree - i) = (-1) ^ i * artinS hmon hpos i ∧
    artinT hmon hpos i =
      (-1) ^ i *
        ((artinG hmon hpos).coeff (f.natDegree - i) - MvPolynomial.C (f.coeff (f.natDegree - i))) := by
  let s : Multiset (ArtinPolyRing K) :=
    (Finset.univ : Finset (Fin f.natDegree)).val.map (artinVar hmon hpos)
  have hcard : Multiset.card s = f.natDegree := by
    simp [s]
  have hk_le : f.natDegree - i ≤ Multiset.card s := by
    rw [hcard]
    omega
  have hprod : (s.map fun t => Polynomial.X - Polynomial.C t).prod = artinG hmon hpos := by
    dsimp [s, artinG]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have hesymm : s.esymm i = artinS hmon hpos i := by
    dsimp [s, artinS, Multiset.esymm, Finset.powersetCard]
    rw [Multiset.powersetCard_map, Multiset.map_pmap, Multiset.map_map]
    simp only [Function.comp_def, Finset.prod_mk]
    rw [Multiset.pmap_eq_map]
  have hsub_sub : Multiset.card s - (f.natDegree - i) = i := by
    rw [hcard]
    omega
  have hcoeff : (artinG hmon hpos).coeff (f.natDegree - i) = (-1) ^ i * artinS hmon hpos i := by
    rw [← hprod, Multiset.prod_X_sub_C_coeff s hk_le, hsub_sub, hesymm]
  refine ⟨hcoeff, ?_⟩
  have hsign : ((-1 : ArtinPolyRing K) ^ i) * ((-1 : ArtinPolyRing K) ^ i) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  unfold artinT artinA
  rw [hcoeff, map_mul, map_pow, map_neg, map_one]
  linear_combination -hsign * artinS hmon hpos i

/-- Generating set `{t_i(f) : f monic non-constant, 1 ≤ i ≤ degree f}` in `K[X_U]` (§8.2, p. 73). -/
def artinGenSet (K : Type u) [Field K] : Set (ArtinPolyRing K) :=
  {t | ∃ (f : K[X]) (hmon : f.Monic) (hpos : 0 < f.natDegree) (i : ℕ),
    1 ≤ i ∧ i ≤ f.natDegree ∧ t = artinT hmon hpos i}

/-- The ideal `I ⊆ K[X_U]` generated by all `t_i(f)` (§8.2, printed p. 73 / PDF p. 81). -/
noncomputable def artinIdeal (K : Type u) [Field K] : Ideal (ArtinPolyRing K) :=
  Ideal.span (artinGenSet K)

/-- Main step in the proof of **Theorem 8.2** (§8.2, printed pp. 73–74 / PDF pp. 81–82):
`I` is a proper ideal of `K[X_U]` (`1 ∉ I`), proved by taking a splitting field `L : K` for
`h = f₁ ⋯ f_N` via `Theorem 7.3` and evaluating `K[X_U] → L`. -/
theorem artinIdeal_proper (K : Type u) [Field K] : artinIdeal K ≠ ⊤ := by
  classical
  intro htop
  have h1 : (1 : ArtinPolyRing K) ∈ Ideal.span (artinGenSet K) := by
    change (1 : ArtinPolyRing K) ∈ artinIdeal K
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨coeffFn, T, hT_sub, _, h1_sum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp h1
  have hgen : ∀ t : T, ∃ (f : K[X]) (hmon : f.Monic) (hpos : 0 < f.natDegree) (i : ℕ),
      1 ≤ i ∧ i ≤ f.natDegree ∧ t.1 = artinT hmon hpos i :=
    fun t => hT_sub t.2
  choose fOf hmonOf hposOf iOf hi1Of hinOf htEq using hgen
  let F : Finset K[X] := T.attach.image fOf
  have hF_props : ∀ p ∈ F, p.Monic ∧ 0 < p.natDegree := by
    intro p hp
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hmonOf t, hposOf t⟩
  let h : K[X] := ∏ p ∈ F, p
  have hh_monic : h.Monic := Polynomial.monic_prod_of_monic F id fun p hp => (hF_props p hp).1
  -- By Theorem 7.3 (`theorem_7_3`), construct a splitting field `L : K` for `h = ∏_{p ∈ F} p`.
  obtain ⟨L, instFieldL, instAlgKL, hsf_h, _⟩ := theorem_7_3 hh_monic.ne_zero rfl
  let _ : Field L := instFieldL
  let _ : Algebra K L := instAlgKL
  have hh_splits : (h.map (algebraMap K L)).Splits :=
    (garlingSplitsOver_iff_splits K L h).mp hsf_h.1
  have hhL_ne0 : h.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hh_monic.ne_zero
  have hp_splits : ∀ p : F,
      ∃ α : Fin p.1.natDegree → L,
        p.1.map (algebraMap K L) = ∏ j : Fin p.1.natDegree, (Polynomial.X - Polynomial.C (α j)) := by
    intro p
    have hdvd : p.1 ∣ h := Finset.dvd_prod_of_mem id p.2
    have hspL : (p.1.map (algebraMap K L)).Splits :=
      Polynomial.Splits.of_dvd hh_splits hhL_ne0 (Polynomial.map_dvd (algebraMap K L) hdvd)
    obtain ⟨n, c, α, hexp⟩ := (garlingSplitsOver_iff_splits K L p.1).mpr hspL
    have hp_monic : p.1.Monic := (hF_props p.1 p.2).1
    obtain ⟨hc_eq, _, hn_eq, _⟩ := garlingSplitsExplicit_props hp_monic.ne_zero hexp
    have hc1 : c = 1 := hc_eq.trans hp_monic.leadingCoeff
    have hn_deg : n = p.1.natDegree := by simpa [garlingDegree] using hn_eq
    subst hn_deg
    refine ⟨α, ?_⟩
    unfold GarlingSplitsExplicit at hexp
    simpa [hc1] using hexp
  choose αOf hαOf using hp_splits
  -- Garling's evaluation map `E : K[X_U] →+* L` sending `x_i(f_k) ↦ α_i(k)` and other vars to `0`.
  let evalVar : ArtinIndex K → L := fun u =>
    if hu : u.1.1 ∈ F then
      αOf ⟨u.1.1, hu⟩ ⟨u.1.2 - 1, by dsimp; have := u.2.2.2.1; have := u.2.2.2.2; omega⟩
    else 0
  let E : ArtinPolyRing K →+* L := MvPolynomial.eval₂Hom (algebraMap K L) evalVar
  have hE_var : ∀ (p : K[X]) (hmon : p.Monic) (hpos : 0 < p.natDegree) (hpF : p ∈ F)
      (j : Fin p.natDegree),
      E (artinVar hmon hpos j) = αOf ⟨p, hpF⟩ j := by
    intro p hmon hpos hpF j
    unfold artinVar
    change MvPolynomial.eval₂Hom (algebraMap K L) evalVar (MvPolynomial.X _) = _
    rw [MvPolynomial.eval₂Hom_X']
    dsimp [evalVar]
    simp [hpF]
  have hE_zero_on_T : ∀ x ∈ T, E x = 0 := by
    intro x hxT
    let t : T := ⟨x, hxT⟩
    let p : K[X] := fOf t
    have hpF : p ∈ F := Finset.mem_image_of_mem fOf (Finset.mem_attach T t)
    have hmapG :
        (artinG (hmonOf t) (hposOf t)).map E = p.map (algebraMap K L) := by
      dsimp [artinG]
      rw [Polynomial.map_prod, hαOf ⟨p, hpF⟩]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [hE_var p (hmonOf t) (hposOf t) hpF j]
    have hcoeff_eq :
        E ((artinG (hmonOf t) (hposOf t)).coeff (p.natDegree - iOf t)) =
          algebraMap K L (p.coeff (p.natDegree - iOf t)) := by
      have h1 := congrArg (fun q : L[X] => q.coeff (p.natDegree - iOf t)) hmapG
      simpa [Polynomial.coeff_map] using h1
    have ht_formula := (artinG_coeff_and_artinT (hmonOf t) (hposOf t) (hinOf t)).2
    change E t.1 = 0
    rw [htEq t, ht_formula, map_mul, map_sub, hcoeff_eq]
    have hEC : E (MvPolynomial.C (p.coeff (p.natDegree - iOf t))) =
        algebraMap K L (p.coeff (p.natDegree - iOf t)) := by
      dsimp [E]
      exact MvPolynomial.eval₂Hom_C _ _ _
    rw [hEC, sub_self, mul_zero]
  -- `1 = E(1) = E(r₁) E(t_{i₁}(f₁)) + ⋯ + E(r_N) E(t_{i_N}(f_N)) = 0` (printed p. 74).
  have h1_zero : (1 : L) = 0 := by
    calc (1 : L) = E 1 := (map_one E).symm
      _ = E (∑ a ∈ T, coeffFn a • a) := by rw [h1_sum]
      _ = ∑ a ∈ T, E (coeffFn a) * E a := by simp [smul_eq_mul, map_sum, map_mul]
      _ = 0 := Finset.sum_eq_zero fun a ha => by rw [hE_zero_on_T a ha, mul_zero]
  exact one_ne_zero h1_zero

/-- Maximal proper ideal `J ⊇ I` in `K[X_U]`, chosen via **Theorem 3.14** (§3.8, p. 34; §8.2,
printed p. 74 / PDF p. 82). -/
noncomputable def artinMaxIdeal (K : Type u) [Field K] : Ideal (ArtinPolyRing K) :=
  (theorem_3_14 (artinIdeal_proper K)).choose

theorem artinMaxIdeal_spec (K : Type u) [Field K] :
    artinIdeal K ≤ artinMaxIdeal K ∧
    IsGarlingMaximalProperIdeal (artinMaxIdeal K) ∧
    (artinMaxIdeal K).IsMaximal :=
  (theorem_3_14 (artinIdeal_proper K)).choose_spec

instance artinMaxIdeal_isMaximal (K : Type u) [Field K] : (artinMaxIdeal K).IsMaximal :=
  (artinMaxIdeal_spec K).2.2

/-- Garling's explicit quotient field `M = K[X_U] / J` (**Theorem 3.16**, §3.9, p. 35; §8.2,
printed p. 74 / PDF p. 82), giving an algebraic closure of `K` in the same universe `u`. -/
abbrev ArtinAlgClosure (K : Type u) [Field K] : Type u :=
  ArtinPolyRing K ⧸ artinMaxIdeal K

noncomputable instance artinAlgClosure_field (K : Type u) [Field K] : Field (ArtinAlgClosure K) :=
  ((theorem_3_16 (artinMaxIdeal_spec K).2.1.1).1.mpr (artinMaxIdeal_spec K).2.1).toField

/-- Quotient map `q : K[X_U] →+* M` and natural monomorphism `j = q ∘ i : K →+* M` (§8.2, p. 74). -/
noncomputable def artinQuotMap (K : Type u) [Field K] : ArtinPolyRing K →+* ArtinAlgClosure K :=
  Ideal.Quotient.mk (artinMaxIdeal K)

noncomputable def artinBaseHom (K : Type u) [Field K] : K →+* ArtinAlgClosure K :=
  (artinQuotMap K).comp MvPolynomial.C

noncomputable instance artinAlgClosure_algebra (K : Type u) [Field K] :
    Algebra K (ArtinAlgClosure K) :=
  (artinBaseHom K).toAlgebra

/-- Image `β_j(f) = q(x_j(f)) ∈ M` of each indeterminate `u = (f, j) ∈ U` (§8.2, p. 74). -/
noncomputable def artinBeta (K : Type u) [Field K] (u : ArtinIndex K) : ArtinAlgClosure K :=
  artinQuotMap K (MvPolynomial.X u)

/-- Verification of Garling's pp. 74 claims:
(1) `(j, K, M)` (`artinBaseHom K`) is an extension of `K` where `M = K[X_U] / J` is a field;
(2) every non-constant monic `f ∈ K[x]` splits over `M` as `∏_{r=1}^n (x - β_r(f))`;
(3) the elements `β_u` (`u ∈ U`) are algebraic over `K` and generate `M` over `K`;
(4) `(j, K, M)` is an algebraic closure of `K` (via `Corollary 2` to `Theorem 4.6` and
    `Theorem 8.1`). -/
theorem artinAlgClosure_isGarlingAlgebraicClosure (K : Type u) [Field K] :
    IsGarlingAlgebraicClosure K (ArtinAlgClosure K) ∧
    IntermediateField.adjoin K (Set.range (artinBeta K)) = ⊤ := by
  let q := artinQuotMap K
  let j := artinBaseHom K
  have hIJ : artinIdeal K ≤ artinMaxIdeal K := (artinMaxIdeal_spec K).1
  -- Every non-constant monic `f ∈ K[x]` factors in `M[x]` as `∏ r, (x - β_r(f))`.
  have hmonic_splits : ∀ (f : K[X]) (hmon : f.Monic) (hpos : 0 < f.natDegree),
      f.map (algebraMap K (ArtinAlgClosure K)) =
        ∏ r : Fin f.natDegree,
          (Polynomial.X - Polynomial.C (q (artinVar hmon hpos r))) := by
    intro f hmon hpos
    have hcoeff_eq :
        f.map (algebraMap K (ArtinAlgClosure K)) = (artinG hmon hpos).map q := by
      ext m
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      by_cases hm_lt : m < f.natDegree
      · let i : ℕ := f.natDegree - m
        have hi1 : 1 ≤ i := by omega
        have hin : i ≤ f.natDegree := by omega
        have hmi : f.natDegree - i = m := by omega
        have ht_mem_I : artinT hmon hpos i ∈ artinIdeal K :=
          Ideal.subset_span ⟨f, hmon, hpos, i, hi1, hin, rfl⟩
        have ht_mem_J : artinT hmon hpos i ∈ artinMaxIdeal K := hIJ ht_mem_I
        have hqt0 : q (artinT hmon hpos i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ht_mem_J
        rw [(artinG_coeff_and_artinT hmon hpos hin).2, hmi, map_mul, map_sub] at hqt0
        have hsign_unit : (-1 : ArtinAlgClosure K) ^ i ≠ 0 :=
          pow_ne_zero i (neg_ne_zero.mpr one_ne_zero)
        have hsub0 : q ((artinG hmon hpos).coeff m) - q (MvPolynomial.C (f.coeff m)) = 0 :=
          (mul_eq_zero.mp hqt0).resolve_left hsign_unit
        exact (sub_eq_zero.mp hsub0).symm
      · have hg_mon : (artinG hmon hpos).Monic :=
          Polynomial.monic_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C _
        have hg_deg : (artinG hmon hpos).natDegree = f.natDegree := by
          dsimp [artinG]
          rw [Polynomial.natDegree_prod _ _ fun r _ => Polynomial.X_sub_C_ne_zero _]
          simp
        by_cases hm_eq : m = f.natDegree
        · subst hm_eq
          have hfc : f.coeff f.natDegree = 1 := hmon.leadingCoeff
          have hgc : (artinG hmon hpos).coeff f.natDegree = 1 := by
            rw [← hg_deg]
            exact hg_mon.leadingCoeff
          rw [hfc, hgc, map_one, map_one]
        · have hm_gt : f.natDegree < m := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hm_gt,
            Polynomial.coeff_eq_zero_of_natDegree_lt (hg_deg ▸ hm_gt), map_zero, map_zero]
    rw [hcoeff_eq]
    dsimp [artinG]
    simp [Polynomial.map_prod]
  -- Each `β_u = q(X_u)` is algebraic over `K`, since it is a root of `u.1.1`.
  have hβ_alg : ∀ x ∈ Set.range (artinBeta K), IsGarlingAlgebraic K x := by
    rintro _ ⟨u, rfl⟩
    let f : K[X] := u.1.1
    have hmon : f.Monic := u.2.1
    have hpos : 0 < f.natDegree := u.2.2.1
    let r0 : Fin f.natDegree := ⟨u.1.2 - 1, by dsimp [f]; have := u.2.2.2.1; have := u.2.2.2.2; omega⟩
    have hu_eq : u = ⟨(f, r0.1 + 1), hmon, hpos, by dsimp; omega, by dsimp; omega⟩ := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      dsimp [r0]
      have := u.2.2.2.1
      omega
    have hβ_eq : artinBeta K u = q (artinVar hmon hpos r0) := by
      dsimp [artinBeta, artinVar]
      rw [← hu_eq]
    refine ⟨f, hmon.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmonic_splits f hmon hpos,
      Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ r0)
    rw [hβ_eq, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  -- The `β_u` generate `M = K[X_U] / J` over `K`.
  have hadj_top : IntermediateField.adjoin K (Set.range (artinBeta K)) = ⊤ := by
    let E := IntermediateField.adjoin K (Set.range (artinBeta K))
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
    change q P ∈ E
    induction P using MvPolynomial.induction_on with
    | C a =>
      exact E.algebraMap_mem a
    | add p₁ p₂ ih₁ ih₂ =>
      rw [map_add]
      exact E.add_mem ih₁ ih₂
    | mul_X p u ih =>
      rw [map_mul]
      exact E.mul_mem ih (IntermediateField.subset_adjoin K (Set.range (artinBeta K)) ⟨u, rfl⟩)
  -- By Corollary 2 to Theorem 4.6 (`corollary_2_to_theorem_4_6`), `M : K` is algebraic.
  have halg_ext : IsAlgebraicExtension K (ArtinAlgClosure K) := by
    let E := IntermediateField.adjoin K (Set.range (artinBeta K))
    have halg_adjoin : IsAlgebraicExtension K E := corollary_2_to_theorem_4_6 hβ_alg
    intro z
    have hzE : z ∈ E := by
      change z ∈ IntermediateField.adjoin K (Set.range (artinBeta K))
      rw [hadj_top]
      exact IntermediateField.mem_top
    let zE : E := ⟨z, hzE⟩
    obtain ⟨p, hp0, hpz⟩ := halg_adjoin zE
    refine ⟨p, hp0, ?_⟩
    have hval : E.val (Polynomial.aeval zE p) = 0 := by
      rw [hpz]
      rfl
    rwa [← Polynomial.aeval_algHom_apply E.val zE p] at hval
  -- Every irreducible `f ∈ K[x]` splits over `M`, so `M : K` is an algebraic closure by Theorem 8.1.
  have hclosed : IsGarlingAlgebraicClosure K (ArtinAlgClosure K) := by
    refine (theorem_8_1 K (ArtinAlgClosure K)).1.mpr ⟨halg_ext, fun f hirr => ?_⟩
    have hdeg_pos : 0 < f.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_ne_zero_of_nonunit hirr.ne_zero hirr.not_isUnit)
    have hlc_ne0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
    let fm : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
    have hfm_monic : fm.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ hlc_ne0]
    have hfm_deg : fm.natDegree = f.natDegree := by
      dsimp [fm]
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_ne0)]
    have hfm_pos : 0 < fm.natDegree := hfm_deg ▸ hdeg_pos
    have hfm_fac := hmonic_splits fm hfm_monic hfm_pos
    refine ⟨fm.natDegree, f.leadingCoeff, fun r => q (artinVar hfm_monic hfm_pos r), ?_⟩
    unfold GarlingSplitsExplicit
    have hf_eq : f = Polynomial.C f.leadingCoeff * fm := by
      dsimp [fm]
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc_ne0, map_one, one_mul]
    conv_lhs => rw [hf_eq]
    rw [Polynomial.map_mul, Polynomial.map_C, hfm_fac]
  exact ⟨hclosed, hadj_top⟩

/-- **Theorem 8.2** (§8.2, printed p. 72 / PDF p. 80; proof pp. 72–74 / PDF pp. 80–82):
*"If `K` is a field, there exists an algebraic closure `L : K`."* -/
theorem theorem_8_2 (K : Type u) [Field K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      IsGarlingAlgebraicClosure K L :=
  ⟨ArtinAlgClosure K, inferInstance, inferInstance, (artinAlgClosure_isGarlingAlgebraicClosure K).1⟩

/-- **Theorem 8.2 (extension-triple `(j, K, M)` form)** (§8.2, printed pp. 72 & 74):
For every field `K`, there exists a field `M` (in the same universe as `K`) and an extension
triple `ext : FieldExtensionTriple K M` such that `(j, K, M)` is an algebraic closure of `K`. -/
theorem theorem_8_2_triple (K : Type u) [Field K] :
    ∃ (M : Type u) (_ : Field M) (ext : FieldExtensionTriple K M),
      IsGarlingAlgebraicClosureTriple ext :=
  ⟨ArtinAlgClosure K, inferInstance, FieldExtensionTriple.ofRingHom (artinBaseHom K),
    (artinAlgClosure_isGarlingAlgebraicClosure K).1⟩

/-! ### Exercises 8.1–8.3 (§8.2, printed pp. 74–75 / PDF pp. 82–83) -/

/-- **Exercise 8.1 (i)** (§8.2, printed p. 74 / PDF p. 82):
*"Suppose that `U` is a non-empty set, and that `P(U)` is the set of subsets of `U`. Show that if
`V ⊆ U` and `f : V → P(U)` is a mapping, then `f` is not onto. (Consider `{x : x ∈ V, x ∉ f(x)}`.)"* -/
theorem exercise_8_1_i {U : Type u} [Nonempty U] {V : Set U} (f : V → Set U) :
    ¬ Function.Surjective f := by
  intro hsurj
  let D : Set U := {x : U | ∃ hx : x ∈ V, x ∉ f ⟨x, hx⟩}
  obtain ⟨⟨v, hv⟩, hfv⟩ := hsurj D
  have hmem : v ∈ D ↔ v ∈ f ⟨v, hv⟩ := by rw [hfv]
  have hdiag : v ∈ D ↔ v ∉ f ⟨v, hv⟩ := by
    simp [D, hv]
  exact iff_not_self (hmem.symm.trans hdiag)

/-- Ambient-subset formulation of **Exercise 8.1 (i)** where `U : Set α`, `U.Nonempty`, `V ⊆ U`,
and `P(U) = {S : Set α // S ⊆ U}`. -/
theorem exercise_8_1_i_subset {α : Type u} {U V : Set α} (hU : U.Nonempty) (hVU : V ⊆ U)
    (f : V → {S : Set α // S ⊆ U}) :
    ¬ Function.Surjective f := by
  have _ : Nonempty U := hU.to_subtype
  let V' : Set U := {u : U | u.1 ∈ V}
  let f' : V' → Set U := fun v => {u : U | u.1 ∈ (f ⟨v.1.1, v.2⟩).1}
  intro hsurj
  apply exercise_8_1_i f'
  intro A
  let S : Set α := Subtype.val '' A
  have hSU : S ⊆ U := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  obtain ⟨⟨v, hvV⟩, hfv⟩ := hsurj ⟨S, hSU⟩
  refine ⟨⟨⟨v, hVU hvV⟩, hvV⟩, ?_⟩
  ext u
  change u.1 ∈ (f ⟨v, hvV⟩).1 ↔ u ∈ A
  rw [hfv]
  simp [S]

/-- **Exercise 8.1 (ii)** (§8.2, printed pp. 74–75 / PDF pp. 82–83):
*"Suppose that `U` is a non-empty set and that `V ⊆ W ⊆ U`. Show that if `f : V → P(U)` is one–one
then there exists a one–one map `g : W → P(U)` such that `g|_V = f`. (Use Zorn's lemma.)"*

Proved directly using Chapter 2's `zorn_lemma_set` and `Exercise 8.1 (i)`. -/
theorem exercise_8_1_ii {U : Type u} [Nonempty U] {V W : Set U} (hVW : V ⊆ W)
    {f : V → Set U} (hf : Function.Injective f) :
    ∃ g : W → Set U, Function.Injective g ∧ ∀ v : V, g ⟨v.1, hVW v.2⟩ = f v := by
  classical
  -- Partial extensions `(A, h)` with `V ⊆ A ⊆ W`, `h` normalized to `∅` outside `A`,
  -- `h` injective on `A`, and `h|_V = f`.
  let P : Set (Set U × (U → Set U)) :=
    {p | V ⊆ p.1 ∧ p.1 ⊆ W ∧
      (∀ x : U, x ∉ p.1 → p.2 x = ∅) ∧
      Set.InjOn p.2 p.1 ∧
      ∀ v : V, p.2 v.1 = f v}
  let leP : (Set U × (U → Set U)) → (Set U × (U → Set U)) → Prop :=
    fun p₁ p₂ => p₁.1 ⊆ p₂.1 ∧ ∀ x ∈ p₁.1, p₂.2 x = p₁.2 x
  have hpo : IsGarlingPartialOrder P leP := by
    refine ⟨fun p _ => ⟨Set.Subset.refl _, fun _ _ => rfl⟩,
      fun {p₁ p₂ p₃} _ _ _ h12 h23 =>
        ⟨h12.1.trans h23.1, fun x hx => (h23.2 x (h12.1 hx)).trans (h12.2 x hx)⟩,
      fun {p₁ p₂} hp₁ hp₂ h12 h21 => ?_⟩
    have hdom : p₁.1 = p₂.1 := Set.Subset.antisymm h12.1 h21.1
    refine Prod.ext hdom (funext fun x => ?_)
    by_cases hx : x ∈ p₁.1
    · exact (h12.2 x hx).symm
    · have hx2 : x ∉ p₂.1 := hdom ▸ hx
      rw [hp₁.2.2.1 x hx, hp₂.2.2.1 x hx2]
  let h₀ : U → Set U := fun x => if hx : x ∈ V then f ⟨x, hx⟩ else ∅
  have hp₀ : (V, h₀) ∈ P := by
    refine ⟨Set.Subset.refl V, hVW, fun x hx => by simp [h₀, hx], ?_, fun v => by simp [h₀, v.2]⟩
    intro x hx y hy hxy
    dsimp [h₀] at hxy
    simp only [hx, hy, ↓reduceDIte] at hxy
    exact congrArg Subtype.val (hf hxy)
  have hchains : ∀ C : Set (Set U × (U → Set U)), IsGarlingChain P leP C →
      ∃ ub, IsGarlingUpperBound P leP C ub := by
    rintro C ⟨hCP, ⟨p_init, hp_init⟩, hCtot⟩
    let A₀ : Set U := {x : U | ∃ p ∈ C, x ∈ p.1}
    let h_ub : U → Set U := fun x =>
      if hx : x ∈ A₀ then hx.choose.2 x else ∅
    have h_ub_agrees : ∀ p ∈ C, ∀ x ∈ p.1, h_ub x = p.2 x := by
      intro p hpC x hxp
      have hxA₀ : x ∈ A₀ := ⟨p, hpC, hxp⟩
      dsimp [h_ub]
      simp only [hxA₀, ↓reduceDIte]
      let q := hxA₀.choose
      have hqC : q ∈ C := hxA₀.choose_spec.1
      have hxq : x ∈ q.1 := hxA₀.choose_spec.2
      rcases hCtot p hpC q hqC with hpq | hqp
      · exact hpq.2 x hxp
      · exact (hqp.2 x hxq).symm
    have hub_P : (A₀, h_ub) ∈ P := by
      refine ⟨fun v hv => ⟨p_init, hp_init, (hCP hp_init).1 hv⟩, ?_,
        fun x hx => by simp [h_ub, hx], ?_, ?_⟩
      · rintro x ⟨p, hpC, hxp⟩
        exact (hCP hpC).2.1 hxp
      · rintro x ⟨p₁, hp₁C, hxp₁⟩ y ⟨p₂, hp₂C, hyp₂⟩ hxy
        dsimp only at hxy
        rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
        · rw [h_ub_agrees p₂ hp₂C x (h12.1 hxp₁), h_ub_agrees p₂ hp₂C y hyp₂] at hxy
          exact (hCP hp₂C).2.2.2.1 (h12.1 hxp₁) hyp₂ hxy
        · rw [h_ub_agrees p₁ hp₁C x hxp₁, h_ub_agrees p₁ hp₁C y (h21.1 hyp₂)] at hxy
          exact (hCP hp₁C).2.2.2.1 hxp₁ (h21.1 hyp₂) hxy
      · intro v
        dsimp only
        rw [h_ub_agrees p_init hp_init v.1 ((hCP hp_init).1 v.2)]
        exact (hCP hp_init).2.2.2.2 v
    exact ⟨(A₀, h_ub), hub_P, fun p hpC =>
      ⟨fun x hxp => ⟨p, hpC, hxp⟩, fun x hxp => h_ub_agrees p hpC x hxp⟩⟩
  obtain ⟨⟨A, h⟩, ⟨hVA, hAW, hOut, hInj, hExt⟩, hMax⟩ :=
    zorn_lemma_set hpo ⟨(V, h₀), hp₀⟩ hchains
  have hAW_eq : A = W := by
    by_contra hne
    have hex_w : ∃ w ∈ W, w ∉ A := by
      by_contra hall
      apply hne
      exact Set.Subset.antisymm hAW fun w hw => by_contra fun hnw => hall ⟨w, hw, hnw⟩
    obtain ⟨w, hwW, hwA⟩ := hex_w
    -- By Exercise 8.1 (i), `a ↦ h a.1 : A → P(U)` is not onto `P(U)`.
    have hnot_surj : ¬ Function.Surjective (fun a : A => h a.1) := exercise_8_1_i _
    have hex_B : ∃ B : Set U, ∀ a ∈ A, h a ≠ B := by
      by_contra hallB
      push Not at hallB
      apply hnot_surj
      intro B
      obtain ⟨a, haA, haB⟩ := hallB B
      exact ⟨⟨a, haA⟩, haB⟩
    obtain ⟨B, hB⟩ := hex_B
    let A' : Set U := insert w A
    let h' : U → Set U := fun x => if x = w then B else h x
    have hp' : (A', h') ∈ P := by
      refine ⟨hVA.trans (Set.subset_insert w A), Set.insert_subset hwW hAW, ?_, ?_, ?_⟩
      · intro x hx
        have hxw : x ≠ w := fun h0 => hx (h0 ▸ Set.mem_insert w A)
        have hxA : x ∉ A := fun h0 => hx (Set.mem_insert_of_mem w h0)
        dsimp [h']
        simp only [hxw, ↓reduceIte]
        exact hOut x hxA
      · intro x hx y hy hxy
        dsimp [h'] at hxy
        rcases Set.mem_insert_iff.mp hx with hxw_eq | hxA <;>
          rcases Set.mem_insert_iff.mp hy with hyw_eq | hyA
        · exact hxw_eq.trans hyw_eq.symm
        · have hyw : y ≠ w := fun h0 => hwA (h0 ▸ hyA)
          simp only [hxw_eq, ↓reduceIte, hyw] at hxy
          exact False.elim (hB y hyA hxy.symm)
        · have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
          simp only [hxw, hyw_eq, ↓reduceIte] at hxy
          exact False.elim (hB x hxA hxy)
        · have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
          have hyw : y ≠ w := fun h0 => hwA (h0 ▸ hyA)
          simp only [hxw, hyw, ↓reduceIte] at hxy
          exact hInj hxA hyA hxy
      · intro v
        have hvw : v.1 ≠ w := fun h0 => hwA (h0 ▸ hVA v.2)
        dsimp [h']
        simp only [hvw, ↓reduceIte]
        exact hExt v
    have hle' : leP (A, h) (A', h') := by
      refine ⟨Set.subset_insert w A, fun x hxA => ?_⟩
      have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
      dsimp [h']
      simp [hxw]
    have heq : (A, h) = (A', h') := hMax (A', h') hp' hle'
    have hAeq : A = insert w A := congrArg Prod.fst heq
    exact hwA (hAeq.symm ▸ Set.mem_insert w A)
  subst hAW_eq
  refine ⟨fun w => h w.1, fun w₁ w₂ hw => Subtype.ext (hInj w₁.2 w₂.2 hw), fun v => hExt v⟩

/-- Ambient-subset formulation of **Exercise 8.1 (ii)** where `V ⊆ W ⊆ U ⊆ α`, `U.Nonempty`, and
`P(U) = {S : Set α // S ⊆ U}`. -/
theorem exercise_8_1_ii_subset {α : Type u} {U V W : Set α}
    (hU : U.Nonempty) (hVW : V ⊆ W) (hWU : W ⊆ U)
    {f : V → {S : Set α // S ⊆ U}} (hf : Function.Injective f) :
    ∃ g : W → {S : Set α // S ⊆ U},
      Function.Injective g ∧ ∀ v : V, g ⟨v.1, hVW v.2⟩ = f v := by
  have _ : Nonempty U := hU.to_subtype
  let V' : Set U := {u : U | u.1 ∈ V}
  let W' : Set U := {u : U | u.1 ∈ W}
  have hVW' : V' ⊆ W' := fun u hu => hVW hu
  let ePow : {S : Set α // S ⊆ U} ≃ Set U :=
    { toFun := fun S => {u : U | u.1 ∈ S.1}
      invFun := fun A => ⟨Subtype.val '' A, by rintro _ ⟨u, _, rfl⟩; exact u.2⟩
      left_inv := fun S => by
        ext x
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact hu
        · intro hx
          exact ⟨⟨x, S.2 hx⟩, hx, rfl⟩
      right_inv := fun A => by
        ext u
        simp }
  let eV : V' ≃ V :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun v => ⟨⟨v.1, hWU (hVW v.2)⟩, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f' : V' → Set U := fun v => ePow (f (eV v))
  have hf' : Function.Injective f' := ePow.injective.comp (hf.comp eV.injective)
  obtain ⟨g', hg'_inj, hg'_ext⟩ := exercise_8_1_ii hVW' hf'
  let eW : W ≃ W' :=
    { toFun := fun w => ⟨⟨w.1, hWU w.2⟩, w.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : W → {S : Set α // S ⊆ U} := fun w => ePow.symm (g' (eW w))
  refine ⟨g, ePow.symm.injective.comp (hg'_inj.comp eW.injective), fun v => ?_⟩
  dsimp [g, eW]
  have hv' := hg'_ext ⟨⟨v.1, hWU (hVW v.2)⟩, v.2⟩
  dsimp [f', eV] at hv'
  rw [hv', ePow.symm_apply_apply]

/-- **Exercise 8.1** (§8.2, printed pp. 74–75 / PDF pp. 82–83):
Combined statement conjoining parts `(i)` and `(ii)`. -/
theorem exercise_8_1 {U : Type u} [Nonempty U] :
    (∀ (V : Set U) (f : V → Set U), ¬ Function.Surjective f) ∧
    (∀ {V W : Set U} (hVW : V ⊆ W) {f : V → Set U},
      Function.Injective f →
      ∃ g : W → Set U, Function.Injective g ∧ ∀ v : V, g ⟨v.1, hVW v.2⟩ = f v) :=
  ⟨fun _ f => exercise_8_1_i f, fun {_ _} hVW {_} hf => exercise_8_1_ii hVW hf⟩

/-- Garling's set `U = K[x] × ℤ⁺` in **Exercises 8.2–8.3** (§8.2, printed p. 75 / PDF p. 83),
where `ℤ⁺ = ℕ+ = {1, 2, 3, …}`. -/
abbrev Ex82U (K : Type u) [Field K] : Type u :=
  K[X] × ℕ+

/-- **Exercise 8.2 (i)** (§8.2, printed p. 75 / PDF p. 83):
*"Suppose that `K` is a field. Let `U = K[x] × ℤ⁺`. Show that if `(k, K, L)` is an algebraic
extension, then there exists a one–one mapping of `L` into `U`. (Use Zorn's lemma.)"*

Proved across arbitrary universes `{K : Type u} {L : Type v}` via Chapter 2's `zorn_lemma_set` on
partial injections `φ : A → K[x] × ℤ⁺` satisfying `(φ(α)).1 = minpoly K α`. -/
theorem exercise_8_2_i {K : Type u} {L : Type v} [Field K] [Field L]
    (ext : FieldExtensionTriple K L)
    (halg : letI : Algebra K L := ext.hom.toAlgebra; IsAlgebraicExtension K L) :
    ∃ φ : L → Ex82U K, Function.Injective φ := by
  classical
  let _ : Algebra K L := ext.hom.toAlgebra
  have halg' : IsAlgebraicExtension K L := halg
  let dflt : Ex82U K := (0, 1)
  let P : Set (Set L × (L → Ex82U K)) :=
    {p | (∀ x : L, x ∉ p.1 → p.2 x = dflt) ∧
      Set.InjOn p.2 p.1 ∧
      ∀ x ∈ p.1, (p.2 x).1 = minpoly K x}
  let leP : (Set L × (L → Ex82U K)) → (Set L × (L → Ex82U K)) → Prop :=
    fun p₁ p₂ => p₁.1 ⊆ p₂.1 ∧ ∀ x ∈ p₁.1, p₂.2 x = p₁.2 x
  have hpo : IsGarlingPartialOrder P leP := by
    refine ⟨fun _ _ => ⟨Set.Subset.refl _, fun _ _ => rfl⟩,
      fun {_ _ _} _ _ _ h12 h23 =>
        ⟨h12.1.trans h23.1, fun x hx => (h23.2 x (h12.1 hx)).trans (h12.2 x hx)⟩,
      fun {p₁ p₂} hp₁ hp₂ h12 h21 => ?_⟩
    have hdom : p₁.1 = p₂.1 := Set.Subset.antisymm h12.1 h21.1
    refine Prod.ext hdom (funext fun x => ?_)
    by_cases hx : x ∈ p₁.1
    · exact (h12.2 x hx).symm
    · rw [hp₁.1 x hx, hp₂.1 x (hdom ▸ hx)]
  have hp₀ : ((∅ : Set L), fun _ : L => dflt) ∈ P :=
    ⟨fun _ _ => rfl, by simp, by simp⟩
  have hchains : ∀ C : Set (Set L × (L → Ex82U K)), IsGarlingChain P leP C →
      ∃ ub, IsGarlingUpperBound P leP C ub := by
    rintro C ⟨hCP, _, hCtot⟩
    let A₀ : Set L := {x : L | ∃ p ∈ C, x ∈ p.1}
    let h_ub : L → Ex82U K := fun x =>
      if hx : x ∈ A₀ then hx.choose.2 x else dflt
    have h_ub_agrees : ∀ p ∈ C, ∀ x ∈ p.1, h_ub x = p.2 x := by
      intro p hpC x hxp
      have hxA₀ : x ∈ A₀ := ⟨p, hpC, hxp⟩
      dsimp [h_ub]
      simp only [hxA₀, ↓reduceDIte]
      let q := hxA₀.choose
      have hqC : q ∈ C := hxA₀.choose_spec.1
      have hxq : x ∈ q.1 := hxA₀.choose_spec.2
      rcases hCtot p hpC q hqC with hpq | hqp
      · exact hpq.2 x hxp
      · exact (hqp.2 x hxq).symm
    have hub_P : (A₀, h_ub) ∈ P := by
      refine ⟨fun x hx => by simp [h_ub, hx], ?_, ?_⟩
      · rintro x ⟨p₁, hp₁C, hxp₁⟩ y ⟨p₂, hp₂C, hyp₂⟩ hxy
        dsimp only at hxy
        rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
        · rw [h_ub_agrees p₂ hp₂C x (h12.1 hxp₁), h_ub_agrees p₂ hp₂C y hyp₂] at hxy
          exact (hCP hp₂C).2.1 (h12.1 hxp₁) hyp₂ hxy
        · rw [h_ub_agrees p₁ hp₁C x hxp₁, h_ub_agrees p₁ hp₁C y (h21.1 hyp₂)] at hxy
          exact (hCP hp₁C).2.1 hxp₁ (h21.1 hyp₂) hxy
      · rintro x ⟨p, hpC, hxp⟩
        dsimp only
        rw [h_ub_agrees p hpC x hxp]
        exact (hCP hpC).2.2 x hxp
    exact ⟨(A₀, h_ub), hub_P, fun p hpC =>
      ⟨fun x hxp => ⟨p, hpC, hxp⟩, fun x hxp => h_ub_agrees p hpC x hxp⟩⟩
  obtain ⟨⟨A, φ⟩, ⟨hOut, hInj, hMin⟩, hMax⟩ :=
    zorn_lemma_set hpo ⟨(∅, fun _ => dflt), hp₀⟩ hchains
  have hA_univ : A = Set.univ := by
    by_contra hne
    have hex_w : ∃ w : L, w ∉ A := by
      by_contra hall
      push Not at hall
      exact hne (Set.eq_univ_of_forall hall)
    obtain ⟨w, hwA⟩ := hex_w
    let m : K[X] := minpoly K w
    have hw_int : IsIntegral K w := (isGarlingAlgebraic_iff_isIntegral K w).mp (halg' w)
    have hm_ne0 : m ≠ 0 := minpoly.ne_zero hw_int
    -- Only finitely many `x ∈ A` can satisfy `(φ x).1 = m`, since each such `x` is a root of `m`.
    let S_m : Set L := {x : L | x ∈ A ∧ (φ x).1 = m}
    have hS_m_sub : S_m ⊆ m.rootSet L := by
      rintro x ⟨hxA, hφx⟩
      rw [Polynomial.mem_rootSet]
      refine ⟨hm_ne0, ?_⟩
      have hmx : minpoly K x = m := (hMin x hxA).symm.trans hφx
      dsimp [m] at hmx ⊢
      rw [← hmx]
      exact minpoly.aeval K x
    have hS_m_fin : S_m.Finite := (m.rootSet_finite L).subset hS_m_sub
    let idxFinset : Finset ℕ := (hS_m_fin.image fun x => (φ x).2.1).toFinset
    let nextNat : ℕ := idxFinset.sup id + 1
    let nextPNat : ℕ+ := ⟨nextNat, by omega⟩
    have hnext_not_mem : ∀ x ∈ S_m, (φ x).2 ≠ nextPNat := by
      intro x hx hEq
      have hmem : (φ x).2.1 ∈ idxFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨x, hx, rfl⟩
      have hle : (φ x).2.1 ≤ idxFinset.sup id := Finset.le_sup (f := id) hmem
      have hval : (φ x).2.1 = nextNat := congrArg Subtype.val hEq
      dsimp [nextNat] at hval
      omega
    let A' : Set L := insert w A
    let φ' : L → Ex82U K := fun x => if x = w then (m, nextPNat) else φ x
    have hp' : (A', φ') ∈ P := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have hxw : x ≠ w := fun h0 => hx (h0 ▸ Set.mem_insert w A)
        have hxA : x ∉ A := fun h0 => hx (Set.mem_insert_of_mem w h0)
        dsimp [φ']
        simp only [hxw, ↓reduceIte]
        exact hOut x hxA
      · intro x hx y hy hxy
        dsimp [φ'] at hxy
        rcases Set.mem_insert_iff.mp hx with hxw_eq | hxA <;>
          rcases Set.mem_insert_iff.mp hy with hyw_eq | hyA
        · exact hxw_eq.trans hyw_eq.symm
        · have hyw : y ≠ w := fun h0 => hwA (h0 ▸ hyA)
          simp only [hxw_eq, ↓reduceIte, hyw] at hxy
          have hy1 : (φ y).1 = m := (congrArg Prod.fst hxy).symm
          have hy2 : (φ y).2 = nextPNat := (congrArg Prod.snd hxy).symm
          exact False.elim (hnext_not_mem y ⟨hyA, hy1⟩ hy2)
        · have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
          simp only [hxw, hyw_eq, ↓reduceIte] at hxy
          have hx1 : (φ x).1 = m := congrArg Prod.fst hxy
          have hx2 : (φ x).2 = nextPNat := congrArg Prod.snd hxy
          exact False.elim (hnext_not_mem x ⟨hxA, hx1⟩ hx2)
        · have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
          have hyw : y ≠ w := fun h0 => hwA (h0 ▸ hyA)
          simp only [hxw, hyw, ↓reduceIte] at hxy
          exact hInj hxA hyA hxy
      · intro x hx
        dsimp [φ']
        rcases Set.mem_insert_iff.mp hx with hxw_eq | hxA
        · simp [hxw_eq, m]
        · have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
          simp only [hxw, ↓reduceIte]
          exact hMin x hxA
    have hle' : leP (A, φ) (A', φ') := by
      refine ⟨Set.subset_insert w A, fun x hxA => ?_⟩
      have hxw : x ≠ w := fun h0 => hwA (h0 ▸ hxA)
      dsimp [φ']
      simp [hxw]
    have heq := hMax (A', φ') hp' hle'
    have hAeq : A = insert w A := congrArg Prod.fst heq
    exact hwA (hAeq.symm ▸ Set.mem_insert w A)
  subst hA_univ
  exact ⟨φ, fun x y hxy => hInj trivial trivial hxy⟩

/-- `[Algebra K L]` specialization of **Exercise 8.2 (i)** (§8.2, printed p. 75). -/
theorem exercise_8_2_i_algebra {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) :
    ∃ φ : L → Ex82U K, Function.Injective φ :=
  exercise_8_2_i (FieldExtensionTriple.ofAlgebra K L) halg

/-- **Exercise 8.2 (ii)** (§8.2, printed p. 75 / PDF p. 83):
*"Suppose that `(k, K, L)` and `(l, L, M)` are algebraic extensions. Show that if `f : L → P(U)` is
one–one then there exists a one–one map `g : M → P(U)` such that `f = g ∘ l`."*

Proved across arbitrary universes `{K : Type u} {L : Type v} {M : Type w}` using `Theorem 4.7`,
`Exercise 8.2 (i)`, and `Exercise 8.1 (ii)`. -/
theorem exercise_8_2_ii {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    (extKL : FieldExtensionTriple K L) (extLM : FieldExtensionTriple L M)
    (halgKL : letI : Algebra K L := extKL.hom.toAlgebra; IsAlgebraicExtension K L)
    (halgLM : letI : Algebra L M := extLM.hom.toAlgebra; IsAlgebraicExtension L M)
    {f : L → Set (Ex82U K)} (hf : Function.Injective f) :
    ∃ g : M → Set (Ex82U K), Function.Injective g ∧ f = g ∘ extLM.hom := by
  have halgKM :
      (letI : Algebra K M := (extLM.hom.comp extKL.hom).toAlgebra; IsAlgebraicExtension K M) :=
    theorem_4_7_triple extKL extLM halgLM halgKL
  obtain ⟨ι, hι⟩ := exercise_8_2_i (FieldExtensionTriple.ofRingHom (extLM.hom.comp extKL.hom)) halgKM
  have _ : Nonempty (Ex82U K) := ⟨(0, 1)⟩
  let W : Set (Ex82U K) := Set.range ι
  let V : Set (Ex82U K) := Set.range (ι ∘ extLM.hom)
  have hVW : V ⊆ W := by
    rintro _ ⟨x, rfl⟩
    exact ⟨extLM.hom x, rfl⟩
  let eW : M ≃ W := Equiv.ofInjective ι hι
  let eV : L ≃ V := Equiv.ofInjective (ι ∘ extLM.hom) (hι.comp extLM.mono)
  let f' : V → Set (Ex82U K) := fun v => f (eV.symm v)
  have hf' : Function.Injective f' := hf.comp eV.symm.injective
  obtain ⟨g', hg'_inj, hg'_ext⟩ := exercise_8_1_ii hVW hf'
  let g : M → Set (Ex82U K) := fun m => g' (eW m)
  refine ⟨g, hg'_inj.comp eW.injective, funext fun x => ?_⟩
  dsimp [g, Function.comp]
  have heW_eq : eW (extLM.hom x) = ⟨(eV x).1, hVW (eV x).2⟩ := Subtype.ext rfl
  rw [heW_eq, hg'_ext (eV x)]
  dsimp [f']
  rw [eV.symm_apply_apply]

/-- **Exercise 8.2** (§8.2, printed p. 75 / PDF p. 83):
Combined statement conjoining parts `(i)` and `(ii)`. -/
theorem exercise_8_2 (K : Type u) [Field K] :
    (∀ {L : Type v} [Field L] (ext : FieldExtensionTriple K L),
      (letI : Algebra K L := ext.hom.toAlgebra; IsAlgebraicExtension K L) →
      ∃ φ : L → Ex82U K, Function.Injective φ) ∧
    (∀ {L : Type v} {M : Type w} [Field L] [Field M]
      (extKL : FieldExtensionTriple K L) (extLM : FieldExtensionTriple L M),
      (letI : Algebra K L := extKL.hom.toAlgebra; IsAlgebraicExtension K L) →
      (letI : Algebra L M := extLM.hom.toAlgebra; IsAlgebraicExtension L M) →
      ∀ {f : L → Set (Ex82U K)}, Function.Injective f →
        ∃ g : M → Set (Ex82U K), Function.Injective g ∧ f = g ∘ extLM.hom) :=
  ⟨fun {_ _} ext halg => exercise_8_2_i ext halg,
   fun {_ _ _ _} extKL extLM halgKL halgLM {_} hf => exercise_8_2_ii extKL extLM halgKL halgLM hf⟩

/-! ### Exercise 8.3 (§8.2, printed p. 75 / PDF p. 83) -/

/-- Reconstruct a Mathlib `Field F` instance from Garling's §1.2 field axioms
`IsGarlingField F add mul` whose underlying `+` and `*` operations are definitionally `add` and
`mul` (used for `F(S)` in `Exercise 8.3 (ii)`–`(iii)`). -/
@[instance_reducible]
noncomputable def garlingFieldToField {F : Type u} {add mul : LawOfComposition F}
    (h : IsGarlingField F add mul) : Field F :=
  open Classical in
  let zero : F := h.exists_zero_one.choose
  let rest₁ := h.exists_zero_one.choose_spec
  let one : F := rest₁.choose
  let spec := rest₁.choose_spec
  let h01 := spec.1
  let hadd_assoc := spec.2.1
  let hzero_add := spec.2.2.2.1
  let hneg := spec.2.2.2.2.1
  let hmul_zero := spec.2.2.2.2.2.1
  let hmul_assoc := spec.2.2.2.2.2.2.2.1
  let hmul_comm := spec.2.2.2.2.2.2.2.2.1
  let hone_mul := spec.2.2.2.2.2.2.2.2.2.1
  let hinv := spec.2.2.2.2.2.2.2.2.2.2.1
  let hdistrib := spec.2.2.2.2.2.2.2.2.2.2.2
  let invFun : F → F := fun x => if hx : x = zero then zero else (hinv x hx).choose
  letI : Add F := ⟨add⟩
  letI : Mul F := ⟨mul⟩
  letI : Zero F := ⟨zero⟩
  letI : One F := ⟨one⟩
  letI : Neg F := ⟨fun x => (hneg x).choose⟩
  letI : Inv F := ⟨invFun⟩
  Field.ofMinimalAxioms F
    (fun a b c => (hadd_assoc a b c).symm)
    (fun a => (hzero_add a).1)
    (fun a => (hneg a).choose_spec.2)
    (fun a b c => by
      change mul (mul a b) c = mul a (mul b c)
      by_cases ha : a = zero
      · subst ha
        rw [(hmul_zero b).1, (hmul_zero c).1, (hmul_zero (mul b c)).1]
      · by_cases hb : b = zero
        · subst hb
          rw [(hmul_zero a).2, (hmul_zero c).1, (hmul_zero a).2]
        · by_cases hc : c = zero
          · subst hc
            rw [(hmul_zero (mul a b)).2, (hmul_zero b).2, (hmul_zero a).2]
          · exact (hmul_assoc a b c ha hb hc).symm)
    (fun a b => by
      change mul a b = mul b a
      by_cases ha : a = zero
      · subst ha
        rw [(hmul_zero b).1, (hmul_zero b).2]
      · by_cases hb : b = zero
        · subst hb
          rw [(hmul_zero a).2, (hmul_zero a).1]
        · exact hmul_comm a b ha hb)
    (fun a => by
      change mul one a = a
      by_cases ha : a = zero
      · subst ha
        exact (hmul_zero one).2
      · exact (hone_mul a ha).1)
    (fun a ha => by
      change mul a (invFun a) = one
      dsimp [invFun]
      split_ifs with hx
      · exact absurd hx ha
      · exact (hinv a hx).choose_spec.2.1)
    (by
      change invFun zero = zero
      dsimp [invFun]
      split_ifs with hx
      · rfl
      · exact absurd rfl hx)
    hdistrib
    ⟨zero, one, h01⟩

/-- Garling's singleton embedding `j : K → P(U)` sending `α ↦ {(x - α, 1)}`, where
`U = K[x] × ℤ⁺` (**Exercise 8.3 (i)**, printed p. 75 / PDF p. 83). -/
noncomputable def ex83J (K : Type u) [Field K] (α : K) : Set (Ex82U K) :=
  {(Polynomial.X - Polynomial.C α, 1)}

theorem ex83J_injective (K : Type u) [Field K] : Function.Injective (ex83J K) := by
  intro α β h
  have hmem : (Polynomial.X - Polynomial.C α, (1 : ℕ+)) ∈ ex83J K β := by
    rw [← h]
    exact Set.mem_singleton _
  have hpoly : (Polynomial.X - Polynomial.C α : K[X]) = Polynomial.X - Polynomial.C β :=
    congrArg Prod.fst (Set.mem_singleton_iff.mp hmem)
  have hcoeff := congrArg (fun p : K[X] => p.coeff 0) hpoly
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
    zero_sub] at hcoeff
  exact neg_injective hcoeff

/-- The image `j(K) ⊆ P(U)` in **Exercise 8.3** (§8.2, printed p. 75 / PDF p. 83). -/
def Ex83JK (K : Type u) [Field K] : Set (Set (Ex82U K)) :=
  Set.range (ex83J K)

/-- Canonical bijection `j : K ≃ j(K)` induced by `ex83J K`. -/
noncomputable def ex83JEquiv (K : Type u) [Field K] : K ≃ Ex83JK K :=
  Equiv.ofInjective (ex83J K) (ex83J_injective K)

/-- Transported `Field` structure on `j(K)` making `j : K → j(K)` a field isomorphism
(**Exercise 8.3 (i)**, printed p. 75). -/
noncomputable instance ex83JKField (K : Type u) [Field K] : Field (Ex83JK K) :=
  (ex83JEquiv K).symm.field

/-- Canonical field isomorphism `j : K ≃+* j(K)` (**Exercise 8.3 (i)**, printed p. 75). -/
noncomputable def ex83JRingEquiv (K : Type u) [Field K] : K ≃+* Ex83JK K :=
  (ex83JEquiv K).symm.ringEquiv.symm

@[simp]
theorem ex83JRingEquiv_coe (K : Type u) [Field K] (α : K) :
    ((ex83JRingEquiv K α : Ex83JK K) : Set (Ex82U K)) = ex83J K α :=
  rfl

/-- **Exercise 8.3 (i)** (§8.2, printed p. 75 / PDF p. 83):
*"If `α ∈ K`, let `j(α) = {(x - α, 1)}`. Show that `j : K → P(U)` is one–one, and that `j(K)` can
be given the structure of a field in such a way that `j` is a field isomorphism."* -/
theorem exercise_8_3_i (K : Type u) [Field K] :
    Function.Injective (ex83J K) ∧
    IsGarlingField (Ex83JK K) (· + ·) (· * ·) ∧
    IsRingIsomorphism (ex83JRingEquiv K).toRingHom ∧
    (∀ α : K, ((ex83JRingEquiv K α : Ex83JK K) : Set (Ex82U K)) = ex83J K α) :=
  ⟨ex83J_injective K, Field.isGarlingField (Ex83JK K), (ex83JRingEquiv K).bijective,
    fun _ => rfl⟩

/-- A triple `(S, +, .)` in `P(U)` (**Exercise 8.3 (ii)**, printed p. 75 / PDF p. 83), living in
the same universe `u` as `K`. -/
structure Ex83Triple (K : Type u) [Field K] : Type u where
  S : Set (Set (Ex82U K))
  add : S → S → S
  mul : S → S → S

/-- Helper: an injective map between fields preserving `+` and `*` automatically preserves `0` and
`1`, hence is a ring monomorphism `F₁ →+* F₂`. -/
private noncomputable def ringHomOfInjAddMul {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (f : F₁ → F₂) (hf_inj : Function.Injective f)
    (hadd : ∀ x y : F₁, f (x + y) = f x + f y)
    (hmul : ∀ x y : F₁, f (x * y) = f x * f y) : F₁ →+* F₂ where
  toFun := f
  map_zero' := by
    have h0 : f 0 + f 0 = f 0 + 0 := by rw [← hadd, add_zero, add_zero]
    exact add_left_cancel h0
  map_one' := by
    have h0 : f 0 = 0 := by
      have h0' : f 0 + f 0 = f 0 + 0 := by rw [← hadd, add_zero, add_zero]
      exact add_left_cancel h0'
    have h1_ne0 : f 1 ≠ 0 := fun h => one_ne_zero (hf_inj (h.trans h0.symm))
    have h1 : f 1 * f 1 = f 1 * 1 := by rw [← hmul, mul_one, mul_one]
    exact mul_left_cancel₀ h1_ne0 h1
  map_add' := hadd
  map_mul' := hmul

/-- Membership predicate for Garling's family `ℱ` of triples `(S, +, .)` in **Exercise 8.3 (ii)**
(§8.2, printed p. 75 / PDF p. 83):
(a) `j(K) ⊆ S ⊆ P(U)`;
(b) `(S, +, .)` is a field `F(S)`;
(c) `(i, j(K), F(S))` is an algebraic extension (where `i : j(K) → F(S)` is the inclusion mapping,
    and `j(K)` carries the field structure from `(i)`). -/
def Ex83F (K : Type u) [Field K] : Set (Ex83Triple K) :=
  {t | ∃ (hJK : Ex83JK K ⊆ t.S) (hField : IsGarlingField t.S t.add t.mul)
      (hadd : ∀ x y : Ex83JK K,
          Set.inclusion hJK (x + y) = t.add (Set.inclusion hJK x) (Set.inclusion hJK y))
      (hmul : ∀ x y : Ex83JK K,
          Set.inclusion hJK (x * y) = t.mul (Set.inclusion hJK x) (Set.inclusion hJK y)),
    @IsAlgebraicExtension (Ex83JK K) t.S _ (garlingFieldToField hField)
      (letI : Field t.S := garlingFieldToField hField
       (ringHomOfInjAddMul (Set.inclusion hJK) (Set.inclusion_injective hJK) hadd hmul).toAlgebra)}

/-- Partial order `(S₁, +₁, .₁) ≤ (S₂, +₂, .₂)` on `ℱ` (**Exercise 8.3 (ii)**, printed p. 75):
`S₁ ⊆ S₂` and `(i, F(S₁), F(S₂))` is an extension, where `i` is the inclusion mapping. -/
def ex83Le {K : Type u} [Field K] (t₁ t₂ : Ex83Triple K) : Prop :=
  ∃ hsub : t₁.S ⊆ t₂.S,
    (∀ x y : t₁.S,
      Set.inclusion hsub (t₁.add x y) = t₂.add (Set.inclusion hsub x) (Set.inclusion hsub y)) ∧
    (∀ x y : t₁.S,
      Set.inclusion hsub (t₁.mul x y) = t₂.mul (Set.inclusion hsub x) (Set.inclusion hsub y))

/-- Base triple `(j(K), +_{j(K)}, ·_{j(K)}) ∈ ℱ`, witnessing `ℱ.Nonempty` in **Exercise 8.3 (ii)**. -/
noncomputable def ex83BaseTriple (K : Type u) [Field K] : Ex83Triple K where
  S := Ex83JK K
  add := (· + ·)
  mul := (· * ·)

theorem ex83BaseTriple_mem (K : Type u) [Field K] : ex83BaseTriple K ∈ Ex83F K := by
  refine ⟨Set.Subset.refl _, Field.isGarlingField (Ex83JK K), fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  let hField := Field.isGarlingField (Ex83JK K)
  let _ : Field (ex83BaseTriple K).S := garlingFieldToField hField
  let iHom : Ex83JK K →+* (ex83BaseTriple K).S :=
    ringHomOfInjAddMul (Set.inclusion (Set.Subset.refl _))
      (Set.inclusion_injective (Set.Subset.refl _)) (fun _ _ => rfl) (fun _ _ => rfl)
  let _ : Algebra (Ex83JK K) (ex83BaseTriple K).S := iHom.toAlgebra
  intro x
  let x₀ : Ex83JK K := x
  refine ⟨Polynomial.X - Polynomial.C x₀, Polynomial.X_sub_C_ne_zero x₀, ?_⟩
  change Polynomial.eval₂ iHom (iHom x₀) (Polynomial.X - Polynomial.C x₀) = 0
  rw [Polynomial.eval₂_at_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, map_zero]

/-- **Exercise 8.3 (ii)** (§8.2, printed p. 75 / PDF p. 83):
`ex83Le` is a partial order on `ℱ` (`IsGarlingPartialOrder`), and `(ℱ, ≤)` has a maximal element
(proved directly via Chapter 2's `zorn_lemma_set`). -/
theorem exercise_8_3_ii (K : Type u) [Field K] :
    IsGarlingPartialOrder (Ex83F K) ex83Le ∧
    ∃ m : Ex83Triple K, IsGarlingMaximal (Ex83F K) ex83Le m := by
  classical
  have hpo : IsGarlingPartialOrder (Ex83F K) ex83Le := by
    refine ⟨fun t _ => ⟨Set.Subset.refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
      fun {t₁ t₂ t₃} _ _ _ ⟨h12, ha12, hm12⟩ ⟨h23, ha23, hm23⟩ =>
        ⟨h12.trans h23,
         fun x y => by
           have h := ha23 (Set.inclusion h12 x) (Set.inclusion h12 y)
           simpa [Set.inclusion_inclusion] using (congrArg (Set.inclusion h23) (ha12 x y)).trans h,
         fun x y => by
           have h := hm23 (Set.inclusion h12 x) (Set.inclusion h12 y)
           simpa [Set.inclusion_inclusion] using (congrArg (Set.inclusion h23) (hm12 x y)).trans h⟩,
      fun {t₁ t₂} _ _ ⟨h12, ha12, hm12⟩ ⟨h21, _, _⟩ => ?_⟩
    have hS : t₁.S = t₂.S := Set.Subset.antisymm h12 h21
    cases t₁ with
    | mk S₁ add₁ mul₁ =>
      cases t₂ with
      | mk S₂ add₂ mul₂ =>
        dsimp at hS
        subst hS
        have hadd_eq : add₁ = add₂ := funext fun x => funext fun y => ha12 x y
        have hmul_eq : mul₁ = mul₂ := funext fun x => funext fun y => hm12 x y
        rw [hadd_eq, hmul_eq]
  have hchains : ∀ C : Set (Ex83Triple K), IsGarlingChain (Ex83F K) ex83Le C →
      ∃ ub : Ex83Triple K, IsGarlingUpperBound (Ex83F K) ex83Le C ub := by
    rintro C ⟨hCF, ⟨t₀, ht₀C⟩, hCtot⟩
    let S₀ : Set (Set (Ex82U K)) := {A | ∃ t ∈ C, A ∈ t.S}
    -- Helper: any two elements of `S₀` lie in a common `t ∈ C`.
    have hex_common2 : ∀ x y : S₀, ∃ t ∈ C, x.1 ∈ t.S ∧ y.1 ∈ t.S := by
      intro x y
      obtain ⟨t₁, ht₁C, hx₁⟩ := x.2
      obtain ⟨t₂, ht₂C, hy₂⟩ := y.2
      rcases hCtot t₁ ht₁C t₂ ht₂C with ⟨h12, _, _⟩ | ⟨h21, _, _⟩
      · exact ⟨t₂, ht₂C, h12 hx₁, hy₂⟩
      · exact ⟨t₁, ht₁C, hx₁, h21 hy₂⟩
    have hex_common3 : ∀ x y z : S₀, ∃ t ∈ C, x.1 ∈ t.S ∧ y.1 ∈ t.S ∧ z.1 ∈ t.S := by
      intro x y z
      obtain ⟨t₁, ht₁C, hx₁, hy₁⟩ := hex_common2 x y
      obtain ⟨t₂, ht₂C, hz₂⟩ := z.2
      rcases hCtot t₁ ht₁C t₂ ht₂C with ⟨h12, _, _⟩ | ⟨h21, _, _⟩
      · exact ⟨t₂, ht₂C, h12 hx₁, h12 hy₁, hz₂⟩
      · exact ⟨t₁, ht₁C, hx₁, hy₁, h21 hz₂⟩
    let add₀ : S₀ → S₀ → S₀ := fun x y =>
      let tc := (hex_common2 x y).choose
      let htc := (hex_common2 x y).choose_spec
      ⟨(tc.add ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩).1, tc, htc.1, (tc.add _ _).2⟩
    let mul₀ : S₀ → S₀ → S₀ := fun x y =>
      let tc := (hex_common2 x y).choose
      let htc := (hex_common2 x y).choose_spec
      ⟨(tc.mul ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩).1, tc, htc.1, (tc.mul _ _).2⟩
    let ub : Ex83Triple K := ⟨S₀, add₀, mul₀⟩
    have hadd₀_agrees : ∀ (t : Ex83Triple K) (htC : t ∈ C) (x y : t.S),
        add₀ ⟨x.1, t, htC, x.2⟩ ⟨y.1, t, htC, y.2⟩ =
          ⟨(t.add x y).1, t, htC, (t.add x y).2⟩ := by
      intro t htC x y
      let x₀ : S₀ := ⟨x.1, t, htC, x.2⟩
      let y₀ : S₀ := ⟨y.1, t, htC, y.2⟩
      let tc := (hex_common2 x₀ y₀).choose
      have htc := (hex_common2 x₀ y₀).choose_spec
      apply Subtype.ext
      change (tc.add ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩).1 = (t.add x y).1
      rcases hCtot t htC tc htc.1 with ⟨_, hadd_sub, _⟩ | ⟨_, hadd_sub, _⟩
      · exact (congrArg Subtype.val (hadd_sub x y)).symm
      · exact congrArg Subtype.val (hadd_sub ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩)
    have hmul₀_agrees : ∀ (t : Ex83Triple K) (htC : t ∈ C) (x y : t.S),
        mul₀ ⟨x.1, t, htC, x.2⟩ ⟨y.1, t, htC, y.2⟩ =
          ⟨(t.mul x y).1, t, htC, (t.mul x y).2⟩ := by
      intro t htC x y
      let x₀ : S₀ := ⟨x.1, t, htC, x.2⟩
      let y₀ : S₀ := ⟨y.1, t, htC, y.2⟩
      let tc := (hex_common2 x₀ y₀).choose
      have htc := (hex_common2 x₀ y₀).choose_spec
      apply Subtype.ext
      change (tc.mul ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩).1 = (t.mul x y).1
      rcases hCtot t htC tc htc.1 with ⟨_, _, hmul_sub⟩ | ⟨_, _, hmul_sub⟩
      · exact (congrArg Subtype.val (hmul_sub x y)).symm
      · exact congrArg Subtype.val (hmul_sub ⟨x.1, htc.2.1⟩ ⟨y.1, htc.2.2⟩)
    have hub_le : ∀ t ∈ C, ex83Le t ub := by
      intro t htC
      refine ⟨fun A hA => ⟨t, htC, hA⟩, fun x y => (hadd₀_agrees t htC x y).symm,
        fun x y => (hmul₀_agrees t htC x y).symm⟩
    -- Prove `ub ∈ Ex83F K`:
    obtain ⟨hJK₀, hField₀, haddJK₀, hmulJK₀, _⟩ := hCF ht₀C
    have hJK_ub : Ex83JK K ⊆ S₀ := fun A hA => ⟨t₀, ht₀C, hJK₀ hA⟩
    -- `0` and `1` of `j(K)` sit inside every `t ∈ C` as its neutral elements.
    let zJK : Ex83JK K := 0
    let oJK : Ex83JK K := 1
    let zero₀ : S₀ := Set.inclusion hJK_ub zJK
    let one₀ : S₀ := Set.inclusion hJK_ub oJK
    have ht_zero_one : ∀ t ∈ C, ∀ (hJK_t : Ex83JK K ⊆ t.S) (hFt : IsGarlingField t.S t.add t.mul),
        (∀ x y : Ex83JK K,
          Set.inclusion hJK_t (x + y) = t.add (Set.inclusion hJK_t x) (Set.inclusion hJK_t y)) →
        (∀ x y : Ex83JK K,
          Set.inclusion hJK_t (x * y) = t.mul (Set.inclusion hJK_t x) (Set.inclusion hJK_t y)) →
        letI : Field t.S := garlingFieldToField hFt
        Set.inclusion hJK_t zJK = 0 ∧ Set.inclusion hJK_t oJK = 1 := by
      intro t _ hJK_t hFt haJK hmJK
      let _ : Field t.S := garlingFieldToField hFt
      let iHom := ringHomOfInjAddMul (Set.inclusion hJK_t) (Set.inclusion_injective hJK_t) haJK hmJK
      exact ⟨iHom.map_zero, iHom.map_one⟩
    have hField_ub : IsGarlingField S₀ add₀ mul₀ := by
      refine ⟨zero₀, one₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h01
        exact zero_ne_one (Set.inclusion_injective hJK_ub h01)
      · intro x y z
        obtain ⟨t, htC, hxt, hyt, hzt⟩ := hex_common3 x y z
        obtain ⟨_, hFt, _, _, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        let zt : t.S := ⟨z.1, hzt⟩
        have hyz := hadd₀_agrees t htC yt zt
        have hxy := hadd₀_agrees t htC xt yt
        change add₀ ⟨xt.1, t, htC, xt.2⟩ (add₀ ⟨yt.1, t, htC, yt.2⟩ ⟨zt.1, t, htC, zt.2⟩) =
          add₀ (add₀ ⟨xt.1, t, htC, xt.2⟩ ⟨yt.1, t, htC, yt.2⟩) ⟨zt.1, t, htC, zt.2⟩
        rw [hyz, hxy, hadd₀_agrees t htC xt (t.add yt zt), hadd₀_agrees t htC (t.add xt yt) zt]
        exact Subtype.ext (congrArg (Subtype.val : t.S → _) (add_assoc xt yt zt).symm)
      · intro x y
        obtain ⟨t, htC, hxt, hyt⟩ := hex_common2 x y
        obtain ⟨_, hFt, _, _, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        change add₀ ⟨xt.1, t, htC, xt.2⟩ ⟨yt.1, t, htC, yt.2⟩ =
          add₀ ⟨yt.1, t, htC, yt.2⟩ ⟨xt.1, t, htC, xt.2⟩
        rw [hadd₀_agrees t htC xt yt, hadd₀_agrees t htC yt xt]
        exact Subtype.ext (congrArg (Subtype.val : t.S → _) (add_comm xt yt))
      · intro x
        obtain ⟨t, htC, hxt⟩ := x.2
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨hz0, _⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        let zt : t.S := Set.inclusion hJK_t zJK
        have hzt : zt = 0 := hz0
        have h1 : add₀ zero₀ x = ⟨(t.add zt xt).1, t, htC, (t.add zt xt).2⟩ :=
          hadd₀_agrees t htC zt xt
        have h2 : add₀ x zero₀ = ⟨(t.add xt zt).1, t, htC, (t.add xt zt).2⟩ :=
          hadd₀_agrees t htC xt zt
        refine ⟨h1.trans (Subtype.ext ?_), h2.trans (Subtype.ext ?_)⟩
        · change (zt + xt).1 = x.1
          rw [hzt, zero_add]
        · change (xt + zt).1 = x.1
          rw [hzt, add_zero]
      · intro x
        obtain ⟨t, htC, hxt⟩ := x.2
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨hz0, _⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        let nxt : t.S := -xt
        refine ⟨⟨nxt.1, t, htC, nxt.2⟩, ?_, ?_⟩
        · rw [show x = ⟨xt.1, t, htC, xt.2⟩ from rfl, hadd₀_agrees t htC xt nxt]
          apply Subtype.ext
          change (xt + -xt).1 = zJK.1
          rw [add_neg_cancel, ← hz0]
        · rw [show x = ⟨xt.1, t, htC, xt.2⟩ from rfl, hadd₀_agrees t htC nxt xt]
          apply Subtype.ext
          change (-xt + xt).1 = zJK.1
          rw [neg_add_cancel, ← hz0]
      · intro x
        obtain ⟨t, htC, hxt⟩ := x.2
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨hz0, _⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        let zt : t.S := Set.inclusion hJK_t zJK
        have hzt : zt = 0 := hz0
        refine ⟨(hmul₀_agrees t htC zt xt).trans (Subtype.ext ?_),
          (hmul₀_agrees t htC xt zt).trans (Subtype.ext ?_)⟩
        · change (zt * xt).1 = zJK.1
          rw [hzt, zero_mul, ← hz0]
        · change (xt * zt).1 = zJK.1
          rw [hzt, mul_zero, ← hz0]
      · intro x y hx0 hy0 hmul_eq
        obtain ⟨t, htC, hxt, hyt⟩ := hex_common2 x y
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨hz0, _⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        have hxt0 : xt ≠ 0 := fun h => hx0 (Subtype.ext (by
          change x.1 = zJK.1
          exact congrArg Subtype.val (h.trans hz0.symm)))
        have hyt0 : yt ≠ 0 := fun h => hy0 (Subtype.ext (by
          change y.1 = zJK.1
          exact congrArg Subtype.val (h.trans hz0.symm)))
        have hm := (hmul₀_agrees t htC xt yt).symm.trans hmul_eq
        have hval : (xt * yt).1 = (0 : t.S).1 :=
          (congrArg (Subtype.val : S₀ → _) hm).trans (congrArg (Subtype.val : t.S → _) hz0)
        exact mul_ne_zero hxt0 hyt0 (Subtype.ext hval)
      · intro x y z _ _ _
        obtain ⟨t, htC, hxt, hyt, hzt⟩ := hex_common3 x y z
        obtain ⟨_, hFt, _, _, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        let zt : t.S := ⟨z.1, hzt⟩
        change mul₀ ⟨xt.1, t, htC, xt.2⟩ (mul₀ ⟨yt.1, t, htC, yt.2⟩ ⟨zt.1, t, htC, zt.2⟩) =
          mul₀ (mul₀ ⟨xt.1, t, htC, xt.2⟩ ⟨yt.1, t, htC, yt.2⟩) ⟨zt.1, t, htC, zt.2⟩
        rw [hmul₀_agrees t htC yt zt, hmul₀_agrees t htC xt yt,
          hmul₀_agrees t htC xt (t.mul yt zt), hmul₀_agrees t htC (t.mul xt yt) zt]
        exact Subtype.ext (congrArg (Subtype.val : t.S → _) (mul_assoc xt yt zt).symm)
      · intro x y _ _
        obtain ⟨t, htC, hxt, hyt⟩ := hex_common2 x y
        obtain ⟨_, hFt, _, _, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        change mul₀ ⟨xt.1, t, htC, xt.2⟩ ⟨yt.1, t, htC, yt.2⟩ =
          mul₀ ⟨yt.1, t, htC, yt.2⟩ ⟨xt.1, t, htC, xt.2⟩
        rw [hmul₀_agrees t htC xt yt, hmul₀_agrees t htC yt xt]
        exact Subtype.ext (congrArg (Subtype.val : t.S → _) (mul_comm xt yt))
      · intro x _
        obtain ⟨t, htC, hxt⟩ := x.2
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨_, ho1⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        let ot : t.S := Set.inclusion hJK_t oJK
        have hot : ot = 1 := ho1
        refine ⟨(hmul₀_agrees t htC ot xt).trans (Subtype.ext ?_),
          (hmul₀_agrees t htC xt ot).trans (Subtype.ext ?_)⟩
        · change (ot * xt).1 = x.1
          rw [hot, one_mul]
        · change (xt * ot).1 = x.1
          rw [hot, mul_one]
      · intro x hx0
        obtain ⟨t, htC, hxt⟩ := x.2
        obtain ⟨hJK_t, hFt, haJK, hmJK, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        have ⟨hz0, ho1⟩ := ht_zero_one t htC hJK_t hFt haJK hmJK
        let xt : t.S := ⟨x.1, hxt⟩
        have hxt0 : xt ≠ 0 := fun h => hx0 (Subtype.ext (by
          change x.1 = zJK.1
          exact congrArg Subtype.val (h.trans hz0.symm)))
        let ixt : t.S := xt⁻¹
        have hixt0 : (⟨ixt.1, t, htC, ixt.2⟩ : S₀) ≠ zero₀ := by
          intro h
          apply inv_ne_zero hxt0
          apply Subtype.ext
          exact (congrArg (Subtype.val : S₀ → _) h).trans (congrArg (Subtype.val : t.S → _) hz0)
        refine ⟨⟨ixt.1, t, htC, ixt.2⟩, hixt0, ?_, ?_⟩
        · rw [show x = ⟨xt.1, t, htC, xt.2⟩ from rfl, hmul₀_agrees t htC xt ixt]
          apply Subtype.ext
          change (xt * xt⁻¹).1 = oJK.1
          rw [mul_inv_cancel₀ hxt0, ← ho1]
        · rw [show x = ⟨xt.1, t, htC, xt.2⟩ from rfl, hmul₀_agrees t htC ixt xt]
          apply Subtype.ext
          change (xt⁻¹ * xt).1 = oJK.1
          rw [inv_mul_cancel₀ hxt0, ← ho1]
      · intro x y z
        obtain ⟨t, htC, hxt, hyt, hzt⟩ := hex_common3 x y z
        obtain ⟨_, hFt, _, _, _⟩ := hCF htC
        let _ : Field t.S := garlingFieldToField hFt
        let xt : t.S := ⟨x.1, hxt⟩
        let yt : t.S := ⟨y.1, hyt⟩
        let zt : t.S := ⟨z.1, hzt⟩
        change mul₀ ⟨xt.1, t, htC, xt.2⟩ (add₀ ⟨yt.1, t, htC, yt.2⟩ ⟨zt.1, t, htC, zt.2⟩) =
          add₀ (mul₀ ⟨xt.1, t, htC, xt.2⟩ ⟨yt.1, t, htC, yt.2⟩)
            (mul₀ ⟨xt.1, t, htC, xt.2⟩ ⟨zt.1, t, htC, zt.2⟩)
        rw [hadd₀_agrees t htC yt zt, hmul₀_agrees t htC xt (t.add yt zt),
          hmul₀_agrees t htC xt yt, hmul₀_agrees t htC xt zt,
          hadd₀_agrees t htC (t.mul xt yt) (t.mul xt zt)]
        exact Subtype.ext (congrArg (Subtype.val : t.S → _) (mul_add xt yt zt))
    have haJK_ub : ∀ x y : Ex83JK K,
        Set.inclusion hJK_ub (x + y) = add₀ (Set.inclusion hJK_ub x) (Set.inclusion hJK_ub y) := by
      intro x y
      have h1 := hadd₀_agrees t₀ ht₀C (Set.inclusion hJK₀ x) (Set.inclusion hJK₀ y)
      apply Subtype.ext
      exact (congrArg (Subtype.val : t₀.S → _) (haddJK₀ x y)).trans
        (congrArg (Subtype.val : S₀ → _) h1.symm)
    have hmJK_ub : ∀ x y : Ex83JK K,
        Set.inclusion hJK_ub (x * y) = mul₀ (Set.inclusion hJK_ub x) (Set.inclusion hJK_ub y) := by
      intro x y
      have h1 := hmul₀_agrees t₀ ht₀C (Set.inclusion hJK₀ x) (Set.inclusion hJK₀ y)
      apply Subtype.ext
      exact (congrArg (Subtype.val : t₀.S → _) (hmulJK₀ x y)).trans
        (congrArg (Subtype.val : S₀ → _) h1.symm)
    have hub_mem : ub ∈ Ex83F K := by
      refine ⟨hJK_ub, hField_ub, haJK_ub, hmJK_ub, ?_⟩
      let _ : Field S₀ := garlingFieldToField hField_ub
      let iHom_ub : Ex83JK K →+* S₀ :=
        ringHomOfInjAddMul (Set.inclusion hJK_ub) (Set.inclusion_injective hJK_ub) haJK_ub hmJK_ub
      let _ : Algebra (Ex83JK K) S₀ := iHom_ub.toAlgebra
      intro x
      obtain ⟨t, htC, hxt⟩ := x.2
      obtain ⟨hJK_t, hFt, haJK_t, hmJK_t, halg_t⟩ := hCF htC
      let _ : Field t.S := garlingFieldToField hFt
      let iHom_t : Ex83JK K →+* t.S :=
        ringHomOfInjAddMul (Set.inclusion hJK_t) (Set.inclusion_injective hJK_t) haJK_t hmJK_t
      let _ : Algebra (Ex83JK K) t.S := iHom_t.toAlgebra
      obtain ⟨hsub_t, ha_t_ub, hm_t_ub⟩ := hub_le t htC
      let φ_t : t.S →+* S₀ :=
        ringHomOfInjAddMul (Set.inclusion hsub_t) (Set.inclusion_injective hsub_t) ha_t_ub hm_t_ub
      obtain ⟨p, hp0, hpx⟩ := halg_t ⟨x.1, hxt⟩
      refine ⟨p, hp0, ?_⟩
      have hcomm : φ_t.comp iHom_t = iHom_ub := RingHom.ext fun _ => rfl
      change Polynomial.eval₂ iHom_ub (φ_t ⟨x.1, hxt⟩) p = 0
      rw [← hcomm, ← Polynomial.hom_eval₂, show Polynomial.eval₂ iHom_t ⟨x.1, hxt⟩ p = 0 from hpx,
        map_zero]
    exact ⟨ub, hub_mem, hub_le⟩
  exact ⟨hpo, zorn_lemma_set hpo ⟨ex83BaseTriple K, ex83BaseTriple_mem K⟩ hchains⟩

/-- **Exercise 8.3 (iii)** (§8.2, printed p. 75 / PDF p. 83):
*"Use Theorem 7.2 or 7.3 to show that if `(S, +, .)` is a maximal element of `ℱ` then `(j, K, F(S))`
is an algebraic closure for `K`. (Here `j` is considered as a mapping of `K` into `F(S)`.)"*

Proved directly using `Theorem 7.2` (`theorem_7_2`) and `Exercise 8.2 (ii)` (`exercise_8_2_ii`). -/
theorem exercise_8_3_iii {K : Type u} [Field K] {t : Ex83Triple K}
    (hmax : IsGarlingMaximal (Ex83F K) ex83Le t) :
    ∃ (_ : Field t.S) (jHom : K →+* t.S),
      (∀ x y : t.S, @HAdd.hAdd t.S t.S t.S instHAdd x y = t.add x y) ∧
      (∀ x y : t.S, @HMul.hMul t.S t.S t.S instHMul x y = t.mul x y) ∧
      (∀ α : K, (jHom α : Set (Ex82U K)) = ex83J K α) ∧
      IsGarlingAlgebraicClosureHom jHom := by
  classical
  obtain ⟨⟨hJK, hField, haJK, hmJK, halg_JK⟩, hmax_prop⟩ := hmax
  let instF : Field t.S := garlingFieldToField hField
  let _ : Field t.S := instF
  let iHom : Ex83JK K →+* t.S :=
    ringHomOfInjAddMul (Set.inclusion hJK) (Set.inclusion_injective hJK) haJK hmJK
  let jHom : K →+* t.S := iHom.comp (ex83JRingEquiv K).toRingHom
  let _ : Algebra K t.S := jHom.toAlgebra
  have halg_K : IsAlgebraicExtension K t.S := by
    let _ : Algebra (Ex83JK K) t.S := iHom.toAlgebra
    intro x
    obtain ⟨p, hp0, hpx⟩ := halg_JK x
    let pK : K[X] := p.map (ex83JRingEquiv K).symm.toRingHom
    have hpK0 : pK ≠ 0 := (Polynomial.map_ne_zero_iff (ex83JRingEquiv K).symm.injective).mpr hp0
    refine ⟨pK, hpK0, ?_⟩
    have hmap : pK.map (ex83JRingEquiv K).toRingHom = p := by
      ext n
      simp [pK]
    rw [Polynomial.aeval_def, show algebraMap K t.S = iHom.comp (ex83JRingEquiv K).toRingHom from rfl,
      ← Polynomial.eval₂_map, hmap]
    exact hpx
  -- Show `F(S)` is algebraically closed: if `f ∈ F(S)[x]` is irreducible, Theorem 7.2 + Ex. 8.2 (ii)
  -- embed a simple root extension `M` into `P(U)` extending `F(S)`, which maximality forces equal
  -- to `F(S)`, giving a root of `f` in `F(S)`.
  have hclosed_S : IsGarlingAlgebraicallyClosed t.S := by
    rw [isGarlingAlgebraicallyClosed_iff]
    refine IsAlgClosed.of_exists_root t.S fun f _ hfirr => ?_
    -- By Theorem 7.2 (`theorem_7_2`), construct `M : F(S)` with root `α ∈ M` of `f`.
    obtain ⟨M, instFieldM, instAlgSM, α, _, halgSM, _, _, hfα⟩ := theorem_7_2 hfirr rfl
    let _ : Field M := instFieldM
    let _ : Algebra t.S M := instAlgSM
    let extKS : FieldExtensionTriple K t.S := FieldExtensionTriple.ofRingHom jHom
    let extSM : FieldExtensionTriple t.S M := FieldExtensionTriple.ofRingHom (algebraMap t.S M)
    -- By Exercise 8.2 (ii), extend `Subtype.val : F(S) ↪ P(U)` across `l : F(S) →+* M`.
    obtain ⟨g, hg_inj, hg_comp⟩ := exercise_8_2_ii extKS extSM halg_K halgSM Subtype.val_injective
    let S' : Set (Set (Ex82U K)) := Set.range g
    let eM : M ≃ S' := Equiv.ofInjective g hg_inj
    let addS' : S' → S' → S' := @HAdd.hAdd S' S' S' (@instHAdd S' eM.symm.field.toAdd)
    let mulS' : S' → S' → S' := @HMul.hMul S' S' S' (@instHMul S' eM.symm.field.toMul)
    let t' : Ex83Triple K := ⟨S', addS', mulS'⟩
    have heM_add : ∀ a b : M, eM (a + b) = addS' (eM a) (eM b) := by
      let _ : Field S' := eM.symm.field
      intro a b
      exact eM.symm.ringEquiv.symm.map_add a b
    have heM_mul : ∀ a b : M, eM (a * b) = mulS' (eM a) (eM b) := by
      let _ : Field S' := eM.symm.field
      intro a b
      exact eM.symm.ringEquiv.symm.map_mul a b
    have hsub_SS' : t.S ⊆ S' := by
      intro A hA
      have hEq : A = g (algebraMap t.S M ⟨A, hA⟩) := congrFun hg_comp ⟨A, hA⟩
      exact hEq ▸ ⟨algebraMap t.S M ⟨A, hA⟩, rfl⟩
    have hincl_eq : ∀ x : t.S, Set.inclusion hsub_SS' x = eM (algebraMap t.S M x) := by
      intro x
      apply Subtype.ext
      exact congrFun hg_comp x
    have ha_SS' : ∀ x y : t.S,
        Set.inclusion hsub_SS' (t.add x y) =
          t'.add (Set.inclusion hsub_SS' x) (Set.inclusion hsub_SS' y) := by
      intro x y
      rw [hincl_eq, hincl_eq, hincl_eq]
      exact (congrArg eM ((algebraMap t.S M).map_add x y)).trans (heM_add _ _)
    have hm_SS' : ∀ x y : t.S,
        Set.inclusion hsub_SS' (t.mul x y) =
          t'.mul (Set.inclusion hsub_SS' x) (Set.inclusion hsub_SS' y) := by
      intro x y
      rw [hincl_eq, hincl_eq, hincl_eq]
      exact (congrArg eM ((algebraMap t.S M).map_mul x y)).trans (heM_mul _ _)
    have hle_tt' : ex83Le t t' := ⟨hsub_SS', ha_SS', hm_SS'⟩
    have ht'_mem : t' ∈ Ex83F K := by
      have hJK' : Ex83JK K ⊆ S' := hJK.trans hsub_SS'
      have hField' : IsGarlingField t'.S t'.add t'.mul :=
        @Field.isGarlingField S' eM.symm.field
      have haJK' : ∀ x y : Ex83JK K,
          Set.inclusion hJK' (x + y) = t'.add (Set.inclusion hJK' x) (Set.inclusion hJK' y) := by
        intro x y
        have h1 : Set.inclusion hJK' (x + y) =
            Set.inclusion hsub_SS' (Set.inclusion hJK (x + y)) := rfl
        rw [h1, haJK x y, ha_SS']
      have hmJK' : ∀ x y : Ex83JK K,
          Set.inclusion hJK' (x * y) = t'.mul (Set.inclusion hJK' x) (Set.inclusion hJK' y) := by
        intro x y
        have h1 : Set.inclusion hJK' (x * y) =
            Set.inclusion hsub_SS' (Set.inclusion hJK (x * y)) := rfl
        rw [h1, hmJK x y, hm_SS']
      refine ⟨hJK', hField', ?_⟩
      let _ : Field t'.S := garlingFieldToField hField'
      refine ⟨haJK', hmJK', ?_⟩
      let iHom' : Ex83JK K →+* t'.S :=
        ringHomOfInjAddMul (Set.inclusion hJK') (Set.inclusion_injective hJK') haJK' hmJK'
      let _ : Algebra (Ex83JK K) t'.S := iHom'.toAlgebra
      let φM : M →+* t'.S :=
        ringHomOfInjAddMul eM eM.injective heM_add heM_mul
      let _ : Algebra (Ex83JK K) t.S := iHom.toAlgebra
      let lJK : Ex83JK K →+* M := (algebraMap t.S M).comp iHom
      have halg_JK_M :
          (letI : Algebra (Ex83JK K) M := lJK.toAlgebra; IsAlgebraicExtension (Ex83JK K) M) :=
        theorem_4_7_triple (FieldExtensionTriple.ofRingHom iHom) extSM halgSM halg_JK
      intro z
      obtain ⟨m, rfl⟩ := eM.surjective z
      obtain ⟨p, hp0, hpm⟩ := halg_JK_M m
      refine ⟨p, hp0, ?_⟩
      have hcomm : φM.comp lJK = iHom' :=
        RingHom.ext fun a => Subtype.ext (by
          change (eM (algebraMap t.S M (Set.inclusion hJK a))).1 = (Set.inclusion hJK' a).1
          rw [← hincl_eq (Set.inclusion hJK a)])
      change Polynomial.eval₂ iHom' (φM m) p = 0
      rw [← hcomm, ← Polynomial.hom_eval₂]
      rw [show Polynomial.eval₂ lJK m p = 0 from hpm, map_zero]
    have htt'_eq : t = t' := hmax_prop t' ht'_mem hle_tt'
    have hS_eq : t.S = S' := congrArg Ex83Triple.S htt'_eq
    have hα_in_S : g α ∈ t.S := hS_eq ▸ ⟨α, rfl⟩
    let β : t.S := ⟨g α, hα_in_S⟩
    have hlβ : algebraMap t.S M β = α := by
      apply hg_inj
      exact (congrFun hg_comp β).symm
    refine ⟨β, ?_⟩
    apply (algebraMap t.S M).injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, hlβ, ← Polynomial.aeval_def, hfα]
  exact ⟨instF, jHom, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, ⟨halg_K, hclosed_S⟩⟩

/-- **Exercise 8.3** (§8.2, printed p. 75 / PDF p. 83):
Combined statement conjoining parts `(i)`, `(ii)`, and `(iii)`. -/
theorem exercise_8_3 (K : Type u) [Field K] :
    (Function.Injective (ex83J K) ∧
      IsGarlingField (Ex83JK K) (· + ·) (· * ·) ∧
      IsRingIsomorphism (ex83JRingEquiv K).toRingHom) ∧
    (IsGarlingPartialOrder (Ex83F K) ex83Le ∧
      ∃ m : Ex83Triple K, IsGarlingMaximal (Ex83F K) ex83Le m) ∧
    (∀ t : Ex83Triple K, IsGarlingMaximal (Ex83F K) ex83Le t →
      ∃ (_ : Field t.S) (jHom : K →+* t.S),
        (∀ α : K, (jHom α : Set (Ex82U K)) = ex83J K α) ∧
        IsGarlingAlgebraicClosureHom jHom) := by
  refine ⟨⟨ex83J_injective K, Field.isGarlingField (Ex83JK K), (ex83JRingEquiv K).bijective⟩,
    exercise_8_3_ii K, fun t hmax => ?_⟩
  obtain ⟨instF, jHom, _, _, hj, hcl⟩ := exercise_8_3_iii hmax
  exact ⟨instF, jHom, hj, hcl⟩

/-! ## §8.3 The uniqueness of an algebraic closure (printed pp. 75–76, PDF pp. 83–84) -/

/-- **Theorem 8.3** (§8.3, printed p. 75 / PDF p. 83; proof pp. 75–76 / PDF pp. 83–84):
*"Suppose that `i : K₁ → K₂` is a monomorphism, that `L : K₁` is algebraic and that `K₂` is
algebraically closed. Then there exists a monomorphism `j : L → K₂` such that `j|_{K₁} = i`."*

Proved across arbitrary universes `{K₁ : Type u} {K₂ : Type v} {L : Type w}` following Garling's
printed argument via Chapter 2's `zorn_lemma_set` and Chapter 7's `Theorem 7.4`. -/
theorem theorem_8_3 {K₁ : Type u} {K₂ : Type v} {L : Type w}
    [Field K₁] [Field K₂] [Field L] [Algebra K₁ L]
    {i : K₁ →+* K₂} (_hi : IsRingMonomorphism i)
    (halg : IsAlgebraicExtension K₁ L)
    (hclosed : IsGarlingAlgebraicallyClosed K₂) :
    ∃ j : L →+* K₂, IsRingMonomorphism j ∧ ∀ k : K₁, j (algebraMap K₁ L k) = i k := by
  classical
  -- Poset `S` of pairs `(M, θ)` where `M : IntermediateField K₁ L` and `θ : L → K₂` (normalized to
  -- `0` outside `M`) restricts to a monomorphism `M →+* K₂` extending `i`.
  let S : Set (IntermediateField K₁ L × (L → K₂)) :=
    {p | (∀ x : L, x ∉ p.1 → p.2 x = 0) ∧
      (∀ x ∈ p.1, ∀ y ∈ p.1, p.2 (x + y) = p.2 x + p.2 y) ∧
      (∀ x ∈ p.1, ∀ y ∈ p.1, p.2 (x * y) = p.2 x * p.2 y) ∧
      p.2 1 = 1 ∧
      ∀ k : K₁, p.2 (algebraMap K₁ L k) = i k}
  let leS : (IntermediateField K₁ L × (L → K₂)) → (IntermediateField K₁ L × (L → K₂)) → Prop :=
    fun p₁ p₂ => p₁.1 ≤ p₂.1 ∧ ∀ x ∈ p₁.1, p₂.2 x = p₁.2 x
  have hpo : IsGarlingPartialOrder S leS := by
    refine ⟨fun _ _ => ⟨le_rfl, fun _ _ => rfl⟩,
      fun {_ _ _} _ _ _ h12 h23 =>
        ⟨h12.1.trans h23.1, fun x hx => (h23.2 x (h12.1 hx)).trans (h12.2 x hx)⟩,
      fun {p₁ p₂} hp₁ hp₂ h12 h21 => ?_⟩
    have hM : p₁.1 = p₂.1 := le_antisymm h12.1 h21.1
    refine Prod.ext hM (funext fun x => ?_)
    by_cases hx : x ∈ p₁.1
    · exact (h12.2 x hx).symm
    · rw [hp₁.1 x hx, hp₂.1 x (hM ▸ hx)]
  -- Base element `(⊥, θ₀) ∈ S` corresponding to `(K₁, i)`.
  let θ₀ : L → K₂ := fun x =>
    if hx : x ∈ (⊥ : IntermediateField K₁ L) then
      i (IntermediateField.mem_bot.mp hx).choose
    else 0
  have hθ₀_algebraMap : ∀ k : K₁, θ₀ (algebraMap K₁ L k) = i k := by
    intro k
    have hmem : algebraMap K₁ L k ∈ (⊥ : IntermediateField K₁ L) :=
      IntermediateField.mem_bot.mpr ⟨k, rfl⟩
    dsimp [θ₀]
    simp only [hmem, ↓reduceDIte]
    have hck := (IntermediateField.mem_bot.mp hmem).choose_spec
    exact congrArg i ((algebraMap K₁ L).injective hck)
  have hp₀ : ((⊥ : IntermediateField K₁ L), θ₀) ∈ S := by
    refine ⟨fun x hx => by simp [θ₀, hx], ?_, ?_, ?_, hθ₀_algebraMap⟩
    · intro x hx y hy
      dsimp only
      obtain ⟨kx, rfl⟩ := IntermediateField.mem_bot.mp hx
      obtain ⟨ky, rfl⟩ := IntermediateField.mem_bot.mp hy
      rw [← map_add, hθ₀_algebraMap, hθ₀_algebraMap, hθ₀_algebraMap, map_add]
    · intro x hx y hy
      dsimp only
      obtain ⟨kx, rfl⟩ := IntermediateField.mem_bot.mp hx
      obtain ⟨ky, rfl⟩ := IntermediateField.mem_bot.mp hy
      rw [← map_mul, hθ₀_algebraMap, hθ₀_algebraMap, hθ₀_algebraMap, map_mul]
    · dsimp only
      rw [← (algebraMap K₁ L).map_one, hθ₀_algebraMap, map_one]
  have hchains : ∀ C : Set (IntermediateField K₁ L × (L → K₂)), IsGarlingChain S leS C →
      ∃ ub, IsGarlingUpperBound S leS C ub := by
    rintro C ⟨hCS, ⟨p_init, hp_init⟩, hCtot⟩
    let N : IntermediateField K₁ L :=
      { carrier := {x : L | ∃ p ∈ C, x ∈ p.1}
        add_mem' := by
          rintro x y ⟨p₁, hp₁C, hx₁⟩ ⟨p₂, hp₂C, hy₂⟩
          rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
          · exact ⟨p₂, hp₂C, p₂.1.add_mem (h12.1 hx₁) hy₂⟩
          · exact ⟨p₁, hp₁C, p₁.1.add_mem hx₁ (h21.1 hy₂)⟩
        mul_mem' := by
          rintro x y ⟨p₁, hp₁C, hx₁⟩ ⟨p₂, hp₂C, hy₂⟩
          rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
          · exact ⟨p₂, hp₂C, p₂.1.mul_mem (h12.1 hx₁) hy₂⟩
          · exact ⟨p₁, hp₁C, p₁.1.mul_mem hx₁ (h21.1 hy₂)⟩
        algebraMap_mem' := fun k => ⟨p_init, hp_init, p_init.1.algebraMap_mem k⟩
        inv_mem' := by
          rintro x ⟨p, hpC, hx⟩
          exact ⟨p, hpC, p.1.inv_mem hx⟩ }
    let ϕ : L → K₂ := fun x => if hx : x ∈ N then hx.choose.2 x else 0
    have hϕ_agrees : ∀ p ∈ C, ∀ x ∈ p.1, ϕ x = p.2 x := by
      intro p hpC x hxp
      have hxN : x ∈ N := ⟨p, hpC, hxp⟩
      dsimp [ϕ]
      simp only [hxN, ↓reduceDIte]
      let q := hxN.choose
      have hqC : q ∈ C := hxN.choose_spec.1
      have hxq : x ∈ q.1 := hxN.choose_spec.2
      rcases hCtot p hpC q hqC with hpq | hqp
      · exact hpq.2 x hxp
      · exact (hqp.2 x hxq).symm
    have hub_S : (N, ϕ) ∈ S := by
      refine ⟨fun x hx => by simp [ϕ, hx], ?_, ?_, ?_, ?_⟩
      · rintro x ⟨p₁, hp₁C, hx₁⟩ y ⟨p₂, hp₂C, hy₂⟩
        dsimp only
        rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
        · rw [hϕ_agrees p₂ hp₂C (x + y) (p₂.1.add_mem (h12.1 hx₁) hy₂),
            hϕ_agrees p₂ hp₂C x (h12.1 hx₁), hϕ_agrees p₂ hp₂C y hy₂]
          exact (hCS hp₂C).2.1 x (h12.1 hx₁) y hy₂
        · rw [hϕ_agrees p₁ hp₁C (x + y) (p₁.1.add_mem hx₁ (h21.1 hy₂)),
            hϕ_agrees p₁ hp₁C x hx₁, hϕ_agrees p₁ hp₁C y (h21.1 hy₂)]
          exact (hCS hp₁C).2.1 x hx₁ y (h21.1 hy₂)
      · rintro x ⟨p₁, hp₁C, hx₁⟩ y ⟨p₂, hp₂C, hy₂⟩
        dsimp only
        rcases hCtot p₁ hp₁C p₂ hp₂C with h12 | h21
        · rw [hϕ_agrees p₂ hp₂C (x * y) (p₂.1.mul_mem (h12.1 hx₁) hy₂),
            hϕ_agrees p₂ hp₂C x (h12.1 hx₁), hϕ_agrees p₂ hp₂C y hy₂]
          exact (hCS hp₂C).2.2.1 x (h12.1 hx₁) y hy₂
        · rw [hϕ_agrees p₁ hp₁C (x * y) (p₁.1.mul_mem hx₁ (h21.1 hy₂)),
            hϕ_agrees p₁ hp₁C x hx₁, hϕ_agrees p₁ hp₁C y (h21.1 hy₂)]
          exact (hCS hp₁C).2.2.1 x hx₁ y (h21.1 hy₂)
      · dsimp only
        rw [hϕ_agrees p_init hp_init 1 p_init.1.one_mem]
        exact (hCS hp_init).2.2.2.1
      · intro k
        dsimp only
        rw [hϕ_agrees p_init hp_init (algebraMap K₁ L k) (p_init.1.algebraMap_mem k)]
        exact (hCS hp_init).2.2.2.2 k
    exact ⟨(N, ϕ), hub_S, fun p hpC => ⟨fun x hx => ⟨p, hpC, hx⟩, fun x hx => hϕ_agrees p hpC x hx⟩⟩
  obtain ⟨⟨M, θ⟩, ⟨hOut, hAdd, hMul, hOne, hExtK₁⟩, hMax⟩ :=
    zorn_lemma_set hpo ⟨(⊥, θ₀), hp₀⟩ hchains
  let θHom : M →+* K₂ :=
    { toFun := fun x => θ x.1
      map_zero' := by
        have h0 : θ 0 + θ 0 = θ 0 + 0 := by rw [← hAdd 0 M.zero_mem 0 M.zero_mem, add_zero, add_zero]
        exact add_left_cancel h0
      map_one' := hOne
      map_add' := fun x y => hAdd x.1 x.2 y.1 y.2
      map_mul' := fun x y => hMul x.1 x.2 y.1 y.2 }
  have hM_top : M = ⊤ := by
    by_contra hne
    have hex_α : ∃ α : L, α ∉ M := by
      by_contra hall
      push Not at hall
      apply hne
      ext x
      simp [hall x]
    obtain ⟨α, hαM_not⟩ := hex_α
    -- `α` is algebraic over `K₁`, hence algebraic over `M`.
    have hαM_alg : IsGarlingAlgebraic M α := by
      obtain ⟨p, hp0, hpα⟩ := halg α
      refine ⟨p.map (algebraMap K₁ M),
        (Polynomial.map_ne_zero_iff (algebraMap K₁ M).injective).mpr hp0, ?_⟩
      rw [Polynomial.aeval_map_algebraMap]
      exact hpα
    have hαM_int : IsIntegral M α := (isGarlingAlgebraic_iff_isIntegral M α).mp hαM_alg
    let m : M[X] := minpoly M α
    have hm_irr : Irreducible m := minpoly.irreducible hαM_int
    have hm_pos : 0 < m.natDegree := minpoly.natDegree_pos hαM_int
    -- `θ(m)` splits over `K₂`, since `K₂` is algebraically closed.
    obtain ⟨r, c, β, hexp⟩ := hclosed (garlingMapPoly θHom m)
    have hθm_ne0 : garlingMapPoly θHom m ≠ 0 :=
      (Polynomial.map_ne_zero_iff θHom.injective).mpr hm_irr.ne_zero
    obtain ⟨_, _, hr_eq, hroots⟩ := garlingSplitsExplicit_props hθm_ne0 hexp
    have hr_deg : r = m.natDegree := by
      have hd : (garlingMapPoly θHom m).natDegree = m.natDegree :=
        Polynomial.natDegree_map_eq_of_injective θHom.injective m
      simpa [garlingDegree, hd] using hr_eq
    have hr_pos : 0 < r := hr_deg ▸ hm_pos
    let β₁ : K₂ := β ⟨0, hr_pos⟩
    have hβ₁_eval : (garlingMapPoly θHom m).eval β₁ = 0 := by
      have hmem : β₁ ∈ (garlingMapPoly θHom m).rootSet K₂ := hroots ▸ ⟨⟨0, hr_pos⟩, rfl⟩
      rw [Polynomial.mem_rootSet] at hmem
      simpa [Polynomial.aeval_def] using hmem.2
    -- By Theorem 7.4 (`theorem_7_4_adjoin`), extend `θHom` to `θ₁ : M(α) →+* K₂`.
    obtain ⟨θ₁, _, _, hθ₁_ext⟩ :=
      (theorem_7_4_adjoin hαM_alg θHom.injective β₁).1.mpr hβ₁_eval
    let Mα : IntermediateField M L := IntermediateField.adjoin M ({α} : Set L)
    let M' : IntermediateField K₁ L := Mα.restrictScalars K₁
    have hMM' : M ≤ M' := fun x hx => Mα.algebraMap_mem ⟨x, hx⟩
    let θ' : L → K₂ := fun x => if hx : x ∈ M' then θ₁ ⟨x, hx⟩ else 0
    have hp' : (M', θ') ∈ S := by
      refine ⟨fun x hx => by simp [θ', hx], ?_, ?_, ?_, ?_⟩
      · intro x hx y hy
        have hxy : x + y ∈ M' := M'.add_mem hx hy
        dsimp [θ']
        simp only [hx, hy, hxy, ↓reduceDIte]
        exact θ₁.map_add ⟨x, hx⟩ ⟨y, hy⟩
      · intro x hx y hy
        have hxy : x * y ∈ M' := M'.mul_mem hx hy
        dsimp [θ']
        simp only [hx, hy, hxy, ↓reduceDIte]
        exact θ₁.map_mul ⟨x, hx⟩ ⟨y, hy⟩
      · have h1M' : (1 : L) ∈ M' := M'.one_mem
        dsimp [θ']
        simp only [h1M', ↓reduceDIte]
        exact θ₁.map_one
      · intro k
        have hkM : algebraMap K₁ L k ∈ M := M.algebraMap_mem k
        have hkM' : algebraMap K₁ L k ∈ M' := hMM' hkM
        dsimp [θ']
        simp only [hkM', ↓reduceDIte]
        exact (hθ₁_ext ⟨algebraMap K₁ L k, hkM⟩).trans (hExtK₁ k)
    have hle' : leS (M, θ) (M', θ') := by
      refine ⟨hMM', fun x hx => ?_⟩
      have hx' : x ∈ M' := hMM' hx
      dsimp [θ']
      simp only [hx', ↓reduceDIte]
      exact hθ₁_ext ⟨x, hx⟩
    have heq := hMax (M', θ') hp' hle'
    have hMeq : M = M' := congrArg Prod.fst heq
    have hαM' : α ∈ M' := IntermediateField.mem_adjoin_simple_self M α
    exact hαM_not (hMeq.symm ▸ hαM')
  let j : L →+* K₂ :=
    { toFun := θ
      map_zero' := by
        have h0M : (0 : L) ∈ M := hM_top ▸ IntermediateField.mem_top
        have h0 : θ 0 + θ 0 = θ 0 + 0 := by rw [← hAdd 0 h0M 0 h0M, add_zero, add_zero]
        exact add_left_cancel h0
      map_one' := hOne
      map_add' := fun x y =>
        hAdd x (hM_top ▸ IntermediateField.mem_top) y (hM_top ▸ IntermediateField.mem_top)
      map_mul' := fun x y =>
        hMul x (hM_top ▸ IntermediateField.mem_top) y (hM_top ▸ IntermediateField.mem_top) }
  exact ⟨j, j.injective, hExtK₁⟩

/-- Extension-triple specialization of **Theorem 8.3** (§8.3, printed p. 75). -/
theorem theorem_8_3_triple {K₁ : Type u} {K₂ : Type v} {L : Type w}
    [Field K₁] [Field K₂] [Field L]
    (ext : FieldExtensionTriple K₁ L) {i : K₁ →+* K₂} (hi : IsRingMonomorphism i)
    (halg : letI : Algebra K₁ L := ext.hom.toAlgebra; IsAlgebraicExtension K₁ L)
    (hclosed : IsGarlingAlgebraicallyClosed K₂) :
    ∃ j : L →+* K₂, IsRingMonomorphism j ∧ j.comp ext.hom = i := by
  let _ : Algebra K₁ L := ext.hom.toAlgebra
  obtain ⟨j, hj_mono, hjk⟩ := theorem_8_3 hi halg hclosed
  exact ⟨j, hj_mono, RingHom.ext hjk⟩

/-- **Theorem 8.4** (§8.3, printed p. 76 / PDF p. 84):
*"Suppose that `(i₁, K, L₁)` and `(i₂, K, L₂)` are two algebraic closures for `K`. Then there exists
an isomorphism `j : L₁ → L₂` such that `i₂ = j i₁`."*

Proved across arbitrary universes `{K : Type u} {L₁ : Type v} {L₂ : Type w}` following Garling's
printed commutative-triangle argument via `Theorem 8.3` and `Theorem 8.1 (iii)`. -/
theorem theorem_8_4 {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂]
    {e₁ : FieldExtensionTriple K L₁} {e₂ : FieldExtensionTriple K L₂}
    (h₁ : IsGarlingAlgebraicClosureTriple e₁)
    (h₂ : IsGarlingAlgebraicClosureTriple e₂) :
    ∃ j : L₁ →+* L₂, IsRingIsomorphism j ∧ e₂.hom = j.comp e₁.hom := by
  -- By Theorem 8.3, extend `i₂ : K →+* L₂` across `(i₁, K, L₁)` to a monomorphism `j : L₁ →+* L₂`.
  obtain ⟨j, hj_mono, hj_comp⟩ := theorem_8_3_triple e₁ e₂.mono h₁.1 h₂.2
  -- Since `(i₂, K, L₂)` is algebraic and `i₂ = j ∘ i₁`, `L₂` is algebraic over `L₁` via `j`.
  let _ : Algebra L₁ L₂ := j.toAlgebra
  have halg_L₁L₂ : IsAlgebraicExtension L₁ L₂ := by
    let _ : Algebra K L₂ := e₂.hom.toAlgebra
    have halg_KL₂ : IsAlgebraicExtension K L₂ := h₂.1
    intro α
    obtain ⟨p, hp0, hpα⟩ := halg_KL₂ α
    refine ⟨p.map e₁.hom, (Polynomial.map_ne_zero_iff e₁.mono).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (j.comp e₁.hom) α p = 0
    rw [hj_comp]
    exact hpα
  -- Since `L₁` is algebraically closed (`h₁.2`), `j` is surjective by Theorem 8.1 (iii).
  have hsurj : Function.Surjective j :=
    (isGarlingAlgebraicallyClosed_surjective_of_algebraic h₁.2 halg_L₁L₂).1
  exact ⟨j, ⟨hj_mono, hsurj⟩, hj_comp.symm⟩

/-- `RingEquiv` formulation of **Theorem 8.4** (§8.3, printed p. 76). -/
theorem theorem_8_4_ringEquiv {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂]
    {e₁ : FieldExtensionTriple K L₁} {e₂ : FieldExtensionTriple K L₂}
    (h₁ : IsGarlingAlgebraicClosureTriple e₁)
    (h₂ : IsGarlingAlgebraicClosureTriple e₂) :
    ∃ j : L₁ ≃+* L₂, ∀ k : K, j (e₁.hom k) = e₂.hom k := by
  obtain ⟨j, hj_bij, hj_comp⟩ := theorem_8_4 h₁ h₂
  exact ⟨RingEquiv.ofBijective j hj_bij, fun k => (RingHom.congr_fun hj_comp k).symm⟩

/-- `[Algebra K L₁] [Algebra K L₂]` `AlgEquiv` formulation of **Theorem 8.4** (§8.3, printed p. 76):
any two algebraic closures of `K` are `K`-isomorphic (`Nonempty (L₁ ≃ₐ[K] L₂)`). -/
theorem theorem_8_4_algEquiv {K : Type u} {L₁ : Type v} {L₂ : Type w}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    (h₁ : IsGarlingAlgebraicClosure K L₁)
    (h₂ : IsGarlingAlgebraicClosure K L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by
  obtain ⟨j, hj_comm⟩ := theorem_8_4_ringEquiv
    (e₁ := FieldExtensionTriple.ofAlgebra K L₁)
    (e₂ := FieldExtensionTriple.ofAlgebra K L₂) h₁ h₂
  exact ⟨AlgEquiv.ofRingEquiv (f := j) hj_comm⟩

/-- Prose notation `K̄ : K` (§8.3, printed p. 76 / PDF p. 84):
*"In future, if `K` is any field, we shall denote by `K̄ : K` any algebraic closure of `K`."*
Canonical representative given by §8.2's explicit Artin quotient field `ArtinAlgClosure K`. -/
abbrev GarlingAlgClosure (K : Type u) [Field K] : Type u :=
  ArtinAlgClosure K

theorem garlingAlgClosure_isGarlingAlgebraicClosure (K : Type u) [Field K] :
    IsGarlingAlgebraicClosure K (GarlingAlgClosure K) :=
  (artinAlgClosure_isGarlingAlgebraicClosure K).1

/-! ### Exercise 8.4 (§8.3, printed p. 76 / PDF p. 84) -/

/-- Exact subfield characterization for **Exercise 8.4** (§8.3, printed p. 76 / PDF p. 84):
a subfield `F : Subfield ℂ` is an algebraic closure of `ℚ` if and only if `F` equals the subfield
`GarlingAlgebraicNumbers` (`= algebraicSubfield ℚ ℂ`) of complex numbers algebraic over `ℚ`. -/
theorem exercise_8_4_iff (F : Subfield ℂ) :
    IsGarlingAlgebraicClosure ℚ F ↔ F = GarlingAlgebraicNumbers := by
  constructor
  · rintro ⟨halgF, hclosedF⟩
    have hF_le : F ≤ GarlingAlgebraicNumbers := by
      intro z hz
      obtain ⟨p, hp0, hpz⟩ := halgF ⟨z, hz⟩
      refine ⟨p, hp0, ?_⟩
      have hrat : F.subtype.comp (algebraMap ℚ F) = algebraMap ℚ ℂ :=
        RingHom.ext fun q => by simp
      rw [Polynomial.aeval_def, ← hrat, show z = F.subtype ⟨z, hz⟩ from rfl, ← Polynomial.hom_eval₂]
      change F.subtype (Polynomial.aeval (⟨z, hz⟩ : F) p) = 0
      rw [hpz, map_zero]
    let inc : F →+* GarlingAlgebraicNumbers := Subfield.inclusion hF_le
    let _ : Algebra F GarlingAlgebraicNumbers := inc.toAlgebra
    have halg_FA : IsAlgebraicExtension F GarlingAlgebraicNumbers := by
      intro y
      obtain ⟨p, hp0, hpy⟩ := y.2
      refine ⟨p.map (algebraMap ℚ F),
        (Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective).mpr hp0, ?_⟩
      apply GarlingAlgebraicNumbers.subtype_injective
      rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂,
        show algebraMap F GarlingAlgebraicNumbers = inc from rfl]
      have hrat :
          GarlingAlgebraicNumbers.subtype.comp (inc.comp (algebraMap ℚ F)) = algebraMap ℚ ℂ :=
        RingHom.ext fun q => by simp
      rw [hrat, ← Polynomial.aeval_def]
      exact hpy
    have hsurj : Function.Surjective inc :=
      (isGarlingAlgebraicallyClosed_surjective_of_algebraic hclosedF halg_FA).1
    have hA_le : GarlingAlgebraicNumbers ≤ F := by
      intro z hz
      obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
      have hval : x.1 = z := congrArg Subtype.val hx
      exact hval ▸ x.2
    exact le_antisymm hF_le hA_le
  · rintro rfl
    exact garlingAlgebraicNumbers_isGarlingAlgebraicClosure.1

/-- **Exercise 8.4** (§8.3, printed p. 76 / PDF p. 84):
*"What is the algebraic closure of `ℚ` (as a subfield of `ℂ`)?"*

Proves both the exact `↔` identification with `GarlingAlgebraicNumbers` (`A = algebraicSubfield ℚ ℂ`)
and unique existence `∃! F : Subfield ℂ, IsGarlingAlgebraicClosure ℚ F`. -/
theorem exercise_8_4 :
    (∀ F : Subfield ℂ, IsGarlingAlgebraicClosure ℚ F ↔ F = GarlingAlgebraicNumbers) ∧
    (∃! F : Subfield ℂ, IsGarlingAlgebraicClosure ℚ F) :=
  ⟨exercise_8_4_iff,
    ⟨GarlingAlgebraicNumbers, garlingAlgebraicNumbers_isGarlingAlgebraicClosure.1,
      fun F hF => (exercise_8_4_iff F).mp hF⟩⟩

/-- `IntermediateField ℚ ℂ` counterpart of **Exercise 8.4** (§8.3, printed p. 76 / PDF p. 84). -/
theorem exercise_8_4_intermediateField :
    (∀ F : IntermediateField ℚ ℂ,
      IsGarlingAlgebraicClosure ℚ F ↔ F = algebraicIntermediateField ℚ ℂ) ∧
    (∃! F : IntermediateField ℚ ℂ, IsGarlingAlgebraicClosure ℚ F) := by
  have hiff : ∀ F : IntermediateField ℚ ℂ,
      IsGarlingAlgebraicClosure ℚ F ↔ F = algebraicIntermediateField ℚ ℂ := by
    intro F
    have hbridge : IsGarlingAlgebraicClosure ℚ F ↔ IsGarlingAlgebraicClosure ℚ F.toSubfield := by
      have halg_eq : algebraMap ℚ F = algebraMap ℚ F.toSubfield :=
        RingHom.ext fun q => Subtype.ext (by simp)
      refine and_congr ⟨fun h x => ?_, fun h x => ?_⟩ Iff.rfl
      · obtain ⟨p, hp0, hpx⟩ := h x
        exact ⟨p, hp0, by simpa only [Polynomial.aeval_def, halg_eq] using hpx⟩
      · obtain ⟨p, hp0, hpx⟩ := h x
        exact ⟨p, hp0, by simpa only [Polynomial.aeval_def, ← halg_eq] using hpx⟩
    rw [hbridge, exercise_8_4_iff]
    exact ⟨fun h => by ext z; exact SetLike.ext_iff.mp h z,
      fun h => congrArg IntermediateField.toSubfield h⟩
  exact ⟨hiff, ⟨algebraicIntermediateField ℚ ℂ,
    (hiff (algebraicIntermediateField ℚ ℂ)).mpr rfl,
    fun F hF => (hiff F).mp hF⟩⟩

/-! ### Exercise 8.5 (§8.3, printed p. 76 / PDF p. 84) -/

/-- **Exercise 8.5** (§8.3, printed p. 76 / PDF p. 84):
*"Show that an algebraically closed field must be infinite."*

Proved directly via Euclid's polynomial `1 + ∏_{a ∈ L} (x - a)` in `L[x]`, giving `Infinite L`,
`¬ Finite L`, and `setOrder L = ⊤` (`|L| = +∞`). -/
theorem exercise_8_5 {L : Type u} [Field L] (hL : IsGarlingAlgebraicallyClosed L) :
    Infinite L ∧ ¬ Finite L ∧ setOrder L = ⊤ := by
  have hinf : Infinite L := by
    by_contra hnot_inf
    have _ : Finite L := not_infinite_iff_finite.mp hnot_inf
    let _ : Fintype L := Fintype.ofFinite L
    let P : L[X] := ∏ a : L, (Polynomial.X - Polynomial.C a)
    have hP_deg : P.natDegree = Fintype.card L := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)]
      simp
    have hcard : 1 < Fintype.card L := Fintype.one_lt_card
    have h1_lt : (1 : L[X]).natDegree < P.natDegree := by
      rw [Polynomial.natDegree_one, hP_deg]
      omega
    have hf_deg : (1 + P).natDegree = Fintype.card L := by
      rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt h1_lt, hP_deg]
    have hf0 : 1 + P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hf_deg
      omega
    obtain ⟨r, c, α, hexp⟩ := hL (1 + P)
    obtain ⟨_, _, hr_eq, hroots⟩ := garlingSplitsExplicit_props hf0 hexp
    have hr_card : r = Fintype.card L := by
      simpa [garlingDegree, hf_deg] using hr_eq
    have hr_pos : 0 < r := by omega
    let b : L := α ⟨0, hr_pos⟩
    have hb_mem : b ∈ (1 + P).rootSet L := hroots ▸ ⟨⟨0, hr_pos⟩, rfl⟩
    rw [Polynomial.mem_rootSet] at hb_mem
    have hb_eval : (1 + P).eval b = 0 := by
      simpa [Polynomial.aeval_def] using hb_mem.2
    rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_prod] at hb_eval
    have hprod0 : (∏ a : L, (Polynomial.X - Polynomial.C a : L[X]).eval b) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
    rw [hprod0, add_zero] at hb_eval
    exact one_ne_zero hb_eval
  have _ : Infinite L := hinf
  exact ⟨hinf, not_finite_iff_infinite.mpr hinf, by simp [setOrder]⟩

/-! ### Exercise 8.6 (§8.3, printed p. 76 / PDF p. 84) -/

/-- **Exercise 8.6** (§8.3, printed p. 76 / PDF p. 84):
*"Suppose that `K(α) : K` is a simple extension and that `α` is transcendental over `K`. Show that
`K(α)` is not algebraically closed."*

Proved unconditionally in **every** characteristic (including `char K = 2`) by showing via Chapter 7's
`exercise_7_3_iff` that `x² - α` is irreducible of degree `2` in `K(α)[x]` and hence cannot split
over `K(α)`. -/
theorem exercise_8_6 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (htrans : IsGarlingTranscendental K α) :
    ¬ IsGarlingAlgebraicallyClosed L := by
  intro hclosed
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C α : L[X]) :=
    (exercise_7_3_iff htrans hsimple 2).mpr (by omega)
  let f : L[X] := Polynomial.X ^ 2 - Polynomial.C α
  have hdeg_lt : (Polynomial.C α : L[X]).natDegree < (Polynomial.X ^ 2 : L[X]).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega
  have hf_deg : f.natDegree = 2 := by
    dsimp [f]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg_lt, Polynomial.natDegree_X_pow]
  obtain ⟨r, c, γ, hexp⟩ := hclosed f
  obtain ⟨_, _, hr_eq, hroots⟩ := garlingSplitsExplicit_props hirr.ne_zero hexp
  have hr_two : r = 2 := by
    simpa [garlingDegree, hf_deg] using hr_eq
  have hr_pos : 0 < r := by omega
  let β : L := γ ⟨0, hr_pos⟩
  have hβ_mem : β ∈ f.rootSet L := hroots ▸ ⟨⟨0, hr_pos⟩, rfl⟩
  rw [Polynomial.mem_rootSet] at hβ_mem
  have hβ_root : f.IsRoot β := by
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hβ_mem.2
  obtain ⟨q, hfq⟩ := Polynomial.dvd_iff_isRoot.mpr hβ_root
  have hX_ne0 : (Polynomial.X - Polynomial.C β : L[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero β
  have hq_ne0 : q ≠ 0 := fun h0 => hirr.ne_zero (by change f = 0; rw [hfq, h0, mul_zero])
  have hq_deg : q.natDegree = 1 := by
    have hd := Polynomial.natDegree_mul hX_ne0 hq_ne0
    rw [← hfq, hf_deg, Polynomial.natDegree_X_sub_C] at hd
    omega
  rcases hirr.isUnit_or_isUnit hfq with hu1 | hu2
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hu1)
      (by rw [Polynomial.natDegree_X_sub_C]; omega)
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hu2) (by omega)

/-- Subfield `K(α)` specialization of **Exercise 8.6** inside any ambient extension `Ω : K`. -/
theorem exercise_8_6_adjoin {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] {α : Ω}
    (htrans : IsGarlingTranscendental K α) :
    ¬ IsGarlingAlgebraicallyClosed (IntermediateField.adjoin K ({α} : Set Ω)) := by
  let Kα := IntermediateField.adjoin K ({α} : Set Ω)
  let α₀ : Kα := ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
  have hsimple : IntermediateField.adjoin K ({α₀} : Set Kα) = ⊤ := by
    ext ⟨xval, hx⟩
    simp only [IntermediateField.mem_top, iff_true]
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self K α₀
    | algebraMap k => exact (IntermediateField.adjoin K ({α₀} : Set Kα)).algebraMap_mem k
    | add y z hy hz ihy ihz =>
      exact (IntermediateField.adjoin K ({α₀} : Set Kα)).add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      exact (IntermediateField.adjoin K ({α₀} : Set Kα)).mul_mem ihy ihz
    | inv y hy ihy =>
      exact (IntermediateField.adjoin K ({α₀} : Set Kα)).inv_mem ihy
  have htrans₀ : IsGarlingTranscendental K α₀ := by
    rintro ⟨p, hp0, hpα⟩
    apply htrans
    refine ⟨p, hp0, ?_⟩
    rw [show α = Kα.val α₀ from rfl, Polynomial.aeval_algHom_apply, hpα, map_zero]
  exact exercise_8_6 hsimple htrans₀

/-- Rational-function-field specialization of **Exercise 8.6**: `FractionRing K[X]` is not
algebraically closed for any field `K`. -/
theorem exercise_8_6_ratFunc (K : Type u) [Field K] :
    ¬ IsGarlingAlgebraicallyClosed (FractionRing K[X]) := by
  let t : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) Polynomial.X
  have htrans : IsGarlingTranscendental K t := by
    rintro ⟨p, hp0, hpt⟩
    have hmap : Polynomial.aeval t p = algebraMap K[X] (FractionRing K[X]) p := by
      rw [Polynomial.aeval_def,
        IsScalarTower.algebraMap_eq K K[X] (FractionRing K[X]),
        ← Polynomial.hom_eval₂]
      change algebraMap K[X] (FractionRing K[X])
        (Polynomial.eval₂ Polynomial.C Polynomial.X p) = _
      rw [Polynomial.eval₂_C_X]
    rw [hmap] at hpt
    exact hp0 ((IsFractionRing.injective K[X] (FractionRing K[X]))
      (hpt.trans (map_zero _).symm))
  have hsimple : IntermediateField.adjoin K ({t} : Set (FractionRing K[X])) = ⊤ := by
    let F := IntermediateField.adjoin K ({t} : Set (FractionRing K[X]))
    have hpoly : ∀ p : K[X], algebraMap K[X] (FractionRing K[X]) p ∈ F := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q ihp ihq =>
        rw [map_add]
        exact F.add_mem ihp ihq
      | monomial n a =>
        have hmon : (Polynomial.monomial n a : K[X]) = Polynomial.C a * Polynomial.X ^ n := by
          rw [Polynomial.C_mul_X_pow_eq_monomial]
        rw [hmon, map_mul, map_pow]
        have haF : algebraMap K[X] (FractionRing K[X]) (Polynomial.C a) ∈ F := by
          have heq : algebraMap K[X] (FractionRing K[X]) (Polynomial.C a) =
              algebraMap K (FractionRing K[X]) a := rfl
          rw [heq]
          exact F.algebraMap_mem a
        exact F.mul_mem haF (F.pow_mem (IntermediateField.mem_adjoin_simple_self K t) n)
    apply top_unique
    intro z _
    obtain ⟨⟨num, den⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors K[X]) z
    dsimp only
    rw [IsFractionRing.mk'_eq_div]
    exact F.div_mem (hpoly num) (hpoly den)
  exact exercise_8_6 hsimple htrans

/-! ### Exercise 8.7 (§8.3, printed p. 76 / PDF p. 84 — `QUEUE.md` fidelity hold) -/

/-- One inductive step of **Exercise 8.7**'s splitting-field tower: given `(F, i : K →+* F)` and
`f ∈ K[X]`, pass to the splitting field `(f.map i).SplittingField` (constructed by finite degree
induction in `Mathlib.FieldTheory.SplittingField.Construction`, without Zorn's lemma). -/
private noncomputable def ex87Next {K : Type u} [Field K] (f : K[X])
    (s : Σ (F : Type u), Σ (_ : Field F), K →+* F) :
    Σ (F' : Type u), Σ (_ : Field F'), K →+* F' :=
  letI : Field s.1 := s.2.1
  let p : s.1[X] := f.map s.2.2
  ⟨p.SplittingField, ⟨inferInstance, (algebraMap s.1 p.SplittingField).comp s.2.2⟩⟩

/-- Bundled stage `n` of **Exercise 8.7**'s successive splitting-field tower along an enumeration
`enumPoly : ℕ → K[X]`. -/
noncomputable def ex87Stage {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    ℕ → Σ (F : Type u), Σ (_ : Field F), K →+* F
  | 0 => ⟨K, ⟨inferInstance, RingHom.id K⟩⟩
  | n + 1 => ex87Next (enumPoly n) (ex87Stage enumPoly n)

/-- Stage-`n` carrier field `K_n` of **Exercise 8.7** (§8.3, printed p. 76 / PDF p. 84). -/
abbrev Ex87Tower {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) : Type u :=
  (ex87Stage enumPoly n).1

noncomputable instance ex87TowerField {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    Field (Ex87Tower enumPoly n) :=
  (ex87Stage enumPoly n).2.1

/-- Canonical monomorphism `K →+* Ex87Tower enumPoly n`. -/
noncomputable def ex87FromK {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    K →+* Ex87Tower enumPoly n :=
  (ex87Stage enumPoly n).2.2

/-- Single-step extension monomorphism `K_n →+* K_{n+1}` into the splitting field of `enumPoly n`. -/
noncomputable def ex87Step {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    Ex87Tower enumPoly n →+* Ex87Tower enumPoly (n + 1) :=
  letI : Field (ex87Stage enumPoly n).1 := (ex87Stage enumPoly n).2.1
  algebraMap (ex87Stage enumPoly n).1
    (((enumPoly n).map (ex87Stage enumPoly n).2.2).SplittingField)

theorem ex87Step_comp_fromK {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    (ex87Step enumPoly n).comp (ex87FromK enumPoly n) = ex87FromK enumPoly (n + 1) :=
  rfl

/-- Directed transition monomorphisms `K_m →+* K_n` for `m ≤ n` in **Exercise 8.7**'s tower. -/
noncomputable def ex87Trans {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (m : ℕ) :
    ∀ n : ℕ, m ≤ n → (Ex87Tower enumPoly m →+* Ex87Tower enumPoly n)
  | 0, h => Nat.eq_zero_of_le_zero h ▸ RingHom.id _
  | n + 1, h =>
    if hmn : m ≤ n then
      (ex87Step enumPoly n).comp (ex87Trans enumPoly m n hmn)
    else
      (show m = n + 1 by omega) ▸ RingHom.id _

@[simp]
theorem ex87Trans_rfl {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    ex87Trans enumPoly n n (le_refl n) = RingHom.id _ := by
  cases n with
  | zero => rfl
  | succ n => simp [ex87Trans]

theorem ex87Trans_step {K : Type u} [Field K] (enumPoly : ℕ → K[X]) {m n : ℕ} (h : m ≤ n) :
    ex87Trans enumPoly m (n + 1) (Nat.le_succ_of_le h) =
      (ex87Step enumPoly n).comp (ex87Trans enumPoly m n h) := by
  simp [ex87Trans, h]

theorem ex87Trans_comp {K : Type u} [Field K] (enumPoly : ℕ → K[X]) {l m n : ℕ}
    (h₁ : l ≤ m) (h₂ : m ≤ n) :
    (ex87Trans enumPoly m n h₂).comp (ex87Trans enumPoly l m h₁) =
      ex87Trans enumPoly l n (h₁.trans h₂) := by
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero h₂
    subst hm0
    have hl0 : l = 0 := Nat.eq_zero_of_le_zero h₁
    subst hl0
    rfl
  | succ n ih =>
    by_cases hmn : m ≤ n
    · have hln : l ≤ n := h₁.trans hmn
      simp only [ex87Trans, hmn, hln, ↓reduceDIte]
      rw [RingHom.comp_assoc, ih hmn]
    · have hm_eq : m = n + 1 := by omega
      subst hm_eq
      rw [ex87Trans_rfl, RingHom.id_comp]

@[simp]
private theorem ex87Trans_trans_apply {K : Type u} [Field K] (enumPoly : ℕ → K[X]) {l m n : ℕ}
    (h₁ : l ≤ m) (h₂ : m ≤ n) (x : Ex87Tower enumPoly l) :
    ex87Trans enumPoly m n h₂ (ex87Trans enumPoly l m h₁ x) =
      ex87Trans enumPoly l n (h₁.trans h₂) x :=
  RingHom.congr_fun (ex87Trans_comp enumPoly h₁ h₂) x

@[simp]
private theorem ex87Trans_self_apply {K : Type u} [Field K] (enumPoly : ℕ → K[X]) {n : ℕ}
    (h : n ≤ n) (x : Ex87Tower enumPoly n) :
    ex87Trans enumPoly n n h x = x := by
  rw [show h = le_refl n from Subsingleton.elim _ _, ex87Trans_rfl]
  rfl

theorem ex87Trans_zero_eq_fromK {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    ex87Trans enumPoly 0 n (Nat.zero_le n) = ex87FromK enumPoly n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show Nat.zero_le (n + 1) = Nat.le_succ_of_le (Nat.zero_le n) from rfl,
      ex87Trans_step enumPoly (Nat.zero_le n), ih]
    exact ex87Step_comp_fromK enumPoly n

/-- Directed-colimit equivalence relation on `Σ n : ℕ, Ex87Tower enumPoly n` (**Exercise 8.7**):
`(m, x) ~ (n, y)` iff `x` and `y` have equal images in `K_{max(m, n)}`. -/
def ex87Rel {K : Type u} [Field K] (enumPoly : ℕ → K[X])
    (a b : Σ n : ℕ, Ex87Tower enumPoly n) : Prop :=
  ex87Trans enumPoly a.1 (max a.1 b.1) (Nat.le_max_left a.1 b.1) a.2 =
    ex87Trans enumPoly b.1 (max a.1 b.1) (Nat.le_max_right a.1 b.1) b.2

private theorem ex87Rel_iff {K : Type u} [Field K] {enumPoly : ℕ → K[X]}
    {a b : Σ n : ℕ, Ex87Tower enumPoly n} {N : ℕ} (ha : a.1 ≤ N) (hb : b.1 ≤ N) :
    ex87Rel enumPoly a b ↔
      ex87Trans enumPoly a.1 N ha a.2 = ex87Trans enumPoly b.1 N hb b.2 := by
  unfold ex87Rel
  have hmax : max a.1 b.1 ≤ N := max_le ha hb
  rw [← ex87Trans_trans_apply enumPoly (Nat.le_max_left a.1 b.1) hmax,
    ← ex87Trans_trans_apply enumPoly (Nat.le_max_right a.1 b.1) hmax]
  exact (ex87Trans enumPoly (max a.1 b.1) N hmax).injective.eq_iff.symm

def ex87Setoid {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Setoid (Σ n : ℕ, Ex87Tower enumPoly n) where
  r := ex87Rel enumPoly
  iseqv :=
    { refl := fun _ => rfl
      symm := fun {a b} hab => by
        rw [ex87Rel_iff (a := b) (b := a) (Nat.le_max_right a.1 b.1) (Nat.le_max_left a.1 b.1)]
        exact ((ex87Rel_iff (Nat.le_max_left a.1 b.1) (Nat.le_max_right a.1 b.1)).mp hab).symm
      trans := fun {a b c} hab hbc => by
        let N := max (max a.1 b.1) c.1
        have ha : a.1 ≤ N := le_trans (Nat.le_max_left a.1 b.1) (Nat.le_max_left _ _)
        have hb : b.1 ≤ N := le_trans (Nat.le_max_right a.1 b.1) (Nat.le_max_left _ _)
        have hc : c.1 ≤ N := Nat.le_max_right _ _
        rw [ex87Rel_iff ha hc]
        exact ((ex87Rel_iff ha hb).mp hab).trans ((ex87Rel_iff hb hc).mp hbc) }

private theorem ex87Equiv_mk_iff {K : Type u} [Field K] {enumPoly : ℕ → K[X]}
    {m n N : ℕ} {x : Ex87Tower enumPoly m} {y : Ex87Tower enumPoly n}
    (hm : m ≤ N) (hn : n ≤ N) :
    @HasEquiv.Equiv (Σ k : ℕ, Ex87Tower enumPoly k)
        (@instHasEquivOfSetoid _ (ex87Setoid enumPoly)) ⟨m, x⟩ ⟨n, y⟩ ↔
      ex87Trans enumPoly m N hm x = ex87Trans enumPoly n N hn y :=
  ex87Rel_iff (a := ⟨m, x⟩) (b := ⟨n, y⟩) hm hn

/-- Explicit directed-colimit field `varinjlim_n K_n` of **Exercise 8.7**'s successive
splitting-field tower (resolving p. 72's inclusion-vs-triple fallacy via the quotient of the
disjoint union `Σ n : ℕ, K_n`). -/
abbrev Ex87Colimit {K : Type u} [Field K] (enumPoly : ℕ → K[X]) : Type u :=
  Quotient (ex87Setoid enumPoly)

private noncomputable def ex87ColimitAdd {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Ex87Colimit enumPoly → Ex87Colimit enumPoly → Ex87Colimit enumPoly :=
  Quotient.lift₂
    (fun a b => Quotient.mk (ex87Setoid enumPoly)
      ⟨max a.1 b.1,
        ex87Trans enumPoly a.1 (max a.1 b.1) (Nat.le_max_left a.1 b.1) a.2 +
          ex87Trans enumPoly b.1 (max a.1 b.1) (Nat.le_max_right a.1 b.1) b.2⟩)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (by
      let N := max (max a₁.1 b₁.1) (max a₂.1 b₂.1)
      have hm1 : max a₁.1 b₁.1 ≤ N := Nat.le_max_left _ _
      have hm2 : max a₂.1 b₂.1 ≤ N := Nat.le_max_right _ _
      have ha1 : a₁.1 ≤ N := le_trans (Nat.le_max_left _ _) hm1
      have hb1 : b₁.1 ≤ N := le_trans (Nat.le_max_right _ _) hm1
      have ha2 : a₂.1 ≤ N := le_trans (Nat.le_max_left _ _) hm2
      have hb2 : b₂.1 ≤ N := le_trans (Nat.le_max_right _ _) hm2
      rw [ex87Equiv_mk_iff hm1 hm2]
      simp [(ex87Rel_iff ha1 ha2).mp ha, (ex87Rel_iff hb1 hb2).mp hb]))

private noncomputable def ex87ColimitMul {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Ex87Colimit enumPoly → Ex87Colimit enumPoly → Ex87Colimit enumPoly :=
  Quotient.lift₂
    (fun a b => Quotient.mk (ex87Setoid enumPoly)
      ⟨max a.1 b.1,
        ex87Trans enumPoly a.1 (max a.1 b.1) (Nat.le_max_left a.1 b.1) a.2 *
          ex87Trans enumPoly b.1 (max a.1 b.1) (Nat.le_max_right a.1 b.1) b.2⟩)
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (by
      let N := max (max a₁.1 b₁.1) (max a₂.1 b₂.1)
      have hm1 : max a₁.1 b₁.1 ≤ N := Nat.le_max_left _ _
      have hm2 : max a₂.1 b₂.1 ≤ N := Nat.le_max_right _ _
      have ha1 : a₁.1 ≤ N := le_trans (Nat.le_max_left _ _) hm1
      have hb1 : b₁.1 ≤ N := le_trans (Nat.le_max_right _ _) hm1
      have ha2 : a₂.1 ≤ N := le_trans (Nat.le_max_left _ _) hm2
      have hb2 : b₂.1 ≤ N := le_trans (Nat.le_max_right _ _) hm2
      rw [ex87Equiv_mk_iff hm1 hm2]
      simp [(ex87Rel_iff ha1 ha2).mp ha, (ex87Rel_iff hb1 hb2).mp hb]))

private noncomputable def ex87ColimitNeg {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Ex87Colimit enumPoly → Ex87Colimit enumPoly :=
  Quotient.lift
    (fun a => Quotient.mk (ex87Setoid enumPoly) ⟨a.1, -a.2⟩)
    (fun a b hab => Quotient.sound (by
      change ex87Trans enumPoly a.1 (max a.1 b.1) (Nat.le_max_left a.1 b.1) (-a.2) =
        ex87Trans enumPoly b.1 (max a.1 b.1) (Nat.le_max_right a.1 b.1) (-b.2)
      rw [map_neg, map_neg]
      exact congrArg Neg.neg hab))

private noncomputable def ex87ColimitInv {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Ex87Colimit enumPoly → Ex87Colimit enumPoly :=
  Quotient.lift
    (fun a => Quotient.mk (ex87Setoid enumPoly) ⟨a.1, a.2⁻¹⟩)
    (fun a b hab => Quotient.sound (by
      change ex87Trans enumPoly a.1 (max a.1 b.1) (Nat.le_max_left a.1 b.1) a.2⁻¹ =
        ex87Trans enumPoly b.1 (max a.1 b.1) (Nat.le_max_right a.1 b.1) b.2⁻¹
      rw [map_inv₀, map_inv₀]
      exact congrArg Inv.inv hab))

noncomputable instance ex87ColimitField {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Field (Ex87Colimit enumPoly) := by
  letI : Add (Ex87Colimit enumPoly) := ⟨ex87ColimitAdd enumPoly⟩
  letI : Mul (Ex87Colimit enumPoly) := ⟨ex87ColimitMul enumPoly⟩
  letI : Zero (Ex87Colimit enumPoly) := ⟨Quotient.mk (ex87Setoid enumPoly) ⟨0, 0⟩⟩
  letI : One (Ex87Colimit enumPoly) := ⟨Quotient.mk (ex87Setoid enumPoly) ⟨0, 1⟩⟩
  letI : Neg (Ex87Colimit enumPoly) := ⟨ex87ColimitNeg enumPoly⟩
  letI : Inv (Ex87Colimit enumPoly) := ⟨ex87ColimitInv enumPoly⟩
  refine Field.ofMinimalAxioms (Ex87Colimit enumPoly)
    (fun x y z => ?_) (fun x => ?_) (fun x => ?_)
    (fun x y z => ?_) (fun x y => ?_) (fun x => ?_)
    (fun x hx => ?_) ?_ (fun x y z => ?_) ⟨Quotient.mk _ ⟨0, 0⟩, Quotient.mk _ ⟨0, 1⟩, ?_⟩
  · refine Quotient.inductionOn₃ x y z fun a b c => Quotient.sound ?_
    let N := max (max a.1 b.1) c.1
    have hab : max a.1 b.1 ≤ N := Nat.le_max_left _ _
    have hbc : max b.1 c.1 ≤ N :=
      max_le (le_trans (Nat.le_max_right a.1 b.1) hab) (Nat.le_max_right _ _)
    have haN : a.1 ≤ N := le_trans (Nat.le_max_left a.1 b.1) hab
    have hL : max (max a.1 b.1) c.1 ≤ N := le_rfl
    have hR : max a.1 (max b.1 c.1) ≤ N := max_le haN hbc
    dsimp only
    rw [ex87Equiv_mk_iff hL hR]
    simp [add_assoc]
  · refine Quotient.inductionOn x fun a => Quotient.sound ?_
    dsimp only
    rw [ex87Equiv_mk_iff (show max 0 a.1 ≤ a.1 by simp) le_rfl]
    simp
  · refine Quotient.inductionOn x fun a => Quotient.sound ?_
    dsimp only
    rw [ex87Equiv_mk_iff (show max a.1 a.1 ≤ a.1 by simp) (Nat.zero_le a.1)]
    simp
  · refine Quotient.inductionOn₃ x y z fun a b c => Quotient.sound ?_
    let N := max (max a.1 b.1) c.1
    have hab : max a.1 b.1 ≤ N := Nat.le_max_left _ _
    have hbc : max b.1 c.1 ≤ N :=
      max_le (le_trans (Nat.le_max_right a.1 b.1) hab) (Nat.le_max_right _ _)
    have haN : a.1 ≤ N := le_trans (Nat.le_max_left a.1 b.1) hab
    have hL : max (max a.1 b.1) c.1 ≤ N := le_rfl
    have hR : max a.1 (max b.1 c.1) ≤ N := max_le haN hbc
    dsimp only
    rw [ex87Equiv_mk_iff hL hR]
    simp [mul_assoc]
  · refine Quotient.inductionOn₂ x y fun a b => Quotient.sound ?_
    let N := max a.1 b.1
    have hL : max a.1 b.1 ≤ N := le_rfl
    have hR : max b.1 a.1 ≤ N := max_le (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    rw [ex87Equiv_mk_iff hL hR]
    simp [mul_comm]
  · refine Quotient.inductionOn x fun a => Quotient.sound ?_
    dsimp only
    rw [ex87Equiv_mk_iff (show max 0 a.1 ≤ a.1 by simp) le_rfl]
    simp
  · refine Quotient.inductionOn x (fun a ha0 => Quotient.sound ?_) hx
    rcases a with ⟨m, am⟩
    have ha_ne0 : am ≠ 0 := by
      intro h0
      apply ha0
      apply Quotient.sound
      rw [ex87Equiv_mk_iff le_rfl (Nat.zero_le m)]
      simp [h0]
    dsimp only
    rw [ex87Equiv_mk_iff (show max m m ≤ m by simp) (Nat.zero_le m)]
    simp [ha_ne0]
  · apply Quotient.sound
    dsimp only
    rw [ex87Equiv_mk_iff le_rfl le_rfl]
    simp
  · refine Quotient.inductionOn₃ x y z fun a b c => Quotient.sound ?_
    let N := max a.1 (max b.1 c.1)
    have haN : a.1 ≤ N := Nat.le_max_left _ _
    have hbc : max b.1 c.1 ≤ N := Nat.le_max_right _ _
    have hbN : b.1 ≤ N := le_trans (Nat.le_max_left b.1 c.1) hbc
    have hcN : c.1 ≤ N := le_trans (Nat.le_max_right b.1 c.1) hbc
    have hL : max a.1 (max b.1 c.1) ≤ N := le_rfl
    have hR : max (max a.1 b.1) (max a.1 c.1) ≤ N := max_le (max_le haN hbN) (max_le haN hcN)
    dsimp only
    rw [ex87Equiv_mk_iff hL hR]
    simp [mul_add]
  · intro h01
    have hrel := Quotient.exact h01
    rw [ex87Equiv_mk_iff le_rfl le_rfl] at hrel
    simp at hrel

/-- Canonical stage embedding `Ex87Tower enumPoly n →+* Ex87Colimit enumPoly`. -/
noncomputable def ex87OfStage {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    Ex87Tower enumPoly n →+* Ex87Colimit enumPoly where
  toFun x := Quotient.mk (ex87Setoid enumPoly) ⟨n, x⟩
  map_zero' := Quotient.sound (by
    rw [ex87Equiv_mk_iff le_rfl (Nat.zero_le n)]
    simp)
  map_one' := Quotient.sound (by
    rw [ex87Equiv_mk_iff le_rfl (Nat.zero_le n)]
    simp)
  map_add' x y := Quotient.sound (by
    dsimp only
    rw [ex87Equiv_mk_iff le_rfl (show max n n ≤ n by simp)]
    simp)
  map_mul' x y := Quotient.sound (by
    dsimp only
    rw [ex87Equiv_mk_iff le_rfl (show max n n ≤ n by simp)]
    simp)

theorem ex87OfStage_comp_trans {K : Type u} [Field K] (enumPoly : ℕ → K[X]) {m n : ℕ}
    (h : m ≤ n) :
    (ex87OfStage enumPoly n).comp (ex87Trans enumPoly m n h) = ex87OfStage enumPoly m := by
  ext x
  apply Quotient.sound
  rw [ex87Equiv_mk_iff le_rfl h]
  simp

noncomputable instance ex87ColimitAlgebra {K : Type u} [Field K] (enumPoly : ℕ → K[X]) :
    Algebra K (Ex87Colimit enumPoly) :=
  (ex87OfStage enumPoly 0).toAlgebra

theorem ex87Tower_algebraic {K : Type u} [Field K] (enumPoly : ℕ → K[X]) (n : ℕ) :
    (letI : Algebra K (Ex87Tower enumPoly n) := (ex87FromK enumPoly n).toAlgebra
     IsAlgebraicExtension K (Ex87Tower enumPoly n)) := by
  induction n with
  | zero =>
    let _ : Algebra K (Ex87Tower enumPoly 0) := (ex87FromK enumPoly 0).toAlgebra
    intro x
    let xK : K := x
    refine ⟨Polynomial.X - Polynomial.C xK, Polynomial.X_sub_C_ne_zero xK, ?_⟩
    change Polynomial.eval₂ (RingHom.id K) xK (Polynomial.X - Polynomial.C xK) = 0
    simp
  | succ n ih =>
    let _ : Field (ex87Stage enumPoly n).1 := (ex87Stage enumPoly n).2.1
    let p : (ex87Stage enumPoly n).1[X] := (enumPoly n).map (ex87Stage enumPoly n).2.2
    have _ : FiniteDimensional (ex87Stage enumPoly n).1 p.SplittingField := inferInstance
    have halg_step :
        (letI : Algebra (Ex87Tower enumPoly n) (Ex87Tower enumPoly (n + 1)) :=
          (ex87Step enumPoly n).toAlgebra
         IsAlgebraicExtension (Ex87Tower enumPoly n) (Ex87Tower enumPoly (n + 1))) :=
      (isAlgebraicExtension_iff (ex87Stage enumPoly n).1 p.SplittingField).mpr
        (Algebra.IsAlgebraic.of_finite (ex87Stage enumPoly n).1 p.SplittingField)
    exact theorem_4_7_triple
      (FieldExtensionTriple.ofRingHom (ex87FromK enumPoly n))
      (FieldExtensionTriple.ofRingHom (ex87Step enumPoly n))
      halg_step ih

/-- **Exercise 8.7** (directed-colimit construction along any surjective enumeration
`enumPoly : ℕ → K[X]`, §8.3, printed p. 76 / PDF p. 84):
`Ex87Colimit enumPoly` is a countable algebraic closure of `K`, constructed purely by finite-step
splitting fields and an explicit quotient colimit (without Zorn's lemma). -/
theorem exercise_8_7_of_surjective {K : Type u} [Field K] {enumPoly : ℕ → K[X]}
    (hsurj : Function.Surjective enumPoly) :
    IsGarlingAlgebraicClosure K (Ex87Colimit enumPoly) ∧ Countable (Ex87Colimit enumPoly) := by
  have hcountK : Countable K := by
    let f : ℕ → K := fun n => (enumPoly n).coeff 0
    have hf : Function.Surjective f := fun c => by
      obtain ⟨n, hn⟩ := hsurj (Polynomial.C c)
      exact ⟨n, by simp [f, hn]⟩
    exact hf.countable
  have _ : Countable K := hcountK
  have halg : IsAlgebraicExtension K (Ex87Colimit enumPoly) := by
    intro z
    refine Quotient.inductionOn z fun a => ?_
    let _ : Algebra K (Ex87Tower enumPoly a.1) := (ex87FromK enumPoly a.1).toAlgebra
    obtain ⟨p, hp0, hpa⟩ := ex87Tower_algebraic enumPoly a.1 a.2
    refine ⟨p, hp0, ?_⟩
    have hcomm : (ex87OfStage enumPoly a.1).comp (ex87FromK enumPoly a.1) =
        algebraMap K (Ex87Colimit enumPoly) := by
      rw [← ex87Trans_zero_eq_fromK enumPoly a.1]
      exact ex87OfStage_comp_trans enumPoly (Nat.zero_le a.1)
    change Polynomial.eval₂ (algebraMap K (Ex87Colimit enumPoly))
      (ex87OfStage enumPoly a.1 a.2) p = 0
    rw [← hcomm, ← Polynomial.hom_eval₂]
    change ex87OfStage enumPoly a.1 (Polynomial.aeval a.2 p) = 0
    rw [hpa, map_zero]
  have hsplit_irr : ∀ f : K[X], Irreducible f → GarlingSplitsOver K (Ex87Colimit enumPoly) f := by
    intro f _
    obtain ⟨n, rfl⟩ := hsurj f
    let _ : Field (ex87Stage enumPoly n).1 := (ex87Stage enumPoly n).2.1
    let p : (ex87Stage enumPoly n).1[X] := (enumPoly n).map (ex87Stage enumPoly n).2.2
    have hsp_stage : Polynomial.Splits (p.map (ex87Step enumPoly n)) :=
      Polynomial.SplittingField.splits p
    have hgar_stage :
        (letI : Algebra K (Ex87Tower enumPoly (n + 1)) := (ex87FromK enumPoly (n + 1)).toAlgebra
         GarlingSplitsOver K (Ex87Tower enumPoly (n + 1)) (enumPoly n)) := by
      let _ : Algebra K (Ex87Tower enumPoly (n + 1)) := (ex87FromK enumPoly (n + 1)).toAlgebra
      rw [garlingSplitsOver_iff_splits]
      change Polynomial.Splits ((enumPoly n).map ((ex87Step enumPoly n).comp (ex87FromK enumPoly n)))
      rw [← Polynomial.map_map]
      exact hsp_stage
    let _ : Algebra K (Ex87Tower enumPoly (n + 1)) := (ex87FromK enumPoly (n + 1)).toAlgebra
    obtain ⟨r, c, α, hexp⟩ := hgar_stage
    refine ⟨r, c, fun j => ex87OfStage enumPoly (n + 1) (α j), ?_⟩
    have hcomm : (ex87OfStage enumPoly (n + 1)).comp (ex87FromK enumPoly (n + 1)) =
        algebraMap K (Ex87Colimit enumPoly) := by
      rw [← ex87Trans_zero_eq_fromK enumPoly (n + 1)]
      exact ex87OfStage_comp_trans enumPoly (Nat.zero_le (n + 1))
    unfold GarlingSplitsExplicit at hexp ⊢
    have hexp' : (enumPoly n).map (ex87FromK enumPoly (n + 1)) =
        Polynomial.C (ex87FromK enumPoly (n + 1) c) *
          ∏ j : Fin r, (Polynomial.X - Polynomial.C (α j)) := hexp
    rw [← hcomm, ← Polynomial.map_map, hexp']
    simp [Polynomial.map_prod]
  have hclosure : IsGarlingAlgebraicClosure K (Ex87Colimit enumPoly) :=
    (theorem_8_1 K (Ex87Colimit enumPoly)).1.mpr ⟨halg, hsplit_irr⟩
  exact ⟨hclosure, exercise_4_7_countable halg⟩

/-- **Exercise 8.7** (§8.3, printed p. 76 / PDF p. 84 — held in `QUEUE.md`):
*"Suppose that `K` is a countable field. Show how to construct an algebraic closure, by successively
constructing splitting fields of the (countably many) polynomials in `K[x]`. Is your construction
less fallacious than the 'fallacious proof' of Theorem 8.2?"*

Provides:
1. Existence of a surjective enumeration `enumPoly : ℕ → K[X]` for any countable field `K` and the
   explicit Zorn-free colimit algebraic closure `Ex87Colimit enumPoly`;
2. An embedded-chain companion inside `P(K[x] × ℤ⁺)` (`Exercise 8.2 (ii)` + `Exercise 8.3 (i)`),
   showing how embedding the splitting-field tower `K_0 → K_1 → …` as genuine subsets
   `j(K) = S_0 ⊆ S_1 ⊆ … ⊆ P(K[x] × ℤ⁺)` makes the **literal set-theoretic union** `⋃_n S_n` an
   algebraic closure of `K` (whereas taking a naive union of abstract extension triples without a
   colimit quotient or ambient embedding commits the exact fallacy analyzed on printed p. 72). -/
theorem exercise_8_7 (K : Type u) [Field K] [Countable K] :
    (∃ enumPoly : ℕ → K[X],
      Function.Surjective enumPoly ∧
      IsGarlingAlgebraicClosure K (Ex87Colimit enumPoly) ∧
      Countable (Ex87Colimit enumPoly)) ∧
    (∃ (S : ℕ → Set (Set (Ex82U K))) (_ : Field ↥(⋃ n : ℕ, S n))
        (jHom : K →+* ↥(⋃ n : ℕ, S n)),
      S 0 = Ex83JK K ∧
      (∀ n : ℕ, S n ⊆ S (n + 1)) ∧
      (∀ α : K, (jHom α : Set (Ex82U K)) = ex83J K α) ∧
      IsGarlingAlgebraicClosureHom jHom) := by
  classical
  have _ : Countable K[X] := countable_polynomial K
  have _ : Nonempty K[X] := ⟨0⟩
  obtain ⟨enumPoly, hsurj⟩ := exists_surjective_nat K[X]
  obtain ⟨hcl, hcnt⟩ := exercise_8_7_of_surjective hsurj
  refine ⟨⟨enumPoly, hsurj, hcl, hcnt⟩, ?_⟩
  -- Embed `Ex87Colimit enumPoly` into `P(U)` extending `ex83J K : K ↪ P(U)` via Exercise 8.2 (ii),
  -- so `S_n = g(ex87OfStage n (K_n))` forms a genuine increasing chain with union `range g ≅ L`.
  obtain ⟨g, hg_inj, hg_comp⟩ := exercise_8_2_ii
    (FieldExtensionTriple.ofRingHom (RingHom.id K))
    (FieldExtensionTriple.ofAlgebra K (Ex87Colimit enumPoly))
    (fun x => ⟨Polynomial.X - Polynomial.C x, Polynomial.X_sub_C_ne_zero x, by
      change Polynomial.eval₂ (RingHom.id K) x (Polynomial.X - Polynomial.C x) = 0
      simp⟩)
    hcl.1
    (ex83J_injective K)
  let S : ℕ → Set (Set (Ex82U K)) := fun n => Set.range (g ∘ ex87OfStage enumPoly n)
  have hS0 : S 0 = Ex83JK K := by
    ext A
    simp only [S, Ex83JK, Set.mem_range, Function.comp_apply]
    refine exists_congr fun α => ?_
    have hα : ex83J K α = g (algebraMap K (Ex87Colimit enumPoly) α) := congrFun hg_comp α
    rw [hα]
    rfl
  have hS_mono : ∀ n : ℕ, S n ⊆ S (n + 1) := by
    rintro n A ⟨x, hxA⟩
    refine ⟨ex87Step enumPoly n x, ?_⟩
    simp only [Function.comp_apply] at hxA ⊢
    have hstep : ex87Step enumPoly n = ex87Trans enumPoly n (n + 1) (Nat.le_succ n) := by
      rw [show Nat.le_succ n = Nat.le_succ_of_le (le_refl n) from rfl,
        ex87Trans_step enumPoly (le_refl n), ex87Trans_rfl, RingHom.comp_id]
    rw [hstep]
    exact (congrArg g (RingHom.congr_fun (ex87OfStage_comp_trans enumPoly (Nat.le_succ n)) x)).trans hxA
  have hiUnion_eq : (⋃ n : ℕ, S n) = Set.range g := by
    ext A
    simp only [S, Set.mem_iUnion, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨n, x, rfl⟩
      exact ⟨ex87OfStage enumPoly n x, rfl⟩
    · rintro ⟨z, rfl⟩
      refine Quotient.inductionOn z fun a => ⟨a.1, a.2, rfl⟩
  let Uset := ⋃ n : ℕ, S n
  let eSet : ↥(Set.range g) ≃ Uset :=
    { toFun := fun x => ⟨x.1, by dsimp only [Uset]; rw [hiUnion_eq]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [← hiUnion_eq]; exact x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eColim : Ex87Colimit enumPoly ≃ Uset :=
    (Equiv.ofInjective g hg_inj).trans eSet
  let instFU : Field Uset := eColim.symm.field
  let _ : Field Uset := instFU
  let eRing : Ex87Colimit enumPoly ≃+* Uset := eColim.symm.ringEquiv.symm
  let jHom : K →+* Uset := eRing.toRingHom.comp (algebraMap K (Ex87Colimit enumPoly))
  have hj_val : ∀ α : K, (jHom α : Set (Ex82U K)) = ex83J K α := by
    intro α
    exact (congrFun hg_comp α).symm
  have hj_cl : IsGarlingAlgebraicClosureHom jHom := by
    let _ : Algebra K Uset := jHom.toAlgebra
    refine ⟨?_, ?_⟩
    · intro u
      obtain ⟨z, rfl⟩ := eRing.surjective u
      obtain ⟨p, hp0, hpz⟩ := hcl.1 z
      refine ⟨p, hp0, ?_⟩
      change Polynomial.eval₂ (eRing.toRingHom.comp (algebraMap K (Ex87Colimit enumPoly)))
        (eRing.toRingHom z) p = 0
      rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hpz, map_zero]
    · intro q
      obtain ⟨r, c, α, hexp⟩ := hcl.2 (q.map eRing.symm.toRingHom)
      refine ⟨r, eRing c, fun i => eRing (α i), ?_⟩
      unfold GarlingSplitsExplicit at hexp ⊢
      have hexp' : (q.map eRing.symm.toRingHom) =
          Polynomial.C c * ∏ i : Fin r, (Polynomial.X - Polynomial.C (α i)) := by
        simpa [Algebra.algebraMap_self, Polynomial.map_id] using hexp
      have hmap := congrArg (Polynomial.map eRing.toRingHom) hexp'
      have hq_id : (q.map eRing.symm.toRingHom).map eRing.toRingHom = q := by
        ext k
        simp
      rw [hq_id] at hmap
      simpa [Algebra.algebraMap_self, Polynomial.map_id, Polynomial.map_prod] using hmap
  exact ⟨S, instFU, jHom, hS0, hS_mono, hj_val, hj_cl⟩

/-! ### Exercise 8.8 (§8.3, printed p. 76 / PDF p. 84 — `QUEUE.md` fidelity hold) -/

/-- **Exercise 8.8, Sense 1 (Tower / transitivity)** (§8.3, printed p. 76 / PDF p. 84):
in any field tower `M : L : K` with `L : K` algebraic, `M` is an algebraic closure of `L` if and
only if `M` is an algebraic closure of `K`. -/
theorem exercise_8_8_tower_iff {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (halg : IsAlgebraicExtension K L) :
    IsGarlingAlgebraicClosure L M ↔ IsGarlingAlgebraicClosure K M := by
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hLM
    exact theorem_4_7 hLM halg
  · intro hKM α
    obtain ⟨p, hp0, hpα⟩ := hKM α
    refine ⟨p.map (algebraMap K L),
      (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K L M,
      ← Polynomial.aeval_def]
    exact hpα

/-- **Exercise 8.8, Sense 2 (Literal subfield equality in a common overfield)** (§8.3, p. 76):
in any tower `Ω : L : K`, if `L : K` is algebraic then `algebraicSubfield L Ω = algebraicSubfield K Ω`;
and when `Ω` is algebraically closed (so `algebraicIntermediateField L Ω` and
`algebraicIntermediateField K Ω` are algebraic closures by `Corollary` to `Theorem 8.1`), literal
equality `algebraicSubfield L Ω = algebraicSubfield K Ω` holds **if and only if** `L : K` is
algebraic. -/
theorem exercise_8_8_ambient_subfield_eq {K : Type u} {L : Type v} {Ω : Type w}
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] :
    (IsAlgebraicExtension K L → algebraicSubfield L Ω = algebraicSubfield K Ω) ∧
    (IsGarlingAlgebraicallyClosed Ω →
      (IsGarlingAlgebraicClosure L (algebraicIntermediateField L Ω) ∧
       IsGarlingAlgebraicClosure K (algebraicIntermediateField K Ω) ∧
       (algebraicSubfield L Ω = algebraicSubfield K Ω ↔ IsAlgebraicExtension K L))) := by
  have hforward : IsAlgebraicExtension K L → algebraicSubfield L Ω = algebraicSubfield K Ω := by
    intro halgKL
    ext α
    rw [mem_algebraicSubfield_iff, mem_algebraicSubfield_iff]
    constructor
    · intro hαL
      let Lα : IntermediateField L Ω := IntermediateField.adjoin L ({α} : Set Ω)
      have halgLα : IsAlgebraicExtension L Lα := corollary_1_to_theorem_4_6 hαL
      let _ : Algebra K Lα := ((algebraMap L Lα).comp (algebraMap K L)).toAlgebra
      have _ : IsScalarTower K L Lα := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have halgK_Lα : IsAlgebraicExtension K Lα := theorem_4_7 halgLα halgKL
      let fK : Lα →ₐ[K] Ω :=
        { Lα.val.toRingHom with
          commutes' := fun k => by
            change algebraMap L Ω (algebraMap K L k) = algebraMap K Ω k
            exact (IsScalarTower.algebraMap_apply K L Ω k).symm }
      let α₀ : Lα := ⟨α, IntermediateField.mem_adjoin_simple_self L α⟩
      obtain ⟨p, hp0, hpα⟩ := halgK_Lα α₀
      refine ⟨p, hp0, ?_⟩
      rw [show α = fK α₀ from rfl, Polynomial.aeval_algHom_apply, hpα, map_zero]
    · rintro ⟨p, hp0, hpα⟩
      refine ⟨p.map (algebraMap K L),
        (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K L Ω,
        ← Polynomial.aeval_def]
      exact hpα
  refine ⟨hforward, fun hΩ => ⟨corollary_to_theorem_8_1 (K := L) hΩ,
    corollary_to_theorem_8_1 (K := K) hΩ, ⟨fun heq β => ?_, hforward⟩⟩⟩
  have hmemL : algebraMap L Ω β ∈ algebraicSubfield L Ω := by
    rw [mem_algebraicSubfield_iff]
    exact ⟨Polynomial.X - Polynomial.C β, Polynomial.X_sub_C_ne_zero β, by simp⟩
  rw [heq, mem_algebraicSubfield_iff] at hmemL
  obtain ⟨p, hp0, hpβ⟩ := hmemL
  refine ⟨p, hp0, ?_⟩
  apply (algebraMap L Ω).injective
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq K L Ω,
    ← Polynomial.aeval_def]
  exact hpβ

/-- **Exercise 8.8, Sense 3 (Isomorphism of arbitrary algebraic closures `(i_K, K, K̄)` and
`(i_L, L, L̄)`)** (§8.3, printed p. 76 / PDF p. 84):
for any algebraic extension `(i, K, L)` and any algebraic closures `(i_K, K, K̄)` and `(i_L, L, L̄)`,
there exist a `K`-monomorphism `σ : L →+* K̄` (`σ ∘ i = i_K`) and a field isomorphism
`e : L̄ ≃+* K̄` extending `σ` (`e ∘ i_L = σ`, hence `e ∘ i_L ∘ i = i_K`). -/
theorem exercise_8_8_isomorphism {K : Type u} {L : Type v} {Kbar : Type w} {Lbar : Type*}
    [Field K] [Field L] [Field Kbar] [Field Lbar]
    (extKL : FieldExtensionTriple K L)
    (extKKbar : FieldExtensionTriple K Kbar)
    (extLLbar : FieldExtensionTriple L Lbar)
    (halgKL : letI : Algebra K L := extKL.hom.toAlgebra; IsAlgebraicExtension K L)
    (hKbar : IsGarlingAlgebraicClosureTriple extKKbar)
    (hLbar : IsGarlingAlgebraicClosureTriple extLLbar) :
    ∃ (σ : L →+* Kbar) (e : Lbar ≃+* Kbar),
      σ.comp extKL.hom = extKKbar.hom ∧
      (∀ x : L, e (extLLbar.hom x) = σ x) ∧
      (∀ k : K, e (extLLbar.hom (extKL.hom k)) = extKKbar.hom k) := by
  obtain ⟨σ, _, hσ_comp⟩ := theorem_8_3_triple extKL extKKbar.mono halgKL hKbar.2
  let extLKbar : FieldExtensionTriple L Kbar := FieldExtensionTriple.ofRingHom σ
  have hLKbar_cl : IsGarlingAlgebraicClosureTriple extLKbar := by
    refine ⟨?_, hKbar.2⟩
    let _ : Algebra L Kbar := σ.toAlgebra
    let _ : Algebra K Kbar := extKKbar.hom.toAlgebra
    have halg_KKbar : IsAlgebraicExtension K Kbar := hKbar.1
    intro z
    obtain ⟨p, hp0, hpz⟩ := halg_KKbar z
    refine ⟨p.map extKL.hom, (Polynomial.map_ne_zero_iff extKL.mono).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (σ.comp extKL.hom) z p = 0
    rw [hσ_comp]
    exact hpz
  obtain ⟨e, he_comm⟩ := theorem_8_4_ringEquiv hLbar hLKbar_cl
  refine ⟨σ, e, hσ_comp, he_comm, fun k => ?_⟩
  rw [he_comm (extKL.hom k)]
  exact RingHom.congr_fun hσ_comp k

/-- **Exercise 8.8, Non-algebraic counterexample** (§8.3, printed p. 76 / PDF p. 84):
the hypothesis that `L : K` is algebraic cannot be dropped — for `ℂ : ℚ`, `ℂ` is an algebraic
closure of `ℂ` and `GarlingAlgebraicNumbers` is an algebraic closure of `ℚ`, yet
`GarlingAlgebraicNumbers ≠ ⊤` in `ℂ` and `GarlingAlgebraicNumbers` is not even abstractly
ring-isomorphic (or equipollent) to `ℂ` (`IsEmpty (GarlingAlgebraicNumbers ≃+* ℂ)`). -/
theorem exercise_8_8_non_algebraic_counterexample :
    ¬ IsAlgebraicExtension ℚ ℂ ∧
    IsGarlingAlgebraicClosure ℂ ℂ ∧
    IsGarlingAlgebraicClosure ℚ GarlingAlgebraicNumbers ∧
    GarlingAlgebraicNumbers ≠ (⊤ : Subfield ℂ) ∧
    IsEmpty (GarlingAlgebraicNumbers ≃+* ℂ) := by
  have hnot_alg : ¬ IsAlgebraicExtension ℚ ℂ := complex_not_isGarlingAlgebraicClosure_rat.1
  have hCC : IsGarlingAlgebraicClosure ℂ ℂ :=
    ⟨fun z => ⟨Polynomial.X - Polynomial.C z, Polynomial.X_sub_C_ne_zero z, by simp⟩,
      complex_isGarlingAlgebraicallyClosed⟩
  have hQA : IsGarlingAlgebraicClosure ℚ GarlingAlgebraicNumbers :=
    garlingAlgebraicNumbers_isGarlingAlgebraicClosure.1
  have hne_top : GarlingAlgebraicNumbers ≠ (⊤ : Subfield ℂ) := by
    intro htop
    apply hnot_alg
    intro z
    have hz : z ∈ GarlingAlgebraicNumbers := htop ▸ Subfield.mem_top z
    exact hz
  have hempty : IsEmpty (GarlingAlgebraicNumbers ≃+* ℂ) := by
    refine ⟨fun e => ?_⟩
    have hcntA : Countable GarlingAlgebraicNumbers := exercise_4_7_countable hQA.1
    have hcntC : Countable ℂ := e.symm.injective.countable
    have hcntR : Countable ℝ := Complex.ofReal_injective.countable
    obtain ⟨_, hnot_cnt_trans⟩ := exercise_4_7_exists_transcendental_real
    exact hnot_cnt_trans (Set.to_countable _)
  exact ⟨hnot_alg, hCC, hQA, hne_top, hempty⟩

/-- **Exercise 8.8** (§8.3, printed p. 76 / PDF p. 84 — held in `QUEUE.md`):
*"Suppose that `L : K` is algebraic. In what sense is it true that `L̄ = K̄`?"*

Bundles all three exact senses (`exercise_8_8_tower_iff`, `exercise_8_8_ambient_subfield_eq`, and
`exercise_8_8_isomorphism`) together with `exercise_8_8_non_algebraic_counterexample`. -/
theorem exercise_8_8 :
    (∀ (K L M : Type u) [Field K] [Field L] [Field M]
      [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M],
      IsAlgebraicExtension K L →
      (IsGarlingAlgebraicClosure L M ↔ IsGarlingAlgebraicClosure K M)) ∧
    (∀ (K L Ω : Type u) [Field K] [Field L] [Field Ω]
      [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω],
      IsGarlingAlgebraicallyClosed Ω →
      (algebraicSubfield L Ω = algebraicSubfield K Ω ↔ IsAlgebraicExtension K L)) ∧
    (∀ (K L Kbar Lbar : Type u) [Field K] [Field L] [Field Kbar] [Field Lbar]
      (extKL : FieldExtensionTriple K L)
      (extKKbar : FieldExtensionTriple K Kbar)
      (extLLbar : FieldExtensionTriple L Lbar),
      (letI : Algebra K L := extKL.hom.toAlgebra; IsAlgebraicExtension K L) →
      IsGarlingAlgebraicClosureTriple extKKbar →
      IsGarlingAlgebraicClosureTriple extLLbar →
      ∃ (σ : L →+* Kbar) (e : Lbar ≃+* Kbar),
        σ.comp extKL.hom = extKKbar.hom ∧
        (∀ x : L, e (extLLbar.hom x) = σ x)) ∧
    IsEmpty (GarlingAlgebraicNumbers ≃+* ℂ) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ halg => exercise_8_8_tower_iff halg,
   fun _ _ _ _ _ _ _ _ _ _ hΩ => ((exercise_8_8_ambient_subfield_eq).2 hΩ).2.2,
   fun _ _ _ _ _ _ _ _ extKL extKKbar extLLbar halg hK hL => by
     obtain ⟨σ, e, h1, h2, _⟩ := exercise_8_8_isomorphism extKL extKKbar extLLbar halg hK hL
     exact ⟨σ, e, h1, h2⟩,
   exercise_8_8_non_algebraic_counterexample.2.2.2.2⟩

/-! ## §8.4 Conclusions (printed p. 77, PDF p. 85) -/

/-- Supporting theorem for **§8.4 Conclusions** (printed p. 77 / PDF p. 85):
`x² + 1` is irreducible in `ℝ[x]`, and `ℂ : ℝ` is simultaneously a splitting field extension for
`x² + 1` and an algebraic closure of `ℝ`. -/
theorem conclusions_8_4_complex_over_real :
    Irreducible (Polynomial.X ^ 2 + 1 : ℝ[X]) ∧
    IsGarlingSplittingFieldExtension ℝ ℂ (Polynomial.X ^ 2 + 1) ∧
    IsGarlingAlgebraicClosure ℝ ℂ := by
  have hdeg_lt : (1 : ℝ[X]).natDegree < (Polynomial.X ^ 2 : ℝ[X]).natDegree := by
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
    omega
  have hf_deg : (Polynomial.X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg_lt, Polynomial.natDegree_X_pow]
  have hf_ne0 : (Polynomial.X ^ 2 + 1 : ℝ[X]) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hf_deg
    omega
  have hirr : Irreducible (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
    refine ⟨fun hu => absurd (Polynomial.natDegree_eq_zero_of_isUnit hu) (by omega), ?_⟩
    intro p q hpq
    have hp0 : p ≠ 0 := fun h => hf_ne0 (by rw [hpq, h, zero_mul])
    have hq0 : q ≠ 0 := fun h => hf_ne0 (by rw [hpq, h, mul_zero])
    by_cases hp_deg0 : p.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp_deg0]
      have hc0 : p.coeff 0 ≠ 0 := fun hc => hp0 (by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hp_deg0, hc, map_zero])
      exact IsUnit.map Polynomial.C (Ne.isUnit hc0)
    · by_cases hq_deg0 : q.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hq_deg0]
        have hc0 : q.coeff 0 ≠ 0 := fun hc => hq0 (by
          rw [Polynomial.eq_C_of_natDegree_eq_zero hq_deg0, hc, map_zero])
        exact IsUnit.map Polynomial.C (Ne.isUnit hc0)
      · exfalso
        have hsum := Polynomial.natDegree_mul hp0 hq0
        rw [← hpq, hf_deg] at hsum
        have hp_deg1 : p.natDegree = 1 := by omega
        have hp_lin : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
          ext k
          rcases k with _ | _ | k
          · simp
          · simp
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
            simp
        have ha0 : p.coeff 1 ≠ 0 := by
          intro ha
          apply Polynomial.leadingCoeff_ne_zero.mpr hp0
          rw [Polynomial.leadingCoeff, hp_deg1, ha]
        let r : ℝ := -p.coeff 0 / p.coeff 1
        have hp_eval : p.eval r = 0 := by
          conv_lhs => rw [hp_lin]
          simp [r, mul_div_cancel₀ _ ha0]
        have hf_eval := congrArg (Polynomial.eval r) hpq
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_mul, hp_eval, zero_mul] at hf_eval
        nlinarith [sq_nonneg r]
  have hsplit_ext : IsGarlingSplittingFieldExtension ℝ ℂ (Polynomial.X ^ 2 + 1) :=
    example_7_3_4_complex_over_real.2
  have halg_RC : IsAlgebraicExtension ℝ ℂ := by
    have _ : FiniteDimensional ℝ ℂ := inferInstance
    exact (isAlgebraicExtension_iff ℝ ℂ).mpr (Algebra.IsAlgebraic.of_finite ℝ ℂ)
  exact ⟨hirr, hsplit_ext, halg_RC, complex_isGarlingAlgebraicallyClosed⟩

end Garling.Chapter08
