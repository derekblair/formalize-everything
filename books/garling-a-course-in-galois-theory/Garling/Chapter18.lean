import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter10
import Garling.Chapter11
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Chapter 18: Transcendental elements and algebraic independence

Formalization of Chapter 18 (*Transcendental elements and algebraic independence*,
printed pp. 139–146 / PDF pp. 147–154) of D. J. H. Garling, *A Course in Galois Theory*
(Cambridge University Press, 1986), covering all five sections (`§18.1`–`§18.5`), all 11
main-text theorem/corollary items (`Theorem 18.1`–`Theorem 18.9` + 2 unnumbered `Corollary`
blocks [to `Theorem 18.6` and to `Theorem 18.8`]), all 7 numbered exercises (`Exercise 18.1`–
`Exercise 18.7`), and all unnumbered inline prose definitions and results in exact source order.

Note on source-fidelity holds (tracked in `QUEUE.md`):
- `Exercise 18.3` and `Exercise 18.4` (p. 141): non-propositional *"determine the fixed field"*
  prompts; both fixed fields (`K((α³ - 3α + 1)/(α² - α))` unconditionally and `K(α^(ord_p n))`)
  are kernel-proved as exact equalities.
- `Exercise 18.6` (p. 146): omits `char K ≠ 2` (mathematically false in every characteristic-2
  field, where `x² + y² = 1` forces `1 + y = x` and `u = (1 + y)/x = 1 ∈ K`); both the
  characteristic-2 counterexamples and the exact `char K ≠ 2` repair / `iff` are kernel-proved.
- `Exercise 18.7` (p. 146): prints the ill-typed hypothesis `Suppose if possible that K(x, y) = s.`
  for `K(x, y) = K(s)`; the repaired `(i)`, `(ii)` (divisibilities + polynomial Fermat
  impossibility over arbitrary `K` with `char K ∤ n`), and non-rationality of `xⁿ + yⁿ = 1`
  are all kernel-proved.
-/

namespace Garling.Chapter18

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter10 Garling.Chapter11
open scoped BigOperators Polynomial IntermediateField

universe u v w

/-! ## §18.1 Transcendental elements and algebraic independence (printed pp. 139–141, PDF pp. 147–149) -/

/-- Bridge between Chapter 4's `IsGarlingTranscendental K α` (recalled on p. 139) and Mathlib's
`Transcendental K α`. -/
theorem isGarlingTranscendental_iff {K L : Type*} [Field K] [Field L] [Algebra K L] (α : L) :
    IsGarlingTranscendental K α ↔ Transcendental K α :=
  Iff.rfl

/-- Helper: `aeval` on `IntermediateField.AdjoinSimple.gen K α` coerces to `evalRingHom K α` in `L`. -/
private theorem coe_aeval_adjoinSimple_gen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) (f : K[X]) :
    ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen K α) f :
      IntermediateField.adjoin K ({α} : Set L)) : L) = evalRingHom K α f := by
  change (IntermediateField.adjoin K ({α} : Set L)).val
    (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K α) f) = Polynomial.aeval α f
  rw [← Polynomial.aeval_algHom_apply]
  rfl

/-- **Theorem 18.1 (uniqueness among arbitrary ring homomorphisms)** (§18.1, printed p. 139 /
PDF p. 147): Any two ring homomorphisms `F₁, F₂ : K(x) →+* L` extending `E_α : K[x] →+* L` agree
on all of `K(x)` (matching Garling's proof via the equalizer subfield containing `K[x]`). -/
theorem theorem_18_1_unique_ringHom {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    {F₁ F₂ : RatFunc K →+* L}
    (h₁ : ∀ f : K[X], F₁ (algebraMap K[X] (RatFunc K) f) = evalRingHom K α f)
    (h₂ : ∀ f : K[X], F₂ (algebraMap K[X] (RatFunc K) f) = evalRingHom K α f) :
    F₁ = F₂ := by
  apply IsFractionRing.ringHom_ext (A := K[X])
  intro f
  rw [h₁ f, h₂ f]

/-- **Theorem 18.1 (`AlgEquiv` form)** (§18.1, printed p. 139 / PDF p. 147):
If `α ∈ L` is transcendental over `K`, then `E_α` extends uniquely to a `K`-algebra isomorphism
`F_α : K(x) ≃ₐ[K] K(α)`. -/
theorem theorem_18_1_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hα : IsGarlingTranscendental K α) :
    ∃! F : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({α} : Set L),
      ∀ f : K[X], (F (algebraMap K[X] (RatFunc K) f) : L) = evalRingHom K α f := by
  have hα' : Transcendental K α := (isGarlingTranscendental_iff α).mp hα
  refine ⟨RatFunc.algEquivOfTranscendental α hα', fun f => ?_, fun F' hF' => ?_⟩
  · rw [RatFunc.algEquivOfTranscendental_algebraMap]
    exact coe_aeval_adjoinSimple_gen α f
  · ext r
    have hcomp :
        ((IntermediateField.adjoin K ({α} : Set L)).val.toRingHom.comp F'.toRingHom) =
        ((IntermediateField.adjoin K ({α} : Set L)).val.toRingHom.comp
          (RatFunc.algEquivOfTranscendental α hα').toRingHom) := by
      apply theorem_18_1_unique_ringHom (α := α)
      · intro f; exact hF' f
      · intro f
        change ((RatFunc.algEquivOfTranscendental α hα' (algebraMap K[X] (RatFunc K) f) :
          IntermediateField.adjoin K ({α} : Set L)) : L) = evalRingHom K α f
        rw [RatFunc.algEquivOfTranscendental_algebraMap]
        exact coe_aeval_adjoinSimple_gen α f
    have hr := RingHom.congr_fun hcomp r
    exact hr

/-- **Theorem 18.1** (§18.1, printed p. 139 / PDF p. 147):
*"Suppose that `L:K` is an extension and that `α ∈ L` is transcendental over `K`. Then the
evaluation map `E_α` can be extended uniquely to an isomorphism `F_α` from the field `K(x)` of
rational expressions in `x` over `K` onto the field `K(α)`."* -/
theorem theorem_18_1 {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hα : IsGarlingTranscendental K α) :
    ∃! F : RatFunc K ≃+* IntermediateField.adjoin K ({α} : Set L),
      ∀ f : K[X], (F (algebraMap K[X] (RatFunc K) f) : L) = evalRingHom K α f := by
  have hα' : Transcendental K α := (isGarlingTranscendental_iff α).mp hα
  refine ⟨(RatFunc.algEquivOfTranscendental α hα').toRingEquiv, fun f => ?_, fun F' hF' => ?_⟩
  · change ((RatFunc.algEquivOfTranscendental α hα' (algebraMap K[X] (RatFunc K) f) :
      IntermediateField.adjoin K ({α} : Set L)) : L) = evalRingHom K α f
    rw [RatFunc.algEquivOfTranscendental_algebraMap]
    exact coe_aeval_adjoinSimple_gen α f
  · ext r
    have hcomp :
        ((IntermediateField.adjoin K ({α} : Set L)).val.toRingHom.comp F'.toRingHom) =
        ((IntermediateField.adjoin K ({α} : Set L)).val.toRingHom.comp
          (RatFunc.algEquivOfTranscendental α hα').toRingEquiv.toRingHom) := by
      apply theorem_18_1_unique_ringHom (α := α)
      · intro f; exact hF' f
      · intro f
        change ((RatFunc.algEquivOfTranscendental α hα' (algebraMap K[X] (RatFunc K) f) :
          IntermediateField.adjoin K ({α} : Set L)) : L) = evalRingHom K α f
        rw [RatFunc.algEquivOfTranscendental_algebraMap]
        exact coe_aeval_adjoinSimple_gen α f
    exact RingHom.congr_fun hcomp r

/-- **Theorem 18.1 (Section 3.2 explicit quotient companion)** (§18.1, p. 139):
Direct bridge to Chapter 3 §3.2's equivalence-class construction `GarlingFieldOfFractions K[X]`
cited on p. 139 l. 17: the explicit map `(f, g) ↦ f(α) * (g(α))⁻¹` descends uniquely to a
bijection `GarlingFieldOfFractions K[X] ≃ IntermediateField.adjoin K {α}` agreeing with `F_α`. -/
theorem theorem_18_1_garlingFieldOfFractions {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingTranscendental K α) :
    ∃ G : GarlingFieldOfFractions K[X] ≃ IntermediateField.adjoin K ({α} : Set L),
      ∀ (f : K[X]) (g : {s : K[X] // s ≠ 0}),
        (G (Quotient.mk (fracSetoid K[X]) (f, g)) : L) =
          evalRingHom K α f * (evalRingHom K α g.1)⁻¹ := by
  have hα' : Transcendental K α := (isGarlingTranscendental_iff α).mp hα
  let eFrac : GarlingFieldOfFractions K[X] ≃ FractionRing K[X] :=
    garlingFieldOfFractionsEquiv K[X]
  let eRF : FractionRing K[X] ≃ₐ[K[X]] RatFunc K :=
    IsLocalization.algEquiv (nonZeroDivisors K[X]) (FractionRing K[X]) (RatFunc K)
  let F : RatFunc K ≃+* IntermediateField.adjoin K ({α} : Set L) :=
    (RatFunc.algEquivOfTranscendental α hα').toRingEquiv
  refine ⟨eFrac.trans (eRF.toEquiv.trans F.toEquiv), fun f g => ?_⟩
  have heRF_alg : ∀ p : K[X],
      eRF (algebraMap K[X] (FractionRing K[X]) p) = algebraMap K[X] (RatFunc K) p := fun p =>
    eRF.commutes p
  have hF_alg : ∀ p : K[X],
      (F (algebraMap K[X] (RatFunc K) p) : L) = evalRingHom K α p := by
    intro p
    change ((RatFunc.algEquivOfTranscendental α hα' (algebraMap K[X] (RatFunc K) p) :
      IntermediateField.adjoin K ({α} : Set L)) : L) = evalRingHom K α p
    rw [RatFunc.algEquivOfTranscendental_algebraMap]
    exact coe_aeval_adjoinSimple_gen α p
  change (F (eRF (eFrac (Quotient.mk (fracSetoid K[X]) (f, g)))) : L) =
    evalRingHom K α f * (evalRingHom K α g.1)⁻¹
  have hmk : eFrac (Quotient.mk (fracSetoid K[X]) (f, g)) =
      algebraMap K[X] (FractionRing K[X]) f / algebraMap K[X] (FractionRing K[X]) g.1 := rfl
  rw [hmk, map_div₀, heRF_alg f, heRF_alg g.1, map_div₀]
  change ((F (algebraMap K[X] (RatFunc K) f) : IntermediateField.adjoin K ({α} : Set L)) : L) /
    ((F (algebraMap K[X] (RatFunc K) g.1) : IntermediateField.adjoin K ({α} : Set L)) : L) =
    evalRingHom K α f * (evalRingHom K α g.1)⁻¹
  rw [hF_alg f, hF_alg g.1, div_eq_mul_inv]

/-- Garling's multivariate *evaluation map* `E_A : K[x₁, ..., xₙ] →+* L` for an indexed `n`-tuple
`α : Fin n → L` (§18.1, printed pp. 139–140 / PDF pp. 147–148). -/
noncomputable def evalMvRingHom (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (α : Fin n → L) : MvPolynomial (Fin n) K →+* L :=
  (MvPolynomial.aeval α).toRingHom

/-- Garling's set-indexed multivariate *evaluation map* `E_A : K[X_A] →+* L` for a subset
`A ⊆ L` (§18.1, printed pp. 139–140 / PDF pp. 147–148). -/
noncomputable def evalSetRingHom (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) : MvPolynomial A K →+* L :=
  (MvPolynomial.aeval ((↑) : A → L)).toRingHom

@[simp]
theorem evalMvRingHom_X (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (α : Fin n → L) (i : Fin n) :
    evalMvRingHom K α (MvPolynomial.X i) = α i := by
  simp [evalMvRingHom]

@[simp]
theorem evalMvRingHom_C (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (α : Fin n → L) (c : K) :
    evalMvRingHom K α (MvPolynomial.C c) = algebraMap K L c := by
  simp [evalMvRingHom]

/-- Garling's inline prose definition of *algebraic independence* for a finite tuple
`(α₁, ..., αₙ)` (§18.1, printed p. 140 / PDF p. 148): `E_A : K[x₁, ..., xₙ] → L` is one-one. -/
def IsGarlingAlgIndepTuple (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (α : Fin n → L) : Prop :=
  Function.Injective (evalMvRingHom K α)

/-- `IsGarlingAlgIndepTuple K α` is definitionally Mathlib's `AlgebraicIndependent K α`. -/
theorem isGarlingAlgIndepTuple_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (α : Fin n → L) :
    IsGarlingAlgIndepTuple K α ↔ AlgebraicIndependent K α :=
  Iff.rfl

/-- Distinctness (`Function.Injective α`) follows automatically from `IsGarlingAlgIndepTuple K α`. -/
theorem IsGarlingAlgIndepTuple.injective {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {α : Fin n → L} (h : IsGarlingAlgIndepTuple K α) :
    Function.Injective α :=
  AlgebraicIndependent.injective h

/-- Garling's inline prose definition of *algebraic independence* for a finite subset `A ⊆ L`
(§18.1, printed p. 140 / PDF p. 148): `E_A` is one-one. -/
def IsGarlingAlgIndepFinite (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) (_hA : A.Finite) : Prop :=
  Function.Injective (evalSetRingHom K A)

/-- Garling's inline prose definition of *algebraic independence* for an arbitrary subset `S ⊆ L`
(§18.1, printed p. 140 / PDF p. 148): *"We say that an arbitrary subset `S` of `L` is algebraically
independent over `K` if each of its finite subsets is algebraically independent over `K`."* -/
def IsGarlingAlgebraicallyIndependent (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (S : Set L) : Prop :=
  ∀ A : Set L, A ⊆ S → (hA : A.Finite) → IsGarlingAlgIndepFinite K A hA

/-- Garling's negation *algebraically dependent over `K`* (§18.3, printed p. 144 / PDF p. 152). -/
def IsGarlingAlgebraicallyDependent (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (S : Set L) : Prop :=
  ¬ IsGarlingAlgebraicallyIndependent K S

/-- Bridge between Garling's finite-subset definition `IsGarlingAlgebraicallyIndependent K S` and
Mathlib's `AlgebraicIndepOn K id S` (`AlgebraicIndependent K ((↑) : S → L)`). -/
theorem isGarlingAlgebraicallyIndependent_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : Set L) :
    IsGarlingAlgebraicallyIndependent K S ↔ AlgebraicIndepOn K id S := by
  constructor
  · intro hS
    exact algebraicIndependent_of_finite S fun t ht hfin => hS t ht hfin
  · intro hS A hAS _
    exact hS.mono hAS

/-- The empty subset `∅ ⊆ L` is algebraically independent over `K` (needed for `n = 0` and
algebraic extensions in `Theorems 18.4–18.6`). -/
theorem isGarlingAlgebraicallyIndependent_empty (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] :
    IsGarlingAlgebraicallyIndependent K (∅ : Set L) := by
  rw [isGarlingAlgebraicallyIndependent_iff]
  exact (algebraicIndependent_empty_iff K L).mpr (algebraMap K L).injective

/-- Monotonicity of algebraic independence under subset inclusion. -/
theorem IsGarlingAlgebraicallyIndependent.mono {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S T : Set L} (hT : IsGarlingAlgebraicallyIndependent K T) (hST : S ⊆ T) :
    IsGarlingAlgebraicallyIndependent K S := by
  rw [isGarlingAlgebraicallyIndependent_iff] at hT ⊢
  exact hT.mono hST

/-- **§18.1 Prose Proposition (printed p. 140 / PDF p. 148):** *"Thus a one-point set `{α}` is
algebraically independent over `K` if and only if `α` is transcendental over `K`."* -/
theorem isGarlingAlgebraicallyIndependent_singleton_iff {K L : Type*} [Field K] [Field L]
    [Algebra K L] (α : L) :
    IsGarlingAlgebraicallyIndependent K ({α} : Set L) ↔ IsGarlingTranscendental K α := by
  rw [isGarlingAlgebraicallyIndependent_iff, isGarlingTranscendental_iff]
  simp [algebraicIndependent_unique_type_iff]

/-- Equivalence between set-based algebraic independence of `Set.range α` and tuple-based algebraic
independence `IsGarlingAlgIndepTuple K α` for any distinct tuple `α : Fin n → L`. -/
theorem isGarlingAlgebraicallyIndependent_range_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {α : Fin n → L} (hinj : Function.Injective α) :
    IsGarlingAlgebraicallyIndependent K (Set.range α) ↔ IsGarlingAlgIndepTuple K α := by
  rw [isGarlingAlgebraicallyIndependent_iff, isGarlingAlgIndepTuple_iff]
  exact algebraicIndependent_subtype_range hinj

/-- Helper: `IsFractionRing.liftAlgHom` lifts an injective `MvPolynomial ι K →ₐ[K] L` to a
`K`-algebra isomorphism `FractionRing (MvPolynomial ι K) ≃ₐ[K] IntermediateField.adjoin K (Set.range α)`. -/
private noncomputable def mvRatFuncEquivAdjoin {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (α : ι → L) (hα : AlgebraicIndependent K α) :
    FractionRing (MvPolynomial ι K) ≃ₐ[K] IntermediateField.adjoin K (Set.range α) := by
  let g : MvPolynomial ι K →ₐ[K] L := MvPolynomial.aeval α
  have hg_inj : Function.Injective g := hα
  let liftHom : FractionRing (MvPolynomial ι K) →ₐ[K] L := IsFractionRing.liftAlgHom hg_inj
  have hlift_inj : Function.Injective liftHom := liftHom.toRingHom.injective
  have hrange : liftHom.toRingHom.fieldRange =
      (IntermediateField.adjoin K (Set.range α)).toSubfield := by
    change (IsFractionRing.lift hg_inj : FractionRing (MvPolynomial ι K) →+* L).fieldRange = _
    rw [IsFractionRing.lift_fieldRange hg_inj]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro y ⟨p, rfl⟩
      change MvPolynomial.aeval α p ∈ IntermediateField.adjoin K (Set.range α)
      induction p using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.aeval_C]
        exact (IntermediateField.adjoin K (Set.range α)).algebraMap_mem c
      | add p q hp hq =>
        rw [map_add]
        exact (IntermediateField.adjoin K (Set.range α)).add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        exact (IntermediateField.adjoin K (Set.range α)).mul_mem hp
          (IntermediateField.subset_adjoin K (Set.range α) ⟨i, rfl⟩)
    · rw [← garlingFieldGenSubfield_eq_adjoin]
      apply sInf_le
      refine ⟨?_, ?_⟩
      · rintro _ ⟨c, rfl⟩
        exact Subfield.subset_closure ⟨MvPolynomial.C c, by simp [g]⟩
      · rintro _ ⟨i, rfl⟩
        exact Subfield.subset_closure ⟨MvPolynomial.X i, by simp [g]⟩
  have hmem : ∀ z : FractionRing (MvPolynomial ι K),
      liftHom z ∈ IntermediateField.adjoin K (Set.range α) := by
    intro z
    have hz : liftHom z ∈ liftHom.toRingHom.fieldRange := ⟨z, rfl⟩
    rw [hrange] at hz
    exact hz
  let toAdjoin : FractionRing (MvPolynomial ι K) →ₐ[K] IntermediateField.adjoin K (Set.range α) :=
    { toFun := fun z => ⟨liftHom z, hmem z⟩
      map_one' := Subtype.ext (map_one liftHom)
      map_mul' := fun x y => Subtype.ext (map_mul liftHom x y)
      map_zero' := Subtype.ext (map_zero liftHom)
      map_add' := fun x y => Subtype.ext (map_add liftHom x y)
      commutes' := fun k => Subtype.ext (liftHom.commutes k) }
  have hsurj : Function.Surjective toAdjoin := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ liftHom.toRingHom.fieldRange := by
      rw [hrange]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, Subtype.ext hz⟩
  have hinj' : Function.Injective toAdjoin := by
    intro z₁ z₂ hz
    exact hlift_inj (congrArg Subtype.val hz)
  exact AlgEquiv.ofBijective toAdjoin ⟨hinj', hsurj⟩

private theorem mvRatFuncEquivAdjoin_algebraMap {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (α : ι → L) (hα : AlgebraicIndependent K α) (f : MvPolynomial ι K) :
    (mvRatFuncEquivAdjoin α hα
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) : L) =
      MvPolynomial.aeval α f :=
  IsFractionRing.lift_algebraMap (K := FractionRing (MvPolynomial ι K))
    (g := (MvPolynomial.aeval α : MvPolynomial ι K →ₐ[K] L).toRingHom) hα f

/-- **Theorem 18.2 (`AlgEquiv` form)** (§18.1, printed p. 140 / PDF p. 148, proof omitted in text):
If `A = {α₁, ..., αₙ}` is algebraically independent over `K`, then `E_A` extends uniquely to a
`K`-algebra isomorphism `F_A : K(x₁, ..., xₙ) ≃ₐ[K] K(α₁, ..., αₙ)`. -/
theorem theorem_18_2_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {α : Fin n → L} (hα : IsGarlingAlgIndepTuple K α) :
    ∃! F : FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K]
        IntermediateField.adjoin K (Set.range α),
      ∀ f : MvPolynomial (Fin n) K,
        (F (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L) =
          evalMvRingHom K α f := by
  refine ⟨mvRatFuncEquivAdjoin α hα, fun f => mvRatFuncEquivAdjoin_algebraMap α hα f,
    fun F' hF' => ?_⟩
  ext z
  have hcomp :
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp F'.toRingHom) =
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp
        (mvRatFuncEquivAdjoin α hα).toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K)
    intro f
    change (F' (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L) =
      (mvRatFuncEquivAdjoin α hα
        (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L)
    rw [hF' f, mvRatFuncEquivAdjoin_algebraMap α hα f]
    rfl
  exact RingHom.congr_fun hcomp z

/-- **Theorem 18.2** (§18.1, printed p. 140 / PDF p. 148, proof omitted in text):
*"Suppose that `L:K` is an extension and that `A = {α₁, ..., αₙ}` is algebraically independent
over `K`. Then the evaluation map `E_A` can be extended uniquely to an isomorphism `F_A` from
the field `K(x₁, ..., xₙ)` of rational expressions in `x₁, ..., xₙ` onto the field
`K(α₁, ..., αₙ)`."* -/
theorem theorem_18_2 {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {α : Fin n → L} (hα : IsGarlingAlgIndepTuple K α) :
    ∃! F : FractionRing (MvPolynomial (Fin n) K) ≃+*
        IntermediateField.adjoin K (Set.range α),
      ∀ f : MvPolynomial (Fin n) K,
        (F (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L) =
          evalMvRingHom K α f := by
  refine ⟨(mvRatFuncEquivAdjoin α hα).toRingEquiv,
    fun f => mvRatFuncEquivAdjoin_algebraMap α hα f, fun F' hF' => ?_⟩
  ext z
  have hcomp :
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp F'.toRingHom) =
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp
        (mvRatFuncEquivAdjoin α hα).toRingEquiv.toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K)
    intro f
    change (F' (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L) =
      (mvRatFuncEquivAdjoin α hα
        (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) f) : L)
    rw [hF' f, mvRatFuncEquivAdjoin_algebraMap α hα f]
    rfl
  exact RingHom.congr_fun hcomp z

private theorem theorem_18_2_general {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    {α : ι → L} (hα : AlgebraicIndependent K α) :
    ∃! F : FractionRing (MvPolynomial ι K) ≃+*
        IntermediateField.adjoin K (Set.range α),
      ∀ f : MvPolynomial ι K,
        (F (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) : L) =
          MvPolynomial.aeval α f := by
  refine ⟨(mvRatFuncEquivAdjoin α hα).toRingEquiv,
    fun f => mvRatFuncEquivAdjoin_algebraMap α hα f, fun F' hF' => ?_⟩
  ext z
  have hcomp :
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp F'.toRingHom) =
      ((IntermediateField.adjoin K (Set.range α)).val.toRingHom.comp
        (mvRatFuncEquivAdjoin α hα).toRingEquiv.toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial ι K)
    intro f
    change (F' (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) : L) =
      (mvRatFuncEquivAdjoin α hα
        (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) : L)
    rw [hF' f, mvRatFuncEquivAdjoin_algebraMap α hα f]
  exact RingHom.congr_fun hcomp z

/-- **Theorem 18.2 (set-indexed form)** (§18.1, printed p. 140 / PDF p. 148):
For any subset `A ⊆ L` (in particular any finite `A`) which is algebraically independent over `K`,
`E_A : K[X_A] → L` extends uniquely to a field isomorphism `Frac(K[X_A]) ≃+* K(A)`. -/
theorem theorem_18_2_set {K L : Type*} [Field K] [Field L] [Algebra K L] {A : Set L}
    (hA : IsGarlingAlgebraicallyIndependent K A) :
    ∃! F : FractionRing (MvPolynomial A K) ≃+* IntermediateField.adjoin K A,
      ∀ f : MvPolynomial A K,
        (F (algebraMap (MvPolynomial A K) (FractionRing (MvPolynomial A K)) f) : L) =
          evalSetRingHom K A f := by
  have hA' : AlgebraicIndependent K ((↑) : A → L) :=
    (isGarlingAlgebraicallyIndependent_iff A).mp hA
  have h := theorem_18_2_general hA'
  have hrange : Set.range ((↑) : A → L) = A := Subtype.range_coe_subtype
  rw [hrange] at h
  exact h

/-- Key denominator-clearing bridge (Garling's p. 140 argument in `Theorem 18.3`):
For any subset `S ⊆ L` and `a ∈ L`, `a` is algebraic over the subalgebra `K[S]` (`Algebra.adjoin K S`)
if and only if `a` is algebraic over the generated subfield `K(S)` (`IntermediateField.adjoin K S`). -/
theorem isAlgebraic_algebraAdjoin_iff_intermediateFieldAdjoin
    {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) (a : L) :
    IsAlgebraic (Algebra.adjoin K S) a ↔
      IsGarlingAlgebraic (IntermediateField.adjoin K S) a := by
  constructor
  · rintro ⟨f, hf0, hfa⟩
    let inc : Algebra.adjoin K S →+* IntermediateField.adjoin K S :=
      (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K S)).toRingHom
    have hinc_inj : Function.Injective inc := Subalgebra.inclusion_injective _
    refine ⟨f.map inc, (Polynomial.map_ne_zero_iff hinc_inj).mpr hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hfa
  · rintro ⟨f, hf0, hfa⟩
    classical
    -- Express every coefficient of `f` as `p_j / q_j` with `p_j, q_j ∈ Algebra.adjoin K S`, `q_j ≠ 0`
    have hcoeff : ∀ j : ℕ, ∃ p q : Algebra.adjoin K S, (q : L) ≠ 0 ∧
        (f.coeff j : L) = (p : L) / (q : L) := by
      intro j
      obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.mp (f.coeff j).2
      by_cases hs0 : s = 0
      · refine ⟨0, 1, one_ne_zero, ?_⟩
        simp [hrs, hs0]
      · exact ⟨⟨r, hr⟩, ⟨s, hs⟩, hs0, hrs⟩
    choose p q hq_ne hcoeff_eq using hcoeff
    let N : Finset ℕ := Finset.range (f.natDegree + 1)
    let Q : Algebra.adjoin K S := ∏ j ∈ N, q j
    have hQ_ne : (Q : L) ≠ 0 := by
      rw [show (Q : L) = ∏ j ∈ N, (q j : L) from map_prod (Algebra.adjoin K S).val q N]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => hq_ne j
    let l : ℕ → Algebra.adjoin K S := fun j =>
      if j ∈ N then p j * ∏ k ∈ N.erase j, q k else 0
    have hl_val : ∀ j ∈ N, (l j : L) = (Q : L) * (f.coeff j : L) := by
      intro j hj
      simp only [l, hj, ↓reduceIte]
      have hQ_split : (Q : L) = (q j : L) * ∏ k ∈ N.erase j, (q k : L) := by
        rw [show (Q : L) = ∏ k ∈ N, (q k : L) from map_prod (Algebra.adjoin K S).val q N]
        exact (Finset.mul_prod_erase N (fun k => (q k : L)) hj).symm
      rw [show ((p j * ∏ k ∈ N.erase j, q k : Algebra.adjoin K S) : L) =
            (p j : L) * ∏ k ∈ N.erase j, (q k : L) by
          simp]
      rw [hQ_split, hcoeff_eq j]
      field_simp [hq_ne j]
    let g : (Algebra.adjoin K S)[X] := ∑ j ∈ N, Polynomial.monomial j (l j)
    have hg_coeff : ∀ j, g.coeff j = l j := by
      intro j
      simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      by_cases hj : j ∈ N
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj; simp [hbj]
        · intro h; exact absurd hj h
      · rw [Finset.sum_eq_zero]
        · simp [l, hj]
        · intro b hb; simp [show b ≠ j from fun h => hj (h ▸ hb)]
    have hg0 : g ≠ 0 := by
      intro hz
      have hnd_mem : f.natDegree ∈ N := Finset.mem_range.mpr (Nat.lt_succ_self _)
      have hnd_zero : l f.natDegree = 0 := by
        rw [← hg_coeff f.natDegree, hz, Polynomial.coeff_zero]
      have hnd_L : (l f.natDegree : L) = 0 := by rw [hnd_zero]; rfl
      rw [hl_val f.natDegree hnd_mem] at hnd_L
      rcases mul_eq_zero.mp hnd_L with hQ0 | hlc0
      · exact hQ_ne hQ0
      · exact Polynomial.leadingCoeff_ne_zero.mpr hf0 (Subtype.ext hlc0)
    have hga : Polynomial.aeval a g = 0 := by
      rw [show Polynomial.aeval a g = ∑ j ∈ N, (l j : L) * a ^ j by
        simp only [g, map_sum, Polynomial.aeval_monomial]
        rfl]
      have hsum_eq : (∑ j ∈ N, (l j : L) * a ^ j) =
          (Q : L) * ∑ j ∈ N, (f.coeff j : L) * a ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hl_val j hj, mul_assoc]
      rw [hsum_eq]
      have hf_eval : ∑ j ∈ N, (f.coeff j : L) * a ^ j = 0 := by
        have h1 : Polynomial.aeval a f = ∑ j ∈ N, (f.coeff j : L) * a ^ j := by
          rw [Polynomial.aeval_eq_sum_range]
          rfl
        rw [← h1, hfa]
      rw [hf_eval, mul_zero]
    exact ⟨g, hg0, hga⟩

/-- Transcendental counterpart of `isAlgebraic_algebraAdjoin_iff_intermediateFieldAdjoin`. -/
theorem isGarlingTranscendental_intermediateFieldAdjoin_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) (a : L) :
    IsGarlingTranscendental (IntermediateField.adjoin K S) a ↔
      Transcendental (Algebra.adjoin K S) a :=
  not_congr (isAlgebraic_algebraAdjoin_iff_intermediateFieldAdjoin S a).symm

/-- Algebraicity of the whole extension `L : K(S)` coincides with `Algebra.IsAlgebraic K[S] L`. -/
theorem isAlgebraicExtension_intermediateFieldAdjoin_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) :
    IsAlgebraicExtension (IntermediateField.adjoin K S) L ↔
      Algebra.IsAlgebraic (Algebra.adjoin K S) L := by
  constructor
  · intro h
    exact ⟨fun a => (isAlgebraic_algebraAdjoin_iff_intermediateFieldAdjoin S a).mpr (h a)⟩
  · intro h a
    exact (isAlgebraic_algebraAdjoin_iff_intermediateFieldAdjoin S a).mp (h.isAlgebraic a)

/-- Helper: inserting one element `a ∉ S` preserves algebraic independence iff `a` is transcendental
over `K(S)`. -/
theorem isGarlingAlgebraicallyIndependent_insert_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] {S : Set L} {a : L} (ha : a ∉ S) :
    IsGarlingAlgebraicallyIndependent K (insert a S) ↔
      IsGarlingAlgebraicallyIndependent K S ∧
      IsGarlingTranscendental (IntermediateField.adjoin K S) a := by
  rw [isGarlingAlgebraicallyIndependent_iff, isGarlingAlgebraicallyIndependent_iff,
    isGarlingTranscendental_intermediateFieldAdjoin_iff]
  have h := AlgebraicIndepOn.insert_iff (R := K) (x := (id : L → L)) ha
  generalize hT : (id : L → L) '' S = T at h
  have hTS : T = S := hT.symm.trans (Set.image_id S)
  subst hTS
  exact h

/-- **Theorem 18.3** (§18.1, printed p. 140 / PDF p. 148; proof pp. 140–141 / PDF pp. 148–149):
*"Suppose that `L:K` is an extension and that `α₁, ..., αₙ` are distinct elements of `L`.
Let `K₀ = K`, `K_i = K(α₁, ..., α_i)` for `1 ≤ i ≤ n`. Then `A = {α₁, ..., αₙ}` is algebraically
independent over `K` if and only if `α_i` is transcendental over `K_{i-1}`, for `1 ≤ i ≤ n`."* -/
theorem theorem_18_3 {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    {α : Fin n → L} (hα : Function.Injective α) :
    let K_step : ℕ → IntermediateField K L :=
      fun i => IntermediateField.adjoin K {x : L | ∃ j : Fin n, (j : ℕ) < i ∧ x = α j}
    K_step 0 = ⊥ ∧
    (IsGarlingAlgebraicallyIndependent K (Set.range α) ↔
      ∀ i : Fin n, IsGarlingTranscendental (K_step i.1) (α i)) := by
  intro K_step
  have hK0 : K_step 0 = ⊥ := by
    simp [K_step]
  refine ⟨hK0, ?_⟩
  let S : ℕ → Set L := fun k => {x : L | ∃ j : Fin n, (j : ℕ) < k ∧ x = α j}
  have hSn : S n = Set.range α := by
    ext x
    simp only [S, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨j, _, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, j.2, rfl⟩
  have hstep : ∀ k (hk : k ≤ n),
      IsGarlingAlgebraicallyIndependent K (S k) ↔
        ∀ (j : Fin n), (j : ℕ) < k → IsGarlingTranscendental (K_step j.1) (α j) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hS0 : S 0 = ∅ := by ext x; simp [S]
      simp [hS0, isGarlingAlgebraicallyIndependent_empty]
    | succ k ih =>
      intro hkn
      let idx : Fin n := ⟨k, hkn⟩
      have hnotmem : α idx ∉ S k := by
        rintro ⟨j, hjk, hj_eq⟩
        have hjeq : j = idx := hα hj_eq.symm
        subst hjeq
        exact Nat.lt_irrefl k hjk
      have hSsucc : S (k + 1) = insert (α idx) (S k) := by
        ext x
        simp only [S, Set.mem_ofPred_eq, Set.mem_insert_iff]
        constructor
        · rintro ⟨j, hjk, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hlt | heq
          · exact Or.inr ⟨j, hlt, rfl⟩
          · exact Or.inl (congrArg α (Fin.ext heq))
        · rintro (rfl | ⟨j, hjk, rfl⟩)
          · exact ⟨idx, Nat.lt_succ_self k, rfl⟩
          · exact ⟨j, Nat.lt_succ_of_lt hjk, rfl⟩
      rw [hSsucc, isGarlingAlgebraicallyIndependent_insert_iff hnotmem, ih (Nat.le_of_succ_le hkn)]
      constructor
      · rintro ⟨hprev, hlast⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
        · exact hprev j hlt
        · have hjeq : j = idx := Fin.ext heq
          subst hjeq
          exact hlast
      · intro hall
        exact ⟨fun j hjk => hall j (Nat.lt_succ_of_lt hjk), hall idx (Nat.lt_succ_self k)⟩
  simpa [hSn] using hstep n le_rfl

/-! ### Exercises 18.1–18.4 (§18.1, printed p. 141, PDF p. 149) -/

/-- Helper: adjoining one more element to an intermediate field `M = K(S)` matches
`K(insert α S)` via the canonical `M`-algebra structure on `K(insert α S)`. -/
private theorem adjoin_insert_eq_adjoin_simple_over
    {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) (α : L) :
    (IntermediateField.adjoin (IntermediateField.adjoin K S) ({α} : Set L)).restrictScalars K =
      IntermediateField.adjoin K (insert α S) := by
  apply le_antisymm
  · rw [IntermediateField.restrictScalars_adjoin, IntermediateField.adjoin_le_iff]
    rintro x (hx | hxα)
    · exact IntermediateField.adjoin.mono K S (insert α S) (Set.subset_insert α S) hx
    · rw [Set.mem_singleton_iff.mp hxα]
      exact IntermediateField.subset_adjoin K (insert α S) (Set.mem_insert α S)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hxα | hxS)
    · rw [hxα]
      exact IntermediateField.mem_adjoin_simple_self _ α
    · exact (IntermediateField.adjoin (IntermediateField.adjoin K S) {α}).algebraMap_mem
        ⟨x, IntermediateField.subset_adjoin K S hxS⟩

/-- **Exercise 18.1 (arbitrary finite subset form)** (§18.1, printed p. 141 / PDF p. 149):
Suppose `A ⊆ L` is finite and algebraically independent over `K`, `β ∈ K(A)`, and `β ∉ K`.
Then `β` is transcendental over `K`.
*(Proved by induction on `|A|` using `Theorem 18.3` and Chapter 5's `Exercise 5.5` — note that
Garling p. 141 misprints the cross-reference as `(cf. Exercise 5.3)`.)* -/
theorem exercise_18_1_finset {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Finset L) (hA : IsGarlingAlgebraicallyIndependent K (A : Set L))
    {β : L} (hβ_mem : β ∈ IntermediateField.adjoin K (A : Set L))
    (hβ_not_K : β ∉ (⊥ : IntermediateField K L)) :
    IsGarlingTranscendental K β := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, IntermediateField.adjoin_empty] at hβ_mem
    exact False.elim (hβ_not_K hβ_mem)
  | @insert a S haS ih =>
    rw [Finset.coe_insert] at hA hβ_mem
    have haS' : a ∉ (S : Set L) := haS
    obtain ⟨hS_ind, ha_trans⟩ := (isGarlingAlgebraicallyIndependent_insert_iff haS').mp hA
    by_cases hβS : β ∈ IntermediateField.adjoin K (S : Set L)
    · exact ih hS_ind hβS
    · let M := IntermediateField.adjoin K (S : Set L)
      have hβ_in_Ma : β ∈ IntermediateField.adjoin M ({a} : Set L) := by
        have h := adjoin_insert_eq_adjoin_simple_over (K := K) (S : Set L) a
        change β ∈ (IntermediateField.adjoin M ({a} : Set L)).restrictScalars K
        rwa [h]
      have hβ_not_M : β ∉ (⊥ : IntermediateField M L) := by
        intro hbot
        obtain ⟨⟨m, hm⟩, hm_eq⟩ := IntermediateField.mem_bot.mp hbot
        have hm_eq' : m = β := hm_eq
        exact hβS (hm_eq' ▸ hm)
      have htrans_M : IsGarlingTranscendental M β :=
        (exercise_5_5_algebraic_and_transcendental ha_trans hβ_in_Ma hβ_not_M).2.2
      intro hβ_alg_K
      obtain ⟨f, hf0, hfβ⟩ := hβ_alg_K
      refine htrans_M ⟨f.map (algebraMap K M),
        (Polynomial.map_ne_zero_iff (algebraMap K M).injective).mpr hf0, ?_⟩
      rw [Polynomial.aeval_map_algebraMap]
      exact hfβ

/-- **Exercise 18.1 (arbitrary subset companion)** (§18.1, p. 141):
Every element `β ∈ K(S) \ K` of the field generated by an arbitrary (possibly infinite)
algebraically independent subset `S ⊆ L` is transcendental over `K`. -/
theorem exercise_18_1_set {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S : Set L} (hS : IsGarlingAlgebraicallyIndependent K S)
    {β : L} (hβ_mem : β ∈ IntermediateField.adjoin K S)
    (hβ_not_K : β ∉ (⊥ : IntermediateField K L)) :
    IsGarlingTranscendental K β := by
  obtain ⟨A, hAS, hβA⟩ := IntermediateField.exists_finset_of_mem_adjoin hβ_mem
  exact exercise_18_1_finset A (hS.mono hAS) hβA hβ_not_K

/-- **Exercise 18.1** (§18.1, printed p. 141 / PDF p. 149):
*"Suppose that `L:K` is an extension, and that `{α₁, ..., α_s}` is algebraically independent over
`K`. Show that if `β ∈ K(α₁, ..., α_s)` and `β ∉ K` then `β` is transcendental over `K`
(cf. Exercise 5.3 [sic: Exercise 5.5])."* -/
theorem exercise_18_1 {K L : Type*} [Field K] [Field L] [Algebra K L] {s : ℕ}
    {α : Fin s → L} (hα : IsGarlingAlgebraicallyIndependent K (Set.range α))
    {β : L} (hβ_mem : β ∈ IntermediateField.adjoin K (Set.range α))
    (hβ_not_K : β ∉ (⊥ : IntermediateField K L)) :
    IsGarlingTranscendental K β :=
  exercise_18_1_set hα hβ_mem hβ_not_K

/-- Helper: in a simple extension `L = K(α)`, a `K`-algebra automorphism `τ : L ≃ₐ[K] L` is
uniquely determined by `τ α`. -/
private theorem algEquiv_ext_of_adjoin_simple_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    {τ₁ τ₂ : L ≃ₐ[K] L} (h : τ₁ α = τ₂ α) : τ₁ = τ₂ := by
  ext x
  have hx : x ∈ IntermediateField.adjoin K ({α} : Set L) := hsimple ▸ IntermediateField.mem_top
  obtain ⟨f, g, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hx
  rw [map_div₀, map_div₀]
  have h1 : ∀ p : K[X], τ₁ (Polynomial.aeval α p) = Polynomial.aeval (τ₁ α) p := fun p =>
    (Polynomial.aeval_algHom_apply τ₁.toAlgHom α p).symm
  have h2 : ∀ p : K[X], τ₂ (Polynomial.aeval α p) = Polynomial.aeval (τ₂ α) p := fun p =>
    (Polynomial.aeval_algHom_apply τ₂.toAlgHom α p).symm
  rw [h1 f, h1 g, h2 f, h2 g, h]

/-- Helper: given `ad ≠ bc` in `K` and `α` transcendental over `K`, `cα + d ≠ 0`,
`β = (aα + b)/(cα + d)` is transcendental over `K`, and `K(β) = K(α)`. -/
private theorem mobius_generator_props {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hα : IsGarlingTranscendental K α) {a b c d : K} (hdet : a * d ≠ b * c) :
    let β : L := (algebraMap K L a * α + algebraMap K L b) /
      (algebraMap K L c * α + algebraMap K L d)
    algebraMap K L c * α + algebraMap K L d ≠ 0 ∧
    β ∉ (⊥ : IntermediateField K L) ∧
    IsGarlingTranscendental K β ∧
    IntermediateField.adjoin K ({β} : Set L) = IntermediateField.adjoin K ({α} : Set L) := by
  intro β
  have hlin_ne : ∀ u v : K, (u ≠ 0 ∨ v ≠ 0) → algebraMap K L u * α + algebraMap K L v ≠ 0 := by
    intro u v huv hz
    by_cases hu : u = 0
    · subst hu
      have hv : v ≠ 0 := huv.resolve_left (not_not.mpr rfl)
      simp only [map_zero, zero_mul, zero_add] at hz
      exact hv ((algebraMap K L).injective (hz.trans (map_zero _).symm))
    · refine hα ⟨Polynomial.C u * Polynomial.X + Polynomial.C v, ?_, ?_⟩
      · intro hp0
        have h1 := congrArg (fun p : K[X] => p.coeff 1) hp0
        simp [hu] at h1
      · simpa using hz
  have hcd_nz : c ≠ 0 ∨ d ≠ 0 := by
    by_contra hboth
    push Not at hboth
    exact hdet (by simp [hboth.1, hboth.2])
  have hden_ne : algebraMap K L c * α + algebraMap K L d ≠ 0 := hlin_ne c d hcd_nz
  have hβ_not_K : β ∉ (⊥ : IntermediateField K L) := by
    intro hbot
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
    have hmul : algebraMap K L a * α + algebraMap K L b =
        algebraMap K L k * (algebraMap K L c * α + algebraMap K L d) := by
      have hk' : β = algebraMap K L k := hk.symm
      rw [← hk']
      exact (div_mul_cancel₀ _ hden_ne).symm
    have hzero : algebraMap K L (a - k * c) * α + algebraMap K L (b - k * d) = 0 := by
      simp only [map_sub, map_mul]
      linear_combination hmul
    by_cases h1 : a - k * c ≠ 0 ∨ b - k * d ≠ 0
    · exact hlin_ne (a - k * c) (b - k * d) h1 hzero
    · push Not at h1
      have ha_eq : a = k * c := sub_eq_zero.mp h1.1
      have hb_eq : b = k * d := sub_eq_zero.mp h1.2
      apply hdet
      rw [ha_eq, hb_eq]
      ring
  have hβ_mem : β ∈ IntermediateField.adjoin K ({α} : Set L) := by
    dsimp only [β]
    refine div_mem ?_ ?_
    · exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self K α)) (IntermediateField.algebraMap_mem _ _)
    · exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self K α)) (IntermediateField.algebraMap_mem _ _)
  have hβ_trans : IsGarlingTranscendental K β :=
    (exercise_5_5_algebraic_and_transcendental hα hβ_mem hβ_not_K).2.2
  have hdetL : algebraMap K L a * algebraMap K L d - algebraMap K L b * algebraMap K L c ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact fun h0 => hdet (sub_eq_zero.mp ((algebraMap K L).injective (h0.trans (map_zero _).symm)))
  have hinv_den : algebraMap K L a - algebraMap K L c * β ≠ 0 := by
    have heq : algebraMap K L a - algebraMap K L c * β =
        (algebraMap K L a * algebraMap K L d - algebraMap K L b * algebraMap K L c) /
          (algebraMap K L c * α + algebraMap K L d) := by
      dsimp only [β]
      field_simp [hden_ne]
      ring
    rw [heq]
    exact div_ne_zero hdetL hden_ne
  have hα_eq : α = (algebraMap K L d * β - algebraMap K L b) /
      (algebraMap K L a - algebraMap K L c * β) := by
    rw [eq_div_iff hinv_den]
    have hβ_mul : β * (algebraMap K L c * α + algebraMap K L d) =
        algebraMap K L a * α + algebraMap K L b := div_mul_cancel₀ _ hden_ne
    apply mul_right_cancel₀ hden_ne
    linear_combination -(α * algebraMap K L c + algebraMap K L d) * hβ_mul
  have hα_mem : α ∈ IntermediateField.adjoin K ({β} : Set L) := by
    rw [hα_eq]
    refine div_mem ?_ ?_
    · exact sub_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self K β)) (IntermediateField.algebraMap_mem _ _)
    · exact sub_mem (IntermediateField.algebraMap_mem _ _)
        (mul_mem (IntermediateField.algebraMap_mem _ _)
          (IntermediateField.mem_adjoin_simple_self K β))
  have hadj_eq : IntermediateField.adjoin K ({β} : Set L) =
      IntermediateField.adjoin K ({α} : Set L) :=
    le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr hβ_mem)
      (IntermediateField.adjoin_simple_le_iff.mpr hα_mem)
  exact ⟨hden_ne, hβ_not_K, hβ_trans, hadj_eq⟩

/-- **Exercise 18.2** (§18.1, printed p. 141 / PDF p. 149):
*"Suppose that `K(α):K` is a simple extension and that `α` is transcendental over `K`. Show that
if `τ` is an automorphism of `K(α)` which fixes `K` then there exist `a, b, c` and `d` in `K`
with `ad ≠ bc` such that `τ(α) = (aα + b)/(cα + d)`. Conversely show that any such `a, b, c`
and `d` determine an automorphism of `K(α)` which fixes `K`."* -/
theorem exercise_18_2 {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : IsGarlingTranscendental K α) :
    (∀ τ : L ≃ₐ[K] L, ∃ a b c d : K, a * d ≠ b * c ∧
      τ α = (algebraMap K L a * α + algebraMap K L b) /
        (algebraMap K L c * α + algebraMap K L d)) ∧
    (∀ a b c d : K, a * d ≠ b * c →
      ∃! τ : L ≃ₐ[K] L,
        τ α = (algebraMap K L a * α + algebraMap K L b) /
          (algebraMap K L c * α + algebraMap K L d)) := by
  constructor
  · intro τ
    set β : L := τ α
    have hβ_not_K : β ∉ (⊥ : IntermediateField K L) := by
      intro hbot
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
      have hα_eq : α = algebraMap K L k := by
        apply τ.injective
        rw [τ.commutes k]
        exact hk.symm
      exact hα ⟨Polynomial.X - Polynomial.C k, Polynomial.X_sub_C_ne_zero k, by simp [hα_eq]⟩
    have hKβ_eq_top : IntermediateField.adjoin K ({β} : Set L) = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      have hy : τ.symm y ∈ IntermediateField.adjoin K ({α} : Set L) :=
        hsimple ▸ IntermediateField.mem_top
      obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K (τ.symm y)).mp hy
      have hy_eq : y = Polynomial.aeval β p / Polynomial.aeval β q := by
        have h1 := congrArg τ hpq
        rw [AlgEquiv.apply_symm_apply, map_div₀] at h1
        have hτae : ∀ r : K[X], τ (Polynomial.aeval α r) = Polynomial.aeval β r := fun r =>
          (Polynomial.aeval_algHom_apply τ.toAlgHom α r).symm
        rw [hτae p, hτae q] at h1
        exact h1
      exact (IntermediateField.mem_adjoin_simple_iff K y).mpr ⟨p, q, hy_eq⟩
    -- Represent `β` as `f(α)/g(α)` with `f, g ∈ K[X]` coprime via `RatFunc.algEquivOfTranscendental`
    have hα' : Transcendental K α := (isGarlingTranscendental_iff α).mp hα
    let eTop : IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K] L :=
      (IntermediateField.equivOfEq hsimple).trans IntermediateField.topEquiv
    let eRF : RatFunc K ≃ₐ[K] L := (RatFunc.algEquivOfTranscendental α hα').trans eTop
    let u : RatFunc K := eRF.symm β
    let f : K[X] := u.num
    let g : K[X] := u.denom
    have hβ_eq : β = Polynomial.aeval α f / Polynomial.aeval α g := by
      have hu : eRF u = β := eRF.apply_symm_apply β
      have h1 : (RatFunc.algEquivOfTranscendental α hα' u : L) =
          Polynomial.aeval α f / Polynomial.aeval α g :=
        RatFunc.algEquivOfTranscendental_apply α hα' u
      rw [← hu]
      exact h1
    have hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]) := by
      have hcop_m : IsCoprime f g := RatFunc.isCoprime_num_denom u
      refine ⟨⟨f, Set.mem_insert f {g}⟩, fun _ _ => one_dvd _, fun r hr => ?_⟩
      obtain ⟨s, t, hst⟩ := hcop_m
      have hr1 : r ∣ 1 := by
        rw [← hst]
        exact dvd_add (dvd_mul_of_dvd_right (hr f (Set.mem_insert f {g})) s)
          (dvd_mul_of_dvd_right (hr g (Set.mem_insert_of_mem f rfl)) t)
      exact hr1
    have h55 := exercise_5_5 hα hβ_not_K hcop hβ_eq
    have hβ_mem_Kα : β ∈ IntermediateField.adjoin K ({α} : Set L) :=
      hsimple ▸ IntermediateField.mem_top
    let inc : IntermediateField.adjoin K ({β} : Set L) →+*
        IntermediateField.adjoin K ({α} : Set L) :=
      Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr
        (Set.singleton_subset_iff.mpr hβ_mem_Kα))
    let _ : Algebra (IntermediateField.adjoin K ({β} : Set L))
        (IntermediateField.adjoin K ({α} : Set L)) := inc.toAlgebra
    have hdeg_eq : extDegree (IntermediateField.adjoin K ({β} : Set L))
        (IntermediateField.adjoin K ({α} : Set L)) =
        ((max f.natDegree g.natDegree : ℕ) : ℕ∞) := h55.2.2.2.2.2
    have hdeg_one : extDegree (IntermediateField.adjoin K ({β} : Set L))
        (IntermediateField.adjoin K ({α} : Set L)) = 1 := by
      have hEq : IntermediateField.adjoin K ({β} : Set L) =
          IntermediateField.adjoin K ({α} : Set L) := hKβ_eq_top.trans hsimple.symm
      rw [extDegree_eq_one_iff_surjective]
      intro ⟨y, hy⟩
      exact ⟨⟨y, hEq ▸ hy⟩, rfl⟩
    have hmax1 : max f.natDegree g.natDegree = 1 := by
      have hnat : ((max f.natDegree g.natDegree : ℕ) : ℕ∞) = (1 : ℕ∞) :=
        hdeg_eq.symm.trans hdeg_one
      exact Nat.cast_injective hnat
    have hf_le1 : f.natDegree ≤ 1 := by omega
    have hg_le1 : g.natDegree ≤ 1 := by omega
    let a : K := f.coeff 1
    let b : K := f.coeff 0
    let c : K := g.coeff 1
    let d : K := g.coeff 0
    have hf_eq : f = Polynomial.C a * Polynomial.X + Polynomial.C b := by
      ext k
      rcases k with _ | _ | k
      · simp [b]
      · simp [a]
      · have hlt : f.natDegree < k + 2 := by omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    have hg_eq : g = Polynomial.C c * Polynomial.X + Polynomial.C d := by
      ext k
      rcases k with _ | _ | k
      · simp [d]
      · simp [c]
      · have hlt : g.natDegree < k + 2 := by omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    have hdet : a * d ≠ b * c := by
      intro hdet_eq
      by_cases hc0 : c = 0
      · have hd0 : d ≠ 0 := by
          intro hd_eq
          have hg0 : g = 0 := by simp [hg_eq, hc0, hd_eq]
          exact RatFunc.denom_ne_zero u hg0
        have ha0 : a = 0 := by
          have : a * d = 0 := by simpa [hc0] using hdet_eq
          exact (mul_eq_zero.mp this).resolve_right hd0
        have hf0 : f.natDegree = 0 := by rw [hf_eq, ha0]; simp
        have hg0 : g.natDegree = 0 := by rw [hg_eq, hc0]; simp
        omega
      · have hcf_eq : Polynomial.C c * f = Polynomial.C a * g := by
          rw [hf_eq, hg_eq, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul,
            ← map_mul, ← map_mul, mul_comm c a, mul_comm c b, ← hdet_eq]
        have heval_eq : algebraMap K L c * Polynomial.aeval α f =
            algebraMap K L a * Polynomial.aeval α g := by
          have h := congrArg (Polynomial.aeval α) hcf_eq
          simpa using h
        have hgα_ne : Polynomial.aeval α g ≠ 0 := h55.2.2.2.1
        have hcL_ne : algebraMap K L c ≠ 0 :=
          fun h0 => hc0 ((algebraMap K L).injective (h0.trans (map_zero _).symm))
        have hβ_in_K : β = algebraMap K L (a / c) := by
          rw [hβ_eq, map_div₀, div_eq_div_iff hgα_ne hcL_ne]
          linear_combination heval_eq
        exact hβ_not_K (hβ_in_K ▸ (⊥ : IntermediateField K L).algebraMap_mem _)
    refine ⟨a, b, c, d, hdet, ?_⟩
    rw [hβ_eq, hf_eq, hg_eq]
    simp
  · intro a b c d hdet
    obtain ⟨_, _, hβ_trans, hadj_eq⟩ := mobius_generator_props hα hdet
    have hα' : Transcendental K α := (isGarlingTranscendental_iff α).mp hα
    set β : L := (algebraMap K L a * α + algebraMap K L b) /
      (algebraMap K L c * α + algebraMap K L d)
    have hβ_trans' : Transcendental K β := (isGarlingTranscendental_iff β).mp hβ_trans
    have hKβ_top : IntermediateField.adjoin K ({β} : Set L) = ⊤ := hadj_eq.trans hsimple
    let eα : RatFunc K ≃ₐ[K] L :=
      (RatFunc.algEquivOfTranscendental α hα').trans
        ((IntermediateField.equivOfEq hsimple).trans IntermediateField.topEquiv)
    let eβ : RatFunc K ≃ₐ[K] L :=
      (RatFunc.algEquivOfTranscendental β hβ_trans').trans
        ((IntermediateField.equivOfEq hKβ_top).trans IntermediateField.topEquiv)
    let τ : L ≃ₐ[K] L := eα.symm.trans eβ
    have hτα : τ α = β := by
      have h1 : eα.symm α = (RatFunc.X : RatFunc K) := by
        apply eα.injective
        rw [eα.apply_symm_apply]
        symm
        change ((RatFunc.algEquivOfTranscendental α hα' (RatFunc.X : RatFunc K) :
          IntermediateField.adjoin K ({α} : Set L)) : L) = α
        exact RatFunc.algEquivOfTranscendental_X α hα'
      change eβ (eα.symm α) = β
      rw [h1]
      change ((RatFunc.algEquivOfTranscendental β hβ_trans' (RatFunc.X : RatFunc K) :
        IntermediateField.adjoin K ({β} : Set L)) : L) = β
      exact RatFunc.algEquivOfTranscendental_X β hβ_trans'
    exact ⟨τ, hτα, fun τ' hτ' => algEquiv_ext_of_adjoin_simple_eq_top hsimple (hτ'.trans hτα.symm)⟩

/-- **Exercise 18.2 (`IsFieldAutomorphism` / `FixesBaseField` companion)** (§18.1, p. 141):
Exact bridge to Chapter 4 §4.5's `IsFieldAutomorphism` and `FixesBaseField` predicates. -/
theorem exercise_18_2_ringHom {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : IsGarlingTranscendental K α) :
    (∀ τ : L →+* L, IsFieldAutomorphism τ → FixesBaseField K τ →
      ∃ a b c d : K, a * d ≠ b * c ∧
        τ α = (algebraMap K L a * α + algebraMap K L b) /
          (algebraMap K L c * α + algebraMap K L d)) ∧
    (∀ a b c d : K, a * d ≠ b * c →
      ∃! τ : L →+* L, IsFieldAutomorphism τ ∧ FixesBaseField K τ ∧
        τ α = (algebraMap K L a * α + algebraMap K L b) /
          (algebraMap K L c * α + algebraMap K L d)) := by
  have h182 := exercise_18_2 hsimple hα
  constructor
  · intro τ hauto hfix
    let e : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective τ hauto) hfix
    exact h182.1 e
  · intro a b c d hdet
    obtain ⟨e, he, he_uniq⟩ := h182.2 a b c d hdet
    refine ⟨e.toRingHom, ⟨⟨e.injective, e.surjective⟩, fun k => e.commutes k, he⟩, ?_⟩
    rintro τ ⟨hauto, hfix, hτα⟩
    let e' : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective τ hauto) hfix
    have heq : e' = e := he_uniq e' hτα
    ext x
    exact congrArg (fun φ : L ≃ₐ[K] L => φ x) heq

/-- Helper: general fixed-field identification lemma combining `Chapter05.exercise_5_5`,
`Chapter11.corollary_to_theorem_11_1`, `Chapter11.theorem_11_3`, and `Chapter04.theorem_4_2`.
If `σ : L ≃ₐ[K] L` has finite order `d ≥ 1` on `L = K(α)` (`α` transcendental over `K`),
`w = f(α)/g(α) ∈ K(α) \ K` is fixed by `σ` with `f, g ∈ K[X]` relatively prime and
`max (deg f) (deg g) = d`, then the fixed field of `σ` equals `K(w)`. -/
private theorem fixedField_eq_adjoin_of_order_eq_max_deg
    {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : IsGarlingTranscendental K α)
    (σ : L ≃ₐ[K] L) {d : ℕ} (hd_pos : 0 < d)
    (hord : orderOf σ = d)
    {w : L} {f g : K[X]}
    (hw_fix : σ w = w)
    (hw_not_K : w ∉ (⊥ : IntermediateField K L))
    (hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]))
    (hw_eq : w = Polynomial.aeval α f / Polynomial.aeval α g)
    (hmax : max f.natDegree g.natDegree = d) :
    garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L)) =
      (IntermediateField.adjoin K ({w} : Set L)).toSubfield ∧
    IntermediateField.fixedField (Subgroup.zpowers σ) =
      IntermediateField.adjoin K ({w} : Set L) := by
  let G : Subgroup (GarlingAut L) := Subgroup.zpowers σ.toRingEquiv
  have hord_ring : orderOf σ.toRingEquiv = d := by
    let emb : (L ≃ₐ[K] L) →* GarlingAut L :=
      { toFun := fun e => e.toRingEquiv
        map_one' := by ext x; rfl
        map_mul' := fun _ _ => by ext x; rfl }
    have hemb_inj : Function.Injective emb := fun e₁ e₂ h => by
      ext x; exact RingEquiv.congr_fun h x
    rw [← hord]
    exact orderOf_injective emb hemb_inj σ
  have hfinG : Finite G := by
    have hzd : σ.toRingEquiv ^ (d : ℤ) = 1 := by
      rw [zpow_natCast, ← hord_ring, pow_orderOf_eq_one]
    refine Finite.of_surjective
      (fun i : Fin d => (⟨σ.toRingEquiv ^ (i : ℕ),
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i.1⟩ : G)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hd_z : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr hd_pos
    have hrem_nn : 0 ≤ k % (d : ℤ) := Int.emod_nonneg k (ne_of_gt hd_z)
    have hrem_lt : (k % (d : ℤ)).toNat < d := by
      have hlt := Int.emod_lt_of_pos k hd_z
      omega
    refine ⟨⟨(k % (d : ℤ)).toNat, hrem_lt⟩, Subtype.ext ?_⟩
    have hk_eq : k = (d : ℤ) * (k / (d : ℤ)) + k % (d : ℤ) :=
      (Int.mul_ediv_add_emod k (d : ℤ)).symm
    change σ.toRingEquiv ^ ((k % (d : ℤ)).toNat : ℕ) = σ.toRingEquiv ^ k
    rw [← zpow_natCast, Int.toNat_of_nonneg hrem_nn]
    conv_rhs => rw [hk_eq, zpow_add, zpow_mul, hzd, one_zpow, one_mul]
  have hcardG : Nat.card G = d := by
    rw [Nat.card_zpowers, hord_ring]
  have hphi_eq : garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L)) =
      garlingPhi (G : Set (GarlingAut L)) := by
    have hcl : Subgroup.closure ({σ.toRingEquiv} : Set (GarlingAut L)) = G :=
      (Subgroup.zpowers_eq_closure σ.toRingEquiv).symm
    rw [← hcl]
    exact corollary_to_theorem_11_1 {σ.toRingEquiv}
  let F : Subfield L := garlingPhi (G : Set (GarlingAut L))
  have h113 := theorem_11_3 G
  have hdeg_FL : extDegree F L = (d : ℕ∞) := by
    rw [← h113.2.1]
    simp only [setOrder, ENat.card_eq_coe_natCard, hcardG]
  -- Show `K(w) ≤ F`
  have hKw_le_F : (IntermediateField.adjoin K ({w} : Set L)).toSubfield ≤ F := by
    dsimp only [F]
    rw [← hphi_eq]
    rw [← garlingFieldGenSubfield_eq_adjoin]
    apply sInf_le
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k, rfl⟩ τ hτ
      rw [Set.mem_singleton_iff.mp hτ]
      exact σ.commutes k
    · intro x hx τ hτ
      rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hτ]
      exact hw_fix
  -- Compute `[L : K(w)] = d` via `Exercise 5.5`
  have h55 := exercise_5_5 hα hw_not_K hcop hw_eq
  let Kw := IntermediateField.adjoin K ({w} : Set L)
  let Kα := IntermediateField.adjoin K ({α} : Set L)
  have hdeg_Kw_L : extDegree Kw L = (d : ℕ∞) := by
    have hw_mem_Kα : w ∈ Kα := by
      show w ∈ IntermediateField.adjoin K ({α} : Set L)
      rw [hsimple]
      exact IntermediateField.mem_top
    let inc : Kw →+* Kα :=
      Subfield.inclusion (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hw_mem_Kα))
    let _ : Algebra Kw Kα := inc.toAlgebra
    let eKw : Kα ≃ₗ[Kw] L :=
      { toFun := fun x => (x : L)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨y, by
          show y ∈ IntermediateField.adjoin K ({α} : Set L)
          rw [hsimple]
          exact IntermediateField.mem_top⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun _ => rfl }
    have hfd_Kα : Module.Finite Kw Kα := (isFiniteExtension_iff_moduleFinite Kw Kα).mp h55.1
    have hfd_L : Module.Finite Kw L := Module.Finite.equiv eKw
    have hfr : Module.finrank Kw L = Module.finrank Kw Kα := eKw.finrank_eq.symm
    rw [extDegree_eq_finrank Kw L, hfr, ← extDegree_eq_finrank Kw Kα, h55.2.2.2.2.2, hmax]
  -- Tower law `Kw ≤ F ≤ L` gives `[F : Kw] = 1`, hence `Kw = F`
  let incKF : Kw.toSubfield →+* F := Subfield.inclusion hKw_le_F
  let _ : Algebra Kw F := incKF.toAlgebra
  have _ : IsScalarTower Kw F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htower := theorem_4_2 Kw F L
  rw [hdeg_Kw_L, hdeg_FL] at htower
  have hdeg_Kw_F : extDegree Kw F = 1 := by
    have hd_ne_zero : (d : ℕ∞) ≠ 0 := by exact_mod_cast hd_pos.ne'
    by_cases htop : extDegree Kw F = ⊤
    · rw [htop, ENat.mul_top hd_ne_zero] at htower
      exact False.elim (ENat.natCast_ne_top d htower)
    · lift extDegree Kw F to ℕ using htop with k hk
      rw [← Nat.cast_mul] at htower
      have hmul : d * k = d := Nat.cast_injective htower.symm
      have hk1 : k = 1 := Nat.eq_of_mul_eq_mul_left hd_pos (by omega)
      exact congrArg (fun m : ℕ => (m : ℕ∞)) hk1
  have hsurj : Function.Surjective (algebraMap Kw F) :=
    (extDegree_eq_one_iff_surjective Kw F).mp hdeg_Kw_F
  have hF_eq_Kw : F = Kw.toSubfield := by
    apply le_antisymm _ hKw_le_F
    intro x hxF
    obtain ⟨y, hy⟩ := hsurj ⟨x, hxF⟩
    have hyx : (y : L) = x := congrArg Subtype.val hy
    exact hyx ▸ y.2
  refine ⟨hphi_eq.trans hF_eq_Kw, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L)) := by
      intro τ hτ
      rw [Set.mem_singleton_iff.mp hτ]
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    rw [hphi_eq.trans hF_eq_Kw] at hx'
    exact hx'
  · intro hx ⟨g, hg⟩
    have hx' : x ∈ F := hF_eq_Kw ▸ hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgk : (σ ^ k).toRingEquiv = σ.toRingEquiv ^ k := by
      let emb : (L ≃ₐ[K] L) →* GarlingAut L :=
        { toFun := fun e => e.toRingEquiv
          map_one' := by ext y; rfl
          map_mul' := fun _ _ => by ext y; rfl }
      exact map_zpow emb σ k
    have hmem : (σ ^ k).toRingEquiv ∈ (G : Set (GarlingAut L)) := by
      rw [hgk]; exact Subgroup.zpow_mem G (Subgroup.mem_zpowers σ.toRingEquiv) k
    exact hx' (σ ^ k).toRingEquiv hmem

/-- **Exercise 18.3** (§18.1, printed p. 141 / PDF p. 149; `QUEUE.md` fidelity hold —
non-propositional *"determine the fixed field of σ"* prompt):
*"Suppose that `K(α):K` is a simple extension and that `α` is transcendental over `K`. Let `σ`
be the automorphism of `K(α)` which fixes `K` and sends `α` to `1/(1 - α)`. Verify that `σ³` is
the identity, and determine the fixed field of `σ`."*

Over every field `K` (including characteristics `2` and `3`), `σ` exists uniquely, has exact
order `3` (`σ³ = 1`, `σ ≠ 1`, `σ² ≠ 1`), and its fixed field is `K((α³ - 3α + 1)/(α² - α))`. -/
theorem exercise_18_3 {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : IsGarlingTranscendental K α) :
    ∃! σ : L ≃ₐ[K] L, σ α = 1 / (1 - α) ∧
      σ ^ 3 = 1 ∧
      orderOf σ = 3 ∧
      garlingPhi ({σ.toRingEquiv} : Set (GarlingAut L)) =
        (IntermediateField.adjoin K ({(α ^ 3 - 3 * α + 1) / (α ^ 2 - α)} : Set L)).toSubfield ∧
      IntermediateField.fixedField (Subgroup.zpowers σ) =
        IntermediateField.adjoin K ({(α ^ 3 - 3 * α + 1) / (α ^ 2 - α)} : Set L) := by
  have hdet : (0 : K) * 1 ≠ 1 * (-1) := by simp
  obtain ⟨σ, hσα_raw, hσ_uniq⟩ := (exercise_18_2 hsimple hα).2 0 1 (-1) 1 hdet
  have hσα : σ α = 1 / (1 - α) := by
    simpa [sub_eq_add_neg, add_comm] using hσα_raw
  have hα_ne0 : α ≠ 0 := fun h0 =>
    hα ⟨Polynomial.X, Polynomial.X_ne_zero, by simp [h0]⟩
  have h1_sub_α_ne0 : 1 - α ≠ 0 := fun h0 =>
    hα ⟨Polynomial.C 1 - Polynomial.X, by
      intro hp0
      have := congrArg (fun p : K[X] => p.coeff 1) hp0
      simp [Polynomial.coeff_one] at this, by simpa using h0⟩
  have hσ2α : (σ ^ 2) α = (α - 1) / α := by
    change σ (σ α) = (α - 1) / α
    rw [hσα, map_div₀, map_one, map_sub, map_one, hσα]
    field_simp [h1_sub_α_ne0, hα_ne0]
    ring
  have hσ3α : (σ ^ 3) α = α := by
    change σ ((σ ^ 2) α) = α
    rw [hσ2α, map_div₀, map_sub, map_one, hσα]
    field_simp [h1_sub_α_ne0]
    ring
  have hσ3 : σ ^ 3 = 1 :=
    algEquiv_ext_of_adjoin_simple_eq_top hsimple (by simpa using hσ3α)
  have hσ_ne1 : σ ≠ 1 := by
    intro h1
    have hfix : 1 / (1 - α) = α := by rw [← hσα, h1]; rfl
    have hpoly : α ^ 2 - α + 1 = 0 := by
      have hmul : 1 = α * (1 - α) := (div_eq_iff h1_sub_α_ne0).mp hfix
      linear_combination hmul
    exact hα ⟨Polynomial.X ^ 2 - Polynomial.X + 1, by
      intro hp0
      have := congrArg (fun p : K[X] => p.coeff 2) hp0
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] at this,
      by simpa using hpoly⟩
  have hord : orderOf σ = 3 := by
    have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hσ_ne1
    · exact h3
  set w : L := (α ^ 3 - 3 * α + 1) / (α ^ 2 - α)
  have hw_sym : w = α + σ α + (σ ^ 2) α := by
    dsimp only [w]
    rw [hσα, hσ2α]
    have hfac : α ^ 2 - α = -(α * (1 - α)) := by ring
    rw [hfac]
    field_simp [h1_sub_α_ne0, hα_ne0]
    ring
  have hw_fix : σ w = w := by
    rw [hw_sym, map_add, map_add]
    have h1 : σ (σ α) = (σ ^ 2) α := rfl
    have h2 : σ ((σ ^ 2) α) = α := hσ3α
    rw [h1, h2]
    ring
  let f : K[X] := Polynomial.X ^ 3 - Polynomial.C 3 * Polynomial.X + 1
  let g : K[X] := Polynomial.X ^ 2 - Polynomial.X
  have hf_deg : f.natDegree = 3 := by
    have h3 : (Polynomial.X ^ 3 : K[X]).natDegree = 3 := Polynomial.natDegree_X_pow 3
    have hlt : (-Polynomial.C (3 : K) * Polynomial.X + 1).natDegree < 3 := by
      calc (-Polynomial.C (3 : K) * Polynomial.X + 1).natDegree
          ≤ max (-Polynomial.C (3 : K) * Polynomial.X).natDegree (1 : K[X]).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ max 1 0 := by
            refine max_le ?_ (by simp)
            calc (-Polynomial.C (3 : K) * Polynomial.X).natDegree
                ≤ (-Polynomial.C (3 : K)).natDegree + (Polynomial.X : K[X]).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ 0 + 1 := by simp
              _ = 1 := by omega
        _ < 3 := by omega
    have hfeq : f = Polynomial.X ^ 3 + (-Polynomial.C (3 : K) * Polynomial.X + 1) := by
      dsimp only [f]; ring
    rw [hfeq, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), h3]
  have hg_deg : g.natDegree = 2 := by
    have h2 : (Polynomial.X ^ 2 : K[X]).natDegree = 2 := Polynomial.natDegree_X_pow 2
    have hlt : (-Polynomial.X : K[X]).natDegree < 2 := by simp
    have hgeq : g = Polynomial.X ^ 2 + (-Polynomial.X) := by dsimp only [g]; ring
    rw [hgeq, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega), h2]
  have hmax3 : max f.natDegree g.natDegree = 3 := by rw [hf_deg, hg_deg]; decide
  have hcop_m : IsCoprime f g := by
    have h1 : IsCoprime Polynomial.X f :=
      ⟨-Polynomial.X ^ 2 + Polynomial.C 3, 1, by dsimp only [f]; ring⟩
    have h2 : IsCoprime (Polynomial.X - 1) f :=
      ⟨Polynomial.X ^ 2 + Polynomial.X - Polynomial.C 2, -1, by
        dsimp only [f]; simp only [map_ofNat]; ring⟩
    have hg_fac : g = Polynomial.X * (Polynomial.X - 1) := by dsimp only [g]; ring
    rw [hg_fac]
    exact (h1.mul_left h2).symm
  have hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]) := by
    refine ⟨⟨f, Set.mem_insert f {g}⟩, fun _ _ => one_dvd _, fun r hr => ?_⟩
    obtain ⟨s, t, hst⟩ := hcop_m
    rw [← hst]
    exact dvd_add (dvd_mul_of_dvd_right (hr f (Set.mem_insert f {g})) s)
      (dvd_mul_of_dvd_right (hr g (Set.mem_insert_of_mem f rfl)) t)
  have hw_eq : w = Polynomial.aeval α f / Polynomial.aeval α g := by
    dsimp only [w, f, g]
    simp [map_ofNat]
  have hw_not_K : w ∉ (⊥ : IntermediateField K L) := by
    intro hbot
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
    have hgα_ne : Polynomial.aeval α g ≠ 0 := fun h0 =>
      hα ⟨g, by intro hz; rw [hz, Polynomial.natDegree_zero] at hg_deg; omega, h0⟩
    have hmul : Polynomial.aeval α (f - Polynomial.C k * g) = 0 := by
      have hk' : w = algebraMap K L k := hk.symm
      rw [hw_eq] at hk'
      have hdiv := (div_eq_iff hgα_ne).mp hk'
      simp only [map_sub, map_mul, Polynomial.aeval_C]
      linear_combination hdiv
    have hdeg_lt : (Polynomial.C k * g).natDegree < f.natDegree := by
      calc (Polynomial.C k * g).natDegree
          ≤ (Polynomial.C k).natDegree + g.natDegree := Polynomial.natDegree_mul_le
        _ = 2 := by simp [hg_deg]
        _ < 3 := by omega
        _ = f.natDegree := hf_deg.symm
    have hne0 : f - Polynomial.C k * g ≠ 0 := by
      intro hz
      have hfeq : f = Polynomial.C k * g := sub_eq_zero.mp hz
      rw [hfeq] at hdeg_lt
      exact lt_irrefl _ hdeg_lt
    exact hα ⟨f - Polynomial.C k * g, hne0, hmul⟩
  obtain ⟨hphi, hff⟩ := fixedField_eq_adjoin_of_order_eq_max_deg hsimple hα σ
    (by decide : 0 < 3) hord hw_fix hw_not_K hcop hw_eq hmax3
  refine ⟨σ, ⟨hσα, hσ3, hord, hphi, hff⟩, ?_⟩
  rintro σ' ⟨hσ'α, _, _, _, _⟩
  exact hσ_uniq σ' (by simpa [sub_eq_add_neg, add_comm] using hσ'α)

/-- **Exercise 18.4** (§18.1, printed p. 141 / PDF p. 149; `QUEUE.md` fidelity hold —
non-propositional *"Determine the fixed field of τ"* prompt):
*"Suppose that `K(α):K` is a simple extension, that `α` is transcendental over `K`, and that
`char K` is an odd prime `p`. Suppose that `1 < n < p`. Let `τ` be the automorphism of `K(α)`
which fixes `K` and sends `α` to `nα`. Determine the fixed field of `τ`."*

Setting `d = orderOf (n : K)` (= `orderOf (n : ZMod p)`), we have `2 ≤ d`, `d ∣ p - 1`,
`orderOf τ = d`, and the fixed field of `τ` is `K(α^d)`. -/
theorem exercise_18_4 {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hsimple : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (hα : IsGarlingTranscendental K α)
    {p n : ℕ} (hchar : ringChar K = p) (hp : Nat.Prime p) (_hp_odd : p ≠ 2)
    (hn1 : 1 < n) (hnp : n < p) :
    let d : ℕ := orderOf (n : K)
    d = orderOf (n : ZMod p) ∧
    2 ≤ d ∧
    d ∣ p - 1 ∧
    ∃! τ : L ≃ₐ[K] L, τ α = (n : L) * α ∧
      orderOf τ = d ∧
      garlingPhi ({τ.toRingEquiv} : Set (GarlingAut L)) =
        (IntermediateField.adjoin K ({α ^ d} : Set L)).toSubfield ∧
      IntermediateField.fixedField (Subgroup.zpowers τ) =
        IntermediateField.adjoin K ({α ^ d} : Set L) := by
  have : CharP K p := hchar ▸ ringChar.charP K
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let φ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hφ_inj : Function.Injective φ := φ.injective
  have hφ_n : φ (n : ZMod p) = (n : K) := by simp [φ]
  have hd_eq : orderOf (n : K) = orderOf (n : ZMod p) := by
    rw [← hφ_n]
    exact orderOf_injective φ.toMonoidHom hφ_inj (n : ZMod p)
  have hn_mod_ne0 : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hnp
  have hn_K_ne0 : (n : K) ≠ 0 := by
    rw [← hφ_n]
    exact fun h0 => hn_mod_ne0 (hφ_inj (h0.trans (map_zero φ).symm))
  have hn_K_ne1 : (n : K) ≠ 1 := by
    intro h1
    have hz : ((n - 1 : ℕ) : K) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, h1, sub_self]
    have hdvd : p ∣ n - 1 := (CharP.cast_eq_zero_iff K p (n - 1)).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
  have hfermat : (n : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hn_mod_ne0
  have hpowK : (n : K) ^ (p - 1) = 1 := by
    rw [← hφ_n, ← map_pow, hfermat, map_one]
  set d : ℕ := orderOf (n : K)
  have hd_dvd : d ∣ p - 1 := orderOf_dvd_of_pow_eq_one hpowK
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by have := hp.two_le; omega)
  have hd_ne1 : d ≠ 1 := fun h1 => hn_K_ne1 (orderOf_eq_one_iff.mp h1)
  have hd_ge2 : 2 ≤ d := by omega
  have hdet : (n : K) * 1 ≠ 0 * 0 := by simpa using hn_K_ne0
  obtain ⟨τ, hτα_raw, hτ_uniq⟩ := (exercise_18_2 hsimple hα).2 (n : K) 0 0 1 hdet
  have hτα : τ α = (n : L) * α := by
    simpa using hτα_raw
  have hτ_pow_α : ∀ k : ℕ, (τ ^ k) α = (n : L) ^ k * α := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, map_natCast, hτα]
      ring
  have hα_ne0 : α ≠ 0 := fun h0 =>
    hα ⟨Polynomial.X, Polynomial.X_ne_zero, by simp [h0]⟩
  have hτ_pow_eq_one_iff : ∀ k : ℕ, τ ^ k = 1 ↔ (n : K) ^ k = 1 := by
    intro k
    constructor
    · intro hk
      have h1 : (τ ^ k) α = α := by rw [hk]; rfl
      rw [hτ_pow_α k] at h1
      have h2 : ((n : L) ^ k - 1) * α = 0 := by linear_combination h1
      have h3 : (n : L) ^ k = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hα_ne0)
      apply (algebraMap K L).injective
      simpa using h3
    · intro hk
      apply algEquiv_ext_of_adjoin_simple_eq_top hsimple
      rw [hτ_pow_α k]
      have hkL : (n : L) ^ k = 1 := by
        simpa using congrArg (algebraMap K L) hk
      simp [hkL]
  have hord_τ : orderOf τ = d := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hτ_pow_eq_one_iff d).mpr (pow_orderOf_eq_one (n : K)))
    · exact orderOf_dvd_of_pow_eq_one ((hτ_pow_eq_one_iff (orderOf τ)).mp (pow_orderOf_eq_one τ))
  have hw_fix : τ (α ^ d) = α ^ d := by
    rw [map_pow, hτα, mul_pow]
    have hnd : (n : L) ^ d = 1 := by
      have h := congrArg (algebraMap K L) (pow_orderOf_eq_one (n : K))
      simpa only [map_pow, map_natCast, map_one] using h
    rw [hnd, one_mul]
  let f : K[X] := Polynomial.X ^ d
  let g : K[X] := 1
  have hcop : IsGarlingRelativelyPrime ({f, g} : Set K[X]) := by
    refine ⟨⟨f, Set.mem_insert f {g}⟩, fun _ _ => one_dvd _,
      fun r hr => hr g (Set.mem_insert_of_mem f rfl)⟩
  have hw_eq : α ^ d = Polynomial.aeval α f / Polynomial.aeval α g := by
    simp [f, g]
  have hmax : max f.natDegree g.natDegree = d := by
    simp [f, g]
  have hw_not_K : α ^ d ∉ (⊥ : IntermediateField K L) := by
    intro hbot
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
    have hk' : α ^ d = algebraMap K L k := hk.symm
    refine hα ⟨Polynomial.X ^ d - Polynomial.C k, ?_, by simp [hk']⟩
    intro hp0
    have hcoeff := congrArg (fun q : K[X] => q.coeff d) hp0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_C,
      show d ≠ 0 by omega, ↓reduceIte, sub_zero, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff
  obtain ⟨hphi, hff⟩ := fixedField_eq_adjoin_of_order_eq_max_deg hsimple hα τ
    hd_pos hord_τ hw_fix hw_not_K hcop hw_eq hmax
  refine ⟨hd_eq, hd_ge2, hd_dvd, τ, ⟨hτα, hord_τ, hphi, hff⟩, ?_⟩
  rintro τ' ⟨hτ'α, _, _, _⟩
  exact hτ_uniq τ' (by simpa using hτ'α)

/-- Small witness illustrating `Exercise 18.4`'s subtlety: for `p = 5, n = 4`, `ord_5(4) = 2 < 4 = p - 1`,
so the fixed field is `K(α²)` rather than `K(α⁴)`. -/
theorem exercise_18_4_non_primitive_root_witness :
    Nat.Prime 5 ∧ (5 : ℕ) ≠ 2 ∧ 1 < 4 ∧ 4 < 5 ∧ orderOf (4 : ZMod 5) = 2 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  have h2 : (4 : ZMod 5) ^ 2 = 1 := by decide
  have h1 : (4 : ZMod 5) ≠ 1 := by decide
  have hdvd : orderOf (4 : ZMod 5) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-! ## §18.2 Transcendence bases (printed pp. 141–143, PDF pp. 149–151) -/

/-- Garling's collection `ℐ` of all subsets of `L` which are algebraically independent over `K`
(§18.2, printed pp. 141–142 / PDF pp. 149–150). -/
def garlingAlgIndepCollection (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Set L) :=
  {S : Set L | IsGarlingAlgebraicallyIndependent K S}

/-- Garling's literal inline prose definition of a *transcendence basis* for `L` over `K`
(§18.2, printed pp. 141–142 / PDF pp. 149–150): *"We order `ℐ` by inclusion. An element `S` of
`ℐ` which is maximal in this ordering is called a **transcendence basis** for `L` over `K`."* -/
def IsGarlingTranscendenceBasis (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (S : Set L) : Prop :=
  IsGarlingMaximal (garlingAlgIndepCollection K L) (· ⊆ ·) S

/-- Bridge between Garling's `IsGarlingTranscendenceBasis K S` and Mathlib's
`IsTranscendenceBasis K ((↑) : S → L)`. -/
theorem isGarlingTranscendenceBasis_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : Set L) :
    IsGarlingTranscendenceBasis K S ↔ IsTranscendenceBasis K ((↑) : S → L) := by
  rw [IsGarlingTranscendenceBasis, IsGarlingMaximal, IsTranscendenceBasis,
    Subtype.range_coe_subtype]
  constructor
  · rintro ⟨hS, hmax⟩
    refine ⟨(isGarlingAlgebraicallyIndependent_iff S).mp hS, fun T hT hST => ?_⟩
    exact hmax T ((isGarlingAlgebraicallyIndependent_iff T).mpr hT) hST
  · rintro ⟨hS, hmax⟩
    refine ⟨(isGarlingAlgebraicallyIndependent_iff S).mpr hS, fun T hT hST => ?_⟩
    exact hmax T ((isGarlingAlgebraicallyIndependent_iff T).mp hT) hST

/-- **Theorem 18.4** (§18.2, printed p. 142 / PDF p. 150):
*"Suppose that `L:K` is an extension and that `S` is a subset of `L`. Then `S` is a
transcendence basis for `L` over `K` if and only if `S` is algebraically independent over `K`
and `L:K(S)` is algebraic."* -/
theorem theorem_18_4 {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) :
    IsGarlingTranscendenceBasis K S ↔
      IsGarlingAlgebraicallyIndependent K S ∧
      IsAlgebraicExtension (IntermediateField.adjoin K S) L := by
  rw [isGarlingTranscendenceBasis_iff, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic,
    isGarlingAlgebraicallyIndependent_iff, isAlgebraicExtension_intermediateFieldAdjoin_iff]
  have hrange : Set.range ((↑) : S → L) = S := Subtype.range_coe_subtype
  rw [hrange]
  rfl

/-- **Theorem 18.5** (§18.2, printed p. 142 / PDF p. 150; proof pp. 142–143 / PDF pp. 150–151):
*"Suppose that `L:K` is an extension, that `A` is a subset of `L` such that `L:K(A)` is algebraic
and that `C` is a subset of `A` which is algebraically independent over `K`. Then there exists a
transcendence basis `B` for `L` over `K` with `C ⊆ B ⊆ A`."*

Proved directly via Chapter 2's `zorn_lemma_set` (note that the poset always contains `C`, so it
is non-empty), `Corollary 2 to Theorem 4.6`, `Theorem 4.7`, and `Theorem 18.4`. -/
theorem theorem_18_5 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A C : Set L}
    (hA : IsAlgebraicExtension (IntermediateField.adjoin K A) L)
    (hCA : C ⊆ A)
    (hC : IsGarlingAlgebraicallyIndependent K C) :
    ∃ B : Set L, IsGarlingTranscendenceBasis K B ∧ C ⊆ B ∧ B ⊆ A := by
  let PSet : Set (Set L) := {B : Set L | C ⊆ B ∧ B ⊆ A ∧ IsGarlingAlgebraicallyIndependent K B}
  have hpo : IsGarlingPartialOrder PSet (· ⊆ ·) := inclusion_isGarlingPartialOrder PSet
  have hne : PSet.Nonempty := ⟨C, Set.Subset.rfl, hCA, hC⟩
  have hchains : ∀ 𝒞 : Set (Set L), IsGarlingChain PSet (· ⊆ ·) 𝒞 →
      ∃ U : Set L, IsGarlingUpperBound PSet (· ⊆ ·) 𝒞 U := by
    rintro 𝒞 ⟨h𝒞P, ⟨B₀, hB₀⟩, h𝒞tot⟩
    refine ⟨⋃₀ 𝒞, ⟨?_, ?_, ?_⟩, fun B hB => Set.subset_sUnion_of_mem hB⟩
    · exact (h𝒞P hB₀).1.trans (Set.subset_sUnion_of_mem hB₀)
    · exact Set.sUnion_subset fun B hB => (h𝒞P hB).2.1
    · rw [isGarlingAlgebraicallyIndependent_iff]
      refine algebraicIndependent_sUnion_of_directed ⟨B₀, hB₀⟩ ?_ fun B hB =>
        (isGarlingAlgebraicallyIndependent_iff B).mp (h𝒞P hB).2.2
      intro B₁ hB₁ B₂ hB₂
      rcases h𝒞tot B₁ hB₁ B₂ hB₂ with h12 | h21
      · exact ⟨B₂, hB₂, h12, Set.Subset.rfl⟩
      · exact ⟨B₁, hB₁, Set.Subset.rfl, h21⟩
  obtain ⟨B, ⟨hCB, hBA, hBind⟩, hBmax⟩ := zorn_lemma_set hpo hne hchains
  refine ⟨B, (theorem_18_4 B).mpr ⟨hBind, ?_⟩, hCB, hBA⟩
  -- Every `a ∈ A` is algebraic over `K(B)`
  have hA_alg : ∀ a ∈ A, IsGarlingAlgebraic (IntermediateField.adjoin K B) a := by
    intro a haA
    by_cases haB : a ∈ B
    · exact isAlgebraic_algebraMap (⟨a, IntermediateField.subset_adjoin K B haB⟩ :
        IntermediateField.adjoin K B)
    · by_contra htrans
      have hins_ind : IsGarlingAlgebraicallyIndependent K (insert a B) :=
        (isGarlingAlgebraicallyIndependent_insert_iff haB).mpr ⟨hBind, htrans⟩
      have hins_mem : insert a B ∈ PSet :=
        ⟨hCB.trans (Set.subset_insert a B), Set.insert_subset haA hBA, hins_ind⟩
      have heq : B = insert a B := hBmax (insert a B) hins_mem (Set.subset_insert a B)
      exact haB (heq ▸ Set.mem_insert a B)
  -- Hence `K(A)` is algebraic over `K(B)` (`Corollary 2 to Theorem 4.6`), and `L : K(B)` is
  -- algebraic by `Theorem 4.7`.
  let KB := IntermediateField.adjoin K B
  let KA := IntermediateField.adjoin K A
  have hKB_le_KA : KB ≤ KA := IntermediateField.adjoin.mono K B A hBA
  let _ : Algebra KB KA := (IntermediateField.inclusion hKB_le_KA).toRingHom.toAlgebra
  have _ : IsScalarTower KB KA L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hKA_alg : IsAlgebraicExtension KB KA := by
    have hall : IsAlgebraicExtension KB (IntermediateField.adjoin KB A) :=
      corollary_2_to_theorem_4_6 hA_alg
    intro ⟨x, hx⟩
    have hx' : x ∈ IntermediateField.adjoin KB A := by
      have hle : KA ≤ (IntermediateField.adjoin KB A).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        intro a ha
        exact IntermediateField.subset_adjoin KB A ha
      exact hle hx
    have h1 := hall ⟨x, hx'⟩
    obtain ⟨p, hp0, hpx⟩ := h1
    refine ⟨p, hp0, Subtype.ext ?_⟩
    have hv1 : Polynomial.aeval x p = 0 := by
      have hv := congrArg (IntermediateField.adjoin KB A).val hpx
      simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
      exact hv
    change (IsScalarTower.toAlgHom KB KA L) (Polynomial.aeval (⟨x, hx⟩ : KA) p) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hv1
  exact theorem_4_7 hA hKA_alg

/-- **§18.2 Prose Result 1 (printed p. 142 / PDF p. 150):**
*"Just as every vector space has a basis, so does every extension `L:K` have a transcendence
basis."* (Special case `C = ∅`, `A = Set.univ` of `Theorem 18.5`.) -/
theorem exists_transcendenceBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ∃ B : Set L, IsGarlingTranscendenceBasis K B := by
  have huniv : IsAlgebraicExtension (IntermediateField.adjoin K (Set.univ : Set L)) L := by
    intro a
    exact isAlgebraic_algebraMap
      (⟨a, IntermediateField.subset_adjoin K Set.univ trivial⟩ :
        IntermediateField.adjoin K (Set.univ : Set L))
  obtain ⟨B, hB, _, _⟩ :=
    theorem_18_5 huniv (Set.empty_subset Set.univ) (isGarlingAlgebraicallyIndependent_empty K)
  exact ⟨B, hB⟩

/-- Helper for §18.2 p. 143: if `K` is countable and `S ⊆ L` is countable, then `K(S)` is
countable. -/
theorem countable_adjoin_of_countable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Countable K] {S : Set L} (hS : S.Countable) :
    Countable (IntermediateField.adjoin K S) := by
  have : Countable S := hS.to_subtype
  have : Countable (S →₀ ℕ) := inferInstance
  have : Countable (MvPolynomial S K) := by
    change Countable (AddMonoidAlgebra K (S →₀ ℕ))
    exact inferInstance
  let f : MvPolynomial S K × MvPolynomial S K → L :=
    fun pq => MvPolynomial.aeval ((↑) : S → L) pq.1 / MvPolynomial.aeval ((↑) : S → L) pq.2
  have hsub : (IntermediateField.adjoin K S : Set L) ⊆ Set.range f := by
    intro x hx
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
    have hrange_aeval : (Algebra.adjoin K S : Set L) =
        Set.range (MvPolynomial.aeval ((↑) : S → L) : MvPolynomial S K → L) := by
      have h1 := Algebra.adjoin_range_eq_range_aeval K ((↑) : S → L)
      rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at h1
      exact congrArg SetLike.coe h1
    have hr' : r ∈ Set.range (MvPolynomial.aeval ((↑) : S → L) : MvPolynomial S K → L) := by
      rw [← hrange_aeval]; exact hr
    have hs' : s ∈ Set.range (MvPolynomial.aeval ((↑) : S → L) : MvPolynomial S K → L) := by
      rw [← hrange_aeval]; exact hs
    obtain ⟨p, hp⟩ := hr'
    obtain ⟨q, hq⟩ := hs'
    exact ⟨(p, q), by simp [f, hp, hq]⟩
  exact ((Set.countable_range f).mono hsub).to_subtype

/-- **§18.2 Prose Result 2 (printed p. 143 / PDF p. 151):**
*"Consider the extension `ℝ:ℚ`. If `S` is any countable subset of `ℝ` [printed slip: `ℚ`], `ℚ(S)`
is countable. If `ℝ:ℚ(S)` were algebraic, `ℝ` would be countable (Exercise 4.7). Thus any
transcendence basis for `ℝ` over `ℚ` must be uncountable."* -/
theorem real_over_rat_transcendenceBasis_uncountable {S : Set ℝ}
    (hS : IsGarlingTranscendenceBasis ℚ S) :
    ¬ S.Countable := by
  intro hcount
  have : Countable (IntermediateField.adjoin ℚ S) := countable_adjoin_of_countable hcount
  have halg : IsAlgebraicExtension (IntermediateField.adjoin ℚ S) ℝ :=
    ((theorem_18_4 S).mp hS).2
  have hR_count : Countable ℝ := exercise_4_7_countable halg
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hR_count)

/-- **§18.2 Prose Result 3 (printed p. 143 / PDF p. 151):**
*"Note that, on the other hand, it follows from Theorem 18.5 that if `L:K` is finitely generated
over `K` then there must be a finite transcendence basis for `L` over `K`."* -/
theorem exists_finite_transcendenceBasis_of_finitelyGenerated
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfg : IsFinitelyGeneratedExtension K L) :
    ∃ B : Set L, B.Finite ∧ IsGarlingTranscendenceBasis K B := by
  obtain ⟨A, hAfin, hAtop⟩ := hfg
  have hAalg : IsAlgebraicExtension (IntermediateField.adjoin K A) L := by
    intro a
    exact isAlgebraic_algebraMap (⟨a, hAtop ▸ IntermediateField.mem_top⟩ :
      IntermediateField.adjoin K A)
  obtain ⟨B, hB, _, hBA⟩ :=
    theorem_18_5 hAalg (Set.empty_subset A) (isGarlingAlgebraicallyIndependent_empty K)
  exact ⟨B, hAfin.subset hBA, hB⟩

/-! ### Exercise 18.5 (§18.2, printed p. 143, PDF p. 151) -/

/-- Helper for `Exercise 18.5`: if `E : K` is an algebraic intermediate field of `L : K`, then
any finite `K`-algebraically independent subset `B ⊆ L` remains algebraically independent over `E`. -/
private theorem isGarlingAlgebraicallyIndependent_finset_over_algebraic_intermediate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (hE : IsAlgebraicExtension K E)
    (B : Finset L) (hBind : IsGarlingAlgebraicallyIndependent K (B : Set L)) :
    IsGarlingAlgebraicallyIndependent E (B : Set L) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty]
    exact isGarlingAlgebraicallyIndependent_empty E
  | @insert b S hbS ih =>
    rw [Finset.coe_insert] at hBind ⊢
    have hbS' : b ∉ (S : Set L) := hbS
    obtain ⟨hS_K, hb_trans_KS⟩ := (isGarlingAlgebraicallyIndependent_insert_iff hbS').mp hBind
    have hS_E : IsGarlingAlgebraicallyIndependent E (S : Set L) := ih hS_K
    rw [isGarlingAlgebraicallyIndependent_insert_iff hbS']
    refine ⟨hS_E, ?_⟩
    intro hb_alg_ES
    let KS : IntermediateField K L := IntermediateField.adjoin K (S : Set L)
    let ES : IntermediateField E L := IntermediateField.adjoin E (S : Set L)
    let ESK : IntermediateField K L := ES.restrictScalars K
    have hKS_le_ESK : KS ≤ ESK := by
      rw [IntermediateField.adjoin_le_iff]
      intro s hs
      exact IntermediateField.subset_adjoin E (S : Set L) hs
    let _ : Algebra KS ESK := (IntermediateField.inclusion hKS_le_ESK).toRingHom.toAlgebra
    have _ : IsScalarTower KS ESK L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- Every element of `E` is algebraic over `K`, hence over `KS`, so `ESK : KS` is algebraic.
    have hE_alg_KS : ∀ e ∈ (E : Set L), IsGarlingAlgebraic KS e := by
      intro e he
      obtain ⟨p, hp0, hpe⟩ := hE ⟨e, he⟩
      refine ⟨p.map (algebraMap K KS),
        (Polynomial.map_ne_zero_iff (algebraMap K KS).injective).mpr hp0, ?_⟩
      rw [Polynomial.aeval_map_algebraMap]
      have hval := congrArg Subtype.val hpe
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] using hval
    have hESK_le : ESK ≤ (IntermediateField.adjoin KS (E : Set L)).restrictScalars K := by
      dsimp only [ESK, ES]
      rw [IntermediateField.restrictScalars_adjoin, IntermediateField.adjoin_le_iff]
      rintro x (hxE | hxS)
      · exact IntermediateField.subset_adjoin KS (E : Set L) hxE
      · exact (IntermediateField.adjoin KS (E : Set L)).algebraMap_mem
          ⟨x, IntermediateField.subset_adjoin K (S : Set L) hxS⟩
    have hESK_alg_KS : IsAlgebraicExtension KS ESK := by
      have hall : IsAlgebraicExtension KS (IntermediateField.adjoin KS (E : Set L)) :=
        corollary_2_to_theorem_4_6 hE_alg_KS
      intro ⟨x, hx⟩
      obtain ⟨p, hp0, hpx⟩ := hall ⟨x, hESK_le hx⟩
      refine ⟨p, hp0, Subtype.ext ?_⟩
      have h1 : Polynomial.aeval x p = 0 := by
        have hv := congrArg (IntermediateField.adjoin KS (E : Set L)).val hpx
        simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
        exact hv
      change (IsScalarTower.toAlgHom KS ESK L) (Polynomial.aeval (⟨x, hx⟩ : ESK) p) = 0
      rw [← Polynomial.aeval_algHom_apply]
      exact h1
    -- `b` is algebraic over `ESK` (same carrier as `ES`)
    have hb_alg_ESK : IsGarlingAlgebraic ESK b := hb_alg_ES
    -- Transitivity via `K(S) ≤ ESK ≤ ESK(b)` (`Theorem 4.7` + `Corollary 1 to Theorem 4.6`)
    have hb_alg_KS : IsGarlingAlgebraic KS b := by
      have h1 : IsAlgebraicExtension ESK (IntermediateField.adjoin ESK ({b} : Set L)) :=
        corollary_1_to_theorem_4_6 hb_alg_ESK
      have _ : IsScalarTower KS (IntermediateField.adjoin ESK ({b} : Set L)) L :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have htrans := theorem_4_7 h1 hESK_alg_KS
      obtain ⟨p, hp0, hpb⟩ := htrans (IntermediateField.AdjoinSimple.gen ESK b)
      refine ⟨p, hp0, ?_⟩
      have hv := congrArg
        (IsScalarTower.toAlgHom KS (IntermediateField.adjoin ESK ({b} : Set L)) L) hpb
      simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
      exact hv
    exact hb_trans_KS hb_alg_KS

/-- **Exercise 18.5** (§18.2, printed p. 143 / PDF p. 151):
*"Suppose that `L:K` is an extension, and that `L` is finitely generated over `K`. Show that the
field `K_a` of elements of `L` which are algebraic over `K` is finitely generated over `K`."*

Holds unconditionally over every field `K` (including imperfect fields of positive characteristic):
in fact `K_a : K` is finite, with `[K_a : K] ≤ [L : K(B)] < ∞` for any finite transcendence basis
`B` of `L : K`. -/
theorem exercise_18_5 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfg : IsFinitelyGeneratedExtension K L) :
    IsFiniteExtension K (algebraicIntermediateField K L) ∧
    IsFinitelyGeneratedExtension K (algebraicIntermediateField K L) := by
  classical
  obtain ⟨B, hBfin, hB⟩ := exists_finite_transcendenceBasis_of_finitelyGenerated hfg
  let KB := IntermediateField.adjoin K B
  have hL_alg_KB : IsAlgebraicExtension KB L := ((theorem_18_4 B).mp hB).2
  have hL_fg_KB : IsFinitelyGeneratedExtension KB L := by
    obtain ⟨A, hAfin, hAtop⟩ := hfg
    refine ⟨A, hAfin, eq_top_iff.mpr fun x _ => ?_⟩
    have hx : x ∈ IntermediateField.adjoin K A := hAtop ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K A ≤
        (IntermediateField.adjoin KB A).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      intro a ha
      exact IntermediateField.subset_adjoin KB A ha
    exact hle hx
  have hL_fin_KB : IsFiniteExtension KB L :=
    (theorem_4_6 KB L).1.mpr ⟨hL_alg_KB, hL_fg_KB⟩
  have : Module.Finite KB L := (isFiniteExtension_iff_moduleFinite KB L).mp hL_fin_KB
  let Ka := algebraicIntermediateField K L
  have hKa_alg : IsAlgebraicExtension K Ka := by
    intro ⟨x, hx⟩
    exact (isAlgebraic_algebraMap_iff (R := K) Subtype.val_injective).mp hx
  have hB_ind_Ka : IsGarlingAlgebraicallyIndependent Ka B := by
    have hB_K : IsGarlingAlgebraicallyIndependent K (hBfin.toFinset : Set L) := by
      simpa using ((theorem_18_4 B).mp hB).1
    simpa using isGarlingAlgebraicallyIndependent_finset_over_algebraic_intermediate
      Ka hKa_alg hBfin.toFinset hB_K
  -- Every finite `K`-linearly independent subset of `Ka` stays `KB`-linearly independent in `L`.
  have hcard_bound : ∀ s : Finset Ka,
      LinearIndependent K (fun x : s => (x : Ka)) → s.card ≤ Module.finrank KB L := by
    intro s hs_li
    have hs_KB : LinearIndependent KB (fun x : s => ((x : Ka) : L)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc_sum
      -- Clear denominators from `K[B]` (`Algebra.adjoin K B`)
      have hrat : ∀ x : s, ∃ p q : Algebra.adjoin K B, (q : L) ≠ 0 ∧
          (c x : L) = (p : L) / (q : L) := by
        intro x
        obtain ⟨r, hr, t, ht, hrt⟩ := IntermediateField.mem_adjoin_iff_div.mp (c x).2
        by_cases ht0 : t = 0
        · refine ⟨0, 1, one_ne_zero, ?_⟩
          simp [hrt, ht0]
        · exact ⟨⟨r, hr⟩, ⟨t, ht⟩, ht0, hrt⟩
      choose p q hq_ne hrat_eq using hrat
      let Q : Algebra.adjoin K B := ∏ y : s, q y
      have hQ_ne : (Q : L) ≠ 0 := by
        rw [show (Q : L) = ∏ y : s, (q y : L) from map_prod (Algebra.adjoin K B).val q Finset.univ]
        exact Finset.prod_ne_zero_iff.mpr fun y _ => hq_ne y
      let r : s → Algebra.adjoin K B := fun x =>
        p x * ∏ y ∈ Finset.univ.erase x, q y
      have hr_val : ∀ x : s, (r x : L) = (Q : L) * (c x : L) := by
        intro x
        have hQ_split : (Q : L) = (q x : L) * ∏ y ∈ Finset.univ.erase x, (q y : L) := by
          rw [show (Q : L) = ∏ y : s, (q y : L) from map_prod (Algebra.adjoin K B).val q Finset.univ]
          exact (Finset.mul_prod_erase Finset.univ (fun y => (q y : L)) (Finset.mem_univ x)).symm
        rw [show (r x : L) = (p x : L) * ∏ y ∈ Finset.univ.erase x, (q y : L) by
          simp [r]]
        rw [hQ_split, hrat_eq x]
        field_simp [hq_ne x]
      -- Express each `r x ∈ Algebra.adjoin K B` as `MvPolynomial.aeval ((↑) : B → L) (P x)`
      have hP_ex : ∀ x : s, ∃ P : MvPolynomial B K, MvPolynomial.aeval ((↑) : B → L) P = (r x : L) := by
        intro x
        have hrange := Algebra.adjoin_range_eq_range_aeval K ((↑) : B → L)
        rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at hrange
        have hmem : (r x : L) ∈ (MvPolynomial.aeval ((↑) : B → L) : MvPolynomial B K →ₐ[K] L).range := by
          rw [← hrange]
          exact (r x).2
        exact hmem
      choose P hP_eq using hP_ex
      -- Form `R = ∑ x, C x * map (algebraMap K Ka) (P x) ∈ MvPolynomial B Ka`
      let R : MvPolynomial B Ka :=
        ∑ x : s, MvPolynomial.C (x : Ka) * MvPolynomial.map (algebraMap K Ka) (P x)
      have hR_eval : MvPolynomial.aeval ((↑) : B → L) R = 0 := by
        simp only [R, map_sum, map_mul, MvPolynomial.aeval_C]
        have hterm : ∀ x : s,
            (algebraMap Ka L (x : Ka)) *
              MvPolynomial.aeval ((↑) : B → L) (MvPolynomial.map (algebraMap K Ka) (P x)) =
            (Q : L) * ((c x : L) * ((x : Ka) : L)) := by
          intro x
          have hmap : MvPolynomial.aeval ((↑) : B → L) (MvPolynomial.map (algebraMap K Ka) (P x)) =
              MvPolynomial.aeval ((↑) : B → L) (P x) := by
            rw [MvPolynomial.aeval_map_algebraMap]
          rw [hmap, hP_eq x, hr_val x]
          change ((x : Ka) : L) * ((Q : L) * (c x : L)) = (Q : L) * ((c x : L) * ((x : Ka) : L))
          ring
        rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum]
        have hcL : ∑ x : s, (c x : L) * ((x : Ka) : L) = 0 := by
          simpa [Algebra.smul_def] using hc_sum
        rw [hcL, mul_zero]
      have hR_zero : R = 0 :=
        ((isGarlingAlgebraicallyIndependent_iff B).mp hB_ind_Ka).eq_zero_of_aeval_eq_zero R hR_eval
      -- Extract coefficients of every monomial `m : B →₀ ℕ`
      have hP_zero : ∀ x : s, P x = 0 := by
        have hcoeff_zero : ∀ (m : B →₀ ℕ) (x : s), (P x).coeff m = 0 := by
          intro m
          have hm : R.coeff m = 0 := by rw [hR_zero]; rfl
          have hsum_m : ∑ x : s, ((P x).coeff m) • (x : Ka) = 0 := by
            rw [← hm]
            simp only [R, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
              MvPolynomial.coeff_map, Algebra.smul_def]
            refine Finset.sum_congr rfl fun x _ => mul_comm _ _
          exact (Fintype.linearIndependent_iff.mp hs_li) (fun x => (P x).coeff m) hsum_m
        intro x
        ext m
        exact hcoeff_zero m x
      intro x
      apply Subtype.ext
      have hrx0 : (r x : L) = 0 := by rw [← hP_eq x, hP_zero x, map_zero]
      rw [hr_val x] at hrx0
      exact (mul_eq_zero.mp hrx0).resolve_left hQ_ne
    have hle := hs_KB.fintype_card_le_finrank
    simpa using hle
  -- `Ka` has a finite `K`-basis (using Chapter 2 `exists_basis`), hence is finite and f.g. over `K`
  obtain ⟨ℬ, hℬ⟩ := exists_basis K Ka
  have hℬ_fin : ℬ.Finite := by
    by_contra hinf
    obtain ⟨s, hsℬ, hscard⟩ := Set.Infinite.exists_subset_card_eq hinf (Module.finrank KB L + 1)
    have hs_li : LinearIndependent K (fun x : s => (x : Ka)) :=
      (isLinearlyIndependent_iff _).mp (hℬ.1.mono hsℬ)
    have hle := hcard_bound s hs_li
    omega
  have hmod_fin : Module.Finite K Ka := by
    rw [Module.finite_def]
    exact ⟨hℬ_fin.toFinset, by simpa [Spans] using hℬ.2⟩
  have hfin : IsFiniteExtension K Ka := (isFiniteExtension_iff_moduleFinite K Ka).mpr hmod_fin
  exact ⟨hfin, ((theorem_4_6 K Ka).1.mp hfin).2⟩

/-- **Exercise 18.5 (`algebraicSubfield` companion)** (§18.2, p. 143):
Subfield formulation matching Chapter 4 §4.4's `algebraicSubfield K L` ($L_a$, denoted $K_a$
in `Exercise 18.5`): there exists a finite subset `A ⊆ K_a` generating `K_a` over `K`. -/
theorem exercise_18_5_subfield {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfg : IsFinitelyGeneratedExtension K L) :
    ∃ A : Set L, A.Finite ∧ A ⊆ (algebraicSubfield K L : Set L) ∧
      garlingFieldGenSubfield K A = algebraicSubfield K L := by
  obtain ⟨A₀, hA₀_fin, hA₀_top⟩ := (exercise_18_5 hfg).2
  let Ka := algebraicIntermediateField K L
  let A : Set L := ((↑) : Ka → L) '' A₀
  have hAfin : A.Finite := hA₀_fin.image _
  have hAsub : A ⊆ (algebraicSubfield K L : Set L) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  refine ⟨A, hAfin, hAsub, ?_⟩
  rw [garlingFieldGenSubfield_eq_adjoin]
  change (IntermediateField.adjoin K A).toSubfield = Ka.toSubfield
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr hAsub
  · intro x hx
    have hx₀ : (⟨x, hx⟩ : Ka) ∈ IntermediateField.adjoin K A₀ := hA₀_top ▸ IntermediateField.mem_top
    have hmap : x ∈ (IntermediateField.adjoin K A₀).map Ka.val := ⟨⟨x, hx⟩, hx₀, rfl⟩
    rw [IntermediateField.adjoin_map] at hmap
    exact hmap

/-! ## §18.3 Transcendence degree (printed pp. 143–144, PDF pp. 151–152) -/

/-- **Theorem 18.6** (§18.3, printed p. 143 / PDF p. 151; proof pp. 143–144 / PDF pp. 151–152):
*"Suppose that `L:K` is an extension, that `C = {c₁, ..., cᵣ}` is a subset of `L` (with `r`
distinct elements) which is algebraically independent over `K` and that `A = {a₁, ..., aₛ}` is
a subset of `L` (with `s` distinct elements) such that `L:K(A)` is algebraic. Then `r ≤ s`, and
there exists a set `D`, with `C ⊆ D ⊆ A ∪ C` such that `|D| = s` and `L:K(D)` is algebraic."*

Proved by induction on `r = C.card` directly following Garling's Steinitz exchange argument on
pp. 143–144 (handling both `c_r ∈ D_0` and `c_r ∉ D_0`). -/
theorem theorem_18_6 {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]
    (C A : Finset L)
    (hC : IsGarlingAlgebraicallyIndependent K (C : Set L))
    (hA : IsAlgebraicExtension (IntermediateField.adjoin K (A : Set L)) L) :
    C.card ≤ A.card ∧
    ∃ D : Finset L, C ⊆ D ∧ D ⊆ A ∪ C ∧ D.card = A.card ∧
      IsAlgebraicExtension (IntermediateField.adjoin K (D : Set L)) L := by
  induction hr : C.card generalizing C with
  | zero =>
    have hCe : C = ∅ := Finset.card_eq_zero.mp hr
    subst hCe
    exact ⟨Nat.zero_le _, A, Finset.empty_subset A, Finset.subset_union_left, rfl, hA⟩
  | succ r ih =>
    have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨c₀, hc₀C⟩ := hCne
    let C₀ : Finset L := C.erase c₀
    have hc₀_not_C₀ : c₀ ∉ C₀ := Finset.notMem_erase c₀ C
    have hC_eq : insert c₀ C₀ = C := Finset.insert_erase hc₀C
    have hC₀_card : C₀.card = r := by
      dsimp only [C₀]
      rw [Finset.card_erase_of_mem hc₀C, hr]
      omega
    have hC₀_ind : IsGarlingAlgebraicallyIndependent K (C₀ : Set L) :=
      hC.mono (by rw [← hC_eq, Finset.coe_insert]; exact Set.subset_insert _ _)
    obtain ⟨hr_le, D₀, hC₀D₀, hD₀_sub, hD₀_card, hD₀_alg⟩ := ih C₀ hC₀_ind hC₀_card
    have hc₀_trans_C₀ : IsGarlingTranscendental (IntermediateField.adjoin K (C₀ : Set L)) c₀ := by
      have hins : IsGarlingAlgebraicallyIndependent K (insert c₀ (C₀ : Set L)) := by
        rwa [← Finset.coe_insert, hC_eq]
      exact ((isGarlingAlgebraicallyIndependent_insert_iff hc₀_not_C₀).mp hins).2
    -- `D₀ \ C₀` is non-empty (otherwise `D₀ = C₀`, making `c₀` algebraic over `K(C₀)`).
    have hdiff_ne : (D₀ \ C₀).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
      have hD₀_eq_C₀ : D₀ = C₀ := Finset.Subset.antisymm hempty hC₀D₀
      rw [hD₀_eq_C₀] at hD₀_alg
      exact hc₀_trans_C₀ (hD₀_alg c₀)
    have hr1_le : r + 1 ≤ A.card := by
      have hsum : (D₀ \ C₀).card + C₀.card = D₀.card := Finset.card_sdiff_add_card_eq_card hC₀D₀
      have hpos : 0 < (D₀ \ C₀).card := Finset.card_pos.mpr hdiff_ne
      omega
    refine ⟨hr1_le, ?_⟩
    by_cases hc₀D₀ : c₀ ∈ D₀
    · -- Already `C = insert c₀ C₀ ⊆ D₀`, so `D = D₀` works directly!
      refine ⟨D₀, ?_, ?_, hD₀_card, hD₀_alg⟩
      · rw [← hC_eq]
        exact Finset.insert_subset hc₀D₀ hC₀D₀
      · refine hD₀_sub.trans ?_
        rw [← hC_eq]
        exact Finset.union_subset_union_right (Finset.subset_insert c₀ C₀)
    · -- `c₀ ∉ D₀`: form `E = insert c₀ D₀ = C ∪ (D₀ \ C₀)` and apply `Theorem 18.3`
      let B : Finset L := D₀ \ C₀
      have hdisj_CB : Disjoint C B := by
        rw [Finset.disjoint_left]
        intro x hxC hxB
        have hxD₀ := (Finset.mem_sdiff.mp hxB).1
        have hxnotC₀ := (Finset.mem_sdiff.mp hxB).2
        rw [← hC_eq, Finset.mem_insert] at hxC
        rcases hxC with rfl | hxC₀
        · exact hc₀D₀ hxD₀
        · exact hxnotC₀ hxC₀
      have hCB_eq : C ∪ B = insert c₀ D₀ := by
        ext x
        simp only [B, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, ← hC_eq]
        constructor
        · rintro ((rfl | hxC₀) | ⟨hxD₀, _⟩)
          · exact Or.inl rfl
          · exact Or.inr (hC₀D₀ hxC₀)
          · exact Or.inr hxD₀
        · rintro (rfl | hxD₀)
          · exact Or.inl (Or.inl rfl)
          · by_cases hxC₀ : x ∈ C₀
            · exact Or.inl (Or.inr hxC₀)
            · exact Or.inr ⟨hxD₀, hxC₀⟩
      let eC : Fin C.card ≃ C := C.equivFin.symm
      let eB : Fin B.card ≃ B := B.equivFin.symm
      let n := C.card + B.card
      let seq : Fin n → L := fun i =>
        if h : (i : ℕ) < C.card then (eC ⟨i.1, h⟩).1
        else (eB ⟨i.1 - C.card, by omega⟩).1
      have hseq_inj : Function.Injective seq := by
        intro i j hij
        by_cases hi : (i : ℕ) < C.card <;> by_cases hj : (j : ℕ) < C.card
        · simp only [seq, hi, hj, ↓reduceDIte] at hij
          have heq := eC.injective (Subtype.ext hij)
          have hval : i.1 = j.1 := congrArg (fun k : Fin C.card => k.1) heq
          exact Fin.ext hval
        · simp only [seq, hi, hj, ↓reduceDIte] at hij
          exact False.elim (Finset.disjoint_left.mp hdisj_CB (eC ⟨i.1, hi⟩).2
            (hij ▸ (eB ⟨j.1 - C.card, by omega⟩).2))
        · simp only [seq, hi, hj, ↓reduceDIte] at hij
          exact False.elim (Finset.disjoint_left.mp hdisj_CB (eC ⟨j.1, hj⟩).2
            (hij.symm ▸ (eB ⟨i.1 - C.card, by omega⟩).2))
        · simp only [seq, hi, hj, ↓reduceDIte] at hij
          have heq := eB.injective (Subtype.ext hij)
          have hval : i.1 - C.card = j.1 - C.card := congrArg Fin.val heq
          exact Fin.ext (by omega)
      have hseq_range : Set.range seq = (insert c₀ D₀ : Set L) := by
        rw [← Finset.coe_insert, ← hCB_eq, Finset.coe_union]
        ext x
        simp only [Set.mem_range, Set.mem_union, Finset.mem_coe]
        constructor
        · rintro ⟨i, rfl⟩
          by_cases hi : (i : ℕ) < C.card
          · simp only [seq, hi, ↓reduceDIte]
            exact Or.inl (eC ⟨i.1, hi⟩).2
          · simp only [seq, hi, ↓reduceDIte]
            exact Or.inr (eB ⟨i.1 - C.card, by omega⟩).2
        · rintro (hxC | hxB)
          · let k : Fin C.card := eC.symm ⟨x, hxC⟩
            refine ⟨⟨k.1, by omega⟩, ?_⟩
            simp [seq, k]
          · let k : Fin B.card := eB.symm ⟨x, hxB⟩
            refine ⟨⟨C.card + k.1, by omega⟩, ?_⟩
            have hnot : ¬ (C.card + k.1 < C.card) := by omega
            simp [seq, hnot, k]
      -- `insert c₀ D₀` is NOT algebraically independent over `K` (since `c₀` is algebraic over `K(D₀)`).
      have hE_dep : ¬ IsGarlingAlgebraicallyIndependent K (Set.range seq) := by
        intro hind
        rw [hseq_range] at hind
        have htr : IsGarlingTranscendental (IntermediateField.adjoin K (D₀ : Set L)) c₀ :=
          ((isGarlingAlgebraicallyIndependent_insert_iff hc₀D₀).mp hind).2
        exact htr (hD₀_alg c₀)
      -- By `Theorem 18.3`, some `seq i` is algebraic over `K(seq 0, ..., seq (i - 1))`.
      have h183 := (theorem_18_3 (K := K) hseq_inj).2
      have hex_alg : ∃ i : Fin n,
          IsGarlingAlgebraic (IntermediateField.adjoin K
            {x : L | ∃ j : Fin n, (j : ℕ) < i.1 ∧ x = seq j}) (seq i) := by
        by_contra hall
        push Not at hall
        exact hE_dep (h183.mpr hall)
      obtain ⟨i₀, hi₀_alg⟩ := hex_alg
      -- Necessarily `C.card ≤ i₀.1` because `{seq 0, ..., seq i₀} ⊆ C` would contradict `hC`.
      have hi₀_ge : C.card ≤ i₀.1 := by
        by_contra hlt
        push Not at hlt
        let S_prev : Set L := {x : L | ∃ j : Fin n, (j : ℕ) < i₀.1 ∧ x = seq j}
        have hnotmem : seq i₀ ∉ S_prev := by
          rintro ⟨j, hji, hjeq⟩
          have := hseq_inj hjeq.symm
          omega
        have hins_sub_C : insert (seq i₀) S_prev ⊆ (C : Set L) := by
          rintro x (rfl | ⟨j, hji, rfl⟩)
          · simp only [seq, hlt, ↓reduceDIte]
            exact (eC ⟨i₀.1, hlt⟩).2
          · have hjlt : (j : ℕ) < C.card := by omega
            simp only [seq, hjlt, ↓reduceDIte]
            exact (eC ⟨j.1, hjlt⟩).2
        have hins_ind : IsGarlingAlgebraicallyIndependent K (insert (seq i₀) S_prev) :=
          hC.mono hins_sub_C
        exact ((isGarlingAlgebraicallyIndependent_insert_iff hnotmem).mp hins_ind).2 hi₀_alg
      let a_t : L := seq i₀
      have ha_t_B : a_t ∈ B := by
        dsimp only [a_t, seq]
        have hnot : ¬ (i₀.1 < C.card) := by omega
        simp only [hnot, ↓reduceDIte]
        exact (eB ⟨i₀.1 - C.card, by omega⟩).2
      have ha_t_D₀ : a_t ∈ D₀ := (Finset.mem_sdiff.mp ha_t_B).1
      have ha_t_not_C : a_t ∉ C := Finset.disjoint_right.mp hdisj_CB ha_t_B
      let D : Finset L := (insert c₀ D₀).erase a_t
      have hC_sub_D : C ⊆ D := by
        intro x hxC
        refine Finset.mem_erase.mpr ⟨fun hxa => ha_t_not_C (hxa ▸ hxC), ?_⟩
        rw [← hCB_eq]
        exact Finset.mem_union_left B hxC
      have hD_sub : D ⊆ A ∪ C := by
        intro x hxD
        have hxE := Finset.mem_of_mem_erase hxD
        rw [Finset.mem_insert] at hxE
        rcases hxE with rfl | hxD₀
        · exact Finset.mem_union_right A hc₀C
        · have hxAC₀ := hD₀_sub hxD₀
          rw [Finset.mem_union] at hxAC₀ ⊢
          rcases hxAC₀ with hxA | hxC₀
          · exact Or.inl hxA
          · exact Or.inr (hC_eq ▸ Finset.mem_insert_of_mem hxC₀)
      have hD_card : D.card = A.card := by
        have ha_t_in_E : a_t ∈ insert c₀ D₀ := Finset.mem_insert_of_mem ha_t_D₀
        rw [Finset.card_erase_of_mem ha_t_in_E, Finset.card_insert_of_notMem hc₀D₀, hD₀_card]
        omega
      -- `a_t` is algebraic over `K(D)` because `{seq j | j < i₀} ⊆ D`.
      have hprev_sub_D : {x : L | ∃ j : Fin n, (j : ℕ) < i₀.1 ∧ x = seq j} ⊆ (D : Set L) := by
        rintro x ⟨j, hji, rfl⟩
        refine Finset.mem_erase.mpr ⟨fun hjeq => ?_, ?_⟩
        · have := hseq_inj hjeq
          omega
        · have hmem : seq j ∈ Set.range seq := ⟨j, rfl⟩
          rw [hseq_range, ← Finset.coe_insert] at hmem
          exact Finset.mem_coe.mp hmem
      have ha_t_alg_D : IsGarlingAlgebraic (IntermediateField.adjoin K (D : Set L)) a_t := by
        let Kprev := IntermediateField.adjoin K {x : L | ∃ j : Fin n, (j : ℕ) < i₀.1 ∧ x = seq j}
        let KD := IntermediateField.adjoin K (D : Set L)
        have hle : Kprev ≤ KD := IntermediateField.adjoin.mono K _ _ hprev_sub_D
        obtain ⟨p, hp0, hpa⟩ := hi₀_alg
        let inc : Kprev →+* KD := (IntermediateField.inclusion hle).toRingHom
        refine ⟨p.map inc, (Polynomial.map_ne_zero_iff (IntermediateField.inclusion hle).injective).mpr hp0, ?_⟩
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        exact hpa
      -- `K(insert c₀ D₀) = K(D)(a_t)` is algebraic over `K(D)`, and `L : K(insert c₀ D₀)` is
      -- algebraic (since `D₀ ⊆ insert c₀ D₀`), so `L : K(D)` is algebraic by `Theorem 4.7`!
      let KD := IntermediateField.adjoin K (D : Set L)
      let KE := IntermediateField.adjoin K (insert c₀ D₀ : Set L)
      have hKD_le_KE : KD ≤ KE :=
        IntermediateField.adjoin.mono K _ _ (by
          intro x hx
          rw [← Finset.coe_insert]
          exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase hx))
      let _ : Algebra KD KE := (IntermediateField.inclusion hKD_le_KE).toRingHom.toAlgebra
      have _ : IsScalarTower KD KE L := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hKE_alg_KD : IsAlgebraicExtension KD KE := by
        have h1 := corollary_1_to_theorem_4_6 ha_t_alg_D
        have hE_eq_ins : insert a_t (D : Set L) = (insert c₀ D₀ : Set L) := by
          rw [← Finset.coe_insert, Finset.insert_erase (Finset.mem_insert_of_mem ha_t_D₀),
            Finset.coe_insert]
        have hKE_le_adj : KE ≤ (IntermediateField.adjoin KD ({a_t} : Set L)).restrictScalars K := by
          rw [adjoin_insert_eq_adjoin_simple_over, hE_eq_ins]
        intro ⟨x, hx⟩
        obtain ⟨p, hp0, hpx⟩ := h1 ⟨x, hKE_le_adj hx⟩
        refine ⟨p, hp0, Subtype.ext ?_⟩
        have hv1 : Polynomial.aeval x p = 0 := by
          have hv := congrArg (IntermediateField.adjoin KD ({a_t} : Set L)).val hpx
          simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
          exact hv
        change (IsScalarTower.toAlgHom KD KE L) (Polynomial.aeval (⟨x, hx⟩ : KE) p) = 0
        rw [← Polynomial.aeval_algHom_apply]
        exact hv1
      have hL_alg_KE : IsAlgebraicExtension KE L := by
        let KD₀ := IntermediateField.adjoin K (D₀ : Set L)
        have hle : KD₀ ≤ KE := IntermediateField.adjoin.mono K _ _ (Set.subset_insert _ _)
        let inc : KD₀ →+* KE := (IntermediateField.inclusion hle).toRingHom
        intro x
        obtain ⟨p, hp0, hpx⟩ := hD₀_alg x
        refine ⟨p.map inc,
          (Polynomial.map_ne_zero_iff (IntermediateField.inclusion hle).injective).mpr hp0, ?_⟩
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        exact hpx
      exact ⟨D, hC_sub_D, hD_sub, hD_card, theorem_4_7 hL_alg_KE hKE_alg_KD⟩

/-- **Theorem 18.6 (distinct-tuple companion)** (§18.3, printed p. 143 / PDF p. 151):
Direct tuple formulation for injective tuples `c : Fin r → L` and `a : Fin s → L`. -/
theorem theorem_18_6_tuple {K L : Type*} [Field K] [Field L] [Algebra K L] {r s : ℕ}
    {c : Fin r → L} {a : Fin s → L}
    (hc_inj : Function.Injective c) (ha_inj : Function.Injective a)
    (hC : IsGarlingAlgebraicallyIndependent K (Set.range c))
    (hA : IsAlgebraicExtension (IntermediateField.adjoin K (Set.range a)) L) :
    r ≤ s ∧
    ∃ D : Finset L,
      Set.range c ⊆ (D : Set L) ∧
      (D : Set L) ⊆ Set.range a ∪ Set.range c ∧
      D.card = s ∧
      IsAlgebraicExtension (IntermediateField.adjoin K (D : Set L)) L := by
  classical
  let Cf : Finset L := Finset.univ.image c
  let Af : Finset L := Finset.univ.image a
  have hCf_coe : (Cf : Set L) = Set.range c := by simp [Cf]
  have hAf_coe : (Af : Set L) = Set.range a := by simp [Af]
  have hCf_card : Cf.card = r := by
    rw [Finset.card_image_of_injective _ hc_inj, Finset.card_univ, Fintype.card_fin]
  have hAf_card : Af.card = s := by
    rw [Finset.card_image_of_injective _ ha_inj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨hle, D, hCD, hDAC, hDcard, hDalg⟩ :=
    theorem_18_6 Cf Af (hCf_coe.symm ▸ hC) (hAf_coe.symm ▸ hA)
  refine ⟨by omega, D, ?_, ?_, by omega, hDalg⟩
  · rw [← hCf_coe]; exact_mod_cast hCD
  · rw [← hAf_coe, ← hCf_coe, ← Finset.coe_union]; exact_mod_cast hDAC

/-- **Corollary** [to `Theorem 18.6`] (§18.3, printed p. 144 / PDF p. 152, no `Proof.` block):
*"If `L:K` is an extension, and `S` and `T` are two transcendence bases for `L` over `K` then
either `S` and `T` are both infinite or `S` and `T` have the same finite number of elements."* -/
theorem corollary_to_theorem_18_6 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S T : Set L}
    (hS : IsGarlingTranscendenceBasis K S) (hT : IsGarlingTranscendenceBasis K T) :
    (S.Infinite ∧ T.Infinite) ∨ (S.Finite ∧ T.Finite ∧ S.ncard = T.ncard) := by
  classical
  have hfin_le : ∀ {U V : Set L},
      IsGarlingTranscendenceBasis K U → IsGarlingTranscendenceBasis K V →
      V.Finite → U.Finite ∧ U.ncard ≤ V.ncard := by
    intro U V hU hV hVfin
    obtain ⟨hUind, _⟩ := (theorem_18_4 U).mp hU
    obtain ⟨_, hValg⟩ := (theorem_18_4 V).mp hV
    have hVcoe : (hVfin.toFinset : Set L) = V := Set.Finite.coe_toFinset hVfin
    have hbound : ∀ C : Finset L, (C : Set L) ⊆ U → C.card ≤ hVfin.toFinset.card := by
      intro C hCU
      exact (theorem_18_6 C hVfin.toFinset (hUind.mono hCU) (hVcoe.symm ▸ hValg)).1
    have hUfin : U.Finite := by
      by_contra hUinf
      obtain ⟨C, hCU, hCcard⟩ := Set.Infinite.exists_subset_card_eq hUinf (hVfin.toFinset.card + 1)
      have := hbound C hCU
      omega
    refine ⟨hUfin, ?_⟩
    rw [Set.ncard_eq_toFinset_card U hUfin, Set.ncard_eq_toFinset_card V hVfin]
    exact hbound hUfin.toFinset (by simp)
  by_cases hTf : T.Finite
  · right
    obtain ⟨hSf, hle1⟩ := hfin_le hS hT hTf
    obtain ⟨_, hle2⟩ := hfin_le hT hS hSf
    exact ⟨hSf, hTf, le_antisymm hle1 hle2⟩
  · left
    refine ⟨?_, hTf⟩
    intro hSf
    exact hTf (hfin_le hT hS hSf).1

/-- `setOrder` invariance of transcendence bases (direct consequence of `Corollary` to `Theorem 18.6`). -/
theorem setOrder_eq_of_isGarlingTranscendenceBasis {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S T : Set L}
    (hS : IsGarlingTranscendenceBasis K S) (hT : IsGarlingTranscendenceBasis K T) :
    setOrder S = setOrder T := by
  rcases corollary_to_theorem_18_6 hS hT with ⟨hSinf, hTinf⟩ | ⟨hSfin, hTfin, hcard⟩
  · have : Infinite S := hSinf.to_subtype
    have : Infinite T := hTinf.to_subtype
    simp [setOrder]
  · simp only [setOrder, ENat.card_coe_set_eq,
      hSfin.encard_eq_coe_toFinset_card, hTfin.encard_eq_coe_toFinset_card]
    rw [← Set.ncard_eq_toFinset_card S hSfin, ← Set.ncard_eq_toFinset_card T hTfin, hcard]

/-- Garling's inline prose definition of *transcendence degree* (§18.3, printed p. 144 / PDF p. 152):
*"If an extension `L:K` has a finite transcendence basis, we define its **transcendence degree**
to be the number of elements in the transcendence basis; otherwise we define the transcendence
degree to be `∞`."*

Valued in `ℕ∞` (matching `Chapter01.setOrder : ℕ∞` and `Chapter04.extDegree : ℕ∞`). -/
noncomputable def transcendenceDegree (K L : Type*) [Field K] [Field L] [Algebra K L] : ℕ∞ :=
  setOrder (exists_transcendenceBasis K L).choose

/-- For every transcendence basis `S` of `L` over `K`, `transcendenceDegree K L = setOrder S`. -/
theorem transcendenceDegree_eq_setOrder {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S : Set L} (hS : IsGarlingTranscendenceBasis K S) :
    transcendenceDegree K L = setOrder S :=
  setOrder_eq_of_isGarlingTranscendenceBasis (exists_transcendenceBasis K L).choose_spec hS

/-- Finite transcendence degree characterization matching Garling's literal p. 144 wording. -/
theorem transcendenceDegree_eq_natCast_iff {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ) :
    transcendenceDegree K L = (n : ℕ∞) ↔
      ∃ S : Set L, IsGarlingTranscendenceBasis K S ∧ S.Finite ∧ S.ncard = n := by
  constructor
  · intro h
    let S := (exists_transcendenceBasis K L).choose
    have hS : IsGarlingTranscendenceBasis K S := (exists_transcendenceBasis K L).choose_spec
    have hord : setOrder S = (n : ℕ∞) := h
    have hSfin : S.Finite := by
      by_contra hinf
      have hinf' : S.Infinite := hinf
      have : Infinite S := hinf'.to_subtype
      have htop : setOrder S = ⊤ := by simp [setOrder]
      rw [htop] at hord
      exact ENat.top_ne_natCast n hord
    have hncard : S.ncard = n := by
      rw [setOrder, ENat.card_coe_set_eq, hSfin.encard_eq_coe_toFinset_card,
        ← Set.ncard_eq_toFinset_card S hSfin] at hord
      exact Nat.cast_injective hord
    exact ⟨S, hS, hSfin, hncard⟩
  · rintro ⟨S, hS, hSfin, hncard⟩
    rw [transcendenceDegree_eq_setOrder hS, setOrder, ENat.card_coe_set_eq,
      hSfin.encard_eq_coe_toFinset_card, ← Set.ncard_eq_toFinset_card S hSfin, hncard]

/-- Infinite transcendence degree (`= ⊤`) characterization matching Garling's literal p. 144 wording. -/
theorem transcendenceDegree_eq_top_iff {K L : Type*} [Field K] [Field L] [Algebra K L] :
    transcendenceDegree K L = ⊤ ↔
      ∀ S : Set L, IsGarlingTranscendenceBasis K S → S.Infinite := by
  constructor
  · intro h S hS hSfin
    rw [transcendenceDegree_eq_setOrder hS] at h
    have : Finite S := hSfin.to_subtype
    simp only [setOrder, ENat.card_eq_coe_natCard] at h
    exact ENat.natCast_ne_top _ h
  · intro hall
    let S := (exists_transcendenceBasis K L).choose
    have hSinf : S.Infinite := hall S (exists_transcendenceBasis K L).choose_spec
    have : Infinite S := hSinf.to_subtype
    simp [transcendenceDegree, setOrder]

/-- `transcendenceDegree K L = 0 ↔ IsAlgebraicExtension K L`. -/
theorem transcendenceDegree_eq_zero_iff {K L : Type*} [Field K] [Field L] [Algebra K L] :
    transcendenceDegree K L = 0 ↔ IsAlgebraicExtension K L := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, transcendenceDegree_eq_natCast_iff]
  constructor
  · rintro ⟨S, hS, hSfin, h0⟩
    have hSe : S = ∅ := (Set.ncard_eq_zero hSfin).mp h0
    subst hSe
    have halg := ((theorem_18_4 (∅ : Set L)).mp hS).2
    intro a
    obtain ⟨p, hp0, hpa⟩ := halg a
    let eBot : (IntermediateField.adjoin K (∅ : Set L)) ≃ₐ[K] K :=
      (IntermediateField.equivOfEq (IntermediateField.adjoin_empty K L)).trans
        (IntermediateField.botEquiv K L)
    refine ⟨p.map eBot.toRingHom, (Polynomial.map_ne_zero_iff eBot.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap K L).comp eBot.toRingHom =
        algebraMap (IntermediateField.adjoin K (∅ : Set L)) L := by
      ext ⟨x, hx⟩
      have hx_bot : x ∈ (⊥ : IntermediateField K L) := by
        rwa [IntermediateField.adjoin_empty] at hx
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hx_bot
      have hxk : (⟨x, hx⟩ : IntermediateField.adjoin K (∅ : Set L)) = algebraMap K _ k :=
        Subtype.ext hk.symm
      rw [RingHom.comp_apply, hxk]
      change algebraMap K L (eBot (algebraMap K _ k)) = algebraMap K L k
      rw [eBot.commutes k]
      simp
    rw [hcomp]
    exact hpa
  · intro halg
    refine ⟨∅, (theorem_18_4 (∅ : Set L)).mpr ⟨isGarlingAlgebraicallyIndependent_empty K, ?_⟩,
      Set.finite_empty, Set.ncard_empty L⟩
    intro a
    obtain ⟨p, hp0, hpa⟩ := halg a
    let inc : K →+* IntermediateField.adjoin K (∅ : Set L) := algebraMap K _
    refine ⟨p.map inc, (Polynomial.map_ne_zero_iff inc.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_map_algebraMap]
    exact hpa

/-- Bridge between Garling's `transcendenceDegree K L : ℕ∞` and Mathlib's `Cardinal.toENat (Algebra.trdeg K L)`. -/
theorem transcendenceDegree_eq_toENat_trdeg (K L : Type*) [Field K] [Field L] [Algebra K L] :
    transcendenceDegree K L = Cardinal.toENat (Algebra.trdeg K L) := by
  let S := (exists_transcendenceBasis K L).choose
  have hS : IsGarlingTranscendenceBasis K S := (exists_transcendenceBasis K L).choose_spec
  have hS_math : IsTranscendenceBasis K ((↑) : S → L) :=
    (isGarlingTranscendenceBasis_iff S).mp hS
  have hcard : Cardinal.mk S = Algebra.trdeg K L := hS_math.cardinalMk_eq_trdeg
  rw [transcendenceDegree_eq_setOrder hS, ← hcard, setOrder, ENat.card_coe_set_eq,
    Set.toENat_cardinalMk]

/-! ## §18.4 The tower law for transcendence degree (printed pp. 144–145, PDF pp. 152–153) -/

/-- Automatic disjointness in `Theorems 18.7–18.8` (Flag 5): if `B ⊆ M` is algebraically
independent over `L`, then no element of `B` lies in `L`, so `(algebraMap L M '' A)` and `B`
are automatically disjoint for every `A ⊆ L`. -/
theorem disjoint_of_algebraicallyIndependent_over_intermediate
    {L M : Type*} [Field L] [Field M] [Algebra L M]
    (A : Set L) {B : Set M} (hB : IsGarlingAlgebraicallyIndependent L B) :
    Disjoint (algebraMap L M '' A) B := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, _, rfl⟩ hmem
  have htr : IsGarlingTranscendental L (algebraMap L M a) :=
    (isGarlingAlgebraicallyIndependent_singleton_iff _).mp
      (hB.mono (Set.singleton_subset_iff.mpr hmem))
  exact htr (isAlgebraic_algebraMap a)

/-- **Theorem 18.7** (§18.4, printed p. 144 / PDF p. 152):
*"Suppose that `M:L` and `L:K` are extensions, that `A` is a subset of `L` which is algebraically
independent over `K` and that `B` is a subset of `M` which is algebraically independent over `L`.
Then `A ∪ B` is algebraically independent over `K`."* -/
theorem theorem_18_7 {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {A : Set L} {B : Set M}
    (hA : IsGarlingAlgebraicallyIndependent K A)
    (hB : IsGarlingAlgebraicallyIndependent L B) :
    IsGarlingAlgebraicallyIndependent K ((algebraMap L M '' A) ∪ B) := by
  have hA' : AlgebraicIndependent K ((↑) : A → L) :=
    (isGarlingAlgebraicallyIndependent_iff A).mp hA
  have hB' : AlgebraicIndependent L ((↑) : B → M) :=
    (isGarlingAlgebraicallyIndependent_iff B).mp hB
  have hsum : AlgebraicIndependent K (Sum.elim ((↑) : B → M) (algebraMap L M ∘ ((↑) : A → L))) :=
    AlgebraicIndependent.sumElim_comp hA' hB'
  have hrange : Set.range (Sum.elim ((↑) : B → M) (algebraMap L M ∘ ((↑) : A → L))) =
      (algebraMap L M '' A) ∪ B := by
    rw [Set.Sum.elim_range, Set.range_comp, Subtype.range_coe_subtype, Subtype.range_coe_subtype,
      Set.union_comm]
    rfl
  rw [isGarlingAlgebraicallyIndependent_iff]
  exact hsum.to_subtype_range' hrange

/-- **Theorem 18.7 (subfield-tower form)** (§18.4, printed p. 144 / PDF p. 152):
For subfields `K ≤ L` of `M` and `A ⊆ L`, `B ⊆ M`, `A ∪ B` is literally a subset of `M`. -/
theorem theorem_18_7_subfield {M : Type*} [Field M] {K L : Subfield M} (hKL : K ≤ L)
    {A B : Set M} (hAL : A ⊆ (L : Set M))
    (hA : IsGarlingAlgebraicallyIndependent K A)
    (hB : IsGarlingAlgebraicallyIndependent L B) :
    IsGarlingAlgebraicallyIndependent K (A ∪ B) := by
  let _ : Algebra K L := (Subfield.inclusion hKL).toAlgebra
  have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let A' : Set L := {x : L | (x : M) ∈ A}
  have hA'_img : algebraMap L M '' A' = A := by
    ext x
    constructor
    · rintro ⟨⟨y, _⟩, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hAL hx⟩, hx, rfl⟩
  have hA'_ind : IsGarlingAlgebraicallyIndependent K A' := by
    rw [isGarlingAlgebraicallyIndependent_iff] at hA ⊢
    let f : A' ≃ A :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hAL y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hcomp : (fun x : A' => (IsScalarTower.toAlgHom K L M) (x : L)) =
        (fun y : A => (y : M)) ∘ f := funext fun _ => rfl
    have h1 : AlgebraicIndependent K (fun x : A' => (IsScalarTower.toAlgHom K L M) (x : L)) := by
      rw [hcomp]
      exact hA.comp f f.injective
    exact h1.of_comp (IsScalarTower.toAlgHom K L M)
  simpa [hA'_img] using theorem_18_7 hA'_ind hB

/-- **Theorem 18.8** (§18.4, printed p. 144 / PDF p. 152; proof pp. 144–145 / PDF pp. 152–153):
*"Suppose that `M:L` and `L:K` are extensions, that `A` is a transcendence basis for `L` over `K`
and that `B` is a transcendence basis for `M` over `L`. Then `A ∪ B` is a transcendence basis for
`M` over `K`."* -/
theorem theorem_18_8 {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {A : Set L} {B : Set M}
    (hA : IsGarlingTranscendenceBasis K A)
    (hB : IsGarlingTranscendenceBasis L B) :
    IsGarlingTranscendenceBasis K ((algebraMap L M '' A) ∪ B) := by
  have hA' : IsTranscendenceBasis K ((↑) : A → L) := (isGarlingTranscendenceBasis_iff A).mp hA
  have hB' : IsTranscendenceBasis L ((↑) : B → M) := (isGarlingTranscendenceBasis_iff B).mp hB
  have hsum : IsTranscendenceBasis K (Sum.elim ((↑) : B → M) (algebraMap L M ∘ ((↑) : A → L))) :=
    IsTranscendenceBasis.sumElim_comp hA' hB'
  have hrange : Set.range (Sum.elim ((↑) : B → M) (algebraMap L M ∘ ((↑) : A → L))) =
      (algebraMap L M '' A) ∪ B := by
    rw [Set.Sum.elim_range, Set.range_comp, Subtype.range_coe_subtype, Subtype.range_coe_subtype,
      Set.union_comm]
    rfl
  rw [isGarlingTranscendenceBasis_iff]
  exact hsum.to_subtype_range' hrange

/-- **Theorem 18.8 (subfield-tower form)** (§18.4, printed p. 144 / PDF p. 152):
For subfields `K ≤ L` of `M`, if `A ⊆ L` is algebraically independent over `K` and every element
of `L` is algebraic over `K(A)` (i.e., `A` is a transcendence basis for `L:K`), and `B ⊆ M` is a
transcendence basis for `M:L`, then `A ∪ B` is a transcendence basis for `M:K`. -/
theorem theorem_18_8_subfield {M : Type*} [Field M] {K L : Subfield M} (hKL : K ≤ L)
    {A B : Set M} (hAL : A ⊆ (L : Set M))
    (hA_ind : IsGarlingAlgebraicallyIndependent K A)
    (hA_alg : ∀ x ∈ L, IsGarlingAlgebraic (IntermediateField.adjoin K A) x)
    (hB : IsGarlingTranscendenceBasis L B) :
    IsGarlingTranscendenceBasis K (A ∪ B) := by
  let _ : Algebra K L := (Subfield.inclusion hKL).toAlgebra
  have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let A' : Set L := {x : L | (x : M) ∈ A}
  have hA'_img : algebraMap L M '' A' = A := by
    ext x
    constructor
    · rintro ⟨⟨y, _⟩, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hAL hx⟩, hx, rfl⟩
  have hA'_ind : IsGarlingAlgebraicallyIndependent K A' := by
    rw [isGarlingAlgebraicallyIndependent_iff] at hA_ind ⊢
    let f : A' ≃ A :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hAL y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hcomp : (fun x : A' => (IsScalarTower.toAlgHom K L M) (x : L)) =
        (fun y : A => (y : M)) ∘ f := funext fun _ => rfl
    have h1 : AlgebraicIndependent K (fun x : A' => (IsScalarTower.toAlgHom K L M) (x : L)) := by
      rw [hcomp]
      exact hA_ind.comp f f.injective
    exact h1.of_comp (IsScalarTower.toAlgHom K L M)
  have hA'_alg : IsAlgebraicExtension (IntermediateField.adjoin K A') L := by
    intro x
    obtain ⟨p, hp0, hpx⟩ := hA_alg x.1 x.2
    have hmap_eq : (IntermediateField.adjoin K A').map (IsScalarTower.toAlgHom K L M) =
        IntermediateField.adjoin K A := by
      rw [IntermediateField.adjoin_map]
      exact congrArg (IntermediateField.adjoin K) hA'_img
    let eKA : IntermediateField.adjoin K A' ≃ₐ[K] IntermediateField.adjoin K A :=
      ((IntermediateField.adjoin K A').equivMapOfInjective (IsScalarTower.toAlgHom K L M)
        Subtype.val_injective).trans (IntermediateField.equivOfEq hmap_eq)
    refine ⟨p.map eKA.symm.toRingHom, (Polynomial.map_ne_zero_iff eKA.symm.injective).mpr hp0, ?_⟩
    apply Subtype.ext
    have h1 : ((Polynomial.aeval x (p.map eKA.symm.toRingHom) : L) : M) = Polynomial.aeval x.1 p := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap L M).comp ((algebraMap (IntermediateField.adjoin K A') L).comp
            eKA.symm.toRingHom) = algebraMap (IntermediateField.adjoin K A) M := by
        ext ⟨z, hz⟩
        have hz_eq := congrArg Subtype.val (eKA.apply_symm_apply ⟨z, hz⟩)
        exact hz_eq
      change (algebraMap L M) (Polynomial.eval₂
        ((algebraMap (IntermediateField.adjoin K A') L).comp eKA.symm.toRingHom) x p) =
        Polynomial.eval₂ (algebraMap (IntermediateField.adjoin K A) M) x.1 p
      rw [Polynomial.hom_eval₂, hcomp]
      rfl
    rw [h1, hpx]
    rfl
  have hA' : IsGarlingTranscendenceBasis K A' := (theorem_18_4 A').mpr ⟨hA'_ind, hA'_alg⟩
  simpa [hA'_img] using theorem_18_8 hA' hB

/-- **Corollary** [to `Theorem 18.8`] (§18.4, printed p. 145 / PDF p. 153, no `Proof.` block):
*"If `M:L` and `L:K` are extensions, the transcendence degree of `M:K` is the sum of the
transcendence degrees of `M:L` and `L:K`."*

Holds unconditionally in `ℕ∞` across both finite and infinite transcendence degrees. -/
theorem corollary_to_theorem_18_8 (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    transcendenceDegree K M = transcendenceDegree L M + transcendenceDegree K L := by
  classical
  obtain ⟨A, hA⟩ := exists_transcendenceBasis K L
  obtain ⟨B, hB⟩ := exists_transcendenceBasis L M
  have hAB : IsGarlingTranscendenceBasis K ((algebraMap L M '' A) ∪ B) := theorem_18_8 hA hB
  have hdisj : Disjoint (algebraMap L M '' A) B :=
    disjoint_of_algebraicallyIndependent_over_intermediate A ((theorem_18_4 B).mp hB).1
  rw [transcendenceDegree_eq_setOrder hAB, transcendenceDegree_eq_setOrder hB,
    transcendenceDegree_eq_setOrder hA]
  have himg_ord : setOrder (algebraMap L M '' A) = setOrder A := by
    unfold setOrder
    exact ENat.card_congr (Equiv.Set.image (algebraMap L M) A (algebraMap L M).injective).symm
  rw [← himg_ord, add_comm]
  unfold setOrder
  rw [← ENat.card_sum]
  exact ENat.card_congr (Equiv.Set.union hdisj)

/-! ## §18.5 Lüroth's theorem (printed pp. 145–146, PDF pp. 153–154) -/

/-- **§18.5 Prose Result (printed p. 145 / PDF p. 153):**
*"Suppose that `L:K` is a finitely generated extension which has transcendence degree `r`. If
`α₁, ..., αᵣ` is a transcendence basis for `L` over `K`, then `L:K(α₁, ..., αᵣ)` is finite."* -/
theorem isFiniteExtension_over_transcendenceBasis_of_finitelyGenerated
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfg : IsFinitelyGeneratedExtension K L)
    {S : Set L} (hS : IsGarlingTranscendenceBasis K S) :
    S.Finite ∧
    transcendenceDegree K L = (S.ncard : ℕ∞) ∧
    IsFiniteExtension (IntermediateField.adjoin K S) L := by
  obtain ⟨B, hBfin, hB⟩ := exists_finite_transcendenceBasis_of_finitelyGenerated hfg
  have hSfin : S.Finite := by
    rcases corollary_to_theorem_18_6 hS hB with ⟨_, hBinf⟩ | ⟨hSf, _, _⟩
    · exact False.elim (hBinf hBfin)
    · exact hSf
  have hdeg : transcendenceDegree K L = (S.ncard : ℕ∞) :=
    (transcendenceDegree_eq_natCast_iff S.ncard).mpr ⟨S, hS, hSfin, rfl⟩
  have halg : IsAlgebraicExtension (IntermediateField.adjoin K S) L :=
    ((theorem_18_4 S).mp hS).2
  have hfgS : IsFinitelyGeneratedExtension (IntermediateField.adjoin K S) L := by
    obtain ⟨A, hAfin, hAtop⟩ := hfg
    refine ⟨A, hAfin, eq_top_iff.mpr fun x _ => ?_⟩
    have hx : x ∈ IntermediateField.adjoin K A := hAtop ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K A ≤
        (IntermediateField.adjoin (IntermediateField.adjoin K S) A).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      intro a ha
      exact IntermediateField.subset_adjoin _ A ha
    exact hle hx
  exact ⟨hSfin, hdeg, (theorem_4_6 _ L).1.mpr ⟨halg, hfgS⟩⟩

/-- Garling's literal inline prose definition of a *purely transcendental* extension
(§18.5, printed p. 145 / PDF p. 153): a finitely generated extension `L:K` admitting a finite
transcendence basis `S` with `L = K(S)`. -/
def IsGarlingPurelyTranscendental (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsFinitelyGeneratedExtension K L ∧
  ∃ S : Set L, S.Finite ∧ IsGarlingTranscendenceBasis K S ∧ IntermediateField.adjoin K S = ⊤

/-- General (possibly infinite transcendence degree) notion of *purely transcendental* extension:
`L = K(S)` for some transcendence basis `S` of `L` over `K`. -/
def IsPurelyTranscendental (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ S : Set L, IsGarlingTranscendenceBasis K S ∧ IntermediateField.adjoin K S = ⊤

/-- On finitely generated extensions `L:K`, `IsGarlingPurelyTranscendental K L` and
`IsPurelyTranscendental K L` coincide. -/
theorem isGarlingPurelyTranscendental_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfg : IsFinitelyGeneratedExtension K L) :
    IsGarlingPurelyTranscendental K L ↔ IsPurelyTranscendental K L := by
  constructor
  · rintro ⟨_, S, _, hS, htop⟩; exact ⟨S, hS, htop⟩
  · rintro ⟨S, hS, htop⟩
    exact ⟨hfg, S, (isFiniteExtension_over_transcendenceBasis_of_finitelyGenerated hfg hS).1,
      hS, htop⟩

/-- **Theorem 18.9 (Lüroth's theorem)** (§18.5, printed p. 145 / PDF p. 153; proof pp. 145–146 /
PDF pp. 153–154):
*"Suppose that `K(t):K` is a simple extension and that `t` is transcendental over `K`. If `L` is
a subfield of `K(t)` containing `K` then `L:K` is a simple extension."* -/
theorem theorem_18_9 {K E : Type*} [Field K] [Field E] [Algebra K E] {t : E}
    (hsimple : IntermediateField.adjoin K ({t} : Set E) = ⊤)
    (ht : IsGarlingTranscendental K t)
    (L : IntermediateField K E) :
    IsSimpleExtension K L := by
  have ht' : Transcendental K t := (isGarlingTranscendental_iff t).mp ht
  let eRF : RatFunc K ≃ₐ[K] E :=
    (RatFunc.algEquivOfTranscendental t ht').trans
      ((IntermediateField.equivOfEq hsimple).trans IntermediateField.topEquiv)
  let L' : IntermediateField K (RatFunc K) := L.map eRF.symm.toAlgHom
  let gen' : RatFunc K := RatFunc.Luroth.generator L'
  have hgen'_mem : gen' ∈ L' := RatFunc.Luroth.generator_mem
  have hL'_eq : L' = IntermediateField.adjoin K ({gen'} : Set (RatFunc K)) :=
    RatFunc.Luroth.eq_adjoin_generator
  let genE : E := eRF gen'
  have hgenE_mem : genE ∈ L := by
    obtain ⟨x, hxL, hx_eq⟩ := hgen'_mem
    have : eRF gen' = x := by rw [← hx_eq]; exact eRF.apply_symm_apply x
    show eRF gen' ∈ L
    rw [this]
    exact hxL
  refine ⟨⟨genE, hgenE_mem⟩, eq_top_iff.mpr fun ⟨y, hyL⟩ _ => ?_⟩
  have hy' : eRF.symm y ∈ L' := ⟨y, hyL, rfl⟩
  rw [hL'_eq] at hy'
  obtain ⟨f, g, hfg_eq⟩ := (IntermediateField.mem_adjoin_simple_iff K (eRF.symm y)).mp hy'
  have hy_eq : y = Polynomial.aeval genE f / Polynomial.aeval genE g := by
    have h1 := congrArg eRF hfg_eq
    rw [AlgEquiv.apply_symm_apply, map_div₀] at h1
    have hae : ∀ p : K[X], eRF (Polynomial.aeval gen' p) = Polynomial.aeval genE p := fun p =>
      (Polynomial.aeval_algHom_apply eRF.toAlgHom gen' p).symm
    rw [hae f, hae g] at h1
    exact h1
  have hy_sub : (⟨y, hyL⟩ : L) =
      Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) f / Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) g := by
    apply Subtype.ext
    change y = ((Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) f : L) : E) /
      ((Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) g : L) : E)
    have h1 : ∀ p : K[X], ((Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) p : L) : E) =
        Polynomial.aeval genE p := fun p => by
      change L.val (Polynomial.aeval (⟨genE, hgenE_mem⟩ : L) p) = Polynomial.aeval genE p
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    rw [h1 f, h1 g]
    exact hy_eq
  exact (IntermediateField.mem_adjoin_simple_iff K (⟨y, hyL⟩ : L)).mpr ⟨f, g, hy_sub⟩

/-- **Theorem 18.9 (Lüroth's theorem — ambient `K(t)` companion)** (§18.5, p. 145):
For any ambient extension `E:K`, transcendental `t ∈ E`, and intermediate field `L ≤ K(t)`,
`L : K` is simple (and `∃ u ∈ L, K(u) = L`). -/
theorem theorem_18_9_adjoin {K E : Type*} [Field K] [Field E] [Algebra K E] {t : E}
    (ht : IsGarlingTranscendental K t)
    {L : IntermediateField K E} (hL : L ≤ IntermediateField.adjoin K ({t} : Set E)) :
    IsSimpleExtension K L ∧ ∃ u : E, u ∈ L ∧ IntermediateField.adjoin K ({u} : Set E) = L := by
  let Kt := IntermediateField.adjoin K ({t} : Set E)
  let tKt : Kt := IntermediateField.AdjoinSimple.gen K t
  have hsimple : IntermediateField.adjoin K ({tKt} : Set Kt) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    obtain ⟨f, g, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hx
    refine (IntermediateField.mem_adjoin_simple_iff K _).mpr ⟨f, g, Subtype.ext ?_⟩
    change Polynomial.aeval t f / Polynomial.aeval t g =
      ((Polynomial.aeval tKt f : Kt) : E) / ((Polynomial.aeval tKt g : Kt) : E)
    rw [coe_aeval_adjoinSimple_gen, coe_aeval_adjoinSimple_gen]
    rfl
  have htKt : IsGarlingTranscendental K tKt := by
    intro ⟨f, hf0, hft⟩
    refine ht ⟨f, hf0, ?_⟩
    have hval : ((Polynomial.aeval tKt f : Kt) : E) = 0 := congrArg Subtype.val hft
    rw [coe_aeval_adjoinSimple_gen] at hval
    exact hval
  let L_sub : IntermediateField K Kt :=
    { carrier := {x : Kt | (x : E) ∈ L}
      mul_mem' := fun ha hb => L.mul_mem ha hb
      add_mem' := fun ha hb => L.add_mem ha hb
      algebraMap_mem' := fun k => L.algebraMap_mem k
      inv_mem' := fun _ ha => L.inv_mem ha }
  have hsimp_sub : IsSimpleExtension K L_sub := theorem_18_9 hsimple htKt L_sub
  let eL : L_sub ≃ₐ[K] L :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hL y.2⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  obtain ⟨u0, hu0_top⟩ := hsimp_sub
  let u : E := u0.1.1
  have huL : u ∈ L := u0.2
  have hL_eq : IntermediateField.adjoin K ({u} : Set E) = L := by
    apply le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr huL)
    intro y hyL
    have hy0 : (⟨⟨y, hL hyL⟩, hyL⟩ : L_sub) ∈ IntermediateField.adjoin K ({u0} : Set L_sub) :=
      hu0_top ▸ IntermediateField.mem_top
    obtain ⟨f, g, hfg⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp hy0
    have hy_eq : y = Polynomial.aeval u f / Polynomial.aeval u g := by
      have hval := congrArg (fun z : L_sub => z.1.1) hfg
      have hae : ∀ p : K[X], (Polynomial.aeval u0 p : L_sub).1.1 = Polynomial.aeval u p := fun p => by
        let valHom : L_sub →ₐ[K] E := Kt.val.comp L_sub.val
        change valHom (Polynomial.aeval u0 p) = Polynomial.aeval (valHom u0) p
        rw [← Polynomial.aeval_algHom_apply]
      simpa [hae] using hval
    exact (IntermediateField.mem_adjoin_simple_iff K y).mpr ⟨f, g, hy_eq⟩
  refine ⟨⟨⟨u, huL⟩, eq_top_iff.mpr fun ⟨y, hyL⟩ _ => ?_⟩, u, huL, hL_eq⟩
  have hy_adj : y ∈ IntermediateField.adjoin K ({u} : Set E) := hL_eq ▸ hyL
  obtain ⟨f, g, hfg⟩ := (IntermediateField.mem_adjoin_simple_iff K y).mp hy_adj
  refine (IntermediateField.mem_adjoin_simple_iff K (⟨y, hyL⟩ : L)).mpr ⟨f, g, Subtype.ext ?_⟩
  have hae : ∀ p : K[X], ((Polynomial.aeval (⟨u, huL⟩ : L) p : L) : E) = Polynomial.aeval u p := fun p => by
    change L.val (Polynomial.aeval (⟨u, huL⟩ : L) p) = Polynomial.aeval (L.val ⟨u, huL⟩) p
    rw [← Polynomial.aeval_algHom_apply]
  simpa [hae] using hfg

/-- **Theorem 18.9 (Lüroth's theorem — subfield form)** (§18.5, printed p. 145 / PDF p. 153):
For any subfield `L : Subfield E` with `K ≤ L` inside a simple transcendental extension `E = K(t)`,
`L = garlingFieldGenSubfield K {u}` for some `u ∈ L`. -/
theorem theorem_18_9_subfield {K E : Type*} [Field K] [Field E] [Algebra K E] {t : E}
    (hsimple : IntermediateField.adjoin K ({t} : Set E) = ⊤)
    (ht : IsGarlingTranscendental K t)
    (L : Subfield E) (hKL : (algebraMap K E).fieldRange ≤ L) :
    ∃ u : E, u ∈ L ∧ garlingFieldGenSubfield K ({u} : Set E) = L := by
  let LI : IntermediateField K E :=
    { carrier := L
      mul_mem' := L.mul_mem'
      add_mem' := L.add_mem'
      algebraMap_mem' := fun k => hKL ⟨k, rfl⟩
      inv_mem' := L.inv_mem' }
  obtain ⟨_, u, huL, huEq⟩ := theorem_18_9_adjoin ht (show LI ≤ IntermediateField.adjoin K {t} by
    rw [hsimple]; exact le_top)
  refine ⟨u, huL, ?_⟩
  rw [garlingFieldGenSubfield_eq_adjoin, huEq]
  rfl

/-! ### Exercises 18.6–18.7 (§18.5, printed p. 146, PDF p. 154) -/

/-- **Exercise 18.6 — Universal characteristic-2 refutation** (§18.5, printed p. 146 / PDF p. 154;
`QUEUE.md` fidelity hold — omitted `char K ≠ 2` hypothesis):
In **every** field `K` of characteristic `2`, for **every** extension `L:K` and elements `x, y ∈ L`
with `x` transcendental over `K` and `x² + y² = 1`, we have `1 + y = x`, hence `u = (1 + y)/x = 1 ∈ K`
and `K(u) = K ⊊ K(x, y)`. -/
theorem exercise_18_6_fails_every_char_two {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hchar2 : ringChar K = 2) {x y : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ 2 + y ^ 2 = 1) :
    (1 + y) / x = 1 ∧
    IntermediateField.adjoin K ({(1 + y) / x} : Set L) = ⊥ ∧
    IntermediateField.adjoin K ({x, y} : Set L) ≠
      IntermediateField.adjoin K ({(1 + y) / x} : Set L) := by
  have : CharP K 2 := hchar2 ▸ ringChar.charP K
  have h2K : (2 : K) = 0 := by
    exact_mod_cast CharP.cast_eq_zero K 2
  have h2L : (2 : L) = 0 := by
    have := congrArg (algebraMap K L) h2K
    simpa only [map_ofNat, map_zero] using this
  have hsq : (1 + y + x) ^ 2 = 0 := by
    have hexp : (1 + y + x) ^ 2 = 1 + (x ^ 2 + y ^ 2) + (2 : L) * (y + x + y * x) := by ring
    rw [hexp, hxy, h2L, zero_mul, add_zero]
    simpa [one_add_one_eq_two] using h2L
  have hsum0 : 1 + y + x = 0 := eq_zero_of_pow_eq_zero hsq
  have h1y_eq_x : 1 + y = x := by
    have hneg : x + x = 0 := by
      have : (2 : L) * x = 0 := by rw [h2L, zero_mul]
      linear_combination this
    linear_combination hsum0 - hneg
  have hx_ne0 : x ≠ 0 := fun h0 => hx ⟨Polynomial.X, Polynomial.X_ne_zero, by simp [h0]⟩
  have hu : (1 + y) / x = 1 := by rw [h1y_eq_x, div_self hx_ne0]
  have hKu : IntermediateField.adjoin K ({(1 + y) / x} : Set L) = ⊥ := by
    rw [hu]
    exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (IntermediateField.one_mem _)
  refine ⟨hu, hKu, ?_⟩
  intro heq
  have hx_bot : x ∈ (⊥ : IntermediateField K L) := by
    rw [← hKu, ← heq]
    exact IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y})
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hx_bot
  exact hx ⟨Polynomial.X - Polynomial.C k, Polynomial.X_sub_C_ne_zero k, by simp [hk]⟩

/-- **Exercise 18.6 — Concrete characteristic-2 counterexample** (§18.5, p. 146; `QUEUE.md` hold):
Over `K = ZMod 2`, in `L = RatFunc (ZMod 2)` with `x = X` and `y = 1 + X`, all printed hypotheses
of `Exercise 18.6` hold (`x` transcendental over `ZMod 2`, `x² + y² = 1`), yet `u = (1 + y)/x = 1`
and `K(x, y) ≠ K(u)`. -/
theorem exercise_18_6_char_two_counterexample :
    ∃ (x y : RatFunc (ZMod 2)),
      IsGarlingTranscendental (ZMod 2) x ∧
      x ^ 2 + y ^ 2 = 1 ∧
      (1 + y) / x = 1 ∧
      IntermediateField.adjoin (ZMod 2) ({x, y} : Set (RatFunc (ZMod 2))) ≠
        IntermediateField.adjoin (ZMod 2) ({(1 + y) / x} : Set (RatFunc (ZMod 2))) := by
  have h2 : (2 : RatFunc (ZMod 2)) = 0 := by
    have h : (2 : ZMod 2) = 0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod 2) (RatFunc (ZMod 2))) h
  have hxy : (RatFunc.X : RatFunc (ZMod 2)) ^ 2 + (1 + RatFunc.X) ^ 2 = 1 := by
    calc (RatFunc.X : RatFunc (ZMod 2)) ^ 2 + (1 + RatFunc.X) ^ 2
        = 1 + (2 : RatFunc (ZMod 2)) * (RatFunc.X ^ 2 + RatFunc.X) := by ring
      _ = 1 := by rw [h2, zero_mul, add_zero]
  refine ⟨RatFunc.X, 1 + RatFunc.X, RatFunc.transcendental_X, hxy, ?_⟩
  have hchar : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  have hfail := exercise_18_6_fails_every_char_two hchar
    (x := (RatFunc.X : RatFunc (ZMod 2))) (y := 1 + RatFunc.X)
    RatFunc.transcendental_X hxy
  exact ⟨hfail.1, hfail.2.2⟩

/-- **Exercise 18.6 — Repaired theorem under `ringChar K ≠ 2`** (§18.5, printed p. 146 / PDF p. 154;
`QUEUE.md` fidelity hold):
If `char K ≠ 2`, `x` is transcendental over `K`, and `x² + y² = 1`, then `K(x, y) = K(u)` where
`u = (1 + y) / x` (with explicit rational parameterization `x = 2u/(1 + u²)` and
`y = (u² - 1)/(1 + u²)`). -/
theorem exercise_18_6_repaired {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hchar : ringChar K ≠ 2) {x y : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ 2 + y ^ 2 = 1) :
    let u : L := (1 + y) / x
    1 + u ^ 2 ≠ 0 ∧
    x = 2 * u / (1 + u ^ 2) ∧
    y = (u ^ 2 - 1) / (1 + u ^ 2) ∧
    IntermediateField.adjoin K ({x, y} : Set L) = IntermediateField.adjoin K ({u} : Set L) := by
  intro u
  have h2K : (2 : K) ≠ 0 := by
    intro h20
    have hdvd : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h20)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have h10 : ((1 : ℕ) : K) = 0 := (ringChar.spec K 1).mpr (by rw [h1])
      simp at h10
    · exact hchar h2
  have h2L : (2 : L) ≠ 0 := by
    intro h20
    exact h2K ((algebraMap K L).injective (by simpa only [map_ofNat, map_zero] using h20))
  have hx_ne0 : x ≠ 0 := fun h0 => hx ⟨Polynomial.X, Polynomial.X_ne_zero, by simp [h0]⟩
  have hy_eq : y = u * x - 1 := by
    dsimp only [u]
    have hmul : 1 + y = u * x := by
      dsimp only [u]
      exact (div_mul_cancel₀ (1 + y) hx_ne0).symm
    linear_combination hmul
  have hrel : (1 + u ^ 2) * x = 2 * u := by
    have h1 : x ^ 2 + (u * x - 1) ^ 2 = 1 := hy_eq ▸ hxy
    have h2 : x * ((1 + u ^ 2) * x - 2 * u) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hx_ne0)
  have hden_ne0 : 1 + u ^ 2 ≠ 0 := by
    intro h0
    have h2u : 2 * u = 0 := by rw [← hrel, h0, zero_mul]
    have hu0 : u = 0 := (mul_eq_zero.mp h2u).resolve_left h2L
    rw [hu0] at h0
    norm_num at h0
  have hx_param : x = 2 * u / (1 + u ^ 2) := (eq_div_iff hden_ne0).mpr (by linear_combination hrel)
  have hy_param : y = (u ^ 2 - 1) / (1 + u ^ 2) := by
    rw [hy_eq, hx_param]
    field_simp [hden_ne0]
    ring
  refine ⟨hden_ne0, hx_param, hy_param, le_antisymm ?_ ?_⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · rw [hx_param]
      exact div_mem (mul_mem (ofNat_mem _ 2) (IntermediateField.mem_adjoin_simple_self K u))
        (add_mem (one_mem _) (pow_mem (IntermediateField.mem_adjoin_simple_self K u) 2))
    · rw [hy_param]
      exact div_mem (sub_mem (pow_mem (IntermediateField.mem_adjoin_simple_self K u) 2) (one_mem _))
        (add_mem (one_mem _) (pow_mem (IntermediateField.mem_adjoin_simple_self K u) 2))
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact div_mem
      (add_mem (one_mem _) (IntermediateField.subset_adjoin K {x, y} (Set.mem_insert_of_mem x rfl)))
      (IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y}))

/-- **Exercise 18.6 — Exact biconditional characterization** (§18.5, p. 146; `QUEUE.md` hold):
For every field `K`, extension `L:K`, and `x, y ∈ L` with `x` transcendental over `K` and
`x² + y² = 1`, `K(x, y) = K((1 + y)/x) ↔ ringChar K ≠ 2`. -/
theorem exercise_18_6_iff {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ 2 + y ^ 2 = 1) :
    IntermediateField.adjoin K ({x, y} : Set L) =
      IntermediateField.adjoin K ({(1 + y) / x} : Set L) ↔ ringChar K ≠ 2 := by
  constructor
  · intro heq hchar2
    exact (exercise_18_6_fails_every_char_two hchar2 hx hxy).2.2 heq
  · intro hchar
    exact (exercise_18_6_repaired hchar hx hxy).2.2.2

/-- Helper for `Exercise 18.7(ii)`: in a UFD/Euclidean domain `K[X]`, if `u^n = c * v^n` with
`n ≥ 1`, `c : K` nonzero, and `u, v ≠ 0`, then `Associated u v` (`u ∣ v` and `v ∣ u`). -/
private theorem isUnit_of_isCoprime_pow_dvd {K : Type*} [Field K] {u v : K[X]} {n : ℕ}
    (hn : 1 ≤ n) (hcop : IsCoprime (u ^ n) (v ^ n)) (hdvd : u ^ n ∣ v ^ n) : IsUnit u := by
  obtain ⟨a, b, hab⟩ := hcop
  have hu1 : u ^ n ∣ 1 := by
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_refl _) a) (dvd_mul_of_dvd_right hdvd b)
  have hun : IsUnit (u ^ n) := isUnit_of_dvd_one hu1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_one] at hun
  exact isUnit_of_mul_isUnit_left hun

private theorem associated_of_pow_eq_C_mul_pow {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n)
    {u v : K[X]} {c : K} (hc : c ≠ 0) (heq : u ^ n = Polynomial.C c * v ^ n) :
    Associated u v := by
  classical
  have hn0 : n ≠ 0 := by omega
  by_cases hv0 : v = 0
  · subst hv0
    have hu0 : u = 0 := by simpa [hn0] using heq
    subst hu0
    exact Associated.refl 0
  have hu0 : u ≠ 0 := by
    intro h0
    subst h0
    have h0' : (0 : K[X]) = Polynomial.C c * v ^ n := by simpa [hn0] using heq
    rcases mul_eq_zero.mp h0'.symm with hc0 | hvpow
    · exact hc (Polynomial.C_eq_zero.mp hc0)
    · exact hv0 (eq_zero_of_pow_eq_zero hvpow)
  let d := EuclideanDomain.gcd u v
  have hd_ne0 : d ≠ 0 := fun h0 => hu0 (by
    have hdvd : d ∣ u := EuclideanDomain.gcd_dvd_left u v
    rw [h0, zero_dvd_iff] at hdvd
    exact hdvd)
  obtain ⟨u', hu'⟩ := EuclideanDomain.gcd_dvd_left u v
  obtain ⟨v', hv'⟩ := EuclideanDomain.gcd_dvd_right u v
  have hcop : IsCoprime u' v' := by
    have hbez := EuclideanDomain.gcd_eq_gcd_ab u v
    refine ⟨EuclideanDomain.gcdA u v, EuclideanDomain.gcdB u v, ?_⟩
    apply mul_left_cancel₀ hd_ne0
    calc d * (EuclideanDomain.gcdA u v * u' + EuclideanDomain.gcdB u v * v')
        = (d * u') * EuclideanDomain.gcdA u v + (d * v') * EuclideanDomain.gcdB u v := by ring
      _ = u * EuclideanDomain.gcdA u v + v * EuclideanDomain.gcdB u v := by rw [← hu', ← hv']
      _ = d := hbez.symm
      _ = d * 1 := (mul_one d).symm
  have hpow' : u' ^ n = Polynomial.C c * v' ^ n := by
    apply mul_left_cancel₀ (pow_ne_zero n hd_ne0)
    calc d ^ n * u' ^ n = (d * u') ^ n := (mul_pow d u' n).symm
      _ = u ^ n := by rw [← hu']
      _ = Polynomial.C c * v ^ n := heq
      _ = Polynomial.C c * (d * v') ^ n := by rw [hv']
      _ = d ^ n * (Polynomial.C c * v' ^ n) := by rw [mul_pow]; ring
  have hu'_dvd_v' : u' ^ n ∣ v' ^ n := ⟨Polynomial.C c⁻¹, by
    rw [hpow', mul_comm (Polynomial.C c) (v' ^ n), mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
      map_one, mul_one]⟩
  have hv'_dvd_u' : v' ^ n ∣ u' ^ n := ⟨Polynomial.C c, by rw [hpow', mul_comm]⟩
  have hcop_pow : IsCoprime (u' ^ n) (v' ^ n) := hcop.pow
  have hu'_unit : IsUnit u' := isUnit_of_isCoprime_pow_dvd hn hcop_pow hu'_dvd_v'
  have hv'_unit : IsUnit v' := isUnit_of_isCoprime_pow_dvd hn hcop_pow.symm hv'_dvd_u'
  conv_lhs => rw [hu']
  conv_rhs => rw [hv']
  exact ((associated_one_iff_isUnit.mpr hu'_unit).mul_left d).trans
    ((associated_one_iff_isUnit.mpr hv'_unit).mul_left d).symm

/-- Helper for `Exercise 18.7(ii)`: any triple `(f, g, h)` in `K[X]` satisfying
`IsGarlingRelativelyPrime {f, g, h}`, `max (deg f, deg g, deg h) ≥ 1`, and `f^n + g^n = h^n`
(`n ≥ 1`) automatically satisfies `f ≠ 0`, `g ≠ 0`, `h ≠ 0`, and pairwise coprimality
`IsCoprime f g ∧ IsCoprime f h ∧ IsCoprime g h`. -/
private theorem fermat_triple_nonzero_and_pairwise_coprime {K : Type*} [Field K] {n : ℕ}
    (hn : 1 ≤ n) {f g h : K[X]}
    (hcop : IsGarlingRelativelyPrime ({f, g, h} : Set K[X]))
    (hmax : 1 ≤ max (max f.natDegree g.natDegree) h.natDegree)
    (heq : f ^ n + g ^ n = h ^ n) :
    f ≠ 0 ∧ g ≠ 0 ∧ h ≠ 0 ∧ IsCoprime f g ∧ IsCoprime f h ∧ IsCoprime g h := by
  classical
  have hrel_unit : ∀ c : K[X], c ∣ f → c ∣ g → c ∣ h → IsUnit c := fun c hcf hcg hch =>
    isUnit_of_dvd_one (hcop.2.2 c (by
      rintro x (rfl | rfl | rfl)
      · exact hcf
      · exact hcg
      · exact hch))
  have hf0 : f ≠ 0 := by
    intro hf
    subst hf
    have hgn : g ^ n = Polynomial.C (1 : K) * h ^ n := by
      simpa [Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)] using heq
    have hass : Associated g h := associated_of_pow_eq_C_mul_pow hn one_ne_zero hgn
    have hu_h : IsUnit h := hrel_unit h (dvd_zero h) hass.symm.dvd (dvd_refl h)
    have hu_g : IsUnit g := hass.isUnit_iff.mpr hu_h
    have hdg : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_g
    have hdh : h.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_h
    simp [hdg, hdh] at hmax
  have hg0 : g ≠ 0 := by
    intro hg
    subst hg
    have hfn : f ^ n = Polynomial.C (1 : K) * h ^ n := by
      simpa [Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)] using heq
    have hass : Associated f h := associated_of_pow_eq_C_mul_pow hn one_ne_zero hfn
    have hu_h : IsUnit h := hrel_unit h hass.symm.dvd (dvd_zero h) (dvd_refl h)
    have hu_f : IsUnit f := hass.isUnit_iff.mpr hu_h
    have hdf : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_f
    have hdh : h.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_h
    simp [hdf, hdh] at hmax
  have hh0 : h ≠ 0 := by
    intro hh
    subst hh
    have hfn : f ^ n = Polynomial.C (-1 : K) * g ^ n := by
      have h0 : f ^ n + g ^ n = 0 := by
        simpa [Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)] using heq
      have : f ^ n = -(g ^ n) := eq_neg_of_add_eq_zero_left h0
      simpa using this
    have hass : Associated f g := associated_of_pow_eq_C_mul_pow hn (neg_ne_zero.mpr one_ne_zero) hfn
    have hu_g : IsUnit g := hrel_unit g hass.symm.dvd (dvd_refl g) (dvd_zero g)
    have hu_f : IsUnit f := hass.isUnit_iff.mpr hu_g
    have hdf : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_f
    have hdg : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_g
    simp [hdf, hdg] at hmax
  -- Pairwise coprimality: any irreducible dividing two of `{f, g, h}` divides the third
  have hpair : ∀ u v w : K[X], u ≠ 0 →
      (∀ p : K[X], Prime p → p ∣ u → p ∣ v → p ∣ w) →
      (∀ p : K[X], p ∣ u → p ∣ v → p ∣ w → IsUnit p) → IsCoprime u v := by
    intro u v w hu0 hthird hall
    let d := EuclideanDomain.gcd u v
    have hd_ne0 : d ≠ 0 := fun h0 => hu0 (by
      have hdvd : d ∣ u := EuclideanDomain.gcd_dvd_left u v
      rw [h0, zero_dvd_iff] at hdvd
      exact hdvd)
    have hd_unit : IsUnit d := by
      by_contra hnu
      obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd_ne0
      have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
      have hpu : p ∣ u := hp_dvd.trans (EuclideanDomain.gcd_dvd_left u v)
      have hpv : p ∣ v := hp_dvd.trans (EuclideanDomain.gcd_dvd_right u v)
      have hpw : p ∣ w := hthird p hp_prime hpu hpv
      exact hp_irr.not_isUnit (hall p hpu hpv hpw)
    obtain ⟨u0, hu0_eq⟩ := hd_unit
    have hbez := EuclideanDomain.gcd_eq_gcd_ab u v
    refine ⟨EuclideanDomain.gcdA u v * (u0⁻¹ : K[X]ˣ),
      EuclideanDomain.gcdB u v * (u0⁻¹ : K[X]ˣ), ?_⟩
    calc EuclideanDomain.gcdA u v * (u0⁻¹ : K[X]ˣ) * u +
          EuclideanDomain.gcdB u v * (u0⁻¹ : K[X]ˣ) * v
        = (u * EuclideanDomain.gcdA u v + v * EuclideanDomain.gcdB u v) * (u0⁻¹ : K[X]ˣ) := by ring
      _ = d * (u0⁻¹ : K[X]ˣ) := by rw [← hbez]
      _ = (u0 : K[X]) * (u0⁻¹ : K[X]ˣ) := by rw [hu0_eq]
      _ = 1 := Units.mul_inv u0
  have hcop_fg : IsCoprime f g := hpair f g h hf0
    (fun p hp hpf hpg => hp.dvd_of_dvd_pow (by
      rw [← heq]
      exact dvd_add (dvd_pow hpf (by omega)) (dvd_pow hpg (by omega))))
    hrel_unit
  have hcop_fh : IsCoprime f h := hpair f h g hf0
    (fun p hp hpf hph => hp.dvd_of_dvd_pow (by
      have hgn : g ^ n = h ^ n - f ^ n := by linear_combination heq
      rw [hgn]
      exact dvd_sub (dvd_pow hph (by omega)) (dvd_pow hpf (by omega))))
    (fun p hpf hph hpg => hrel_unit p hpf hpg hph)
  have hcop_gh : IsCoprime g h := hpair g h f hg0
    (fun p hp hpg hph => hp.dvd_of_dvd_pow (by
      have hfn : f ^ n = h ^ n - g ^ n := by linear_combination heq
      rw [hfn]
      exact dvd_sub (dvd_pow hph (by omega)) (dvd_pow hpg (by omega))))
    (fun p hpg hph hpf => hrel_unit p hpf hpg hph)
  exact ⟨hf0, hg0, hh0, hcop_fg, hcop_fh, hcop_gh⟩

/-- **Exercise 18.7(i) — Repaired with `K(x, y) = K(s)`** (§18.5, printed p. 146 / PDF p. 154;
`QUEUE.md` fidelity hold — scan prints ill-typed `K(x, y) = s`):
If `n ≥ 3`, `x` is transcendental over `K`, `xⁿ + yⁿ = 1`, and `K(x, y) = K(s)` for some `s ∈ L`,
then there exist relatively prime polynomials `f, g, h ∈ K[X]` (in Garling's §3.6 sense) with
`f ≠ 0`, `g ≠ 0`, `h ≠ 0`, `max (deg f, deg g, deg h) ≥ 1`, and `fⁿ + gⁿ = hⁿ`. -/
theorem exercise_18_7_i {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (hn : 3 ≤ n) {x y s : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ n + y ^ n = 1)
    (hs : IntermediateField.adjoin K ({x, y} : Set L) = IntermediateField.adjoin K ({s} : Set L)) :
    ∃ f g h : K[X],
      IsGarlingRelativelyPrime ({f, g, h} : Set K[X]) ∧
      f ≠ 0 ∧ g ≠ 0 ∧ h ≠ 0 ∧
      1 ≤ max (max f.natDegree g.natDegree) h.natDegree ∧
      f ^ n + g ^ n = h ^ n := by
  classical
  have hx_in_Ks : x ∈ IntermediateField.adjoin K ({s} : Set L) :=
    hs ▸ IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y})
  have hy_in_Ks : y ∈ IntermediateField.adjoin K ({s} : Set L) :=
    hs ▸ IntermediateField.subset_adjoin K {x, y} (Set.mem_insert_of_mem x rfl)
  have hs_trans : IsGarlingTranscendental K s := by
    intro hs_alg
    have halg_Ks : IsAlgebraicExtension K (IntermediateField.adjoin K ({s} : Set L)) :=
      corollary_1_to_theorem_4_6 hs_alg
    obtain ⟨p, hp0, hpx⟩ := halg_Ks ⟨x, hx_in_Ks⟩
    refine hx ⟨p, hp0, ?_⟩
    have hval := congrArg Subtype.val hpx
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] using hval
  have hs_trans' : Transcendental K s := (isGarlingTranscendental_iff s).mp hs_trans
  let eRF : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({s} : Set L) :=
    RatFunc.algEquivOfTranscendental s hs_trans'
  let rx : RatFunc K := eRF.symm ⟨x, hx_in_Ks⟩
  let ry : RatFunc K := eRF.symm ⟨y, hy_in_Ks⟩
  have hx_eq : x = Polynomial.aeval s rx.num / Polynomial.aeval s rx.denom := by
    have h1 : (eRF rx : L) = x := congrArg Subtype.val (eRF.apply_symm_apply ⟨x, hx_in_Ks⟩)
    rw [← h1]
    exact RatFunc.algEquivOfTranscendental_apply s hs_trans' rx
  have hy_eq : y = Polynomial.aeval s ry.num / Polynomial.aeval s ry.denom := by
    have h1 : (eRF ry : L) = y := congrArg Subtype.val (eRF.apply_symm_apply ⟨y, hy_in_Ks⟩)
    rw [← h1]
    exact RatFunc.algEquivOfTranscendental_apply s hs_trans' ry
  let f₀ : K[X] := rx.num * ry.denom
  let g₀ : K[X] := ry.num * rx.denom
  let h₀ : K[X] := rx.denom * ry.denom
  have hh₀_ne0 : h₀ ≠ 0 := mul_ne_zero (RatFunc.denom_ne_zero rx) (RatFunc.denom_ne_zero ry)
  let d : K[X] := EuclideanDomain.gcd (EuclideanDomain.gcd f₀ g₀) h₀
  have hd_ne0 : d ≠ 0 := fun h0 => hh₀_ne0 (by
    have hdvd : d ∣ h₀ := EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd f₀ g₀) h₀
    rw [h0, zero_dvd_iff] at hdvd
    exact hdvd)
  have hd_f₀ : d ∣ f₀ :=
    (EuclideanDomain.gcd_dvd_left _ h₀).trans (EuclideanDomain.gcd_dvd_left f₀ g₀)
  have hd_g₀ : d ∣ g₀ :=
    (EuclideanDomain.gcd_dvd_left _ h₀).trans (EuclideanDomain.gcd_dvd_right f₀ g₀)
  have hd_h₀ : d ∣ h₀ := EuclideanDomain.gcd_dvd_right _ h₀
  obtain ⟨f, hf_eq⟩ := hd_f₀
  obtain ⟨g, hg_eq⟩ := hd_g₀
  obtain ⟨h, hh_eq⟩ := hd_h₀
  have hh_ne0 : h ≠ 0 := fun h0 => hh₀_ne0 (by simp [hh_eq, h0])
  have hcop : IsGarlingRelativelyPrime ({f, g, h} : Set K[X]) := by
    refine ⟨⟨f, Set.mem_insert f {g, h}⟩, fun _ _ => one_dvd _, fun c hc => ?_⟩
    have hcf : c ∣ f := hc f (Set.mem_insert f {g, h})
    have hcg : c ∣ g := hc g (Set.mem_insert_of_mem f (Set.mem_insert g {h}))
    have hch : c ∣ h := hc h (Set.mem_insert_of_mem f (Set.mem_insert_of_mem g rfl))
    have hcd_f₀ : d * c ∣ f₀ := hf_eq ▸ mul_dvd_mul_left d hcf
    have hcd_g₀ : d * c ∣ g₀ := hg_eq ▸ mul_dvd_mul_left d hcg
    have hcd_h₀ : d * c ∣ h₀ := hh_eq ▸ mul_dvd_mul_left d hch
    have hcd_d : d * c ∣ d :=
      EuclideanDomain.dvd_gcd (EuclideanDomain.dvd_gcd hcd_f₀ hcd_g₀) hcd_h₀
    obtain ⟨k, hk⟩ := hcd_d
    have hck : c * k = 1 := by
      apply mul_left_cancel₀ hd_ne0
      calc d * (c * k) = d * c * k := by ring
        _ = d := hk.symm
        _ = d * 1 := (mul_one d).symm
    exact ⟨k, hck.symm⟩
  -- Check `x = f(s)/h(s)` and `y = g(s)/h(s)`
  have hd_eval_ne0 : Polynomial.aeval s d ≠ 0 := fun h0 => hs_trans ⟨d, hd_ne0, h0⟩
  have hh_eval_ne0 : Polynomial.aeval s h ≠ 0 := fun h0 => hs_trans ⟨h, hh_ne0, h0⟩
  have hrx_den_ne0 : Polynomial.aeval s rx.denom ≠ 0 :=
    fun h0 => hs_trans ⟨rx.denom, RatFunc.denom_ne_zero rx, h0⟩
  have hry_den_ne0 : Polynomial.aeval s ry.denom ≠ 0 :=
    fun h0 => hs_trans ⟨ry.denom, RatFunc.denom_ne_zero ry, h0⟩
  have hx_fh : x = Polynomial.aeval s f / Polynomial.aeval s h := by
    rw [hx_eq, div_eq_div_iff hrx_den_ne0 hh_eval_ne0]
    have h1 := congrArg (Polynomial.aeval s) hf_eq
    have h2 := congrArg (Polynomial.aeval s) hh_eq
    simp only [f₀, h₀, map_mul] at h1 h2
    apply mul_left_cancel₀ hry_den_ne0
    linear_combination (Polynomial.aeval s h) * h1 - (Polynomial.aeval s f) * h2
  have hy_gh : y = Polynomial.aeval s g / Polynomial.aeval s h := by
    rw [hy_eq, div_eq_div_iff hry_den_ne0 hh_eval_ne0]
    have h1 := congrArg (Polynomial.aeval s) hg_eq
    have h2 := congrArg (Polynomial.aeval s) hh_eq
    simp only [g₀, h₀, map_mul] at h1 h2
    apply mul_left_cancel₀ hrx_den_ne0
    linear_combination (Polynomial.aeval s h) * h1 - (Polynomial.aeval s g) * h2
  have hfermat : f ^ n + g ^ n = h ^ n := by
    apply sub_eq_zero.mp
    by_contra hne
    refine hs_trans ⟨f ^ n + g ^ n - h ^ n, hne, ?_⟩
    simp only [map_sub, map_add, map_pow]
    have h1 := hxy
    rw [hx_fh, hy_gh, div_pow, div_pow] at h1
    have hhpow_ne0 : (Polynomial.aeval s h) ^ n ≠ 0 := pow_ne_zero n hh_eval_ne0
    have h2 := congrArg (fun z => z * (Polynomial.aeval s h) ^ n) h1
    simp only [add_mul, one_mul, div_mul_cancel₀ _ hhpow_ne0] at h2
    linear_combination h2
  have hmax : 1 ≤ max (max f.natDegree g.natDegree) h.natDegree := by
    by_contra h0
    push Not at h0
    have hdf0 : f.natDegree = 0 := by omega
    have hdh0 : h.natDegree = 0 := by omega
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hdf0
    have hhC := Polynomial.eq_C_of_natDegree_eq_zero hdh0
    have hxK : x = algebraMap K L (f.coeff 0 / h.coeff 0) := by
      rw [map_div₀]
      conv_lhs => rw [hx_fh, hfC, hhC, Polynomial.aeval_C, Polynomial.aeval_C]
    exact hx ⟨Polynomial.X - Polynomial.C (f.coeff 0 / h.coeff 0),
      Polynomial.X_sub_C_ne_zero _, by simp [hxK]⟩
  obtain ⟨hf_ne0, hg_ne0, hh_ne0', _, _, _⟩ :=
    fermat_triple_nonzero_and_pairwise_coprime (by omega : 1 ≤ n) hcop hmax hfermat
  exact ⟨f, g, h, hcop, hf_ne0, hg_ne0, hh_ne0', hmax, hfermat⟩

/-- **Exercise 18.7(ii) — Part 1 (Divisibilities)** (§18.5, printed p. 146 / PDF p. 154;
`QUEUE.md` fidelity hold):
If `n ≥ 3`, `char K ∤ n`, `f, g, h ∈ K[X]` are relatively prime with
`max (deg f, deg g, deg h) ≥ 1` and `fⁿ + gⁿ = hⁿ`, then
`f^(n-1) ∣ (h * Df - ...)` — specifically:
`f^(n-1) ∣ (h * garlingDeriv g - g * garlingDeriv h)` and
`g^(n-1) ∣ (h * garlingDeriv f - f * garlingDeriv h)`. -/
theorem exercise_18_7_ii_dvd {K : Type*} [Field K] {n : ℕ}
    (hn : 3 ≤ n) (hchar : ¬ ringChar K ∣ n)
    {f g h : K[X]}
    (hcop : IsGarlingRelativelyPrime ({f, g, h} : Set K[X]))
    (hmax : 1 ≤ max (max f.natDegree g.natDegree) h.natDegree)
    (heq : f ^ n + g ^ n = h ^ n) :
    f ≠ 0 ∧ g ≠ 0 ∧ h ≠ 0 ∧
    IsCoprime f g ∧ IsCoprime f h ∧ IsCoprime g h ∧
    f ^ (n - 1) ∣ (h * garlingDeriv g - g * garlingDeriv h) ∧
    g ^ (n - 1) ∣ (h * garlingDeriv f - f * garlingDeriv h) := by
  obtain ⟨hf0, hg0, hh0, hcop_fg, hcop_fh, hcop_gh⟩ :=
    fermat_triple_nonzero_and_pairwise_coprime (by omega : 1 ≤ n) hcop hmax heq
  have hnK_ne0 : (n : K) ≠ 0 := by
    intro h0
    exact hchar ((ringChar.spec K n).mp (by exact_mod_cast h0))
  have hnC_ne0 : (Polynomial.C (n : K) : K[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hnK_ne0
  -- Differentiate `f^n + g^n = h^n`
  have hderiv := congrArg Polynomial.derivative heq
  rw [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_pow,
    Polynomial.derivative_pow] at hderiv
  have hderiv' :
      Polynomial.C (n : K) * (f ^ (n - 1) * Polynomial.derivative f +
        g ^ (n - 1) * Polynomial.derivative g) =
      Polynomial.C (n : K) * (h ^ (n - 1) * Polynomial.derivative h) := by
    have hnat : ∀ p : K[X], (n : K[X]) * p = Polynomial.C (n : K) * p := fun p => by simp
    simp only [mul_add, ← mul_assoc, ← hnat]
    simpa [mul_assoc] using hderiv
  have hcancel : f ^ (n - 1) * Polynomial.derivative f + g ^ (n - 1) * Polynomial.derivative g =
      h ^ (n - 1) * Polynomial.derivative h :=
    mul_left_cancel₀ hnC_ne0 hderiv'
  -- Multiply by `h` and use `h * h^(n-1) = h^n = f^n + g^n = f * f^(n-1) + g * g^(n-1)`
  have hpow_split : ∀ u : K[X], u * u ^ (n - 1) = u ^ n := fun u => by
    conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm]
  have hkey : f ^ (n - 1) * (h * Polynomial.derivative f - f * Polynomial.derivative h) =
      -(g ^ (n - 1) * (h * Polynomial.derivative g - g * Polynomial.derivative h)) := by
    have h1 := congrArg (fun p => h * p) hcancel
    have hh : h * (h ^ (n - 1) * Polynomial.derivative h) =
        (f * f ^ (n - 1) + g * g ^ (n - 1)) * Polynomial.derivative h := by
      rw [← mul_assoc, hpow_split h, ← heq, hpow_split f, hpow_split g]
    rw [hh] at h1
    linear_combination h1
  have hcop_pow : IsCoprime (f ^ (n - 1)) (g ^ (n - 1)) := hcop_fg.pow
  have hf_dvd : f ^ (n - 1) ∣ (h * Polynomial.derivative g - g * Polynomial.derivative h) := by
    have hd1 : f ^ (n - 1) ∣ g ^ (n - 1) * (h * Polynomial.derivative g - g * Polynomial.derivative h) := by
      refine ⟨-(h * Polynomial.derivative f - f * Polynomial.derivative h), ?_⟩
      linear_combination hkey
    exact hcop_pow.dvd_of_dvd_mul_left hd1
  have hg_dvd : g ^ (n - 1) ∣ (h * Polynomial.derivative f - f * Polynomial.derivative h) := by
    have hd1 : g ^ (n - 1) ∣ f ^ (n - 1) * (h * Polynomial.derivative f - f * Polynomial.derivative h) := by
      refine ⟨-(h * Polynomial.derivative g - g * Polynomial.derivative h), ?_⟩
      linear_combination hkey
    exact hcop_pow.symm.dvd_of_dvd_mul_left hd1
  simp only [garlingDeriv_eq_derivative]
  exact ⟨hf0, hg0, hh0, hcop_fg, hcop_fh, hcop_gh, hf_dvd, hg_dvd⟩

/-- Helper for `Exercise 18.7(ii)`: degree bound on Wronskians `u * Dv - v * Du ≠ 0`. -/
private theorem natDegree_wronskian_add_one_le {K : Type*} [Field K] {u v : K[X]}
    (hne : u * Polynomial.derivative v - v * Polynomial.derivative u ≠ 0) :
    (u * Polynomial.derivative v - v * Polynomial.derivative u).natDegree + 1 ≤
      u.natDegree + v.natDegree := by
  have hterm : ∀ a b : K[X], a * Polynomial.derivative b ≠ 0 →
      (a * Polynomial.derivative b).natDegree + 1 ≤ a.natDegree + b.natDegree := by
    intro a b hab
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
    have hdb0 : Polynomial.derivative b ≠ 0 := right_ne_zero_of_mul hab
    have hb_pos : 1 ≤ b.natDegree := by
      by_contra h0
      have hb0 : b.natDegree = 0 := by omega
      rw [Polynomial.eq_C_of_natDegree_eq_zero hb0, Polynomial.derivative_C] at hdb0
      exact hdb0 rfl
    have hdb_le : (Polynomial.derivative b).natDegree ≤ b.natDegree - 1 :=
      Polynomial.natDegree_derivative_le b
    rw [Polynomial.natDegree_mul ha0 hdb0]
    omega
  by_cases h1 : u * Polynomial.derivative v = 0
  · rw [h1, zero_sub, Polynomial.natDegree_neg]
    have h2 : v * Polynomial.derivative u ≠ 0 := by
      intro hz; rw [h1, hz, sub_self] at hne; exact hne rfl
    have := hterm v u h2
    omega
  · by_cases h2 : v * Polynomial.derivative u = 0
    · rw [h2, sub_zero]
      exact hterm u v h1
    · have hb1 := hterm u v h1
      have hb2 := hterm v u h2
      have hsub := Polynomial.natDegree_sub_le (u * Polynomial.derivative v) (v * Polynomial.derivative u)
      omega

/-- Helper for `Exercise 18.7(ii)`: if `u ≠ 0` and `u ∣ Polynomial.derivative u`, then
`Polynomial.derivative u = 0`. -/
private theorem derivative_eq_zero_of_dvd_derivative {K : Type*} [Field K] {u : K[X]}
    (_hu0 : u ≠ 0) (hdvd : u ∣ Polynomial.derivative u) :
    Polynomial.derivative u = 0 := by
  by_contra hdu0
  have hle := Polynomial.natDegree_le_of_dvd hdvd hdu0
  have hlt := Polynomial.natDegree_derivative_lt (p := u) (by
    intro h0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C] at hdu0
    exact hdu0 rfl)
  omega

/-- Helper for `Exercise 18.7(ii)`: over an algebraically closed field `F` of prime characteristic `p`,
every polynomial `u ∈ F[X]` with `u.derivative = 0` is a `p`-th power `u = u₁ ^ p` in `F[X]`. -/
private theorem exists_pow_char_eq_of_derivative_eq_zero {F : Type*} [Field F] [IsAlgClosed F]
    {p : ℕ} (hp : Nat.Prime p) (hchar : ringChar F = p) {u : F[X]}
    (hdu : Polynomial.derivative u = 0) :
    ∃ u₁ : F[X], u₁ ^ p = u := by
  classical
  have : CharP F p := hchar ▸ ringChar.charP F
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hcoeff_zero : ∀ m : ℕ, ¬ p ∣ m → u.coeff m = 0 := by
    intro m hndvd
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have : m = 0 := by omega
      subst this
      exact hndvd (dvd_zero p)
    by_contra hne
    have hspec := (garlingDeriv_eq_zero_iff_char_dvd u).mp
      (by rwa [garlingDeriv_eq_derivative])
    rw [hchar] at hspec
    exact hndvd (hspec m hm1 hne)
  have hroot : ∀ c : F, ∃ r : F, r ^ p = c := fun c => IsAlgClosed.exists_pow_nat_eq c hp.pos
  choose rootP hrootP using hroot
  let N : ℕ := u.natDegree / p + 1
  let term : ℕ → F[X] := fun k => Polynomial.monomial k (rootP (u.coeff (k * p)))
  let u₁ : F[X] := ∑ k ∈ Finset.range N, term k
  refine ⟨u₁, ?_⟩
  have hpow_sum : u₁ ^ p = ∑ k ∈ Finset.range N, (term k) ^ p := by
    dsimp only [u₁]
    induction (Finset.range N) using Finset.induction_on with
    | empty => simp [zero_pow hp.ne_zero]
    | @insert a s has ih =>
      rw [Finset.sum_insert has, add_pow_char, ih, Finset.sum_insert has]
  rw [hpow_sum]
  ext m
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ k : ℕ,
      ((term k) ^ p).coeff m =
        if k * p = m then u.coeff (k * p) else 0 := by
    intro k
    dsimp only [term]
    rw [Polynomial.monomial_pow, hrootP, Polynomial.coeff_monomial]
  simp only [hterm]
  by_cases hm : p ∣ m
  · obtain ⟨k, rfl⟩ := hm
    by_cases hkN : k ∈ Finset.range N
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hbk
        have hne : b * p ≠ p * k := by
          intro heq
          exact hbk (Nat.eq_of_mul_eq_mul_right hp.pos (by linarith))
        simp [hne]
      · intro hnot; exact absurd hkN hnot
    · have hkge : u.natDegree / p + 1 ≤ k := by
        simpa [N, Finset.mem_range] using hkN
      have hlt : u.natDegree < p * k := by
        have hdiv : u.natDegree < (u.natDegree / p + 1) * p := by
          have := Nat.div_add_mod u.natDegree p
          have := Nat.mod_lt u.natDegree hp.pos
          nlinarith
        nlinarith
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hblt : b < N := Finset.mem_range.mp hb
      have hne : b * p ≠ p * k := by
        intro heq
        have hbk : b = k := Nat.eq_of_mul_eq_mul_right hp.pos (by linarith)
        omega
      simp [hne]
  · rw [hcoeff_zero m hm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : b * p ≠ m := fun heq => hm ⟨b, by linarith⟩
    simp [hne]

/-- Helper for `Exercise 18.7(ii)`: Fermat impossibility over an algebraically closed field `F`
with `char F ∤ n`, proved by strong induction on `max (deg f, deg g, deg h)` (handling both
the Wronskian degree contradiction and characteristic-`p` `p`-th-root descent). -/
private theorem fermat_poly_impossible_algClosed {F : Type*} [Field F] [IsAlgClosed F]
    {n : ℕ} (hn : 3 ≤ n) (hchar : ¬ ringChar F ∣ n) :
    ∀ M : ℕ, ∀ f g h : F[X],
      max (max f.natDegree g.natDegree) h.natDegree = M →
      1 ≤ M →
      IsGarlingRelativelyPrime ({f, g, h} : Set F[X]) →
      f ^ n + g ^ n = h ^ n →
      False := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro f g h hM hM1 hcop heq
    obtain ⟨hf0, hg0, hh0, hcop_fg, hcop_fh, hcop_gh, hf_dvd, hg_dvd⟩ :=
      exercise_18_7_ii_dvd hn hchar hcop (hM.symm ▸ hM1) heq
    simp only [garlingDeriv_eq_derivative] at hf_dvd hg_dvd
    by_cases hW : h * Polynomial.derivative g - g * Polynomial.derivative h ≠ 0
    · -- Non-vanishing Wronskian case: degree contradiction!
      have hWf : h * Polynomial.derivative f - f * Polynomial.derivative h ≠ 0 := by
        intro hWf0
        -- From `h * Df = f * Dh` and `IsCoprime f h`, `Df = 0` and `Dh = 0`, contradicting `hW`
        have hfd : f ∣ Polynomial.derivative f :=
          hcop_fh.dvd_of_dvd_mul_left ⟨Polynomial.derivative h, by linear_combination hWf0⟩
        have hhd : h ∣ Polynomial.derivative h :=
          hcop_fh.symm.dvd_of_dvd_mul_left ⟨Polynomial.derivative f, by linear_combination -hWf0⟩
        have hdf0 : Polynomial.derivative f = 0 := derivative_eq_zero_of_dvd_derivative hf0 hfd
        have hdh0 : Polynomial.derivative h = 0 := derivative_eq_zero_of_dvd_derivative hh0 hhd
        -- Differentiating `f^n + g^n = h^n` gives `n * g^(n-1) * Dg = 0`, so `Dg = 0`!
        have hderiv := congrArg Polynomial.derivative heq
        rw [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_pow,
          Polynomial.derivative_pow, hdf0, hdh0, mul_zero, mul_zero, zero_add] at hderiv
        have hnK_ne0 : (n : F) ≠ 0 := fun h0 =>
          hchar ((ringChar.spec F n).mp (by exact_mod_cast h0))
        have hdg0 : Polynomial.derivative g = 0 := by
          have h1 : (Polynomial.C (n : F) * g ^ (n - 1)) * Polynomial.derivative g = 0 := by
            simpa [mul_assoc] using hderiv
          exact (mul_eq_zero.mp h1).resolve_left
            (mul_ne_zero (Polynomial.C_ne_zero.mpr hnK_ne0) (pow_ne_zero (n - 1) hg0))
        exact hW (by rw [hdg0, hdh0]; ring)
      -- Degree bounds from `f^(n-1) ∣ W_g` and `g^(n-1) ∣ W_f`
      have hdeg_f : (n - 1) * f.natDegree + 1 ≤ g.natDegree + h.natDegree := by
        have h1 := Polynomial.natDegree_le_of_dvd hf_dvd hW
        rw [Polynomial.natDegree_pow] at h1
        have h2 := natDegree_wronskian_add_one_le hW
        omega
      have hdeg_g : (n - 1) * g.natDegree + 1 ≤ f.natDegree + h.natDegree := by
        have h1 := Polynomial.natDegree_le_of_dvd hg_dvd hWf
        rw [Polynomial.natDegree_pow] at h1
        have h2 := natDegree_wronskian_add_one_le hWf
        omega
      -- `deg h ≤ max (deg f) (deg g)` from `h^n = f^n + g^n`
      have hdeg_h : h.natDegree ≤ max f.natDegree g.natDegree := by
        have h1 : n * h.natDegree ≤ max (n * f.natDegree) (n * g.natDegree) := by
          rw [← Polynomial.natDegree_pow, ← heq]
          calc (f ^ n + g ^ n).natDegree
              ≤ max (f ^ n).natDegree (g ^ n).natDegree := Polynomial.natDegree_add_le _ _
            _ = max (n * f.natDegree) (n * g.natDegree) := by
                rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow]
        rcases le_total f.natDegree g.natDegree with hfg | hgf
        · rw [max_eq_right hfg]
          have : max (n * f.natDegree) (n * g.natDegree) = n * g.natDegree :=
            max_eq_right (Nat.mul_le_mul_left n hfg)
          rw [this] at h1
          exact Nat.le_of_mul_le_mul_left h1 (by omega)
        · rw [max_eq_left hgf]
          have : max (n * f.natDegree) (n * g.natDegree) = n * f.natDegree :=
            max_eq_left (Nat.mul_le_mul_left n hgf)
          rw [this] at h1
          exact Nat.le_of_mul_le_mul_left h1 (by omega)
      -- Arithmetic contradiction for `n ≥ 3`
      have hmax_fg : 1 ≤ max f.natDegree g.natDegree := by omega
      have hn2 : 2 ≤ n - 1 := by omega
      rcases le_total f.natDegree g.natDegree with hfg | hgf
      · have hg_pos : 1 ≤ g.natDegree := by omega
        have hh_le : h.natDegree ≤ g.natDegree := by omega
        have : 2 * g.natDegree ≤ (n - 1) * g.natDegree := Nat.mul_le_mul_right g.natDegree hn2
        omega
      · have hf_pos : 1 ≤ f.natDegree := by omega
        have hh_le : h.natDegree ≤ f.natDegree := by omega
        have : 2 * f.natDegree ≤ (n - 1) * f.natDegree := Nat.mul_le_mul_right f.natDegree hn2
        omega
    · -- Vanishing Wronskian case: `h * Dg - g * Dh = 0`, forcing `Df = Dg = Dh = 0`!
      push Not at hW
      have hgd : g ∣ Polynomial.derivative g :=
        hcop_gh.dvd_of_dvd_mul_left ⟨Polynomial.derivative h, by linear_combination hW⟩
      have hhd : h ∣ Polynomial.derivative h :=
        hcop_gh.symm.dvd_of_dvd_mul_left ⟨Polynomial.derivative g, by linear_combination -hW⟩
      have hdg0 : Polynomial.derivative g = 0 := derivative_eq_zero_of_dvd_derivative hg0 hgd
      have hdh0 : Polynomial.derivative h = 0 := derivative_eq_zero_of_dvd_derivative hh0 hhd
      have hderiv := congrArg Polynomial.derivative heq
      rw [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_pow,
        Polynomial.derivative_pow, hdg0, hdh0, mul_zero, mul_zero, add_zero] at hderiv
      have hnK_ne0 : (n : F) ≠ 0 := fun h0 =>
        hchar ((ringChar.spec F n).mp (by exact_mod_cast h0))
      have hdf0 : Polynomial.derivative f = 0 := by
        have h1 : (Polynomial.C (n : F) * f ^ (n - 1)) * Polynomial.derivative f = 0 := by
          simpa [mul_assoc] using hderiv
        exact (mul_eq_zero.mp h1).resolve_left
          (mul_ne_zero (Polynomial.C_ne_zero.mpr hnK_ne0) (pow_ne_zero (n - 1) hf0))
      rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | hzero
      · -- Positive prime characteristic `p`: extract `p`-th roots `f₁, g₁, h₁` and descend!
        set p := ringChar F
        have : CharP F p := ringChar.charP F
        have : Fact (Nat.Prime p) := ⟨hp⟩
        obtain ⟨f₁, hf₁⟩ := exists_pow_char_eq_of_derivative_eq_zero hp rfl hdf0
        obtain ⟨g₁, hg₁⟩ := exists_pow_char_eq_of_derivative_eq_zero hp rfl hdg0
        obtain ⟨h₁, hh₁⟩ := exists_pow_char_eq_of_derivative_eq_zero hp rfl hdh0
        have heq₁ : f₁ ^ n + g₁ ^ n = h₁ ^ n := by
          apply sub_eq_zero.mp
          apply eq_zero_of_pow_eq_zero (n := p)
          have hchar_pow : (f₁ ^ n + g₁ ^ n - h₁ ^ n) ^ p =
              (f₁ ^ n) ^ p + (g₁ ^ n) ^ p - (h₁ ^ n) ^ p := by
            rw [sub_pow_char, add_pow_char]
          rw [hchar_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n p, pow_mul, pow_mul, pow_mul,
            hf₁, hg₁, hh₁, heq, sub_self]
        have hcop₁ : IsGarlingRelativelyPrime ({f₁, g₁, h₁} : Set F[X]) := by
          refine ⟨⟨f₁, Set.mem_insert f₁ {g₁, h₁}⟩, fun _ _ => one_dvd _, fun c hc => ?_⟩
          have hcf : c ∣ f := hf₁ ▸ dvd_pow (hc f₁ (Set.mem_insert f₁ {g₁, h₁})) hp.ne_zero
          have hcg : c ∣ g := hg₁ ▸ dvd_pow (hc g₁ (Set.mem_insert_of_mem f₁ (Set.mem_insert g₁ {h₁}))) hp.ne_zero
          have hch : c ∣ h := hh₁ ▸ dvd_pow (hc h₁ (Set.mem_insert_of_mem f₁ (Set.mem_insert_of_mem g₁ rfl))) hp.ne_zero
          exact hcop.2.2 c (by rintro x (rfl | rfl | rfl) <;> assumption)
        have hdeg_f : f.natDegree = p * f₁.natDegree := by rw [← hf₁, Polynomial.natDegree_pow]
        have hdeg_g : g.natDegree = p * g₁.natDegree := by rw [← hg₁, Polynomial.natDegree_pow]
        have hdeg_h : h.natDegree = p * h₁.natDegree := by rw [← hh₁, Polynomial.natDegree_pow]
        let M₁ := max (max f₁.natDegree g₁.natDegree) h₁.natDegree
        have hM_eq : M = p * M₁ := by
          rw [← hM, hdeg_f, hdeg_g, hdeg_h]
          dsimp only [M₁]
          rw [Nat.mul_max_mul_left, Nat.mul_max_mul_left]
        have hp2 : 2 ≤ p := hp.two_le
        have hM₁_pos : 1 ≤ M₁ := by nlinarith
        have hM₁_lt : M₁ < M := by nlinarith
        exact ih M₁ hM₁_lt f₁ g₁ h₁ rfl hM₁_pos hcop₁ heq₁
      · -- Characteristic `0`: `Df = Dg = Dh = 0` forces `deg f = deg g = deg h = 0`, contradicting `M ≥ 1`
        have hdeg0 : ∀ u : F[X], Polynomial.derivative u = 0 → u.natDegree = 0 := by
          intro u hdu
          have hspec := (garlingDeriv_eq_zero_iff_char_dvd u).mp
            (by rwa [garlingDeriv_eq_derivative])
          rw [hzero] at hspec
          have hcoeff : ∀ m : ℕ, 1 ≤ m → u.coeff m = 0 := by
            intro m hm
            by_contra hne
            have h0dvd : 0 ∣ m := hspec m hm hne
            rw [zero_dvd_iff] at h0dvd
            omega
          exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr
            (Polynomial.degree_le_zero_iff.mpr (by
              ext m
              cases m with
              | zero => simp
              | succ k => simp [hcoeff (k + 1) (Nat.succ_pos k)]))
        rw [hdeg0 f hdf0, hdeg0 g hdg0, hdeg0 h hdh0] at hM
        simp at hM
        omega

/-- **Exercise 18.7(ii) — Part 2 (Polynomial Fermat Impossibility)** (§18.5, printed p. 146 /
PDF p. 154; `QUEUE.md` fidelity hold):
Over **every** field `K` with `char K ∤ n` (`n ≥ 3`), there do NOT exist relatively prime
polynomials `f, g, h ∈ K[X]` with `max (deg f, deg g, deg h) ≥ 1` and `fⁿ + gⁿ = hⁿ`. -/
theorem exercise_18_7_ii_impossible {K : Type*} [Field K] {n : ℕ}
    (hn : 3 ≤ n) (hchar : ¬ ringChar K ∣ n)
    {f g h : K[X]}
    (hcop : IsGarlingRelativelyPrime ({f, g, h} : Set K[X]))
    (hmax : 1 ≤ max (max f.natDegree g.natDegree) h.natDegree)
    (heq : f ^ n + g ^ n = h ^ n) : False := by
  obtain ⟨_, _, _, hcop_fg, _, _⟩ :=
    fermat_triple_nonzero_and_pairwise_coprime (by omega : 1 ≤ n) hcop hmax heq
  let F := AlgebraicClosure K
  let ι : K →+* F := algebraMap K F
  have hι_inj : Function.Injective ι := ι.injective
  have hcharF : ringChar F = ringChar K := (ringChar.eq_iff.mpr (by
    have : CharP K (ringChar K) := ringChar.charP K
    exact RingHom.charP_iff_charP ι (ringChar K) |>.mp inferInstance))
  let f' : F[X] := f.map ι
  let g' : F[X] := g.map ι
  let h' : F[X] := h.map ι
  have hcop' : IsGarlingRelativelyPrime ({f', g', h'} : Set F[X]) := by
    refine ⟨⟨f', Set.mem_insert f' {g', h'}⟩, fun _ _ => one_dvd _, fun c hc => ?_⟩
    obtain ⟨a, b, hab⟩ := hcop_fg
    have hab' : a.map ι * f' + b.map ι * g' = 1 := by
      have h1 := congrArg (Polynomial.map ι) hab
      simpa [f', g', Polynomial.map_add, Polynomial.map_mul] using h1
    rw [← hab']
    exact dvd_add
      (dvd_mul_of_dvd_right (hc f' (Set.mem_insert f' {g', h'})) (a.map ι))
      (dvd_mul_of_dvd_right (hc g' (Set.mem_insert_of_mem f' (Set.mem_insert g' {h'}))) (b.map ι))
  have hmax' : 1 ≤ max (max f'.natDegree g'.natDegree) h'.natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hι_inj,
      Polynomial.natDegree_map_eq_of_injective hι_inj,
      Polynomial.natDegree_map_eq_of_injective hι_inj]
  have heq' : f' ^ n + g' ^ n = h' ^ n := by
    have h1 := congrArg (Polynomial.map ι) heq
    simpa [f', g', h', Polynomial.map_add, Polynomial.map_pow] using h1
  exact fermat_poly_impossible_algClosed hn (hcharF.symm ▸ hchar)
    (max (max f'.natDegree g'.natDegree) h'.natDegree) f' g' h' rfl hmax' hcop' heq'

/-- **Exercise 18.7 — Repaired full theorem (with `K(x, y) = K(s)`)** (§18.5, printed p. 146 /
PDF p. 154; `QUEUE.md` fidelity hold — scan prints ill-typed `K(x, y) = s`):
Suppose `n ≥ 3`, `K(x, y) : K` is an extension with `x` transcendental over `K`, `xⁿ + yⁿ = 1`,
and `char K ∤ n`. Then `K(x, y)` is NOT a simple extension of `K` (there is no `s ∈ L` with
`K(x, y) = K(s)`), hence not purely transcendental over `K` of transcendence degree `1`. -/
theorem exercise_18_7_repaired {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (hn : 3 ≤ n) (hchar : ¬ ringChar K ∣ n) {x y : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ n + y ^ n = 1) :
    ¬ ∃ s : L, IntermediateField.adjoin K ({x, y} : Set L) =
      IntermediateField.adjoin K ({s} : Set L) := by
  rintro ⟨s, hs⟩
  obtain ⟨f, g, h, hcop, _, _, _, hmax, heq⟩ := exercise_18_7_i hn hx hxy hs
  exact exercise_18_7_ii_impossible hn hchar hcop hmax heq

/-- **Exercise 18.7 — Non-pure-transcendence conclusion** (§18.5, printed p. 146 / PDF p. 154;
`QUEUE.md` fidelity hold):
Under the repaired hypotheses of `Exercise 18.7` (`n ≥ 3`, `char K ∤ n`, `x` transcendental over
`K`, `xⁿ + yⁿ = 1`), `K(x, y) : K` has transcendence degree `1` (`{x}` is a transcendence basis),
and is neither `IsGarlingPurelyTranscendental` nor `IsPurelyTranscendental` over `K`. -/
theorem exercise_18_7_not_purelyTranscendental {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hn : 3 ≤ n) (hchar : ¬ ringChar K ∣ n) {x y : L}
    (hx : IsGarlingTranscendental K x) (hxy : x ^ n + y ^ n = 1) :
    let Kxy := IntermediateField.adjoin K ({x, y} : Set L)
    transcendenceDegree K Kxy = 1 ∧
    ¬ IsGarlingPurelyTranscendental K Kxy ∧
    ¬ IsPurelyTranscendental K Kxy := by
  intro Kxy
  let x' : Kxy := ⟨x, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y})⟩
  let y' : Kxy := ⟨y, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert_of_mem x rfl)⟩
  have hx'_trans : IsGarlingTranscendental K x' := by
    intro ⟨p, hp0, hpx⟩
    refine hx ⟨p, hp0, ?_⟩
    have hv := congrArg Kxy.val hpx
    simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
    exact hv
  have hS_ind : IsGarlingAlgebraicallyIndependent K ({x'} : Set Kxy) :=
    (isGarlingAlgebraicallyIndependent_singleton_iff x').mpr hx'_trans
  have hS_alg : IsAlgebraicExtension (IntermediateField.adjoin K ({x'} : Set Kxy)) Kxy := by
    let Kx' := IntermediateField.adjoin K ({x'} : Set Kxy)
    have hy'_alg : IsGarlingAlgebraic Kx' y' := by
      let c : Kx' := ⟨x' ^ n - 1, sub_mem (pow_mem (IntermediateField.mem_adjoin_simple_self K x') n)
        (one_mem _)⟩
      refine ⟨Polynomial.X ^ n + Polynomial.C c, ?_, ?_⟩
      · intro hp0
        have hcoeff := congrArg (fun p : Kx'[X] => p.coeff n) hp0
        simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_self, Polynomial.coeff_C,
          show n ≠ 0 by omega, ↓reduceIte, add_zero, Polynomial.coeff_zero] at hcoeff
        exact one_ne_zero hcoeff
      · apply Subtype.ext
        have hval : ((Polynomial.aeval y' (Polynomial.X ^ n + Polynomial.C c) : Kxy) : L) =
            y ^ n + (x ^ n - 1) := by
          simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
          rfl
        rw [hval]
        change y ^ n + (x ^ n - 1) = 0
        linear_combination hxy
    have hKxy_le : (⊤ : IntermediateField Kx' Kxy) ≤ IntermediateField.adjoin Kx' ({y'} : Set Kxy) := by
      intro z _
      have hz_mem : (z : L) ∈ IntermediateField.adjoin K ({x, y} : Set L) := z.2
      have hmap_le : IntermediateField.adjoin K ({x, y} : Set L) ≤
          ((IntermediateField.adjoin Kx' ({y'} : Set Kxy)).restrictScalars K).map Kxy.val := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w (rfl | hw)
        · exact ⟨x', (IntermediateField.adjoin Kx' ({y'} : Set Kxy)).algebraMap_mem
            ⟨x', IntermediateField.mem_adjoin_simple_self K x'⟩, rfl⟩
        · rw [Set.mem_singleton_iff.mp hw]
          exact ⟨y', IntermediateField.mem_adjoin_simple_self Kx' y', rfl⟩
      obtain ⟨z', hz', hzz⟩ := hmap_le hz_mem
      have hzeq : z' = z := Subtype.ext hzz
      exact hzeq ▸ hz'
    have h1 := corollary_1_to_theorem_4_6 hy'_alg
    intro z
    obtain ⟨p, hp0, hpz⟩ := h1 ⟨z, hKxy_le trivial⟩
    refine ⟨p, hp0, ?_⟩
    have hv := congrArg (IntermediateField.adjoin Kx' ({y'} : Set Kxy)).val hpz
    simp only [← Polynomial.aeval_algHom_apply, map_zero] at hv
    exact hv
  have hx'_basis : IsGarlingTranscendenceBasis K ({x'} : Set Kxy) :=
    (theorem_18_4 ({x'} : Set Kxy)).mpr ⟨hS_ind, hS_alg⟩
  have htrdeg : transcendenceDegree K Kxy = 1 :=
    (transcendenceDegree_eq_natCast_iff 1).mpr
      ⟨{x'}, hx'_basis, Set.finite_singleton x', Set.ncard_singleton x'⟩
  have hnot_pure : ¬ IsPurelyTranscendental K Kxy := by
    rintro ⟨S, hS_basis, hS_top⟩
    have hS1 : S.Finite ∧ S.ncard = 1 := by
      rcases corollary_to_theorem_18_6 hS_basis hx'_basis with ⟨_, hinf⟩ | ⟨hSf, _, hnc⟩
      · exact False.elim (hinf (Set.finite_singleton x'))
      · exact ⟨hSf, hnc.trans (Set.ncard_singleton x')⟩
    obtain ⟨s', rfl⟩ := Set.ncard_eq_one.mp hS1.2
    refine exercise_18_7_repaired hn hchar hx hxy ⟨(s' : L), ?_⟩
    apply le_antisymm
    · intro z hz
      have hz' : (⟨z, hz⟩ : Kxy) ∈ IntermediateField.adjoin K ({s'} : Set Kxy) :=
        hS_top ▸ IntermediateField.mem_top
      have hmap : z ∈ (IntermediateField.adjoin K ({s'} : Set Kxy)).map Kxy.val :=
        ⟨⟨z, hz⟩, hz', rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
      exact hmap
    · exact IntermediateField.adjoin_simple_le_iff.mpr s'.2
  exact ⟨htrdeg, fun h => hnot_pure ⟨h.2.choose, h.2.choose_spec.2.1, h.2.choose_spec.2.2⟩, hnot_pure⟩

end Garling.Chapter18
