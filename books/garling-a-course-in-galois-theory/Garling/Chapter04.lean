import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Cardinality

/-!
# Chapter 4: Field extensions

Formalization of Chapter 4 (printed pp. 39–48, PDF pp. 47–56) of D. J. H. Garling,
*A Course in Galois Theory* (Cambridge University Press, 1986), following the chapter's
five sections (§4.1 *Introduction*, §4.2 *Field extensions*, §4.3 *Algebraic and transcendental
elements*, §4.4 *Algebraic extensions*, §4.5 *Monomorphisms of algebraic extensions*) and all
numbered/corollary items in source order.
-/

namespace Garling.Chapter04

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open scoped BigOperators Polynomial

/-! ## §4.1 Introduction (printed pp. 39–40, PDF pp. 47–48) -/

/-- Motivating linear example (§4.1, p. 39): `2x + 3 = 0` has no solution in `ℤ`, whereas over `ℚ`
it has the unique solution `x = -3 / 2`. -/
theorem intro_linear_equation :
    (¬ ∃ x : ℤ, 2 * x + 3 = 0) ∧
    (∃! x : ℚ, 2 * x + 3 = 0 ∧ x = -3 / 2) := by
  refine ⟨by rintro ⟨x, hx⟩; omega, ⟨-3 / 2, ⟨by ring, rfl⟩, ?_⟩⟩
  rintro y ⟨_, rfl⟩
  rfl

/-- Motivating quadratic example (§4.1, pp. 39–40): `x² - 2x - 1` completes the square as
`(x - 1)² - 2`, has no root in `ℚ`, is irreducible in `ℚ[X]` (and in `ℤ[X]`), and factorizes into
linear factors `(x - (1 - √2))(x - (1 + √2))` over `ℝ` and over `K = ℚ(√2)` (`qSqrtTwoSubfield`). -/
theorem intro_quadratic_equation :
    (¬ ∃ r : ℚ, r ^ 2 - 2 * r - 1 = 0) ∧
    Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ) * Polynomial.X - 1 : ℚ[X]) ∧
    Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ℤ) * Polynomial.X - 1 : ℤ[X]) ∧
    ((Polynomial.X ^ 2 - Polynomial.C (2 : ℝ) * Polynomial.X - 1 : ℝ[X]) =
      (Polynomial.X - Polynomial.C (1 - Real.sqrt 2)) *
        (Polynomial.X - Polynomial.C (1 + Real.sqrt 2))) ∧
    ∃ α₁ α₂ : qSqrtTwoSubfield,
      (Polynomial.X ^ 2 - Polynomial.C (2 : qSqrtTwoSubfield) * Polynomial.X - 1 :
          qSqrtTwoSubfield[X]) =
        (Polynomial.X - Polynomial.C α₁) * (Polynomial.X - Polynomial.C α₂) := by
  have hno_rat_root : ¬ ∃ r : ℚ, r ^ 2 - 2 * r - 1 = 0 := by
    rintro ⟨r, hr⟩
    have hsq : ((r - 1 : ℚ) : ℝ) ^ 2 = 2 := by
      have hq : (r - 1) ^ 2 = 2 := by linear_combination hr
      exact_mod_cast hq
    have habs : |((r - 1 : ℚ) : ℝ)| = Real.sqrt 2 := by
      rw [← Real.sqrt_sq_eq_abs, hsq]
    rcases abs_cases ((r - 1 : ℚ) : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
    · exact sqrt_two_irrational ⟨r - 1, h ▸ habs⟩
    · have hneg : ((-(r - 1) : ℚ) : ℝ) = Real.sqrt 2 := by
        rw [← habs, h]
        push_cast
        ring
      exact sqrt_two_irrational ⟨-(r - 1), hneg⟩
  let pZ : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C 2 * Polynomial.X - 1
  have hpZ_deg : pZ.natDegree = 2 := by
    dsimp [pZ]
    compute_degree!
  have hpZ_monic : pZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hpZ_deg]
    dsimp [pZ]
    simp [Polynomial.coeff_one, Polynomial.coeff_X]
  have hpZ_irred : Irreducible pZ := by
    refine ⟨fun hu => by have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, ?_⟩
    intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · by_cases hb : IsUnit b
      · exact Or.inr hb
      · exfalso
        have ha0 : a ≠ 0 := fun h0 => by
          rw [h0, zero_mul] at hab
          exact hpZ_monic.ne_zero hab
        have hb0 : b ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at hab
          exact hpZ_monic.ne_zero hab
        have hlc_unit : IsUnit a.leadingCoeff ∧ IsUnit b.leadingCoeff := by
          have hprod : a.leadingCoeff * b.leadingCoeff = 1 := by
            rw [← Polynomial.leadingCoeff_mul, ← hab, hpZ_monic.leadingCoeff]
          exact ⟨IsUnit.of_mul_eq_one b.leadingCoeff hprod,
            IsUnit.of_mul_eq_one_right a.leadingCoeff hprod⟩
        have hadeg_pos : 0 < a.natDegree := by
          by_contra hle
          have h0 : a.natDegree = 0 := by omega
          rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at ha
          have hca : a.coeff 0 = a.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
          exact ha (hca ▸ hlc_unit.1.map Polynomial.C)
        have hbdeg_pos : 0 < b.natDegree := by
          by_contra hle
          have h0 : b.natDegree = 0 := by omega
          rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hb
          have hcb : b.coeff 0 = b.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
          exact hb (hcb ▸ hlc_unit.2.map Polynomial.C)
        have hdeg_sum : a.natDegree + b.natDegree = 2 := by
          rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hpZ_deg]
        have ha1 : a.natDegree = 1 := by omega
        have alc_pm1 : a.leadingCoeff = 1 ∨ a.leadingCoeff = -1 := Int.isUnit_iff.mp hlc_unit.1
        let r : ℚ := -(a.coeff 0 : ℚ) / (a.coeff 1 : ℚ)
        have ha1_ne : (a.coeff 1 : ℚ) ≠ 0 := by
          have h1 : a.coeff 1 = a.leadingCoeff := by rw [Polynomial.leadingCoeff, ha1]
          rcases alc_pm1 with h | h <;> simp [h1, h]
        have ha_eq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) :=
          Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq ha1)
        have ha_eval : Polynomial.aeval r a = 0 := by
          rw [ha_eq]
          simp [r, mul_div_cancel₀ _ ha1_ne]
        have hp_eval : Polynomial.aeval r pZ = 0 := by
          rw [hab, map_mul, ha_eval, zero_mul]
        apply hno_rat_root
        refine ⟨r, ?_⟩
        have h2 : (Polynomial.aeval r) (2 : ℤ[X]) = (2 : ℚ) := map_ofNat _ 2
        simpa [pZ, h2] using hp_eval
  have hpQ_eq : (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ) * Polynomial.X - 1 : ℚ[X]) =
      pZ.map (algebraMap ℤ ℚ) := by
    simp [pZ, Polynomial.C_ofNat]
  have hpQ_irred :
      Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ) * Polynomial.X - 1 : ℚ[X]) := by
    rw [hpQ_eq]
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hpZ_monic.isPrimitive).mp hpZ_irred
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfacR : (Polynomial.X ^ 2 - Polynomial.C (2 : ℝ) * Polynomial.X - 1 : ℝ[X]) =
      (Polynomial.X - Polynomial.C (1 - Real.sqrt 2)) *
        (Polynomial.X - Polynomial.C (1 + Real.sqrt 2)) := by
    have hprod_C :
        Polynomial.C (1 - Real.sqrt 2) * Polynomial.C (1 + Real.sqrt 2) = (-1 : ℝ[X]) := by
      rw [← map_mul]
      have hmul : (1 - Real.sqrt 2) * (1 + Real.sqrt 2) = -1 := by linear_combination -hsq2
      rw [hmul, map_neg, map_one]
    have hsum_C :
        Polynomial.C (1 - Real.sqrt 2) + Polynomial.C (1 + Real.sqrt 2) =
          Polynomial.C (2 : ℝ) := by
      rw [← map_add]
      exact congrArg Polynomial.C (by ring)
    symm
    calc (Polynomial.X - Polynomial.C (1 - Real.sqrt 2)) *
          (Polynomial.X - Polynomial.C (1 + Real.sqrt 2))
      _ = Polynomial.X ^ 2 -
            (Polynomial.C (1 - Real.sqrt 2) + Polynomial.C (1 + Real.sqrt 2)) * Polynomial.X +
            Polynomial.C (1 - Real.sqrt 2) * Polynomial.C (1 + Real.sqrt 2) := by ring
      _ = Polynomial.X ^ 2 - Polynomial.C (2 : ℝ) * Polynomial.X - 1 := by
          rw [hsum_C, hprod_C]; ring
  let α₁ : qSqrtTwoSubfield := ⟨1 - Real.sqrt 2, 1, -1, by push_cast; ring⟩
  let α₂ : qSqrtTwoSubfield := ⟨1 + Real.sqrt 2, 1, 1, by push_cast; ring⟩
  have hfacK :
      (Polynomial.X ^ 2 - Polynomial.C (2 : qSqrtTwoSubfield) * Polynomial.X - 1 :
          qSqrtTwoSubfield[X]) =
        (Polynomial.X - Polynomial.C α₁) * (Polynomial.X - Polynomial.C α₂) := by
    apply Polynomial.map_injective qSqrtTwoSubfield.subtype Subtype.val_injective
    have h2 : qSqrtTwoSubfield.subtype (2 : qSqrtTwoSubfield) = (2 : ℝ) := map_ofNat _ 2
    simpa [Polynomial.map_sub, Polynomial.map_mul, h2, α₁, α₂] using hfacR
  exact ⟨hno_rat_root, hpQ_irred, hpZ_irred, hfacR, α₁, α₂, hfacK⟩

/-! ## §4.2 Field extensions (printed pp. 40–42, PDF pp. 48–50) -/

/-- Garling's triple definition of an *extension* `(i, K, L)` of a field `K` (§4.2, p. 40):
`L` is a field and `i : K →+* L` is a ring monomorphism of `K` into `L`. -/
structure FieldExtensionTriple (K L : Type*) [Field K] [Field L] where
  hom : K →+* L
  mono : IsRingMonomorphism hom

/-- Every ring homomorphism `i : K →+* L` between fields is automatically a ring monomorphism
(by §3.9 `field_ringHom_injective`), yielding a `FieldExtensionTriple` (§4.2, p. 40). -/
def FieldExtensionTriple.ofRingHom {K L : Type*} [Field K] [Field L] (i : K →+* L) :
    FieldExtensionTriple K L where
  hom := i
  mono := (field_ringHom_injective i).2

/-- Canonical `FieldExtensionTriple` associated to `[Algebra K L]` (§4.2, p. 40). -/
def FieldExtensionTriple.ofAlgebra (K L : Type*) [Field K] [Field L] [Algebra K L] :
    FieldExtensionTriple K L :=
  FieldExtensionTriple.ofRingHom (algebraMap K L)

/-- Subfield identification (§4.2, p. 40): if `(i, K, L)` is an extension of `K`, the image `i(K)`
is a subfield of `L` isomorphic to `K`. -/
noncomputable def FieldExtensionTriple.imageEquiv {K L : Type*} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : K ≃+* ext.hom.fieldRange :=
  let φ : K →+* ext.hom.fieldRange :=
    { toFun := fun k => ⟨ext.hom k, k, rfl⟩
      map_one' := Subtype.ext ext.hom.map_one
      map_mul' := fun x y => Subtype.ext (ext.hom.map_mul x y)
      map_zero' := Subtype.ext ext.hom.map_zero
      map_add' := fun x y => Subtype.ext (ext.hom.map_add x y) }
  RingEquiv.ofBijective φ
    ⟨fun _ _ h => ext.mono (congrArg Subtype.val h),
     by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

/-- Garling's literal axioms of a *vector space* `V` over a field `K` (§1.3, p. 9; cited in
Theorem 4.1 on p. 40): `(V, +)` is an abelian group and `(α, x) ↦ smul α x` satisfies
(a) `α(x + y) = αx + αy`, (b) `(α + β)x = αx + βx`, (c) `(αβ)x = α(βx)`, and (d) `1 · x = x`. -/
structure IsGarlingVectorSpace (K V : Type*) [Field K]
    (add : V → V → V) (smul : K → V → V) : Prop where
  nonempty : Nonempty V
  exists_zero : ∃ zero : V,
    (∀ x y z : V, add (add x y) z = add x (add y z)) ∧
    (∀ x y : V, add x y = add y x) ∧
    (∀ x : V, add zero x = x ∧ add x zero = x) ∧
    (∀ x : V, ∃ nx : V, add x nx = zero ∧ add nx x = zero)
  smul_add : ∀ (α : K) (x y : V), smul α (add x y) = add (smul α x) (smul α y)
  add_smul : ∀ (α β : K) (x : V), smul (α + β) x = add (smul α x) (smul β x)
  mul_smul : ∀ (α β : K) (x : V), smul (α * β) x = smul α (smul β x)
  one_smul : ∀ x : V, smul 1 x = x

/-- Explicit `Module K L` structure induced by a `FieldExtensionTriple` `(i, K, L)` via
`(k, l) ↦ i(k) * l` (§4.2, Theorem 4.1, p. 40). -/
abbrev FieldExtensionTriple.toModule {K L : Type*} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : Module K L :=
  letI : Algebra K L := ext.hom.toAlgebra
  inferInstance

/-- **Theorem 4.1** (§4.2, p. 40): Suppose that `L : K` is an extension. Under the operations
`(l₁, l₂) ↦ l₁ + l₂` from `L × L` to `L` and `(k, l) ↦ k * l` (`algebraMap K L k * l`) from
`K × L` to `L`, `L` is a vector space over `K`. -/
theorem theorem_4_1 (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingVectorSpace K L (· + ·) (fun k l => algebraMap K L k * l) :=
  { nonempty := ⟨0⟩
    exists_zero := ⟨0, add_assoc, add_comm, fun x => ⟨zero_add x, add_zero x⟩,
      fun x => ⟨-x, add_neg_cancel x, neg_add_cancel x⟩⟩
    smul_add := fun k x y => mul_add (algebraMap K L k) x y
    add_smul := fun α β x => by rw [map_add, right_distrib]
    mul_smul := fun α β x => by rw [map_mul, mul_assoc]
    one_smul := fun x => by rw [map_one, one_mul] }

/-- **Theorem 4.1** (triple `(i, K, L)` form, §4.2, p. 40): For any extension triple `(i, K, L)`,
`L` is a vector space over `K` under `(l₁, l₂) ↦ l₁ + l₂` and `(k, l) ↦ i(k) * l`. -/
theorem theorem_4_1_triple {K L : Type*} [Field K] [Field L] (ext : FieldExtensionTriple K L) :
    IsGarlingVectorSpace K L (· + ·) (fun k l => ext.hom k * l) := by
  let _ : Algebra K L := ext.hom.toAlgebra
  exact theorem_4_1 K L

/-- **Theorem 4.1** (subfield `K ⊆ L` form, §4.2, p. 40): For any subfield `K : Subfield L`,
`L` is a vector space over `K` under `(l₁, l₂) ↦ l₁ + l₂` and `(k, l) ↦ (k : L) * l`. -/
theorem theorem_4_1_subfield {L : Type*} [Field L] (K : Subfield L) :
    IsGarlingVectorSpace K L (· + ·) (fun k l => (k : L) * l) :=
  theorem_4_1 K L

/-- Equivalence between Garling's `IsFiniteDimensional K V` (§1.3, p. 10) and Mathlib's
`Module.Finite K V` (`FiniteDimensional K V`). -/
theorem isFiniteDimensional_iff_moduleFinite (K V : Type*) [Field K]
    [AddCommGroup V] [Module K V] :
    IsFiniteDimensional K V ↔ Module.Finite K V := by
  constructor
  · rintro ⟨A, hAfin, hAspan⟩
    exact ⟨⟨hAfin.toFinset, by simpa [Spans] using hAspan⟩⟩
  · rintro ⟨⟨s, hs⟩⟩
    exact ⟨(s : Set V), s.finite_toSet, hs⟩

/-- Bridge between Garling's `garlingDim K V hV` (§1.3, p. 12) and Mathlib's `Module.finrank K V`
on finite-dimensional vector spaces. -/
theorem garlingDim_eq_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : IsFiniteDimensional K V) :
    garlingDim K V hV = Module.finrank K V := by
  classical
  have _ : Module.Finite K V := (isFiniteDimensional_iff_moduleFinite K V).mp hV
  let b := Module.Free.chooseBasis K V
  have hb_inj : Function.Injective b := b.injective
  let B : Set V := Set.range b
  have hB_ind : IsLinearlyIndependent K B := by
    rw [isLinearlyIndependent_iff]
    exact b.linearIndependent.linearIndepOn_id
  have hB_basis : IsBasis K V B := ⟨hB_ind, b.span_eq⟩
  have hcard : setOrder B = (Fintype.card (Module.Free.ChooseBasisIndex K V) : ℕ∞) := by
    rw [setOrder, ENat.card_congr (Equiv.ofInjective b hb_inj).symm, ENat.card_eq_coe_fintype_card]
  have hspec := garlingDim_spec hV hB_basis
  rw [hcard] at hspec
  have heq : garlingDim K V hV = Fintype.card (Module.Free.ChooseBasisIndex K V) :=
    Nat.cast_injective (R := ℕ∞) hspec.symm
  rw [heq, Module.finrank_eq_card_chooseBasisIndex]

/-- Garling's *degree* `[L : K]` of a field extension `L : K` (§4.2, p. 41), taking values in
`ℕ∞` (`ℕ ∪ {∞}`): equal to `garlingDim K L h` when `L` is finite-dimensional over `K`, and `⊤`
(`∞`) otherwise, avoiding `Module.finrank`'s junk value `0` on infinite extensions. -/
noncomputable def extDegree (K L : Type*) [Field K] [Field L] [Algebra K L] : ℕ∞ :=
  open Classical in
  if h : IsFiniteDimensional K L then (garlingDim K L h : ℕ∞) else ⊤

/-- A field extension `L : K` is *finite* if `[L : K] < ∞` (§4.2, p. 41). -/
def IsFiniteExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  extDegree K L < ⊤

/-- A field extension `L : K` is *infinite* if `[L : K] = ∞` (§4.2, p. 41). -/
def IsInfiniteExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  extDegree K L = ⊤

theorem extDegree_eq_garlingDim {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : IsFiniteDimensional K L) :
    extDegree K L = (garlingDim K L h : ℕ∞) := by
  simp [extDegree, h]

theorem extDegree_eq_finrank (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] :
    extDegree K L = (Module.finrank K L : ℕ∞) := by
  have h : IsFiniteDimensional K L := (isFiniteDimensional_iff_moduleFinite K L).mpr inferInstance
  rw [extDegree_eq_garlingDim h, garlingDim_eq_finrank h]

theorem isFiniteExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsFiniteExtension K L ↔ IsFiniteDimensional K L := by
  classical
  unfold IsFiniteExtension extDegree
  split_ifs with h
  · simp [h, ENat.natCast_lt_top]
  · simp [h]

theorem isFiniteExtension_iff_moduleFinite (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsFiniteExtension K L ↔ Module.Finite K L :=
  (isFiniteExtension_iff K L).trans (isFiniteDimensional_iff_moduleFinite K L)

theorem isInfiniteExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsInfiniteExtension K L ↔ ¬ IsFiniteDimensional K L := by
  classical
  unfold IsInfiniteExtension extDegree
  split_ifs with h <;> simp [h]

/-- Unconditional basis characterization of `[L : K]` (§4.2, p. 41): for *every* basis `B` of `L`
over `K` (finite or infinite), `[L : K] = |B|` in `ℕ∞`. -/
theorem extDegree_eq_setOrder_basis {K L : Type*} [Field K] [Field L] [Algebra K L]
    {B : Set L} (hB : IsBasis K L B) :
    extDegree K L = setOrder B := by
  by_cases hfin : IsFiniteDimensional K L
  · rw [extDegree_eq_garlingDim hfin, (garlingDim_spec hfin hB).symm]
  · rw [(isInfiniteExtension_iff K L).mpr hfin]
    have hB_not_fin : ¬ B.Finite := fun hBf => hfin ⟨B, hBf, hB.2⟩
    have _ : Infinite B := not_finite_iff_infinite.mp hB_not_fin
    symm
    exact ENat.card_eq_top.mpr inferInstance

/-- Every field extension `L : K` has degree `[L : K] ≥ 1` (so `[L : K] ≠ 0` in `ℕ∞`). -/
theorem one_le_extDegree (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (1 : ℕ∞) ≤ extDegree K L := by
  by_cases hfin : IsFiniteDimensional K L
  · have _ : Module.Finite K L := (isFiniteDimensional_iff_moduleFinite K L).mp hfin
    rw [extDegree_eq_finrank K L]
    exact Nat.cast_le.mpr Module.finrank_pos
  · rw [(isInfiniteExtension_iff K L).mpr hfin]
    exact le_top

theorem extDegree_ne_zero (K L : Type*) [Field K] [Field L] [Algebra K L] :
    extDegree K L ≠ 0 := by
  have h := one_le_extDegree K L
  intro h0
  rw [h0] at h
  exact absurd h (by decide)

/-- `[K : K] = 1` for every field `K`. -/
@[simp]
theorem extDegree_self (K : Type*) [Field K] : extDegree K K = 1 := by
  rw [extDegree_eq_finrank K K, Module.finrank_self, Nat.cast_one]

/-- Degree examples (§4.2, p. 41): `[ℂ : ℝ] = 2`, `[ℝ : ℚ] = ∞`, and `[ℚ(√2) : ℚ] = 2`. -/
theorem examples_4_2_degrees :
    extDegree ℝ ℂ = 2 ∧
    extDegree ℚ ℝ = ⊤ ∧
    extDegree ℚ qSqrtTwoSubfield = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [extDegree_eq_finrank ℝ ℂ, Complex.finrank_real_complex]
    rfl
  · change IsInfiniteExtension ℚ ℝ
    rw [isInfiniteExtension_iff, isFiniteDimensional_iff_moduleFinite]
    intro hfin
    let b := Module.Free.chooseBasis ℚ ℝ
    have hcount : Countable ℝ := Countable.of_equiv _ b.equivFun.toEquiv.symm
    exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hcount)
  · let e₁ : qSqrtTwoSubfield := ⟨1, 1, 0, by simp⟩
    let e₂ : qSqrtTwoSubfield := ⟨Real.sqrt 2, 0, 1, by simp⟩
    let v : Fin 2 → qSqrtTwoSubfield := ![e₁, e₂]
    have hli : LinearIndependent ℚ v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hval : ((c 0 : ℝ) + (c 1 : ℝ) * Real.sqrt 2) = 0 := by
        have hsub := congrArg Subtype.val hc
        simpa [Fin.sum_univ_two, v, e₁, e₂, Algebra.smul_def] using hsub
      have hc1 : c 1 = 0 := by
        by_contra h1
        apply sqrt_two_irrational
        refine ⟨-c 0 / c 1, ?_⟩
        have hc1R : (c 1 : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr h1
        push_cast
        field_simp [hc1R]
        linarith
      have hc0 : c 0 = 0 := by
        rw [hc1, Rat.cast_zero, zero_mul, add_zero] at hval
        exact Rat.cast_eq_zero.mp hval
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
    have hspan : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
      rintro ⟨x, r, s, rfl⟩ _
      have hx : (⟨(r : ℝ) + (s : ℝ) * Real.sqrt 2, r, s, rfl⟩ : qSqrtTwoSubfield) =
          r • v 0 + s • v 1 := by
        ext
        simp [v, e₁, e₂, Algebra.smul_def]
      rw [hx]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ r (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ s (Submodule.subset_span ⟨1, rfl⟩))
    let b : Module.Basis (Fin 2) ℚ qSqrtTwoSubfield := Module.Basis.mk hli hspan
    have _ : Module.Finite ℚ qSqrtTwoSubfield := Module.Finite.of_basis b
    rw [extDegree_eq_finrank ℚ qSqrtTwoSubfield, Module.finrank_eq_card_basis b, Fintype.card_fin]
    rfl

/-- **Theorem 4.2** (§4.2, p. 41): Suppose that `M : L` and `L : K` are extensions. Then
`[M : K] = [M : L] [L : K]` in `ℕ∞` (both in the finite case and when either factor is `∞`). -/
theorem theorem_4_2 (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    extDegree K M = extDegree L M * extDegree K L := by
  by_cases hLM : Module.Finite L M
  · by_cases hKL : Module.Finite K L
    · have _ : Module.Finite K M := Module.Finite.trans L M
      rw [extDegree_eq_finrank K M, extDegree_eq_finrank L M, extDegree_eq_finrank K L,
        ← Nat.cast_mul, mul_comm, Module.finrank_mul_finrank K L M]
    · have hKM_inf : ¬ Module.Finite K M := fun hKM => hKL (Module.Finite.left K L M)
      have hKL_top : extDegree K L = ⊤ :=
        (isInfiniteExtension_iff K L).mpr
          (mt (isFiniteDimensional_iff_moduleFinite K L).mp hKL)
      have hKM_top : extDegree K M = ⊤ :=
        (isInfiniteExtension_iff K M).mpr
          (mt (isFiniteDimensional_iff_moduleFinite K M).mp hKM_inf)
      rw [hKM_top, hKL_top, ENat.mul_top (extDegree_ne_zero L M)]
  · have hKM_inf : ¬ Module.Finite K M := fun hKM => hLM (Module.Finite.right K L M)
    have hLM_top : extDegree L M = ⊤ :=
      (isInfiniteExtension_iff L M).mpr
        (mt (isFiniteDimensional_iff_moduleFinite L M).mp hLM)
    have hKM_top : extDegree K M = ⊤ :=
      (isInfiniteExtension_iff K M).mpr
        (mt (isFiniteDimensional_iff_moduleFinite K M).mp hKM_inf)
    rw [hKM_top, hLM_top, ENat.top_mul (extDegree_ne_zero K L)]

private lemma subfield_chain_le {Ω : Type*} [Field Ω] :
    ∀ (n : ℕ) (K : Fin (n + 1) → Subfield Ω),
      (∀ j : Fin n, K j.castSucc ≤ K j.succ) → K 0 ≤ K (Fin.last n)
  | 0, _, _ => le_rfl
  | n + 1, K, hchain =>
    (subfield_chain_le n (fun i => K i.castSucc) (fun i => hchain i.castSucc)).trans
      (hchain (Fin.last n))

/-- Prose *tower law* for an `n`-step tower of field extensions `K_n : K_{n-1} : ... : K_0` inside
an ambient field `Ω` (§4.2, p. 42): `[K_n : K_0] = ∏_{j=0}^{n-1} [K_{j+1} : K_j]`. -/
theorem tower_law {Ω : Type*} [Field Ω] :
    ∀ (n : ℕ) (K : Fin (n + 1) → Subfield Ω)
      (hchain : ∀ j : Fin n, K j.castSucc ≤ K j.succ),
      @extDegree (K 0) (K (Fin.last n)) _ _
        (Subfield.inclusion (subfield_chain_le n K hchain)).toAlgebra =
        ∏ j : Fin n,
          @extDegree (K j.castSucc) (K j.succ) _ _ (Subfield.inclusion (hchain j)).toAlgebra
  | 0, K, _ => by
    have hprod : (∏ j : Fin 0, @extDegree (K j.castSucc) (K j.succ) _ _
        (Subfield.inclusion (nomatch j)).toAlgebra) = 1 := rfl
    rw [hprod]
    change @extDegree (K 0) (K 0) _ _ (Subfield.inclusion le_rfl).toAlgebra = 1
    have hid : Subfield.inclusion (le_rfl : K 0 ≤ K 0) = RingHom.id (K 0) := by ext; rfl
    rw [hid]
    exact @extDegree_self (K 0) _
  | n + 1, K, hchain => by
    have h0m : K 0 ≤ K (Fin.castSucc (Fin.last n)) :=
      subfield_chain_le n (fun i => K i.castSucc) (fun i => hchain i.castSucc)
    have hmlast : K (Fin.castSucc (Fin.last n)) ≤ K (Fin.last (n + 1)) := hchain (Fin.last n)
    have h0last : K 0 ≤ K (Fin.last (n + 1)) := h0m.trans hmlast
    let _ : Algebra (K 0) (K (Fin.castSucc (Fin.last n))) :=
      (Subfield.inclusion h0m).toAlgebra
    let _ : Algebra (K (Fin.castSucc (Fin.last n))) (K (Fin.last (n + 1))) :=
      (Subfield.inclusion hmlast).toAlgebra
    let _ : Algebra (K 0) (K (Fin.last (n + 1))) :=
      (Subfield.inclusion h0last).toAlgebra
    have _ : IsScalarTower (K 0) (K (Fin.castSucc (Fin.last n))) (K (Fin.last (n + 1))) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hstep := theorem_4_2 (K 0) (K (Fin.castSucc (Fin.last n))) (K (Fin.last (n + 1)))
    have ih := tower_law n (fun i => K i.castSucc) (fun i => hchain i.castSucc)
    rw [Fin.prod_univ_castSucc, mul_comm]
    exact hstep.trans (congrArg (fun x => _ * x) ih)

/-- `[L : K] = 1` if and only if `algebraMap K L` is surjective (`⊥ = ⊤` as intermediate fields). -/
theorem extDegree_eq_one_iff_surjective (K L : Type*) [Field K] [Field L] [Algebra K L] :
    extDegree K L = 1 ↔ Function.Surjective (algebraMap K L) := by
  constructor
  · intro h1
    have hfin : IsFiniteDimensional K L :=
      (isFiniteExtension_iff K L).mp (by unfold IsFiniteExtension; rw [h1]; exact ENat.natCast_lt_top 1)
    let U : Submodule K L := LinearMap.range (Algebra.linearMap K L)
    have hU_dim : garlingDim K U (subspace_isFiniteDimensional hfin U) = 1 := by
      rw [garlingDim_eq_finrank]
      have e : K ≃ₗ[K] U := LinearEquiv.ofInjective (Algebra.linearMap K L)
        (RingHom.injective (algebraMap K L))
      rw [← e.finrank_eq, Module.finrank_self]
    have hL_dim : garlingDim K L hfin = 1 :=
      Nat.cast_injective (R := ℕ∞) (by rw [← extDegree_eq_garlingDim hfin, h1, Nat.cast_one])
    have hU_top : U = ⊤ := (theorem_1_4 hfin U).2.mp (hU_dim.trans hL_dim.symm)
    intro y
    have hy : y ∈ U := hU_top ▸ Submodule.mem_top
    exact hy
  · intro hsurj
    let e : K ≃+* L := RingEquiv.ofBijective (algebraMap K L)
      ⟨RingHom.injective (algebraMap K L), hsurj⟩
    let elin : K ≃ₗ[K] L :=
      { e with
        map_smul' := fun c x => by
          change algebraMap K L (c * x) = c • algebraMap K L x
          rw [map_mul, Algebra.smul_def] }
    have _ : Module.Finite K L := Module.Finite.equiv elin
    rw [extDegree_eq_finrank K L, ← elin.finrank_eq, Module.finrank_self, Nat.cast_one]

/-- **Exercise 4.1** (§4.2, p. 42): Suppose that `[L : K]` is a prime number `p`. Then the only
fields intermediate between `L` and `K` are `K` (`⊥`) and `L` (`⊤`), which are distinct. -/
theorem exercise_4_1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hdeg : extDegree K L = p) :
    (⊥ : IntermediateField K L) ≠ ⊤ ∧
    ∀ M : IntermediateField K L, M = ⊥ ∨ M = ⊤ := by
  refine ⟨?_, fun M => ?_⟩
  · intro hbot_top
    have hsurj : Function.Surjective (algebraMap K L) := by
      intro y
      have hy : y ∈ (⊥ : IntermediateField K L) := hbot_top ▸ IntermediateField.mem_top
      rwa [IntermediateField.mem_bot] at hy
    have h1 : extDegree K L = 1 := (extDegree_eq_one_iff_surjective K L).mpr hsurj
    rw [hdeg] at h1
    exact hp.ne_one (Nat.cast_injective (R := ℕ∞) h1)
  · have hmul : (p : ℕ∞) = extDegree M L * extDegree K M := by
      rw [← hdeg]
      exact theorem_4_2 K M L
    have hML_lt : extDegree M L < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop, ENat.top_mul (extDegree_ne_zero K M)] at hmul
      exact ENat.natCast_ne_top p hmul
    have hKM_lt : extDegree K M < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop, ENat.mul_top (extDegree_ne_zero M L)] at hmul
      exact ENat.natCast_ne_top p hmul
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hML_lt.ne
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hKM_lt.ne
    rw [← ha, ← hb, ← Nat.cast_mul] at hmul
    have hab : a * b = p := (Nat.cast_injective (R := ℕ∞) hmul).symm
    have hdvd : a ∣ p := ⟨b, hab.symm⟩
    rcases (Nat.dvd_prime hp).mp hdvd with rfl | rfl
    · right
      have hsurj : Function.Surjective (algebraMap M L) :=
        (extDegree_eq_one_iff_surjective M L).mp ha.symm
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      obtain ⟨m, rfl⟩ := hsurj x
      exact m.2
    · left
      have hb1 : b = 1 := by
        have hpos : 0 < a := hp.pos
        nlinarith
      subst hb1
      have hsurj : Function.Surjective (algebraMap K M) :=
        (extDegree_eq_one_iff_surjective K M).mp hb.symm
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := hsurj ⟨x, hx⟩
        rw [IntermediateField.mem_bot]
        exact ⟨k, congrArg Subtype.val hk⟩
      · intro hx
        exact (bot_le : (⊥ : IntermediateField K L) ≤ M) hx

/-- **Exercise 4.1** (subfield `K ≤ M ≤ L` form, §4.2, p. 42): If `K : Subfield L` has prime degree
`[L : K] = p`, then for every subfield `M : Subfield L` with `K ≤ M`, either `M = K` or `M = ⊤`. -/
theorem exercise_4_1_subfield {L : Type*} [Field L] (K : Subfield L)
    {p : ℕ} (hp : Nat.Prime p) (hdeg : extDegree K L = p)
    (M : Subfield L) (hKM : K ≤ M) :
    M = K ∨ M = ⊤ := by
  let M' : IntermediateField K L :=
    { M with
      algebraMap_mem' := fun k => hKM k.2 }
  rcases (exercise_4_1 hp hdeg).2 M' with hbot | htop
  · left
    ext x
    constructor
    · intro hx
      have hxbot : x ∈ (⊥ : IntermediateField K L) := by
        have hxM' : x ∈ M' := hx
        rwa [hbot] at hxM'
      rw [IntermediateField.mem_bot] at hxbot
      rcases hxbot with ⟨k, rfl⟩
      exact k.2
    · exact fun hx => hKM hx
  · right
    ext x
    simp only [Subfield.mem_top, iff_true]
    have hxtop : x ∈ (⊤ : IntermediateField K L) := IntermediateField.mem_top
    rw [← htop] at hxtop
    exact hxtop

/-! ## §4.3 Algebraic and transcendental elements (printed pp. 42–45, PDF pp. 50–53) -/

/-- Garling's intersection definition of the subfield `K(A)` of `L` generated by `K` and a subset
`A ⊆ L` (§4.3, p. 42): the intersection of all subfields of `L` containing `K` and `A`. -/
def garlingFieldGenSubfield (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) : Subfield L :=
  sInf {F : Subfield L | Set.range (algebraMap K L) ⊆ (F : Set L) ∧ A ⊆ (F : Set L)}

/-- `garlingFieldGenSubfield K A` agrees with `(IntermediateField.adjoin K A).toSubfield`
(§4.3, p. 42). -/
theorem garlingFieldGenSubfield_eq_adjoin (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (A : Set L) :
    garlingFieldGenSubfield K A = (IntermediateField.adjoin K A).toSubfield := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨?_, IntermediateField.subset_adjoin K A⟩
    rintro _ ⟨k, rfl⟩
    exact (IntermediateField.adjoin K A).algebraMap_mem k
  · have hrange : Set.range (algebraMap K L) ⊆ (garlingFieldGenSubfield K A : Set L) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, garlingFieldGenSubfield, Subfield.mem_sInf]
      intro F hF
      exact hF.1 ⟨k, rfl⟩
    have hA : A ⊆ (garlingFieldGenSubfield K A : Set L) := by
      intro a ha
      rw [SetLike.mem_coe, garlingFieldGenSubfield, Subfield.mem_sInf]
      intro F hF
      exact hF.2 ha
    let M : IntermediateField K L :=
      { garlingFieldGenSubfield K A with
        algebraMap_mem' := fun k => hrange ⟨k, rfl⟩ }
    have hle : IntermediateField.adjoin K A ≤ M := IntermediateField.adjoin_le_iff.mpr hA
    exact hle

/-- Garling's set `S = {α₁ ⋯ α_k : α_i ∈ A ∪ {1}}` of finite products of elements of `A ∪ {1}`
(§4.3, p. 42). -/
def garlingFiniteProducts {L : Type*} [Field L] (A : Set L) : Set L :=
  {x : L | ∃ l : List L, (∀ a ∈ l, a ∈ A ∪ ({1} : Set L)) ∧ l.prod = x}

/-- Garling's `K`-linear subspace `V = span_K(S)` generated by `garlingFiniteProducts A`
(§4.3, p. 42). -/
def garlingGenSubspace (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) : Submodule K L :=
  Submodule.span K (garlingFiniteProducts A)

/-- `garlingGenSubspace K A` has the same carrier as `Algebra.adjoin K A` (§4.3, p. 42). -/
theorem garlingGenSubspace_eq_algebraAdjoin (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (A : Set L) :
    (garlingGenSubspace K A : Set L) = (Algebra.adjoin K A : Set L) := by
  have hS_sub : garlingFiniteProducts A ⊆ (Algebra.adjoin K A : Set L) := by
    rintro _ ⟨l, hl, rfl⟩
    induction l with
    | nil => exact (Algebra.adjoin K A).one_mem
    | cons a tl ih =>
      rw [List.prod_cons]
      have ha : a ∈ Algebra.adjoin K A := by
        rcases hl a (by simp) with haA | ha1
        · exact Algebra.subset_adjoin haA
        · rw [Set.mem_singleton_iff.mp ha1]
          exact (Algebra.adjoin K A).one_mem
      exact (Algebra.adjoin K A).mul_mem ha (ih fun b hb => hl b (List.mem_cons_of_mem a hb))
  have hle1 : garlingGenSubspace K A ≤ (Algebra.adjoin K A).toSubmodule :=
    Submodule.span_le.mpr hS_sub
  have h1_mem : (1 : L) ∈ garlingGenSubspace K A :=
    Submodule.subset_span ⟨[], (fun _ h => nomatch h), rfl⟩
  have hmul_S : ∀ {x y : L}, x ∈ garlingFiniteProducts A → y ∈ garlingFiniteProducts A →
      x * y ∈ garlingFiniteProducts A := by
    rintro _ _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, rfl⟩
    refine ⟨l₁ ++ l₂, ?_, List.prod_append⟩
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact hl₁ a h1
    · exact hl₂ a h2
  have hmul_V : ∀ {u v : L}, u ∈ garlingGenSubspace K A → v ∈ garlingGenSubspace K A →
      u * v ∈ garlingGenSubspace K A := by
    intro u v hu hv
    induction hu using Submodule.span_induction with
    | mem x hx =>
      induction hv using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hmul_S hx hy)
      | zero => simp
      | add y₁ y₂ _ _ iy₁ iy₂ => rw [mul_add]; exact Submodule.add_mem _ iy₁ iy₂
      | smul c y _ iy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c iy
    | zero => simp
    | add x₁ x₂ _ _ ix₁ ix₂ => rw [add_mul]; exact Submodule.add_mem _ ix₁ ix₂
    | smul c x _ ix => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ix
  let B : Subalgebra K L :=
    { garlingGenSubspace K A with
      one_mem' := h1_mem
      mul_mem' := hmul_V
      algebraMap_mem' := fun k => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ k h1_mem }
  have hA_B : A ⊆ (B : Set L) := fun a ha =>
    Submodule.subset_span ⟨[a], fun b hb => by
      rw [List.mem_singleton.mp hb]; exact Or.inl ha, List.prod_singleton⟩
  have hle2 : Algebra.adjoin K A ≤ B := Algebra.adjoin_le hA_B
  exact Set.Subset.antisymm hle1 hle2

/-- Explicit element description of `K(A)` (§4.3, p. 42):
`K(A) = {r * s⁻¹ : r ∈ V, s ∈ V \ {0}}`, where `V = span_K(S)` and
`S = {α₁ ⋯ α_k : α_i ∈ A ∪ {1}}`. -/
theorem garlingFieldGen_eq_ratios (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) :
    (garlingFieldGenSubfield K A : Set L) =
      {x : L | ∃ r ∈ garlingGenSubspace K A,
        ∃ s ∈ (garlingGenSubspace K A : Set L) \ {0}, x = r * s⁻¹} := by
  rw [garlingFieldGenSubfield_eq_adjoin]
  ext x
  change x ∈ IntermediateField.adjoin K A ↔ _
  rw [IntermediateField.mem_adjoin_iff_div]
  constructor
  · rintro ⟨r, hr, s, hs, rfl⟩
    have hrV : r ∈ garlingGenSubspace K A := by
      change r ∈ (garlingGenSubspace K A : Set L)
      rwa [garlingGenSubspace_eq_algebraAdjoin]
    have hsV : s ∈ garlingGenSubspace K A := by
      change s ∈ (garlingGenSubspace K A : Set L)
      rwa [garlingGenSubspace_eq_algebraAdjoin]
    by_cases hs0 : s = 0
    · refine ⟨0, (garlingGenSubspace K A).zero_mem, 1,
        ⟨Submodule.subset_span ⟨[], (fun _ h => nomatch h), rfl⟩, one_ne_zero⟩, ?_⟩
      simp [hs0]
    · exact ⟨r, hrV, s, ⟨hsV, hs0⟩, div_eq_mul_inv r s⟩
  · rintro ⟨r, hrV, s, ⟨hsV, _⟩, rfl⟩
    have hr : r ∈ Algebra.adjoin K A := by
      change r ∈ (Algebra.adjoin K A : Set L)
      rwa [← garlingGenSubspace_eq_algebraAdjoin]
    have hs : s ∈ Algebra.adjoin K A := by
      change s ∈ (Algebra.adjoin K A : Set L)
      rwa [← garlingGenSubspace_eq_algebraAdjoin]
    exact ⟨r, hr, s, hs, (div_eq_mul_inv r s).symm⟩

/-- An extension `L : K` is *simple* if `L = K(α)` for some `α ∈ L` (§4.3, p. 43). -/
def IsSimpleExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ α : L, IntermediateField.adjoin K {α} = ⊤

theorem isSimpleExtension_iff_garling (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsSimpleExtension K L ↔ ∃ α : L, garlingFieldGenSubfield K {α} = ⊤ := by
  refine exists_congr fun α => ?_
  rw [garlingFieldGenSubfield_eq_adjoin]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    ext x
    change x ∈ (IntermediateField.adjoin K {α}).toSubfield ↔ _
    rw [h]
    simp

/-- Examples of simple extensions (§4.3, p. 43): `ℂ = ℝ(i)` (`IsSimpleExtension ℝ ℂ`) and
`ℚ(√2)` is the subfield of `ℝ` generated over `ℚ` by `√2`. -/
theorem examples_4_3_simple :
    IsSimpleExtension ℝ ℂ ∧
    IntermediateField.adjoin ℝ {Complex.I} = ⊤ ∧
    (IntermediateField.adjoin ℚ {Real.sqrt 2}).toSubfield = qSqrtTwoSubfield := by
  have hC : IntermediateField.adjoin ℝ {Complex.I} = ⊤ := by
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    have hz : z = algebraMap ℝ ℂ z.re + algebraMap ℝ ℂ z.im * Complex.I :=
      (Complex.re_add_im z).symm
    rw [hz]
    exact (IntermediateField.adjoin ℝ {Complex.I}).add_mem
      ((IntermediateField.adjoin ℝ {Complex.I}).algebraMap_mem z.re)
      ((IntermediateField.adjoin ℝ {Complex.I}).mul_mem
        ((IntermediateField.adjoin ℝ {Complex.I}).algebraMap_mem z.im)
        (IntermediateField.mem_adjoin_simple_self ℝ Complex.I))
  refine ⟨⟨Complex.I, hC⟩, hC, ?_⟩
  apply le_antisymm
  · rw [← garlingFieldGenSubfield_eq_adjoin]
    apply sInf_le
    refine ⟨?_, ?_⟩
    · rintro _ ⟨q, rfl⟩
      exact ⟨q, 0, by simp⟩
    · intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact ⟨0, 1, by simp⟩
  · rintro x ⟨r, s, rfl⟩
    change (algebraMap ℚ ℝ r) + (algebraMap ℚ ℝ s) * Real.sqrt 2 ∈
      IntermediateField.adjoin ℚ {Real.sqrt 2}
    exact (IntermediateField.adjoin ℚ {Real.sqrt 2}).add_mem
      ((IntermediateField.adjoin ℚ {Real.sqrt 2}).algebraMap_mem r)
      ((IntermediateField.adjoin ℚ {Real.sqrt 2}).mul_mem
        ((IntermediateField.adjoin ℚ {Real.sqrt 2}).algebraMap_mem s)
        (IntermediateField.mem_adjoin_simple_self ℚ (Real.sqrt 2)))

private lemma sigma_fin_apply {α : Type*} {m n : ℕ} {f : Fin m → α} {g : Fin n → α}
    (h : (⟨m, f⟩ : Σ k, Fin k → α) = ⟨n, g⟩) (k : ℕ) (hkm : k < m) (hkn : k < n) :
    f ⟨k, hkm⟩ = g ⟨k, hkn⟩ := by
  cases h
  rfl

/-- Countability of `R[X]` when `R` is countable (used in §4.3 p. 43 and `Exercise 4.7` p. 47). -/
theorem countable_polynomial (R : Type*) [Semiring R] [Countable R] : Countable R[X] := by
  let enc : R[X] → Σ n : ℕ, Fin n → R :=
    fun p => ⟨p.natDegree + 1, fun i => p.coeff i⟩
  have henc : Function.Injective enc := by
    intro p q hpq
    have hdeg1 : p.natDegree + 1 = q.natDegree + 1 := congrArg Sigma.fst hpq
    ext k
    by_cases hk : k < p.natDegree + 1
    · have hk' : k < q.natDegree + 1 := hdeg1 ▸ hk
      exact sigma_fin_apply hpq k hk hk'
    · have hkp : p.natDegree < k := by omega
      have hkq : q.natDegree < k := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkp,
        Polynomial.coeff_eq_zero_of_natDegree_lt hkq]
  exact henc.countable

/-- Prose proposition (§4.3, p. 43): If `L : K` is a simple extension and `K` is countable, then
`L` is countable. -/
theorem countable_of_isSimpleExtension {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Countable K] (hsimple : IsSimpleExtension K L) : Countable L := by
  obtain ⟨α, hα⟩ := hsimple
  have _ : Countable K[X] := countable_polynomial K
  let f : K[X] × K[X] → L := fun rs => Polynomial.aeval α rs.1 / Polynomial.aeval α rs.2
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K {α} := hα ▸ IntermediateField.mem_top
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hx
    exact ⟨(r, s), rfl⟩
  exact hsurj.countable

/-- Prose corollary (§4.3, p. 43): `ℝ : ℚ` is not a simple extension. -/
theorem real_over_rat_not_simple : ¬ IsSimpleExtension ℚ ℝ := by
  intro hsimple
  have hcount : Countable ℝ := countable_of_isSimpleExtension hsimple
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hcount)

/-- Garling's definition of an element `α ∈ L` being *algebraic* over `K` (§4.3, p. 43): there
exists a non-zero polynomial `f ∈ K[X]` such that `f(α) = 0`. -/
def IsGarlingAlgebraic (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : Prop :=
  ∃ f : K[X], f ≠ 0 ∧ Polynomial.aeval α f = 0

theorem isGarlingAlgebraic_iff (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) :
    IsGarlingAlgebraic K α ↔ IsAlgebraic K α :=
  Iff.rfl

theorem isGarlingAlgebraic_iff_isIntegral (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (α : L) :
    IsGarlingAlgebraic K α ↔ IsIntegral K α :=
  isAlgebraic_iff_isIntegral

/-- Garling's definition of an element `α ∈ L` being *transcendental* over `K` (§4.3, p. 43): no
non-zero polynomial `f ∈ K[X]` satisfies `f(α) = 0`. -/
def IsGarlingTranscendental (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : Prop :=
  ¬ IsGarlingAlgebraic K α

/-- Garling's *evaluation map* `E_α : K[X] →+* L`, `E_α(f) = f(α)` (§4.3, p. 43). -/
noncomputable def evalRingHom (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : K[X] →+* L :=
  (Polynomial.aeval α).toRingHom

/-- Injectivity characterizations of `E_α` (§4.3, p. 43): `α` is transcendental over `K` iff `E_α`
is one-one, and `α` is algebraic over `K` iff `E_α` is not one-one. -/
theorem evalRingHom_injective_iff (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) :
    (Function.Injective (evalRingHom K α) ↔ IsGarlingTranscendental K α) ∧
    (¬ Function.Injective (evalRingHom K α) ↔ IsGarlingAlgebraic K α) := by
  have h1 : Function.Injective (evalRingHom K α) ↔ IsGarlingTranscendental K α := by
    rw [injective_iff_map_eq_zero]
    unfold IsGarlingTranscendental IsGarlingAlgebraic evalRingHom
    push Not
    constructor
    · intro h f hf h0
      exact hf (h f h0)
    · intro h f h0
      by_contra hf
      exact h f hf h0
  exact ⟨h1, ⟨fun hn => by by_contra ha; exact hn (h1.mpr ha), fun ha hn => h1.mp hn ha⟩⟩

/-- Kernel `K_α = ker(E_α)` of the evaluation map `E_α` (§4.3, p. 43). -/
noncomputable def evalKer (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : Ideal K[X] :=
  RingHom.ker (evalRingHom K α)

private lemma eq_of_monic_of_dvd_of_natDegree_le {R : Type*} [CommRing R] [IsDomain R]
    {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q)
    (hdeg : q.natDegree ≤ p.natDegree) : p = q := by
  obtain ⟨r, hr⟩ := hdvd
  have hq0 : q ≠ 0 := hq.ne_zero
  have hp0 : p ≠ 0 := hp.ne_zero
  have hr0 : r ≠ 0 := fun h0 => hq0 (by rw [hr, h0, mul_zero])
  have hsum : q.natDegree = p.natDegree + r.natDegree := by
    rw [hr, Polynomial.natDegree_mul hp0 hr0]
  have hrdeg : r.natDegree = 0 := by omega
  have hrc : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hrdeg
  have hlc : r.coeff 0 = 1 := by
    have h1 : q.leadingCoeff = p.leadingCoeff * r.leadingCoeff := by
      rw [hr, Polynomial.leadingCoeff_mul]
    rw [hp.leadingCoeff, hq.leadingCoeff, one_mul, Polynomial.leadingCoeff, hrdeg] at h1
    exact h1.symm
  rw [hr, hrc, hlc, map_one, mul_one]

/-- Existence and uniqueness of the monic generator `m_α = minpoly K α` of `K_α = ker(E_α)` when
`α` is algebraic over `K` (§4.3, pp. 43–44). -/
theorem exists_unique_monic_generator_evalKer {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingAlgebraic K α) :
    (minpoly K α).Monic ∧
    evalKer K α = Ideal.span {minpoly K α} ∧
    ∃! m : K[X], m.Monic ∧ evalKer K α = Ideal.span {m} := by
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  have hmonic : (minpoly K α).Monic := minpoly.monic hint
  have hker : evalKer K α = Ideal.span {minpoly K α} := by
    ext f
    rw [evalKer, RingHom.mem_ker, Ideal.mem_span_singleton]
    exact (minpoly.dvd_iff (A := K) (x := α)).symm
  refine ⟨hmonic, hker, ⟨minpoly K α, ⟨hmonic, hker⟩, ?_⟩⟩
  rintro m ⟨hm_monic, hm_ker⟩
  have hspan : Ideal.span {m} = Ideal.span {minpoly K α} := hm_ker.symm.trans hker
  have hdvd1 : m ∣ minpoly K α := Ideal.mem_span_singleton.mp (hspan ▸ Ideal.mem_span_singleton_self _)
  have hdvd2 : minpoly K α ∣ m := Ideal.mem_span_singleton.mp (hspan.symm ▸ Ideal.mem_span_singleton_self _)
  exact eq_of_monic_of_dvd_of_natDegree_le hm_monic hmonic hdvd1
    (Polynomial.natDegree_le_of_dvd hdvd2 hm_monic.ne_zero)

/-- **Theorem 4.3** (§4.3, p. 44): Suppose that `L : K` is an extension and that `α ∈ L` is
algebraic over `K`. Then `m_α = minpoly K α` is irreducible in `K[X]`, the image `E_α(K[X])` of
`K[X]` is the subfield `K(α)` of `L`, and `E_α` factors as `i ∘ eTilde ∘ q` where
`q : K[X] →+* K[X] ⧸ (m_α)` is the quotient mapping, `eTilde : K[X] ⧸ (m_α) →+* K(α)` is a ring
isomorphism, and `i : K(α) →+* L` is the inclusion mapping. -/
theorem theorem_4_3 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingAlgebraic K α) :
    Irreducible (minpoly K α) ∧
    IsGarlingIrreducible (minpoly K α) ∧
    Set.range (evalRingHom K α) = (IntermediateField.adjoin K {α} : Set L) ∧
    Set.range (evalRingHom K α) = (garlingFieldGenSubfield K {α} : Set L) ∧
    ∃ eTilde : (K[X] ⧸ Ideal.span {minpoly K α}) →+* IntermediateField.adjoin K {α},
      IsRingIsomorphism eTilde ∧
      evalRingHom K α =
        (IntermediateField.adjoin K {α}).val.toRingHom.comp
          (eTilde.comp (Ideal.Quotient.mk (Ideal.span {minpoly K α}))) := by
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  have hirred : Irreducible (minpoly K α) := minpoly.irreducible hint
  have hgar_irred : IsGarlingIrreducible (minpoly K α) :=
    (isGarlingIrreducible_iff (minpoly K α)).mpr hirred
  have hrange : Set.range (evalRingHom K α) = (IntermediateField.adjoin K {α} : Set L) := by
    have hsub := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((isGarlingAlgebraic_iff K α).mp hα)
    have hset : (IntermediateField.adjoin K {α} : Set L) = (Algebra.adjoin K {α} : Set L) :=
      congrArg SetLike.coe hsub
    rw [hset, Algebra.adjoin_singleton_eq_range_aeval]
    rfl
  have hrange_gar : Set.range (evalRingHom K α) = (garlingFieldGenSubfield K {α} : Set L) := by
    rw [garlingFieldGenSubfield_eq_adjoin]
    exact hrange
  have hker : evalKer K α = Ideal.span {minpoly K α} :=
    (exists_unique_monic_generator_evalKer hα).2.1
  let liftL : (K[X] ⧸ Ideal.span {minpoly K α}) →+* L :=
    Ideal.Quotient.lift (Ideal.span {minpoly K α}) (evalRingHom K α)
      (fun f hf => by
        rw [← hker] at hf
        exact hf)
  have hlift_inj : Function.Injective liftL := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hf : f ∈ Ideal.span {minpoly K α} := hker ▸ RingHom.mem_ker.mpr hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hmem : ∀ x : K[X] ⧸ Ideal.span {minpoly K α},
      liftL x ∈ IntermediateField.adjoin K {α} := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change evalRingHom K α f ∈ (IntermediateField.adjoin K {α} : Set L)
    rw [← hrange]
    exact ⟨f, rfl⟩
  let eTilde : (K[X] ⧸ Ideal.span {minpoly K α}) →+* IntermediateField.adjoin K {α} :=
    { toFun := fun x => ⟨liftL x, hmem x⟩
      map_one' := Subtype.ext liftL.map_one
      map_mul' := fun x y => Subtype.ext (liftL.map_mul x y)
      map_zero' := Subtype.ext liftL.map_zero
      map_add' := fun x y => Subtype.ext (liftL.map_add x y) }
  have heTilde_bij : IsRingIsomorphism eTilde := by
    refine ⟨fun x y hxy => hlift_inj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    have hy_range : y ∈ Set.range (evalRingHom K α) := hrange.symm ▸ hy
    obtain ⟨f, rfl⟩ := hy_range
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  refine ⟨hirred, hgar_irred, hrange, hrange_gar, eTilde, heTilde_bij, ?_⟩
  apply RingHom.ext
  intro f
  rfl

/-- Explicit power basis `{1, α, ..., α^{n-1}}` (`n = deg m_α`) of `K(α)` over `K` from the proof
of **Theorem 4.4** (§4.3, p. 45). -/
theorem theorem_4_4_power_basis {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingAlgebraic K α) :
    IsBasis K (IntermediateField.adjoin K {α})
      (Set.range fun i : Fin (minpoly K α).natDegree =>
        (IntermediateField.AdjoinSimple.gen K α) ^ (i : ℕ)) := by
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  let pb := IntermediateField.adjoin.powerBasis hint
  have hfun : (fun i : Fin (minpoly K α).natDegree =>
      (IntermediateField.AdjoinSimple.gen K α) ^ (i : ℕ)) = ⇑pb.basis := by
    ext i
    rw [pb.basis_eq_pow i, IntermediateField.adjoin.powerBasis_gen]
  rw [hfun]
  exact ⟨(isLinearlyIndependent_iff _).mpr pb.basis.linearIndependent.linearIndepOn_id,
    pb.basis.span_eq⟩

/-- **Theorem 4.4** (§4.3, p. 45): Suppose that `L : K` is an extension and that `α ∈ L`. Then `α`
is algebraic over `K` if and only if `[K(α) : K] < ∞`. If this is so, then `[K(α) : K]` is the
degree of `m_α = minpoly K α`. -/
theorem theorem_4_4 {K L : Type*} [Field K] [Field L] [Algebra K L] (α : L) :
    (IsGarlingAlgebraic K α ↔ extDegree K (IntermediateField.adjoin K {α}) < ⊤) ∧
    ∀ hα : IsGarlingAlgebraic K α,
      extDegree K (IntermediateField.adjoin K {α}) =
        (garlingDegree (minpoly K α)
          (minpoly.ne_zero ((isGarlingAlgebraic_iff_isIntegral K α).mp hα)) : ℕ∞) ∧
      extDegree K (IntermediateField.adjoin K {α}) = ((minpoly K α).natDegree : ℕ∞) := by
  have hiff : IsGarlingAlgebraic K α ↔ extDegree K (IntermediateField.adjoin K {α}) < ⊤ := by
    constructor
    · intro hα
      have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
      have _ : Module.Finite K (IntermediateField.adjoin K {α}) :=
        IntermediateField.adjoin.finiteDimensional hint
      rw [extDegree_eq_finrank K (IntermediateField.adjoin K {α})]
      exact ENat.natCast_lt_top _
    · intro hlt
      have _ : Module.Finite K (IntermediateField.adjoin K {α}) :=
        (isFiniteExtension_iff_moduleFinite K (IntermediateField.adjoin K {α})).mp hlt
      have halg_gen : IsAlgebraic K (IntermediateField.AdjoinSimple.gen K α) :=
        Algebra.IsAlgebraic.isAlgebraic (IntermediateField.AdjoinSimple.gen K α)
      obtain ⟨f, hf0, hfeval⟩ := halg_gen
      refine ⟨f, hf0, ?_⟩
      have hval := congrArg (IntermediateField.adjoin K {α}).val hfeval
      simpa [Polynomial.aeval_algHom_apply] using hval
  refine ⟨hiff, fun hα => ?_⟩
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  have _ : Module.Finite K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hdeg : extDegree K (IntermediateField.adjoin K {α}) = ((minpoly K α).natDegree : ℕ∞) := by
    rw [extDegree_eq_finrank K (IntermediateField.adjoin K {α}),
      IntermediateField.adjoin.finrank hint]
  exact ⟨hdeg, hdeg⟩

/-- **Exercise 4.2** (lattice `K₁ ⊔ K₂ = ⊤` form, §4.3, p. 45): If `K₁` and `K₂` are intermediate
fields of `L : K` with `K₁ ⊔ K₂ = ⊤`, then `[L : K] ≤ [K₁ : K] [K₂ : K]` in `ℕ∞`. -/
theorem exercise_4_2_sup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (K₁ K₂ : IntermediateField K L) (hL : K₁ ⊔ K₂ = ⊤) :
    extDegree K L ≤ extDegree K K₁ * extDegree K K₂ := by
  by_cases h1 : Module.Finite K K₁
  · by_cases h2 : Module.Finite K K₂
    · have _ : FiniteDimensional K K₁ := h1
      have _ : FiniteDimensional K K₂ := h2
      have hsup_fin : FiniteDimensional K ↥(K₁ ⊔ K₂) :=
        IntermediateField.finiteDimensional_sup K₁ K₂
      let eTop : ↥(K₁ ⊔ K₂) ≃ₐ[K] L :=
        (IntermediateField.equivOfEq hL).trans IntermediateField.topEquiv
      have _ : Module.Finite K L := Module.Finite.equiv eTop.toLinearEquiv
      rw [extDegree_eq_finrank K L, extDegree_eq_finrank K K₁, extDegree_eq_finrank K K₂,
        ← Nat.cast_mul, Nat.cast_le, ← eTop.toLinearEquiv.finrank_eq]
      exact IntermediateField.finrank_sup_le K₁ K₂
    · have h2_top : extDegree K K₂ = ⊤ :=
        (isInfiniteExtension_iff K K₂).mpr
          (mt (isFiniteDimensional_iff_moduleFinite K K₂).mp h2)
      rw [h2_top, ENat.mul_top (extDegree_ne_zero K K₁)]
      exact le_top
  · have h1_top : extDegree K K₁ = ⊤ :=
      (isInfiniteExtension_iff K K₁).mpr
        (mt (isFiniteDimensional_iff_moduleFinite K K₁).mp h1)
    rw [h1_top, ENat.top_mul (extDegree_ne_zero K K₂)]
    exact le_top

/-- **Exercise 4.2** (§4.3, p. 45): Suppose that `L : K` and that `K₁` and `K₂` are two
intermediate fields such that `L = K(K₁, K₂)` (`IntermediateField.adjoin K (K₁ ∪ K₂) = ⊤`).
Then `[L : K] ≤ [K₁ : K] [K₂ : K]` in `ℕ∞`. -/
theorem exercise_4_2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (K₁ K₂ : IntermediateField K L)
    (hL : IntermediateField.adjoin K ((K₁ : Set L) ∪ (K₂ : Set L)) = ⊤) :
    extDegree K L ≤ extDegree K K₁ * extDegree K K₂ := by
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    apply top_unique
    rw [← hL, IntermediateField.adjoin_le_iff]
    rintro x (hx1 | hx2)
    · exact (le_sup_left : K₁ ≤ K₁ ⊔ K₂) hx1
    · exact (le_sup_right : K₂ ≤ K₁ ⊔ K₂) hx2
  exact exercise_4_2_sup K₁ K₂ hsup

/-- Multiplication-by-`α` `K`-linear mapping `T_α : K(α) →ₗ[K] K(α)`, `T_α(β) = αβ`
(`Exercise 4.3`, §4.3, p. 45). -/
noncomputable def mulByGenLinearMap (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) : Module.End K (IntermediateField.adjoin K {α}) :=
  Algebra.lmul K (IntermediateField.adjoin K {α}) (IntermediateField.AdjoinSimple.gen K α)

@[simp]
theorem mulByGenLinearMap_coe (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (α : L) (β : IntermediateField.adjoin K {α}) :
    ((mulByGenLinearMap K α β : IntermediateField.adjoin K {α}) : L) = α * (β : L) :=
  rfl

/-- **Exercise 4.3** (§4.3, p. 45): Suppose that `K(α) : K` is a finite simple extension, and let
`T_α : K(α) →ₗ[K] K(α)` be given by `T_α(β) = αβ`. Then `det(xI - T_α)` is the minimal polynomial
`minpoly K α` of `α` over `K` (proved as `T_α.charpoly = minpoly K α`, as the basis-free `K[X]`
base-change determinant `det(X • I - T_α ⊗_K K[X]) = minpoly K α`, and as the matrix determinant
`det(X • I - [T_α]_b) = minpoly K α` in any finite `K`-basis `b` of `K(α)`). -/
theorem exercise_4_3 {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hfin : IsFiniteExtension K (IntermediateField.adjoin K {α})) :
    (letI : Module.Finite K (IntermediateField.adjoin K {α}) :=
      (isFiniteExtension_iff_moduleFinite K (IntermediateField.adjoin K {α})).mp hfin
     (mulByGenLinearMap K α).charpoly = minpoly K α) ∧
    LinearMap.det
      ((Polynomial.X : K[X]) •
        (1 : Module.End K (IntermediateField.adjoin K {α})).baseChange K[X] -
        (mulByGenLinearMap K α).baseChange K[X]) = minpoly K α ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (b : Module.Basis ι K (IntermediateField.adjoin K {α})),
      Matrix.det (Matrix.scalar ι (Polynomial.X : K[X]) -
        (Polynomial.C : K →+* K[X]).mapMatrix (LinearMap.toMatrix b b (mulByGenLinearMap K α))) =
        minpoly K α := by
  let _ : Module.Finite K (IntermediateField.adjoin K {α}) :=
    (isFiniteExtension_iff_moduleFinite K (IntermediateField.adjoin K {α})).mp hfin
  have hα : IsGarlingAlgebraic K α := (theorem_4_4 α).1.mpr hfin
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  let T : Module.End K (IntermediateField.adjoin K {α}) := mulByGenLinearMap K α
  let gen := IntermediateField.AdjoinSimple.gen K α
  have hch_gen : Polynomial.aeval gen T.charpoly = 0 := by
    have hch : Polynomial.aeval (Algebra.lmul K (IntermediateField.adjoin K {α}) gen) T.charpoly =
        0 := LinearMap.aeval_self_charpoly T
    have halg := Polynomial.aeval_algHom_apply
      (Algebra.lmul K (IntermediateField.adjoin K {α})) gen T.charpoly
    rw [halg] at hch
    have hch1 : (Algebra.lmul K (IntermediateField.adjoin K {α})
        (Polynomial.aeval gen T.charpoly)) 1 = 0 := by rw [hch]; rfl
    change Polynomial.aeval gen T.charpoly * 1 = 0 at hch1
    simpa using hch1
  have hch_alpha : Polynomial.aeval α T.charpoly = 0 := by
    have hval := congrArg (IntermediateField.adjoin K {α}).val hch_gen
    simpa [Polynomial.aeval_algHom_apply, gen] using hval
  have hdvd : minpoly K α ∣ T.charpoly := minpoly.dvd K α hch_alpha
  have hdeg_eq : T.charpoly.natDegree = (minpoly K α).natDegree := by
    rw [LinearMap.charpoly_natDegree, IntermediateField.adjoin.finrank hint]
  have hchar : T.charpoly = minpoly K α :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) T.charpoly_monic hdvd
      (le_of_eq hdeg_eq)).symm
  refine ⟨hchar, ?_, fun b => ?_⟩
  · classical
    let b := Module.Free.chooseBasis K (IntermediateField.adjoin K {α})
    have hb_char : Matrix.det (Matrix.scalar _ (Polynomial.X : K[X]) -
        (Polynomial.C : K →+* K[X]).mapMatrix (LinearMap.toMatrix b b T)) = minpoly K α := by
      change (LinearMap.toMatrix b b T).charpoly = minpoly K α
      rw [LinearMap.charpoly_toMatrix T b, hchar]
    rw [← LinearMap.det_toMatrix (b.baseChange K[X]), ← hb_char]
    congr 1
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;>
      simp [hij, LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one,
        Polynomial.algebraMap_eq, Matrix.scalar_apply, T]
  · change (LinearMap.toMatrix b b T).charpoly = minpoly K α
    rw [LinearMap.charpoly_toMatrix T b, hchar]

private lemma monic_cubic_int_irreducible_of_no_root (p : ℤ[X]) (hm : p.Monic)
    (hdeg : p.natDegree = 3) (hroot : ∀ z : ℤ, p.eval z ≠ 0) : Irreducible p := by
  refine ⟨fun hu => by have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, ?_⟩
  intro a b hab
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · by_cases hb : IsUnit b
    · exact Or.inr hb
    · exfalso
      have ha0 : a ≠ 0 := fun h0 => hm.ne_zero (by rw [hab, h0, zero_mul])
      have hb0 : b ≠ 0 := fun h0 => hm.ne_zero (by rw [hab, h0, mul_zero])
      have hprod : a.leadingCoeff * b.leadingCoeff = 1 := by
        rw [← Polynomial.leadingCoeff_mul, ← hab, hm.leadingCoeff]
      have ha_lc : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one b.leadingCoeff hprod
      have hb_lc : IsUnit b.leadingCoeff := IsUnit.of_mul_eq_one_right a.leadingCoeff hprod
      have hadeg_pos : 0 < a.natDegree := by
        by_contra hle
        have h0 : a.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at ha
        have hca : a.coeff 0 = a.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
        exact ha (hca ▸ ha_lc.map Polynomial.C)
      have hbdeg_pos : 0 < b.natDegree := by
        by_contra hle
        have h0 : b.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hb
        have hcb : b.coeff 0 = b.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
        exact hb (hcb ▸ hb_lc.map Polynomial.C)
      have hsum : a.natDegree + b.natDegree = 3 := by
        rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hdeg]
      have hex_lin : ∃ g : ℤ[X], g ∣ p ∧ g.natDegree = 1 ∧ IsUnit g.leadingCoeff := by
        rcases (by omega : a.natDegree = 1 ∨ b.natDegree = 1) with ha1 | hb1
        · exact ⟨a, ⟨b, hab⟩, ha1, ha_lc⟩
        · exact ⟨b, ⟨a, hab.trans (mul_comm a b)⟩, hb1, hb_lc⟩
      obtain ⟨g, ⟨q, hpq⟩, hg1, hglc⟩ := hex_lin
      have hg_eq : g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hg1)
      have hc1_eq : g.coeff 1 = g.leadingCoeff := by rw [Polynomial.leadingCoeff, hg1]
      let z : ℤ := -g.coeff 0 * g.coeff 1
      have hgeval : g.eval z = 0 := by
        rw [hg_eq]
        rcases Int.isUnit_iff.mp (hc1_eq ▸ hglc) with hc1 | hc1
        · simp [z, hc1]
        · simp [z, hc1]
      apply hroot z
      rw [hpq, Polynomial.eval_mul, hgeval, zero_mul]

/-- **Exercise 4.4** (§4.3, p. 45): `x³ + 3x + 1` is irreducible in `ℚ[X]` (and has roots in `ℂ`).
For any root `α ∈ ℂ` of `x³ + 3x + 1`, `α ≠ 0`, `1 + α ≠ 0`, and `α⁻¹` and `(1 + α)⁻¹` have unique
expressions as rational linear combinations of `1`, `α`, and `α²`, namely
`α⁻¹ = -3 - α²` (`(-3, 0, -1)`) and `(1 + α)⁻¹ = 4/3 - (1/3)α + (1/3)α²` (`(4/3, -1/3, 1/3)`). -/
theorem exercise_4_4 :
    Irreducible (Polynomial.X ^ 3 + Polynomial.C (3 : ℚ) * Polynomial.X + 1 : ℚ[X]) ∧
    (∃ α : ℂ, α ^ 3 + 3 * α + 1 = 0) ∧
    ∀ α : ℂ, α ^ 3 + 3 * α + 1 = 0 →
      α ≠ 0 ∧ 1 + α ≠ 0 ∧
      (α⁻¹ = ((-3 : ℚ) : ℂ) + (0 : ℚ) * α + ((-1 : ℚ) : ℂ) * α ^ 2) ∧
      ((1 + α)⁻¹ = ((4 / 3 : ℚ) : ℂ) + ((-1 / 3 : ℚ) : ℂ) * α + ((1 / 3 : ℚ) : ℂ) * α ^ 2) ∧
      (∃! c : ℚ × ℚ × ℚ,
        α⁻¹ = (c.1 : ℂ) + (c.2.1 : ℂ) * α + (c.2.2 : ℂ) * α ^ 2) ∧
      (∃! c : ℚ × ℚ × ℚ,
        (1 + α)⁻¹ = (c.1 : ℂ) + (c.2.1 : ℂ) * α + (c.2.2 : ℂ) * α ^ 2) := by
  let pZ : ℤ[X] := Polynomial.X ^ 3 + Polynomial.C 3 * Polynomial.X + 1
  have hpZ_deg : pZ.natDegree = 3 := by dsimp [pZ]; compute_degree!
  have hpZ_monic : pZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hpZ_deg]
    dsimp [pZ]
    simp [Polynomial.coeff_one, Polynomial.coeff_X]
  have hpZ_irred : Irreducible pZ := by
    apply monic_cubic_int_irreducible_of_no_root pZ hpZ_monic hpZ_deg
    intro z hz
    have hev : z ^ 3 + 3 * z + 1 = 0 := by simpa [pZ] using hz
    rcases le_or_gt 0 z with hnonneg | hneg
    · nlinarith [sq_nonneg z]
    · have hz1 : z ≤ -1 := by omega
      have hcube : z ^ 3 ≤ -1 := by
        have hsq : 1 ≤ z ^ 2 := by nlinarith
        nlinarith
      nlinarith
  let pQ : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C (3 : ℚ) * Polynomial.X + 1
  have hpQ_eq : pQ = pZ.map (algebraMap ℤ ℚ) := by
    simp [pQ, pZ, Polynomial.C_ofNat]
  have hpQ_irred : Irreducible pQ := by
    rw [hpQ_eq]
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hpZ_monic.isPrimitive).mp hpZ_irred
  have hex_root : ∃ α : ℂ, α ^ 3 + 3 * α + 1 = 0 := by
    let pC : ℂ[X] := Polynomial.X ^ 3 + Polynomial.C (3 : ℂ) * Polynomial.X + 1
    have hpC_deg : pC.degree = 3 := by dsimp [pC]; compute_degree!
    obtain ⟨α, hα⟩ := Complex.exists_root (f := pC) (by rw [hpC_deg]; decide)
    exact ⟨α, by simpa [pC, Polynomial.IsRoot] using hα⟩
  refine ⟨hpQ_irred, hex_root, fun α hα => ?_⟩
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0] at hα
    norm_num at hα
  have h1α0 : 1 + α ≠ 0 := by
    intro h0
    have hneg1 : α = -1 := by linear_combination h0
    rw [hneg1] at hα
    norm_num at hα
  have hinv1 : α⁻¹ = ((-3 : ℚ) : ℂ) + (0 : ℚ) * α + ((-1 : ℚ) : ℂ) * α ^ 2 := by
    apply mul_left_cancel₀ hα0
    rw [mul_inv_cancel₀ hα0]
    push_cast
    linear_combination hα
  have hinv2 :
      (1 + α)⁻¹ = ((4 / 3 : ℚ) : ℂ) + ((-1 / 3 : ℚ) : ℂ) * α + ((1 / 3 : ℚ) : ℂ) * α ^ 2 := by
    apply mul_left_cancel₀ h1α0
    rw [mul_inv_cancel₀ h1α0]
    push_cast
    linear_combination -(1 / 3 : ℂ) * hα
  have hpQ_monic : pQ.Monic := hpQ_eq ▸ hpZ_monic.map (algebraMap ℤ ℚ)
  have hpQ_deg : pQ.natDegree = 3 := by
    rw [hpQ_eq, hpZ_monic.natDegree_map, hpZ_deg]
  have hpQ_aeval : Polynomial.aeval α pQ = 0 := by
    have h3 : (Polynomial.aeval α) (Polynomial.C (3 : ℚ)) = (3 : ℂ) := by simp
    simpa [pQ, h3] using hα
  have hmin : minpoly ℚ α = pQ :=
    (minpoly.eq_of_irreducible_of_monic hpQ_irred hpQ_aeval hpQ_monic).symm
  have huniq : ∀ {c d : ℚ × ℚ × ℚ},
      (c.1 : ℂ) + (c.2.1 : ℂ) * α + (c.2.2 : ℂ) * α ^ 2 =
        (d.1 : ℂ) + (d.2.1 : ℂ) * α + (d.2.2 : ℂ) * α ^ 2 → c = d := by
    intro c d hcd
    let r : ℚ[X] := Polynomial.C (c.1 - d.1) + Polynomial.C (c.2.1 - d.2.1) * Polynomial.X +
      Polynomial.C (c.2.2 - d.2.2) * Polynomial.X ^ 2
    have hreval : Polynomial.aeval α r = 0 := by
      simp only [r, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        eq_ratCast, Rat.cast_sub]
      linear_combination hcd
    have hdvd : pQ ∣ r := hmin ▸ minpoly.dvd ℚ α hreval
    have hr_le : r.natDegree ≤ 2 := by dsimp [r]; compute_degree!
    have hr0 : r = 0 := by
      by_contra hne
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      omega
    have hc0 : c.1 - d.1 = 0 := by
      have h := congrArg (fun f : ℚ[X] => f.coeff 0) hr0
      simpa [r] using h
    have hc1 : c.2.1 - d.2.1 = 0 := by
      have h := congrArg (fun f : ℚ[X] => f.coeff 1) hr0
      simp only [r, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h
      simpa using h
    have hc2 : c.2.2 - d.2.2 = 0 := by
      have h := congrArg (fun f : ℚ[X] => f.coeff 2) hr0
      simp only [r, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h
      simpa using h
    ext
    · linarith
    · linarith
    · linarith
  exact ⟨hα0, h1α0, hinv1, hinv2,
    ⟨(-3, 0, -1), hinv1, fun c hc => huniq (hc.symm.trans hinv1)⟩,
    ⟨(4 / 3, -1 / 3, 1 / 3), hinv2, fun c hc => huniq (hc.symm.trans hinv2)⟩⟩

/-- Bridge between `Nat.Coprime m n` and Garling's §3.6 `IsGarlingRelativelyPrime {(m : ℤ), (n : ℤ)}`
(`Exercise 4.5`, §4.3, p. 45). -/
theorem natCoprime_iff_isGarlingRelativelyPrime (m n : ℕ) :
    Nat.Coprime m n ↔ IsGarlingRelativelyPrime ({(m : ℤ), (n : ℤ)} : Set ℤ) := by
  constructor
  · intro hcop
    refine ⟨⟨(m : ℤ), by simp⟩, ⟨fun _ _ => one_dvd _, fun d hd => ?_⟩⟩
    have hdm : d ∣ (m : ℤ) := hd (m : ℤ) (by simp)
    have hdn : d ∣ (n : ℤ) := hd (n : ℤ) (by simp)
    have hnat : d.natAbs ∣ Nat.gcd m n :=
      Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hdm) (Int.natAbs_dvd_natAbs.mpr hdn)
    rw [hcop] at hnat
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hnat)
  · rintro ⟨_, ⟨_, hmax⟩⟩
    let g : ℕ := Nat.gcd m n
    have hg1 : (g : ℤ) ∣ (1 : ℤ) := by
      apply hmax (g : ℤ)
      intro b hb
      rcases hb with rfl | rfl
      · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left m n)
      · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right m n)
    exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hg1)

/-- **Exercise 4.5 — Non-degenerate counterexample to the literal printed statement** (§4.3, p. 45;
`QUEUE.md` fidelity hold): Taking `K = ℚ`, `L = ℚ(√2)` (`qSqrtTwoSubfield`), and
`α = 2^(1/6) ∈ ℝ` inside `ℝ`, the tower `L(α) : L : ℚ` satisfies `[L(α) : L] = 3` and `[L : ℚ] = 2`,
which are relatively prime (`Nat.Coprime 3 2` and `IsGarlingRelativelyPrime {(3 : ℤ), (2 : ℤ)}`),
yet `minpoly L α = X³ - C √2` has constant coefficient `-√2 ∉ ℚ`. -/
theorem exercise_4_5_printed_counterexample :
    let α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 6)
    let s2 : qSqrtTwoSubfield := ⟨Real.sqrt 2, 0, 1, by simp⟩
    extDegree qSqrtTwoSubfield (IntermediateField.adjoin qSqrtTwoSubfield {α}) = 3 ∧
    extDegree ℚ qSqrtTwoSubfield = 2 ∧
    Nat.Coprime 3 2 ∧
    IsGarlingRelativelyPrime ({(3 : ℤ), (2 : ℤ)} : Set ℤ) ∧
    minpoly qSqrtTwoSubfield α = Polynomial.X ^ 3 - Polynomial.C s2 ∧
    (minpoly qSqrtTwoSubfield α).coeff 0 ∉ Set.range (algebraMap ℚ qSqrtTwoSubfield) := by
  intro α s2
  have hα3 : α ^ 3 = Real.sqrt 2 := by
    dsimp [α]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.sqrt_eq_rpow]
  have hα6 : α ^ 6 = 2 := by
    calc α ^ 6 = (α ^ 3) ^ 2 := by ring
      _ = (Real.sqrt 2) ^ 2 := by rw [hα3]
      _ = 2 := Real.sq_sqrt (by norm_num)
  let P : qSqrtTwoSubfield[X] := Polynomial.X ^ 3 - Polynomial.C s2
  have hP_deg : P.natDegree = 3 := by dsimp [P]; compute_degree!
  have hP_monic : P.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hP_deg]
    dsimp [P]
    simp
  have hP_aeval : Polynomial.aeval α P = 0 := by
    have hs2 : algebraMap qSqrtTwoSubfield ℝ s2 = Real.sqrt 2 := rfl
    simp [P, hs2, hα3]
  have hintL : IsIntegral qSqrtTwoSubfield α := ⟨P, hP_monic, hP_aeval⟩
  have hdvdP : minpoly qSqrtTwoSubfield α ∣ P := minpoly.dvd qSqrtTwoSubfield α hP_aeval
  have hdeg_le : (minpoly qSqrtTwoSubfield α).natDegree ≤ 3 := by
    have hle := Polynomial.natDegree_le_of_dvd hdvdP hP_monic.ne_zero
    omega
  have _ : Module.Finite qSqrtTwoSubfield (IntermediateField.adjoin qSqrtTwoSubfield {α}) :=
    IntermediateField.adjoin.finiteDimensional hintL
  have hdegL_eq : extDegree ℚ qSqrtTwoSubfield = 2 := examples_4_2_degrees.2.2
  have hfin_QL : IsFiniteExtension ℚ qSqrtTwoSubfield := by
    unfold IsFiniteExtension
    rw [hdegL_eq]
    exact ENat.natCast_lt_top 2
  have _ : Module.Finite ℚ qSqrtTwoSubfield :=
    (isFiniteExtension_iff_moduleFinite ℚ qSqrtTwoSubfield).mp hfin_QL
  have hfinrank_QL : Module.finrank ℚ qSqrtTwoSubfield = 2 := by
    have h := extDegree_eq_finrank ℚ qSqrtTwoSubfield
    rw [hdegL_eq] at h
    exact Nat.cast_injective (R := ℕ∞) h.symm
  let E := IntermediateField.adjoin qSqrtTwoSubfield {α}
  have _ : Module.Finite ℚ E := Module.Finite.trans qSqrtTwoSubfield E
  let β : E := (IntermediateField.AdjoinSimple.gen qSqrtTwoSubfield α) ^ 2
  have hβ3 : β ^ 3 = 2 := by
    ext
    change ((α ^ 2) ^ 3 : ℝ) = 2
    calc (α ^ 2) ^ 3 = α ^ 6 := by ring
      _ = 2 := hα6
  let qZ : ℤ[X] := Polynomial.X ^ 3 - Polynomial.C 2
  have hqZ_deg : qZ.natDegree = 3 := by dsimp [qZ]; compute_degree!
  have hqZ_monic : qZ.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hqZ_deg]
    dsimp [qZ]
    simp
  have hqZ_irred : Irreducible qZ := by
    apply monic_cubic_int_irreducible_of_no_root qZ hqZ_monic hqZ_deg
    intro z hz
    have hev : z ^ 3 - 2 = 0 := by simpa [qZ] using hz
    by_cases hz2 : 2 ≤ z
    · have h8 : 8 ≤ z ^ 3 := by
        have hsq : 4 ≤ z ^ 2 := by nlinarith
        nlinarith
      omega
    · by_cases hz0 : 0 ≤ z
      · have hz01 : z = 0 ∨ z = 1 := by omega
        rcases hz01 with rfl | rfl <;> omega
      · have hz1 : z ≤ -1 := by omega
        have hneg : z ^ 3 ≤ -1 := by
          have hsq : 1 ≤ z ^ 2 := by nlinarith
          nlinarith
        omega
  let qQ : ℚ[X] := Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)
  have hqQ_eq : qQ = qZ.map (algebraMap ℤ ℚ) := by simp [qQ, qZ, Polynomial.C_ofNat]
  have hqQ_irred : Irreducible qQ :=
    hqQ_eq ▸ (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hqZ_monic.isPrimitive).mp hqZ_irred
  have hqQ_monic : qQ.Monic := hqQ_eq ▸ hqZ_monic.map (algebraMap ℤ ℚ)
  have hqQ_deg : qQ.natDegree = 3 := by rw [hqQ_eq, hqZ_monic.natDegree_map, hqZ_deg]
  have hqQ_aeval : Polynomial.aeval β qQ = 0 := by
    have h2 : (Polynomial.aeval β) (Polynomial.C (2 : ℚ)) = (2 : E) := by simp
    simpa [qQ, h2] using sub_eq_zero.mpr hβ3
  have hmin_β : minpoly ℚ β = qQ :=
    (minpoly.eq_of_irreducible_of_monic hqQ_irred hqQ_aeval hqQ_monic).symm
  have hfinrank_β : Module.finrank ℚ (IntermediateField.adjoin ℚ {β}) = 3 := by
    rw [IntermediateField.adjoin.finrank ⟨qQ, hqQ_monic, hqQ_aeval⟩, hmin_β, hqQ_deg]
  have hdvd_3 : 3 ∣ 2 * Module.finrank qSqrtTwoSubfield E := by
    have htower1 := Module.finrank_mul_finrank ℚ qSqrtTwoSubfield E
    have htower2 := Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {β}) E
    rw [hfinrank_QL] at htower1
    rw [hfinrank_β] at htower2
    exact ⟨Module.finrank (IntermediateField.adjoin ℚ {β}) E, htower1.trans htower2.symm⟩
  have hfinrank_LE_le : Module.finrank qSqrtTwoSubfield E ≤ 3 := by
    rw [IntermediateField.adjoin.finrank hintL]
    exact hdeg_le
  have hfinrank_LE_pos : 0 < Module.finrank qSqrtTwoSubfield E := Module.finrank_pos
  have hfinrank_LE : Module.finrank qSqrtTwoSubfield E = 3 := by omega
  have hmin_deg : (minpoly qSqrtTwoSubfield α).natDegree = 3 := by
    rw [← IntermediateField.adjoin.finrank hintL]
    exact hfinrank_LE
  have hmin_eq : minpoly qSqrtTwoSubfield α = P :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintL) hP_monic hdvdP
      (by rw [hP_deg, hmin_deg])
  have hcoeff_not_mem :
      (minpoly qSqrtTwoSubfield α).coeff 0 ∉ Set.range (algebraMap ℚ qSqrtTwoSubfield) := by
    rw [hmin_eq]
    rintro ⟨q, hq⟩
    have hc0 : P.coeff 0 = -s2 := by simp [P]
    rw [hc0] at hq
    have hval : (q : ℝ) = -Real.sqrt 2 := congrArg Subtype.val hq
    exact sqrt_two_irrational ⟨-q, by push_cast; linarith⟩
  have hcop : Nat.Coprime 3 2 := by decide
  refine ⟨?_, hdegL_eq, hcop, (natCoprime_iff_isGarlingRelativelyPrime 3 2).mp hcop,
    hmin_eq, hcoeff_not_mem⟩
  rw [extDegree_eq_finrank qSqrtTwoSubfield E, hfinrank_LE]
  rfl

/-- **Exercise 4.5 — Degenerate `α ∈ L \ K` counterexample** (§4.3, p. 45; `QUEUE.md` fidelity
hold): Taking `K = ℚ`, `L = ℚ(√2)`, and `α = √2 ∈ L`, we also have `[L(α) : L] = 1` and `[L : ℚ] = 2`
relatively prime, while `minpoly L α = X - C √2` has constant coefficient `-√2 ∉ ℚ`. -/
theorem exercise_4_5_degenerate_counterexample :
    let s2 : qSqrtTwoSubfield := ⟨Real.sqrt 2, 0, 1, by simp⟩
    extDegree qSqrtTwoSubfield (IntermediateField.adjoin qSqrtTwoSubfield {Real.sqrt 2}) = 1 ∧
    extDegree ℚ qSqrtTwoSubfield = 2 ∧
    Nat.Coprime 1 2 ∧
    IsGarlingRelativelyPrime ({(1 : ℤ), (2 : ℤ)} : Set ℤ) ∧
    minpoly qSqrtTwoSubfield (Real.sqrt 2) = Polynomial.X - Polynomial.C s2 ∧
    (minpoly qSqrtTwoSubfield (Real.sqrt 2)).coeff 0 ∉ Set.range (algebraMap ℚ qSqrtTwoSubfield) := by
  intro s2
  have hs2 : algebraMap qSqrtTwoSubfield ℝ s2 = Real.sqrt 2 := rfl
  have hmin : minpoly qSqrtTwoSubfield (Real.sqrt 2) = Polynomial.X - Polynomial.C s2 := by
    rw [← hs2, minpoly.algebraMap_eq (RingHom.injective _) s2, minpoly.eq_X_sub_C']
  have hint : IsIntegral qSqrtTwoSubfield (Real.sqrt 2) :=
    ⟨Polynomial.X - Polynomial.C s2, Polynomial.monic_X_sub_C s2, by simp [hs2]⟩
  have _ : Module.Finite qSqrtTwoSubfield
      (IntermediateField.adjoin qSqrtTwoSubfield {Real.sqrt 2}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hdeg1 :
      extDegree qSqrtTwoSubfield (IntermediateField.adjoin qSqrtTwoSubfield {Real.sqrt 2}) = 1 := by
    rw [extDegree_eq_finrank, IntermediateField.adjoin.finrank hint, hmin,
      Polynomial.natDegree_X_sub_C, Nat.cast_one]
  have hcop : Nat.Coprime 1 2 := by decide
  refine ⟨hdeg1, examples_4_2_degrees.2.2, hcop,
    (natCoprime_iff_isGarlingRelativelyPrime 1 2).mp hcop, hmin, ?_⟩
  rw [hmin]
  rintro ⟨q, hq⟩
  have hc0 : (Polynomial.X - Polynomial.C s2).coeff 0 = -s2 := by simp
  rw [hc0] at hq
  have hval : (q : ℝ) = -Real.sqrt 2 := congrArg Subtype.val hq
  exact sqrt_two_irrational ⟨-q, by push_cast; linarith⟩

/-- **Exercise 4.5 — Exact necessary and sufficient characterization** (§4.3, p. 45): For any
tower `M : L : K` and `α ∈ M` algebraic over `L`, the minimal polynomial `minpoly L α` has all its
coefficients in `K` if and only if `α` is algebraic over `K` and `[L(α) : L] = [K(α) : K]`
(equivalently `minpoly L α = (minpoly K α).map (algebraMap K L)`). -/
theorem exercise_4_5_coeffs_in_base_iff {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {α : M} (hαL : IsGarlingAlgebraic L α) :
    (∀ i : ℕ, (minpoly L α).coeff i ∈ Set.range (algebraMap K L)) ↔
      (IsGarlingAlgebraic K α ∧
        extDegree L (IntermediateField.adjoin L {α}) =
          extDegree K (IntermediateField.adjoin K {α}) ∧
        minpoly L α = (minpoly K α).map (algebraMap K L)) := by
  have hintL : IsIntegral L α := (isGarlingAlgebraic_iff_isIntegral L α).mp hαL
  constructor
  · intro hcoeffs
    choose c hc using hcoeffs
    let mL := minpoly L α
    let g : K[X] := ∑ i ∈ Finset.range (mL.natDegree + 1), Polynomial.C (c i) * Polynomial.X ^ i
    have hg_map : g.map (algebraMap K L) = mL := by
      conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow mL]
      simp only [g, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, hc]
      rfl
    have hg0 : g ≠ 0 := by
      intro h0
      have hm0 : mL = 0 := by rw [← hg_map, h0, Polynomial.map_zero]
      exact minpoly.ne_zero hintL hm0
    have hgae : Polynomial.aeval α g = 0 := by
      have hmap : Polynomial.aeval α (g.map (algebraMap K L)) = Polynomial.aeval α g :=
        Polynomial.aeval_map_algebraMap L α g
      rw [← hmap, hg_map]
      exact minpoly.aeval L α
    have hαK : IsGarlingAlgebraic K α := ⟨g, hg0, hgae⟩
    have hintK : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hαK
    have hdvd1 : minpoly K α ∣ g := minpoly.dvd K α hgae
    have hdvd2_map : mL ∣ (minpoly K α).map (algebraMap K L) :=
      minpoly.dvd L α (by rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K α)
    have hdeg_le1 : (minpoly K α).natDegree ≤ g.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd1 hg0
    have hg_deg : g.natDegree = mL.natDegree := by
      rw [← hg_map, Polynomial.natDegree_map (algebraMap K L)]
    have hdeg_le2 : mL.natDegree ≤ (minpoly K α).natDegree := by
      have hle := Polynomial.natDegree_le_of_dvd hdvd2_map
        ((minpoly.monic hintK).map (algebraMap K L)).ne_zero
      rwa [Polynomial.natDegree_map (algebraMap K L)] at hle
    have hdeg_eq : mL.natDegree = (minpoly K α).natDegree := by omega
    have hmL_eq : mL = (minpoly K α).map (algebraMap K L) :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintL)
        ((minpoly.monic hintK).map (algebraMap K L)) hdvd2_map
        (by rw [Polynomial.natDegree_map (algebraMap K L), hdeg_eq])
    have hdeg_ext :
        extDegree L (IntermediateField.adjoin L {α}) =
          extDegree K (IntermediateField.adjoin K {α}) := by
      rw [(theorem_4_4 (K := L) α).2 hαL |>.2, (theorem_4_4 (K := K) α).2 hαK |>.2, hdeg_eq]
    exact ⟨hαK, hdeg_ext, hmL_eq⟩
  · rintro ⟨_, _, hmL_eq⟩ i
    rw [hmL_eq, Polynomial.coeff_map]
    exact ⟨(minpoly K α).coeff i, rfl⟩

/-- **Exercise 4.5 — Repaired theorem** (§4.3, p. 45; `QUEUE.md` fidelity hold): Suppose `M : L : K`
is a tower of field extensions, `α ∈ M`, and `[K(α) : K] = m` and `[L : K] = n` are finite and
relatively prime (`Nat.Coprime m n`, or `IsGarlingRelativelyPrime {(m : ℤ), (n : ℤ)}`). Then
`[L(α) : L] = m`, `minpoly L α = (minpoly K α).map (algebraMap K L)`, and all coefficients of
`minpoly L α` lie in `K` (`Set.range (algebraMap K L)`). -/
theorem exercise_4_5 {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {α : M} {m n : ℕ}
    (hm : extDegree K (IntermediateField.adjoin K {α}) = m)
    (hn : extDegree K L = n)
    (hcop : Nat.Coprime m n) :
    extDegree L (IntermediateField.adjoin L {α}) = m ∧
    minpoly L α = (minpoly K α).map (algebraMap K L) ∧
    ∀ i : ℕ, (minpoly L α).coeff i ∈ Set.range (algebraMap K L) := by
  have hfin_Kα : extDegree K (IntermediateField.adjoin K {α}) < ⊤ := by
    rw [hm]; exact ENat.natCast_lt_top m
  have hαK : IsGarlingAlgebraic K α := (theorem_4_4 α).1.mpr hfin_Kα
  have hintK : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hαK
  have hm_deg : (minpoly K α).natDegree = m := by
    have h := (theorem_4_4 α).2 hαK |>.2
    rw [hm] at h
    exact Nat.cast_injective (R := ℕ∞) h.symm
  have hfin_KL : IsFiniteExtension K L := by
    unfold IsFiniteExtension; rw [hn]; exact ENat.natCast_lt_top n
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin_KL
  have hn_finrank : Module.finrank K L = n := by
    have h := extDegree_eq_finrank K L
    rw [hn] at h
    exact Nat.cast_injective (R := ℕ∞) h.symm
  let pL : L[X] := (minpoly K α).map (algebraMap K L)
  have hpL_monic : pL.Monic := (minpoly.monic hintK).map (algebraMap K L)
  have hpL_aeval : Polynomial.aeval α pL = 0 := by
    dsimp [pL]
    rw [Polynomial.aeval_map_algebraMap]
    exact minpoly.aeval K α
  have hintL : IsIntegral L α := ⟨pL, hpL_monic, hpL_aeval⟩
  have hdvd : minpoly L α ∣ pL := minpoly.dvd L α hpL_aeval
  have hpL_deg : pL.natDegree = m := by
    dsimp [pL]
    rw [Polynomial.natDegree_map (algebraMap K L), hm_deg]
  let d := (minpoly L α).natDegree
  have hd_le : d ≤ m := by
    have hle := Polynomial.natDegree_le_of_dvd hdvd hpL_monic.ne_zero
    rwa [hpL_deg] at hle
  have _ : Module.Finite L (IntermediateField.adjoin L {α}) :=
    IntermediateField.adjoin.finiteDimensional hintL
  have _ : Module.Finite K (IntermediateField.adjoin L {α}) :=
    Module.Finite.trans L (IntermediateField.adjoin L {α})
  have hfinrank_Lα : Module.finrank L (IntermediateField.adjoin L {α}) = d :=
    IntermediateField.adjoin.finrank hintL
  let E_K : IntermediateField K M := (IntermediateField.adjoin L {α}).restrictScalars K
  have hKα_le : IntermediateField.adjoin K {α} ≤ E_K :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self L α)
  let _ : Algebra (IntermediateField.adjoin K {α}) E_K :=
    (IntermediateField.inclusion hKα_le).toRingHom.toAlgebra
  have _ : IsScalarTower K (IntermediateField.adjoin K {α}) E_K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Module.Finite K E_K :=
    show Module.Finite K (IntermediateField.adjoin L {α}) from inferInstance
  have hfinrank_EK : Module.finrank K E_K = n * d := by
    change Module.finrank K (IntermediateField.adjoin L {α}) = n * d
    rw [← hn_finrank, ← hfinrank_Lα, Module.finrank_mul_finrank K L (IntermediateField.adjoin L {α})]
  have hm_dvd_nd : m ∣ n * d := by
    have hmul := Module.finrank_mul_finrank K (IntermediateField.adjoin K {α}) E_K
    rw [IntermediateField.adjoin.finrank hintK, hm_deg, hfinrank_EK] at hmul
    exact ⟨Module.finrank (IntermediateField.adjoin K {α}) E_K, hmul.symm⟩
  have hm_dvd_d : m ∣ d := hcop.dvd_of_dvd_mul_left hm_dvd_nd
  have hd_pos : 0 < d := minpoly.natDegree_pos hintL
  have hd_eq : d = m := Nat.le_antisymm hd_le (Nat.le_of_dvd hd_pos hm_dvd_d)
  have hmin_eq : minpoly L α = pL :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintL) hpL_monic hdvd
      (by rw [hpL_deg]; exact le_of_eq hd_eq.symm)
  refine ⟨?_, hmin_eq, fun i => ?_⟩
  · rw [extDegree_eq_finrank L (IntermediateField.adjoin L {α}), hfinrank_Lα, hd_eq]
  · rw [hmin_eq, Polynomial.coeff_map]
    exact ⟨(minpoly K α).coeff i, rfl⟩

/-- **Exercise 4.5 — Repaired theorem under `IsGarlingRelativelyPrime`** (§4.3, p. 45). -/
theorem exercise_4_5_garling_relPrime {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {α : M} {m n : ℕ}
    (hm : extDegree K (IntermediateField.adjoin K {α}) = m)
    (hn : extDegree K L = n)
    (hcop : IsGarlingRelativelyPrime ({(m : ℤ), (n : ℤ)} : Set ℤ)) :
    extDegree L (IntermediateField.adjoin L {α}) = m ∧
    minpoly L α = (minpoly K α).map (algebraMap K L) ∧
    ∀ i : ℕ, (minpoly L α).coeff i ∈ Set.range (algebraMap K L) :=
  exercise_4_5 hm hn ((natCoprime_iff_isGarlingRelativelyPrime m n).mpr hcop)

/-- **Exercise 4.6** (§4.3, p. 45): Suppose that `[L : K]` is a prime number. Then `L : K` is
simple. -/
theorem exercise_4_6 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : Nat.Prime p) (hdeg : extDegree K L = p) :
    IsSimpleExtension K L := by
  obtain ⟨hbot_ne_top, hsimple_ord⟩ := exercise_4_1 hp hdeg
  have hex : ∃ α : L, α ∉ (⊥ : IntermediateField K L) := by
    by_contra hno
    push Not at hno
    apply hbot_ne_top
    ext x
    simp [hno x]
  obtain ⟨α, hα⟩ := hex
  refine ⟨α, ?_⟩
  rcases hsimple_ord (IntermediateField.adjoin K {α}) with hbot | htop
  · exfalso
    apply hα
    rw [← hbot]
    exact IntermediateField.mem_adjoin_simple_self K α
  · exact htop

/-! ## §4.4 Algebraic extensions (printed pp. 46–48, PDF pp. 54–56) -/

/-- Garling's set `L_a` of elements of `L` which are algebraic over `K` (§4.4, Theorem 4.5, p. 46). -/
def algebraicElementsSet (K L : Type*) [Field K] [Field L] [Algebra K L] : Set L :=
  {α : L | IsGarlingAlgebraic K α}

/-- Degree-bound lemma used in Garling's proof of `Theorem 4.5` (§4.4, p. 46): if `α` and `β` are
algebraic over `K`, then `[K(α, β) : K] < ∞`. -/
theorem theorem_4_5_adjoin_pair_finite {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α β : L} (hα : IsGarlingAlgebraic K α) (hβ : IsGarlingAlgebraic K β) :
    extDegree K (IntermediateField.adjoin K ({α, β} : Set L)) < ⊤ := by
  have _ : Finite ({α, β} : Set L) := (Set.finite_singleton β).insert α
  have hint : ∀ x ∈ ({α, β} : Set L), IsIntegral K x := by
    rintro x (rfl | hβx)
    · exact (isGarlingAlgebraic_iff_isIntegral K x).mp hα
    · rw [Set.mem_singleton_iff.mp hβx]
      exact (isGarlingAlgebraic_iff_isIntegral K β).mp hβ
  have hfd : FiniteDimensional K (IntermediateField.adjoin K ({α, β} : Set L)) :=
    IntermediateField.finiteDimensional_adjoin hint
  exact (isFiniteExtension_iff_moduleFinite K _).mpr hfd

/-- Intermediate field `L_a` of elements of `L` algebraic over `K` (§4.4, Theorem 4.5, p. 46). -/
def algebraicIntermediateField (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IntermediateField K L where
  toSubalgebra := Subalgebra.algebraicClosure K L
  inv_mem' _ hx := hx.inv

/-- Subfield `L_a` of `L` consisting of all elements of `L` algebraic over `K` (§4.4, Theorem 4.5,
p. 46). -/
def algebraicSubfield (K L : Type*) [Field K] [Field L] [Algebra K L] : Subfield L :=
  (algebraicIntermediateField K L).toSubfield

@[simp]
theorem mem_algebraicIntermediateField_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} :
    α ∈ algebraicIntermediateField K L ↔ IsGarlingAlgebraic K α :=
  Iff.rfl

@[simp]
theorem mem_algebraicSubfield_iff {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L} :
    α ∈ algebraicSubfield K L ↔ IsGarlingAlgebraic K α :=
  Iff.rfl

/-- **Theorem 4.5** (§4.4, p. 46): Suppose that `L : K` is an extension. The set `L_a` of those
elements of `L` which are algebraic over `K` is a subfield of `L`. -/
theorem theorem_4_5 (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (algebraicSubfield K L : Set L) = algebraicElementsSet K L ∧
    (algebraicIntermediateField K L : Set L) = algebraicElementsSet K L ∧
    ∃ F : Subfield L, (F : Set L) = algebraicElementsSet K L :=
  ⟨rfl, rfl, algebraicSubfield K L, rfl⟩

/-- **Theorem 4.5 (triple form)** (§4.4, p. 46): For any field extension triple `(i, K, L)`, the
set of elements of `L` algebraic over `K` via `i` is a subfield of `L`. -/
theorem theorem_4_5_triple {K L : Type*} [Field K] [Field L] (e : FieldExtensionTriple K L) :
    letI : Algebra K L := e.hom.toAlgebra
    ∃ F : Subfield L, (F : Set L) = algebraicElementsSet K L := by
  let _ : Algebra K L := e.hom.toAlgebra
  exact ⟨algebraicSubfield K L, rfl⟩

/-- Garling's definition of an *algebraic* extension `L : K` (§4.4, p. 46): every element of `L` is
algebraic over `K`. -/
def IsAlgebraicExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ α : L, IsGarlingAlgebraic K α

theorem isAlgebraicExtension_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsAlgebraicExtension K L ↔ Algebra.IsAlgebraic K L :=
  ⟨fun h => ⟨h⟩, fun h α => h.isAlgebraic α⟩

/-- Garling's subfield `A` of *algebraic numbers* (§4.4, p. 46): the set of complex numbers which
are algebraic over `ℚ`. -/
noncomputable def GarlingAlgebraicNumbers : Subfield ℂ :=
  algebraicSubfield ℚ ℂ

theorem garlingAlgebraicNumbers_isAlgebraicExtension :
    IsAlgebraicExtension ℚ GarlingAlgebraicNumbers := by
  intro x
  have hx : IsAlgebraic ℚ (x : ℂ) := x.2
  have hinj : Function.Injective (algebraMap GarlingAlgebraicNumbers ℂ) := Subtype.val_injective
  exact (isAlgebraic_algebraMap_iff (R := ℚ) hinj).mp hx

/-- An extension `L : K` is *finitely generated over `K`* if `L = K(A)` for some finite subset
`A ⊆ L` (§4.4, Theorem 4.6(ii), p. 46). -/
def IsFinitelyGeneratedExtension (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ A : Set L, A.Finite ∧ IntermediateField.adjoin K A = ⊤

theorem isFinitelyGeneratedExtension_iff_garling (K L : Type*) [Field K] [Field L]
    [Algebra K L] :
    IsFinitelyGeneratedExtension K L ↔
      ∃ A : Set L, A.Finite ∧ garlingFieldGenSubfield K A = ⊤ := by
  refine exists_congr fun A => and_congr_right fun _ => ?_
  rw [garlingFieldGenSubfield_eq_adjoin]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    ext x
    change x ∈ (IntermediateField.adjoin K A).toSubfield ↔ _
    rw [h]
    simp

/-- **Theorem 4.6** (§4.4, p. 46): Suppose that `L : K` is an extension. The following are
equivalent:
(i) `[L : K] < ∞`;
(ii) `L : K` is algebraic, and `L` is finitely generated over `K`;
(iii) there exist finitely many algebraic elements `α₁, ..., α_n` of `L` such that
`L = K(α₁, ..., α_n)`. -/
theorem theorem_4_6 (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (extDegree K L < ⊤ ↔ IsAlgebraicExtension K L ∧ IsFinitelyGeneratedExtension K L) ∧
    (IsAlgebraicExtension K L ∧ IsFinitelyGeneratedExtension K L ↔
      ∃ (n : ℕ) (α : Fin n → L),
        (∀ i : Fin n, IsGarlingAlgebraic K (α i)) ∧
        IntermediateField.adjoin K (Set.range α) = ⊤) ∧
    (extDegree K L < ⊤ ↔
      ∃ (n : ℕ) (α : Fin n → L),
        (∀ i : Fin n, IsGarlingAlgebraic K (α i)) ∧
        IntermediateField.adjoin K (Set.range α) = ⊤) := by
  have h12 : extDegree K L < ⊤ → IsAlgebraicExtension K L ∧ IsFinitelyGeneratedExtension K L := by
    intro hfin
    have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
    have halg : IsAlgebraicExtension K L := by
      intro α
      have hfd_sub : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set L)) :=
        inferInstance
      have hdeg_lt : extDegree K (IntermediateField.adjoin K ({α} : Set L)) < ⊤ :=
        (isFiniteExtension_iff_moduleFinite K _).mpr hfd_sub
      exact (theorem_4_4 α).1.mpr hdeg_lt
    have hfg : IsFinitelyGeneratedExtension K L := by
      let b := Module.finBasis K L
      refine ⟨Set.range b, Set.finite_range b, ?_⟩
      rw [eq_top_iff]
      intro x _
      have hx_span : x ∈ Submodule.span K (Set.range b) := b.mem_span x
      have hspan_le :
          Submodule.span K (Set.range b) ≤
            (IntermediateField.adjoin K (Set.range b)).toSubmodule :=
        Submodule.span_le.mpr (IntermediateField.subset_adjoin K (Set.range b))
      exact hspan_le hx_span
    exact ⟨halg, hfg⟩
  have h23 :
      IsAlgebraicExtension K L ∧ IsFinitelyGeneratedExtension K L →
        ∃ (n : ℕ) (α : Fin n → L),
          (∀ i : Fin n, IsGarlingAlgebraic K (α i)) ∧
          IntermediateField.adjoin K (Set.range α) = ⊤ := by
    rintro ⟨halg, ⟨A, hAfin, hAtop⟩⟩
    classical
    let _ : Fintype A := hAfin.fintype
    let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
    let α : Fin (Fintype.card A) → L := fun i => (e i : L)
    have hrange : Set.range α = A := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp [α]⟩
    exact ⟨Fintype.card A, α, fun i => halg (α i), by rwa [hrange]⟩
  have h31 :
      (∃ (n : ℕ) (α : Fin n → L),
        (∀ i : Fin n, IsGarlingAlgebraic K (α i)) ∧
        IntermediateField.adjoin K (Set.range α) = ⊤) →
      extDegree K L < ⊤ := by
    rintro ⟨n, α, halg, htop⟩
    have hS_int : ∀ x ∈ Set.range α, IsIntegral K x := by
      rintro _ ⟨i, rfl⟩
      exact (isGarlingAlgebraic_iff_isIntegral K (α i)).mp (halg i)
    have hfd_adj : FiniteDimensional K (IntermediateField.adjoin K (Set.range α)) :=
      IntermediateField.finiteDimensional_adjoin hS_int
    let eL : IntermediateField.adjoin K (Set.range α) ≃ₐ[K] L :=
      (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
    have hfd_L : Module.Finite K L := Module.Finite.equiv eL.toLinearEquiv
    exact (isFiniteExtension_iff_moduleFinite K L).mpr hfd_L
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h => h12 (h31 h)⟩, ⟨fun h => h23 (h12 h), h31⟩⟩

/-- **Theorem 4.6 (non-empty tuple variant)** (§4.4, p. 46): Condition (iii) of `Theorem 4.6` is
equivalently witnessed by a non-empty tuple `α : Fin (n + 1) → L` (`n ≥ 0`, i.e. at least one
generator `α₁, ..., α_{n+1}`, taking `1 ∈ L` when `L = K`). -/
theorem theorem_4_6_nonempty_tuple (K L : Type*) [Field K] [Field L] [Algebra K L] :
    extDegree K L < ⊤ ↔
      ∃ (n : ℕ) (α : Fin (n + 1) → L),
        (∀ i : Fin (n + 1), IsGarlingAlgebraic K (α i)) ∧
        IntermediateField.adjoin K (Set.range α) = ⊤ := by
  rw [(theorem_4_6 K L).2.2]
  constructor
  · rintro ⟨n, α, halg, htop⟩
    refine ⟨n, Fin.cons 1 α, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => halg j) i
      exact isAlgebraic_one
    · rw [eq_top_iff, ← htop, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin K _ ⟨i.succ, by simp⟩
  · rintro ⟨n, α, halg, htop⟩
    exact ⟨n + 1, α, halg, htop⟩

/-- **Corollary 1** [to Theorem 4.6] (§4.4, p. 47): If `L : K` is an extension and if `α` is an
element of `L` which is algebraic over `K`, then `K(α) : K` is algebraic. -/
theorem corollary_1_to_theorem_4_6 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingAlgebraic K α) :
    IsAlgebraicExtension K (IntermediateField.adjoin K ({α} : Set L)) := by
  have hfin : extDegree K (IntermediateField.adjoin K ({α} : Set L)) < ⊤ :=
    (theorem_4_4 α).1.mp hα
  exact ((theorem_4_6 K (IntermediateField.adjoin K ({α} : Set L))).1.mp hfin).1

/-- **Corollary 2** [to Theorem 4.6] (§4.4, p. 47): Suppose that `L : K` is an extension and that
`S ⊆ L`. If each `α ∈ S` is algebraic over `K`, then `K(S) : K` is algebraic. -/
theorem corollary_2_to_theorem_4_6 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {S : Set L} (hS : ∀ α ∈ S, IsGarlingAlgebraic K α) :
    IsAlgebraicExtension K (IntermediateField.adjoin K S) := by
  rw [isAlgebraicExtension_iff]
  exact IntermediateField.isAlgebraic_adjoin fun α hα =>
    (isGarlingAlgebraic_iff_isIntegral K α).mp (hS α hα)

/-- **Theorem 4.7** (§4.4, p. 47): Suppose that `M : L` and `L : K` are algebraic extensions.
Then `M : K` is algebraic. -/
theorem theorem_4_7 {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (hML : IsAlgebraicExtension L M) (hLK : IsAlgebraicExtension K L) :
    IsAlgebraicExtension K M := by
  have _ : Algebra.IsAlgebraic K L := (isAlgebraicExtension_iff K L).mp hLK
  have _ : Algebra.IsAlgebraic L M := (isAlgebraicExtension_iff L M).mp hML
  exact (isAlgebraicExtension_iff K M).mpr (Algebra.IsAlgebraic.trans K L M)

/-- **Theorem 4.7 (triple form)** (§4.4, p. 47): Transitivity of algebraic extensions along field
extension triples `e₁ : FieldExtensionTriple K L` and `e₂ : FieldExtensionTriple L M`. -/
theorem theorem_4_7_triple {K L M : Type*} [Field K] [Field L] [Field M]
    (e₁ : FieldExtensionTriple K L) (e₂ : FieldExtensionTriple L M) :
    letI : Algebra K L := e₁.hom.toAlgebra
    letI : Algebra L M := e₂.hom.toAlgebra
    letI : Algebra K M := (e₂.hom.comp e₁.hom).toAlgebra
    IsAlgebraicExtension L M → IsAlgebraicExtension K L → IsAlgebraicExtension K M := by
  let _ : Algebra K L := e₁.hom.toAlgebra
  let _ : Algebra L M := e₂.hom.toAlgebra
  let _ : Algebra K M := (e₂.hom.comp e₁.hom).toAlgebra
  have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact theorem_4_7

/-! ### Exercises 4.7–4.10 (§4.4, printed pp. 47–48, PDF pp. 55–56) -/

/-- **Exercise 4.7 (first part, universe-polymorphic)** (§4.4, p. 47): If `L : K` is algebraic and
`K` is countable, then `L` is countable. -/
theorem exercise_4_7_countable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Countable K] (halg : IsAlgebraicExtension K L) : Countable L := by
  classical
  have _ : Countable K[X] := countable_polynomial K
  let P := {f : K[X] // f ≠ 0}
  let R : P → Finset L := fun p => (p.1.map (algebraMap K L)).roots.toFinset
  let g : (Σ p : P, {y : L // y ∈ R p}) → L := fun z => z.2.1
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨f, hf0, hfx⟩ := halg x
    have hfL0 : f.map (algebraMap K L) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
    have hx_root : x ∈ R ⟨f, hf0⟩ := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL0, Polynomial.IsRoot,
        Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hfx
    exact ⟨⟨⟨f, hf0⟩, ⟨x, hx_root⟩⟩, rfl⟩
  exact hsurj.countable

/-- Countability of the set of real numbers algebraic over `ℚ` (used in `Exercise 4.7` and
`Exercise 4.9`). -/
theorem countable_algebraic_reals : (algebraicElementsSet ℚ ℝ).Countable := by
  have halg : IsAlgebraicExtension ℚ (algebraicSubfield ℚ ℝ) := by
    intro x
    have hx : IsAlgebraic ℚ (x : ℝ) := x.2
    have hinj : Function.Injective (algebraMap (algebraicSubfield ℚ ℝ) ℝ) := Subtype.val_injective
    exact (isAlgebraic_algebraMap_iff (R := ℚ) hinj).mp hx
  have hcount : Countable (algebraicSubfield ℚ ℝ) := exercise_4_7_countable halg
  have hset : ((algebraicSubfield ℚ ℝ : Set ℝ)).Countable := Set.countable_coe_iff.mpr hcount
  exact hset

/-- **Exercise 4.7 (second part)** (§4.4, p. 47): There exist real numbers which are
transcendental over the rationals (indeed, the set of real numbers transcendental over `ℚ` is
uncountable). -/
theorem exercise_4_7_exists_transcendental_real :
    (∃ x : ℝ, IsGarlingTranscendental ℚ x) ∧
    ¬ ({x : ℝ | IsGarlingTranscendental ℚ x}).Countable := by
  have hnot_count : ¬ ({x : ℝ | IsGarlingTranscendental ℚ x}).Countable := by
    intro htrans_count
    have huniv : (Set.univ : Set ℝ) =
        algebraicElementsSet ℚ ℝ ∪ {x : ℝ | IsGarlingTranscendental ℚ x} := by
      ext x
      simp only [Set.mem_univ, Set.mem_union, true_iff]
      exact em (IsGarlingAlgebraic ℚ x)
    have huniv_count : (Set.univ : Set ℝ).Countable := by
      rw [huniv]
      exact countable_algebraic_reals.union htrans_count
    exact Cardinal.not_countable_real huniv_count
  have hne : ({x : ℝ | IsGarlingTranscendental ℚ x}).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hnot_count
    rw [hempty]
    exact Set.countable_empty
  exact ⟨hne, hnot_count⟩

/-- **Exercise 4.7** (§4.4, p. 47): If `L : K` is algebraic and `K` is countable then `L` is
countable; and there exist real numbers which are transcendental over the rationals. -/
theorem exercise_4_7 :
    (∀ (K L : Type) [Field K] [Field L] [Algebra K L] [Countable K],
      IsAlgebraicExtension K L → Countable L) ∧
    (∃ x : ℝ, IsGarlingTranscendental ℚ x) ∧
    ¬ ({x : ℝ | IsGarlingTranscendental ℚ x}).Countable :=
  ⟨fun _ _ _ _ _ _ halg => exercise_4_7_countable halg, exercise_4_7_exists_transcendental_real⟩

/-- **Exercise 4.8** (§4.4, p. 47): Suppose that `L : K` is an extension, that `α` is an element of
`L` which is transcendental over `K`, and that `f` is a non-constant element of `K[X]`
(`0 < f.natDegree`). Then `f(α)` is transcendental over `K`; and if `β ∈ L` satisfies `f(β) = α`,
then `β` is transcendental over `K`. -/
theorem exercise_4_8 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α : L} (hα : IsGarlingTranscendental K α)
    {f : K[X]} (hf : 0 < f.natDegree) :
    IsGarlingTranscendental K (Polynomial.aeval α f) ∧
    ∀ β : L, Polynomial.aeval β f = α → IsGarlingTranscendental K β := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg0, hgf⟩
    have hg_pos : 0 < g.natDegree := by
      by_contra hg_le
      have hg_deg0 : g.natDegree = 0 := by omega
      have hg_eq_C : g = Polynomial.C (g.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hg_deg0
      have hc0 : g.coeff 0 ≠ 0 := by
        intro hc
        apply hg0
        rw [hg_eq_C, hc, map_zero]
      rw [hg_eq_C, Polynomial.aeval_C] at hgf
      exact hc0 ((injective_iff_map_eq_zero _).mp (algebraMap K L).injective _ hgf)
    have hcomp_deg : 0 < (g.comp f).natDegree := by
      rw [Polynomial.natDegree_comp]
      exact Nat.mul_pos hg_pos hf
    have hcomp_ne0 : g.comp f ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hcomp_deg
      omega
    have hcomp_eval : Polynomial.aeval α (g.comp f) = 0 := by
      rw [Polynomial.aeval_comp, hgf]
    exact hα ⟨g.comp f, hcomp_ne0, hcomp_eval⟩
  · intro β hβ_eq hβ_alg
    apply hα
    rw [← hβ_eq]
    let βS : Subalgebra.algebraicClosure K L := ⟨β, hβ_alg⟩
    have hcoe : (Polynomial.aeval βS f : L) = Polynomial.aeval β f :=
      (Subalgebra.aeval_coe (Subalgebra.algebraicClosure K L) βS f).symm
    rw [← hcoe]
    exact (Polynomial.aeval βS f).2

/-- Equivalence of algebraicity/transcendence over `ℚ` between `x : ℝ` and `(x : ℂ)` (used in
`Exercise 4.9`). -/
theorem isGarlingAlgebraic_rat_ofReal_iff (x : ℝ) :
    IsGarlingAlgebraic ℚ (x : ℂ) ↔ IsGarlingAlgebraic ℚ x :=
  isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ) Complex.ofReal_injective

theorem isGarlingTranscendental_rat_ofReal_iff (x : ℝ) :
    IsGarlingTranscendental ℚ (x : ℂ) ↔ IsGarlingTranscendental ℚ x :=
  not_congr (isGarlingAlgebraic_rat_ofReal_iff x)

private lemma not_countable_Ioi (c : ℝ) : ¬ (Set.Ioi c).Countable := by
  intro hcount
  have _ : Countable (Set.Ioi c) := Set.countable_coe_iff.mpr hcount
  let φ : ℝ → Set.Ioi c := fun t =>
    ⟨c + Real.exp t, show c < c + Real.exp t by linarith [Real.exp_pos t]⟩
  have hφ_inj : Function.Injective φ := by
    intro t₁ t₂ h
    have hexp : Real.exp t₁ = Real.exp t₂ := by
      have hv : (φ t₁).1 = (φ t₂).1 := congrArg Subtype.val h
      dsimp [φ] at hv
      linarith
    exact Real.exp_injective hexp
  have hR : Countable ℝ := hφ_inj.countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hR)

/-- **Exercise 4.9 (negative answer: `a^b` need not be transcendental over `ℚ`)** (§4.4, p. 48):
There exist positive real numbers `a > 1` and `b > 0`, both transcendental over `ℚ` (in `ℝ` and
in `ℂ`), such that `a ^ b = 2` (with real power `Real.rpow` and complex power `Complex.cpow`
agreeing canonically), so `a ^ b ∈ ℚ` is algebraic rather than transcendental over `ℚ`. -/
theorem exercise_4_9_exists_algebraic_power :
    ∃ a b : ℝ,
      1 < a ∧ 0 < b ∧
      IsGarlingTranscendental ℚ a ∧ IsGarlingTranscendental ℚ b ∧
      IsGarlingTranscendental ℚ (a : ℂ) ∧ IsGarlingTranscendental ℚ (b : ℂ) ∧
      a ^ b = (2 : ℝ) ∧ ((a : ℂ) ^ (b : ℂ)) = (2 : ℂ) ∧
      ¬ IsGarlingTranscendental ℚ ((a : ℂ) ^ (b : ℂ)) := by
  let S := Set.Ioi (1 : ℝ)
  let f : S → ℝ := fun a => Real.log 2 / Real.log a.1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ h
    have ha₁_gt1 : 1 < a₁.1 := a₁.2
    have ha₂_gt1 : 1 < a₂.1 := a₂.2
    have ha₁_pos : 0 < a₁.1 := by linarith
    have ha₂_pos : 0 < a₂.1 := by linarith
    have hlog₁ : 0 < Real.log a₁.1 := Real.log_pos ha₁_gt1
    have hlog₂ : 0 < Real.log a₂.1 := Real.log_pos ha₂_gt1
    have hlog_eq : Real.log a₁.1 = Real.log a₂.1 := by
      dsimp [f] at h
      have h1 : Real.log 2 / Real.log a₁.1 * Real.log a₁.1 * Real.log a₂.1 =
          Real.log 2 / Real.log a₂.1 * Real.log a₁.1 * Real.log a₂.1 := by
        rw [h]
      rw [div_mul_cancel₀ _ (ne_of_gt hlog₁)] at h1
      have h2 : Real.log 2 * Real.log a₂.1 = Real.log 2 * Real.log a₁.1 := by
        calc Real.log 2 * Real.log a₂.1
          _ = (Real.log 2 / Real.log a₂.1 * Real.log a₁.1) * Real.log a₂.1 := h1
          _ = (Real.log 2 / Real.log a₂.1 * Real.log a₂.1) * Real.log a₁.1 := by ring
          _ = Real.log 2 * Real.log a₁.1 := by rw [div_mul_cancel₀ _ (ne_of_gt hlog₂)]
      exact (mul_left_cancel₀ (ne_of_gt hlog2_pos) h2).symm
    ext
    rw [← Real.exp_log ha₁_pos, ← Real.exp_log ha₂_pos, hlog_eq]
  let Alg := algebraicElementsSet ℚ ℝ
  let Bad : Set S := (Subtype.val ⁻¹' Alg) ∪ (f ⁻¹' Alg)
  have hBad_count : Bad.Countable :=
    (countable_algebraic_reals.preimage Subtype.val_injective).union
      (countable_algebraic_reals.preimage hf_inj)
  have hex : ∃ a : S, a ∉ Bad := by
    by_contra hno
    push Not at hno
    have huniv : Bad = Set.univ := Set.eq_univ_of_forall hno
    have hS_count_type : Countable S := by
      rw [← Set.countable_univ_iff, ← huniv]
      exact hBad_count
    exact not_countable_Ioi 1 (Set.countable_coe_iff.mp hS_count_type)
  obtain ⟨a, ha_notBad⟩ := hex
  have ha_trans : IsGarlingTranscendental ℚ a.1 :=
    fun h => ha_notBad (Or.inl h)
  have hb_trans : IsGarlingTranscendental ℚ (f a) :=
    fun h => ha_notBad (Or.inr h)
  have ha_gt1 : 1 < a.1 := a.2
  have ha_pos : 0 < a.1 := by linarith
  have hlog_a_pos : 0 < Real.log a.1 := Real.log_pos ha_gt1
  have hb_pos : 0 < f a := div_pos hlog2_pos hlog_a_pos
  have hrpow : a.1 ^ (f a) = (2 : ℝ) := by
    rw [Real.rpow_def_of_pos ha_pos]
    dsimp [f]
    rw [mul_div_cancel₀ _ (ne_of_gt hlog_a_pos), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hcpow : ((a.1 : ℂ) ^ ((f a : ℝ) : ℂ)) = (2 : ℂ) := by
    have hcast := Complex.ofReal_cpow (le_of_lt ha_pos) (f a)
    rw [hrpow] at hcast
    exact mod_cast hcast.symm
  have h2_alg : ¬ IsGarlingTranscendental ℚ ((a.1 : ℂ) ^ ((f a : ℝ) : ℂ)) := by
    rw [hcpow]
    intro h2t
    apply h2t
    exact ⟨Polynomial.X - Polynomial.C 2,
      Polynomial.X_sub_C_ne_zero 2,
      by simp⟩
  exact ⟨a.1, f a, a.2, hb_pos, ha_trans, hb_trans,
    (isGarlingTranscendental_rat_ofReal_iff a.1).mpr ha_trans,
    (isGarlingTranscendental_rat_ofReal_iff (f a)).mpr hb_trans,
    hrpow, hcpow, h2_alg⟩

/-- **Exercise 4.9 (positive possibility: `a^b` can also be transcendental over `ℚ`)** (§4.4,
p. 48): There exist real numbers `a > 1` and `b > 1`, both transcendental over `ℚ`, such that
`a ^ b` (both as a real power and as a complex power) is transcendental over `ℚ`. -/
theorem exercise_4_9_exists_transcendental_power :
    ∃ a b : ℝ,
      1 < a ∧ 1 < b ∧
      IsGarlingTranscendental ℚ a ∧ IsGarlingTranscendental ℚ b ∧
      IsGarlingTranscendental ℚ (a : ℂ) ∧ IsGarlingTranscendental ℚ (b : ℂ) ∧
      ((a ^ b : ℝ) : ℂ) = (a : ℂ) ^ (b : ℂ) ∧
      IsGarlingTranscendental ℚ (a ^ b) ∧
      IsGarlingTranscendental ℚ ((a : ℂ) ^ (b : ℂ)) := by
  obtain ⟨a, _, ha1, _, ha_trans, _, haC_trans, _, _, _, _⟩ :=
    exercise_4_9_exists_algebraic_power
  have ha_pos : 0 < a := by linarith
  have hlog_a_pos : 0 < Real.log a := Real.log_pos ha1
  let S := Set.Ioi (1 : ℝ)
  let g : S → ℝ := fun b => a ^ b.1
  have hg_inj : Function.Injective g := by
    intro b₁ b₂ h
    have hlog := congrArg Real.log h
    dsimp [g] at hlog
    rw [Real.log_rpow ha_pos, Real.log_rpow ha_pos] at hlog
    ext
    exact mul_right_cancel₀ (ne_of_gt hlog_a_pos) hlog
  let Alg := algebraicElementsSet ℚ ℝ
  let Bad : Set S := (Subtype.val ⁻¹' Alg) ∪ (g ⁻¹' Alg)
  have hBad_count : Bad.Countable :=
    (countable_algebraic_reals.preimage Subtype.val_injective).union
      (countable_algebraic_reals.preimage hg_inj)
  have hex : ∃ b : S, b ∉ Bad := by
    by_contra hno
    push Not at hno
    have huniv : Bad = Set.univ := Set.eq_univ_of_forall hno
    have hS_count_type : Countable S := by
      rw [← Set.countable_univ_iff, ← huniv]
      exact hBad_count
    exact not_countable_Ioi 1 (Set.countable_coe_iff.mp hS_count_type)
  obtain ⟨b, hb_notBad⟩ := hex
  have hb_trans : IsGarlingTranscendental ℚ b.1 :=
    fun h => hb_notBad (Or.inl h)
  have hab_trans : IsGarlingTranscendental ℚ (a ^ b.1) :=
    fun h => hb_notBad (Or.inr h)
  have hcpow_eq : ((a ^ b.1 : ℝ) : ℂ) = (a : ℂ) ^ (b.1 : ℂ) :=
    Complex.ofReal_cpow (le_of_lt ha_pos) b.1
  have habC_trans : IsGarlingTranscendental ℚ ((a : ℂ) ^ (b.1 : ℂ)) := by
    rw [← hcpow_eq]
    exact (isGarlingTranscendental_rat_ofReal_iff (a ^ b.1)).mpr hab_trans
  exact ⟨a, b.1, ha1, b.2, ha_trans, hb_trans, haC_trans,
    (isGarlingTranscendental_rat_ofReal_iff b.1).mpr hb_trans,
    hcpow_eq, hab_trans, habC_trans⟩

/-- **Exercise 4.9** (§4.4, p. 48): Complete answer to *"Suppose that `a` and `b` are complex
numbers which are transcendental over `ℚ`. Is `a^b` transcendental over `ℚ`?"* — **No** in general
(there exist positive real transcendental numbers `a > 1, b > 0` with `a^b = 2 ∈ ℚ`, where real
and complex powers coincide), though **transcendental values also occur** (there exist positive
real transcendental numbers `a > 1, b > 1` with `a^b` transcendental over `ℚ`). -/
theorem exercise_4_9 :
    ¬ (∀ a b : ℂ, IsGarlingTranscendental ℚ a → IsGarlingTranscendental ℚ b →
        IsGarlingTranscendental ℚ (a ^ b)) ∧
    (∃ a b : ℝ,
      1 < a ∧ 0 < b ∧
      IsGarlingTranscendental ℚ a ∧ IsGarlingTranscendental ℚ b ∧
      a ^ b = (2 : ℝ) ∧ ((a : ℂ) ^ (b : ℂ)) = (2 : ℂ) ∧
      ¬ IsGarlingTranscendental ℚ ((a : ℂ) ^ (b : ℂ))) ∧
    (∃ a b : ℝ,
      1 < a ∧ 1 < b ∧
      IsGarlingTranscendental ℚ a ∧ IsGarlingTranscendental ℚ b ∧
      ((a ^ b : ℝ) : ℂ) = (a : ℂ) ^ (b : ℂ) ∧
      IsGarlingTranscendental ℚ ((a : ℂ) ^ (b : ℂ))) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, ha₁t, hb₁t, ha₁Ct, hb₁Ct, hr₁, hc₁, hnot₁⟩ :=
    exercise_4_9_exists_algebraic_power
  obtain ⟨a₂, b₂, ha₂, hb₂, ha₂t, hb₂t, _, _, hc₂, _, hab₂Ct⟩ :=
    exercise_4_9_exists_transcendental_power
  refine ⟨?_, ⟨a₁, b₁, ha₁, hb₁, ha₁t, hb₁t, hr₁, hc₁, hnot₁⟩,
    ⟨a₂, b₂, ha₂, hb₂, ha₂t, hb₂t, hc₂, hab₂Ct⟩⟩
  intro hall
  exact hnot₁ (hall (a₁ : ℂ) (b₁ : ℂ) ha₁Ct hb₁Ct)

/-- **Exercise 4.10 (ambient extension form)** (§4.4, p. 48): Any extension `L : K` containing an
element `α ∈ L \ K` algebraic over `K` and an element `β ∈ L` transcendental over `K` is not
simple over `K` (in particular, when `L = K(α, β)`). -/
theorem exercise_4_10_ambient {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α β : L} (hα_alg : IsGarlingAlgebraic K α)
    (hα_notMem : α ∉ Set.range (algebraMap K L))
    (hβ_trans : IsGarlingTranscendental K β) :
    ¬ IsSimpleExtension K L := by
  rintro ⟨γ, hγ⟩
  have hα_ne0 : α ≠ 0 := by
    rintro rfl
    exact hα_notMem ⟨0, map_zero _⟩
  have hα_mem : α ∈ IntermediateField.adjoin K ({γ} : Set L) :=
    hγ ▸ IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K α).mp hα_mem
  have hs_eval : Polynomial.aeval γ s ≠ 0 := by
    intro hs0
    apply hα_ne0
    rw [hrs, hs0, div_zero]
  have hs_ne0 : s ≠ 0 := by
    intro hs0
    apply hs_eval
    simp [hs0]
  let F : IntermediateField K L := IntermediateField.adjoin K ({α} : Set L)
  let αF : F := ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
  let P : F[X] := r.map (algebraMap K F) - Polynomial.C αF * s.map (algebraMap K F)
  have hP_ne0 : P ≠ 0 := by
    intro hP0
    let i := s.natDegree
    have hs_coeff : s.coeff i ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hs_ne0
    have hci : (P.coeff i : L) = 0 := by rw [hP0]; simp
    have hci_eq :
        (P.coeff i : L) = algebraMap K L (r.coeff i) - α * algebraMap K L (s.coeff i) := by
      simp only [P, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map]
      rfl
    rw [hci_eq, sub_eq_zero] at hci
    have hsK_ne0 : algebraMap K L (s.coeff i) ≠ 0 :=
      fun h0 => hs_coeff ((injective_iff_map_eq_zero _).mp (algebraMap K L).injective _ h0)
    have hα_eq : α = algebraMap K L (r.coeff i / s.coeff i) := by
      rw [map_div₀]
      exact (eq_div_iff hsK_ne0).mpr hci.symm
    exact hα_notMem ⟨r.coeff i / s.coeff i, hα_eq.symm⟩
  have haeval_map : ∀ q : K[X], Polynomial.aeval γ (q.map (algebraMap K F)) =
      Polynomial.aeval γ q := by
    intro q
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K F L,
      ← Polynomial.aeval_def]
  have hP_eval : Polynomial.aeval γ P = 0 := by
    simp only [P, map_sub, map_mul, Polynomial.aeval_C, haeval_map]
    have hmul : Polynomial.aeval γ r = α * Polynomial.aeval γ s :=
      (div_eq_iff hs_eval).mp hrs.symm
    have hαF : algebraMap F L αF = α := rfl
    rw [hαF, hmul, sub_self]
  have hγ_alg : IsGarlingAlgebraic F γ := ⟨P, hP_ne0, hP_eval⟩
  have hadj_F : IntermediateField.adjoin F ({γ} : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxK : x ∈ IntermediateField.adjoin K ({γ} : Set L) := hγ ▸ IntermediateField.mem_top
    obtain ⟨u, v, huv⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hxK
    rw [IntermediateField.mem_adjoin_simple_iff F x]
    refine ⟨u.map (algebraMap K F), v.map (algebraMap K F), ?_⟩
    rw [haeval_map, haeval_map, huv]
  have halg_Fadj : IsAlgebraicExtension F (IntermediateField.adjoin F ({γ} : Set L)) :=
    corollary_1_to_theorem_4_6 hγ_alg
  have halg_FL : IsAlgebraicExtension F L := by
    let eFL : IntermediateField.adjoin F ({γ} : Set L) ≃ₐ[F] L :=
      (IntermediateField.equivOfEq hadj_F).trans IntermediateField.topEquiv
    have _ : Algebra.IsAlgebraic F (IntermediateField.adjoin F ({γ} : Set L)) :=
      (isAlgebraicExtension_iff F _).mp halg_Fadj
    exact (isAlgebraicExtension_iff F L).mpr eFL.isAlgebraic
  have halg_KF : IsAlgebraicExtension K F := corollary_1_to_theorem_4_6 hα_alg
  have halg_KL : IsAlgebraicExtension K L := theorem_4_7 halg_FL halg_KF
  exact hβ_trans (halg_KL β)

/-- **Exercise 4.10** (§4.4, p. 48): Suppose that `K(α, β) : K` is an extension, that `α` is
algebraic over `K`, but not in `K`, and that `β` is transcendental over `K`. Then `K(α, β) : K` is
not simple. -/
theorem exercise_4_10 {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α β : L} (hα_alg : IsGarlingAlgebraic K α)
    (hα_notMem : α ∉ Set.range (algebraMap K L))
    (hβ_trans : IsGarlingTranscendental K β) :
    ¬ IsSimpleExtension K (IntermediateField.adjoin K ({α, β} : Set L)) := by
  let E := IntermediateField.adjoin K ({α, β} : Set L)
  let αE : E := ⟨α, IntermediateField.subset_adjoin K ({α, β} : Set L) (by simp)⟩
  let βE : E := ⟨β, IntermediateField.subset_adjoin K ({α, β} : Set L) (by simp)⟩
  have hinj : Function.Injective (algebraMap E L) := Subtype.val_injective
  have hαE_alg : IsGarlingAlgebraic K αE :=
    (isAlgebraic_algebraMap_iff (R := K) hinj).mp hα_alg
  have hαE_notMem : αE ∉ Set.range (algebraMap K E) := by
    rintro ⟨k, hk⟩
    apply hα_notMem
    refine ⟨k, ?_⟩
    have hv := congrArg Subtype.val hk
    exact hv
  have hβE_trans : IsGarlingTranscendental K βE := by
    intro hβE_alg
    exact hβ_trans ((isAlgebraic_algebraMap_iff (R := K) hinj).mpr hβE_alg)
  exact exercise_4_10_ambient hαE_alg hαE_notMem hβE_trans

/-! ## §4.5 Monomorphisms of algebraic extensions (printed p. 48, PDF p. 56) -/

/-- Garling's definition (§4.5, p. 48): for an extension `L : K` and a ring homomorphism
`τ : L →+* L`, we say that `τ` *fixes `K`* if `τ(k) = k` for each `k ∈ K`. -/
def FixesBaseField (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (τ : L →+* L) : Prop :=
  ∀ k : K, τ (algebraMap K L k) = algebraMap K L k

/-- Bundling a ring homomorphism `τ : L →+* L` fixing `K` as a `K`-algebra endomorphism
`L →ₐ[K] L`. -/
def FixesBaseField.toAlgHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L →+* L} (hfix : FixesBaseField K τ) : L →ₐ[K] L :=
  { τ with commutes' := hfix }

/-- **Theorem 4.8** (§4.5, p. 48): Suppose that `L : K` is algebraic and that `τ : L → L` is a
monomorphism which fixes `K`. Then `τ` maps `L` onto `L`. -/
theorem theorem_4_8 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) {τ : L →+* L}
    (hmono : IsRingMonomorphism τ) (hfix : FixesBaseField K τ) :
    Function.Surjective τ := by
  classical
  intro α
  obtain ⟨f, hf0, hfα⟩ := halg α
  let fL : L[X] := f.map (algebraMap K L)
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  let R : Finset L := fL.roots.toFinset
  have hmap_root : ∀ β : L, β ∈ R → τ β ∈ R := by
    intro β hβ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL0, Polynomial.IsRoot] at hβ ⊢
    have hτ_eval : fL.eval (τ β) = τ (fL.eval β) := by
      dsimp only [fL]
      rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
      have hcomp : τ.comp (algebraMap K L) = algebraMap K L := RingHom.ext hfix
      rw [hcomp]
    rw [hτ_eval, hβ, map_zero]
  let τR : {x : L // x ∈ R} → {x : L // x ∈ R} :=
    fun x => ⟨τ x.1, hmap_root x.1 x.2⟩
  have hτR_inj : Function.Injective τR := by
    intro x y hxy
    ext
    exact hmono (congrArg Subtype.val hxy)
  have hτR_surj : Function.Surjective τR := Finite.surjective_of_injective hτR_inj
  have hα_mem : α ∈ R := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL0, Polynomial.IsRoot]
    dsimp only [fL]
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hfα
  obtain ⟨⟨β, _⟩, hβ⟩ := hτR_surj ⟨α, hα_mem⟩
  exact ⟨β, congrArg Subtype.val hβ⟩

/-- Garling's prose definition of a field *automorphism* (§4.5, p. 48): a ring monomorphism of a
field onto itself. -/
def IsFieldAutomorphism {L : Type*} [Field L] (τ : L →+* L) : Prop :=
  IsRingMonomorphism τ ∧ Function.Surjective τ

/-- Immediate corollary of `Theorem 4.8` in Garling's prose (§4.5, p. 48): every ring monomorphism
`τ : L →+* L` fixing `K` on an algebraic extension `L : K` is a field automorphism of `L`. -/
theorem theorem_4_8_isFieldAutomorphism {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) {τ : L →+* L}
    (hmono : IsRingMonomorphism τ) (hfix : FixesBaseField K τ) :
    IsFieldAutomorphism τ :=
  ⟨hmono, theorem_4_8 halg hmono hfix⟩

/-- **Theorem 4.8 (subfield form)** (§4.5, p. 48): For `K : Subfield L` with `L : K` algebraic,
any monomorphism `τ : L →+* L` fixing each `k ∈ K` is surjective. -/
theorem theorem_4_8_subfield {L : Type*} [Field L] (K : Subfield L)
    (halg : IsAlgebraicExtension K L) {τ : L →+* L}
    (hmono : IsRingMonomorphism τ) (hfix : ∀ k ∈ K, τ k = k) :
    Function.Surjective τ :=
  theorem_4_8 halg hmono fun k => hfix k.1 k.2

/-- **Exercise 4.11 (for every base field `K`)** (§4.5, p. 48): On `L = FractionRing K[X]`, the
`K`-fixing monomorphism `τ : L →+* L` induced by `X ↦ X²` is not surjective (`X` is not in the
range of `τ`), witnessing for every field `K` that the hypothesis `IsAlgebraicExtension K L`
cannot be dropped from `Theorem 4.8`. -/
theorem exercise_4_11_for_every_field (K : Type*) [Field K] :
    ∃ τ : FractionRing K[X] →+* FractionRing K[X],
      ¬ IsAlgebraicExtension K (FractionRing K[X]) ∧
      IsRingMonomorphism τ ∧
      FixesBaseField K τ ∧
      ¬ Function.Surjective τ := by
  let L := FractionRing K[X]
  let j : K[X] →+* K[X] := (Polynomial.aeval (Polynomial.X ^ 2 : K[X])).toRingHom
  have hj_deg : ∀ p : K[X], (j p).natDegree = p.natDegree * 2 := by
    intro p
    change (Polynomial.aeval (Polynomial.X ^ 2 : K[X]) p).natDegree = p.natDegree * 2
    rw [← Polynomial.comp_eq_aeval, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  have hj_inj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_cases hp_deg : p.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hp_deg] at hp ⊢
      change Polynomial.aeval (Polynomial.X ^ 2 : K[X]) (Polynomial.C (p.coeff 0)) = 0 at hp
      rw [Polynomial.aeval_C] at hp
      exact hp
    · have hpos : 0 < (j p).natDegree := by
        rw [hj_deg]
        omega
      rw [hp, Polynomial.natDegree_zero] at hpos
      omega
  let ι : K[X] →+* L := (algebraMap K[X] L).comp j
  have hι_inj : Function.Injective ι :=
    (IsFractionRing.injective K[X] L).comp hj_inj
  let τ : L →+* L := IsFractionRing.lift hι_inj
  refine ⟨τ, ?_, τ.injective, ?_, ?_⟩
  · intro halg
    obtain ⟨f, hf0, hfx⟩ := halg (algebraMap K[X] L Polynomial.X)
    have hfx' :
        Polynomial.aeval (algebraMap K[X] L Polynomial.X) f = algebraMap K[X] L f := by
      have hhom := Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom K K[X] L) (Polynomial.X : K[X]) f
      simpa using hhom
    rw [hfx'] at hfx
    exact hf0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective K[X] L) f hfx)
  · intro k
    rw [IsScalarTower.algebraMap_apply K K[X] L k]
    dsimp only [τ]
    rw [IsFractionRing.lift_algebraMap hι_inj]
    dsimp only [ι, RingHom.comp_apply, j]
    change algebraMap K[X] L (Polynomial.aeval (Polynomial.X ^ 2 : K[X]) (algebraMap K K[X] k)) = _
    rw [(Polynomial.aeval (Polynomial.X ^ 2 : K[X])).commutes k]
  · intro hsurj
    obtain ⟨y, hy⟩ := hsurj (algebraMap K[X] L Polynomial.X)
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) y
    have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    have hjs0 : j s ≠ 0 := fun h0 => hs0 ((injective_iff_map_eq_zero _).mp hj_inj s h0)
    have hajs0 : algebraMap K[X] L (j s) ≠ 0 :=
      fun h0 => hjs0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective K[X] L) _ h0)
    dsimp only [τ] at hy
    rw [map_div₀, IsFractionRing.lift_algebraMap hι_inj,
      IsFractionRing.lift_algebraMap hι_inj] at hy
    dsimp only [ι, RingHom.comp_apply] at hy
    have hmul : algebraMap K[X] L (j r) = algebraMap K[X] L (Polynomial.X * j s) := by
      rw [map_mul]
      exact (div_eq_iff hajs0).mp hy
    have hpoly : j r = Polynomial.X * j s :=
      IsFractionRing.injective K[X] L hmul
    have hd_eq : (j r).natDegree = (Polynomial.X * j s).natDegree :=
      congrArg Polynomial.natDegree hpoly
    rw [hj_deg r, Polynomial.natDegree_mul Polynomial.X_ne_zero hjs0,
      Polynomial.natDegree_X, hj_deg s] at hd_eq
    omega

/-- **Exercise 4.11** (§4.5, p. 48): The condition that `L : K` is algebraic cannot be dropped
from `Theorem 4.8`: there exist a field extension `L : K` (not algebraic) and a ring monomorphism
`τ : L →+* L` fixing `K` such that `τ` is not surjective (so the version of `Theorem 4.8` omitting
`IsAlgebraicExtension K L` is false). -/
theorem exercise_4_11 :
    (∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (τ : L →+* L),
      ¬ IsAlgebraicExtension K L ∧ IsRingMonomorphism τ ∧ FixesBaseField K τ ∧
      ¬ Function.Surjective τ) ∧
    ¬ (∀ (K L : Type) [Field K] [Field L] [Algebra K L] (τ : L →+* L),
      IsRingMonomorphism τ → FixesBaseField K τ → Function.Surjective τ) := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hnalg, hmono, hfix, hnsurj⟩ := exercise_4_11_for_every_field (ZMod 2)
  refine ⟨⟨ZMod 2, FractionRing (ZMod 2)[X], _, _, _, τ, hnalg, hmono, hfix, hnsurj⟩, ?_⟩
  intro hall
  exact hnsurj (@hall (ZMod 2) (FractionRing (ZMod 2)[X]) _ _ _ τ hmono hfix)

end Garling.Chapter04
