import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter06
import Garling.Chapter07
import Garling.Chapter09
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Chapter 10: Separability

Formalization of Chapter 10 (*Separability*, printed pp. 82–90 / PDF pp. 90–98) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering all
six sections (`§10.1`–`§10.6`), all 15 main-text theorem/corollary items, all 11 numbered exercises
(`10.1`–`10.11`), and all unnumbered prose definitions, derivative identities, and concrete examples
in exact source order:

- **§10.1 Basic ideas** (printed p. 82 / PDF p. 90):
  prose definitions of *separable* irreducible/arbitrary polynomials (`IsGarlingSeparableIrreducible`,
  `IsGarlingSeparablePoly`), *separable* elements (`IsGarlingSeparableElement`), and *separable*
  extensions (`IsGarlingSeparableExtension`), bridges to Mathlib's `Polynomial.Separable`,
  `IsSeparable`, and `Algebra.IsSeparable`, plus `Theorem 10.1`.
- **§10.2 Monomorphisms and automorphisms** (printed pp. 83–84 / PDF pp. 91–92):
  `Theorem 10.2`, `Theorem 10.3`, `Corollary 1`–`Corollary 4` [to `Theorem 10.3`], and
  `Exercise 10.1`.
- **§10.3 Galois extensions** (printed pp. 84–85 / PDF pp. 92–93):
  prose definition of *Galois extension* (`IsGarlingGaloisExtension` = finite + normal + separable,
  bridged to `FiniteDimensional ∧ IsGalois`), and `Theorem 10.4`.
- **§10.4 Differentiation** (printed pp. 85–87 / PDF pp. 93–95):
  prose definitions of *repeated root* (`HasGarlingRepeatedRoot` vs. the literal p. 85 `in K[x]`
  slip `HasLiteralPrintedRepeatedRootInBasePoly`) and algebraic derivative `D : K[x] → K[x]`
  (`garlingDeriv`) with `K`-linearity and Leibniz rules, `Theorem 10.5` (with p. 85 counterexamples),
  `Theorem 10.6`, `Corollary` [to `Theorem 10.6`], `Exercise 10.2` (Taylor's formula), and
  `Exercise 10.3` (with counterexamples to the omitted `= 0` slip and exact multiplicity theorems).
- **§10.5 The Frobenius monomorphism** (printed pp. 87–88 / PDF pp. 95–96):
  `Theorem 10.7`, prose definition of *Frobenius monomorphism* (`garlingFrobenius`), `Corollary`
  [to `Theorem 10.7`], `Exercise 10.4` (Wilson's theorem via `x^{p-1} - 1`), `Exercise 10.5`, and
  `Exercise 10.6`.
- **§10.6 Inseparable polynomials** (printed pp. 88–90 / PDF pp. 96–98):
  `f(x) = g(x^p)` notation (`garlingCompXPow`), `Theorem 10.8`, `Corollary` [to `Theorem 10.8`],
  the p. 89 `ℤ_p(α)` inseparable irreducible example `x^p - α`, and `Exercises 10.7`–`10.11`
  (including inline definitions `IsGarlingPerfectField` in `10.7` and `IsGarlingTotallyInseparable`
  in `10.10`).
-/

namespace Garling.Chapter10

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter09
open scoped BigOperators Polynomial IntermediateField

universe u v w

/-! ## §10.1 Basic ideas (printed p. 82, PDF p. 90) -/

/-- Garling's prose definition that an irreducible polynomial `f ∈ K[x]` of degree `n` is
*separable (over `K`)* (§10.1, printed p. 82 / PDF p. 90):
*"Suppose first that `f` is an irreducible polynomial of degree `n` in `K[x]` and that `L : K` is a
splitting field extension for `f`. We say that `f` is separable (over `K`) if `f` has `n` distinct
roots in `L`."*

Quantifying over all `Type u` splitting field extensions (which exist by `Theorem 7.3`,
`theorem_7_3_natDegree`) stays inside `Prop`, and `isGarlingSeparableIrreducible_iff_of_splittingField`
below proves via `Corollary 1` to `Theorem 7.5` (`splitting_field_unique_up_to_algEquiv`) that the
condition holds for one splitting field extension `L : K` (in *any* universe `v`) if and only if it
holds for all splitting field extensions. -/
def IsGarlingSeparableIrreducible {K : Type u} [Field K] (f : K[X]) : Prop :=
  ∃ h : Irreducible f,
    ∀ (L : Type u) [Field L] [Algebra K L],
      IsGarlingSplittingFieldExtension K L f →
        setOrder {α : L | Polynomial.aeval α f = 0} = (garlingDegree f h.ne_zero : ℕ∞)

/-- Helper: transporting the distinct-root count `setOrder {α : L | aeval α f = 0}` across a
`K`-algebra isomorphism `e : L₁ ≃ₐ[K] L₂`. -/
private theorem setOrder_roots_congr {K : Type*} {L₁ : Type*} {L₂ : Type*}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (f : K[X]) :
    setOrder {α : L₁ | Polynomial.aeval α f = 0} =
      setOrder {β : L₂ | Polynomial.aeval β f = 0} := by
  refine ENat.card_congr
    { toFun := fun α => ⟨e α.1, by
        change Polynomial.aeval (e.toAlgHom α.1) f = 0
        rw [Polynomial.aeval_algHom_apply, α.2, map_zero]⟩
      invFun := fun β => ⟨e.symm β.1, by
        change Polynomial.aeval (e.symm.toAlgHom β.1) f = 0
        rw [Polynomial.aeval_algHom_apply, β.2, map_zero]⟩
      left_inv := fun α => Subtype.ext (e.symm_apply_apply α.1)
      right_inv := fun β => Subtype.ext (e.apply_symm_apply β.1) }

/-- Helper: for any non-zero `f ∈ K[X]` and any field extension `L : K`, the root set
`{α : L | aeval α f = 0}` is finite and has `setOrder` equal to `(f.map (algebraMap K L)).roots.toFinset.card`. -/
private theorem setOrder_aeval_eq_zero_eq_toFinset_card {K L : Type*} [Field K] [Field L]
    [Algebra K L] [DecidableEq L] {f : K[X]} (hf0 : f ≠ 0) :
    setOrder {α : L | Polynomial.aeval α f = 0} =
      (((f.map (algebraMap K L)).roots.toFinset.card : ℕ) : ℕ∞) ∧
    Nat.card {α : L // Polynomial.aeval α f = 0} =
      (f.map (algebraMap K L)).roots.toFinset.card := by
  have hfL0 : f.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  let s : Finset L := (f.map (algebraMap K L)).roots.toFinset
  let eFin : {α : L // Polynomial.aeval α f = 0} ≃ s :=
    { toFun := fun α => ⟨α.1, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL0, Polynomial.IsRoot.def,
          Polynomial.eval_map, ← Polynomial.aeval_def]
        exact α.2⟩
      invFun := fun α => ⟨α.1, by
        have h := (Polynomial.mem_roots hfL0).mp (Multiset.mem_toFinset.mp α.2)
        rwa [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : setOrder {α : L | Polynomial.aeval α f = 0} = ENat.card s := ENat.card_congr eFin
  rw [h1, ENat.card_eq_coe_fintype_card, Fintype.card_coe]
  refine ⟨rfl, ?_⟩
  rw [Nat.card_congr eFin, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Independence of splitting field choice (§10.1, p. 82, via `Corollary 1` to `Theorem 7.5`):
for any irreducible `f ∈ K[x]` (`K : Type u`) and *any* splitting field extension `L : K` (`L : Type v`
in *any* universe `v`), `IsGarlingSeparableIrreducible f` holds if and only if `f` has
`n = garlingDegree f hf.ne_zero` distinct roots in `L`. -/
theorem isGarlingSeparableIrreducible_iff_of_splittingField {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf : Irreducible f)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    (IsGarlingSeparableIrreducible f ↔
      setOrder {α : L | Polynomial.aeval α f = 0} = (garlingDegree f hf.ne_zero : ℕ∞)) ∧
    (IsGarlingSeparableIrreducible f ↔
      Nat.card {α : L // Polynomial.aeval α f = 0} = garlingDegree f hf.ne_zero) := by
  classical
  have h1 :
      IsGarlingSeparableIrreducible f ↔
        setOrder {α : L | Polynomial.aeval α f = 0} = (garlingDegree f hf.ne_zero : ℕ∞) := by
    constructor
    · rintro ⟨_, hall⟩
      obtain ⟨L₀, instF₀, instA₀, hsf₀, _⟩ := theorem_7_3_natDegree f
      let _ : Field L₀ := instF₀
      let _ : Algebra K L₀ := instA₀
      obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf₀ hsf
      rw [← setOrder_roots_congr e f]
      exact hall L₀ hsf₀
    · intro hL
      refine ⟨hf, fun L' _ _ hsf' => ?_⟩
      obtain ⟨e⟩ := splitting_field_unique_up_to_algEquiv hsf' hsf
      rw [setOrder_roots_congr e f]
      exact hL
  refine ⟨h1, h1.trans ?_⟩
  obtain ⟨hord, hnat⟩ := setOrder_aeval_eq_zero_eq_toFinset_card (L := L) hf.ne_zero
  rw [hord, hnat]
  exact ⟨fun h => Nat.cast_injective h, fun h => congrArg Nat.cast h⟩

/-- Exact equivalence between Garling's §10.1 distinct-roots definition `IsGarlingSeparableIrreducible f`
(for irreducible `f ∈ K[X]`) and Mathlib's `Polynomial.Separable f`. -/
theorem isGarlingSeparableIrreducible_iff_separable {K : Type u} [Field K] {f : K[X]}
    (hf : Irreducible f) :
    IsGarlingSeparableIrreducible f ↔ f.Separable := by
  classical
  obtain ⟨L, instFL, instAL, hsf, _⟩ := theorem_7_3_natDegree f
  let _ : Field L := instFL
  let _ : Algebra K L := instAL
  let _ : DecidableEq L := Classical.decEq L
  rw [(isGarlingSeparableIrreducible_iff_of_splittingField hf hsf).2]
  obtain ⟨_, hnat⟩ := setOrder_aeval_eq_zero_eq_toFinset_card (L := L) hf.ne_zero
  rw [hnat]
  have hf0 : f ≠ 0 := hf.ne_zero
  have hsp : (f.map (algebraMap K L)).Splits :=
    (garlingSplitsOver_iff_splits K L f).mp hsf.1
  have hmap0 : f.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  have hcard_roots : (f.map (algebraMap K L)).roots.card = garlingDegree f hf0 := by
    unfold garlingDegree
    rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective f]
    exact hsp.natDegree_eq_card_roots.symm
  constructor
  · intro hcard
    rw [← hcard_roots] at hcard
    have hnodup : (f.map (algebraMap K L)).roots.Nodup :=
      Multiset.toFinset_card_eq_card_iff_nodup.mp hcard
    have heq := Polynomial.Splits.eq_prod_roots hsp
    have hsep_prod :
        (((f.map (algebraMap K L)).roots).map fun a : L => Polynomial.X - Polynomial.C a).prod.Separable := by
      have hfin_prod :
          (∏ a ∈ (f.map (algebraMap K L)).roots.toFinset, (Polynomial.X - Polynomial.C a)) =
            (((f.map (algebraMap K L)).roots).map fun a : L => Polynomial.X - Polynomial.C a).prod := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
      rw [← hfin_prod]
      refine Polynomial.separable_prod' (fun x _ y _ hxy => ?_) (fun _ _ => Polynomial.separable_X_sub_C)
      exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy
    have hlc_unit : IsUnit (Polynomial.C (f.map (algebraMap K L)).leadingCoeff) :=
      (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hmap0)).map Polynomial.C
    have hsep_map : (f.map (algebraMap K L)).Separable := by
      rw [heq]
      exact Polynomial.Separable.unit_mul hlc_unit hsep_prod
    exact (Polynomial.separable_map (algebraMap K L)).mp hsep_map
  · intro hsep
    rw [← hcard_roots]
    exact Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots ((Polynomial.separable_map (algebraMap K L)).mpr hsep))

/-- Garling's prose definition that an arbitrary polynomial `f ∈ K[x]` is *separable (over `K`)*
(§10.1, printed p. 82 / PDF p. 90):
*"Suppose next that `f` is an arbitrary polynomial in `K[x]`. We say that `f` is separable (over `K`)
if each of its irreducible factors is separable."*

Note (`BRIEF.md` Flag 2): unlike Mathlib's `Polynomial.Separable` (which requires squarefreeness and
`f ≠ 0`), Garling's definition allows repeated separable irreducible factors such as `(x - 1)^2 ∈ ℚ[x]`
and units `c ∈ Kˣ`, which is essential for `Corollary 3` [to `Theorem 10.3`], `Corollary` [to
`Theorem 10.6`], `Corollary` [to `Theorem 10.8`], and `Exercise 10.7`. -/
def IsGarlingSeparablePoly {K : Type u} [Field K] (f : K[X]) : Prop :=
  ∀ g : K[X], Irreducible g → g ∣ f → IsGarlingSeparableIrreducible g

/-- Equivalence of `IsGarlingSeparablePoly f` with Chapter 3's `IsGarlingIrreducible` predicate. -/
theorem isGarlingSeparablePoly_iff_garlingIrreducible {K : Type u} [Field K] (f : K[X]) :
    IsGarlingSeparablePoly f ↔
      ∀ g : K[X], IsGarlingIrreducible g → g ∣ f → IsGarlingSeparableIrreducible g := by
  constructor
  · exact fun h g hg hdvd => h g ((isGarlingIrreducible_iff g).mp hg) hdvd
  · exact fun h g hg hdvd => h g ((isGarlingIrreducible_iff g).mpr hg) hdvd

/-- Bridge between `IsGarlingSeparablePoly f` and `Polynomial.Separable` on irreducible divisors. -/
theorem isGarlingSeparablePoly_iff {K : Type u} [Field K] (f : K[X]) :
    IsGarlingSeparablePoly f ↔ ∀ g : K[X], Irreducible g → g ∣ f → g.Separable := by
  refine forall_congr' fun g => imp_congr_right fun hg => forall_congr' fun _ => ?_
  exact isGarlingSeparableIrreducible_iff_separable hg

/-- On an irreducible polynomial `f ∈ K[X]`, `IsGarlingSeparablePoly f`,
`IsGarlingSeparableIrreducible f`, and Mathlib's `f.Separable` all coincide. -/
theorem isGarlingSeparablePoly_of_irreducible_iff {K : Type u} [Field K] {f : K[X]}
    (hf : Irreducible f) :
    IsGarlingSeparablePoly f ↔ f.Separable := by
  rw [isGarlingSeparablePoly_iff]
  constructor
  · exact fun h => h f hf dvd_rfl
  · intro hsep g hg hdvd
    exact (hg.associated_of_dvd hf hdvd).symm.separable hsep

/-- Every unit `u ∈ K[X]` (i.e. non-zero constant `c ∈ Kˣ`) has no irreducible divisors and hence is
separable under `IsGarlingSeparablePoly`. -/
theorem isGarlingSeparablePoly_of_isUnit {K : Type u} [Field K] {f : K[X]} (hu : IsUnit f) :
    IsGarlingSeparablePoly f :=
  fun _ hg hdvd => (hg.not_isUnit (isUnit_of_dvd_unit hdvd hu)).elim

/-- Edge behavior at `f = 0` (`BRIEF.md` Flag 2): since every polynomial divides `0`, `0 ∈ K[X]`
satisfies `IsGarlingSeparablePoly 0` iff every irreducible polynomial in `K[X]` is separable (which
holds iff every polynomial in `K[X]` is separable). -/
theorem isGarlingSeparablePoly_zero_iff (K : Type u) [Field K] :
    IsGarlingSeparablePoly (0 : K[X]) ↔ ∀ f : K[X], IsGarlingSeparablePoly f := by
  constructor
  · intro h0 f g hg _
    exact h0 g hg (dvd_zero g)
  · exact fun hall => hall 0

/-- Exact relationship between Mathlib's `Polynomial.Separable` and Garling's §10.1
`IsGarlingSeparablePoly` (`BRIEF.md` Flag 2): `f.Separable` holds iff `f ≠ 0`, `Squarefree f`, and
`IsGarlingSeparablePoly f`. -/
theorem mathlib_separable_iff_squarefree_and_isGarlingSeparablePoly {K : Type u} [Field K]
    (f : K[X]) :
    f.Separable ↔ f ≠ 0 ∧ Squarefree f ∧ IsGarlingSeparablePoly f := by
  rw [isGarlingSeparablePoly_iff]
  constructor
  · intro hsep
    exact ⟨hsep.ne_zero, hsep.squarefree, fun _ _ hdvd => hsep.of_dvd hdvd⟩
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

/-- Concrete witness for `BRIEF.md` Flag 2: `(x - 1)^2 ∈ ℚ[X]` is separable in Garling's §10.1
sense (`IsGarlingSeparablePoly`) because its irreducible divisors are associates of `x - 1`, whereas
it is **not** separable in Mathlib's squarefree sense (`¬ ((X - 1 : ℚ[X]) ^ 2).Separable`). -/
theorem repeated_linear_factor_garlingSeparable_not_mathlibSeparable :
    IsGarlingSeparablePoly ((Polynomial.X - 1 : ℚ[X]) ^ 2) ∧
      ¬ ((Polynomial.X - 1 : ℚ[X]) ^ 2).Separable := by
  refine ⟨?_, ?_⟩
  · rw [isGarlingSeparablePoly_iff]
    intro g hg _
    exact hg.separable
  · intro hsep
    have hnu : ¬ IsUnit (Polynomial.X - 1 : ℚ[X]) := by
      intro hu
      have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hd1 : (Polynomial.X - 1 : ℚ[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C 1
      omega
    have h1 := (hsep.of_pow hnu (by decide : (2 : ℕ) ≠ 0)).2
    omega

/-- Garling's prose definition that an element `α ∈ L` is *separable (over `K`)* (§10.1, printed
p. 82 / PDF p. 90):
*"We say that `α` is separable (over `K`) if it is algebraic over `K` and its minimal polynomial
over `K` is separable."* -/
def IsGarlingSeparableElement (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : L) : Prop :=
  IsGarlingAlgebraic K α ∧ IsGarlingSeparablePoly (minpoly K α)

/-- Exact equivalence between `IsGarlingSeparableElement K α` (§10.1, p. 82) and Mathlib's
`IsSeparable K α`. -/
theorem isGarlingSeparableElement_iff (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : L) :
    IsGarlingSeparableElement K α ↔ IsSeparable K α := by
  constructor
  · rintro ⟨halg, hsep⟩
    have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp halg
    exact (isGarlingSeparablePoly_of_irreducible_iff (minpoly.irreducible hint)).mp hsep
  · intro hsep
    have hint : IsIntegral K α := hsep.isIntegral
    exact ⟨(isGarlingAlgebraic_iff_isIntegral K α).mpr hint,
      (isGarlingSeparablePoly_of_irreducible_iff (minpoly.irreducible hint)).mpr hsep⟩

/-- Garling's prose definition that an extension `L : K` is *separable* (§10.1, printed p. 82 /
PDF p. 90):
*"...and say that `L : K` is separable if each `α` in `L` is separable over `K`."* -/
def IsGarlingSeparableExtension (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ α : L, IsGarlingSeparableElement K α

/-- Extension-triple formulation of a *separable* extension `(i, K, L)` (§4.2, p. 40; §10.1, p. 82). -/
def IsGarlingSeparableExtensionTriple {K : Type u} {L : Type v} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : Prop :=
  letI : Algebra K L := ext.hom.toAlgebra
  IsGarlingSeparableExtension K L

/-- Exact equivalence between `IsGarlingSeparableExtension K L` (§10.1, p. 82) and Mathlib's
`Algebra.IsSeparable K L`. -/
theorem isGarlingSeparableExtension_iff (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    IsGarlingSeparableExtension K L ↔ Algebra.IsSeparable K L := by
  rw [Algebra.isSeparable_def]
  exact forall_congr' fun α => isGarlingSeparableElement_iff K α

/-- Core minimal-polynomial divisibility step from the proof of `Theorem 10.1` (§10.1, printed p. 82 /
PDF p. 90), proved directly via `Theorem 7.3` (`theorem_7_3_natDegree`) with zero algebraic closures:
in any tower `K → M → L`, if `α ∈ L` is separable over `K`, then `α` is separable over `M`. -/
theorem isGarlingSeparableElement_tower_top {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] {α : L} (hα : IsGarlingSeparableElement K α) :
    IsGarlingSeparableElement M α := by
  classical
  obtain ⟨halgK, hsep_m₂⟩ := hα
  have hintK : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp halgK
  have hintM : IsIntegral M α := hintK.tower_top
  have halgM : IsGarlingAlgebraic M α := (isGarlingAlgebraic_iff_isIntegral M α).mpr hintM
  let m₁ : M[X] := minpoly M α
  let m₂ : K[X] := minpoly K α
  have hm₁_irr : Irreducible m₁ := minpoly.irreducible hintM
  have hm₂_irr : Irreducible m₂ := minpoly.irreducible hintK
  have hm₂_sep : m₂.Separable :=
    (isGarlingSeparablePoly_of_irreducible_iff hm₂_irr).mp hsep_m₂
  have hm₂M_eval : Polynomial.aeval α (m₂.map (algebraMap K M)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact minpoly.aeval K α
  have hdvd : m₁ ∣ m₂.map (algebraMap K M) := minpoly.dvd M α hm₂M_eval
  -- Construct a splitting field extension `N : M` for `m₂` viewed in `M[x]` via `Theorem 7.3`.
  obtain ⟨N, instFN, instAMN, hsfN, _⟩ := theorem_7_3_natDegree (m₂.map (algebraMap K M))
  let _ : Field N := instFN
  let _ : Algebra M N := instAMN
  have hm₂N_sep : ((m₂.map (algebraMap K M)).map (algebraMap M N)).Separable := by
    rw [Polynomial.map_map]
    exact (Polynomial.separable_map ((algebraMap M N).comp (algebraMap K M))).mpr hm₂_sep
  have hdvdN : m₁.map (algebraMap M N) ∣ (m₂.map (algebraMap K M)).map (algebraMap M N) :=
    Polynomial.map_dvd (algebraMap M N) hdvd
  have hm₁N_sep : (m₁.map (algebraMap M N)).Separable := hm₂N_sep.of_dvd hdvdN
  have hm₁_sep : m₁.Separable := (Polynomial.separable_map (algebraMap M N)).mp hm₁N_sep
  exact ⟨halgM, (isGarlingSeparablePoly_of_irreducible_iff hm₁_irr).mpr hm₁_sep⟩

/-- Scalar-tower form of **Theorem 10.1** (§10.1, printed p. 82 / PDF p. 90):
for any tower `K → M → L`, if `L : K` is separable, then `L : M` and `M : K` are separable. -/
theorem theorem_10_1_tower {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (hsep : IsGarlingSeparableExtension K L) :
    IsGarlingSeparableExtension M L ∧ IsGarlingSeparableExtension K M := by
  refine ⟨fun α => isGarlingSeparableElement_tower_top (hsep α), fun β => ?_⟩
  have hβL : IsGarlingSeparableElement K (algebraMap M L β) := hsep (algebraMap M L β)
  have hmin : minpoly K (algebraMap M L β) = minpoly K β :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom K M L) (algebraMap M L).injective β
  obtain ⟨⟨p, hp0, hpeval⟩, hsep_min⟩ := hβL
  refine ⟨⟨p, hp0, ?_⟩, hmin ▸ hsep_min⟩
  apply (algebraMap M L).injective
  rw [map_zero]
  have h1 : algebraMap M L (Polynomial.aeval β p) = Polynomial.aeval (algebraMap M L β) p := by
    simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K M L) β p).symm
  exact h1.trans hpeval

/-- **Theorem 10.1** (§10.1, printed p. 82 / PDF p. 90):
*"Suppose that `L : K` is separable and that `M` is an intermediate field. Then `L : M` and `M : K`
are separable."* -/
theorem theorem_10_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hsep : IsGarlingSeparableExtension K L) (M : IntermediateField K L) :
    IsGarlingSeparableExtension M L ∧ IsGarlingSeparableExtension K M :=
  theorem_10_1_tower hsep

/-! ## §10.2 Monomorphisms and automorphisms (printed pp. 83–84, PDF pp. 91–92) -/

/-- Helper: transporting separability of an irreducible polynomial along a field monomorphism
`j : K →+* L` (`α` is separable over `K` iff `j(m_α)` is separable; §10.2, printed p. 83). -/
private theorem isGarlingSeparableElement_iff_map_minpoly_separable
    {K : Type u} {Kα : Type v} {L : Type w} [Field K] [Field Kα] [Algebra K Kα] [Field L]
    {α : Kα} (_hα : IsGarlingAlgebraic K α) (j : K →+* L) :
    IsGarlingSeparableElement K α ↔ (garlingMapPoly j (minpoly K α)).Separable := by
  rw [isGarlingSeparableElement_iff, IsSeparable, garlingMapPoly_apply, Polynomial.separable_map]

/-- **Theorem 10.2** (§10.2, printed p. 83 / PDF p. 91):
*"Suppose that `K(α) : K` is a simple algebraic extension of degree `d`. Suppose that `j : K → L` is
a monomorphism. If `α` is separable over `K` and if `j(m_α)` splits over `L` then there are exactly
`d` monomorphisms from `K(α)` to `L` extending `j`; otherwise there are fewer than `d` such
monomorphisms."*

Proved directly following Garling's proof on p. 83 via `Corollary 2` to `Theorem 7.4`
(`corollary_2_to_theorem_7_4_finset`) and `Theorem 4.4`. -/
theorem theorem_10_2 {K : Type u} {Kα : Type v} {L : Type w}
    [Field K] [Field Kα] [Algebra K Kα] [Field L]
    {α : Kα} (hadj : IntermediateField.adjoin K ({α} : Set Kα) = ⊤)
    (hα : IsGarlingAlgebraic K α) {d : ℕ} (hd : extDegree K Kα = (d : ℕ∞))
    {j : K →+* L} (hj : IsRingMonomorphism j) :
    let S := {σ : Kα →+* L | IsRingMonomorphism σ ∧ ∀ k : K, σ (algebraMap K Kα k) = j k}
    ((IsGarlingSeparableElement K α ∧ GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S = (d : ℕ∞) ∧ Nat.card S = d) ∧
    (¬ (IsGarlingSeparableElement K α ∧ GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S < (d : ℕ∞) ∧ Nat.card S < d) := by
  classical
  let _ : DecidableEq L := Classical.decEq L
  intro S
  have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα
  -- By Theorem 4.4, `d = [K(α) : K] = deg m_α = deg j(m_α)`.
  have hd_deg : (minpoly K α).natDegree = d := by
    have hequiv : IntermediateField.adjoin K ({α} : Set Kα) ≃ₐ[K] Kα :=
      (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
    have hfin : IsFiniteExtension K Kα := by
      unfold IsFiniteExtension
      rw [hd]
      exact ENat.natCast_lt_top d
    have _ : Module.Finite K Kα := (isFiniteExtension_iff_moduleFinite K Kα).mp hfin
    have hd_fr : Module.finrank K Kα = d := by
      have h1 := extDegree_eq_finrank K Kα
      rw [hd] at h1
      exact Nat.cast_injective h1.symm
    rw [← IntermediateField.adjoin.finrank hint, LinearEquiv.finrank_eq hequiv.toLinearEquiv, hd_fr]
  let pL : L[X] := garlingMapPoly j (minpoly K α)
  have hpL_monic : pL.Monic := (minpoly.monic hint).map j
  have hpL_deg : pL.natDegree = d :=
    (Polynomial.natDegree_map_eq_of_injective hj (minpoly K α)).trans hd_deg
  let r : ℕ := pL.roots.toFinset.card
  obtain ⟨hord_r, hnat_r⟩ := corollary_2_to_theorem_7_4_finset hadj hα hj (r := r) rfl
  have hnat_S : Nat.card S = r := hnat_r
  have hr_le_roots : r ≤ pL.roots.card := Multiset.toFinset_card_le pL.roots
  have hroots_le_d : pL.roots.card ≤ d := hpL_deg ▸ Polynomial.card_roots' pL
  have hr_le_d : r ≤ d := hr_le_roots.trans hroots_le_d
  -- Equivalence `r = d ↔ (α separable over K ∧ j(m_α) splits over L)`.
  have hr_eq_d_iff :
      r = d ↔
        (IsGarlingSeparableElement K α ∧ GarlingSplitsOver L L pL) := by
    rw [isGarlingSeparableElement_iff_map_minpoly_separable hα j,
      (garlingSplitsOver_mapPoly_iff j (minpoly K α)).1]
    change r = d ↔ (pL.Separable ∧ pL.Splits)
    constructor
    · intro hrd
      have hcard_eq_d : pL.roots.card = d := by omega
      have hnodup : pL.roots.Nodup :=
        Multiset.toFinset_card_eq_card_iff_nodup.mp (hrd.trans hcard_eq_d.symm)
      have hsp : pL.Splits :=
        Polynomial.splits_iff_card_roots.mpr (hcard_eq_d.trans hpL_deg.symm)
      have heq := Polynomial.Splits.eq_prod_roots hsp
      have hsep_prod :
          ((pL.roots.map fun a : L => Polynomial.X - Polynomial.C a).prod).Separable := by
        have hfin_prod :
            (∏ a ∈ pL.roots.toFinset, (Polynomial.X - Polynomial.C a)) =
              (pL.roots.map fun a : L => Polynomial.X - Polynomial.C a).prod := by
          rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
        rw [← hfin_prod]
        refine Polynomial.separable_prod' (fun x _ y _ hxy => ?_)
          (fun _ _ => Polynomial.separable_X_sub_C)
        exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxy
      have hsep : pL.Separable := by
        rw [heq, hpL_monic.leadingCoeff, map_one, one_mul]
        exact hsep_prod
      exact ⟨hsep, hsp⟩
    · rintro ⟨hsep, hsp⟩
      have hnodup : pL.roots.Nodup := Polynomial.nodup_roots hsep
      have hcard_d : pL.roots.card = d := hsp.natDegree_eq_card_roots.symm.trans hpL_deg
      exact (Multiset.toFinset_card_of_nodup hnodup).trans hcard_d
  refine ⟨fun hcond => ?_, fun hnot => ?_⟩
  · have hrd : r = d := hr_eq_d_iff.mpr hcond
    exact ⟨hord_r.trans (by rw [hrd]), hnat_S.trans hrd⟩
  · have hr_ne : r ≠ d := fun hrd => hnot (hr_eq_d_iff.mp hrd)
    have hr_lt : r < d := Nat.lt_of_le_of_ne hr_le_d hr_ne
    refine ⟨?_, ?_⟩
    · rw [hord_r]
      exact mod_cast hr_lt
    · rw [hnat_S]
      exact hr_lt

/-- Subfield `IntermediateField.adjoin K {α}` companion to **Theorem 10.2** (§10.2, p. 83). -/
theorem theorem_10_2_adjoin {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Algebra K M] [Field L]
    {α : M} (hα : IsGarlingAlgebraic K α) {d : ℕ}
    (hd : extDegree K (IntermediateField.adjoin K ({α} : Set M)) = (d : ℕ∞))
    {j : K →+* L} (hj : IsRingMonomorphism j) :
    let Kα := IntermediateField.adjoin K ({α} : Set M)
    let S := {σ : Kα →+* L | IsRingMonomorphism σ ∧ ∀ k : K, σ (algebraMap K Kα k) = j k}
    ((IsGarlingSeparableElement K α ∧ GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S = (d : ℕ∞) ∧ Nat.card S = d) ∧
    (¬ (IsGarlingSeparableElement K α ∧ GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S < (d : ℕ∞) ∧ Nat.card S < d) := by
  let F : IntermediateField K M := IntermediateField.adjoin K ({α} : Set M)
  let gen : F := IntermediateField.AdjoinSimple.gen K α
  have hadj_gen : IntermediateField.adjoin K ({gen} : Set F) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K M := (IntermediateField.adjoin K ({gen} : Set F)).map F.val
    have hα_mem : α ∈ L0 := ⟨gen, IntermediateField.mem_adjoin_simple_self K gen, rfl⟩
    obtain ⟨y, hy, hyx⟩ :=
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα_mem)) x.2
    exact (F.val.injective hyx) ▸ hy
  have hmin : minpoly K gen = minpoly K α :=
    (minpoly.algHom_eq F.val F.val.injective gen).symm
  have hgen_alg : IsGarlingAlgebraic K gen := by
    obtain ⟨p, hp0, hpeval⟩ := hα
    exact ⟨p, hp0, Subtype.ext ((Polynomial.aeval_algHom_apply F.val gen p).symm.trans hpeval)⟩
  have hsep_iff : IsGarlingSeparableElement K gen ↔ IsGarlingSeparableElement K α := by
    unfold IsGarlingSeparableElement
    rw [hmin]
    exact ⟨fun ⟨_, hs⟩ => ⟨hα, hs⟩, fun ⟨_, hs⟩ => ⟨hgen_alg, hs⟩⟩
  have h := theorem_10_2 hadj_gen hgen_alg hd hj
  simpa only [hmin, hsep_iff] using h

/-- Fiber bijection along a field tower `K → M → K'` for monomorphisms into `L` extending
`j : K →+* L`: restricting `σ : K' →+* L` to `M` identifies `j`-extending monomorphisms `K' →+* L`
with dependent pairs `(k, σ)` where `k : M →+* L` extends `j` and `σ : K' →+* L` extends `k`. -/
private noncomputable def extendingMonomorphismSigmaEquiv
    {K : Type*} {M : Type*} {K' : Type*} {L : Type*}
    [Field K] [Field M] [Field K'] [Field L]
    [Algebra K M] [Algebra M K'] [Algebra K K'] [IsScalarTower K M K']
    (j : K →+* L) :
    {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x} ≃
      Σ k : {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x},
        {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m} where
  toFun σ :=
    ⟨⟨σ.1.comp (algebraMap M K'),
      σ.2.1.comp (algebraMap M K').injective,
      fun x => by
        change σ.1 (algebraMap M K' (algebraMap K M x)) = j x
        rw [← IsScalarTower.algebraMap_apply K M K' x]
        exact σ.2.2 x⟩,
     ⟨σ.1, σ.2.1, fun _ => rfl⟩⟩
  invFun p :=
    ⟨p.2.1, p.2.2.1, fun x => by
      rw [IsScalarTower.algebraMap_apply K M K' x, p.2.2.2 (algebraMap K M x)]
      exact p.1.2.2 x⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨k, hk1, hk2⟩, ⟨σ, hσ1, hσ2⟩⟩
    have hk_eq : σ.comp (algebraMap M K') = k := RingHom.ext hσ2
    subst hk_eq
    rfl

/-- Reusable finite-sigma cardinality helper for monomorphisms along a tower `K → M → K'`. -/
private theorem card_extendingMonomorphisms_tower
    {K : Type*} {M : Type*} {K' : Type*} {L : Type*}
    [Field K] [Field M] [Field K'] [Field L]
    [Algebra K M] [Algebra M K'] [Algebra K K'] [IsScalarTower K M K']
    (j : K →+* L)
    (hSM_fin : Finite {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x})
    (hfib_fin : ∀ k : {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x},
      Finite {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m}) :
    let SM := {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x}
    let S := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x}
    Finite S ∧
    ((∀ k : SM, Nat.card {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m} = d₂) →
      Nat.card S = Nat.card SM * d₂) ∧
    ((∀ k : SM, Nat.card {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m} ≤ d₂) →
      Nat.card S ≤ Nat.card SM * d₂) := by
  classical
  intro SM S
  let eSigma := extendingMonomorphismSigmaEquiv (K := K) (M := M) (K' := K') (L := L) j
  let _ : Fintype SM := Fintype.ofFinite SM
  let _ : ∀ k : SM, Fintype {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m} :=
    fun _ => Fintype.ofFinite _
  have hS_fin : Finite S := Finite.of_equiv _ eSigma.symm
  refine ⟨hS_fin, fun heq => ?_, fun hle => ?_⟩
  · rw [Nat.card_congr eSigma, Nat.card_eq_fintype_card, Fintype.card_sigma]
    have h1 : ∀ k : SM,
        Fintype.card {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m} = d₂ := by
      intro k
      rw [← Nat.card_eq_fintype_card]
      exact heq k
    simp_rw [h1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
    rfl
  · rw [Nat.card_congr eSigma, Nat.card_eq_fintype_card, Fintype.card_sigma]
    have h1 :
        (∑ k : SM, Fintype.card {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m}) ≤
          ∑ _k : SM, d₂ := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Nat.card_eq_fintype_card]
      exact hle k
    simpa [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul] using h1

/-- Same-universe (`K, K' : Type v`) strong induction for **Theorem 10.3** (§10.2, printed p. 83 /
PDF p. 91), following Garling's induction on `d = [K' : K]` word-for-word (`Theorem 10.2` +
`Theorem 10.1` + `Theorem 4.2`). -/
private theorem theorem_10_3_sameUniv :
    ∀ (d : ℕ) {K K' : Type v} {L : Type w}
      [Field K] [Field K'] [Algebra K K'] [Field L]
      (_hfin : IsFiniteExtension K K') (_hd : extDegree K K' = (d : ℕ∞))
      {j : K →+* L} (_hj : IsRingMonomorphism j),
      let S := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x}
      Finite S ∧
      ((IsGarlingSeparableExtension K K' ∧
          ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
        setOrder S = (d : ℕ∞) ∧ Nat.card S = d) ∧
      (¬ (IsGarlingSeparableExtension K K' ∧
          ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
        setOrder S < (d : ℕ∞) ∧ Nat.card S < d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro K K' L _ _ _ _ hfin hd j hj
    classical
    have _ : Module.Finite K K' := (isFiniteExtension_iff_moduleFinite K K').mp hfin
    have hd_fr : Module.finrank K K' = d := by
      have h1 := extDegree_eq_finrank K K'
      rw [hd] at h1
      exact Nat.cast_injective h1.symm
    have hd_pos : 0 < d := hd_fr ▸ Module.finrank_pos
    let S := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x}
    by_cases hd1 : d = 1
    · -- Base case `d = 1`: `K' = K` (`⊥ = ⊤`), the conditions hold automatically, and `|S| = 1`.
      subst hd1
      have hbot_sub_top : (⊥ : IntermediateField K K').toSubmodule = ⊤ :=
        Submodule.eq_top_of_finrank_eq
          ((IntermediateField.finrank_bot (F := K) (E := K')).trans hd_fr.symm)
      have hsurj : Function.Surjective (algebraMap K K') := by
        intro y
        have hy : y ∈ (⊥ : IntermediateField K K') :=
          SetLike.ext_iff.mp hbot_sub_top y |>.mpr Submodule.mem_top
        exact IntermediateField.mem_bot.mp hy
      let eKK' : K ≃+* K' := RingEquiv.ofBijective (algebraMap K K')
        ⟨(algebraMap K K').injective, hsurj⟩
      let σ₀ : K' →+* L := j.comp eKK'.symm.toRingHom
      have hσ₀_mem : σ₀ ∈ S := by
        refine ⟨hj.comp eKK'.symm.injective, fun x => ?_⟩
        change j (eKK'.symm (eKK' x)) = j x
        rw [eKK'.symm_apply_apply]
      have hS_uniq : ∀ σ : S, σ = ⟨σ₀, hσ₀_mem⟩ := by
        rintro ⟨σ, _, hσk⟩
        apply Subtype.ext
        ext y
        obtain ⟨x, rfl⟩ := hsurj y
        exact (hσk x).trans (hσ₀_mem.2 x).symm
      have _ : Subsingleton S := ⟨fun a b => (hS_uniq a).trans (hS_uniq b).symm⟩
      have _ : Nonempty S := ⟨⟨σ₀, hσ₀_mem⟩⟩
      have hS_fin : Finite S := Finite.of_subsingleton
      have hS_nat : Nat.card S = 1 := Nat.card_unique
      have hS_ord : setOrder S = (1 : ℕ∞) := by
        change ENat.card S = 1
        rw [ENat.card_eq_coe_natCard, hS_nat, Nat.cast_one]
      have hcond_true :
          IsGarlingSeparableExtension K K' ∧
            ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α)) := by
        refine ⟨fun α => ?_, fun α => ?_⟩
        · obtain ⟨x, rfl⟩ := hsurj α
          exact (isGarlingSeparableElement_iff K _).mpr (isSeparable_algebraMap x)
        · obtain ⟨x, rfl⟩ := hsurj α
          rw [(garlingSplitsOver_mapPoly_iff j (minpoly K (algebraMap K K' x))).1,
            minpoly.eq_X_sub_C_of_algebraMap_inj x (algebraMap K K').injective,
            Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
          exact Polynomial.Splits.X_sub_C (j x)
      exact ⟨hS_fin, fun _ => ⟨hS_ord, hS_nat⟩, fun hnot => (hnot hcond_true).elim⟩
    · -- Inductive step `d > 1`.
      have hd_gt1 : 1 < d := by omega
      have hexists_not_bot : ∃ α : K', α ∉ (⊥ : IntermediateField K K') := by
        by_contra hall
        push Not at hall
        have hbot_top : (⊥ : IntermediateField K K') = ⊤ := eq_top_iff.mpr fun x _ => hall x
        have h1 : Module.finrank K K' = 1 := by
          rw [← IntermediateField.finrank_bot (F := K) (E := K')]
          exact LinearEquiv.finrank_eq
            ((IntermediateField.equivOfEq hbot_top).trans IntermediateField.topEquiv).toLinearEquiv.symm
        omega
      by_cases hcond :
          IsGarlingSeparableExtension K K' ∧
            ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))
      · -- Case 1 (printed p. 83): the conditions are satisfied.
        obtain ⟨hsep, hsplits⟩ := hcond
        obtain ⟨α, hα_not_bot⟩ := hexists_not_bot
        let M : IntermediateField K K' := IntermediateField.adjoin K ({α} : Set K')
        have hα_alg : IsGarlingAlgebraic K α := (hsep α).1
        let d₁ : ℕ := Module.finrank K M
        let d₂ : ℕ := Module.finrank M K'
        have htower_fr : d₁ * d₂ = d := (Module.finrank_mul_finrank K M K').trans hd_fr
        have hd₁_gt1 : 1 < d₁ := by
          by_contra hle
          have hd₁_pos : 0 < d₁ := Module.finrank_pos
          have hd₁_eq1 : d₁ = 1 := by omega
          have hbot_eq_M : (⊥ : IntermediateField K K').toSubmodule = M.toSubmodule :=
            Submodule.eq_of_le_of_finrank_eq
              (fun x hx => (bot_le : (⊥ : IntermediateField K K') ≤ M) hx)
              ((IntermediateField.finrank_bot (F := K) (E := K')).trans hd₁_eq1.symm)
          have hαM : α ∈ M := IntermediateField.mem_adjoin_simple_self K α
          have hα_bot : α ∈ (⊥ : IntermediateField K K') :=
            SetLike.ext_iff.mp hbot_eq_M.symm α |>.mp hαM
          exact hα_not_bot hα_bot
        have hd₂_pos : 0 < d₂ := Module.finrank_pos
        have hd₂_lt : d₂ < d := by nlinarith
        have hfin_MK' : IsFiniteExtension M K' :=
          (isFiniteExtension_iff_moduleFinite M K').mpr inferInstance
        have hd₁_ext : extDegree K M = (d₁ : ℕ∞) := extDegree_eq_finrank K M
        have hd₂_ext : extDegree M K' = (d₂ : ℕ∞) := extDegree_eq_finrank M K'
        -- By Theorem 10.2, `j` has `d₁` extensions `k : M →+* L`.
        have h102 := (theorem_10_2_adjoin hα_alg hd₁_ext hj).1 ⟨hsep α, hsplits α⟩
        let SM := {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x}
        have hSM_fin : Finite SM := by
          by_contra hinf
          have _ : Infinite SM := not_finite_iff_infinite.mp hinf
          have htop : setOrder SM = ⊤ := ENat.card_eq_top_of_infinite
          exact ENat.natCast_ne_top d₁ (h102.1.symm.trans htop)
        -- By Theorem 10.1, `K' : M` is separable, and for each `k ∈ SM` and `β ∈ K'`, `k(n_β)` splits over `L`.
        have hsep_MK' : IsGarlingSeparableExtension M K' := (theorem_10_1 hsep M).1
        have hfiber :
            ∀ k : SM,
              let Sk := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m}
              Finite Sk ∧ Nat.card Sk = d₂ := by
          intro k
          have hsplits_k : ∀ β : K', GarlingSplitsOver L L (garlingMapPoly k.1 (minpoly M β)) := by
            intro β
            let mβ : K[X] := minpoly K β
            let nβ : M[X] := minpoly M β
            have hmβ_eval : Polynomial.aeval β (mβ.map (algebraMap K M)) = 0 := by
              rw [Polynomial.aeval_map_algebraMap]
              exact minpoly.aeval K β
            have hdvd : nβ ∣ mβ.map (algebraMap K M) := minpoly.dvd M β hmβ_eval
            have hdvdL : nβ.map k.1 ∣ (mβ.map (algebraMap K M)).map k.1 :=
              Polynomial.map_dvd k.1 hdvd
            have hcomp : k.1.comp (algebraMap K M) = j := RingHom.ext k.2.2
            have hmap_eq : (mβ.map (algebraMap K M)).map k.1 = mβ.map j := by
              rw [Polynomial.map_map, hcomp]
            rw [hmap_eq] at hdvdL
            have hmβ_sp : (mβ.map j).Splits :=
              (garlingSplitsOver_mapPoly_iff j mβ).1.mp (hsplits β)
            have hmβ_ne0 : mβ.map j ≠ 0 :=
              ((minpoly.monic ((isGarlingAlgebraic_iff_isIntegral K β).mp (hsep β).1)).map j).ne_zero
            rw [(garlingSplitsOver_mapPoly_iff k.1 nβ).1]
            exact Polynomial.Splits.of_dvd hmβ_sp hmβ_ne0 hdvdL
          have hih := ih d₂ hd₂_lt hfin_MK' hd₂_ext k.2.1
          exact ⟨hih.1, (hih.2.1 ⟨hsep_MK', hsplits_k⟩).2⟩
        obtain ⟨hS_fin, hS_mul, _⟩ := card_extendingMonomorphisms_tower (K := K) (M := M) (K' := K')
          (L := L) (d₂ := d₂) j hSM_fin (fun k => (hfiber k).1)
        have hcard_S : Nat.card S = d := by
          rw [hS_mul (fun k => (hfiber k).2), h102.2, htower_fr]
        have hord_S : setOrder S = (d : ℕ∞) := by
          change ENat.card S = (d : ℕ∞)
          rw [ENat.card_eq_coe_natCard, hcard_S]
        exact ⟨hS_fin, fun _ => ⟨hord_S, hcard_S⟩, fun hnot => (hnot ⟨hsep, hsplits⟩).elim⟩
      · -- Case 2 (printed p. 83): the conditions are not satisfied.
        have hexists_bad :
            ∃ α : K', ¬ (IsGarlingSeparableElement K α ∧
              GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) := by
          by_contra hall_good
          push Not at hall_good
          exact hcond ⟨fun α => (hall_good α).1, fun α => (hall_good α).2⟩
        obtain ⟨α, hα_bad⟩ := hexists_bad
        have hα_alg : IsGarlingAlgebraic K α :=
          (isGarlingAlgebraic_iff_isIntegral K α).mpr (Algebra.IsIntegral.isIntegral α)
        have hα_not_bot : α ∉ (⊥ : IntermediateField K K') := by
          intro hαb
          obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp hαb
          subst hx
          apply hα_bad
          refine ⟨(isGarlingSeparableElement_iff K _).mpr (isSeparable_algebraMap x), ?_⟩
          have hmin_x : minpoly K (algebraMap K K' x) = Polynomial.X - Polynomial.C x :=
            minpoly.eq_X_sub_C_of_algebraMap_inj x (algebraMap K K').injective
          rw [(garlingSplitsOver_mapPoly_iff j (minpoly K (algebraMap K K' x))).1, hmin_x,
            Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
          exact Polynomial.Splits.X_sub_C (j x)
        let M : IntermediateField K K' := IntermediateField.adjoin K ({α} : Set K')
        let d₁ : ℕ := Module.finrank K M
        let d₂ : ℕ := Module.finrank M K'
        have htower_fr : d₁ * d₂ = d := (Module.finrank_mul_finrank K M K').trans hd_fr
        have hd₁_gt1 : 1 < d₁ := by
          by_contra hle
          have hd₁_pos : 0 < d₁ := Module.finrank_pos
          have hd₁_eq1 : d₁ = 1 := by omega
          have hbot_eq_M : (⊥ : IntermediateField K K').toSubmodule = M.toSubmodule :=
            Submodule.eq_of_le_of_finrank_eq
              (fun x hx => (bot_le : (⊥ : IntermediateField K K') ≤ M) hx)
              ((IntermediateField.finrank_bot (F := K) (E := K')).trans hd₁_eq1.symm)
          exact hα_not_bot (SetLike.ext_iff.mp hbot_eq_M.symm α |>.mp
            (IntermediateField.mem_adjoin_simple_self K α))
        have hd₂_pos : 0 < d₂ := Module.finrank_pos
        have hd₂_lt : d₂ < d := by nlinarith
        have hfin_MK' : IsFiniteExtension M K' :=
          (isFiniteExtension_iff_moduleFinite M K').mpr inferInstance
        have hd₁_ext : extDegree K M = (d₁ : ℕ∞) := extDegree_eq_finrank K M
        have hd₂_ext : extDegree M K' = (d₂ : ℕ∞) := extDegree_eq_finrank M K'
        have h102_lt := (theorem_10_2_adjoin hα_alg hd₁_ext hj).2 hα_bad
        let SM := {k : M →+* L | IsRingMonomorphism k ∧ ∀ x : K, k (algebraMap K M x) = j x}
        have hSM_fin : Finite SM := by
          by_contra hinf
          have _ : Infinite SM := not_finite_iff_infinite.mp hinf
          have htop : setOrder SM = ⊤ := ENat.card_eq_top_of_infinite
          have hlt := h102_lt.1
          rw [htop] at hlt
          exact not_top_lt hlt
        have hfiber_le :
            ∀ k : SM,
              let Sk := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ m : M, σ (algebraMap M K' m) = k.1 m}
              Finite Sk ∧ Nat.card Sk ≤ d₂ := by
          intro k
          have hih := ih d₂ hd₂_lt hfin_MK' hd₂_ext k.2.1
          refine ⟨hih.1, ?_⟩
          by_cases hk_cond :
              IsGarlingSeparableExtension M K' ∧
                ∀ β : K', GarlingSplitsOver L L (garlingMapPoly k.1 (minpoly M β))
          · exact le_of_eq (hih.2.1 hk_cond).2
          · exact le_of_lt (hih.2.2 hk_cond).2
        obtain ⟨hS_fin, _, hS_le⟩ := card_extendingMonomorphisms_tower (K := K) (M := M) (K' := K')
          (L := L) (d₂ := d₂) j hSM_fin (fun k => (hfiber_le k).1)
        have hcard_le : Nat.card S ≤ Nat.card SM * d₂ := hS_le fun k => (hfiber_le k).2
        have hmul_lt : Nat.card SM * d₂ < d₁ * d₂ :=
          Nat.mul_lt_mul_of_pos_right h102_lt.2 hd₂_pos
        have hcard_lt : Nat.card S < d := by omega
        have hord_lt : setOrder S < (d : ℕ∞) := by
          change ENat.card S < (d : ℕ∞)
          rw [ENat.card_eq_coe_natCard]
          exact mod_cast hcard_lt
        exact ⟨hS_fin, fun hc => (hcond hc).elim, fun _ => ⟨hord_lt, hcard_lt⟩⟩

/-- **Theorem 10.3** (§10.2, printed p. 83 / PDF p. 91):
*"Suppose that `K' : K` is a finite extension of degree `d`, and that `j : K → L` is a monomorphism.
If `K' : K` is separable and `j(m_α)` splits over `L` for each `α` in `K'` then there are exactly
`d` monomorphisms from `K'` to `L` extending `j`; otherwise, there are fewer than `d` such
monomorphisms."* -/
theorem theorem_10_3 {K : Type u} {K' : Type v} {L : Type w}
    [Field K] [Field K'] [Algebra K K'] [Field L]
    (hfin : IsFiniteExtension K K') {d : ℕ} (hd : extDegree K K' = (d : ℕ∞))
    {j : K →+* L} (hj : IsRingMonomorphism j) :
    let S := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x}
    ((IsGarlingSeparableExtension K K' ∧
        ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S = (d : ℕ∞) ∧ Nat.card S = d) ∧
    (¬ (IsGarlingSeparableExtension K K' ∧
        ∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) →
      setOrder S < (d : ℕ∞) ∧ Nat.card S < d) := by
  -- Transport `K : Type u` to `B = (⊥ : IntermediateField K K') : Type v` via `botEquiv` so
  -- `theorem_10_3_sameUniv` applies across arbitrary universes `u, v, w`.
  intro S
  have _ : Module.Finite K K' := (isFiniteExtension_iff_moduleFinite K K').mp hfin
  let B : IntermediateField K K' := ⊥
  let e : K ≃ₐ[K] B := (IntermediateField.botEquiv K K').symm
  let jB : B →+* L := j.comp e.symm.toRingHom
  have hjB : IsRingMonomorphism jB := hj.comp e.symm.injective
  have _ : Module.Finite B K' := Module.Finite.of_restrictScalars_finite K B K'
  have hfin_BK' : IsFiniteExtension B K' :=
    (isFiniteExtension_iff_moduleFinite B K').mpr inferInstance
  have hd_fr_K : Module.finrank K K' = d := by
    have h1 := extDegree_eq_finrank K K'
    rw [hd] at h1
    exact Nat.cast_injective h1.symm
  have hd_fr_B : Module.finrank B K' = d := by
    have hmul := Module.finrank_mul_finrank K B K'
    rw [IntermediateField.finrank_bot (F := K) (E := K'), one_mul, hd_fr_K] at hmul
    exact hmul
  have hd_B : extDegree B K' = (d : ℕ∞) :=
    (extDegree_eq_finrank B K').trans (congrArg Nat.cast hd_fr_B)
  let SB := {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ b : B, σ (algebraMap B K' b) = jB b}
  have hS_eq : S = SB := by
    ext σ
    refine and_congr_right fun _ => ⟨fun h b => ?_, fun h k => ?_⟩
    · obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp b.2
      have hb_eq : b = e k := Subtype.ext hk.symm
      rw [hb_eq]
      change σ (algebraMap K K' k) = j (e.symm (e k))
      rw [e.symm_apply_apply]
      exact h k
    · have hk := h (e k)
      change σ (algebraMap K K' k) = j (e.symm (e k)) at hk
      rwa [e.symm_apply_apply] at hk
  have hmin_map : ∀ α : K', (minpoly K α).map e.toRingHom = minpoly B α := by
    intro α
    have hintK : IsIntegral K α := Algebra.IsIntegral.isIntegral α
    have hmonic : ((minpoly K α).map e.toRingHom).Monic := (minpoly.monic hintK).map e.toRingHom
    have hirr : Irreducible ((minpoly K α).map e.toRingHom) :=
      (minpoly.irreducible hintK).map (Polynomial.mapEquiv e.toRingEquiv)
    have haev : Polynomial.aeval α ((minpoly K α).map e.toRingHom) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap B K').comp e.toRingHom = algebraMap K K' := RingHom.ext fun _ => rfl
      rw [hcomp, ← Polynomial.aeval_def, minpoly.aeval K α]
    exact minpoly.eq_of_irreducible_of_monic hirr haev hmonic
  have hsep_iff : IsGarlingSeparableExtension K K' ↔ IsGarlingSeparableExtension B K' := by
    rw [isGarlingSeparableExtension_iff, isGarlingSeparableExtension_iff,
      Algebra.isSeparable_def, Algebra.isSeparable_def]
    refine forall_congr' fun α => ?_
    rw [IsSeparable, IsSeparable, ← hmin_map α, Polynomial.separable_map]
  have hsp_iff :
      (∀ α : K', GarlingSplitsOver L L (garlingMapPoly j (minpoly K α))) ↔
        (∀ α : K', GarlingSplitsOver L L (garlingMapPoly jB (minpoly B α))) := by
    refine forall_congr' fun α => ?_
    have hmap_eq : garlingMapPoly jB (minpoly B α) = garlingMapPoly j (minpoly K α) := by
      rw [← hmin_map α, garlingMapPoly_apply, garlingMapPoly_apply, Polynomial.map_map]
      congr 1
      ext k
      change j (e.symm (e k)) = j k
      rw [e.symm_apply_apply]
    rw [hmap_eq]
  rw [hS_eq, hsep_iff, hsp_iff]
  exact (theorem_10_3_sameUniv d hfin_BK' hd_B hjB).2

/-- Helper exposing `Finite S` from `theorem_10_3_sameUniv` across arbitrary universes `u, v, w`. -/
private theorem extendingMonomorphisms_finite {K : Type u} {K' : Type v} {L : Type w}
    [Field K] [Field K'] [Algebra K K'] [Field L]
    (hfin : IsFiniteExtension K K') (j : K →+* L) :
    Finite {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x} := by
  have _ : Module.Finite K K' := (isFiniteExtension_iff_moduleFinite K K').mp hfin
  let B : IntermediateField K K' := ⊥
  let e : K ≃ₐ[K] B := (IntermediateField.botEquiv K K').symm
  let jB : B →+* L := j.comp e.symm.toRingHom
  have hjB : IsRingMonomorphism jB := j.injective.comp e.symm.injective
  have _ : Module.Finite B K' := Module.Finite.of_restrictScalars_finite K B K'
  have hfin_BK' : IsFiniteExtension B K' :=
    (isFiniteExtension_iff_moduleFinite B K').mpr inferInstance
  have hB := (theorem_10_3_sameUniv (Module.finrank B K') hfin_BK'
    (extDegree_eq_finrank B K') (j := jB) hjB).1
  have hS_eq :
      {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ x : K, σ (algebraMap K K' x) = j x} =
        {σ : K' →+* L | IsRingMonomorphism σ ∧ ∀ b : B, σ (algebraMap B K' b) = jB b} := by
    ext σ
    refine and_congr_right fun _ => ⟨fun h b => ?_, fun h k => ?_⟩
    · obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp b.2
      have hb_eq : b = e k := Subtype.ext hk.symm
      rw [hb_eq]
      change σ (algebraMap K K' k) = j (e.symm (e k))
      rw [e.symm_apply_apply]
      exact h k
    · have hk := h (e k)
      change σ (algebraMap K K' k) = j (e.symm (e k)) at hk
      rwa [e.symm_apply_apply] at hk
  rwa [hS_eq]

/-- Prefix intermediate field `K_m = K(α₁, …, α_m)` for a tuple `α : Fin r → L` (`0 ≤ m ≤ r`;
`BRIEF.md` Flag 5 & `Corollary 1` proof on printed p. 84):
at `m = 0`, `garlingPrefixField K α 0 = ⊥` (`K₀ = K`); at `m = r`, `garlingPrefixField K α r =
IntermediateField.adjoin K (Set.range α)`. -/
def garlingPrefixField (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {r : ℕ} (α : Fin r → L) (m : ℕ) : IntermediateField K L :=
  IntermediateField.adjoin K (α '' {j : Fin r | (j : ℕ) < m})

@[simp]
theorem garlingPrefixField_zero (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {r : ℕ} (α : Fin r → L) :
    garlingPrefixField K α 0 = ⊥ := by
  unfold garlingPrefixField
  have hempty : {j : Fin r | (j : ℕ) < 0} = ∅ := by ext j; simp
  rw [hempty, Set.image_empty, IntermediateField.adjoin_empty]

theorem garlingPrefixField_full (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {r : ℕ} (α : Fin r → L) :
    garlingPrefixField K α r = IntermediateField.adjoin K (Set.range α) := by
  unfold garlingPrefixField
  have huniv : {j : Fin r | (j : ℕ) < r} = Set.univ := by ext j; simp
  rw [huniv, Set.image_univ]

theorem garlingPrefixField_mono (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    {r : ℕ} (α : Fin r → L) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    garlingPrefixField K α m₁ ≤ garlingPrefixField K α m₂ :=
  IntermediateField.adjoin_le_iff.mpr fun _ hx =>
    IntermediateField.subset_adjoin K _
      (Set.image_mono (fun _ hj => lt_of_lt_of_le hj h) hx)

/-- **Corollary 1** [to Theorem 10.3] (§10.2, printed p. 84 / PDF p. 92):
*"Suppose that `L : K` is finite and that `L = K(α₁, …, α_r)`. If `α_i` is separable over
`K(α₁, …, α_{i-1})` for `1 ≤ i ≤ r`, then `L : K` is separable."*

Proved directly following Garling's normal-closure proof on p. 84 (`Corollary 2` to `Theorem 9.1` +
`Theorem 10.2` + `Theorem 4.2` + `Theorem 10.3`), with zero algebraic closures. -/
theorem corollary_1_to_theorem_10_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) {r : ℕ} (α : Fin r → L)
    (hadj : IntermediateField.adjoin K (Set.range α) = ⊤)
    (hsep_step : ∀ i : Fin r, IsGarlingSeparableElement (garlingPrefixField K α i.val) (α i)) :
    IsGarlingSeparableExtension K L := by
  classical
  obtain ⟨F, instFF, instAKF, instALF, instTower, _, _, hcl⟩ := corollary_2_to_theorem_9_1 hfin
  let _ : Field F := instFF
  let _ : Algebra K F := instAKF
  let _ : Algebra L F := instALF
  have _ : IsScalarTower K L F := instTower
  have hnormKF : IsGarlingNormal K F := hcl.2.1
  obtain ⟨_, hminF⟩ := (isGarlingNormal_iff_minpoly_splits K F).mp hnormKF
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  -- Show inductively for `0 ≤ m ≤ r` that `K_m = garlingPrefixField K α m` has `[K_m : K]`
  -- `K`-fixing monomorphisms into `F`.
  have hcount :
      ∀ m : ℕ, m ≤ r →
        Nat.card {σ : garlingPrefixField K α m →+* F | IsRingMonomorphism σ ∧
          ∀ k : K, σ (algebraMap K (garlingPrefixField K α m) k) = algebraMap K F k} =
          Module.finrank K (garlingPrefixField K α m) := by
    intro m hm
    induction m with
    | zero =>
      let K0 := garlingPrefixField K α 0
      have hK0_bot : K0 = ⊥ := garlingPrefixField_zero K α
      have hfr1 : Module.finrank K K0 = 1 := by
        rw [hK0_bot]
        exact IntermediateField.finrank_bot (F := K) (E := L)
      have hfin0 : IsFiniteExtension K K0 :=
        (isFiniteExtension_iff_moduleFinite K K0).mpr inferInstance
      have h103 := theorem_10_3 hfin0
        ((extDegree_eq_finrank K K0).trans (by rw [hfr1, Nat.cast_one]))
        (algebraMap K F).injective
      have hcond0 :
          IsGarlingSeparableExtension K K0 ∧
            ∀ β : K0, GarlingSplitsOver F F (garlingMapPoly (algebraMap K F) (minpoly K β)) := by
        have hsurj0 : Function.Surjective (algebraMap K K0) := by
          intro x
          have hx : (x : L) ∈ (⊥ : IntermediateField K L) := hK0_bot ▸ x.2
          obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hx
          exact ⟨k, Subtype.ext hk⟩
        refine ⟨fun β => ?_, fun β => ?_⟩
        · obtain ⟨k, rfl⟩ := hsurj0 β
          exact (isGarlingSeparableElement_iff K _).mpr (isSeparable_algebraMap k)
        · obtain ⟨k, rfl⟩ := hsurj0 β
          have hmin_k : minpoly K (algebraMap K K0 k) = Polynomial.X - Polynomial.C k :=
            minpoly.eq_X_sub_C_of_algebraMap_inj k (algebraMap K K0).injective
          rw [(garlingSplitsOver_mapPoly_iff (algebraMap K F) _).1, hmin_k,
            Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
          exact Polynomial.Splits.X_sub_C (algebraMap K F k)
      exact (h103.1 hcond0).2.trans hfr1.symm
    | succ m ihm =>
      have hm_lt : m < r := Nat.lt_of_succ_le hm
      let idx : Fin r := ⟨m, hm_lt⟩
      have hSm_card := ihm (Nat.le_of_lt hm_lt)
      let Km := garlingPrefixField K α m
      let Km1 := garlingPrefixField K α (m + 1)
      have hle_m : Km ≤ Km1 := garlingPrefixField_mono K α (Nat.le_succ m)
      let inc : Km →ₐ[K] Km1 := IntermediateField.inclusion hle_m
      let _ : Algebra Km Km1 := inc.toRingHom.toAlgebra
      have _ : IsScalarTower K Km Km1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have _ : IsScalarTower Km Km1 L := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let valKm : Km1 →ₐ[Km] L :=
        { Km1.val.toRingHom with commutes' := fun _ => rfl }
      let α_Km1 : Km1 := ⟨α idx, IntermediateField.subset_adjoin K _
        ⟨idx, Nat.lt_succ_self m, rfl⟩⟩
      have hadj_step : IntermediateField.adjoin Km ({α_Km1} : Set Km1) = ⊤ := by
        ext x
        simp only [IntermediateField.mem_top, iff_true]
        let E_K : IntermediateField K L :=
          ((IntermediateField.adjoin Km ({α_Km1} : Set Km1)).restrictScalars K).map Km1.val
        have hsub : α '' {j : Fin r | (j : ℕ) < m + 1} ⊆ (E_K : Set L) := by
          rintro _ ⟨j, hj, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
          · let yKm : Km := ⟨α j, IntermediateField.subset_adjoin K _ ⟨j, hj_lt, rfl⟩⟩
            refine ⟨algebraMap Km Km1 yKm, ?_, rfl⟩
            exact (IntermediateField.adjoin Km ({α_Km1} : Set Km1)).algebraMap_mem yKm
          · have hj_idx : j = idx := Fin.ext hj_eq
            subst hj_idx
            exact ⟨α_Km1, IntermediateField.mem_adjoin_simple_self Km α_Km1, rfl⟩
        have hKm1_le : Km1 ≤ E_K := IntermediateField.adjoin_le_iff.mpr hsub
        obtain ⟨y, hy, hyx⟩ := hKm1_le x.2
        exact (Km1.val.injective hyx) ▸ hy
      have hsep_idx : IsGarlingSeparableElement Km α_Km1 := by
        have hsL : IsGarlingSeparableElement Km (α idx) := hsep_step idx
        have hmin_eq : minpoly Km (α idx) = minpoly Km α_Km1 :=
          minpoly.algHom_eq valKm Km1.val.injective α_Km1
        refine ⟨?_, hmin_eq ▸ hsL.2⟩
        obtain ⟨p, hp0, hpeval⟩ := hsL.1
        exact ⟨p, hp0, Subtype.ext ((Polynomial.aeval_algHom_apply valKm α_Km1 p).symm.trans hpeval)⟩
      have _ : Module.Finite Km Km1 := Module.Finite.of_restrictScalars_finite K Km Km1
      let dm1 : ℕ := Module.finrank Km Km1
      have hdm1_ext : extDegree Km Km1 = (dm1 : ℕ∞) := extDegree_eq_finrank Km Km1
      have hSm_fin : Finite {i : Km →+* F | IsRingMonomorphism i ∧
          ∀ k : K, i (algebraMap K Km k) = algebraMap K F k} :=
        extendingMonomorphisms_finite
          ((isFiniteExtension_iff_moduleFinite K Km).mpr inferInstance) (algebraMap K F)
      have hfiber_step :
          ∀ i : {i : Km →+* F | IsRingMonomorphism i ∧ ∀ k : K, i (algebraMap K Km k) = algebraMap K F k},
            let Si := {σ : Km1 →+* F | IsRingMonomorphism σ ∧ ∀ x : Km, σ (algebraMap Km Km1 x) = i.1 x}
            Finite Si ∧ Nat.card Si = dm1 := by
        intro i
        let nj : Km[X] := minpoly Km α_Km1
        let mj : K[X] := minpoly K (α idx)
        have hmj_eval : Polynomial.aeval α_Km1 (mj.map (algebraMap K Km)) = 0 := by
          apply Km1.val.injective
          change valKm (Polynomial.aeval α_Km1 (mj.map (algebraMap K Km))) = 0
          rw [← Polynomial.aeval_algHom_apply valKm α_Km1 (mj.map (algebraMap K Km)),
            Polynomial.aeval_map_algebraMap]
          exact minpoly.aeval K (α idx)
        have hdvd : nj ∣ mj.map (algebraMap K Km) := minpoly.dvd Km α_Km1 hmj_eval
        have hdvdF : nj.map i.1 ∣ (mj.map (algebraMap K Km)).map i.1 :=
          Polynomial.map_dvd i.1 hdvd
        have hcomp : i.1.comp (algebraMap K Km) = algebraMap K F := RingHom.ext i.2.2
        have hmap_mj : (mj.map (algebraMap K Km)).map i.1 = mj.map (algebraMap K F) := by
          rw [Polynomial.map_map, hcomp]
        rw [hmap_mj] at hdvdF
        have hmin_F : minpoly K (algebraMap L F (α idx)) = mj :=
          minpoly.algHom_eq (IsScalarTower.toAlgHom K L F) (algebraMap L F).injective (α idx)
        have hmj_sp : (mj.map (algebraMap K F)).Splits :=
          (garlingSplitsOver_iff_splits K F mj).mp (hmin_F ▸ hminF (algebraMap L F (α idx)))
        have hmj_ne0 : mj.map (algebraMap K F) ≠ 0 :=
          ((minpoly.monic (Algebra.IsIntegral.isIntegral (α idx))).map (algebraMap K F)).ne_zero
        have hnj_sp : GarlingSplitsOver F F (garlingMapPoly i.1 nj) :=
          (garlingSplitsOver_mapPoly_iff i.1 nj).1.mpr
            (Polynomial.Splits.of_dvd hmj_sp hmj_ne0 hdvdF)
        have h102 := (theorem_10_2 hadj_step hsep_idx.1 hdm1_ext i.2.1).1 ⟨hsep_idx, hnj_sp⟩
        have hSi_fin : Finite {σ : Km1 →+* F | IsRingMonomorphism σ ∧ ∀ x : Km, σ (algebraMap Km Km1 x) = i.1 x} :=
          extendingMonomorphisms_finite
            ((isFiniteExtension_iff_moduleFinite Km Km1).mpr inferInstance) i.1
        exact ⟨hSi_fin, h102.2⟩
      obtain ⟨_, hmul_eq, _⟩ := card_extendingMonomorphisms_tower (K := K) (M := Km) (K' := Km1)
        (L := F) (d₂ := dm1) (algebraMap K F) hSm_fin (fun i => (hfiber_step i).1)
      calc Nat.card {σ : Km1 →+* F | IsRingMonomorphism σ ∧
              ∀ k : K, σ (algebraMap K Km1 k) = algebraMap K F k}
          = Nat.card {i : Km →+* F | IsRingMonomorphism i ∧
              ∀ k : K, i (algebraMap K Km k) = algebraMap K F k} * dm1 :=
            hmul_eq fun i => (hfiber_step i).2
        _ = Module.finrank K Km * dm1 := by rw [hSm_card]
        _ = Module.finrank K Km1 := Module.finrank_mul_finrank K Km Km1
  -- At `m = r`, `garlingPrefixField K α r = ⊤`, so `L` has `[L : K]` `K`-fixing monomorphisms into `F`.
  have hSr_card := hcount r le_rfl
  have hKr_top : garlingPrefixField K α r = ⊤ := (garlingPrefixField_full K α).trans hadj
  let eL : (garlingPrefixField K α r) ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hKr_top).trans IntermediateField.topEquiv
  let SL := {σ : L →+* F | IsRingMonomorphism σ ∧ ∀ k : K, σ (algebraMap K L k) = algebraMap K F k}
  let eHom :
      {σ : garlingPrefixField K α r →+* F | IsRingMonomorphism σ ∧
        ∀ k : K, σ (algebraMap K (garlingPrefixField K α r) k) = algebraMap K F k} ≃ SL :=
    { toFun := fun σ => ⟨σ.1.comp eL.symm.toRingHom,
        σ.2.1.comp eL.symm.injective,
        fun k => by
          change σ.1 (eL.symm (algebraMap K L k)) = algebraMap K F k
          rw [eL.symm.commutes k]
          exact σ.2.2 k⟩
      invFun := fun τ => ⟨τ.1.comp eL.toRingHom,
        τ.2.1.comp eL.injective,
        fun k => by
          change τ.1 (eL (algebraMap K _ k)) = algebraMap K F k
          rw [eL.commutes k]
          exact τ.2.2 k⟩
      left_inv := fun σ => Subtype.ext (RingHom.ext fun x => by
        change σ.1 (eL.symm (eL x)) = σ.1 x
        rw [eL.symm_apply_apply])
      right_inv := fun τ => Subtype.ext (RingHom.ext fun y => by
        change τ.1 (eL (eL.symm y)) = τ.1 y
        rw [eL.apply_symm_apply]) }
  have hSL_card : Nat.card SL = Module.finrank K L := by
    rw [← Nat.card_congr eHom, hSr_card, LinearEquiv.finrank_eq eL.toLinearEquiv]
  -- Apply Theorem 10.3 to `L : K` and `algebraMap K F : K →+* F` to conclude `L : K` is separable.
  have h103_L := theorem_10_3 hfin (extDegree_eq_finrank K L) (algebraMap K F).injective
  by_contra hnot_sep
  have hlt := (h103_L.2 (fun hc => hnot_sep hc.1)).2
  exact Nat.lt_irrefl _ (hSL_card ▸ hlt)

/-- **Corollary 2** [to Theorem 10.3] (§10.2, printed p. 84 / PDF p. 92):
*"Suppose that `L : K` is finite and that `L = K(α₁, …, α_r)`. If each `α_i` is separable over `K`
then `L : K` is separable."*

Proved directly from `Corollary 1` and `Theorem 10.1`'s minimal-polynomial divisibility step. -/
theorem corollary_2_to_theorem_10_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) {r : ℕ} (α : Fin r → L)
    (hadj : IntermediateField.adjoin K (Set.range α) = ⊤)
    (hsep : ∀ i : Fin r, IsGarlingSeparableElement K (α i)) :
    IsGarlingSeparableExtension K L :=
  corollary_1_to_theorem_10_3 hfin α hadj fun i => isGarlingSeparableElement_tower_top (hsep i)

/-- **Corollary 3** [to Theorem 10.3] (§10.2, printed p. 84 / PDF p. 92):
*"Suppose that `f ∈ K[x]` is separable over `K` and that `L : K` is a splitting field extension for
`f`. Then `L : K` is separable."*

Holds literally for **every** `f ∈ K[x]` (including `f = 0` and degree-`0` constants, synchronized
with `Garling/Chapter07.lean`'s `IsGarlingSplittingFieldExtension`), proved by applying
`Corollary 2` to the roots of `f` in `L`. -/
theorem corollary_3_to_theorem_10_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : IsGarlingSeparablePoly f) (hsf : IsGarlingSplittingFieldExtension K L f) :
    IsGarlingSeparableExtension K L := by
  have hfin : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsf).1
  by_cases hf0 : f = 0
  · subst hf0
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ :=
      (isGarlingSplittingFieldExtension_zero_iff K L).mp hsf
    exact corollary_2_to_theorem_10_3 hfin Fin.elim0
      (by rw [Set.range_eq_empty, IntermediateField.adjoin_empty, hbot_top])
      (fun i => Fin.elim0 i)
  · obtain ⟨n, c, α, hexp⟩ := hsf.1
    have hadj_top : IntermediateField.adjoin K (Set.range α) = ⊤ := by
      have h71 : IsGarlingSplittingFieldExtension K (IntermediateField.adjoin K (Set.range α)) f :=
        theorem_7_1 hf0 hexp
      by_contra hne
      exact hsf.2 (IntermediateField.adjoin K (Set.range α)) hne h71.1
    have hroots : Set.range α = f.rootSet L := (garlingSplitsExplicit_props hf0 hexp).2.2.2
    refine corollary_2_to_theorem_10_3 hfin α hadj_top fun i => ?_
    have hmem : α i ∈ f.rootSet L := hroots ▸ ⟨i, rfl⟩
    have haeval : Polynomial.aeval (α i) f = 0 := (Polynomial.mem_rootSet.mp hmem).2
    have halg : IsGarlingAlgebraic K (α i) := ⟨f, hf0, haeval⟩
    have hint : IsIntegral K (α i) := (isGarlingAlgebraic_iff_isIntegral K (α i)).mp halg
    have hm_irr : Irreducible (minpoly K (α i)) := minpoly.irreducible hint
    have hm_dvd : minpoly K (α i) ∣ f := minpoly.dvd K (α i) haeval
    have hm_sep : (minpoly K (α i)).Separable :=
      (isGarlingSeparableIrreducible_iff_separable hm_irr).mp (hf (minpoly K (α i)) hm_irr hm_dvd)
    exact ⟨halg, (isGarlingSeparablePoly_of_irreducible_iff hm_irr).mpr hm_sep⟩

/-- Scalar-tower form of **Corollary 4** [to Theorem 10.3] (§10.2, printed p. 84 / PDF p. 92):
for any tower `K → M → L` with `L : K` finite, if `L : M` and `M : K` are separable, then `L : K`
is separable.

Proved directly following Garling's 2-line proof on p. 84: writes `M = K(α₁, …, α_r)` and
`L = M(α_{r+1}, …, α_s)` via finite bases and applies `Corollary 1` and `Theorem 10.1`. -/
theorem corollary_4_to_theorem_10_3_tower {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (hfin : IsFiniteExtension K L)
    (hsep_ML : IsGarlingSeparableExtension M L) (hsep_MK : IsGarlingSeparableExtension K M) :
    IsGarlingSeparableExtension K L := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have _ : Module.Finite M L := Module.Finite.of_restrictScalars_finite K M L
  let imM : IntermediateField K L := (IsScalarTower.toAlgHom K M L).fieldRange
  let eM : M ≃ₐ[K] imM := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M L)
  have _ : Module.Finite K M := Module.Finite.equiv eM.symm.toLinearEquiv
  let r : ℕ := Module.finrank K M
  let t : ℕ := Module.finrank M L
  let bM : Module.Basis (Fin r) K M := Module.finBasis K M
  let bL : Module.Basis (Fin t) M L := Module.finBasis M L
  let α : Fin (r + t) → L :=
    Fin.append (fun i => algebraMap M L (bM i)) bL
  have hadj : IntermediateField.adjoin K (Set.range α) = ⊤ := by
    let E : IntermediateField K L := IntermediateField.adjoin K (Set.range α)
    have hbM_in_E : ∀ i : Fin r, algebraMap M L (bM i) ∈ E := fun i =>
      IntermediateField.subset_adjoin K (Set.range α)
        ⟨Fin.castAdd t i, by simp [α, Fin.append_left]⟩
    have hM_in_E : ∀ m : M, algebraMap M L m ∈ E := by
      let P : Submodule K M := E.toSubmodule.comap (IsScalarTower.toAlgHom K M L).toLinearMap
      have htop_P : (⊤ : Submodule K M) ≤ P := by
        rw [← bM.span_eq, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hbM_in_E i
      exact fun m => htop_P Submodule.mem_top
    let E_M : IntermediateField M L :=
      { E.toSubfield with algebraMap_mem' := hM_in_E }
    have hbL_in_EM : ∀ j : Fin t, bL j ∈ E_M := fun j =>
      IntermediateField.subset_adjoin K (Set.range α)
        ⟨Fin.natAdd r j, by simp [α, Fin.append_right]⟩
    have htop_L : (⊤ : Submodule M L) ≤ E_M.toSubmodule := by
      rw [← bL.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hbL_in_EM j
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    exact htop_L Submodule.mem_top
  refine corollary_1_to_theorem_10_3 hfin α hadj fun i => ?_
  by_cases hi : (i : ℕ) < r
  · let i₀ : Fin r := ⟨i.val, hi⟩
    have hαi : α i = algebraMap M L (bM i₀) := by
      have hi_eq : i = Fin.castAdd t i₀ := Fin.ext rfl
      rw [hi_eq]
      simp [α, Fin.append_left]
    rw [hαi]
    have hsep_bM : IsGarlingSeparableElement K (bM i₀) := hsep_MK (bM i₀)
    have hmin_eq : minpoly K (algebraMap M L (bM i₀)) = minpoly K (bM i₀) :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom K M L) (algebraMap M L).injective (bM i₀)
    have hsep_K : IsGarlingSeparableElement K (algebraMap M L (bM i₀)) := by
      obtain ⟨⟨p, hp0, hpeval⟩, hs⟩ := hsep_bM
      refine ⟨⟨p, hp0, ?_⟩, hmin_eq ▸ hs⟩
      have h1 : algebraMap M L (Polynomial.aeval (bM i₀) p) =
          Polynomial.aeval (algebraMap M L (bM i₀)) p := by
        simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K M L) (bM i₀) p).symm
      rw [← h1, hpeval, map_zero]
    exact isGarlingSeparableElement_tower_top hsep_K
  · have hr_le : r ≤ (i : ℕ) := Nat.le_of_not_lt hi
    let Ki : IntermediateField K L := garlingPrefixField K α i.val
    have himM_le : imM ≤ Ki := by
      have hbM_Ki : ∀ j : Fin r, algebraMap M L (bM j) ∈ Ki := by
        intro j
        apply IntermediateField.subset_adjoin K
        refine ⟨Fin.castAdd t j, ?_, ?_⟩
        · exact lt_of_lt_of_le j.isLt hr_le
        · simp [α, Fin.append_left]
      let P : Submodule K M := Ki.toSubmodule.comap (IsScalarTower.toAlgHom K M L).toLinearMap
      have htop_P : (⊤ : Submodule K M) ≤ P := by
        rw [← bM.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hbM_Ki j
      rintro _ ⟨m, rfl⟩
      exact htop_P Submodule.mem_top
    let mToKi : M →+* Ki :=
      { toFun := fun m => ⟨algebraMap M L m, himM_le ⟨m, rfl⟩⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun x y => Subtype.ext (map_mul _ x y)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun x y => Subtype.ext (map_add _ x y) }
    let _ : Algebra M Ki := mToKi.toAlgebra
    have _ : IsScalarTower M Ki L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact isGarlingSeparableElement_tower_top (K := M) (M := Ki) (L := L) (hsep_ML (α i))

/-- **Corollary 4** [to Theorem 10.3] (§10.2, printed p. 84 / PDF p. 92):
*"Suppose that `L : K` is finite, and that `L : M : K` is a tower. If `L : M` and `M : K` are
separable, then so is `L : K`."* -/
theorem corollary_4_to_theorem_10_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (M : IntermediateField K L)
    (hsep_LM : IsGarlingSeparableExtension M L) (hsep_MK : IsGarlingSeparableExtension K M) :
    IsGarlingSeparableExtension K L :=
  corollary_4_to_theorem_10_3_tower hfin hsep_LM hsep_MK

/-- **Exercise 10.1** (§10.2, printed p. 84 / PDF p. 92 — verified on 160 DPI scan; note OCR
`garling1986_pages.txt` corrupts both occurrences of `L'` to `E`):
*"Suppose that `L : K` is finite and that `L' : L` is a normal closure for `L : K`. Show that
`L : K` is separable if and only if there are exactly `[L : K]` monomorphisms of `L` into `L'`
which fix `K`."* -/
theorem exercise_10_1 {K : Type u} {L : Type v} {L' : Type w}
    [Field K] [Field L] [Field L'] [Algebra K L] [Algebra L L'] [Algebra K L']
    [IsScalarTower K L L'] (hfin : IsFiniteExtension K L)
    (hcl : IsGarlingNormalClosure K L L') :
    let S := {σ : L →+* L' | IsRingMonomorphism σ ∧
      ∀ k : K, σ (algebraMap K L k) = algebraMap K L' k}
    (IsGarlingSeparableExtension K L ↔ setOrder S = extDegree K L) ∧
    (IsGarlingSeparableExtension K L ↔ Nat.card S = Module.finrank K L) := by
  intro S
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  let d : ℕ := Module.finrank K L
  have hd_ext : extDegree K L = (d : ℕ∞) := extDegree_eq_finrank K L
  obtain ⟨_, hminL'⟩ := (isGarlingNormal_iff_minpoly_splits K L').mp hcl.2.1
  have hsplits_all : ∀ α : L, GarlingSplitsOver L' L' (garlingMapPoly (algebraMap K L') (minpoly K α)) := by
    intro α
    have hmin_eq : minpoly K (algebraMap L L' α) = minpoly K α :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom K L L') (algebraMap L L').injective α
    rw [(garlingSplitsOver_mapPoly_iff (algebraMap K L') (minpoly K α)).1]
    exact (garlingSplitsOver_iff_splits K L' (minpoly K α)).mp (hmin_eq ▸ hminL' (algebraMap L L' α))
  have h103 := theorem_10_3 hfin hd_ext (algebraMap K L').injective
  have hiff_nat : IsGarlingSeparableExtension K L ↔ Nat.card S = d := by
    constructor
    · intro hsep
      exact (h103.1 ⟨hsep, hsplits_all⟩).2
    · intro hcard
      by_contra hnot
      have hlt := (h103.2 (fun hc => hnot hc.1)).2
      exact Nat.lt_irrefl d (hcard ▸ hlt)
  have hiff_ord : IsGarlingSeparableExtension K L ↔ setOrder S = extDegree K L := by
    rw [hd_ext]
    constructor
    · intro hsep
      exact (h103.1 ⟨hsep, hsplits_all⟩).1
    · intro hord
      by_contra hnot
      have hlt := (h103.2 (fun hc => hnot hc.1)).1
      rw [hord] at hlt
      exact lt_irrefl _ hlt
  exact ⟨hiff_ord, hiff_nat⟩

/-- `AlgHom` (`L →ₐ[K] L'`) companion to **Exercise 10.1** (§10.2, p. 84). -/
theorem exercise_10_1_algHom {K : Type u} {L : Type v} {L' : Type w}
    [Field K] [Field L] [Field L'] [Algebra K L] [Algebra L L'] [Algebra K L']
    [IsScalarTower K L L'] (hfin : IsFiniteExtension K L)
    (hcl : IsGarlingNormalClosure K L L') :
    IsGarlingSeparableExtension K L ↔ Nat.card (L →ₐ[K] L') = Module.finrank K L := by
  let e : (L →ₐ[K] L') ≃
      {σ : L →+* L' | IsRingMonomorphism σ ∧
        ∀ k : K, σ (algebraMap K L k) = algebraMap K L' k} :=
    { toFun := fun φ => ⟨φ.toRingHom, φ.injective, φ.commutes⟩
      invFun := fun σ => { σ.1 with commutes' := σ.2.2 }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact (exercise_10_1 hfin hcl).2

/-- Extension-triple companion to **Exercise 10.1** (§10.2, p. 84). -/
theorem exercise_10_1_triple {K : Type u} {L : Type v} {L' : Type w}
    [Field K] [Field L] [Field L']
    (eKL : FieldExtensionTriple K L) (eLL' : FieldExtensionTriple L L')
    (hfin : letI : Algebra K L := eKL.hom.toAlgebra; IsFiniteExtension K L)
    (hcl : IsGarlingNormalClosureTriple eKL eLL') :
    letI : Algebra K L := eKL.hom.toAlgebra
    (IsGarlingSeparableExtension K L ↔
      setOrder {σ : L →+* L' | IsRingMonomorphism σ ∧
        ∀ k : K, σ (eKL.hom k) = eLL'.hom (eKL.hom k)} = extDegree K L) := by
  let _ : Algebra K L := eKL.hom.toAlgebra
  let _ : Algebra L L' := eLL'.hom.toAlgebra
  let _ : Algebra K L' := (eLL'.hom.comp eKL.hom).toAlgebra
  have _ : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (exercise_10_1 hfin hcl).1

/-! ## §10.3 Galois extensions (printed pp. 84–85, PDF pp. 92–93) -/

/-- Garling's prose definition of a *Galois extension* `L : K` (§10.3, printed p. 84 / PDF p. 92):
*"An extension which is finite, normal and separable is called a Galois extension."*

Note (`BRIEF.md` Flag 5): Garling includes `IsFiniteExtension K L` in the definition of a Galois
extension, making `IsGarlingGaloisExtension K L` equivalent to `FiniteDimensional K L ∧ IsGalois K L`. -/
def IsGarlingGaloisExtension (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Prop :=
  IsFiniteExtension K L ∧ IsGarlingNormal K L ∧ IsGarlingSeparableExtension K L

/-- Extension-triple formulation of a *Galois extension* `(i, K, L)` (§4.2, p. 40; §10.3, p. 84). -/
def IsGarlingGaloisExtensionTriple {K : Type u} {L : Type v} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : Prop :=
  letI : Algebra K L := ext.hom.toAlgebra
  IsGarlingGaloisExtension K L

/-- Exact bridge between Garling's `IsGarlingGaloisExtension K L` (§10.3, p. 84) and Mathlib's
`FiniteDimensional K L ∧ IsGalois K L`. -/
theorem isGarlingGaloisExtension_iff (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    IsGarlingGaloisExtension K L ↔ FiniteDimensional K L ∧ IsGalois K L := by
  rw [IsGarlingGaloisExtension, isFiniteExtension_iff_moduleFinite, isGarlingNormal_iff,
    isGarlingSeparableExtension_iff, isGalois_iff]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨h1, h2, h3⟩⟩

/-- **Theorem 10.4** (§10.3, printed p. 84 / PDF p. 92):
*"Suppose that `L : K` is finite. If `L : K` is a Galois extension, there are `[L : K]`
automorphisms of `L` which fix `K`; otherwise there are fewer than `[L : K]` such automorphisms."*

Proved directly following Garling's 1-line deduction on p. 84: applies `Theorem 10.3` to
`algebraMap K L : K →+* L` and invokes `Theorem 4.8` (`theorem_4_8_isFieldAutomorphism`) to identify
`K`-fixing monomorphisms `L →+* L` with `K`-fixing automorphisms of `L`. -/
theorem theorem_10_4 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    let A := {σ : L →+* L | IsFieldAutomorphism σ ∧ FixesBaseField K σ}
    (IsGarlingGaloisExtension K L →
      setOrder A = extDegree K L ∧ Nat.card A = Module.finrank K L) ∧
    (¬ IsGarlingGaloisExtension K L →
      setOrder A < extDegree K L ∧ Nat.card A < Module.finrank K L) := by
  intro A
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have halg : IsAlgebraicExtension K L := ((theorem_4_6 K L).1.mp hfin).1
  let d : ℕ := Module.finrank K L
  have hd_ext : extDegree K L = (d : ℕ∞) := extDegree_eq_finrank K L
  let S := {σ : L →+* L | IsRingMonomorphism σ ∧ ∀ k : K, σ (algebraMap K L k) = algebraMap K L k}
  have hAS : A = S := by
    ext σ
    exact ⟨fun ⟨haut, hfix⟩ => ⟨haut.1, hfix⟩,
      fun ⟨hmono, hfix⟩ => ⟨theorem_4_8_isFieldAutomorphism halg hmono hfix, hfix⟩⟩
  have hcond_iff :
      (IsGarlingSeparableExtension K L ∧
        ∀ α : L, GarlingSplitsOver L L (garlingMapPoly (algebraMap K L) (minpoly K α))) ↔
        IsGarlingGaloisExtension K L := by
    unfold IsGarlingGaloisExtension
    rw [isGarlingNormal_iff_minpoly_splits]
    have hsp_iff :
        ∀ α : L,
          GarlingSplitsOver L L (garlingMapPoly (algebraMap K L) (minpoly K α)) ↔
            GarlingSplitsOver K L (minpoly K α) := by
      intro α
      rw [(garlingSplitsOver_mapPoly_iff (algebraMap K L) (minpoly K α)).1,
        garlingSplitsOver_iff_splits]
    simp_rw [hsp_iff]
    exact ⟨fun ⟨hsep, hsp⟩ => ⟨hfin, ⟨halg, hsp⟩, hsep⟩,
      fun ⟨_, ⟨_, hsp⟩, hsep⟩ => ⟨hsep, hsp⟩⟩
  have h103 := theorem_10_3 hfin hd_ext (algebraMap K L).injective
  rw [hAS, hd_ext]
  exact ⟨fun hgal => h103.1 (hcond_iff.mpr hgal),
    fun hngal => h103.2 (fun hc => hngal (hcond_iff.mp hc))⟩

/-- Bundled `AlgEquiv` (`L ≃ₐ[K] L`) companion to **Theorem 10.4** (§10.3, p. 84). -/
theorem theorem_10_4_algEquiv {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    (IsGarlingGaloisExtension K L → Nat.card (L ≃ₐ[K] L) = Module.finrank K L) ∧
    (¬ IsGarlingGaloisExtension K L → Nat.card (L ≃ₐ[K] L) < Module.finrank K L) := by
  let e : (L ≃ₐ[K] L) ≃ {σ : L →+* L | IsFieldAutomorphism σ ∧ FixesBaseField K σ} :=
    { toFun := fun φ => ⟨φ.toRingHom, ⟨φ.injective, φ.surjective⟩, φ.commutes⟩
      invFun := fun σ =>
        AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective σ.1 ⟨σ.2.1.1, σ.2.1.2⟩) σ.2.2
      left_inv := fun φ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  rw [Nat.card_congr e]
  have h := theorem_10_4 hfin
  exact ⟨fun hg => (h.1 hg).2, fun hng => (h.2 hng).2⟩

/-! ## §10.4 Differentiation (printed pp. 85–87, PDF pp. 93–95) -/

/-- Garling's *repeated root* relation in a splitting field `L : K` for `f ∈ K[x]` (§10.4, printed
p. 86 l. 1: *"Suppose that `f` has a repeated root `α` in `L`. Then `f = (x - α)^k g`, where `k > 1`
and `g ∈ L[x]`"*): there exist `α ∈ L` and `k > 1` such that `(x - α)^k ∣ f` in `L[x]`. -/
def HasGarlingRepeatedRoot (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]
    (f : K[X]) : Prop :=
  ∃ (α : L) (k : ℕ), 1 < k ∧ (Polynomial.X - Polynomial.C α) ^ k ∣ f.map (algebraMap K L)

/-- Literal printed wording of *repeated root* on p. 85 l. 9 (`BRIEF.md` Flag 3; see `QUEUE.md`):
*"We say that `f` has a repeated root in `L` if there exists `α ∈ L` and `k > 1` such that
`(x - α)^k ∣ f` in `K[x]`."*
Viewed inside `L[x]`, divisibility in `K[x]` requires a cofactor `g ∈ K[x]` (and `(x - α)^k ∈ K[x]`). -/
def HasLiteralPrintedRepeatedRootInBasePoly (K : Type*) (L : Type*) [Field K] [Field L]
    [Algebra K L] (f : K[X]) : Prop :=
  ∃ (α : L) (k : ℕ) (g : K[X]),
    1 < k ∧ f.map (algebraMap K L) = (Polynomial.X - Polynomial.C α) ^ k * g.map (algebraMap K L)

/-- Prose characterization of inseparable irreducible polynomials (§10.4, printed p. 85 / PDF p. 93):
*"An irreducible polynomial in `K[x]` is not separable if and only if it has a repeated root in a
splitting field."* -/
theorem irreducible_not_separable_iff_hasGarlingRepeatedRoot {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {f : K[X]} (hf : Irreducible f)
    (hsf : IsGarlingSplittingFieldExtension K L f) :
    ¬ IsGarlingSeparablePoly f ↔ HasGarlingRepeatedRoot K L f := by
  classical
  let _ : DecidableEq L := Classical.decEq L
  rw [isGarlingSeparablePoly_of_irreducible_iff hf,
    ← isGarlingSeparableIrreducible_iff_separable hf,
    (isGarlingSeparableIrreducible_iff_of_splittingField hf hsf).2]
  obtain ⟨_, hnat⟩ := setOrder_aeval_eq_zero_eq_toFinset_card (L := L) hf.ne_zero
  rw [hnat]
  let fL : L[X] := f.map (algebraMap K L)
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf.ne_zero
  have hsp : fL.Splits := (garlingSplitsOver_iff_splits K L f).mp hsf.1
  have hcard_roots : fL.roots.card = garlingDegree f hf.ne_zero := by
    unfold garlingDegree
    rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective f]
    exact hsp.natDegree_eq_card_roots.symm
  rw [← hcard_roots]
  constructor
  · intro hne
    have hnot_nodup : ¬ fL.roots.Nodup := fun hnd =>
      hne (Multiset.toFinset_card_of_nodup hnd)
    rw [Multiset.nodup_iff_count_le_one] at hnot_nodup
    push Not at hnot_nodup
    obtain ⟨α, hcount⟩ := hnot_nodup
    refine ⟨α, fL.roots.count α, hcount, ?_⟩
    rw [Polynomial.count_roots]
    exact Polynomial.pow_rootMultiplicity_dvd fL α
  · rintro ⟨α, k, hk1, hdvd⟩
    intro hcard_eq
    have hnodup : fL.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp hcard_eq
    have hk_le : k ≤ fL.roots.count α := by
      rw [Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hfL0).mpr hdvd
    have hle1 : fL.roots.count α ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnodup α
    omega

/-- Garling's algebraic derivative `D : K[x] → K[x]` (§10.4, printed p. 85 / PDF p. 93):
for `f = a₀ + a₁ x + ⋯ + a_n x^n ∈ K[x]`, `Df = a₁ + 2 a₂ x + ⋯ + n a_n x^{n-1}`, where
`j a_j = a_j + ⋯ + a_j` (`j` times, i.e. `j • a_j`). -/
noncomputable def garlingDeriv {K : Type*} [CommRing K] (f : K[X]) : K[X] :=
  f.sum fun j a => if j = 0 then 0 else Polynomial.C (j • a) * Polynomial.X ^ (j - 1)

/-- Exact agreement between Garling's coefficient-sum definition `garlingDeriv` (§10.4, p. 85) and
Mathlib's `Polynomial.derivative`. -/
@[simp]
theorem garlingDeriv_eq_derivative {K : Type*} [CommRing K] (f : K[X]) :
    garlingDeriv f = Polynomial.derivative f := by
  unfold garlingDeriv
  rw [Polynomial.derivative_apply]
  unfold Polynomial.sum
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hj, nsmul_eq_mul, mul_comm]

/-- Prose `K`-linearity and Leibniz product rules for `D : K[x] → K[x]` (§10.4, printed p. 85 /
PDF p. 93): `D(f + g) = Df + Dg`, `D(α f) = α (Df)`, `D(x^m x^n) = (D x^m) x^n + x^m (D x^n)`, and
`D(f g) = (Df) g + f (Dg)`. -/
theorem garlingDeriv_add {K : Type*} [CommRing K] (f g : K[X]) :
    garlingDeriv (f + g) = garlingDeriv f + garlingDeriv g := by
  simp [Polynomial.derivative_add]

theorem garlingDeriv_C_mul {K : Type*} [CommRing K] (α : K) (f : K[X]) :
    garlingDeriv (Polynomial.C α * f) = Polynomial.C α * garlingDeriv f := by
  simp

/-- Bundled `K`-linear map `D : K[x] →ₗ[K] K[x]` (§10.4, printed p. 85: *"D is a K-linear mapping"*). -/
noncomputable def garlingDerivLinearMap (K : Type*) [CommRing K] : K[X] →ₗ[K] K[X] where
  toFun := garlingDeriv
  map_add' := garlingDeriv_add
  map_smul' α f := by
    simp [Algebra.smul_def]

theorem garlingDeriv_mul {K : Type*} [CommRing K] (f g : K[X]) :
    garlingDeriv (f * g) = garlingDeriv f * g + f * garlingDeriv g := by
  simp [Polynomial.derivative_mul]

theorem garlingDeriv_pow {K : Type*} [CommRing K] (f : K[X]) (k : ℕ) :
    garlingDeriv (f ^ k) = (k : K[X]) * f ^ (k - 1) * garlingDeriv f := by
  rw [garlingDeriv_eq_derivative, Polynomial.derivative_pow]
  simp

/-- Prose characteristic-`p` identity (§10.4, printed p. 85 / PDF p. 93):
*"Notice also that, if `K` has non-zero characteristic `p`, then `D x^p = p x^{p-1} = 0`."* -/
theorem garlingDeriv_X_pow_char {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (_hp : p ≠ 0) :
    garlingDeriv (Polynomial.X ^ p : K[X]) = 0 := by
  have hpK : (p : K) = 0 := by
    rw [← hchar]
    exact ringChar.Nat.cast_ringChar
  rw [garlingDeriv_pow, garlingDeriv_eq_derivative, Polynomial.derivative_X, mul_one]
  have hpKX : (p : K[X]) = 0 := by
    rw [← Polynomial.C_eq_natCast, hpK, map_zero]
  rw [hpKX, zero_mul]

theorem garlingDeriv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R[X]) :
    garlingDeriv (f.map φ) = (garlingDeriv f).map φ := by
  simp [Polynomial.derivative_map]

theorem garlingDeriv_iterate_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (k : ℕ) (f : R[X]) :
    (garlingDeriv^[k] (f.map φ)) = (garlingDeriv^[k] f).map φ := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, garlingDeriv_map]

/-- **Counterexample to the literal p. 85 `in K[x]` wording in `Theorem 10.5 (i)`**
(`BRIEF.md` Flag 3; see `QUEUE.md`):
For `K = ℚ`, `f = (x² - 2)² ∈ ℚ[x]`, and splitting field `L = ℚ(√2)` (`qSqrtTwoSubfield`),
`f ≠ 0`, `L : ℚ` is a splitting field extension for `f`, `Theorem 10.5 (ii)` holds (`α = √2`),
`Theorem 10.5 (iii)` holds (`m = x² - 2`), and `HasGarlingRepeatedRoot ℚ L f` holds (`(x - √2)^2 ∣ f`
in `L[x]`), **yet** `¬ HasLiteralPrintedRepeatedRootInBasePoly ℚ L f` (no `α ∈ L` and `k > 1` has
`(x - α)^k` dividing `f` with a cofactor in `ℚ[x]`, nor even `(x - α)^k ∈ ℚ[x]`). -/
theorem theorem_10_5_literal_p85_counterexample :
    let f : ℚ[X] := (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ)) ^ 2
    let L := qSqrtTwoSubfield
    f ≠ 0 ∧
    IsGarlingSplittingFieldExtension ℚ L f ∧
    HasGarlingRepeatedRoot ℚ L f ∧
    (∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0) ∧
    (∃ (m : ℚ[X]) (hm0 : m ≠ 0), 1 ≤ garlingDegree m hm0 ∧ m ∣ f ∧ m ∣ garlingDeriv f) ∧
    ¬ HasLiteralPrintedRepeatedRootInBasePoly ℚ L f ∧
    ¬ ∃ (α : L) (k : ℕ), 1 < k ∧
        (Polynomial.X - Polynomial.C α) ^ k ∣ f.map (algebraMap ℚ L) ∧
        (Polynomial.X - Polynomial.C α) ^ k ∈ Set.range (Polynomial.map (algebraMap ℚ L)) := by
  intro f L
  let r2 : L := ⟨Real.sqrt 2, by
    change Real.sqrt 2 ∈ qSqrtTwoSubfield
    exact ⟨0, 1, by simp⟩⟩
  have hr2_sq : r2 ^ 2 = 2 := by
    apply Subtype.ext
    change (Real.sqrt 2) ^ 2 = 2
    exact Real.sq_sqrt (by norm_num)
  have hr2_not_rat : ∀ q : ℚ, algebraMap ℚ L q ≠ r2 := by
    intro q hq
    have hreal : (q : ℝ) = Real.sqrt 2 := congrArg Subtype.val hq
    exact irrational_sqrt_two ⟨q, hreal⟩
  have hmr2_not_rat : ∀ q : ℚ, algebraMap ℚ L q ≠ -r2 := by
    intro q hq
    apply hr2_not_rat (-q)
    rw [map_neg, hq, neg_neg]
  have hf_monic : f.Monic := (Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide)).pow 2
  have hf0 : f ≠ 0 := hf_monic.ne_zero
  -- Explicit factorization `f = (x - √2)(x - √2)(x + √2)(x + √2)` over `L = ℚ(√2)`.
  have hfL_fac :
      f.map (algebraMap ℚ L) =
        (Polynomial.X - Polynomial.C r2) ^ 2 * (Polynomial.X + Polynomial.C r2) ^ 2 := by
    dsimp [f]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have h2 : (algebraMap ℚ L 2 : L) = r2 ^ 2 := by
      rw [hr2_sq]
      norm_num
    rw [h2, map_pow]
    ring
  let roots4 : Fin 4 → L := ![r2, r2, -r2, -r2]
  have hexp : GarlingSplitsExplicit ℚ L f 4 1 roots4 := by
    unfold GarlingSplitsExplicit
    rw [hfL_fac, Fin.prod_univ_four]
    simp [roots4, sub_neg_eq_add]
    ring
  have hsf : IsGarlingSplittingFieldExtension ℚ L f := by
    refine ⟨⟨4, 1, roots4, hexp⟩, fun M hMne hspM => hMne ?_⟩
    have hr2_M : r2 ∈ M := by
      refine mem_of_garlingSplitsOver_intermediateField hf0 hspM ?_
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hfL_fac]
      simp
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨a, b, hx⟩ := x.2
    have hxeq : x = algebraMap ℚ L a + algebraMap ℚ L b * r2 := Subtype.ext hx
    rw [hxeq]
    exact M.add_mem (M.algebraMap_mem a) (M.mul_mem (M.algebraMap_mem b) hr2_M)
  have hrep : HasGarlingRepeatedRoot ℚ L f :=
    ⟨r2, 2, by decide, ⟨(Polynomial.X + Polynomial.C r2) ^ 2, hfL_fac⟩⟩
  have hdf : garlingDeriv f = Polynomial.C 4 * Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C 2) := by
    dsimp [f]
    rw [garlingDeriv_pow, garlingDeriv_eq_derivative, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_C]
    simp only [Nat.cast_ofNat, sub_zero, map_ofNat]
    ring
  have hii : ∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0 := by
    refine ⟨r2, ?_, ?_⟩
    · dsimp [f]
      simp [hr2_sq]
    · rw [hdf]
      simp [hr2_sq]
  have hiii : ∃ (m : ℚ[X]) (hm0 : m ≠ 0), 1 ≤ garlingDegree m hm0 ∧ m ∣ f ∧ m ∣ garlingDeriv f := by
    let m : ℚ[X] := Polynomial.X ^ 2 - Polynomial.C 2
    have hm_monic : m.Monic := Polynomial.monic_X_pow_sub_C (2 : ℚ) (by decide)
    have hm0 : m ≠ 0 := hm_monic.ne_zero
    have hm_deg : garlingDegree m hm0 = 2 := by
      unfold garlingDegree
      exact Polynomial.natDegree_X_pow_sub_C
    exact ⟨m, hm0, by omega, ⟨m, by dsimp [f, m]; ring⟩,
      ⟨Polynomial.C 4 * Polynomial.X, by rw [hdf]; dsimp [m]; ring⟩⟩
  -- Next-to-leading coefficient of `(X - C α)^k` for `k ≥ 1` is `-(k : L) * α`.
  have hdeg_sub_pow : ∀ (α : L) (k : ℕ), ((Polynomial.X - Polynomial.C α) ^ k).natDegree = k := by
    intro α k
    rw [(Polynomial.monic_X_sub_C α).natDegree_pow k, Polynomial.natDegree_X_sub_C, mul_one]
  have hcoeff_sub_pow :
      ∀ (α : L) (k : ℕ), 1 ≤ k →
        ((Polynomial.X - Polynomial.C α) ^ k).coeff (k - 1) = -(k : L) * α := by
    intro α k hk
    induction k with
    | zero => omega
    | succ m ihm =>
      rcases m with _ | m
      · simp
      · have hm1 : 1 ≤ m + 1 := Nat.succ_pos m
        have hih := ihm hm1
        have hmon : ((Polynomial.X - Polynomial.C α) ^ (m + 1)).Monic :=
          (Polynomial.monic_X_sub_C α).pow (m + 1)
        have hdeg : ((Polynomial.X - Polynomial.C α) ^ (m + 1)).natDegree = m + 1 :=
          hdeg_sub_pow α (m + 1)
        have hih' : ((Polynomial.X - Polynomial.C α) ^ (m + 1)).coeff m =
            -((m + 1 : ℕ) : L) * α := hih
        have hlead : ((Polynomial.X - Polynomial.C α) ^ (m + 1)).coeff (m + 1) = 1 := by
          rw [← hmon.leadingCoeff, Polynomial.leadingCoeff, hdeg]
        rw [pow_succ]
        change (((Polynomial.X - Polynomial.C α) ^ (m + 1) *
            (Polynomial.X - Polynomial.C α)).coeff (m + 1)) =
          -((m + 1 + 1 : ℕ) : L) * α
        rw [mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
          mul_comm _ (Polynomial.C α), Polynomial.coeff_C_mul, hih', hlead]
        push_cast
        ring
  -- Any `α ∈ L` with `(X - C α) ∣ f` satisfies `α² = 2` and hence `α ∉ ℚ`.
  have hroot_not_rat :
      ∀ α : L, (Polynomial.X - Polynomial.C α) ∣ f.map (algebraMap ℚ L) →
        ∀ q : ℚ, algebraMap ℚ L q ≠ α := by
    intro α hdvd q hq
    have hev : (f.map (algebraMap ℚ L)).eval α = 0 := Polynomial.dvd_iff_isRoot.mp hdvd
    rw [hfL_fac] at hev
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)] at hev
    rcases hev with hsub | hadd
    · exact hr2_not_rat q (hq.trans (sub_eq_zero.mp hsub))
    · exact hmr2_not_rat q (hq.trans (eq_neg_of_add_eq_zero_left hadd))
  have hno_range :
      ¬ ∃ (α : L) (k : ℕ), 1 < k ∧
        (Polynomial.X - Polynomial.C α) ^ k ∣ f.map (algebraMap ℚ L) ∧
        (Polynomial.X - Polynomial.C α) ^ k ∈ Set.range (Polynomial.map (algebraMap ℚ L)) := by
    rintro ⟨α, k, hk1, hdvd, g, hg⟩
    have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ f.map (algebraMap ℚ L) :=
      dvd_trans (dvd_pow_self _ (by omega)) hdvd
    have hc := congrArg (fun p : L[X] => p.coeff (k - 1)) hg
    rw [Polynomial.coeff_map, hcoeff_sub_pow α k (by omega)] at hc
    have hkL : (k : L) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hα_eq : algebraMap ℚ L (-g.coeff (k - 1) / (k : ℚ)) = α := by
      rw [map_div₀, map_neg, map_natCast, hc]
      field_simp [hkL]
    exact hroot_not_rat α hdvd1 (-g.coeff (k - 1) / (k : ℚ)) hα_eq
  have hnot_lit : ¬ HasLiteralPrintedRepeatedRootInBasePoly ℚ L f := by
    rintro ⟨α, k, g, hk1, hfac⟩
    have hdvd : (Polynomial.X - Polynomial.C α) ^ k ∣ f.map (algebraMap ℚ L) :=
      ⟨g.map (algebraMap ℚ L), hfac⟩
    have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ f.map (algebraMap ℚ L) :=
      dvd_trans (dvd_pow_self _ (by omega)) hdvd
    have hfL0 : f.map (algebraMap ℚ L) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ L).injective).mpr hf0
    have hgL0 : g.map (algebraMap ℚ L) ≠ 0 := fun h0 => hfL0 (by rw [hfac, h0, mul_zero])
    have hf_deg4 : (f.map (algebraMap ℚ L)).natDegree = 4 := by
      rw [hfL_fac, Polynomial.natDegree_mul
        (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero r2))
        (pow_ne_zero 2 (Polynomial.monic_X_add_C r2).ne_zero)]
      have h1 : ((Polynomial.X - Polynomial.C r2) ^ 2).natDegree = 2 := hdeg_sub_pow r2 2
      have h2 : ((Polynomial.X + Polynomial.C r2) ^ 2).natDegree = 2 := by
        rw [(Polynomial.monic_X_add_C r2).natDegree_pow 2, Polynomial.natDegree_X_add_C, mul_one]
      omega
    have hk_deg : ((Polynomial.X - Polynomial.C α) ^ k).natDegree = k := hdeg_sub_pow α k
    have hgL_deg : (g.map (algebraMap ℚ L)).natDegree = g.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ L).injective g
    have hsum_deg : k + g.natDegree = 4 := by
      have h1 := congrArg Polynomial.natDegree hfac
      rw [hf_deg4, Polynomial.natDegree_mul (pow_ne_zero k (Polynomial.X_sub_C_ne_zero α)) hgL0,
        hk_deg, hgL_deg] at h1
      omega
    have hp_monic : ((Polynomial.X - Polynomial.C α) ^ k).Monic :=
      (Polynomial.monic_X_sub_C α).pow k
    have hfL_monic : (f.map (algebraMap ℚ L)).Monic := hf_monic.map (algebraMap ℚ L)
    have hg_lc1 : g.leadingCoeff = 1 := by
      apply (algebraMap ℚ L).injective
      have h1 := congrArg Polynomial.leadingCoeff hfac
      rw [hfL_monic.leadingCoeff, Polynomial.leadingCoeff_mul, hp_monic.leadingCoeff, one_mul,
        Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ L).injective] at h1
      exact h1.symm.trans (map_one (algebraMap ℚ L)).symm
    have hf_coeff3 : (f.map (algebraMap ℚ L)).coeff 3 = 0 := by
      rw [Polynomial.coeff_map]
      have hf_exp : f = Polynomial.X ^ 4 - Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 4 := by
        dsimp [f]
        simp only [map_ofNat]
        ring
      rw [hf_exp]
      simp [Polynomial.coeff_X_pow]
    let P : L[X] := (Polynomial.X - Polynomial.C α) ^ k
    let Q : L[X] := g.map (algebraMap ℚ L)
    have hP_gt : ∀ i : ℕ, k < i → P.coeff i = 0 := fun i hi =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (hk_deg.symm ▸ hi)
    have hQ_gt : ∀ j : ℕ, g.natDegree < j → Q.coeff j = 0 := fun j hj =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (hgL_deg.symm ▸ hj)
    have hP_top : P.coeff k = 1 := by rw [← hk_deg, Polynomial.coeff_natDegree]; exact hp_monic.leadingCoeff
    have hQ_top : Q.coeff g.natDegree = 1 := by
      rw [Polynomial.coeff_map, ← Polynomial.leadingCoeff, hg_lc1, map_one]
    have hRHS_coeff3 : ∃ c : ℚ, (P * Q).coeff 3 = -(k : L) * α + algebraMap ℚ L c := by
      have hk_cases : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk_cases with rfl | rfl | rfl
      · have hgd : g.natDegree = 2 := by omega
        refine ⟨g.coeff 1, ?_⟩
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        have hP01 : P.coeff 1 = -(2 : L) * α := hcoeff_sub_pow α 2 (by decide)
        have hP2 : P.coeff 2 = 1 := hP_top
        have hP3 : P.coeff 3 = 0 := hP_gt 3 (by decide)
        have hQ2 : Q.coeff 2 = 1 := hgd ▸ hQ_top
        have hQ3 : Q.coeff 3 = 0 := hQ_gt 3 (by omega)
        have hQ1 : Q.coeff 1 = algebraMap ℚ L (g.coeff 1) := Polynomial.coeff_map _ _
        rw [hP01, hP2, hP3, hQ2, hQ3, hQ1]
        ring
      · have hgd : g.natDegree = 1 := by omega
        refine ⟨g.coeff 0, ?_⟩
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        have hP2 : P.coeff 2 = -(3 : L) * α := hcoeff_sub_pow α 3 (by decide)
        have hP3 : P.coeff 3 = 1 := hP_top
        have hQ1 : Q.coeff 1 = 1 := hgd ▸ hQ_top
        have hQ2 : Q.coeff 2 = 0 := hQ_gt 2 (by omega)
        have hQ3 : Q.coeff 3 = 0 := hQ_gt 3 (by omega)
        have hQ0 : Q.coeff 0 = algebraMap ℚ L (g.coeff 0) := Polynomial.coeff_map _ _
        rw [hP2, hP3, hQ1, hQ2, hQ3, hQ0]
        ring
      · have hgd : g.natDegree = 0 := by omega
        refine ⟨0, ?_⟩
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        have hP3 : P.coeff 3 = -(4 : L) * α := hcoeff_sub_pow α 4 (by decide)
        have hQ0 : Q.coeff 0 = 1 := hgd ▸ hQ_top
        have hQ1 : Q.coeff 1 = 0 := hQ_gt 1 (by omega)
        have hQ2 : Q.coeff 2 = 0 := hQ_gt 2 (by omega)
        have hQ3 : Q.coeff 3 = 0 := hQ_gt 3 (by omega)
        rw [hP3, hQ0, hQ1, hQ2, hQ3, map_zero (algebraMap ℚ L)]
        ring
    obtain ⟨c, hc⟩ := hRHS_coeff3
    have h0 : -(k : L) * α + algebraMap ℚ L c = 0 := by
      rw [← hc, ← hfac, hf_coeff3]
    have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hkL : (k : L) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hα_rat : algebraMap ℚ L (c / (k : ℚ)) = α := by
      have h1 : (k : L) * α = algebraMap ℚ L c := by linear_combination -h0
      rw [map_div₀, map_natCast, ← h1]
      field_simp [hkL]
    exact hroot_not_rat α hdvd1 (c / (k : ℚ)) hα_rat
  exact ⟨hf0, hsf, hrep, hii, hiii, hnot_lit, hno_range⟩

/-- **Theorem 10.5** (§10.4, printed pp. 85–86 / PDF pp. 93–94; see `QUEUE.md` for the p. 85
`in K[x]` prose-definition slip):
*"Suppose that `f` is a non-zero element of `K[x]` and that `L : K` is a splitting field for `f`.
The following are equivalent:
(i) `f` has a repeated root in `L`;
(ii) there exists `α` in `L` for which `f(α) = (Df)(α) = 0`;
(iii) there exists `m` in `K[x]`, with `degree m ≥ 1`, such that `m ∣ f` and `m ∣ Df`."*

Proved step-by-step following Garling's cycle `(i) ⟹ (ii) ⟹ (iii) ⟹ (i)` on p. 86 using
`HasGarlingRepeatedRoot` (`(x - α)^k ∣ f` in `L[x]`, matching p. 86 l. 1). -/
theorem theorem_10_5 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f ≠ 0) (hsf : IsGarlingSplittingFieldExtension K L f) :
    (HasGarlingRepeatedRoot K L f ↔
      ∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0) ∧
    ((∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0) ↔
      ∃ (m : K[X]) (hm0 : m ≠ 0),
        1 ≤ garlingDegree m hm0 ∧ m ∣ f ∧ m ∣ garlingDeriv f) := by
  -- (i) ⟹ (ii)
  have hi_imp_hii :
      HasGarlingRepeatedRoot K L f →
        ∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0 := by
    rintro ⟨α, k, hk1, g, hfac⟩
    have hk2 : 2 ≤ k := by omega
    have hdvd2 : (Polynomial.X - Polynomial.C α) ^ 2 ∣ f.map (algebraMap K L) :=
      ⟨(Polynomial.X - Polynomial.C α) ^ (k - 2) * g, by
        rw [hfac, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hk2]⟩
    obtain ⟨h, hh⟩ := hdvd2
    refine ⟨α, ?_, ?_⟩
    · rw [Polynomial.aeval_def, ← Polynomial.eval_map, hh]
      simp
    · rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← garlingDeriv_map, hh, garlingDeriv_mul,
        garlingDeriv_pow, garlingDeriv_eq_derivative (Polynomial.X - Polynomial.C α),
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]
      simp
  -- (ii) ⟹ (iii)
  have hii_imp_hiii :
      (∃ α : L, Polynomial.aeval α f = 0 ∧ Polynomial.aeval α (garlingDeriv f) = 0) →
        ∃ (m : K[X]) (hm0 : m ≠ 0),
          1 ≤ garlingDegree m hm0 ∧ m ∣ f ∧ m ∣ garlingDeriv f := by
    rintro ⟨α, hfα, hdfα⟩
    have halg : IsGarlingAlgebraic K α := ⟨f, hf, hfα⟩
    have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp halg
    let m : K[X] := minpoly K α
    have hm_irr : Irreducible m := minpoly.irreducible hint
    have hm0 : m ≠ 0 := hm_irr.ne_zero
    have hm_deg : 1 ≤ garlingDegree m hm0 := minpoly.natDegree_pos hint
    exact ⟨m, hm0, hm_deg, minpoly.dvd K α hfα, minpoly.dvd K α hdfα⟩
  -- (iii) ⟹ (i)
  have hiii_imp_hi :
      (∃ (m : K[X]) (hm0 : m ≠ 0),
        1 ≤ garlingDegree m hm0 ∧ m ∣ f ∧ m ∣ garlingDeriv f) →
        HasGarlingRepeatedRoot K L f := by
    rintro ⟨m, hm0, hm_deg, hmf, hmdf⟩
    have hf_sp : (f.map (algebraMap K L)).Splits :=
      (garlingSplitsOver_iff_splits K L f).mp hsf.1
    have hfL0 : f.map (algebraMap K L) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf
    have hmL_dvd : m.map (algebraMap K L) ∣ f.map (algebraMap K L) :=
      Polynomial.map_dvd (algebraMap K L) hmf
    have hmL_sp : (m.map (algebraMap K L)).Splits :=
      Polynomial.Splits.of_dvd hf_sp hfL0 hmL_dvd
    have hmL0 : m.map (algebraMap K L) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hm0
    have hmL_deg : 1 ≤ (m.map (algebraMap K L)).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]
      exact hm_deg
    -- Since `m` splits over `L` and has degree `≥ 1`, `m` has a root `α ∈ L`.
    obtain ⟨n, c, αs, hexpm⟩ := (garlingSplitsOver_iff_splits K L m).mpr hmL_sp
    obtain ⟨_, _, hn_deg, hroots⟩ := garlingSplitsExplicit_props hm0 hexpm
    have hn_pos : 0 < n := by omega
    let α : L := αs ⟨0, hn_pos⟩
    have hα_root_m : (m.map (algebraMap K L)).IsRoot α := by
      have hmem : α ∈ m.rootSet L := hroots ▸ ⟨⟨0, hn_pos⟩, rfl⟩
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact (Polynomial.mem_rootSet.mp hmem).2
    have hlin_dvd_m : (Polynomial.X - Polynomial.C α) ∣ m.map (algebraMap K L) :=
      Polynomial.dvd_iff_isRoot.mpr hα_root_m
    obtain ⟨q, hq⟩ := dvd_trans hlin_dvd_m hmL_dvd
    -- Differentiate `f.map i = (X - C α) * q` in `L[x]`.
    have hdfL : (garlingDeriv f).map (algebraMap K L) =
        q + (Polynomial.X - Polynomial.C α) * garlingDeriv q := by
      rw [← garlingDeriv_map, hq, garlingDeriv_mul,
        garlingDeriv_eq_derivative (Polynomial.X - Polynomial.C α),
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, one_mul]
    have hlin_dvd_df : (Polynomial.X - Polynomial.C α) ∣ (garlingDeriv f).map (algebraMap K L) :=
      dvd_trans hlin_dvd_m (Polynomial.map_dvd (algebraMap K L) hmdf)
    have hdf_eval0 : ((garlingDeriv f).map (algebraMap K L)).eval α = 0 :=
      Polynomial.dvd_iff_isRoot.mp hlin_dvd_df
    have hq_eval0 : q.eval α = 0 := by
      rw [hdfL, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] at hdf_eval0
      exact hdf_eval0
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hq_eval0
    refine ⟨α, 2, by decide, r, ?_⟩
    rw [hq, hr, sq, mul_assoc]
  exact ⟨⟨hi_imp_hii, fun hii => hiii_imp_hi (hii_imp_hiii hii)⟩,
    ⟨hii_imp_hiii, fun hiii => hi_imp_hii (hiii_imp_hi hiii)⟩⟩

/-- Helper characterizing `garlingDeriv f = 0` over any field `K` (§10.4, printed p. 86 / PDF p. 94):
`Df = 0` iff either `deg f = 0` (every `j ≥ 1` has `f.coeff j = 0`) or `char K = p > 0` divides every
exponent `j ≥ 1` with `f.coeff j ≠ 0`. -/
theorem garlingDeriv_eq_zero_iff_char_dvd {K : Type*} [Field K] (f : K[X]) :
    garlingDeriv f = 0 ↔ ∀ j : ℕ, 1 ≤ j → f.coeff j ≠ 0 → ringChar K ∣ j := by
  rw [garlingDeriv_eq_derivative]
  constructor
  · intro hdf0 j hj hfj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hc := congrArg (fun p : K[X] => p.coeff m) hdf0
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, mul_eq_zero] at hc
    rcases hc with hfm | hm0
    · exact (hfj hfm).elim
    · have hcast : ((m + 1 : ℕ) : K) = 0 := by exact_mod_cast hm0
      exact (ringChar.spec K (m + 1)).mp hcast
  · intro h
    ext m
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero]
    by_cases hfm : f.coeff (m + 1) = 0
    · rw [hfm, zero_mul]
    · have hdvd : ringChar K ∣ (m + 1) := h (m + 1) (Nat.succ_pos m) hfm
      have hcast : ((m + 1 : ℕ) : K) = 0 := (ringChar.spec K (m + 1)).mpr hdvd
      have hcast' : (m : K) + 1 = 0 := by exact_mod_cast hcast
      rw [hcast', mul_zero]

/-- Helper converting `garlingDeriv f = 0` in `char K = p > 0` into `f = g(x^p)` (`Polynomial.expand K p g`)
and explicit sum `a₀ + a₁ x^p + ⋯ + a_n x^{np}` (§10.4, p. 86 & §10.6, p. 88). -/
theorem eq_sum_X_pow_mul_char_of_garlingDeriv_eq_zero {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp : 0 < p) {f : K[X]} (hdf : garlingDeriv f = 0) :
    (∃ (n : ℕ) (a : Fin (n + 1) → K),
      f = ∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ ((i : ℕ) * p)) ∧
    (∃ g : K[X], f = Polynomial.expand K p g) := by
  have hdvd_all := (garlingDeriv_eq_zero_iff_char_dvd f).mp hdf
  let n : ℕ := f.natDegree / p
  let a : Fin (n + 1) → K := fun i => f.coeff ((i : ℕ) * p)
  have hf_sum : f = ∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ ((i : ℕ) * p) := by
    ext k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases hfk : f.coeff k = 0
    · rw [hfk]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hik
      · subst hik
        exact hfk
      · rfl
    · have hk_le : k ≤ f.natDegree := Polynomial.le_natDegree_of_ne_zero hfk
      have hp_dvd_k : p ∣ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · exact dvd_zero p
        · exact hchar ▸ hdvd_all k hk_pos hfk
      obtain ⟨q, rfl⟩ := hp_dvd_k
      have hq_le' : q ≤ n := (Nat.le_div_iff_mul_le hp).mpr (by linarith)
      let iq : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hq_le'⟩
      rw [Finset.sum_eq_single iq]
      · have hiq : p * q = (iq : ℕ) * p := mul_comm p q
        simp only [hiq, ↓reduceIte]
        rfl
      · intro j _ hj_ne
        split_ifs with hjp
        · exfalso
          apply hj_ne
          ext
          have hmul : (j : ℕ) * p = q * p := by linarith
          exact Nat.eq_of_mul_eq_mul_right hp hmul
        · rfl
      · intro hnot
        exact (hnot (Finset.mem_univ iq)).elim
  refine ⟨⟨n, a, hf_sum⟩, ?_⟩
  let g : K[X] := ∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
  refine ⟨g, ?_⟩
  rw [hf_sum]
  dsimp [g]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X, ← pow_mul, mul_comm p (i : ℕ)]

/-- **Theorem 10.6** (§10.4, printed p. 86 / PDF p. 94):
*"Suppose that `f ∈ K[x]` is irreducible. Then `f` is not separable if and only if `char K = p > 0`
and `f` has the form `f = a₀ + a₁ x^p + a₂ x^{2p} + ⋯ + a_n x^{np}`."*

Proved directly following Garling's proof on p. 86 via `Theorem 10.5 (iii)`. -/
theorem theorem_10_6 {K : Type u} [Field K] {f : K[X]} (hf : Irreducible f) :
    ¬ IsGarlingSeparablePoly f ↔
      ∃ p : ℕ, ringChar K = p ∧ 0 < p ∧
        ∃ (n : ℕ) (a : Fin (n + 1) → K),
          f = ∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ ((i : ℕ) * p) := by
  obtain ⟨L, instFL, instAL, hsf, _⟩ := theorem_7_3_natDegree f
  let _ : Field L := instFL
  let _ : Algebra K L := instAL
  rw [irreducible_not_separable_iff_hasGarlingRepeatedRoot hf hsf]
  have h105 := theorem_10_5 hf.ne_zero hsf
  rw [h105.1, h105.2]
  constructor
  · rintro ⟨m, hm0, hm_deg, hmf, hmdf⟩
    have hm_nu : ¬ IsUnit m := by
      intro hu
      have hd0 : m.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      unfold garlingDegree at hm_deg
      omega
    have hm_irr : Irreducible m := by
      rcases hf.isUnit_or_isUnit (Classical.choose_spec hmf) with hu | hv
      · exact (hm_nu hu).elim
      · have hassoc : Associated m f := ⟨hv.unit, (Classical.choose_spec hmf).symm⟩
        exact hassoc.symm.irreducible hf
    have hassoc : Associated f m := hf.associated_of_dvd hm_irr (by
      have h := hm_irr.associated_of_dvd hf hmf
      exact h.symm.dvd)
    have hfd : f ∣ garlingDeriv f := hassoc.dvd.trans hmdf
    -- As `deg Df < deg f` when `Df ≠ 0`, `f ∣ Df` forces `Df = 0`.
    have hdf0 : garlingDeriv f = 0 := by
      by_contra hne0
      have hle : f.natDegree ≤ (garlingDeriv f).natDegree :=
        Polynomial.natDegree_le_of_dvd hfd hne0
      rw [garlingDeriv_eq_derivative] at hle
      have hlt : (Polynomial.derivative f).natDegree < f.natDegree :=
        Polynomial.natDegree_derivative_lt hf.natDegree_pos.ne'
      omega
    -- Since `deg f ≥ 1`, `f` has a non-zero coefficient at `deg f ≥ 1`, forcing `ringChar K > 0`.
    have hf_deg_pos : 1 ≤ f.natDegree := hf.natDegree_pos
    have hflc : f.coeff f.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf.ne_zero
    have hdvd_deg : ringChar K ∣ f.natDegree :=
      (garlingDeriv_eq_zero_iff_char_dvd f).mp hdf0 f.natDegree hf_deg_pos hflc
    have hp_pos : 0 < ringChar K := by
      by_contra hle0
      have h0 : ringChar K = 0 := by omega
      rw [h0, zero_dvd_iff] at hdvd_deg
      omega
    refine ⟨ringChar K, rfl, hp_pos, ?_⟩
    exact (eq_sum_X_pow_mul_char_of_garlingDeriv_eq_zero rfl hp_pos hdf0).1
  · rintro ⟨p, hchar, hp_pos, n, a, hf_eq⟩
    have hdf0 : garlingDeriv f = 0 := by
      rw [hf_eq, garlingDeriv_eq_derivative, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
      have hpK : (p : K) = 0 := hchar ▸ ringChar.Nat.cast_ringChar
      have hmul0 : (((i : ℕ) * p : ℕ) : K) = 0 := by
        rw [Nat.cast_mul, hpK, mul_zero]
      rw [hmul0, map_zero, zero_mul, mul_zero]
    exact ⟨f, hf.ne_zero, hf.natDegree_pos, dvd_rfl, hdf0 ▸ dvd_zero f⟩

/-- `Polynomial.expand` and `IsGarlingIrreducible` companion to **Theorem 10.6** (§10.4, p. 86). -/
theorem theorem_10_6_expand {K : Type u} [Field K] {f : K[X]} (hf : IsGarlingIrreducible f) :
    ¬ IsGarlingSeparablePoly f ↔
      0 < ringChar K ∧ ∃ g : K[X], f = Polynomial.expand K (ringChar K) g := by
  have hfirr : Irreducible f := (isGarlingIrreducible_iff f).mp hf
  rw [theorem_10_6 hfirr]
  constructor
  · rintro ⟨p, rfl, hp, n, a, hf_eq⟩
    refine ⟨hp, ∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ), ?_⟩
    rw [hf_eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X, ← pow_mul, mul_comm (ringChar K) (i : ℕ)]
  · rintro ⟨hp, g, rfl⟩
    refine ⟨ringChar K, rfl, hp, g.natDegree, fun i => g.coeff i.val, ?_⟩
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow g]
    rw [map_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X, ← pow_mul, mul_comm (ringChar K) (i : ℕ)]

/-- **Corollary** [to Theorem 10.6] (§10.4, printed p. 86 / PDF p. 94):
*"If `char K = 0`, all polynomials in `K[x]` are separable."*

Holds literally for **every** polynomial `f ∈ K[x]` (including `f = 0`, non-zero constants, and
polynomials with repeated factors such as `(x - 1)^2`), directly justifying Garling's §10.1
irreducible-factor definition `IsGarlingSeparablePoly` (`BRIEF.md` Flag 2). -/
theorem corollary_to_theorem_10_6 {K : Type u} [Field K] (hchar : ringChar K = 0)
    (f : K[X]) : IsGarlingSeparablePoly f := by
  intro g hg _
  by_contra hnot_sep
  have hnot_poly : ¬ IsGarlingSeparablePoly g := by
    rw [isGarlingSeparablePoly_of_irreducible_iff hg, ← isGarlingSeparableIrreducible_iff_separable hg]
    exact hnot_sep
  obtain ⟨p, hp_eq, hp_pos, _⟩ := (theorem_10_6 hg).mp hnot_poly
  omega

/-- `[CharZero K]` typeclass companion to **Corollary** [to Theorem 10.6] (§10.4, p. 86). -/
theorem corollary_to_theorem_10_6_charZero (K : Type u) [Field K] [CharZero K] (f : K[X]) :
    IsGarlingSeparablePoly f :=
  corollary_to_theorem_10_6 (ringChar.eq_zero) f

/-- Iterated formal derivative of `(x - α)^m`:
`D^k ((x - α)^m) = m.descFactorial k • (x - α)^{m - k}` (used for both `Exercise 10.2` Taylor's
formula and `Exercise 10.3` exact root multiplicity). -/
theorem garlingDeriv_iterate_X_sub_C_pow {R : Type*} [CommRing R] (α : R) (m : ℕ) :
    ∀ k : ℕ,
      garlingDeriv^[k] ((Polynomial.X - Polynomial.C α) ^ m) =
        (m.descFactorial k : R[X]) * (Polynomial.X - Polynomial.C α) ^ (m - k)
  | 0 => by simp
  | k + 1 => by
    rw [Function.iterate_succ_apply', garlingDeriv_iterate_X_sub_C_pow α m k]
    by_cases hkm : k < m
    · have hsub_pos : 1 ≤ m - k := by omega
      have hcast : (m.descFactorial k : R[X]) = Polynomial.C (m.descFactorial k : R) :=
        (Polynomial.C_eq_natCast _).symm
      rw [hcast, garlingDeriv_C_mul, garlingDeriv_pow,
        garlingDeriv_eq_derivative (Polynomial.X - Polynomial.C α),
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, mul_one, ← Polynomial.C_eq_natCast (m - k), ← mul_assoc, ← Polynomial.C_mul,
        ← Nat.cast_mul, mul_comm (m.descFactorial k) (m - k), ← Nat.descFactorial_succ,
        Polynomial.C_eq_natCast, Nat.sub_sub]
    · have hge : m ≤ k := Nat.le_of_not_lt hkm
      have hsub0 : m - k = 0 := Nat.sub_eq_zero_of_le hge
      have hsub1 : m - (k + 1) = 0 := Nat.sub_eq_zero_of_le (Nat.le_succ_of_le hge)
      have hdesc0 : m.descFactorial (k + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_of_le hge)
      rw [hsub0, hsub1, hdesc0, pow_zero, mul_one, Nat.cast_zero, zero_mul,
        garlingDeriv_eq_derivative, Polynomial.derivative_natCast]

/-- Evaluating `D^k ((x - α)^m)` at `α` yields `m!` when `k = m` and `0` otherwise. -/
theorem eval_garlingDeriv_iterate_X_sub_C_pow {R : Type*} [CommRing R] (α : R) (m k : ℕ) :
    (garlingDeriv^[k] ((Polynomial.X - Polynomial.C α) ^ m)).eval α =
      if k = m then (m.factorial : R) else 0 := by
  rw [garlingDeriv_iterate_X_sub_C_pow, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  by_cases hkm : k = m
  · subst hkm
    simp [Nat.descFactorial_self]
  · split_ifs
    rcases lt_or_gt_of_ne hkm with hlt | hgt
    · have hpos : m - k ≠ 0 := by omega
      rw [zero_pow hpos, mul_zero]
    · have hdesc0 : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hgt
      rw [hdesc0, Nat.cast_zero, zero_mul]

/-- Helper: under `char K = 0` or `char K > n`, `(k! : K) ≠ 0` for every `k ≤ n`. -/
theorem factorial_cast_ne_zero_of_char {K : Type*} [Field K] {n : ℕ}
    (hchar : ringChar K = 0 ∨ n < ringChar K) {k : ℕ} (hk : k ≤ n) :
    (k.factorial : K) ≠ 0 := by
  intro h0
  have hdvd : ringChar K ∣ k.factorial := (ringChar.spec K k.factorial).mp h0
  rcases hchar with hc0 | hlt
  · rw [hc0, zero_dvd_iff] at hdvd
    exact (Nat.factorial_ne_zero k) hdvd
  · have hprime : Nat.Prime (ringChar K) :=
      (theorem_3_17 K).2 (by omega) |>.1
    have hle : ringChar K ≤ k := (Nat.Prime.dvd_factorial hprime).mp hdvd
    omega

/-- Degree-`≤ n` Taylor expansion (covers all `f ∈ K[x]` with `f.natDegree ≤ n`, including `f = 0`). -/
theorem exercise_10_2_le {K : Type*} [Field K] {f : K[X]} {n : ℕ}
    (hdeg : f.natDegree ≤ n) (hchar : ringChar K = 0 ∨ n < ringChar K) (α : K) :
    f = ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (((garlingDeriv^[k] f).eval α) / (k.factorial : K)) *
        (Polynomial.X - Polynomial.C α) ^ k := by
  let g : K[X] := f.comp (Polynomial.X + Polynomial.C α)
  have hg_deg : g.natDegree ≤ n := by
    calc g.natDegree ≤ f.natDegree * (Polynomial.X + Polynomial.C α).natDegree :=
          Polynomial.natDegree_comp_le
      _ = f.natDegree * 1 := by rw [Polynomial.natDegree_X_add_C]
      _ = f.natDegree := mul_one _
      _ ≤ n := hdeg
  have hf_eq_g : f = ∑ m ∈ Finset.range (n + 1),
      Polynomial.C (g.coeff m) * (Polynomial.X - Polynomial.C α) ^ m := by
    have hcomp : g.comp (Polynomial.X - Polynomial.C α) = f := by
      dsimp [g]
      rw [Polynomial.comp_assoc]
      have h1 : (Polynomial.X + Polynomial.C α).comp (Polynomial.X - Polynomial.C α) = Polynomial.X := by
        simp
      rw [h1, Polynomial.comp_X]
    rw [← hcomp]
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' g (Nat.lt_succ_of_le hg_deg)]
    rw [Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
  -- Compute `(D^k f)(α) = g.coeff k * k!` for every `k ≤ n`.
  have hiter_sum : ∀ (d : ℕ) (s : Finset ℕ) (F : ℕ → K[X]),
      garlingDeriv^[d] (∑ i ∈ s, F i) = ∑ i ∈ s, garlingDeriv^[d] (F i) := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d ihd => intro s F; simp [Function.iterate_succ_apply', ihd]
  have hiter_C_mul : ∀ (d : ℕ) (a : K) (p : K[X]),
      garlingDeriv^[d] (Polynomial.C a * p) = Polynomial.C a * garlingDeriv^[d] p := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d ihd => intro a p; simp [Function.iterate_succ_apply', ihd]
  have hderiv_eval : ∀ k ∈ Finset.range (n + 1),
      (garlingDeriv^[k] f).eval α = g.coeff k * (k.factorial : K) := by
    intro k hk
    have hmap_sum :
        garlingDeriv^[k] f = ∑ m ∈ Finset.range (n + 1),
          Polynomial.C (g.coeff m) * garlingDeriv^[k] ((Polynomial.X - Polynomial.C α) ^ m) := by
      conv_lhs => rw [hf_eq_g]
      exact (hiter_sum k _ _).trans
        (Finset.sum_congr rfl fun m _ => hiter_C_mul k (g.coeff m) _)
    rw [hmap_sum, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_C, eval_garlingDeriv_iterate_X_sub_C_pow,
      mul_ite, mul_zero]
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hmk
      split_ifs with h
      · exact (hmk h.symm).elim
      · rfl
    · intro hnot
      exact (hnot hk).elim
  have hderiv_eval' : ∀ k ∈ Finset.range (n + 1),
      g.coeff k = ((garlingDeriv^[k] f).eval α) / (k.factorial : K) := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hfac0 : (k.factorial : K) ≠ 0 := factorial_cast_ne_zero_of_char hchar hk_le
    rw [hderiv_eval k hk, mul_div_cancel_right₀ _ hfac0]
  conv_lhs => rw [hf_eq_g]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hderiv_eval' k hk]

/-- **Exercise 10.2** (§10.4, printed p. 86 / PDF p. 94 — *Taylor's formula*):
*"Suppose that `f` is a polynomial in `K[x]` of degree `n` and that either `char K = 0` or
`char K > n`. Suppose that `α ∈ K`. Establish Taylor's formula:
`f = f(α) + Df(α)(x - α) + (D²f(α) / 2!)(x - α)² + ⋯ + (D^n f(α) / n!)(x - α)^n`."* -/
theorem exercise_10_2 {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) {n : ℕ}
    (hdeg : garlingDegree f hf = n) (hchar : ringChar K = 0 ∨ n < ringChar K) (α : K) :
    f = ∑ k ∈ Finset.range (n + 1),
      Polynomial.C (((garlingDeriv^[k] f).eval α) / (k.factorial : K)) *
        (Polynomial.X - Polynomial.C α) ^ k :=
  exercise_10_2_le (le_of_eq hdeg) hchar α

/-! ### Exercise 10.3: Exact Root Multiplicity and Omitted `= 0` Fidelity Hold (§10.4, p. 87) -/

/-- Exact divisibility multiplicity `(x - α)^r ∣ f` and `(x - α)^{r+1} ∤ f` in `K[x]`
(`BRIEF.md` Flag 4; *multiplicity* / *exact multiplicity* is used in `Exercises 10.3` and `10.11`
without an earlier standalone prose definition in Chapter 10). -/
def HasExactRootMultiplicity {K : Type*} [CommRing K] (f : K[X]) (α : K) (r : ℕ) : Prop :=
  (Polynomial.X - Polynomial.C α) ^ r ∣ f ∧
    ¬ ((Polynomial.X - Polynomial.C α) ^ (r + 1) ∣ f)

/-- Root-presupposing variant of exact multiplicity (`α` is a root of `f` and has exact multiplicity
`r`, hence `r ≥ 1`). -/
def IsRootOfExactMultiplicity {K : Type*} [CommRing K] (f : K[X]) (α : K) (r : ℕ) : Prop :=
  f.IsRoot α ∧ HasExactRootMultiplicity f α r

/-- Exact bridge between `HasExactRootMultiplicity f α r` and Mathlib's `Polynomial.rootMultiplicity`
for every non-zero polynomial `f ∈ K[x]` and every `r : ℕ` (including `r = 0`). -/
theorem hasExactRootMultiplicity_iff_rootMultiplicity {K : Type*} [Field K] {f : K[X]}
    (hf : f ≠ 0) (α : K) (r : ℕ) :
    HasExactRootMultiplicity f α r ↔ f.rootMultiplicity α = r := by
  unfold HasExactRootMultiplicity
  rw [← Polynomial.le_rootMultiplicity_iff hf, ← Polynomial.le_rootMultiplicity_iff hf]
  omega

/-- **Counterexamples to the literal printed right-hand side of `Exercise 10.3`**
(§10.4, printed p. 87 / PDF p. 95 — `BRIEF.md` Flag 4; see `QUEUE.md`):
On p. 87, the displayed condition prints
`f(α) = Df(α) = ⋯ = D^{r-1}f(α)   and   D^r f(α) ≠ 0`
omitting **`= 0`** at the end of the equality chain (`∃ c, ∀ j < r, D^j f(α) = c`):
1. At `r = 1`: on `K = ℚ`, `f = x` (`n = 1`), `α = 1`, the 1-term chain `f(α)` imposes no equality
   condition and `(Df)(1) = 1 ≠ 0`, yet `f(1) = 1 ≠ 0`, so `α = 1` is neither a root nor of exact
   multiplicity `1`.
2. At `r = 2` (`r ≥ 2`): on `K = ℚ`, `f = x² + x + 1` (`n = 2`), `α = 0`, we have
   `f(0) = 1 = (Df)(0)` and `(D²f)(0) = 2 ≠ 0`, satisfying the literal printed equality chain with
   common value `c = 1 ≠ 0`, yet `f(0) = 1 ≠ 0`, so `α = 0` is neither a root nor of exact
   multiplicity `2`. -/
theorem exercise_10_3_omitted_zero_counterexamples :
    (let f₁ : ℚ[X] := Polynomial.X
     ∃ hf₁ : f₁ ≠ 0,
       garlingDegree f₁ hf₁ = 1 ∧
       ringChar ℚ = 0 ∧
       (∃ c : ℚ, ∀ j < 1, (garlingDeriv^[j] f₁).eval (1 : ℚ) = c) ∧
       (garlingDeriv^[1] f₁).eval (1 : ℚ) ≠ 0 ∧
       ¬ f₁.IsRoot (1 : ℚ) ∧
       ¬ HasExactRootMultiplicity f₁ (1 : ℚ) 1) ∧
    (let f₂ : ℚ[X] := Polynomial.X ^ 2 + Polynomial.X + 1
     ∃ hf₂ : f₂ ≠ 0,
       garlingDegree f₂ hf₂ = 2 ∧
       ringChar ℚ = 0 ∧
       f₂.eval (0 : ℚ) = (garlingDeriv f₂).eval (0 : ℚ) ∧
       (garlingDeriv^[2] f₂).eval (0 : ℚ) ≠ 0 ∧
       ¬ f₂.IsRoot (0 : ℚ) ∧
       ¬ HasExactRootMultiplicity f₂ (0 : ℚ) 2) := by
  refine ⟨?_, ?_⟩
  · refine ⟨Polynomial.X_ne_zero, Polynomial.natDegree_X, ringChar.eq_zero,
      ⟨1, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      rw [hj0]
      simp only [Function.iterate_zero, id_eq, Polynomial.eval_X]
    · simp only [Function.iterate_one, garlingDeriv_eq_derivative, Polynomial.derivative_X,
        Polynomial.eval_one, ne_eq, one_ne_zero, not_false_eq_true]
    · rw [Polynomial.IsRoot.def, Polynomial.eval_X]
      exact one_ne_zero
    · rintro ⟨hdvd, _⟩
      rw [pow_one] at hdvd
      have h0 := Polynomial.dvd_iff_isRoot.mp hdvd
      rw [Polynomial.IsRoot.def, Polynomial.eval_X] at h0
      exact one_ne_zero h0
  · let f₂ : ℚ[X] := Polynomial.X ^ 2 + Polynomial.X + 1
    have hcoeff2 : f₂.coeff 2 = 1 := by
      simp only [f₂, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one]
      norm_num
    have hf₂0 : f₂ ≠ 0 := fun h0 => by
      have hc0 : f₂.coeff 2 = 0 := by rw [h0, Polynomial.coeff_zero]
      linarith
    have hdeg_le : f₂.natDegree ≤ 2 := by
      dsimp [f₂]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · rw [Polynomial.natDegree_X_pow]
        · rw [Polynomial.natDegree_X]; omega
      · rw [Polynomial.natDegree_one]; omega
    have hdeg : f₂.natDegree = 2 :=
      le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff2]; exact one_ne_zero))
    refine ⟨hf₂0, hdeg, ringChar.eq_zero, ?_, ?_, ?_, ?_⟩
    · simp only [garlingDeriv_eq_derivative, Polynomial.derivative_add,
        Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_one,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_zero]
      norm_num
    · simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
        garlingDeriv_eq_derivative, Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_one,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_zero]
      norm_num
    · rw [Polynomial.IsRoot.def]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      norm_num
    · rintro ⟨hdvd, _⟩
      have hdvd1 : (Polynomial.X - Polynomial.C (0 : ℚ)) ∣ f₂ :=
        dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hdvd
      have h0 := Polynomial.dvd_iff_isRoot.mp hdvd1
      rw [Polynomial.IsRoot.def] at h0
      simp only [f₂, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at h0
      norm_num at h0

/-- **Exercise 10.3 (all `0 ≤ r ≤ n` via `HasExactRootMultiplicity`)** (§10.4, printed p. 87 /
PDF p. 95, with repaired `= 0` condition; see `QUEUE.md`):
For any non-zero `f ∈ K[x]` of degree `n` under `char K = 0` or `char K > n`, any `α ∈ K`, and any
`r ≤ n` (including `r = 0`, where `HasExactRootMultiplicity f α 0 ↔ f(α) ≠ 0`),
`HasExactRootMultiplicity f α r ↔ (∀ j < r, (D^j f)(α) = 0) ∧ (D^r f)(α) ≠ 0`. -/
theorem exercise_10_3_all_r {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) {n : ℕ}
    (hdeg : garlingDegree f hf = n) (hchar : ringChar K = 0 ∨ n < ringChar K)
    (α : K) {r : ℕ} (hr : r ≤ n) :
    HasExactRootMultiplicity f α r ↔
      (∀ j < r, (garlingDeriv^[j] f).eval α = 0) ∧ (garlingDeriv^[r] f).eval α ≠ 0 := by
  -- Use `Exercise 10.2` (`exercise_10_2`) to write `f = ∑_{k ≤ n} C c_k * (X - C α)^k`.
  let c : ℕ → K := fun k => ((garlingDeriv^[k] f).eval α) / (k.factorial : K)
  have hc_zero_iff : ∀ k ≤ n, c k = 0 ↔ (garlingDeriv^[k] f).eval α = 0 := by
    intro k hk
    have hfac0 : (k.factorial : K) ≠ 0 := factorial_cast_ne_zero_of_char hchar hk
    dsimp [c]
    exact div_eq_zero_iff.trans (or_iff_left hfac0)
  have htaylor : f = ∑ k ∈ Finset.range (n + 1), Polynomial.C (c k) * (Polynomial.X - Polynomial.C α) ^ k :=
    exercise_10_2 hf hdeg hchar α
  -- Split the Taylor sum at `r`: `f = P_low + (X - C α)^r * P_high`.
  have hsplit_range : n + 1 = r + (n + 1 - r) := by omega
  let P_low : K[X] := ∑ k ∈ Finset.range r, Polynomial.C (c k) * (Polynomial.X - Polynomial.C α) ^ k
  let P_high : K[X] := ∑ j ∈ Finset.range (n + 1 - r),
    Polynomial.C (c (r + j)) * (Polynomial.X - Polynomial.C α) ^ j
  have hf_split : f = P_low + (Polynomial.X - Polynomial.C α) ^ r * P_high := by
    conv_lhs => rw [htaylor, hsplit_range, Finset.sum_range_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have hiter_zero : ∀ d : ℕ, garlingDeriv^[d] (0 : K[X]) = 0 := by
    intro d
    induction d with
    | zero => rfl
    | succ d ihd => simp [Function.iterate_succ_apply', ihd]
  have hiter_sum : ∀ (d : ℕ) (s : Finset ℕ) (F : ℕ → K[X]),
      garlingDeriv^[d] (∑ i ∈ s, F i) = ∑ i ∈ s, garlingDeriv^[d] (F i) := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d ihd => intro s F; simp [Function.iterate_succ_apply', ihd]
  have hiter_C_mul : ∀ (d : ℕ) (a : K) (p : K[X]),
      garlingDeriv^[d] (Polynomial.C a * p) = Polynomial.C a * garlingDeriv^[d] p := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d ihd => intro a p; simp [Function.iterate_succ_apply', ihd]
  -- Key lemma: `(X - C α)^r ∣ f ↔ ∀ j < r, (D^j f)(α) = 0`.
  have hdvd_r_iff :
      (Polynomial.X - Polynomial.C α) ^ r ∣ f ↔ ∀ j < r, (garlingDeriv^[j] f).eval α = 0 := by
    constructor
    · intro hdvd j hj
      have hsub_dvd : (Polynomial.X - Polynomial.C α) ^ r ∣ P_low := by
        have h1 : P_low = f - (Polynomial.X - Polynomial.C α) ^ r * P_high := by
          rw [hf_split, add_sub_cancel_right]
        rw [h1]
        exact dvd_sub hdvd (dvd_mul_right _ _)
      -- `deg P_low < r`, so `(X - C α)^r ∣ P_low` forces `P_low = 0`.
      have hP_low_zero : P_low = 0 := by
        by_contra hne0
        have hr_pos : 0 < r := by omega
        have hdeg_lt : P_low.natDegree < r := by
          dsimp [P_low]
          refine (Polynomial.natDegree_sum_le _ _).trans_lt ?_
          rw [Finset.fold_max_lt]
          refine ⟨hr_pos, fun k hk => ?_⟩
          have hk_lt : k < r := Finset.mem_range.mp hk
          calc (Polynomial.C (c k) * (Polynomial.X - Polynomial.C α) ^ k).natDegree
              ≤ (Polynomial.C (c k)).natDegree + ((Polynomial.X - Polynomial.C α) ^ k).natDegree :=
                Polynomial.natDegree_mul_le
            _ = 0 + k := by
                rw [Polynomial.natDegree_C, (Polynomial.monic_X_sub_C α).natDegree_pow,
                  Polynomial.natDegree_X_sub_C, mul_one]
            _ < r := by omega
        have hdeg_ge : r ≤ P_low.natDegree := by
          have h := Polynomial.natDegree_le_of_dvd hsub_dvd hne0
          rwa [(Polynomial.monic_X_sub_C α).natDegree_pow, Polynomial.natDegree_X_sub_C,
            mul_one] at h
        omega
      -- Evaluate `D^j P_low` at `α` to extract `c j * j! = 0`.
      have hev0 : (garlingDeriv^[j] P_low).eval α = 0 := by
        rw [hP_low_zero, hiter_zero, Polynomial.eval_zero]
      have hsum_dj :
          (garlingDeriv^[j] P_low).eval α = c j * (j.factorial : K) := by
        have hmap_sum :
            garlingDeriv^[j] P_low = ∑ k ∈ Finset.range r,
              Polynomial.C (c k) * garlingDeriv^[j] ((Polynomial.X - Polynomial.C α) ^ k) := by
          dsimp [P_low]
          exact (hiter_sum j _ _).trans
            (Finset.sum_congr rfl fun k _ => hiter_C_mul j (c k) _)
        rw [hmap_sum, Polynomial.eval_finsetSum]
        simp_rw [Polynomial.eval_mul, Polynomial.eval_C, eval_garlingDeriv_iterate_X_sub_C_pow,
          mul_ite, mul_zero]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj
          split_ifs with h
          · exact (hkj h.symm).elim
          · rfl
        · intro hnot
          exact (hnot (Finset.mem_range.mpr hj)).elim
      rw [hsum_dj] at hev0
      have hfac0 : (j.factorial : K) ≠ 0 := factorial_cast_ne_zero_of_char hchar (by omega)
      have hcj0 : c j = 0 := (mul_eq_zero.mp hev0).resolve_right hfac0
      exact (hc_zero_iff j (by omega)).mp hcj0
    · intro hall
      have hP_low0 : P_low = 0 := by
        dsimp [P_low]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj_lt : j < r := Finset.mem_range.mp hj
        have hcj0 : c j = 0 := (hc_zero_iff j (by omega)).mpr (hall j hj_lt)
        rw [hcj0, map_zero, zero_mul]
      rw [hf_split, hP_low0, zero_add]
      exact dvd_mul_right _ _
  -- When `P_low = 0`, `f = (X - C α)^r * P_high`, and `P_high.eval α = c r`.
  have hPhigh_eval : P_high.eval α = c r := by
    dsimp [P_high]
    rw [Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj0
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow hj0, mul_zero]
    · intro hnot
      have h0mem : 0 ∈ Finset.range (n + 1 - r) := Finset.mem_range.mpr (by omega)
      exact (hnot h0mem).elim
  unfold HasExactRootMultiplicity
  constructor
  · rintro ⟨hdvd_r, hndvd_succ⟩
    have hall : ∀ j < r, (garlingDeriv^[j] f).eval α = 0 := hdvd_r_iff.mp hdvd_r
    refine ⟨hall, fun hdr0 => hndvd_succ ?_⟩
    have hP_low0 : P_low = 0 := by
      dsimp [P_low]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < r := Finset.mem_range.mp hj
      have hcj0 : c j = 0 := (hc_zero_iff j (by omega)).mpr (hall j hj_lt)
      rw [hcj0, map_zero, zero_mul]
    have hcr0 : c r = 0 := (hc_zero_iff r hr).mpr hdr0
    have hroot_high : P_high.IsRoot α := hPhigh_eval.trans hcr0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot_high
    refine ⟨q, ?_⟩
    rw [hf_split, hP_low0, zero_add, hq]
    ring
  · rintro ⟨hall, hdr_ne0⟩
    have hdvd_r : (Polynomial.X - Polynomial.C α) ^ r ∣ f := hdvd_r_iff.mpr hall
    refine ⟨hdvd_r, fun hdvd_succ => hdr_ne0 ?_⟩
    have hP_low0 : P_low = 0 := by
      dsimp [P_low]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < r := Finset.mem_range.mp hj
      have hcj0 : c j = 0 := (hc_zero_iff j (by omega)).mpr (hall j hj_lt)
      rw [hcj0, map_zero, zero_mul]
    obtain ⟨q, hq⟩ := hdvd_succ
    have hcancel :
        (Polynomial.X - Polynomial.C α) ^ r * P_high =
          (Polynomial.X - Polynomial.C α) ^ r * ((Polynomial.X - Polynomial.C α) * q) := by
      calc (Polynomial.X - Polynomial.C α) ^ r * P_high
          = f := by rw [hf_split, hP_low0, zero_add]
        _ = (Polynomial.X - Polynomial.C α) ^ (r + 1) * q := hq
        _ = (Polynomial.X - Polynomial.C α) ^ r * ((Polynomial.X - Polynomial.C α) * q) := by
            rw [pow_succ, mul_assoc]
    have hpow_ne0 : (Polynomial.X - Polynomial.C α) ^ r ≠ 0 :=
      pow_ne_zero r (Polynomial.X_sub_C_ne_zero α)
    have hPhigh_eq : P_high = (Polynomial.X - Polynomial.C α) * q :=
      mul_left_cancel₀ hpow_ne0 hcancel
    have hcr0 : c r = 0 := by
      rw [← hPhigh_eval, hPhigh_eq]
      simp
    exact (hc_zero_iff r hr).mp hcr0

/-- **Exercise 10.3** (§10.4, printed p. 87 / PDF p. 95, for roots `1 ≤ r ≤ n` with repaired `= 0`;
see `QUEUE.md`):
*"Suppose that `f` is a polynomial in `K[x]` of degree `n` and that either `char K = 0` or
`char K > n`. Show that `α` is a root of exact multiplicity `r (≤ n)` if and only if
`f(α) = Df(α) = ⋯ = D^{r-1}f(α) = 0` and `D^r f(α) ≠ 0`."* -/
theorem exercise_10_3 {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) {n : ℕ}
    (hdeg : garlingDegree f hf = n) (hchar : ringChar K = 0 ∨ n < ringChar K)
    (α : K) {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    IsRootOfExactMultiplicity f α r ↔
      (∀ j < r, (garlingDeriv^[j] f).eval α = 0) ∧ (garlingDeriv^[r] f).eval α ≠ 0 := by
  unfold IsRootOfExactMultiplicity
  rw [exercise_10_3_all_r hf hdeg hchar α hrn]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro h
    refine ⟨?_, h⟩
    simpa using h.1 0 (by omega)

/-- Extension-field companion to **Exercise 10.3** (§10.4, p. 87): applies to roots `α ∈ L` in any
field extension `L : K`. -/
theorem exercise_10_3_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f ≠ 0) {n : ℕ} (hdeg : garlingDegree f hf = n)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (α : L) {r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    IsRootOfExactMultiplicity (f.map (algebraMap K L)) α r ↔
      (∀ j < r, Polynomial.aeval α (garlingDeriv^[j] f) = 0) ∧
        Polynomial.aeval α (garlingDeriv^[r] f) ≠ 0 := by
  have hfL0 : f.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf
  have hdegL : garlingDegree (f.map (algebraMap K L)) hfL0 = n := by
    unfold garlingDegree at hdeg ⊢
    rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]
  have hchar_eq : ringChar L = ringChar K :=
    Nat.dvd_antisymm
      ((ringChar.spec L (ringChar K)).mp (by
        rw [← map_natCast (algebraMap K L), ringChar.Nat.cast_ringChar, map_zero]))
      ((ringChar.spec K (ringChar L)).mp ((algebraMap K L).injective (by
        rw [map_natCast, ringChar.Nat.cast_ringChar, map_zero])))
  have hcharL : ringChar L = 0 ∨ n < ringChar L := hchar_eq ▸ hchar
  rw [exercise_10_3 hfL0 hdegL hcharL α hr1 hrn]
  have heval_eq : ∀ m : ℕ,
      (garlingDeriv^[m] (f.map (algebraMap K L))).eval α =
        Polynomial.aeval α (garlingDeriv^[m] f) := by
    intro m
    rw [garlingDeriv_iterate_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  simp_rw [heval_eq]

/-! ## §10.5 The Frobenius monomorphism (printed pp. 87–88, PDF pp. 95–96) -/

/-- Helper: binomial coefficient divisibility `p ∣ p.choose r` for prime `p` and `1 ≤ r < p`,
proved directly from `r! * (p - r)! * p.choose r = p!` as in Garling's proof of `Theorem 10.7`
(printed p. 87 / PDF p. 95). -/
private theorem prime_dvd_choose_between {p r : ℕ} (hp : Nat.Prime p) (hr1 : 1 ≤ r) (hrp : r < p) :
    p ∣ p.choose r := by
  have hfac_eq : p.choose r * r.factorial * (p - r).factorial = p.factorial :=
    Nat.choose_mul_factorial_mul_factorial (le_of_lt hrp)
  have hdvd_pfac : p ∣ p.choose r * r.factorial * (p - r).factorial :=
    hfac_eq.symm ▸ Nat.dvd_factorial hp.pos le_rfl
  have hnot_sub : ¬ (p ∣ (p - r).factorial) := fun h => by
    have hle := (Nat.Prime.dvd_factorial hp).mp h
    omega
  have hnot_r : ¬ (p ∣ r.factorial) := fun h => by
    have hle := (Nat.Prime.dvd_factorial hp).mp h
    omega
  have hdvd1 : p ∣ p.choose r * r.factorial := (hp.dvd_mul.mp hdvd_pfac).resolve_right hnot_sub
  exact (hp.dvd_mul.mp hdvd1).resolve_right hnot_r

/-- Helper extracting `Nat.Prime p` from `ringChar K = p` and `p ≠ 0` via `Theorem 3.17`
(`theorem_3_17`). -/
private theorem prime_of_ringChar_field {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) : Nat.Prime p :=
  hchar ▸ ((theorem_3_17 K).2 (hchar.symm ▸ hp0)).1

/-- Garling's *Frobenius monomorphism* `ϕ(α) = α^p` on a field `K` of characteristic `p ≠ 0`
(§10.5, printed p. 87 / PDF p. 95: *"The mapping `ϕ` is called the Frobenius monomorphism"*),
constructed directly from Garling's binomial-theorem argument on p. 87. -/
def garlingFrobenius (K : Type*) [Field K] {p : ℕ} (hchar : ringChar K = p) (hp0 : p ≠ 0) :
    K →+* K where
  toFun α := α ^ p
  map_one' := one_pow p
  map_mul' α β := mul_pow α β p
  map_zero' := zero_pow hp0
  map_add' α β := by
    have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
    rw [add_pow]
    -- Split off `m = 0` (`β^p`) and `m = p` (`α^p`); intermediate terms `1 ≤ m < p` vanish mod `p`.
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      mul_one]
    have hlow : ∑ m ∈ Finset.range p, α ^ m * β ^ (p - m) * (p.choose m : K) = β ^ p := by
      rcases p with _ | p'
      · exact (hp0 rfl).elim
      · rw [Finset.sum_range_succ']
        simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
        have hmid : ∑ k ∈ Finset.range p',
            α ^ (k + 1) * β ^ (p' + 1 - (k + 1)) * ((p' + 1).choose (k + 1) : K) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hk_lt : k + 1 < p' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
          have hdvd : (p' + 1) ∣ (p' + 1).choose (k + 1) :=
            prime_dvd_choose_between hp_prime (Nat.succ_pos k) hk_lt
          have hcast0 : (((p' + 1).choose (k + 1) : ℕ) : K) = 0 :=
            (ringChar.spec K _).mpr (hchar ▸ hdvd)
          rw [hcast0, mul_zero]
        rw [hmid, zero_add]
    rw [hlow, add_comm]

@[simp]
theorem garlingFrobenius_apply {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p)
    (hp0 : p ≠ 0) (α : K) :
    garlingFrobenius K hchar hp0 α = α ^ p :=
  rfl

/-- **Theorem 10.7** (§10.5, printed p. 87 / PDF p. 95):
*"Suppose that `char K = p ≠ 0`. The map `ϕ(α) = α^p` is a monomorphism of `K` into itself. The set
of elements which remain fixed under `ϕ` is exactly the prime subfield."*

Proved directly following Garling's proof on p. 87 via `Theorem 3.17` (`theorem_3_17`) and root
counting on `x^p - x ∈ K[x]`. -/
theorem theorem_10_7 {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p) (hp0 : p ≠ 0) :
    let φ := garlingFrobenius K hchar hp0
    IsGarlingRingHom (fun α : K => α ^ p) ∧
    IsRingMonomorphism φ ∧
    {α : K | φ α = α} = (primeSubfield K : Set K) := by
  classical
  let _ : DecidableEq K := Classical.decEq K
  intro φ
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  have hghom : IsGarlingRingHom (fun α : K => α ^ p) :=
    ⟨φ.map_add, φ.map_mul, φ.map_one⟩
  have hmono : IsRingMonomorphism φ := φ.injective
  -- Fixed field `F = {α : K | φ α = α}` is a subfield of `K`, hence contains `primeSubfield K`.
  let F : Subfield K :=
    { carrier := {α : K | φ α = α}
      mul_mem' := fun {a b} ha hb => by change φ (a * b) = a * b; rw [map_mul, ha, hb]
      one_mem' := φ.map_one
      add_mem' := fun {a b} ha hb => by change φ (a + b) = a + b; rw [map_add, ha, hb]
      zero_mem' := φ.map_zero
      neg_mem' := fun {a} ha => by change φ (-a) = -a; rw [map_neg, ha]
      inv_mem' := fun {a} ha => by change φ a⁻¹ = a⁻¹; rw [map_inv₀, ha] }
  have hprime_le : (primeSubfield K : Set K) ⊆ {α : K | φ α = α} := by
    change primeSubfield K ≤ F
    rw [primeSubfield_eq_bot]
    exact bot_le
  -- Every fixed element is a root of `x^p - x`, which has degree `p ≥ 2` and hence at most `p` roots.
  let q : K[X] := Polynomial.X ^ p - Polynomial.X
  have hq_deg : q.natDegree = p := by
    dsimp [q]
    have hgt : (Polynomial.X : K[X]).natDegree < (Polynomial.X ^ p : K[X]).natDegree := by
      rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
      exact hp_prime.one_lt
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hgt, Polynomial.natDegree_X_pow]
  have hq_ne0 : q ≠ 0 := by
    intro h0
    have hd0 : q.natDegree = 0 := by rw [h0, Polynomial.natDegree_zero]
    have hp1 := hp_prime.pos
    omega
  have hsub_roots : {α : K | φ α = α} ⊆ (q.roots.toFinset : Set K) := by
    intro α hα
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq_ne0, Polynomial.IsRoot.def]
    dsimp [q]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.mpr hα
  have hfin_fix : ({α : K | φ α = α}).Finite := (q.roots.toFinset.finite_toSet).subset hsub_roots
  have hncard_fix_le : ({α : K | φ α = α}).ncard ≤ p := by
    calc ({α : K | φ α = α}).ncard
        ≤ (q.roots.toFinset : Set K).ncard := Set.ncard_le_ncard hsub_roots
      _ = q.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ = p := hq_deg
  -- By Theorem 3.17, `primeSubfield K ≃+* ZMod p` has cardinality `p`.
  obtain ⟨_, ⟨ePrime⟩⟩ := (theorem_3_17 K).2 (hchar.symm ▸ hp0)
  have _ : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hncard_prime : (primeSubfield K : Set K).ncard = p := by
    have hnat : Nat.card (primeSubfield K) = p := by
      have h1 : Nat.card (primeSubfield K) = Nat.card (ZMod (ringChar K)) :=
        Nat.card_congr ePrime.toEquiv
      rw [h1, hchar, Nat.card_zmod]
    rw [← Nat.card_coe_set_eq]
    exact hnat
  have heq_set : {α : K | φ α = α} = (primeSubfield K : Set K) :=
    (Set.eq_of_subset_of_ncard_le hprime_le (hncard_prime ▸ hncard_fix_le) hfin_fix).symm
  exact ⟨hghom, hmono, heq_set⟩

/-- `[CharP K p]` companion to **Theorem 10.7** (§10.5, p. 87). -/
theorem theorem_10_7_charP (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsRingMonomorphism (frobenius K p) ∧
    {α : K | frobenius K p α = α} = (primeSubfield K : Set K) := by
  have hchar : ringChar K = p := ringChar.eq K p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨_, _, hfix⟩ := theorem_10_7 (K := K) hchar hp0
  exact ⟨(frobenius K p).injective, hfix⟩

/-- **Corollary** [to Theorem 10.7] (§10.5, printed p. 87 / PDF p. 95):
*"If `char K = p ≠ 0` and `K` is algebraic over its prime subfield, then the Frobenius monomorphism
`ϕ` is an automorphism."*

Proved in 3 lines as an immediate consequence of `Theorem 10.7` and `Theorem 4.8`
(`theorem_4_8_subfield`), matching Garling's 1-line deduction on p. 87. -/
theorem corollary_to_theorem_10_7 {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0)
    (halg : IsAlgebraicExtension (primeSubfield K) K) :
    IsFieldAutomorphism (garlingFrobenius K hchar hp0) := by
  obtain ⟨_, hmono, hfix⟩ := theorem_10_7 hchar hp0
  refine ⟨hmono, theorem_4_8_subfield (primeSubfield K) halg hmono fun k hk => ?_⟩
  exact (Set.ext_iff.mp hfix k).mpr hk

/-- Supporting factorization for **Exercise 10.4** (§10.5, printed p. 87 / PDF p. 95):
for any prime `p`, `x^{p-1} - 1 = ∏_{a ∈ ℤ_p \ {0}} (x - a)` in `ℤ_p[x]`. -/
theorem exercise_10_4_factorization {p : ℕ} (hp : Nat.Prime p) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    (Polynomial.X ^ (p - 1) - 1 : (ZMod p)[X]) =
      ∏ a ∈ Finset.univ.erase (0 : ZMod p), (Polynomial.X - Polynomial.C a) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  let S : Finset (ZMod p) := Finset.univ.erase 0
  let LHS : (ZMod p)[X] := Polynomial.X ^ (p - 1) - 1
  let RHS : (ZMod p)[X] := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  have hS_card : S.card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hLHS_monic : LHS.Monic :=
    Polynomial.monic_X_pow_sub_C (1 : ZMod p) (Nat.sub_ne_zero_of_lt hp.one_lt)
  have hRHS_monic : RHS.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hLHS_deg : LHS.natDegree = p - 1 := Polynomial.natDegree_X_pow_sub_C
  have hRHS_deg : RHS.natDegree = p - 1 := by
    dsimp [RHS]
    rw [Polynomial.natDegree_prod _ _ fun a _ => Polynomial.X_sub_C_ne_zero a]
    simp [hS_card]
  -- Every `a ∈ ℤ_p \ {0}` lies in `primeSubfield (ZMod p)`, so `a^p = a` by `Theorem 10.7`.
  obtain ⟨_, _, hfix_zp⟩ := theorem_10_7 (K := ZMod p) (ringChar.eq (ZMod p) p) hp.ne_zero
  have hroots : ∀ a ∈ S, LHS.IsRoot a := by
    intro a ha
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    have hnat_mem : ∀ k : ℕ, (k : ZMod p) ∈ primeSubfield (ZMod p) := fun k => by
      induction k with
      | zero => simp
      | succ m ihm =>
        rw [Nat.cast_succ]
        exact (primeSubfield (ZMod p)).add_mem ihm (primeSubfield (ZMod p)).one_mem
    have hmem : a ∈ primeSubfield (ZMod p) := by
      rw [← ZMod.natCast_zmod_val a]
      exact hnat_mem a.val
    have hap : a ^ p = a := (Set.ext_iff.mp hfix_zp a).mpr hmem
    have hap1 : a ^ (p - 1) * a = 1 * a := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.pos, hap]
    have ha_pow : a ^ (p - 1) = 1 := mul_right_cancel₀ ha0 hap1
    dsimp [LHS]
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, ha_pow, sub_self]
  -- Thus `RHS ∣ LHS`; since both are monic of degree `p - 1`, `LHS = RHS`.
  have hdvd : RHS ∣ LHS := by
    dsimp [RHS]
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_)
      (fun a ha => Polynomial.dvd_iff_isRoot.mpr (hroots a ha))
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := fun h0 => hLHS_monic.ne_zero (by rw [hq, h0, mul_zero])
  have hq_deg0 : q.natDegree = 0 := by
    have hsum := congrArg Polynomial.natDegree hq
    rw [hLHS_deg, Polynomial.natDegree_mul hRHS_monic.ne_zero hq0, hRHS_deg] at hsum
    omega
  have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg0
  have hqlc : q.coeff 0 = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [hLHS_monic.leadingCoeff, Polynomial.leadingCoeff_mul, hRHS_monic.leadingCoeff, one_mul,
      Polynomial.leadingCoeff, hq_deg0] at hlc
    exact hlc.symm
  exact hq.trans (by rw [hqc, hqlc, map_one, mul_one])

/-- **Exercise 10.4** (§10.5, printed p. 87 / PDF p. 95 — *Wilson's theorem*):
*"Suppose that `p` is a prime number. By factorizing `x^{p-1} - 1` over `ℤ_p`, shows [sic: `show`]
that `(p - 1)! + 1 = 0 (mod p)` (Wilson's theorem)."*

Proved directly from `exercise_10_4_factorization` by evaluating `x^{p-1} - 1 = ∏_{a ≠ 0} (x - a)`
at `x = 0`, in all three standard congruence formulations (`ZMod p`, `Int.ModEq`, and `Nat.ModEq`). -/
theorem exercise_10_4 {p : ℕ} (hp : Nat.Prime p) :
    (((p - 1).factorial + 1 : ℕ) : ZMod p) = 0 ∧
    (((p - 1).factorial : ℤ) + 1) ≡ 0 [ZMOD (p : ℤ)] ∧
    ((p - 1).factorial + 1) ≡ 0 [MOD p] := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hfac := exercise_10_4_factorization hp
  -- Evaluate `X^{p-1} - 1 = ∏_{a ∈ univ.erase 0} (X - C a)` at `0 : ZMod p`.
  have hev0 := congrArg (fun q : (ZMod p)[X] => q.eval 0) hfac
  have hp1_ne0 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    zero_pow hp1_ne0, zero_sub, Polynomial.eval_prod, Polynomial.eval_C] at hev0
  -- Reindex `univ.erase 0` by `k ↦ ((k + 1) : ZMod p)` for `k ∈ Finset.range (p - 1)`.
  have herase_eq :
      (Finset.univ.erase (0 : ZMod p)) =
        (Finset.range (p - 1)).image (fun k : ℕ => ((k + 1 : ℕ) : ZMod p)) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx0
      have hval_lt : x.val < p := x.val_lt
      have hval_pos : 0 < x.val := Nat.pos_of_ne_zero fun hv0 =>
        hx0 ((ZMod.val_eq_zero x).mp hv0)
      refine ⟨x.val - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel hval_pos, ZMod.natCast_zmod_val]
    · rintro ⟨k, hk, rfl⟩
      intro h0
      have hdvd : p ∣ (k + 1) := (ZMod.natCast_eq_zero_iff (k + 1) p).mp h0
      have hle : p ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdvd
      omega
  have hinj : Set.InjOn (fun k : ℕ => ((k + 1 : ℕ) : ZMod p)) (Finset.range (p - 1)) := by
    intro i hi j hj hij
    have hi_lt : i + 1 < p := by have := Finset.mem_range.mp hi; omega
    have hj_lt : j + 1 < p := by have := Finset.mem_range.mp hj; omega
    have hval := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi_lt, ZMod.val_natCast_of_lt hj_lt] at hval
    omega
  rw [herase_eq, Finset.prod_image hinj] at hev0
  have hprod_neg :
      (∏ k ∈ Finset.range (p - 1), -((k + 1 : ℕ) : ZMod p)) =
        (-1 : ZMod p) ^ (p - 1) * (((p - 1).factorial : ℕ) : ZMod p) := by
    have h1 : (∏ k ∈ Finset.range (p - 1), -((k + 1 : ℕ) : ZMod p)) =
        (∏ _k ∈ Finset.range (p - 1), (-1 : ZMod p)) *
          ∏ k ∈ Finset.range (p - 1), ((k + 1 : ℕ) : ZMod p) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      ring
    rw [h1, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
      Finset.prod_range_add_one_eq_factorial]
  rw [hprod_neg] at hev0
  -- For `p = 2`, `(2 - 1)! + 1 = 2 = 0` in `ZMod 2`; for odd `p`, `p - 1` is even.
  have hzmod : (((p - 1).factorial + 1 : ℕ) : ZMod p) = 0 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · have h2 : (2 - 1).factorial + 1 = 2 := rfl
      rw [h2]
      exact ZMod.natCast_self 2
    · have heven : Even (p - 1) := Nat.even_iff.mpr (by omega)
      rw [heven.neg_one_pow, one_mul] at hev0
      rw [Nat.cast_add, Nat.cast_one, ← hev0, neg_add_cancel]
  have hdvd_nat : p ∣ ((p - 1).factorial + 1) :=
    (ZMod.natCast_eq_zero_iff _ p).mp hzmod
  have hmod_nat : ((p - 1).factorial + 1) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hdvd_nat
  have hmod_int : (((p - 1).factorial : ℤ) + 1) ≡ 0 [ZMOD (p : ℤ)] := by
    rw [Int.modEq_zero_iff_dvd]
    exact_mod_cast hdvd_nat
  exact ⟨hzmod, hmod_int, hmod_nat⟩

private noncomputable def gaussianIntToSubringHom : GaussianInt →+* GaussianIntSubring where
  toFun z := ⟨(z : ℂ), by
    change ∃ m n : ℤ, (z : ℂ) = (m : ℂ) + Complex.I * (n : ℂ)
    refine ⟨z.re, z.im, ?_⟩
    rw [GaussianInt.toComplex_def]
    ring⟩
  map_one' := Subtype.ext GaussianInt.toComplex_one
  map_mul' x y := Subtype.ext (GaussianInt.toComplex_mul x y)
  map_zero' := Subtype.ext GaussianInt.toComplex_zero
  map_add' x y := Subtype.ext (GaussianInt.toComplex_add x y)

@[simp]
private theorem gaussianIntToSubringHom_coe (z : GaussianInt) :
    (gaussianIntToSubringHom z : ℂ) = (z : ℂ) :=
  rfl

/-- Canonical ring isomorphism from Mathlib's `GaussianInt` (`ℤ[i]`) to Chapter 3's
`GaussianIntSubring` (`ℤ + iℤ ⊆ ℂ`, §3.1 Example 3, printed p. 18), used in `Exercises 10.5` and
`10.6`. -/
noncomputable def gaussianIntToSubring : GaussianInt ≃+* GaussianIntSubring :=
  RingEquiv.ofBijective gaussianIntToSubringHom
    ⟨fun x y hxy => GaussianInt.toComplex_injective (congrArg Subtype.val hxy),
     by
      rintro ⟨_, m, n, rfl⟩
      refine ⟨⟨m, n⟩, Subtype.ext ?_⟩
      rw [gaussianIntToSubringHom_coe, GaussianInt.toComplex_def']
      ring⟩

/-- Inverse ring isomorphism `GaussianIntSubring ≃+* GaussianInt`. -/
noncomputable def gaussianIntSubringEquiv : GaussianIntSubring ≃+* GaussianInt :=
  gaussianIntToSubring.symm

/-- Transport `Prime` across a ring isomorphism `R ≃+* S`. -/
private theorem prime_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {x : R} (hx : Prime x) : Prime (e x) := by
  refine ⟨fun h0 => hx.ne_zero (e.injective (h0.trans e.map_zero.symm)),
    fun hu => hx.not_isUnit (by
      obtain ⟨u, hu_eq⟩ := hu
      refine ⟨Units.map e.symm.toRingHom.toMonoidHom u, e.injective ?_⟩
      change e (e.symm ↑u) = e x
      rw [e.apply_symm_apply, hu_eq]),
    fun a b hab => ?_⟩
  obtain ⟨c, hc⟩ := hab
  have hpre : x ∣ e.symm a * e.symm b :=
    ⟨e.symm c, e.injective (by simp [map_mul, hc])⟩
  rcases hx.dvd_or_dvd hpre with ⟨d, hd⟩ | ⟨d, hd⟩
  · left
    exact ⟨e d, by rw [← map_mul, ← hd, e.apply_symm_apply]⟩
  · right
    exact ⟨e d, by rw [← map_mul, ← hd, e.apply_symm_apply]⟩

/-- **Exercise 10.5** (§10.5, printed p. 87 / PDF p. 95):
*"Suppose that `p` is a prime number of the form `4n + 1`. Show that there exists `k` such that
`k² + 1 = 0 (mod p)`. Show that `p` is not a prime in `ℤ + iℤ` and show that there exist `u` and `v`
in `ℤ` such that `u² + v² = p`."*

Proved directly from Wilson's theorem (`exercise_10_4`, pairing `j` with `p - j` in `(4n)!` so
`k = (2n)!` satisfies `k² + 1 ≡ 0 (mod p)`) and Euclidean factorization in `ℤ + iℤ`. -/
theorem exercise_10_5 {p : ℕ} (hp : Nat.Prime p) (hn : ∃ n : ℕ, p = 4 * n + 1) :
    (∃ k : ℤ, k ^ 2 + 1 ≡ 0 [ZMOD (p : ℤ)]) ∧
    (∃ k : ZMod p, k ^ 2 + 1 = 0) ∧
    ¬ IsGarlingPrime (⟨(p : ℂ), (p : ℤ), 0, by simp⟩ : GaussianIntSubring) ∧
    ¬ Prime (p : GaussianInt) ∧
    (∃ u v : ℤ, u ^ 2 + v ^ 2 = (p : ℤ)) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hpn⟩ := hn
  -- 1. Construct `k = (2n)!` in `ZMod p` via Wilson's theorem (`Exercise 10.4`).
  let m : ℕ := 2 * n
  have hp_sub1 : p - 1 = 2 * m := by dsimp [m]; omega
  -- Pair `(p - 1)! = (2m)! = (∏_{j < m} (j + 1)) * (∏_{j < m} (p - (j + 1)))` in `ZMod p`.
  have hwilson_pair :
      (((p - 1).factorial : ℕ) : ZMod p) = (((m.factorial : ℕ) : ZMod p)) ^ 2 := by
    rw [hp_sub1, ← Finset.prod_range_add_one_eq_factorial, two_mul, Finset.prod_range_add,
      Nat.cast_mul, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Nat.cast_prod]
    have hupper :
        (∏ x ∈ Finset.range m, ((m + x + 1 : ℕ) : ZMod p)) =
          ∏ j ∈ Finset.range m, -((j + 1 : ℕ) : ZMod p) := by
      conv_lhs => rw [← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj_lt : j < m := Finset.mem_range.mp hj
      have hsum_p : (m + (m - 1 - j) + 1) + (j + 1) = p := by dsimp [m]; omega
      have hcast_sum : (((m + (m - 1 - j) + 1 : ℕ) : ZMod p)) + ((j + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, hsum_p, ZMod.natCast_self]
      exact eq_neg_of_add_eq_zero_left hcast_sum
    have hneg_even :
        (∏ j ∈ Finset.range m, -((j + 1 : ℕ) : ZMod p)) =
          ∏ j ∈ Finset.range m, ((j + 1 : ℕ) : ZMod p) := by
      have h1 : (∏ j ∈ Finset.range m, -((j + 1 : ℕ) : ZMod p)) =
          (∏ _j ∈ Finset.range m, (-1 : ZMod p)) *
            ∏ j ∈ Finset.range m, ((j + 1 : ℕ) : ZMod p) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        ring
      have hm_even : Even m := ⟨n, by dsimp [m]; ring⟩
      rw [h1, Finset.prod_const, Finset.card_range, hm_even.neg_one_pow, one_mul]
    rw [hupper, hneg_even, sq]
  have hwilson := (exercise_10_4 hp).1
  rw [Nat.cast_add, Nat.cast_one, hwilson_pair] at hwilson
  let kZMod : ZMod p := (m.factorial : ZMod p)
  have hk_zmod : kZMod ^ 2 + 1 = 0 := hwilson
  let kInt : ℤ := (m.factorial : ℤ)
  have hk_dvd : (p : ℤ) ∣ (kInt ^ 2 + 1) := by
    have hnat : (((m.factorial ^ 2 + 1 : ℕ) : ZMod p)) = 0 := by
      simpa [kZMod, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hk_zmod
    have hdvd_nat : p ∣ (m.factorial ^ 2 + 1) := (ZMod.natCast_eq_zero_iff _ p).mp hnat
    dsimp [kInt]
    exact_mod_cast hdvd_nat
  have hk_mod : kInt ^ 2 + 1 ≡ 0 [ZMOD (p : ℤ)] := Int.modEq_zero_iff_dvd.mpr hk_dvd
  -- 2. Show `p` is not prime in `GaussianInt` (nor in `GaussianIntSubring`).
  have hnot_prime_gi : ¬ Prime (p : GaussianInt) := by
    intro hprime
    obtain ⟨qInt, hqInt⟩ := hk_dvd
    let z₁ : GaussianInt := ⟨kInt, 1⟩
    let z₂ : GaussianInt := ⟨kInt, -1⟩
    have hprod_gi : z₁ * z₂ = (p : GaussianInt) * ⟨qInt, 0⟩ := by
      ext
      · simp [z₁, z₂]
        linarith [hqInt, show kInt * kInt + 1 = kInt ^ 2 + 1 by ring]
      · simp [z₁, z₂]
    have hdvd_prod : (p : GaussianInt) ∣ z₁ * z₂ := ⟨⟨qInt, 0⟩, hprod_gi⟩
    rcases hprime.dvd_or_dvd hdvd_prod with ⟨w, hw⟩ | ⟨w, hw⟩
    · have him : (1 : ℤ) = (p : ℤ) * w.im := by
        have h := congrArg Zsqrtd.im hw
        simpa [z₁] using h
      have hp_dvd1 : (p : ℤ) ∣ 1 := ⟨w.im, him⟩
      have hp_le1 : p ≤ 1 := Int.le_of_ofNat_le_ofNat (Int.le_of_dvd zero_lt_one hp_dvd1)
      exact absurd hp_le1 (not_le_of_gt hp.one_lt)
    · have him : (-1 : ℤ) = (p : ℤ) * w.im := by
        have h := congrArg Zsqrtd.im hw
        simpa [z₂] using h
      have hp_dvd1 : (p : ℤ) ∣ 1 := ⟨-w.im, by linarith⟩
      have hp_le1 : p ≤ 1 := Int.le_of_ofNat_le_ofNat (Int.le_of_dvd zero_lt_one hp_dvd1)
      exact absurd hp_le1 (not_le_of_gt hp.one_lt)
  let pSub : GaussianIntSubring := ⟨(p : ℂ), (p : ℤ), 0, by simp⟩
  have hp_to : gaussianIntToSubring (p : GaussianInt) = pSub := by
    apply Subtype.ext
    change ((p : GaussianInt) : ℂ) = (p : ℂ)
    simp
  have hp_map : gaussianIntSubringEquiv pSub = (p : GaussianInt) := by
    dsimp [gaussianIntSubringEquiv]
    rw [← hp_to, gaussianIntToSubring.symm_apply_apply]
  have hnot_garling_prime : ¬ IsGarlingPrime pSub := by
    rw [isGarlingPrime_iff]
    intro hpSub
    exact hnot_prime_gi (hp_map ▸ prime_of_ringEquiv gaussianIntSubringEquiv hpSub)
  -- 3. Deduce `∃ u v : ℤ, u^2 + v^2 = p` since `GaussianInt` is a Euclidean domain.
  have hnot_irr : ¬ Irreducible (p : GaussianInt) := fun hirr =>
    hnot_prime_gi (_root_.irreducible_iff_prime.mp hirr)
  obtain ⟨uNat, vNat, huv⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hnot_irr
  refine ⟨⟨kInt, hk_mod⟩, ⟨kZMod, hk_zmod⟩, hnot_garling_prime, hnot_prime_gi,
    ⟨(uNat : ℤ), (vNat : ℤ), by exact_mod_cast huv⟩⟩

/-- **Exercise 10.6** (§10.5, printed p. 88 / PDF p. 96):
*"Suppose that `p` is a prime number of the form `4n + 3`. Show that `p` is a prime in `ℤ + iℤ`."*

Proved in both Chapter 3's `GaussianIntSubring` (`IsGarlingPrime` and `Prime`) and Mathlib's
`GaussianInt`, via squares modulo `4` and `Theorem 3.8` (`irreducible ↔ prime` in the PID `ℤ + iℤ`). -/
theorem exercise_10_6 {p : ℕ} (hp : Nat.Prime p) (hn : ∃ n : ℕ, p = 4 * n + 3) :
    let pSub : GaussianIntSubring := ⟨(p : ℂ), (p : ℤ), 0, by simp⟩
    IsGarlingPrime pSub ∧
    Prime pSub ∧
    Prime (p : GaussianInt) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨n, hpn⟩ := hn
  intro pSub
  -- Show `(p : GaussianInt)` is irreducible: if not, `a^2 + b^2 = p = 4n + 3`, impossible mod `4`.
  have hirr_gi : Irreducible (p : GaussianInt) := by
    by_contra hnot_irr
    obtain ⟨a, b, hab⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hnot_irr
    have ha_mod4 : (a ^ 2) % 4 = 0 ∨ (a ^ 2) % 4 = 1 := by
      have h4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      rcases h4 with h | h | h | h <;>
      · rw [sq, Nat.mul_mod, h]
        omega
    have hb_mod4 : (b ^ 2) % 4 = 0 ∨ (b ^ 2) % 4 = 1 := by
      have h4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      rcases h4 with h | h | h | h <;>
      · rw [sq, Nat.mul_mod, h]
        omega
    have hsum_mod4 : (a ^ 2 + b ^ 2) % 4 = 3 := by rw [hab, hpn]; omega
    rcases ha_mod4 with ha | ha <;> rcases hb_mod4 with hb | hb <;>
    · rw [Nat.add_mod, ha, hb] at hsum_mod4
      omega
  have hprime_gi : Prime (p : GaussianInt) :=
    _root_.irreducible_iff_prime.mp hirr_gi
  have hp_to : gaussianIntToSubring (p : GaussianInt) = pSub := by
    apply Subtype.ext
    change ((p : GaussianInt) : ℂ) = (p : ℂ)
    simp
  have hprime_sub : Prime pSub := hp_to ▸ prime_of_ringEquiv gaussianIntToSubring hprime_gi
  exact ⟨(isGarlingPrime_iff pSub).mpr hprime_sub, hprime_sub, hprime_gi⟩

/-! ## §10.6 Inseparable polynomials (printed pp. 88–90, PDF pp. 96–98) -/

/-- Helper extracting `CharP R p` from `ringChar R = p`. -/
private theorem charP_of_ringChar_eq {R : Type*} [Semiring R] {p : ℕ}
    (hchar : ringChar R = p) : CharP R p :=
  hchar ▸ ringChar.charP R

/-- In characteristic `p ≠ 0`, raising a polynomial `h ∈ K[x]` to the `p`th power applies the
Frobenius monomorphism `garlingFrobenius` to its coefficients and substitutes `x ↦ x^p`
(§10.6, printed p. 88 / PDF p. 96: `(b_0 + b_1 x + ⋯ + x^n)^p = a_0 + a_1 x^p + ⋯ + x^{np}`). -/
theorem poly_pow_char_eq_expand_map_frobenius {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) (h : K[X]) :
    h ^ p = Polynomial.expand K p (h.map (garlingFrobenius K hchar hp0)) := by
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  have _ : CharP K p := charP_of_ringChar_eq hchar
  have _ : Fact p.Prime := ⟨hp_prime⟩
  have hfr_eq : garlingFrobenius K hchar hp0 = frobenius K p := by
    ext x
    rfl
  rw [hfr_eq, ← Polynomial.map_expand, Polynomial.map_frobenius_expand]

/-- Helper: factor out the maximal power `f₁ ^ m` of a monic irreducible divisor `f₁ ∣ q` from a
monic polynomial `q ∈ K[x]`, yielding `q = f₁ ^ m * h₂` with `m ≥ 1`, `h₂.Monic`, and `¬ (f₁ ∣ h₂)`
(used in Garling's proof of `Theorem 10.8`, printed p. 88 / PDF p. 96). -/
private theorem exists_monic_pow_mul_not_dvd {K : Type*} [Field K] {q f₁ : K[X]}
    (hq : q.Monic) (hf₁ : f₁.Monic) (hf₁_irr : Irreducible f₁) (hdvd : f₁ ∣ q) :
    ∃ (m : ℕ) (h₂ : K[X]), 1 ≤ m ∧ h₂.Monic ∧ ¬ (f₁ ∣ h₂) ∧ q = f₁ ^ m * h₂ := by
  induction hn : q.natDegree using Nat.strong_induction_on generalizing q with
  | h n ih =>
    obtain ⟨q', hq'⟩ := hdvd
    have hq'_monic : q'.Monic := hf₁.of_mul_monic_left (hq' ▸ hq)
    by_cases hdvd' : f₁ ∣ q'
    · have hf₁_deg : 0 < f₁.natDegree := hf₁_irr.natDegree_pos
      have hq'_lt : q'.natDegree < n := by
        have hmul : q.natDegree = f₁.natDegree + q'.natDegree := by
          rw [hq', Polynomial.natDegree_mul hf₁.ne_zero hq'_monic.ne_zero]
        omega
      obtain ⟨m', h₂, hm'1, hh₂_monic, hndvd, hq'_eq⟩ :=
        ih q'.natDegree hq'_lt hq'_monic hdvd' rfl
      refine ⟨m' + 1, h₂, by omega, hh₂_monic, hndvd, ?_⟩
      rw [hq', hq'_eq, pow_succ', mul_assoc]
    · exact ⟨1, q', le_rfl, hq'_monic, hdvd', by rw [pow_one, hq']⟩

/-- **Theorem 10.8** (§10.6, printed p. 88 / PDF p. 96):
*"Suppose that `char K = p > 0` and that
`f(x) = a_0 + a_1 x^p + ⋯ + a_{n-1} x^{(n-1)p} + x^{np} = g(x^p)`, where `g ∈ K[x]`.
Then `f` is irreducible if and only if `g` is irreducible and not all the coefficients `a_i` are
`p`th powers of elements of `K`."*

Proved directly following Garling's elementary Bézout/derivative proof on p. 88 (zero algebraic
closures). Because `f` (and hence `g`) is monic (`g.coeff n = 1 = 1^p` and `g.coeff i = 0 = 0^p`
for `i > n`), *"not all coefficients of `g` are `p`th powers"* holds unconditionally across all
indices `i : ℕ` (see `theorem_10_8_sum` for the explicit indexed-sum formulation over `Fin n`). -/
theorem theorem_10_8 {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p) (hp_pos : 0 < p)
    {f g : K[X]} (hf_monic : f.Monic) (hfg : f = Polynomial.expand K p g) :
    IsGarlingIrreducible f ↔
      IsGarlingIrreducible g ∧ ¬ (∀ i : ℕ, ∃ b : K, g.coeff i = b ^ p) := by
  rw [isGarlingIrreducible_iff, isGarlingIrreducible_iff]
  have hp0 : p ≠ 0 := hp_pos.ne'
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  have _ : CharP K p := charP_of_ringChar_eq hchar
  have _ : Fact p.Prime := ⟨hp_prime⟩
  have hg_monic : g.Monic := (Polynomial.monic_expand_iff hp_pos).mp (hfg ▸ hf_monic)
  constructor
  · -- (`⇒`) If `f = g(x^p)` is irreducible, then `g` is irreducible; if all `g.coeff i = b_i^p`,
    -- then `f = h^p` is reducible.
    intro hf_irr
    have hg_irr : Irreducible g := Polynomial.of_irreducible_expand hp0 (hfg ▸ hf_irr)
    refine ⟨hg_irr, fun hall => ?_⟩
    choose b hb using hall
    let h : K[X] := ∑ i ∈ Finset.range (g.natDegree + 1), Polynomial.C (b i) * Polynomial.X ^ i
    have hmap : h.map (garlingFrobenius K hchar hp0) = g := by
      dsimp [h]
      rw [Polynomial.map_sum]
      conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow' g (Nat.lt_succ_self _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        garlingFrobenius_apply, ← hb i]
    have hf_pow : f = h ^ p := by
      rw [hfg, ← hmap, ← poly_pow_char_eq_expand_map_frobenius hchar hp0 h]
    exact not_irreducible_pow hp_prime.ne_one (hf_pow ▸ hf_irr)
  · -- (`⇐`) Suppose `g` is irreducible and not all `g.coeff i` are `p`th powers, yet `f` is
    -- reducible; follow Garling's two-case proof on p. 88.
    rintro ⟨hg_irr, hnot_all⟩
    by_contra hf_not_irr
    have hg_deg_pos : 0 < g.natDegree := hg_irr.natDegree_pos
    have hf_deg_pos : 0 < f.natDegree := by
      rw [hfg, Polynomial.natDegree_expand]
      exact Nat.mul_pos hg_deg_pos hp_pos
    have hf_not_unit : ¬ IsUnit f := fun hu => by
      have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    obtain ⟨q₀, hq₀_irr, hq₀_dvd⟩ :=
      WfDvdMonoid.exists_irreducible_factor hf_not_unit hf_monic.ne_zero
    -- Rescale `q₀` to a monic irreducible divisor `f₁` of `f`.
    let f₁ : K[X] := q₀ * Polynomial.C q₀.leadingCoeff⁻¹
    have hf₁_monic : f₁.Monic := Polynomial.monic_mul_leadingCoeff_inv hq₀_irr.ne_zero
    have hlc_ne0 : q₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₀_irr.ne_zero
    have hu_inv : IsUnit (Polynomial.C q₀.leadingCoeff⁻¹) :=
      Polynomial.isUnit_C.mpr (inv_ne_zero hlc_ne0).isUnit
    have hassoc : Associated q₀ f₁ := associated_mul_unit_right q₀ _ hu_inv
    have hf₁_irr : Irreducible f₁ := hassoc.irreducible hq₀_irr
    have hf₁_dvd : f₁ ∣ f := hassoc.symm.dvd.trans hq₀_dvd
    -- Extract the maximal power `f = f₁^m * h₂` with `m ≥ 1`, `h₂.Monic`, and `¬ (f₁ ∣ h₂)`.
    obtain ⟨m, h₂, hm1, hh₂_monic, hndvd, hf_fact⟩ :=
      exists_monic_pow_mul_not_dvd hf_monic hf₁_monic hf₁_irr hf₁_dvd
    let h₁ : K[X] := f₁ ^ m
    have hh₁_monic : h₁.Monic := hf₁_monic.pow m
    have hh₁_deg_pos : 0 < h₁.natDegree := by
      dsimp [h₁]
      rw [hf₁_monic.natDegree_pow]
      exact Nat.mul_pos hm1 hf₁_irr.natDegree_pos
    -- Note `Df = 0` since `f = expand K p g` in characteristic `p`.
    have hdf0 : Polynomial.derivative f = 0 := by
      rw [hfg, Polynomial.derivative_expand]
      have hp_cast0 : (p : K[X]) = 0 := CharP.cast_eq_zero K[X] p
      rw [hp_cast0, zero_mul, mul_zero]
    -- Case split on whether `h₂` has positive degree (`h₂ ≠ 1`) or `h₂ = 1` (`h₂.natDegree = 0`).
    by_cases hh₂_deg0 : h₂.natDegree = 0
    · -- Case 2 (`h₂ = 1`, p. 88): `f = f₁ ^ m` with `m > 1`.
      have hh₂_eq1 : h₂ = 1 := by
        have hc := Polynomial.eq_C_of_natDegree_eq_zero hh₂_deg0
        have hlc : h₂.coeff 0 = 1 := by
          have h := hh₂_monic.leadingCoeff
          rwa [Polynomial.leadingCoeff, hh₂_deg0] at h
        rw [hc, hlc, map_one]
      have hf_eq_pow : f = f₁ ^ m := by rw [hf_fact, hh₂_eq1, mul_one]
      have hm_ne1 : m ≠ 1 := fun hm_eq1 => hf_not_irr (by rw [hf_eq_pow, hm_eq1, pow_one]; exact hf₁_irr)
      by_cases hp_dvd_m : p ∣ m
      · -- Subcase 2b (`p ∣ m`): write `m = p * r`, `f = (f₁^r)^p`, forcing all `g.coeff i` to be
        -- `p`th powers!
        obtain ⟨r, hmr⟩ := hp_dvd_m
        let u : K[X] := f₁ ^ r
        have hf_up : f = u ^ p := by
          dsimp [u]
          rw [hf_eq_pow, hmr, mul_comm, pow_mul]
        have hexp_eq :
            Polynomial.expand K p g =
              Polynomial.expand K p (u.map (garlingFrobenius K hchar hp0)) := by
          rw [← hfg, hf_up, poly_pow_char_eq_expand_map_frobenius hchar hp0 u]
        have hg_eq : g = u.map (garlingFrobenius K hchar hp0) :=
          Polynomial.expand_injective hp_pos hexp_eq
        exact hnot_all fun i => ⟨u.coeff i, by rw [hg_eq, Polynomial.coeff_map]; rfl⟩
      · -- Subcase 2a (`¬ (p ∣ m)`): `0 = Df = m * f₁^{m-1} * Df₁` with `(m : K) ≠ 0`, so `Df₁ = 0`,
        -- hence `f₁ = g₁(x^p)` and `g = g₁^m` is reducible!
        have hm_cast_ne0 : (m : K) ≠ 0 := fun hm0 =>
          hp_dvd_m ((CharP.cast_eq_zero_iff K p m).mp hm0)
        have hdf_pow : Polynomial.derivative (f₁ ^ m) = 0 := hf_eq_pow ▸ hdf0
        rw [Polynomial.derivative_pow] at hdf_pow
        have hC_ne0 : (Polynomial.C (m : K)) ≠ 0 := Polynomial.C_ne_zero.mpr hm_cast_ne0
        have hf₁_pow_ne0 : f₁ ^ (m - 1) ≠ 0 := pow_ne_zero _ hf₁_monic.ne_zero
        have hleft_ne0 : Polynomial.C (m : K) * f₁ ^ (m - 1) ≠ 0 := mul_ne_zero hC_ne0 hf₁_pow_ne0
        have hdf₁0 : Polynomial.derivative f₁ = 0 :=
          (mul_eq_zero.mp hdf_pow).resolve_left hleft_ne0
        let g₁ : K[X] := Polynomial.contract p f₁
        have hf₁_exp : Polynomial.expand K p g₁ = f₁ :=
          Polynomial.expand_contract p hdf₁0 hp0
        have hg_pow : Polynomial.expand K p g = Polynomial.expand K p (g₁ ^ m) := by
          rw [← hfg, hf_eq_pow, map_pow, hf₁_exp]
        have hg_eq : g = g₁ ^ m := Polynomial.expand_injective hp_pos hg_pow
        exact not_irreducible_pow hm_ne1 (hg_eq ▸ hg_irr)
    · -- Case 1 (`deg h₂ ≥ 1`, p. 88): `h₁` and `h₂` are coprime (`k₁ h₁ + k₂ h₂ = 1`) and
      -- `0 = Df = Dh₁ * h₂ + h₁ * Dh₂`, forcing `Dh₁ = 0` and `Dh₂ = 0`, hence `g = g₁ * g₂`!
      have hh₂_deg_pos : 0 < h₂.natDegree := Nat.pos_of_ne_zero hh₂_deg0
      have hcop₁ : IsCoprime f₁ h₂ := (Irreducible.coprime_iff_not_dvd hf₁_irr).mpr hndvd
      have hcop : IsCoprime h₁ h₂ := hcop₁.pow_left
      obtain ⟨k₁, k₂, hbez⟩ := hcop
      have hprod_deriv : Polynomial.derivative h₁ * h₂ + h₁ * Polynomial.derivative h₂ = 0 := by
        have hd := hf_fact ▸ hdf0
        rwa [Polynomial.derivative_mul] at hd
      have hdh₁_mul_h₂ : Polynomial.derivative h₁ * h₂ = -(h₁ * Polynomial.derivative h₂) :=
        eq_neg_of_add_eq_zero_left hprod_deriv
      have hh₁_dvd_dh₁ : h₁ ∣ Polynomial.derivative h₁ := by
        refine ⟨k₁ * Polynomial.derivative h₁ - k₂ * Polynomial.derivative h₂, ?_⟩
        calc Polynomial.derivative h₁
            = Polynomial.derivative h₁ * 1 := (mul_one _).symm
          _ = Polynomial.derivative h₁ * (k₁ * h₁ + k₂ * h₂) := by rw [hbez]
          _ = k₁ * h₁ * Polynomial.derivative h₁ + k₂ * (Polynomial.derivative h₁ * h₂) := by ring
          _ = k₁ * h₁ * Polynomial.derivative h₁ + k₂ * (-(h₁ * Polynomial.derivative h₂)) := by
                rw [hdh₁_mul_h₂]
          _ = h₁ * (k₁ * Polynomial.derivative h₁ - k₂ * Polynomial.derivative h₂) := by ring
      have hdh₁0 : Polynomial.derivative h₁ = 0 := by
        by_contra hdh₁_ne0
        have hle := Polynomial.natDegree_le_of_dvd hh₁_dvd_dh₁ hdh₁_ne0
        have hlt := Polynomial.natDegree_derivative_lt hh₁_deg_pos.ne'
        omega
      have hdh₂0 : Polynomial.derivative h₂ = 0 := by
        rw [hdh₁0, zero_mul, zero_add] at hprod_deriv
        exact (mul_eq_zero.mp hprod_deriv).resolve_left hh₁_monic.ne_zero
      let g₁ : K[X] := Polynomial.contract p h₁
      let g₂ : K[X] := Polynomial.contract p h₂
      have hh₁_exp : Polynomial.expand K p g₁ = h₁ := Polynomial.expand_contract p hdh₁0 hp0
      have hh₂_exp : Polynomial.expand K p g₂ = h₂ := Polynomial.expand_contract p hdh₂0 hp0
      have hg_eq : g = g₁ * g₂ := Polynomial.expand_injective hp_pos (by
        rw [← hfg, hf_fact, map_mul, hh₁_exp, hh₂_exp])
      have hg₁_not_unit : ¬ IsUnit g₁ := fun hu => by
        have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have h1 : h₁.natDegree = 0 := by
          rw [← hh₁_exp, Polynomial.natDegree_expand, hd0, zero_mul]
        omega
      have hg₂_not_unit : ¬ IsUnit g₂ := fun hu => by
        have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have h2 : h₂.natDegree = 0 := by
          rw [← hh₂_exp, Polynomial.natDegree_expand, hd0, zero_mul]
        omega
      rcases hg_irr.isUnit_or_isUnit hg_eq with hu₁ | hu₂
      · exact hg₁_not_unit hu₁
      · exact hg₂_not_unit hu₂

/-- Explicit indexed-sum companion to **Theorem 10.8** (§10.6, printed p. 88 / PDF p. 96), matching
Garling's displayed formula `f(x) = a_0 + a_1 x^p + ⋯ + a_{n-1} x^{(n-1)p} + x^{np} = g(x^p)` verbatim
for all `n : ℕ` and `a : Fin n → K`. -/
theorem theorem_10_8_sum {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p) (hp_pos : 0 < p)
    (n : ℕ) (a : Fin n → K) :
    let g : K[X] := (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) + Polynomial.X ^ n
    let f : K[X] :=
      (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ ((i : ℕ) * p)) + Polynomial.X ^ (n * p)
    f = Polynomial.expand K p g ∧
    (IsGarlingIrreducible f ↔
      IsGarlingIrreducible g ∧ ∃ i : Fin n, ¬ ∃ b : K, a i = b ^ p) := by
  intro g f
  have hfg : f = Polynomial.expand K p g := by
    dsimp [f, g]
    rw [map_add, map_sum, map_pow, Polynomial.expand_X, ← pow_mul, mul_comm p n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.expand_C, map_pow, Polynomial.expand_X, ← pow_mul, mul_comm p (i : ℕ)]
  have hsum_deg_lt : ∀ (m : ℕ), 0 < m → ∀ (c : Fin m → K),
      (∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree < m := by
    intro m hm_pos c
    refine (Polynomial.natDegree_sum_le _ _).trans_lt ?_
    rw [Finset.fold_max_lt]
    refine ⟨hm_pos, fun i _ => ?_⟩
    calc (Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).natDegree
        ≤ (Polynomial.C (c i)).natDegree + (Polynomial.X ^ (i : ℕ) : K[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ = (i : ℕ) := by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
      _ < m := i.isLt
  have hg_monic : g.Monic := by
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · dsimp [g]; simp
    · dsimp [g]
      rw [add_comm]
      have hdeg_lt :
          (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree <
            (Polynomial.X ^ n : K[X]).degree := by
        rw [Polynomial.degree_X_pow]
        exact Polynomial.degree_le_natDegree.trans_lt
          (WithBot.coe_lt_coe.mpr (hsum_deg_lt n hn_pos a))
      exact (Polynomial.monic_X_pow n).add_of_left hdeg_lt
  have hf_monic : f.Monic := hfg ▸ hg_monic.expand hp_pos
  refine ⟨hfg, (theorem_10_8 hchar hp_pos hf_monic hfg).trans (and_congr_right fun _ => ?_)⟩
  -- Compare `¬ ∀ i : ℕ, ∃ b, g.coeff i = b ^ p` with `∃ i : Fin n, ¬ ∃ b, a i = b ^ p`.
  have hg_coeff : ∀ k : ℕ,
      g.coeff k = if hk : k < n then a ⟨k, hk⟩ else if k = n then 1 else 0 := by
    intro k
    dsimp [g]
    rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkn : k < n
    · have hne_kn : k ≠ n := ne_of_lt hkn
      simp only [hkn, ↓reduceDIte, hne_kn, ↓reduceIte, add_zero]
      rw [Finset.sum_eq_single ⟨k, hkn⟩]
      · simp
      · intro j _ hjk
        have hne : k ≠ (j : ℕ) := fun h => hjk (Fin.ext h.symm)
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    · by_cases hkeq : k = n
      · subst hkeq
        simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte]
        have h0 : (∑ x : Fin k, a x * if k = (x : ℕ) then (1 : K) else 0) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          have hne : k ≠ (x : ℕ) := (ne_of_lt x.isLt).symm
          simp [hne]
        rw [h0, zero_add]
      · simp only [hkn, ↓reduceDIte, hkeq, ↓reduceIte, add_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        have hlt_x : (x : ℕ) < n := x.isLt
        have hne : k ≠ (x : ℕ) := by omega
        simp [hne]
  constructor
  · intro hnot
    by_contra hnone
    have hnone' : ∀ i : Fin n, ∃ b : K, a i = b ^ p :=
      fun i => Classical.not_not.mp fun h => hnone ⟨i, h⟩
    apply hnot
    intro k
    rw [hg_coeff k]
    by_cases hkn : k < n
    · simp only [hkn, ↓reduceDIte]
      exact hnone' ⟨k, hkn⟩
    · by_cases hkeq : k = n
      · subst hkeq
        simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte]
        exact ⟨1, (one_pow p).symm⟩
      · simp only [hkn, ↓reduceDIte, hkeq, ↓reduceIte]
        exact ⟨0, (zero_pow hp_pos.ne').symm⟩
  · rintro ⟨i, hi⟩ hall
    obtain ⟨b, hb⟩ := hall i.1
    rw [hg_coeff i.1] at hb
    simp only [i.isLt, ↓reduceDIte] at hb
    exact hi ⟨b, hb⟩

/-- Helper: if `char K = p ≠ 0` and the Frobenius monomorphism `garlingFrobenius K hchar hp0` is
surjective, then every polynomial in `K[x]` is separable (`IsGarlingSeparablePoly`), proved directly
via `Theorem 10.6` (`theorem_10_6_expand`) and `Theorem 10.8` as on printed p. 89. -/
private theorem isGarlingSeparablePoly_of_frobenius_surjective {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0)
    (hsurj : Function.Surjective (garlingFrobenius K hchar hp0)) (f : K[X]) :
    IsGarlingSeparablePoly f := by
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  intro q hq_irr _
  by_contra hnot_sep
  -- Rescale `q` to monic `q₁ = q * C q.leadingCoeff⁻¹`.
  let q₁ : K[X] := q * Polynomial.C q.leadingCoeff⁻¹
  have hq₁_monic : q₁.Monic := Polynomial.monic_mul_leadingCoeff_inv hq_irr.ne_zero
  have hlc_ne0 : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_irr.ne_zero
  have hassoc : Associated q q₁ :=
    associated_mul_unit_right q _ (Polynomial.isUnit_C.mpr (inv_ne_zero hlc_ne0).isUnit)
  have hq₁_irr : Irreducible q₁ := hassoc.irreducible hq_irr
  have hq₁_garling_irr : IsGarlingIrreducible q₁ := (isGarlingIrreducible_iff q₁).mpr hq₁_irr
  have hq₁_not_poly : ¬ IsGarlingSeparablePoly q₁ := fun hpoly₁ => by
    have hq₁_s : q₁.Separable := (isGarlingSeparablePoly_of_irreducible_iff hq₁_irr).mp hpoly₁
    have hq_s : q.Separable := hq₁_s.of_dvd hassoc.dvd
    exact hnot_sep ((isGarlingSeparableIrreducible_iff_separable hq_irr).mpr hq_s)
  -- By `Theorem 10.6`, `q₁ = expand K p g` for some `g ∈ K[x]`.
  obtain ⟨_, g, hq₁_exp⟩ := (theorem_10_6_expand hq₁_garling_irr).mp hq₁_not_poly
  rw [hchar] at hq₁_exp
  -- Since Frobenius is surjective, every `g.coeff i` is a `p`th power, contradicting `Theorem 10.8`!
  have hall_pow : ∀ i : ℕ, ∃ b : K, g.coeff i = b ^ p := fun i => by
    obtain ⟨b, hb⟩ := hsurj (g.coeff i)
    exact ⟨b, hb.symm⟩
  have hnot_all :=
    ((theorem_10_8 hchar hp_prime.pos hq₁_monic hq₁_exp).mp hq₁_garling_irr).2
  exact hnot_all hall_pow

/-- **Corollary** [to Theorem 10.8] (§10.6, printed p. 89 / PDF p. 97):
*"Suppose that `char K = p > 0` and that `K` is algebraic over its prime subfield. Then every
polynomial in `K[x]` is separable."*

Proved directly from the `Corollary` to `Theorem 10.7` (`corollary_to_theorem_10_7`), `Theorem 10.6`,
and `Theorem 10.8`, matching Garling's proof on p. 89 (and holding literally for all `f ∈ K[x]`,
including `f = 0`). -/
theorem corollary_to_theorem_10_8 {K : Type*} [Field K] {p : ℕ}
    (hchar : ringChar K = p) (hp_pos : 0 < p)
    (halg : IsAlgebraicExtension (primeSubfield K) K) (f : K[X]) :
    IsGarlingSeparablePoly f :=
  isGarlingSeparablePoly_of_frobenius_surjective hchar hp_pos.ne'
    (corollary_to_theorem_10_7 hchar hp_pos.ne' halg).2 f

/-- **§10.6 Prose Inseparable Irreducible Example** (printed p. 89 / PDF p. 97):
*"For example, let `K = ℤ_p(α)`, where `α` is transcendental over `ℤ_p`. Then `x^p - α` is an
inseparable irreducible polynomial over `K`, since `x - α` is certainly irreducible and `-α` has no
`p`th root in `K`. If `L : K` is a splitting field for `x^p - α` and `β` is a root of `x^p - α` in
`L`, then `(x - β)^p = x^p - β^p = x^p - α` in `L[x]`, so that `x^p - α` has just one root (counted
without multiplicity) in `L`."* -/
theorem section_10_6_inseparable_example {p : ℕ} (hp : Nat.Prime p) :
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let K := FractionRing (ZMod p)[X]
    let α : K := ratFuncVar (ZMod p)
    let f : K[X] := Polynomial.X ^ p - Polynomial.C α
    (¬ ∃ b : K, -α = b ^ p) ∧
    IsGarlingIrreducible f ∧
    ¬ IsGarlingSeparableIrreducible f ∧
    ¬ IsGarlingSeparablePoly f ∧
    (∀ (L : Type u) [Field L] [Algebra K L] (β : L),
      Polynomial.aeval β f = 0 →
        ((Polynomial.X : L[X]) - Polynomial.C β) ^ p = f.map (algebraMap K L) ∧
        ∀ γ : L, Polynomial.aeval γ f = 0 → γ = β) := by
  have _ : Fact (Nat.Prime p) := ⟨hp⟩
  intro K α f
  let ι := algebraMap (ZMod p)[X] K
  have hι_inj : Function.Injective ι := IsFractionRing.injective (ZMod p)[X] K
  have hcharK : ringChar K = p := by
    have hcharZ : ringChar (ZMod p)[X] = p := ringChar.eq (ZMod p)[X] p
    have hdvd1 : ringChar K ∣ p :=
      (ringChar.spec K p).mp (by
        have h0 : ((p : ℕ) : (ZMod p)[X]) = 0 :=
          (ringChar.spec (ZMod p)[X] p).mpr (dvd_of_eq hcharZ)
        rw [← map_natCast ι, h0, map_zero])
    have hdvd2 : ringChar (ZMod p)[X] ∣ ringChar K :=
      (ringChar.spec (ZMod p)[X] (ringChar K)).mp (hι_inj (by
        rw [map_natCast, ringChar.Nat.cast_ringChar, map_zero]))
    rw [hcharZ] at hdvd2
    exact Nat.dvd_antisymm hdvd1 hdvd2
  -- 1. Show `-α` has no `p`th root in `K = FractionRing (ZMod p)[X]` by polynomial degrees mod `p`.
  have hno_pth_root : ¬ ∃ b : K, -α = b ^ p := by
    rintro ⟨b, hb⟩
    obtain ⟨u, v, hv_mem, huv⟩ := IsFractionRing.div_surjective (A := (ZMod p)[X]) b
    have hv0 : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv_mem
    have hιv0 : ι v ≠ 0 := fun h0 => hv0 (hι_inj (h0.trans (map_zero ι).symm))
    have hιvp0 : (ι v) ^ p ≠ 0 := pow_ne_zero p hιv0
    have hdiv : -ι Polynomial.X = (ι u) ^ p / (ι v) ^ p := by
      dsimp [α, ratFuncVar] at hb
      rwa [← huv, div_pow] at hb
    have hclear : -ι Polynomial.X * (ι v) ^ p = (ι u) ^ p :=
      (eq_div_iff hιvp0).mp hdiv
    have hpoly_eq : -Polynomial.X * v ^ p = u ^ p := hι_inj (by
      simpa only [map_mul, map_neg, map_pow] using hclear)
    have hlhs0 : (-Polynomial.X * v ^ p : (ZMod p)[X]) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr Polynomial.X_ne_zero) (pow_ne_zero p hv0)
    have _hu0 : u ≠ 0 := fun h0 => hlhs0 (by rw [hpoly_eq, h0, zero_pow hp.ne_zero])
    have hdeg_eq := congrArg Polynomial.natDegree hpoly_eq
    rw [Polynomial.natDegree_mul (neg_ne_zero.mpr Polynomial.X_ne_zero) (pow_ne_zero p hv0),
      Polynomial.natDegree_neg, Polynomial.natDegree_X, Polynomial.natDegree_pow,
      Polynomial.natDegree_pow] at hdeg_eq
    have hmod : (1 + p * v.natDegree) % p = (p * u.natDegree) % p := congrArg (· % p) hdeg_eq
    rw [Nat.add_mul_mod_self_left, Nat.mul_mod_right, Nat.mod_eq_of_lt hp.one_lt] at hmod
    omega
  -- 2. Deduce `Irreducible (X^p - C α)` from `Theorem 10.8` applied to `g = X - C α`.
  let g : K[X] := Polynomial.X - Polynomial.C α
  have hfg : f = Polynomial.expand K p g := by
    dsimp [f, g]
    rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C α hp.ne_zero
  have hg_irr : IsGarlingIrreducible g :=
    (isGarlingIrreducible_iff g).mpr (Polynomial.irreducible_X_sub_C α)
  have hnot_all_g : ¬ ∀ i : ℕ, ∃ b : K, g.coeff i = b ^ p := by
    intro hall
    obtain ⟨b, hb⟩ := hall 0
    have hc0 : g.coeff 0 = -α := by simp [g]
    exact hno_pth_root ⟨b, hc0 ▸ hb⟩
  have hf_garling_irr : IsGarlingIrreducible f :=
    (theorem_10_8 hcharK hp.pos hf_monic hfg).mpr ⟨hg_irr, hnot_all_g⟩
  have hf_irr : Irreducible f := (isGarlingIrreducible_iff f).mp hf_garling_irr
  -- 3. Deduce inseparability from `Theorem 10.6` (`theorem_10_6_expand`).
  have hf_not_sep_poly : ¬ IsGarlingSeparablePoly f :=
    (theorem_10_6_expand hf_garling_irr).mpr
      ⟨by rw [hcharK]; exact hp.pos, g, by rw [hcharK]; exact hfg⟩
  have hf_not_sep_irr : ¬ IsGarlingSeparableIrreducible f := fun hsep =>
    hf_not_sep_poly ((isGarlingSeparablePoly_of_irreducible_iff hf_irr).mpr
      ((isGarlingSeparableIrreducible_iff_separable hf_irr).mp hsep))
  -- 4. In any extension `L : K`, if `β^p = α` then `(X - C β)^p = X^p - C α` in `L[X]`.
  refine ⟨hno_pth_root, hf_garling_irr, hf_not_sep_irr, hf_not_sep_poly, ?_⟩
  intro L _ _ β hβ
  have hcharL : ringChar L = p := by
    have hdvd1 : ringChar L ∣ p :=
      (ringChar.spec L p).mp (by
        have h0 : ((p : ℕ) : K) = 0 := (ringChar.spec K p).mpr (dvd_of_eq hcharK)
        rw [← map_natCast (algebraMap K L), h0, map_zero])
    have hdvd2 : ringChar K ∣ ringChar L :=
      (ringChar.spec K (ringChar L)).mp ((algebraMap K L).injective (by
        rw [map_natCast, ringChar.Nat.cast_ringChar, map_zero]))
    rw [hcharK] at hdvd2
    exact Nat.dvd_antisymm hdvd1 hdvd2
  have hβp : β ^ p = algebraMap K L α := by
    dsimp [f] at hβ
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hβ
    exact sub_eq_zero.mp hβ
  have hfactor : ((Polynomial.X : L[X]) - Polynomial.C β) ^ p = f.map (algebraMap K L) := by
    rw [poly_pow_char_eq_expand_map_frobenius hcharL hp.ne_zero
        ((Polynomial.X : L[X]) - Polynomial.C β),
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, garlingFrobenius_apply,
      map_sub, Polynomial.expand_X, Polynomial.expand_C, hβp]
    dsimp [f]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  refine ⟨hfactor, fun γ hγ => ?_⟩
  have hγ_eval : (((Polynomial.X : L[X]) - Polynomial.C β) ^ p).eval γ = 0 := by
    rw [hfactor, Polynomial.eval_map, ← Polynomial.aeval_def, hγ]
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hγ_eval
  exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp hγ_eval)

/-- Garling's prose definition of a *perfect field* (§10.6, printed p. 90 / PDF p. 98):
*"A field `K` is said to be **perfect** if every polynomial in `K[x]` is separable."* -/
def IsGarlingPerfectField (K : Type*) [Field K] : Prop :=
  ∀ f : K[X], IsGarlingSeparablePoly f

/-- Exact equivalence between Garling's `IsGarlingPerfectField K` (§10.6, printed p. 90 / PDF p. 98) and Mathlib's
`PerfectField K` (`∀ {f : K[X]}, Irreducible f → f.Separable`). -/
theorem isGarlingPerfectField_iff_perfectField (K : Type*) [Field K] :
    IsGarlingPerfectField K ↔ PerfectField K := by
  constructor
  · intro hperf
    refine ⟨fun {f} hf => ?_⟩
    exact (isGarlingSeparableIrreducible_iff_separable hf).mp (hperf f f hf dvd_rfl)
  · intro hperf f g hg _
    exact (isGarlingSeparableIrreducible_iff_separable hg).mpr (hperf.separable_of_irreducible hg)

/-- Characteristic-`0` fields are perfect (`Corollary` to `Theorem 10.6`, §10.6 prose p. 89). -/
theorem isGarlingPerfectField_of_char_zero {K : Type*} [Field K] (hchar : ringChar K = 0) :
    IsGarlingPerfectField K :=
  fun f => corollary_to_theorem_10_6 hchar f

/-- **Exercise 10.7** (§10.6, printed p. 90 / PDF p. 98):
*"Suppose that `char K = p ≠ 0`. Show that `K` is perfect if and only if the Frobenius monomorphism
is an automorphism."* -/
theorem exercise_10_7 {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p) (hp0 : p ≠ 0) :
    IsGarlingPerfectField K ↔ IsFieldAutomorphism (garlingFrobenius K hchar hp0) := by
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  constructor
  · -- (`⇒`) Suppose `K` is perfect; `φ` is already a monomorphism by `Theorem 10.7`. For any `α ∈ K`,
    -- if `α` is not in the image of `φ`, then `-α` has no `p`th root (since `(-b)^p = -b^p`), so
    -- `X^p - C α` is irreducible by `Theorem 10.8` yet inseparable by `Theorem 10.6`.
    intro hperf
    obtain ⟨_, hmono, _⟩ := theorem_10_7 hchar hp0
    refine ⟨hmono, fun α => ?_⟩
    by_contra hnot_mem
    have hno_neg : ¬ ∃ b : K, -α = b ^ p := by
      rintro ⟨b, hb⟩
      apply hnot_mem
      refine ⟨-b, ?_⟩
      rw [map_neg, garlingFrobenius_apply, ← hb, neg_neg]
    let g : K[X] := Polynomial.X - Polynomial.C α
    let f : K[X] := Polynomial.X ^ p - Polynomial.C α
    have hfg : f = Polynomial.expand K p g := by
      dsimp [f, g]
      rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
    have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C α hp0
    have hg_irr : IsGarlingIrreducible g :=
      (isGarlingIrreducible_iff g).mpr (Polynomial.irreducible_X_sub_C α)
    have hnot_all : ¬ ∀ i : ℕ, ∃ b : K, g.coeff i = b ^ p := by
      intro hall
      obtain ⟨b, hb⟩ := hall 0
      have hc0 : g.coeff 0 = -α := by simp [g]
      exact hno_neg ⟨b, hc0 ▸ hb⟩
    have hf_garling_irr : IsGarlingIrreducible f :=
      (theorem_10_8 hchar hp_prime.pos hf_monic hfg).mpr ⟨hg_irr, hnot_all⟩
    have hf_not_sep : ¬ IsGarlingSeparablePoly f :=
      (theorem_10_6_expand hf_garling_irr).mpr ⟨hchar ▸ hp_prime.pos, g, hchar.symm ▸ hfg⟩
    exact hf_not_sep (hperf f)
  · -- (`⇐`) Proved in `isGarlingSeparablePoly_of_frobenius_surjective`.
    intro hauto
    exact isGarlingSeparablePoly_of_frobenius_surjective hchar hp0 hauto.2

/-- Universe-polymorphic forward direction of **Exercise 10.8** (§10.6, printed p. 90 / PDF p. 98):
over a perfect field `K : Type u`, every algebraic (and hence every finite) extension `L : Type v`
is separable. -/
theorem exercise_10_8_mp_univ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hperf : IsGarlingPerfectField K) (halg : IsAlgebraicExtension K L) :
    IsGarlingSeparableExtension K L :=
  fun α => ⟨halg α, hperf (minpoly K α)⟩

/-- **Exercise 10.8** (§10.6, printed p. 90 / PDF p. 98):
*"Show that a field `K` is perfect if and only if every finite extension of `K` is separable."*

Proved directly via `Theorem 4.6` (`theorem_4_6`: finite extensions are algebraic) for `(⇒)` and
`Theorem 7.2` (`theorem_7_2`: existence of a finite root extension `L : K` of degree `deg g` for any
irreducible `g ∈ K[x]`) for `(⇐)`. -/
theorem exercise_10_8 {K : Type u} [Field K] :
    IsGarlingPerfectField K ↔
      ∀ (L : Type u) [Field L] [Algebra K L],
        IsFiniteExtension K L → IsGarlingSeparableExtension K L := by
  constructor
  · intro hperf L _ _ hfin
    exact exercise_10_8_mp_univ hperf ((theorem_4_6 K L).1.mp hfin).1
  · intro hfin_sep f g hg_irr _
    obtain ⟨L, instFL, instAKL, α, _, halgL, _, hdegL, haeval⟩ := theorem_7_2 hg_irr rfl
    let _ : Field L := instFL
    let _ : Algebra K L := instAKL
    have hfinL : IsFiniteExtension K L := by
      unfold IsFiniteExtension
      rw [hdegL]
      exact ENat.natCast_lt_top _
    have hsep_α : IsGarlingSeparableElement K α := hfin_sep L hfinL α
    have hmin_sep : (minpoly K α).Separable := (isGarlingSeparableElement_iff K α).mp hsep_α
    have hint_α : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halgL α)
    have hmin_irr : Irreducible (minpoly K α) := minpoly.irreducible hint_α
    have hdvd : minpoly K α ∣ g := minpoly.dvd K α haeval
    -- Since both `minpoly K α` and `g` are irreducible, `g ∣ minpoly K α` as well.
    obtain ⟨u, hu⟩ := hdvd
    have hu_unit : IsUnit u := (hg_irr.isUnit_or_isUnit hu).resolve_left hmin_irr.not_isUnit
    obtain ⟨u₀, rfl⟩ := hu_unit
    have hg_dvd_min : g ∣ minpoly K α := ⟨↑u₀⁻¹, by rw [hu, mul_assoc, Units.mul_inv, mul_one]⟩
    exact (isGarlingSeparableIrreducible_iff_separable hg_irr).mpr (hmin_sep.of_dvd hg_dvd_min)

/-- **Exercise 10.9** (§10.6, printed p. 90 / PDF p. 98):
*"Suppose that `char K = p > 0` and that `f` is an irreducible polynomial in `K[x]`. Show that there
exist a non-negative integer `n` and a separable irreducible polynomial `g` in `K[x]` such that
`f(x) = g(x^{p^n})`."* -/
theorem exercise_10_9 {K : Type*} [Field K] {p : ℕ} (hchar : ringChar K = p) (hp_pos : 0 < p)
    {f : K[X]} (hf_irr : IsGarlingIrreducible f) :
    ∃ (n : ℕ) (g : K[X]),
      f = Polynomial.expand K (p ^ n) g ∧
      IsGarlingIrreducible g ∧
      IsGarlingSeparableIrreducible g ∧
      IsGarlingSeparablePoly g := by
  have hp0 : p ≠ 0 := hp_pos.ne'
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  have hf : Irreducible f := (isGarlingIrreducible_iff f).mp hf_irr
  induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases hsep : IsGarlingSeparableIrreducible f
    · have hf_s : f.Separable := (isGarlingSeparableIrreducible_iff_separable hf).mp hsep
      have hpoly : IsGarlingSeparablePoly f :=
        (isGarlingSeparablePoly_of_irreducible_iff hf).mpr hf_s
      refine ⟨0, f, ?_, hf_irr, hsep, hpoly⟩
      rw [pow_zero, Polynomial.expand_one]
    · -- By `Theorem 10.6` (`theorem_10_6_expand`), `f = expand K p f₁` with `Irreducible f₁` and
      -- `f₁.natDegree < f.natDegree`.
      have hnot_poly : ¬ IsGarlingSeparablePoly f := fun hpoly =>
        hsep ((isGarlingSeparableIrreducible_iff_separable hf).mpr
          ((isGarlingSeparablePoly_of_irreducible_iff hf).mp hpoly))
      obtain ⟨_, f₁, hf_exp⟩ := (theorem_10_6_expand hf_irr).mp hnot_poly
      rw [hchar] at hf_exp
      have hf₁_irr : Irreducible f₁ := Polynomial.of_irreducible_expand hp0 (hf_exp ▸ hf)
      have hf₁_deg_pos : 0 < f₁.natDegree := hf₁_irr.natDegree_pos
      have hf₁_lt : f₁.natDegree < d := by
        have hmul : d = f₁.natDegree * p := by
          rw [← hd, hf_exp, Polynomial.natDegree_expand]
        have hp2 := hp_prime.one_lt
        nlinarith
      obtain ⟨m, g, hf₁_eq, hg_irr, hg_sep_irr, hg_sep_poly⟩ :=
        ih f₁.natDegree hf₁_lt ((isGarlingIrreducible_iff f₁).mpr hf₁_irr) hf₁_irr rfl
      refine ⟨m + 1, g, ?_, hg_irr, hg_sep_irr, hg_sep_poly⟩
      rw [hf_exp, hf₁_eq, Polynomial.expand_expand, ← pow_succ']

/-- Garling's definition of a *totally inseparable* algebraic extension inside `Exercise 10.10`
(§10.6, printed p. 90 / PDF p. 98):
*"An algebraic extension `L : K` is said to be **totally inseparable** if no element of `L \ K` is
separable over `K`."* -/
def IsGarlingTotallyInseparable (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsAlgebraicExtension K L ∧
    ∀ γ : L, γ ∉ Set.range (algebraMap K L) → ¬ IsGarlingSeparableElement K γ

/-- **Exercise 10.10** (§10.6, printed p. 90 / PDF p. 98):
*"An algebraic extension `L : K` is said to be **totally inseparable** if no element of `L \ K` is
separable over `K`. Suppose that `char K = p > 0`, that `L : K` is totally inseparable and that
`β ∈ L`. Show that the minimal polynomial of `β` over `K` is of the form `x^{p^n} - α`
(where `α ∈ K`)."* -/
theorem exercise_10_10 {K L : Type*} [Field K] [Field L] [Algebra K L] {p : ℕ}
    (hchar : ringChar K = p) (hp_pos : 0 < p)
    (htot : IsGarlingTotallyInseparable K L) (β : L) :
    ∃ (n : ℕ) (α : K), minpoly K β = Polynomial.X ^ (p ^ n) - Polynomial.C α := by
  have hint_β : IsIntegral K β := (isGarlingAlgebraic_iff_isIntegral K β).mp (htot.1 β)
  have hf_monic : (minpoly K β).Monic := minpoly.monic hint_β
  have hf_irr : Irreducible (minpoly K β) := minpoly.irreducible hint_β
  -- By `Exercise 10.9`, `minpoly K β = g(x^{p^n})` for some irreducible separable `g ∈ K[x]`.
  obtain ⟨n, g, hfg, hg_garling_irr, _, hg_sep_poly⟩ :=
    exercise_10_9 hchar hp_pos ((isGarlingIrreducible_iff _).mpr hf_irr)
  have hg_irr : Irreducible g := (isGarlingIrreducible_iff g).mp hg_garling_irr
  have hp_pow_pos : 0 < p ^ n := pow_pos hp_pos n
  have hg_monic : g.Monic := (Polynomial.monic_expand_iff hp_pow_pos).mp (hfg ▸ hf_monic)
  -- Set `γ = β^{p^n} ∈ L`; then `g(γ) = (minpoly K β)(β) = 0`, so `minpoly K γ = g`.
  let γ : L := β ^ (p ^ n)
  have haeval_γ : Polynomial.aeval γ g = 0 := by
    dsimp [γ]
    rw [← Polynomial.expand_aeval, ← hfg, minpoly.aeval]
  have hmin_γ : minpoly K γ = g :=
    (minpoly.eq_of_irreducible_of_monic hg_irr haeval_γ hg_monic).symm
  -- Hence `γ` is separable over `K`; since `L : K` is totally inseparable, `γ ∈ K`!
  have hsep_γ : IsGarlingSeparableElement K γ := ⟨htot.1 γ, hmin_γ ▸ hg_sep_poly⟩
  have hγ_mem : γ ∈ Set.range (algebraMap K L) := by
    by_contra hnot_mem
    exact htot.2 γ hnot_mem hsep_γ
  obtain ⟨α, hα⟩ := hγ_mem
  have haeval_lin : Polynomial.aeval γ (Polynomial.X - Polynomial.C α) = 0 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hα, sub_self]
  have hmin_γ_lin : minpoly K γ = Polynomial.X - Polynomial.C α :=
    (minpoly.eq_of_irreducible_of_monic (Polynomial.irreducible_X_sub_C α) haeval_lin
      (Polynomial.monic_X_sub_C α)).symm
  have hg_eq : g = Polynomial.X - Polynomial.C α := hmin_γ.symm.trans hmin_γ_lin
  refine ⟨n, α, ?_⟩
  rw [hfg, hg_eq, map_sub, Polynomial.expand_X, Polynomial.expand_C]

/-- **Exercise 10.11** (§10.6, printed p. 90 / PDF p. 98):
*"Suppose that `char K = p ≠ 0`, that `f` is an irreducible polynomial in `K[x]`, and that `L : K`
is a splitting field for `f`. Show that there is a non-negative integer `n` such that every root of
`f` in `L` has multiplicity `p^n`. (Hint: use Exercise 10.3.)"*

Note on the parenthetical hint (`GARLING-STAGE10-ENUMERATION.md` / `PROGRESS.md`): the theorem
statement itself holds literally as printed, whereas for `n ≥ 1` we have `deg f ≥ p = char K` so
`Exercise 10.3`'s hypothesis `char K > deg f` does not apply directly; we prove the exact statement
via `Exercise 10.9` (`f(x) = g(x^{p^n})` with separable irreducible `g`) and root multiplicity under
`x ↦ x^{p^n}`. -/
theorem exercise_10_11 {K L : Type*} [Field K] [Field L] [Algebra K L] {p : ℕ}
    (hchar : ringChar K = p) (hp0 : p ≠ 0) {f : K[X]} (hf_irr : IsGarlingIrreducible f)
    (_hsplit : IsGarlingSplittingFieldExtension K L f) :
    ∃ n : ℕ, ∀ γ : L, Polynomial.aeval γ f = 0 →
      IsRootOfExactMultiplicity (f.map (algebraMap K L)) γ (p ^ n) ∧
      (f.map (algebraMap K L)).rootMultiplicity γ = p ^ n := by
  have hp_prime : Nat.Prime p := prime_of_ringChar_field hchar hp0
  have hcharL : ringChar L = p :=
    Nat.dvd_antisymm
      ((ringChar.spec L p).mp (by
        have h0 : ((p : ℕ) : K) = 0 := (ringChar.spec K p).mpr (dvd_of_eq hchar)
        rw [← map_natCast (algebraMap K L), h0, map_zero]))
      (hchar ▸ (ringChar.spec K (ringChar L)).mp ((algebraMap K L).injective (by
        rw [map_natCast, ringChar.Nat.cast_ringChar, map_zero])))
  have _ : CharP L p := charP_of_ringChar_eq hcharL
  have _ : Fact p.Prime := ⟨hp_prime⟩
  -- Decompose `f = expand K (p^n) g` with separable irreducible `g` via `Exercise 10.9`.
  obtain ⟨n, g, hfg, hg_garling_irr, hg_sep_irr, _⟩ :=
    exercise_10_9 hchar hp_prime.pos hf_irr
  have hf : Irreducible f := (isGarlingIrreducible_iff f).mp hf_irr
  have hg : Irreducible g := (isGarlingIrreducible_iff g).mp hg_garling_irr
  have hg_sep : g.Separable := (isGarlingSeparableIrreducible_iff_separable hg).mp hg_sep_irr
  let fL : L[X] := f.map (algebraMap K L)
  let gL : L[X] := g.map (algebraMap K L)
  have hfL0 : fL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf.ne_zero
  have hgL0 : gL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hg.ne_zero
  have hgL_sep : gL.Separable := hg_sep.map
  have hfL_exp : fL = Polynomial.expand L (p ^ n) gL := by
    dsimp [fL, gL]
    rw [hfg, Polynomial.map_expand]
  refine ⟨n, fun γ hγ => ?_⟩
  -- Show `γ^{p^n}` is a simple root (`rootMultiplicity = 1`) of `gL`.
  have hgL_root : gL.IsRoot (γ ^ (p ^ n)) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
      ← Polynomial.expand_aeval, ← hfg, hγ]
  have hge1 : 1 ≤ gL.rootMultiplicity (γ ^ (p ^ n)) :=
    (Polynomial.le_rootMultiplicity_iff hgL0).mpr (by
      rw [pow_one]
      exact Polynomial.dvd_iff_isRoot.mpr hgL_root)
  have hnot_ge2 : ¬ (2 ≤ gL.rootMultiplicity (γ ^ (p ^ n))) := by
    rw [Polynomial.le_rootMultiplicity_iff hgL0, sq]
    intro hdvd2
    have hunit : IsUnit (Polynomial.X - Polynomial.C (γ ^ (p ^ n))) :=
      hgL_sep.squarefree _ hdvd2
    have hd0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    have hd1 : (Polynomial.X - Polynomial.C (γ ^ (p ^ n))).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    omega
  have hmult_gL : gL.rootMultiplicity (γ ^ (p ^ n)) = 1 := by omega
  have hmult_fL : fL.rootMultiplicity γ = p ^ n := by
    rw [hfL_exp, Polynomial.rootMultiplicity_expand_pow (p := p), hmult_gL, mul_one]
  have hfL_root : fL.IsRoot γ := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def, hγ]
  have hexact : HasExactRootMultiplicity fL γ (p ^ n) :=
    (hasExactRootMultiplicity_iff_rootMultiplicity hfL0 γ (p ^ n)).mpr hmult_fL
  exact ⟨⟨hfL_root, hexact⟩, hmult_fL⟩

end Garling.Chapter10
