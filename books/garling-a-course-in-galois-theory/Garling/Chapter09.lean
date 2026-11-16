import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05
import Garling.Chapter06
import Garling.Chapter07
import Garling.Chapter08
import Mathlib.FieldTheory.Normal.Closure

/-!
# Chapter 9: Normal extensions

Formalization of Chapter 9 (*Normal extensions*, printed pp. 78–81 / PDF pp. 86–89) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986), covering both
sections and all 12 numbered scope-of-record items in exact source order:

- **§9.1 Basic properties** (printed pp. 78–80 / PDF pp. 86–88):
  prose definitions of *normal* extension (`IsGarlingNormal`, bridged to `Normal`) and its
  minimal-polynomial characterization, *splitting field extension for `S ⊆ K[x]`*
  (`IsGarlingSplittingFieldExtensionSet`) and the finite-`S` product remark, `Theorem 9.1`
  (proved via Garling's subfield-inclusion diamond using `Corollary 2` to `Theorem 4.6`,
  `Theorem 7.1`, `Theorem 7.3`, `Corollary 1` to `Theorem 7.4`, `Corollary 1` to `Theorem 7.5`,
  and `Theorem 4.2`), `Corollary 1` [to Theorem 9.1], the p. 80 generator-product remark, prose
  definition of *normal closure* (`IsGarlingNormalClosure`, bridged to abstract towers and to
  Mathlib's `IsNormalClosure`), `Corollary 2` [to Theorem 9.1], `Corollary 3` [to Theorem 9.1],
  and `Exercises 9.1`–`9.3`.
- **§9.2 Monomorphisms and automorphisms** (printed pp. 80–81 / PDF pp. 88–89):
  introductory prose counterexample `ℚ(2^{1/3}, ω) : ℚ` vs. `ℚ(2^{1/3}) : ℚ`, `Theorem 9.2`, and
  `Exercises 9.4`–`9.7`.
-/

namespace Garling.Chapter09

open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03
open Garling.Chapter04 Garling.Chapter05 Garling.Chapter06
open Garling.Chapter07 Garling.Chapter08
open scoped BigOperators Polynomial IntermediateField

universe u v w

/-! ## §9.1 Basic properties (printed pp. 78–80, PDF pp. 86–88) -/

/-- Garling's prose definition of a *normal* extension `L : K` (§9.1, printed p. 78 / PDF p. 86):
*"An extension `L : K` is said to be normal if it is algebraic and whenever `f` is an irreducible
polynomial in `K[x]` then either `f` splits over `L` or `f` has no roots in `L`."* -/
def IsGarlingNormal (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  IsAlgebraicExtension K L ∧
  ∀ f : K[X], Irreducible f →
    GarlingSplitsOver K L f ∨ ¬ ∃ α : L, Polynomial.aeval α f = 0

/-- Extension-triple formulation of a *normal* extension `(i, K, L)` (§4.2, p. 40; §9.1, p. 78). -/
def IsGarlingNormalTriple {K L : Type*} [Field K] [Field L]
    (ext : FieldExtensionTriple K L) : Prop :=
  letI : Algebra K L := ext.hom.toAlgebra
  IsGarlingNormal K L

private lemma natDegree_pos_of_irreducible {K : Type*} [Field K] {f : K[X]}
    (hf : Irreducible f) : 0 < f.natDegree := by
  by_contra hlt
  have h0 : f.natDegree = 0 := by omega
  have hfc : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
  have hc0 : f.coeff 0 ≠ 0 := fun h => hf.ne_zero (by rw [hfc, h, map_zero])
  exact hf.not_isUnit (hfc ▸ (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C)

/-- For an irreducible polynomial `f ∈ K[x]`, `f` has positive degree, so *"f splits over L"* and
*"f has no roots in L"* are mutually exclusive; hence inclusive `∨` and exclusive `Xor` (and
`Irreducible` vs. Chapter 3's `IsGarlingIrreducible`) coincide identically in `IsGarlingNormal`. -/
theorem isGarlingNormal_iff_garlingIrreducible_xor (K L : Type*) [Field K] [Field L]
    [Algebra K L] :
    IsGarlingNormal K L ↔
      IsAlgebraicExtension K L ∧
      ∀ f : K[X], IsGarlingIrreducible f →
        Xor (GarlingSplitsOver K L f) (¬ ∃ α : L, Polynomial.aeval α f = 0) := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h f hfg
    have hf : Irreducible f := (isGarlingIrreducible_iff f).mp hfg
    rcases h f hf with hsp | hno
    · left
      refine ⟨hsp, not_not.mpr ?_⟩
      obtain ⟨n, c, α, hexp⟩ := hsp
      obtain ⟨_, _, hn_deg, hroots⟩ := garlingSplitsExplicit_props hf.ne_zero hexp
      have hpos : 0 < n := by
        rw [hn_deg, garlingDegree]
        exact natDegree_pos_of_irreducible hf
      have hmem : α ⟨0, hpos⟩ ∈ f.rootSet L := hroots ▸ ⟨⟨0, hpos⟩, rfl⟩
      exact ⟨α ⟨0, hpos⟩, (Polynomial.mem_rootSet.mp hmem).2⟩
    · right
      refine ⟨hno, fun hsp => hno ?_⟩
      obtain ⟨n, c, α, hexp⟩ := hsp
      obtain ⟨_, _, hn_deg, hroots⟩ := garlingSplitsExplicit_props hf.ne_zero hexp
      have hpos : 0 < n := by
        rw [hn_deg, garlingDegree]
        exact natDegree_pos_of_irreducible hf
      have hmem : α ⟨0, hpos⟩ ∈ f.rootSet L := hroots ▸ ⟨⟨0, hpos⟩, rfl⟩
      exact ⟨α ⟨0, hpos⟩, (Polynomial.mem_rootSet.mp hmem).2⟩
  · intro h f hf
    rcases h f ((isGarlingIrreducible_iff f).mpr hf) with ⟨hsp, _⟩ | ⟨hno, _⟩
    · exact Or.inl hsp
    · exact Or.inr hno

/-- Prose characterization of normality (§9.1, printed p. 78 / PDF p. 86):
*"Clearly an algebraic extension `L : K` is normal if and only if the minimal polynomial over `K`
of each element of `L` splits over `L`."* -/
theorem isGarlingNormal_iff_minpoly_splits (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingNormal K L ↔
      IsAlgebraicExtension K L ∧ ∀ α : L, GarlingSplitsOver K L (minpoly K α) := by
  constructor
  · rintro ⟨halg, hnorm⟩
    refine ⟨halg, fun α => ?_⟩
    have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
    rcases hnorm (minpoly K α) (minpoly.irreducible hint) with hsp | hno
    · exact hsp
    · exact False.elim (hno ⟨α, minpoly.aeval K α⟩)
  · rintro ⟨halg, hmin⟩
    refine ⟨halg, fun f hfirr => ?_⟩
    by_cases hroot : ∃ α : L, Polynomial.aeval α f = 0
    · left
      obtain ⟨α, hα⟩ := hroot
      have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
      have hdvd : minpoly K α ∣ f := minpoly.dvd K α hα
      have hassoc : Associated (minpoly K α) f :=
        associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hfirr hdvd)
      obtain ⟨u, hu⟩ := hassoc
      have hu0 : (u : K[X]).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
      have huc : (u : K[X]) = Polynomial.C ((u : K[X]).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hu0
      rw [garlingSplitsOver_iff_splits]
      have hsp_min : ((minpoly K α).map (algebraMap K L)).Splits :=
        (garlingSplitsOver_iff_splits K L (minpoly K α)).mp (hmin α)
      rw [← hu, huc, Polynomial.map_mul, Polynomial.map_C]
      exact Polynomial.Splits.mul hsp_min (Polynomial.Splits.C _)
    · exact Or.inr hroot

/-- Exact bridge between Garling's `IsGarlingNormal K L` (§9.1, p. 78) and Mathlib's
`Normal K L`. -/
theorem isGarlingNormal_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsGarlingNormal K L ↔ Normal K L := by
  rw [isGarlingNormal_iff_minpoly_splits, normal_iff]
  constructor
  · rintro ⟨halg, hsp⟩ α
    exact ⟨(isGarlingAlgebraic_iff_isIntegral K α).mp (halg α),
      (garlingSplitsOver_iff_splits K L (minpoly K α)).mp (hsp α)⟩
  · intro h
    exact ⟨fun α => (isGarlingAlgebraic_iff_isIntegral K α).mpr (h α).1,
      fun α => (garlingSplitsOver_iff_splits K L (minpoly K α)).mpr (h α).2⟩

/-- Helper: transporting `IsGarlingNormal` across a `K`-algebra equivalence `L ≃ₐ[K] L'`. -/
theorem isGarlingNormal_congr {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    IsGarlingNormal K L ↔ IsGarlingNormal K L' := by
  rw [isGarlingNormal_iff, isGarlingNormal_iff]
  exact e.transfer_normal

/-- Helper: if `f ≠ 0` in `K[X]` splits over an intermediate field `M : IntermediateField K L`,
then every root of `f` in `L` belongs to `M`. -/
theorem mem_of_garlingSplitsOver_intermediateField {K L : Type*} [Field K] [Field L] [Algebra K L]
    {M : IntermediateField K L} {f : K[X]} (hf : f ≠ 0)
    (hsplitM : GarlingSplitsOver K M f) {α : L} (hα : Polynomial.aeval α f = 0) :
    α ∈ M := by
  obtain ⟨n, c, β, hβM, hexp⟩ := (garlingSplitsOver_intermediateField_iff M f).mp hsplitM
  have hroots : Set.range β = f.rootSet L := (garlingSplitsExplicit_props hf hexp).2.2.2
  have hmem : α ∈ Set.range β := hroots ▸ Polynomial.mem_rootSet.mpr ⟨hf, hα⟩
  obtain ⟨j, rfl⟩ := hmem
  exact hβM j

/-- Helper: if `f, g ≠ 0` in `K[X]`, then `f * g` splits over `L` iff both `f` and `g` split
over `L`. -/
theorem garlingSplitsOver_mul_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    GarlingSplitsOver K L (f * g) ↔ GarlingSplitsOver K L f ∧ GarlingSplitsOver K L g := by
  rw [garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits, garlingSplitsOver_iff_splits,
    Polynomial.map_mul]
  exact Polynomial.splits_mul
    ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf)
    ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hg)

/-- Helper: for any finite family of non-zero polynomials `f_i ∈ K[X]` (`i ∈ s`), their product
`∏ i ∈ s, f_i` is non-zero and splits over `L` iff every `f_i` splits over `L`. -/
theorem garlingSplitsOver_finset_prod_iff {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (s : Finset ι) (f : ι → K[X]) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i) ≠ 0 ∧
    (GarlingSplitsOver K L (∏ i ∈ s, f i) ↔ ∀ i ∈ s, GarlingSplitsOver K L (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ⟨fun _ i hi => (Finset.notMem_empty i hi).elim, fun _ => ?_⟩⟩
    rw [Finset.prod_empty, garlingSplitsOver_iff_splits, Polynomial.map_one]
    exact Polynomial.Splits.one
  | @insert a s ha ih =>
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨hprod0, hiff⟩ := ih hs0
    rw [Finset.prod_insert ha]
    refine ⟨mul_ne_zero ha0 hprod0, ?_⟩
    rw [garlingSplitsOver_mul_iff ha0 hprod0, hiff]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact h1
      · exact h2 i his
    · intro hall
      exact ⟨hall a (Finset.mem_insert_self a s),
        fun i hi => hall i (Finset.mem_insert_of_mem hi)⟩

/-- Garling's prose definition of a *splitting field extension for `S`* (§9.1, printed p. 78 /
PDF p. 86):
*"Suppose that `K` is a field, and that `S` is a subset of `K[x]`. We say that an extension `L`
of `K` is a splitting field extension for `S` if each `f` in `S` splits over `L`, and if
`L ⊇ L' ⊇ K` and each `f` in `S` splits over `L'`, then `L' = L`."* -/
def IsGarlingSplittingFieldExtensionSet (K L : Type*) [Field K] [Field L] [Algebra K L]
    (S : Set K[X]) : Prop :=
  (∀ f ∈ S, GarlingSplitsOver K L f) ∧
  ∀ L' : IntermediateField K L, (∀ f ∈ S, GarlingSplitsOver K L' f) → L' = ⊤

/-- Equivalence between `IsGarlingSplittingFieldExtensionSet` (stated with `IntermediateField K L`)
and the literal `Subfield L` inclusion formulation `L ⊇ L' ⊇ K ⟹ L' = L` on printed p. 78. -/
theorem isGarlingSplittingFieldExtensionSet_iff_subfield (K L : Type*) [Field K] [Field L]
    [Algebra K L] (S : Set K[X]) :
    IsGarlingSplittingFieldExtensionSet K L S ↔
      (∀ f ∈ S, GarlingSplitsOver K L f) ∧
      ∀ L' : Subfield L, Set.range (algebraMap K L) ⊆ (L' : Set L) →
        (∀ f ∈ S, ∃ (n : ℕ) (c : K) (α : Fin n → L),
          (∀ j, α j ∈ L') ∧ GarlingSplitsExplicit K L f n c α) →
        L' = ⊤ := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro hmin L' hK hsplit
    let M : IntermediateField K L :=
      { L' with algebraMap_mem' := fun k => hK ⟨k, rfl⟩ }
    have hMtop : M = ⊤ := hmin M fun f hf =>
      (garlingSplitsOver_intermediateField_iff M f).mpr (hsplit f hf)
    ext x
    have hx : x ∈ M := hMtop ▸ IntermediateField.mem_top
    simpa [M] using hx
  · intro hmin M hsplitM
    have hK : Set.range (algebraMap K L) ⊆ (M.toSubfield : Set L) := by
      rintro _ ⟨k, rfl⟩
      exact M.algebraMap_mem k
    have htop : M.toSubfield = ⊤ := hmin M.toSubfield hK fun f hf =>
      (garlingSplitsOver_intermediateField_iff M f).mp (hsplitM f hf)
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    have hx : x ∈ M.toSubfield := htop ▸ Subfield.mem_top x
    exact hx

/-- Exact agreement between `IsGarlingSplittingFieldExtensionSet K L {f}` and Chapter 7's
single-polynomial `IsGarlingSplittingFieldExtension K L f` across **all** `f ∈ K[X]` (including
`f = 0` and constants). -/
theorem isGarlingSplittingFieldExtensionSet_singleton_iff (K L : Type*) [Field K] [Field L]
    [Algebra K L] (f : K[X]) :
    IsGarlingSplittingFieldExtensionSet K L ({f} : Set K[X]) ↔
      IsGarlingSplittingFieldExtension K L f := by
  unfold IsGarlingSplittingFieldExtensionSet IsGarlingSplittingFieldExtension
  simp only [Set.mem_singleton_iff, forall_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h M hne hsp
    exact hne (h M hsp)
  · intro h M hsp
    by_contra hne
    exact h M hne hsp

/-- Because `0 ∈ K[X]` splits over every extension of `K` under Chapter 7's `GarlingSplitsOver`,
`L : K` is a splitting field extension for `S` if and only if it is a splitting field extension for
`S \ {0}`. -/
theorem isGarlingSplittingFieldExtensionSet_diff_zero_iff (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (S : Set K[X]) :
    IsGarlingSplittingFieldExtensionSet K L (S \ {(0 : K[X])}) ↔
      IsGarlingSplittingFieldExtensionSet K L S := by
  have hforall : ∀ (E : Type v) [Field E] [Algebra K E],
      (∀ f ∈ S \ {(0 : K[X])}, GarlingSplitsOver K E f) ↔
        (∀ f ∈ S, GarlingSplitsOver K E f) := by
    intro E _ _
    constructor
    · intro h f hf
      by_cases hf0 : f = 0
      · subst hf0
        exact ⟨0, 0, Fin.elim0, by simp [GarlingSplitsExplicit]⟩
      · exact h f ⟨hf, hf0⟩
    · exact fun h f hf => h f hf.1
  unfold IsGarlingSplittingFieldExtensionSet
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hforall L).mp h1, fun L' hL' => h2 L' ((hforall L').mpr hL')⟩,
    fun ⟨h1, h2⟩ => ⟨(hforall L).mpr h1, fun L' hL' => h2 L' ((hforall L').mp hL')⟩⟩

/-- At `S = ∅`, `L : K` is a splitting field extension for `∅` iff `L = K` (`⊥ = ⊤`). -/
theorem isGarlingSplittingFieldExtensionSet_empty_iff (K L : Type*) [Field K] [Field L]
    [Algebra K L] :
    IsGarlingSplittingFieldExtensionSet K L (∅ : Set K[X]) ↔
      (⊥ : IntermediateField K L) = ⊤ := by
  unfold IsGarlingSplittingFieldExtensionSet
  constructor
  · rintro ⟨_, h⟩
    exact h ⊥ (fun _ hf => hf.elim)
  · intro htop
    exact ⟨fun _ hf => hf.elim, fun L' _ => top_unique (htop ▸ bot_le)⟩

/-- Prose finite-`S` product remark (§9.1, printed p. 78 / PDF p. 86, indexed form):
for non-zero polynomials `f₁, …, f_n ∈ K[x]`, `L : K` is a splitting field extension for
`{f₁, …, f_n}` if and only if it is a splitting field extension for `g = f₁ ⋯ f_n`. -/
theorem isGarlingSplittingFieldExtensionSet_range_iff_prod {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] {n : ℕ} (f : Fin n → K[X]) (hf : ∀ i : Fin n, f i ≠ 0) :
    IsGarlingSplittingFieldExtensionSet K L (Set.range f) ↔
      IsGarlingSplittingFieldExtension K L (∏ i : Fin n, f i) := by
  rw [← isGarlingSplittingFieldExtensionSet_singleton_iff]
  have hequiv : ∀ (E : Type v) [Field E] [Algebra K E],
      (∀ p ∈ Set.range f, GarlingSplitsOver K E p) ↔
        (∀ p ∈ ({∏ i : Fin n, f i} : Set K[X]), GarlingSplitsOver K E p) := by
    intro E _ _
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_singleton_iff, forall_eq]
    have hprod := (garlingSplitsOver_finset_prod_iff (L := E) Finset.univ f (fun i _ => hf i)).2
    exact ⟨fun h => hprod.mpr fun i _ => h i, fun h i => hprod.mp h i (Finset.mem_univ i)⟩
  unfold IsGarlingSplittingFieldExtensionSet
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hequiv L).mp h1, fun L' hL' => h2 L' ((hequiv L').mpr hL')⟩,
    fun ⟨h1, h2⟩ => ⟨(hequiv L).mpr h1, fun L' hL' => h2 L' ((hequiv L').mp hL')⟩⟩

/-- Prose finite-`S` product remark (§9.1, printed p. 78 / PDF p. 86, `Finset` form):
if `S` is a finite subset of `K[x]` with `0 ∉ S`, then `L : K` is a splitting field extension for
`S` if and only if it is a splitting field extension for `∏ f ∈ S, f`. -/
theorem isGarlingSplittingFieldExtensionSet_finset_iff_prod {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (S : Finset K[X]) (h0 : (0 : K[X]) ∉ S) :
    IsGarlingSplittingFieldExtensionSet K L (S : Set K[X]) ↔
      IsGarlingSplittingFieldExtension K L (∏ f ∈ S, f) := by
  rw [← isGarlingSplittingFieldExtensionSet_singleton_iff]
  have hf0 : ∀ f ∈ S, f ≠ 0 := by
    intro f hf rfl
    exact h0 hf
  have hequiv : ∀ (E : Type v) [Field E] [Algebra K E],
      (∀ p ∈ (S : Set K[X]), GarlingSplitsOver K E p) ↔
        (∀ p ∈ ({∏ f ∈ S, f} : Set K[X]), GarlingSplitsOver K E p) := by
    intro E _ _
    simp only [Finset.mem_coe, Set.mem_singleton_iff, forall_eq]
    exact ((garlingSplitsOver_finset_prod_iff (L := E) S id hf0).2).symm
  unfold IsGarlingSplittingFieldExtensionSet
  exact ⟨fun ⟨h1, h2⟩ => ⟨(hequiv L).mp h1, fun L' hL' => h2 L' ((hequiv L').mpr hL')⟩,
    fun ⟨h1, h2⟩ => ⟨(hequiv L).mpr h1, fun L' hL' => h2 L' ((hequiv L').mp hL')⟩⟩

/-- Supporting note on the `0 ∉ S` guard in p. 78's unnumbered finite-`S` product remark:
under Chapter 7's `GarlingSplitsOver` (where `0` splits over every field), `S = {x² + 1, 0} ⊆ ℝ[x]`
has splitting field `ℂ : ℝ`, whereas `(x² + 1) · 0 = 0` has splitting field `ℝ : ℝ` (not `ℂ : ℝ`). -/
theorem finite_set_prod_zero_mem_counterexample :
    let S : Set ℝ[X] := {Polynomial.X ^ 2 + 1, 0}
    IsGarlingSplittingFieldExtensionSet ℝ ℂ S ∧
    ¬ IsGarlingSplittingFieldExtension ℝ ℂ ((Polynomial.X ^ 2 + 1) * 0) := by
  intro S
  have hC : IsGarlingSplittingFieldExtension ℝ ℂ (Polynomial.X ^ 2 + 1) :=
    conclusions_8_4_complex_over_real.2.1
  have hdiff : S \ {(0 : ℝ[X])} = {Polynomial.X ^ 2 + 1} := by
    ext p
    simp only [S, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, hp0⟩
      · rfl
      · exact False.elim (hp0 rfl)
    · rintro rfl
      exact ⟨Or.inl rfl, by intro h; have := congrArg (fun q : ℝ[X] => q.eval 0) h; norm_num at this⟩
  have hS : IsGarlingSplittingFieldExtensionSet ℝ ℂ S := by
    rw [← isGarlingSplittingFieldExtensionSet_diff_zero_iff, hdiff,
      isGarlingSplittingFieldExtensionSet_singleton_iff]
    exact hC
  refine ⟨hS, ?_⟩
  rw [mul_zero, isGarlingSplittingFieldExtension_zero_iff]
  intro hbot_top
  have hI : Complex.I ∈ (⊥ : IntermediateField ℝ ℂ) := hbot_top ▸ IntermediateField.mem_top
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hI
  have him := congrArg Complex.im hr
  simp at him

/-- Helper: every element of `IntermediateField.adjoin K A` lies in `IntermediateField.adjoin K s`
for some finite subset `s : Finset L` with `(s : Set L) ⊆ A`. -/
private lemma exists_finset_subset_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : Set L) {x : L} (hx : x ∈ IntermediateField.adjoin K A) :
    ∃ (n : ℕ) (α : Fin n → L),
      (∀ i, α i ∈ A) ∧ x ∈ IntermediateField.adjoin K (Set.range α) := by
  classical
  let F : IntermediateField K L :=
    { carrier := {y : L | ∃ s : Finset L, (s : Set L) ⊆ A ∧ y ∈ IntermediateField.adjoin K (s : Set L)}
      add_mem' := by
        rintro a b ⟨s₁, hs₁, ha⟩ ⟨s₂, hs₂, hb⟩
        refine ⟨s₁ ∪ s₂, ?_, ?_⟩
        · rw [Finset.coe_union]; exact Set.union_subset hs₁ hs₂
        · have h1 : IntermediateField.adjoin K (s₁ : Set L) ≤
              IntermediateField.adjoin K ((s₁ ∪ s₂ : Finset L) : Set L) :=
            IntermediateField.adjoin_le_iff.mpr fun z hz =>
              IntermediateField.subset_adjoin K _ (by rw [Finset.coe_union]; exact Or.inl hz)
          have h2 : IntermediateField.adjoin K (s₂ : Set L) ≤
              IntermediateField.adjoin K ((s₁ ∪ s₂ : Finset L) : Set L) :=
            IntermediateField.adjoin_le_iff.mpr fun z hz =>
              IntermediateField.subset_adjoin K _ (by rw [Finset.coe_union]; exact Or.inr hz)
          exact add_mem (h1 ha) (h2 hb)
      mul_mem' := by
        rintro a b ⟨s₁, hs₁, ha⟩ ⟨s₂, hs₂, hb⟩
        refine ⟨s₁ ∪ s₂, ?_, ?_⟩
        · rw [Finset.coe_union]; exact Set.union_subset hs₁ hs₂
        · have h1 : IntermediateField.adjoin K (s₁ : Set L) ≤
              IntermediateField.adjoin K ((s₁ ∪ s₂ : Finset L) : Set L) :=
            IntermediateField.adjoin_le_iff.mpr fun z hz =>
              IntermediateField.subset_adjoin K _ (by rw [Finset.coe_union]; exact Or.inl hz)
          have h2 : IntermediateField.adjoin K (s₂ : Set L) ≤
              IntermediateField.adjoin K ((s₁ ∪ s₂ : Finset L) : Set L) :=
            IntermediateField.adjoin_le_iff.mpr fun z hz =>
              IntermediateField.subset_adjoin K _ (by rw [Finset.coe_union]; exact Or.inr hz)
          exact mul_mem (h1 ha) (h2 hb)
      algebraMap_mem' := fun k =>
        ⟨∅, by simp, (IntermediateField.adjoin K ((∅ : Finset L) : Set L)).algebraMap_mem k⟩
      inv_mem' := by
        rintro a ⟨s, hs, ha⟩
        exact ⟨s, hs, inv_mem ha⟩ }
  have hle : IntermediateField.adjoin K A ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    intro a ha
    refine ⟨{a}, by simpa using ha, ?_⟩
    simpa using IntermediateField.mem_adjoin_simple_self K a
  obtain ⟨s, hsA, hxs⟩ := hle hx
  let e : Fin s.card ≃ s := s.equivFin.symm
  let α : Fin s.card → L := fun i => (e i).1
  have hrange : Set.range α = (s : Set L) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hz; exact ⟨e.symm ⟨z, hz⟩, by simp [α]⟩
  exact ⟨s.card, α, fun i => hsA (e i).2, hrange.symm ▸ hxs⟩

/-- **Theorem 9.1** (§9.1, printed p. 78 / PDF p. 86; proof pp. 78–79 / PDF pp. 86–87):
*"An extension `L : K` is normal if and only if it is a splitting field extension for some
`S ⊆ K[x]`."*

Proved step-by-step following Garling's printed proof on pp. 78–79:
- `(⇒)`: takes `S = {minpoly K α | α ∈ L}`;
- `(⇐)`: passes to `S₀ = S \ {0}`, sets `A = ⋃_{f ∈ S₀} rootSet_L(f)`, deduces `L = K(A)` and
  `IsAlgebraicExtension K L` via `Corollary 2` to `Theorem 4.6`, reduces to a finite product
  `g = f₁ ⋯ f_n`, constructs `H : K(R)` via `Theorem 7.3`, and runs the 6-arrow subfield diamond
  via `Corollary 1` to `Theorem 7.4`, `Corollary 1` to `Theorem 7.5`, and `Theorem 4.2`. -/
theorem theorem_9_1 (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    IsGarlingNormal K L ↔
      ∃ S : Set K[X], IsGarlingSplittingFieldExtensionSet K L S := by
  constructor
  · intro hnorm
    obtain ⟨halg, hmin⟩ := (isGarlingNormal_iff_minpoly_splits K L).mp hnorm
    refine ⟨Set.range (fun α : L => minpoly K α), ?_, ?_⟩
    · rintro _ ⟨α, rfl⟩
      exact hmin α
    · intro L' hL'
      ext α
      simp only [IntermediateField.mem_top, iff_true]
      have hint : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
      exact mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hint)
        (hL' (minpoly K α) ⟨α, rfl⟩) (minpoly.aeval K α)
  · rintro ⟨S, hsfS⟩
    classical
    let S₀ : Set K[X] := S \ {(0 : K[X])}
    have hsfS₀ : IsGarlingSplittingFieldExtensionSet K L S₀ :=
      (isGarlingSplittingFieldExtensionSet_diff_zero_iff K L S).mpr hsfS
    -- Let `A` denote the set of roots in `L` of polynomials in `S₀`.
    let A : Set L := {α : L | ∃ f ∈ S₀, Polynomial.aeval α f = 0}
    have hKA_splits : ∀ f ∈ S₀, GarlingSplitsOver K (IntermediateField.adjoin K A) f := by
      intro f hf
      obtain ⟨n, c, α, hexp⟩ := hsfS₀.1 f hf
      have hroots : Set.range α = f.rootSet L :=
        (garlingSplitsExplicit_props hf.2 hexp).2.2.2
      refine (garlingSplitsOver_intermediateField_iff (IntermediateField.adjoin K A) f).mpr
        ⟨n, c, α, fun j => ?_, hexp⟩
      apply IntermediateField.subset_adjoin K A
      have hmem : α j ∈ f.rootSet L := hroots ▸ ⟨j, rfl⟩
      exact ⟨f, hf, (Polynomial.mem_rootSet.mp hmem).2⟩
    -- Clearly `L = K(A)`, and so `L : K` is algebraic by Corollary 2 to Theorem 4.6.
    have hL_eq_KA : IntermediateField.adjoin K A = ⊤ := hsfS₀.2 _ hKA_splits
    have hA_alg : ∀ α ∈ A, IsGarlingAlgebraic K α := by
      rintro α ⟨f, ⟨_, hf0⟩, hα⟩
      exact ⟨f, hf0, hα⟩
    have halg_KA : IsAlgebraicExtension K (IntermediateField.adjoin K A) :=
      corollary_2_to_theorem_4_6 hA_alg
    have halg : IsAlgebraicExtension K L := by
      intro x
      let xKA : IntermediateField.adjoin K A := ⟨x, hL_eq_KA ▸ IntermediateField.mem_top⟩
      obtain ⟨p, hp0, hpx⟩ := halg_KA xKA
      refine ⟨p, hp0, ?_⟩
      have hval := congrArg (IntermediateField.adjoin K A).val hpx
      rw [← Polynomial.aeval_algHom_apply, map_zero] at hval
      exact hval
    -- Show `minpoly K β` splits over `L` for every `β ∈ L` via Garling's diamond on p. 79.
    rw [isGarlingNormal_iff_minpoly_splits]
    refine ⟨halg, fun β => ?_⟩
    have hβA : β ∈ IntermediateField.adjoin K A := hL_eq_KA ▸ IntermediateField.mem_top
    obtain ⟨n, α, hαA, hβ_adj⟩ := exists_finset_subset_adjoin A hβA
    choose f hfS₀ hα_root using fun i : Fin n => hαA i
    let g : K[X] := ∏ i : Fin n, f i
    have hg_props := garlingSplitsOver_finset_prod_iff (L := L) Finset.univ f
      (fun i _ => (hfS₀ i).2)
    have hg0 : g ≠ 0 := hg_props.1
    have hg_splitsL : GarlingSplitsOver K L g :=
      hg_props.2.mpr fun i _ => hsfS₀.1 (f i) (hfS₀ i)
    obtain ⟨d, cg, rg, hexp_g⟩ := hg_splitsL
    have hrg_roots : Set.range rg = g.rootSet L :=
      (garlingSplitsExplicit_props hg0 hexp_g).2.2.2
    let KR : IntermediateField K L := IntermediateField.adjoin K (Set.range rg)
    have hβ_KR : β ∈ KR := by
      have hsub : Set.range α ⊆ (KR : Set L) := by
        rintro _ ⟨i, rfl⟩
        apply IntermediateField.subset_adjoin K (Set.range rg)
        rw [hrg_roots, Polynomial.mem_rootSet]
        refine ⟨hg0, ?_⟩
        dsimp [g]
        rw [map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hα_root i)
      exact (IntermediateField.adjoin_le_iff.mpr hsub) hβ_adj
    -- Construct splitting field extension `H : K(R)` for `m = minpoly K β`.
    have hβ_int : IsIntegral K β := (isGarlingAlgebraic_iff_isIntegral K β).mp (halg β)
    let m : K[X] := minpoly K β
    have hm_monic : m.Monic := minpoly.monic hβ_int
    have hm_irr : Irreducible m := minpoly.irreducible hβ_int
    let mKR : KR[X] := m.map (algebraMap K KR)
    obtain ⟨H, instFieldH, instAlgKRH, hsfH, _⟩ := theorem_7_3_natDegree mKR
    let _ : Field H := instFieldH
    let _ : Algebra KR H := instAlgKRH
    let _ : Algebra K H := ((algebraMap KR H).comp (algebraMap K KR)).toAlgebra
    have _ : IsScalarTower K KR H := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let iKRH : KR →ₐ[K] H := IsScalarTower.toAlgHom K KR H
    let KRH : IntermediateField K H := iKRH.fieldRange
    let rH : Fin d → H := fun j =>
      iKRH ⟨rg j, IntermediateField.subset_adjoin K (Set.range rg) ⟨j, rfl⟩⟩
    have hKRH_eq : KRH = IntermediateField.adjoin K (Set.range rH) := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        let P : IntermediateField K KR := (IntermediateField.adjoin K (Set.range rH)).comap iKRH
        let PL : IntermediateField K L := P.map KR.val
        have hrg_PL : Set.range rg ⊆ (PL : Set L) := by
          rintro _ ⟨j, rfl⟩
          refine ⟨⟨rg j, IntermediateField.subset_adjoin K (Set.range rg) ⟨j, rfl⟩⟩, ?_, rfl⟩
          change rH j ∈ IntermediateField.adjoin K (Set.range rH)
          exact IntermediateField.subset_adjoin K (Set.range rH) ⟨j, rfl⟩
        have hKR_le_PL : KR ≤ PL := IntermediateField.adjoin_le_iff.mpr hrg_PL
        obtain ⟨y, hyP, hyval⟩ := hKR_le_PL x.2
        have hyx : y = x := Subtype.ext hyval
        exact hyx ▸ hyP
      · rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact ⟨⟨rg j, IntermediateField.subset_adjoin K (Set.range rg) ⟨j, rfl⟩⟩, rfl⟩
    have hexp_g_H : GarlingSplitsExplicit K H g d cg rH := by
      unfold GarlingSplitsExplicit at hexp_g ⊢
      have hrg_KR : ∀ j : Fin d, rg j ∈ KR := fun j =>
        IntermediateField.subset_adjoin K (Set.range rg) ⟨j, rfl⟩
      have hexp_KR :
          g.map (algebraMap K KR) =
            Polynomial.C (algebraMap K KR cg) *
              ∏ j : Fin d, (Polynomial.X - Polynomial.C (⟨rg j, hrg_KR j⟩ : KR)) := by
        apply Polynomial.map_injective KR.val.toRingHom KR.val.injective
        have hmap : (g.map (algebraMap K KR)).map KR.val.toRingHom = g.map (algebraMap K L) := by
          rw [Polynomial.map_map]; rfl
        rw [hmap, hexp_g]
        simp [Polynomial.map_mul, Polynomial.map_prod]
      have hmapH : (g.map (algebraMap K KR)).map (algebraMap KR H) = g.map (algebraMap K H) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      rw [← hmapH, hexp_KR, Polynomial.map_mul, Polynomial.map_C,
        ← IsScalarTower.algebraMap_apply K KR H]
      simp [Polynomial.map_prod, rH, iKRH]
    -- Show every root `γ ∈ H` of `m` belongs to `KRH` via the 6-arrow diamond.
    have hγ_in_KRH : ∀ γ : H, Polynomial.aeval γ m = 0 → γ ∈ KRH := by
      intro γ hγ_root
      let βKR : KR := ⟨β, hβ_KR⟩
      let βH : H := iKRH βKR
      have hβH_mem : βH ∈ KRH := ⟨βKR, rfl⟩
      have hβKR_root : Polynomial.aeval βKR m = 0 := by
        apply KR.val.injective
        exact (Polynomial.aeval_algHom_apply KR.val βKR m).symm.trans
          ((minpoly.aeval K β).trans (map_zero KR.val).symm)
      have hβH_root : Polynomial.aeval βH m = 0 :=
        (Polynomial.aeval_algHom_apply iKRH βKR m).trans
          ((congrArg iKRH hβKR_root).trans (map_zero iKRH))
      have hγ_alg : IsGarlingAlgebraic K γ := ⟨m, hm_irr.ne_zero, hγ_root⟩
      have hm_βH : minpoly K βH = m :=
        (minpoly.eq_of_irreducible_of_monic hm_irr hβH_root hm_monic).symm
      have hm_γ : minpoly K γ = m :=
        (minpoly.eq_of_irreducible_of_monic hm_irr hγ_root hm_monic).symm
      let Kβ : IntermediateField K H := IntermediateField.adjoin K ({βH} : Set H)
      let Kγ : IntermediateField K H := IntermediateField.adjoin K ({γ} : Set H)
      let genβ : Kβ := IntermediateField.AdjoinSimple.gen K βH
      let genγ : Kγ := IntermediateField.AdjoinSimple.gen K γ
      have hadj_β : IntermediateField.adjoin K ({genβ} : Set Kβ) = ⊤ := by
        ext x
        simp only [IntermediateField.mem_top, iff_true]
        let L0 : IntermediateField K H := (IntermediateField.adjoin K ({genβ} : Set Kβ)).map Kβ.val
        have hmem : βH ∈ L0 := ⟨genβ, IntermediateField.mem_adjoin_simple_self K genβ, rfl⟩
        obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
        exact (Kβ.val.injective hyx) ▸ hy
      have hadj_γ : IntermediateField.adjoin K ({genγ} : Set Kγ) = ⊤ := by
        ext x
        simp only [IntermediateField.mem_top, iff_true]
        let L0 : IntermediateField K H := (IntermediateField.adjoin K ({genγ} : Set Kγ)).map Kγ.val
        have hmem : γ ∈ L0 := ⟨genγ, IntermediateField.mem_adjoin_simple_self K genγ, rfl⟩
        obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
        exact (Kγ.val.injective hyx) ▸ hy
      have hgenβ_alg : IsGarlingAlgebraic K genβ :=
        ⟨m, hm_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kβ.val genβ m).symm.trans hβH_root)⟩
      have hgenγ_alg : IsGarlingAlgebraic K genγ :=
        ⟨m, hm_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kγ.val genγ m).symm.trans hγ_root)⟩
      have hmin_genβ : minpoly K genβ = m :=
        (minpoly.algHom_eq Kβ.val Kβ.val.injective genβ).symm.trans hm_βH
      have hmin_genγ : minpoly K genγ = m :=
        (minpoly.algHom_eq Kγ.val Kγ.val.injective genγ).symm.trans hm_γ
      -- By Corollary 1 to Theorem 7.4, `τ : K(β) ≃+* K(γ)` sending `β ↦ γ` and fixing `K`.
      have hm_eq_map :
          garlingMapPoly (RingEquiv.refl K).toRingHom (minpoly K genβ) = minpoly K genγ := by
        simp [hmin_genβ, hmin_genγ]
      obtain ⟨τ, ⟨_hτ_gen, hτ_fix⟩, _⟩ :=
        (corollary_1_to_theorem_7_4_equiv hadj_β hgenβ_alg hadj_γ hgenγ_alg (RingEquiv.refl K)).2
          hm_eq_map
      -- `K(R) : K(β)` and `K(R, γ) : K(γ)` are splitting field extensions for `g` and `τ(g) = g`.
      let Eβ : IntermediateField Kβ H := IntermediateField.adjoin Kβ (Set.range rH)
      let Eγ : IntermediateField Kγ H := IntermediateField.adjoin Kγ (Set.range rH)
      let gβ : Kβ[X] := g.map (algebraMap K Kβ)
      let gγ : Kγ[X] := g.map (algebraMap K Kγ)
      have hgβ0 : gβ ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K Kβ).injective).mpr hg0
      have hexp_gβ : GarlingSplitsExplicit Kβ H gβ d (algebraMap K Kβ cg) rH := by
        unfold GarlingSplitsExplicit
        have hmap : gβ.map (algebraMap Kβ H) = g.map (algebraMap K H) := by
          dsimp [gβ]; rw [Polynomial.map_map]; rfl
        rw [hmap, hexp_g_H]
        rfl
      have hexp_gγ : GarlingSplitsExplicit Kγ H gγ d (algebraMap K Kγ cg) rH := by
        unfold GarlingSplitsExplicit
        have hmap : gγ.map (algebraMap Kγ H) = g.map (algebraMap K H) := by
          dsimp [gγ]; rw [Polynomial.map_map]; rfl
        rw [hmap, hexp_g_H]
        rfl
      have hsf_Eβ : IsGarlingSplittingFieldExtension Kβ Eβ gβ := theorem_7_1 hgβ0 hexp_gβ
      have hτ_gβ : garlingMapPoly τ.toRingHom gβ = gγ := by
        have hcomp : τ.toRingHom.comp (algebraMap K Kβ) = algebraMap K Kγ :=
          RingHom.ext fun k => by simpa using hτ_fix k
        change (g.map (algebraMap K Kβ)).map τ.toRingHom = g.map (algebraMap K Kγ)
        rw [Polynomial.map_map, hcomp]
      have hsf_Eγ : IsGarlingSplittingFieldExtension Kγ Eγ (garlingMapPoly τ.toRingHom gβ) := by
        rw [hτ_gβ]
        have hgγ0 : gγ ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K Kγ).injective).mpr hg0
        exact theorem_7_1 hgγ0 hexp_gγ
      -- By Corollary 1 to Theorem 7.5, `τ` extends to an isomorphism `σ : Eβ →+* Eγ`.
      have hτ_iso : IsRingIsomorphism τ.toRingHom := τ.bijective
      obtain ⟨σ, hσ_iso, hσ_ext⟩ :=
        corollary_1_to_theorem_7_5 hτ_iso gβ hsf_Eβ hsf_Eγ
      -- Identify `Eβ.restrictScalars K = KRH` and `KRH ≤ Eγ.restrictScalars K` (with `γ ∈ Eγ`).
      let KRγ : IntermediateField K H := Eγ.restrictScalars K
      have hEβ_eq : Eβ.restrictScalars K = KRH := by
        apply le_antisymm
        · intro x hx
          have hsub_β : Kβ ≤ KRH :=
            IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβH_mem)
          let KRH_β : IntermediateField Kβ H :=
            { KRH.toSubfield with algebraMap_mem' := fun b => hsub_β b.2 }
          have hr_mem : Set.range rH ⊆ (KRH_β : Set H) := by
            change Set.range rH ⊆ (KRH : Set H)
            rw [hKRH_eq]
            exact IntermediateField.subset_adjoin K (Set.range rH)
          have hle : Eβ ≤ KRH_β := IntermediateField.adjoin_le_iff.mpr hr_mem
          exact hle hx
        · rw [hKRH_eq, IntermediateField.adjoin_le_iff]
          rintro _ ⟨j, rfl⟩
          exact IntermediateField.subset_adjoin Kβ (Set.range rH) ⟨j, rfl⟩
      have hKRH_le_KRγ : KRH ≤ KRγ := by
        rw [hKRH_eq, IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin Kγ (Set.range rH) ⟨j, rfl⟩
      -- `σ` fixes `K`, giving a `K`-algebra isomorphism `Eβ.restrictScalars K ≃ₐ[K] KRγ`.
      let σEquiv : Eβ.restrictScalars K ≃+* KRγ := RingEquiv.ofBijective σ hσ_iso
      have hσ_fixK : ∀ k : K,
          σEquiv (algebraMap K (Eβ.restrictScalars K) k) = algebraMap K KRγ k := by
        intro k
        change σ (algebraMap Kβ Eβ (algebraMap K Kβ k)) =
          algebraMap Kγ Eγ (algebraMap K Kγ k)
        rw [hσ_ext (algebraMap K Kβ k)]
        congr 1
        simpa using hτ_fix k
      let σAlg : (Eβ.restrictScalars K) ≃ₐ[K] KRγ := AlgEquiv.ofRingEquiv (f := σEquiv) hσ_fixK
      -- By Theorem 4.2 (tower law / finite dimensions), `[KRH : K] = [KRγ : K]`, so `KRH = KRγ`.
      have _ : FiniteDimensional K Kγ :=
        IntermediateField.finiteDimensional_adjoin fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          exact (isGarlingAlgebraic_iff_isIntegral K γ).mp hγ_alg
      have _ : FiniteDimensional Kγ Eγ :=
        (isFiniteExtension_iff_moduleFinite Kγ Eγ).mp
          (corollary_to_theorem_7_1 (hτ_gβ ▸ hsf_Eγ)).1
      have _ : FiniteDimensional K KRγ := by
        change FiniteDimensional K Eγ
        exact Module.Finite.trans Kγ Eγ
      have _ : FiniteDimensional K KRH := hEβ_eq ▸ σAlg.symm.toLinearEquiv.finiteDimensional
      have hfinrank_eq : Module.finrank K KRH = Module.finrank K KRγ := by
        rw [← hEβ_eq]
        exact σAlg.toLinearEquiv.finrank_eq
      have hSub_eq : KRH.toSubmodule = KRγ.toSubmodule :=
        Submodule.eq_of_le_of_finrank_eq
          (show KRH.toSubmodule ≤ KRγ.toSubmodule from hKRH_le_KRγ) hfinrank_eq
      have hKRH_eq_KRγ : KRH = KRγ := by
        ext z
        exact SetLike.ext_iff.mp hSub_eq z
      have hγ_KRγ : γ ∈ KRγ :=
        Eγ.algebraMap_mem ⟨γ, IntermediateField.mem_adjoin_simple_self K γ⟩
      exact hKRH_eq_KRγ.symm ▸ hγ_KRγ
    -- All roots of `m` in `H` lie in `KRH`, so `m` splits over `KR` and hence over `L`.
    obtain ⟨nm, cm, γm, hexp_mH⟩ := hsfH.1
    have hmKR_ne0 : mKR ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap K KR).injective).mpr hm_irr.ne_zero
    have hmKR_roots : Set.range γm = mKR.rootSet H :=
      (garlingSplitsExplicit_props hmKR_ne0 hexp_mH).2.2.2
    have hγm_in_KRH : ∀ j : Fin nm, γm j ∈ KRH := by
      intro j
      apply hγ_in_KRH
      have hmem : γm j ∈ mKR.rootSet H := hmKR_roots ▸ ⟨j, rfl⟩
      have haev : Polynomial.aeval (γm j) mKR = 0 := (Polynomial.mem_rootSet.mp hmem).2
      dsimp [mKR] at haev
      rwa [Polynomial.aeval_map_algebraMap] at haev
    choose δKR hδKR using fun j : Fin nm => hγm_in_KRH j
    obtain ⟨hcm_eq, _, _, _⟩ := garlingSplitsExplicit_props hmKR_ne0 hexp_mH
    have hcm_one : cm = 1 := by
      rw [hcm_eq]
      dsimp [mKR]
      rw [Polynomial.leadingCoeff_map_of_injective (algebraMap K KR).injective,
        hm_monic.leadingCoeff, map_one]
    have hexp_mKR :
        m.map (algebraMap K KR) =
          ∏ j : Fin nm, (Polynomial.X - Polynomial.C (δKR j)) := by
      apply Polynomial.map_injective (algebraMap KR H) (algebraMap KR H).injective
      have h1 := hexp_mH
      unfold GarlingSplitsExplicit at h1
      rw [hcm_one, map_one, map_one, one_mul] at h1
      change (mKR.map (algebraMap KR H)) = _
      rw [h1]
      simp [Polynomial.map_prod, show ∀ j, algebraMap KR H (δKR j) = γm j from hδKR]
    refine ⟨nm, 1, fun j => (δKR j : L), ?_⟩
    unfold GarlingSplitsExplicit
    have hmapL : (m.map (algebraMap K KR)).map KR.val.toRingHom = m.map (algebraMap K L) := by
      rw [Polynomial.map_map]; rfl
    rw [← hmapL, hexp_mKR]
    simp [Polynomial.map_prod]

/-- **Corollary 1** [to Theorem 9.1] (§9.1, printed p. 79 / PDF p. 87):
*"A finite extension `L : K` is normal if and only if `L : K` is a splitting field extension for
some `g ∈ K[x]`."*

Proved following Garling's 2-line argument via a `K`-basis `α₁, …, α_n` of `L` and
`g = m_{α₁} m_{α₂} ⋯ m_{α_n}`. -/
theorem corollary_1_to_theorem_9_1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    IsGarlingNormal K L ↔
      ∃ g : K[X], IsGarlingSplittingFieldExtension K L g := by
  constructor
  · intro hnorm
    classical
    have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
    obtain ⟨halg, hmin⟩ := (isGarlingNormal_iff_minpoly_splits K L).mp hnorm
    let b := Module.Basis.ofVectorSpace K L
    let g : K[X] := ∏ i, minpoly K (b i)
    have hb_int : ∀ i, IsIntegral K (b i) :=
      fun i => (isGarlingAlgebraic_iff_isIntegral K (b i)).mp (halg (b i))
    have hg_props := garlingSplitsOver_finset_prod_iff (L := L) Finset.univ
      (fun i => minpoly K (b i)) (fun i _ => minpoly.ne_zero (hb_int i))
    have hg0 : g ≠ 0 := hg_props.1
    have hg_splits : GarlingSplitsOver K L g := hg_props.2.mpr fun i _ => hmin (b i)
    refine ⟨g, hg_splits, fun M hMne hsplitM => hMne ?_⟩
    have hb_mem : ∀ i, b i ∈ M := by
      intro i
      refine mem_of_garlingSplitsOver_intermediateField hg0 hsplitM ?_
      dsimp [g]
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (b i))
    have hspan_le : (⊤ : Submodule K L) ≤ M.toSubmodule := by
      rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb_mem i
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    exact hspan_le Submodule.mem_top
  · rintro ⟨g, hsf⟩
    exact (theorem_9_1 K L).mpr
      ⟨{g}, (isGarlingSplittingFieldExtensionSet_singleton_iff K L g).mpr hsf⟩

/-- Two-sided finite+normal characterization companion to **Corollary 1** [to Theorem 9.1]
(§9.1, p. 79): because every splitting field extension for a single `g ∈ K[x]` (including `g = 0`)
is automatically finite over `K` (`Corollary` to `Theorem 7.1`), `L : K` is finite and normal iff
`L : K` is a splitting field extension for some `g ∈ K[x]`. -/
theorem corollary_1_to_theorem_9_1_iff (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (IsFiniteExtension K L ∧ IsGarlingNormal K L) ↔
      ∃ g : K[X], IsGarlingSplittingFieldExtension K L g := by
  constructor
  · rintro ⟨hfin, hnorm⟩
    exact (corollary_1_to_theorem_9_1 hfin).mp hnorm
  · rintro ⟨g, hsf⟩
    have hfin : IsFiniteExtension K L := (corollary_to_theorem_7_1 hsf).1
    exact ⟨hfin, (corollary_1_to_theorem_9_1 hfin).mpr ⟨g, hsf⟩⟩

/-- Prose generator-product normality criterion (§9.1, top of printed p. 80 / PDF p. 88):
*"Let `L = K(α₁, …, α_n)`, let `m_i` be the minimal polynomial of `α_i` over `K`, and let
`g = m₁ ⋯ m_n`. Then `L : K` is normal if and only if `L : K` is a splitting field extension
for `g`."*

Holds unconditionally across all `α : Fin n → L` (both when each `α_i` is algebraic over `K`, where
`m_i = minpoly K (α i)` is the §4.3 minimal polynomial, and when some `α_i` is transcendental, where
both sides are false). -/
theorem normal_iff_splittingField_prod_minpoly_of_adjoin {K L : Type*} [Field K] [Field L]
    [Algebra K L] {n : ℕ} (α : Fin n → L)
    (hadj : IntermediateField.adjoin K (Set.range α) = ⊤) :
    IsGarlingNormal K L ↔
      IsGarlingSplittingFieldExtension K L (∏ i : Fin n, minpoly K (α i)) := by
  classical
  constructor
  · intro hnorm
    obtain ⟨halg, hmin⟩ := (isGarlingNormal_iff_minpoly_splits K L).mp hnorm
    have hα_int : ∀ i : Fin n, IsIntegral K (α i) :=
      fun i => (isGarlingAlgebraic_iff_isIntegral K (α i)).mp (halg (α i))
    have hg_props := garlingSplitsOver_finset_prod_iff (L := L) Finset.univ
      (fun i => minpoly K (α i)) (fun i _ => minpoly.ne_zero (hα_int i))
    refine ⟨hg_props.2.mpr fun i _ => hmin (α i), fun M hMne hsplitM => hMne ?_⟩
    have hsub : Set.range α ⊆ (M : Set L) := by
      rintro _ ⟨i, rfl⟩
      refine mem_of_garlingSplitsOver_intermediateField hg_props.1 hsplitM ?_
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (α i))
    exact top_unique (hadj ▸ IntermediateField.adjoin_le_iff.mpr hsub)
  · intro hsf
    exact (theorem_9_1 K L).mpr
      ⟨{∏ i : Fin n, minpoly K (α i)},
        (isGarlingSplittingFieldExtensionSet_singleton_iff K L _).mpr hsf⟩

/-! ### Normal closures, Corollaries 2 & 3, and Exercises 9.1–9.3 (printed p. 80 / PDF p. 88) -/

/-- Helper: in any tower `K → L → F`, if `F : K` is algebraic, then `L : K` and `F : L` are both
algebraic. -/
theorem tower_algebraic_of_top_algebraic {K L F : Type*} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (halg : IsAlgebraicExtension K F) :
    IsAlgebraicExtension K L ∧ IsAlgebraicExtension L F := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · obtain ⟨p, hp0, hpx⟩ := halg (algebraMap L F x)
    refine ⟨p, hp0, ?_⟩
    apply (algebraMap L F).injective
    rw [map_zero]
    have h1 : algebraMap L F (Polynomial.aeval x p) = Polynomial.aeval (algebraMap L F x) p := by
      simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K L F) x p).symm
    exact h1.trans hpx
  · obtain ⟨p, hp0, hpy⟩ := halg y
    refine ⟨p.map (algebraMap K L),
      (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0, ?_⟩
    rwa [Polynomial.aeval_map_algebraMap]

/-- Garling's prose definition of a *normal closure* `F : L` for an algebraic extension `L : K`
(§9.1, printed p. 80 / PDF p. 88):
*"Suppose that `L : K` is algebraic. An extension `F : L` is a normal closure for `L : K` if `F : K`
is normal, and if `F : M : L` is a tower and `M : K` is normal, then `M = F`."* -/
def IsGarlingNormalClosure (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F] : Prop :=
  IsAlgebraicExtension K L ∧
  IsGarlingNormal K F ∧
  ∀ M : IntermediateField L F, IsGarlingNormal K M → M = ⊤

/-- Extension-triple formulation of a *normal closure* `(i_LF, L, F)` for `(i_KL, K, L)`
(§4.2, p. 40; §9.1, p. 80; `Exercise 9.4`, p. 81). -/
def IsGarlingNormalClosureTriple {K L F : Type*} [Field K] [Field L] [Field F]
    (eKL : FieldExtensionTriple K L) (eLF : FieldExtensionTriple L F) : Prop :=
  letI : Algebra K L := eKL.hom.toAlgebra
  letI : Algebra L F := eLF.hom.toAlgebra
  letI : Algebra K F := (eLF.hom.comp eKL.hom).toAlgebra
  haveI : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  IsGarlingNormalClosure K L F

/-- Because `F : K` normal implies `F : K` algebraic, which in a tower `K → L → F` automatically
forces `L : K` algebraic, `IsAlgebraicExtension K L` in `IsGarlingNormalClosure` is automatically
redundant (covering `Exercise 9.4`, p. 81, where `L : K` algebraic is not restated). -/
theorem isGarlingNormalClosure_iff_of_tower (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F] :
    IsGarlingNormalClosure K L F ↔
      IsGarlingNormal K F ∧ ∀ M : IntermediateField L F, IsGarlingNormal K M → M = ⊤ :=
  ⟨fun ⟨_, hF, hmin⟩ => ⟨hF, hmin⟩,
   fun ⟨hF, hmin⟩ => ⟨(tower_algebraic_of_top_algebraic hF.1).1, hF, hmin⟩⟩

/-- Universe-polymorphic abstract-tower consequence of `IsGarlingNormalClosure K L F`: for *any*
field `M` (in *any* universe `w`) forming a tower `K → L → M → F` with `M : K` normal,
`algebraMap M F` is surjective (`(⊥ : IntermediateField M F) = ⊤`). -/
theorem isGarlingNormalClosure_surjective_of_tower {K : Type u} {L : Type v} {F : Type*}
    {M : Type w} [Field K] [Field L] [Field F] [Field M]
    [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    [Algebra K M] [Algebra L M] [Algebra M F]
    [IsScalarTower K L M] [IsScalarTower L M F] [IsScalarTower K M F]
    (hcl : IsGarlingNormalClosure K L F) (hM : IsGarlingNormal K M) :
    Function.Surjective (algebraMap M F) ∧ (⊥ : IntermediateField M F) = ⊤ := by
  let iMF : M →ₐ[L] F := IsScalarTower.toAlgHom L M F
  let imM : IntermediateField L F := iMF.fieldRange
  let eK : M ≃ₐ[K] imM :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M F)
  have himM_norm : IsGarlingNormal K imM := (isGarlingNormal_congr eK).mp hM
  have himM_top : imM = ⊤ := hcl.2.2 imM himM_norm
  have hsurj : Function.Surjective (algebraMap M F) := by
    intro y
    have hy : y ∈ imM := himM_top ▸ IntermediateField.mem_top
    exact hy
  exact ⟨hsurj, (bot_eq_top_iff_surjective_algebraMap M F).mpr hsurj⟩

/-- Exact equivalence between Garling's `IsGarlingNormalClosure K L F` (§9.1, p. 80) and Mathlib's
`IsNormalClosure K L F` in any scalar tower `K → L → F`. -/
theorem isGarlingNormalClosure_iff_isNormalClosure (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F] :
    IsGarlingNormalClosure K L F ↔ IsNormalClosure K L F := by
  constructor
  · rintro ⟨halg, hnormF, hmin⟩
    have hnormF_ml : Normal K F := (isGarlingNormal_iff K F).mp hnormF
    have _ : Normal K F := hnormF_ml
    have _ : Algebra.IsAlgebraic K L := (isAlgebraicExtension_iff K L).mp halg
    refine ⟨fun x => ?_, ?_⟩
    · have hmin_eq : minpoly K (algebraMap L F x) = minpoly K x :=
        minpoly.algHom_eq (IsScalarTower.toAlgHom K L F) (algebraMap L F).injective x
      rw [← hmin_eq]
      exact hnormF_ml.splits (algebraMap L F x)
    · let NC : IntermediateField L F :=
        { (IntermediateField.normalClosure K L F).toSubfield with
          algebraMap_mem' := fun l =>
            (IsScalarTower.toAlgHom K L F).fieldRange_le_normalClosure ⟨l, rfl⟩ }
      have hNC_normK : Normal K NC := by
        change Normal K (IntermediateField.normalClosure K L F)
        infer_instance
      have hNC_top : NC = ⊤ := hmin NC ((isGarlingNormal_iff K NC).mpr hNC_normK)
      rw [← normalClosure_eq_iSup_adjoin K L F]
      ext z
      simp only [IntermediateField.mem_top, iff_true]
      have hz : z ∈ NC := hNC_top ▸ IntermediateField.mem_top
      exact hz
  · intro hnc
    have hnormF_ml : Normal K F := hnc.normal
    have hnormF : IsGarlingNormal K F := (isGarlingNormal_iff K F).mpr hnormF_ml
    have halgKL : IsAlgebraicExtension K L := (tower_algebraic_of_top_algebraic hnormF.1).1
    refine ⟨halgKL, hnormF, fun M hnormM => ?_⟩
    have hM_ml : Normal K M := (isGarlingNormal_iff K M).mp hnormM
    have hsub : ⨆ x : L, IntermediateField.adjoin K ((minpoly K x).rootSet F) ≤
        M.restrictScalars K := by
      refine iSup_le fun x => IntermediateField.adjoin_le_iff.mpr fun r hr => ?_
      have hx_int : IsIntegral K x := (isGarlingAlgebraic_iff_isIntegral K x).mp (halgKL x)
      have hmin_xM : minpoly K (algebraMap L M x) = minpoly K x :=
        minpoly.algHom_eq (IsScalarTower.toAlgHom K L M) (algebraMap L M).injective x
      have hspM : GarlingSplitsOver K (M.restrictScalars K) (minpoly K x) := by
        rw [garlingSplitsOver_iff_splits]
        change ((minpoly K x).map (algebraMap K M)).Splits
        rw [← hmin_xM]
        exact hM_ml.splits (algebraMap L M x)
      exact mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hx_int) hspM
        (Polynomial.mem_rootSet.mp hr).2
    rw [hnc.adjoin_rootSet] at hsub
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    exact hsub IntermediateField.mem_top

/-- **Corollary 2** [to Theorem 9.1] (§9.1, printed p. 80 / PDF p. 88):
*"If `L : K` is finite, it has a finite normal closure `F : L`."*

Proved directly following Garling's 4-line proof on p. 80: takes `g = m_{α₁} ⋯ m_{α_n}` for a
`K`-basis `α₁, …, α_n` of `L` and constructs `F : L` as a splitting field extension for `g` over `L`
via `Theorem 7.3` (`theorem_7_3_natDegree`), establishing both `IsFiniteExtension L F` and
`IsFiniteExtension K F`. -/
theorem corollary_2_to_theorem_9_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) :
    ∃ (F : Type v) (_ : Field F) (_ : Algebra K F) (_ : Algebra L F) (_ : IsScalarTower K L F),
      IsFiniteExtension L F ∧
      IsFiniteExtension K F ∧
      IsGarlingNormalClosure K L F := by
  classical
  have _ : Module.Finite K L := (isFiniteExtension_iff_moduleFinite K L).mp hfin
  have halgKL : IsAlgebraicExtension K L :=
    fun x => (isGarlingAlgebraic_iff_isIntegral K x).mpr (Algebra.IsIntegral.isIntegral x)
  let b := Module.Basis.ofVectorSpace K L
  have hb_int : ∀ i, IsIntegral K (b i) :=
    fun i => (isGarlingAlgebraic_iff_isIntegral K (b i)).mp (halgKL (b i))
  let g : K[X] := ∏ i, minpoly K (b i)
  have hg0 : g ≠ 0 :=
    (garlingSplitsOver_finset_prod_iff (L := K) Finset.univ
      (fun i => minpoly K (b i)) (fun i _ => minpoly.ne_zero (hb_int i))).1
  let gL : L[X] := g.map (algebraMap K L)
  obtain ⟨F, instFieldF, instAlgLF, hsfLF, _⟩ := theorem_7_3_natDegree gL
  let _ : Field F := instFieldF
  let _ : Algebra L F := instAlgLF
  let _ : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinLF : IsFiniteExtension L F := (corollary_to_theorem_7_1 hsfLF).1
  have _ : Module.Finite L F := (isFiniteExtension_iff_moduleFinite L F).mp hfinLF
  have _ : Module.Finite K F := Module.Finite.trans L F
  have hfinKF : IsFiniteExtension K F := (isFiniteExtension_iff_moduleFinite K F).mpr inferInstance
  -- Show `F : K` is a splitting field extension for `g` over `K`, hence normal by Corollary 1.
  have hsfKF : IsGarlingSplittingFieldExtension K F g := by
    have hg_splitsF : GarlingSplitsOver K F g := by
      rw [garlingSplitsOver_iff_splits, IsScalarTower.algebraMap_eq K L F, ← Polynomial.map_map]
      exact (garlingSplitsOver_iff_splits L F gL).mp hsfLF.1
    refine ⟨hg_splitsF, fun M₀ hM₀_ne hspM₀ => hM₀_ne ?_⟩
    -- Every `b i` is a root of `g`, so `algebraMap L F (b i) ∈ M₀`, hence `L ⊆ M₀`.
    have hb_M₀ : ∀ i, algebraMap L F (b i) ∈ M₀ := by
      intro i
      refine mem_of_garlingSplitsOver_intermediateField hg0 hspM₀ ?_
      have hevL : Polynomial.aeval (b i) g = 0 := by
        dsimp [g]
        rw [map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval K (b i))
      have h1 : algebraMap L F (Polynomial.aeval (b i) g) =
          Polynomial.aeval (algebraMap L F (b i)) g := by
        simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K L F) (b i) g).symm
      rw [← h1, hevL, map_zero]
    have hL_in_M₀ : ∀ l : L, algebraMap L F l ∈ M₀ := by
      let P : Submodule K L := M₀.toSubmodule.comap (IsScalarTower.toAlgHom K L F).toLinearMap
      have htop_P : (⊤ : Submodule K L) ≤ P := by
        rw [← b.span_eq, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb_M₀ i
      intro l
      exact htop_P Submodule.mem_top
    let M₀_L : IntermediateField L F :=
      { M₀.toSubfield with algebraMap_mem' := hL_in_M₀ }
    have hgL_sp : GarlingSplitsOver L M₀_L gL := by
      rw [garlingSplitsOver_iff_splits]
      have hsp' : (g.map (algebraMap K M₀)).Splits :=
        (garlingSplitsOver_iff_splits K M₀ g).mp hspM₀
      have hmap_eq : gL.map (algebraMap L M₀_L) = g.map (algebraMap K M₀) := by
        dsimp [gL]
        rw [Polynomial.map_map]
        rfl
      rwa [hmap_eq]
    have hM₀_L_top : M₀_L = ⊤ := by
      by_contra hne
      exact hsfLF.2 M₀_L hne hgL_sp
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    have hx : x ∈ M₀_L := hM₀_L_top ▸ IntermediateField.mem_top
    exact hx
  have hnormKF : IsGarlingNormal K F :=
    (corollary_1_to_theorem_9_1 hfinKF).mpr ⟨g, hsfKF⟩
  -- Minimality: if `F : M : L` is a tower and `M : K` is normal, each `m_{b_i}` splits over `M`,
  -- so `g` splits over `M`, hence `M = F`.
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
    hfinLF, hfinKF, halgKL, hnormKF, fun M hnormKM => ?_⟩
  obtain ⟨_, hminM⟩ := (isGarlingNormal_iff_minpoly_splits K M).mp hnormKM
  have hg_spM : GarlingSplitsOver K M g := by
    refine (garlingSplitsOver_finset_prod_iff (L := M) Finset.univ
      (fun i => minpoly K (b i)) (fun i _ => minpoly.ne_zero (hb_int i))).2.mpr fun i _ => ?_
    have hmin_eq : minpoly K (algebraMap L M (b i)) = minpoly K (b i) :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom K L M) (algebraMap L M).injective (b i)
    rw [← hmin_eq]
    exact hminM (algebraMap L M (b i))
  have hgL_spM : GarlingSplitsOver L M gL := by
    rw [garlingSplitsOver_iff_splits]
    have hmap_eq : gL.map (algebraMap L M) = g.map (algebraMap K M) := by
      dsimp [gL]
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L M]
    rw [hmap_eq]
    exact (garlingSplitsOver_iff_splits K M g).mp hg_spM
  by_contra hne
  exact hsfLF.2 M hne hgL_spM

/-- Extension-triple companion to **Corollary 2** [to Theorem 9.1] (§9.1, printed p. 80). -/
theorem corollary_2_to_theorem_9_1_triple {K : Type u} {L : Type v} [Field K] [Field L]
    (eKL : FieldExtensionTriple K L)
    (hfin : letI : Algebra K L := eKL.hom.toAlgebra; IsFiniteExtension K L) :
    ∃ (F : Type v) (_ : Field F) (eLF : FieldExtensionTriple L F),
      (letI : Algebra L F := eLF.hom.toAlgebra; IsFiniteExtension L F) ∧
      IsGarlingNormalClosureTriple eKL eLF := by
  let _ : Algebra K L := eKL.hom.toAlgebra
  obtain ⟨F, instFieldF, instAlgKF, instAlgLF, instTower, hfinLF, _, hcl⟩ :=
    corollary_2_to_theorem_9_1 (K := K) (L := L) hfin
  let _ : Field F := instFieldF
  obtain ⟨iLF, hiLF⟩ : ∃ iLF : L →+* F, iLF = @algebraMap L F _ _ instAlgLF := ⟨_, rfl⟩
  have halgL_eq : instAlgLF = iLF.toAlgebra := by
    apply Algebra.algebra_ext
    intro l
    rw [hiLF]
    rfl
  subst halgL_eq
  have halgK_eq : instAlgKF = (iLF.comp eKL.hom).toAlgebra := by
    apply Algebra.algebra_ext
    intro k
    exact @IsScalarTower.algebraMap_apply K L F _ _ _ _ iLF.toAlgebra instAlgKF instTower k
  subst halgK_eq
  exact ⟨F, instFieldF, { hom := iLF, mono := iLF.injective }, hfinLF, hcl⟩

/-- Scalar-tower form of **Corollary 3** [to Theorem 9.1] (§9.1, printed p. 80 / PDF p. 88):
for any field tower `K → M → L`, if `L : K` is normal then `L : M` is normal.

Proved directly following Garling's 2-line proof on p. 80: takes `S ⊆ K[x]` for which `L : K` is a
splitting field extension and views `S` inside `M[x]` (`S_M = map (algebraMap K M) '' S`). -/
theorem corollary_3_to_theorem_9_1_tower {K : Type u} {M : Type v} {L : Type w}
    [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (hnorm : IsGarlingNormal K L) :
    IsGarlingNormal M L := by
  obtain ⟨S, hsfS⟩ := (theorem_9_1 K L).mp hnorm
  refine (theorem_9_1 M L).mpr ⟨(Polynomial.map (algebraMap K M)) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hfS, rfl⟩
    rw [garlingSplitsOver_iff_splits, Polynomial.map_map, ← IsScalarTower.algebraMap_eq K M L]
    exact (garlingSplitsOver_iff_splits K L f).mp (hsfS.1 f hfS)
  · intro L' hL'
    let L'K : IntermediateField K L := L'.restrictScalars K
    have hL'K_top : L'K = ⊤ := hsfS.2 L'K fun f hfS => by
      rw [garlingSplitsOver_iff_splits]
      have hspM : ((f.map (algebraMap K M)).map (algebraMap M L')).Splits :=
        (garlingSplitsOver_iff_splits M L' (f.map (algebraMap K M))).mp
          (hL' (f.map (algebraMap K M)) ⟨f, hfS, rfl⟩)
      have hmap : (f.map (algebraMap K M)).map (algebraMap M L') = f.map (algebraMap K L'K) := by
        rw [Polynomial.map_map]
        congr 1
        ext k : 1
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply K M L k).symm
      rwa [hmap] at hspM
    ext x
    simp only [IntermediateField.mem_top, iff_true]
    have hx : x ∈ L'K := hL'K_top ▸ IntermediateField.mem_top
    exact hx

/-- **Corollary 3** [to Theorem 9.1] (§9.1, printed p. 80 / PDF p. 88):
*"If `L : K` is normal and `M` is an intermediate field then `L : M` is normal."* -/
theorem corollary_3_to_theorem_9_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hnorm : IsGarlingNormal K L) (M : IntermediateField K L) :
    IsGarlingNormal M L :=
  corollary_3_to_theorem_9_1_tower hnorm

/-- **Exercise 9.1** (§9.1, printed p. 80 / PDF p. 88):
*"Show that every algebraic extension has a normal closure."*

Constructed in the same universe `v` as `L` inside Chapter 8's explicit algebraic closure
`L̄ = GarlingAlgClosure L` by adjoining all roots in `L̄` of `{minpoly K α | α ∈ L}` and applying
`Theorem 9.1`. -/
theorem exercise_9_1 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) :
    ∃ (F : Type v) (_ : Field F) (_ : Algebra K F) (_ : Algebra L F) (_ : IsScalarTower K L F),
      IsGarlingNormalClosure K L F := by
  obtain ⟨LBar, instFieldBar, instAlgLBar, hclLBar⟩ := theorem_8_2 L
  let _ : Field LBar := instFieldBar
  let _ : Algebra L LBar := instAlgLBar
  let _ : Algebra K LBar := ((algebraMap L LBar).comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower K L LBar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let R : Set LBar := {r : LBar | ∃ α : L, Polynomial.aeval r (minpoly K α) = 0}
  let Fsub : IntermediateField L LBar := IntermediateField.adjoin L R
  have hL_in_R : Set.range (algebraMap L LBar) ⊆ R := by
    rintro _ ⟨α, rfl⟩
    refine ⟨α, ?_⟩
    have h1 : algebraMap L LBar (Polynomial.aeval α (minpoly K α)) =
        Polynomial.aeval (algebraMap L LBar α) (minpoly K α) := by
      simpa using (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K L LBar) α (minpoly K α)).symm
    rw [← h1, minpoly.aeval K α, map_zero]
  -- `Fsub.restrictScalars K` equals `IntermediateField.adjoin K R` and is a splitting field for
  -- `S = {minpoly K α | α ∈ L}`.
  let FK : IntermediateField K LBar := Fsub.restrictScalars K
  have hFK_eq : FK = IntermediateField.adjoin K R := by
    apply le_antisymm
    · have hL_le : ∀ l : L, algebraMap L LBar l ∈ IntermediateField.adjoin K R := fun l =>
        IntermediateField.subset_adjoin K R (hL_in_R ⟨l, rfl⟩)
      let E_L : IntermediateField L LBar :=
        { (IntermediateField.adjoin K R).toSubfield with algebraMap_mem' := hL_le }
      have hR_EL : R ⊆ (E_L : Set LBar) := IntermediateField.subset_adjoin K R
      have hle : Fsub ≤ E_L := IntermediateField.adjoin_le_iff.mpr hR_EL
      exact fun x hx => hle hx
    · rw [IntermediateField.adjoin_le_iff]
      exact IntermediateField.subset_adjoin L R
  let S : Set K[X] := Set.range (fun α : L => minpoly K α)
  have hsfS : IsGarlingSplittingFieldExtensionSet K FK S := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨α, rfl⟩
      have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
      have hm0 : minpoly K α ≠ 0 := minpoly.ne_zero hα_int
      have hspLBar : GarlingSplitsOver K LBar (minpoly K α) := by
        rw [garlingSplitsOver_iff_splits]
        have hcl := (garlingSplitsOver_iff_splits LBar LBar
          ((minpoly K α).map (algebraMap K LBar))).mp
          (hclLBar.2 ((minpoly K α).map (algebraMap K LBar)))
        simpa [Algebra.algebraMap_self, Polynomial.map_id] using hcl
      obtain ⟨n, c, γ, hexp⟩ := hspLBar
      have hroots : Set.range γ = (minpoly K α).rootSet LBar :=
        (garlingSplitsExplicit_props hm0 hexp).2.2.2
      refine (garlingSplitsOver_intermediateField_iff FK (minpoly K α)).mpr ⟨n, c, γ, fun j => ?_, hexp⟩
      have hmem : γ j ∈ (minpoly K α).rootSet LBar := hroots ▸ ⟨j, rfl⟩
      exact IntermediateField.subset_adjoin L R ⟨α, (Polynomial.mem_rootSet.mp hmem).2⟩
    · intro M₀ hspM₀
      let M₀_LBar : IntermediateField K LBar := M₀.map FK.val
      have hR_sub : R ⊆ (M₀_LBar : Set LBar) := by
        rintro r ⟨α, hr⟩
        have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
        have hr_FK : r ∈ FK := IntermediateField.subset_adjoin L R ⟨α, hr⟩
        let rFK : FK := ⟨r, hr_FK⟩
        have hrFK_root : Polynomial.aeval rFK (minpoly K α) = 0 := by
          apply FK.val.injective
          exact (Polynomial.aeval_algHom_apply FK.val rFK (minpoly K α)).symm.trans
            (hr.trans (map_zero FK.val).symm)
        have hmemM₀ : rFK ∈ M₀ :=
          mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hα_int)
            (hspM₀ (minpoly K α) ⟨α, rfl⟩) hrFK_root
        exact ⟨rFK, hmemM₀, rfl⟩
      have hFK_le : FK ≤ M₀_LBar := hFK_eq ▸ IntermediateField.adjoin_le_iff.mpr hR_sub
      ext x
      simp only [IntermediateField.mem_top, iff_true]
      obtain ⟨y, hyM₀, hyval⟩ := hFK_le x.2
      have hyx : y = x := Subtype.ext hyval
      exact hyx ▸ hyM₀
  have hnormFK : IsGarlingNormal K Fsub := (theorem_9_1 K FK).mpr ⟨S, hsfS⟩
  refine ⟨Fsub, inferInstance, inferInstance, inferInstance, inferInstance,
    halg, hnormFK, fun M hnormM => ?_⟩
  obtain ⟨_, hminM⟩ := (isGarlingNormal_iff_minpoly_splits K M).mp hnormM
  let M_LBar : IntermediateField L LBar := M.map Fsub.val
  have hR_in_M : R ⊆ (M_LBar : Set LBar) := by
    rintro r ⟨α, hr⟩
    have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
    have hr_F : r ∈ Fsub := IntermediateField.subset_adjoin L R ⟨α, hr⟩
    let rF : Fsub := ⟨r, hr_F⟩
    have hrF_root : Polynomial.aeval rF (minpoly K α) = 0 := by
      apply FK.val.injective
      exact (Polynomial.aeval_algHom_apply FK.val rF (minpoly K α)).symm.trans
        (hr.trans (map_zero FK.val).symm)
    have hmin_αM : minpoly K (algebraMap L M α) = minpoly K α :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom K L M) (algebraMap L M).injective α
    have hspM : GarlingSplitsOver K (M.restrictScalars K) (minpoly K α) := by
      rw [← hmin_αM]
      exact hminM (algebraMap L M α)
    have hrM : rF ∈ M :=
      mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hα_int) hspM hrF_root
    exact ⟨rF, hrM, rfl⟩
  have hF_le : Fsub ≤ M_LBar := IntermediateField.adjoin_le_iff.mpr hR_in_M
  ext x
  simp only [IntermediateField.mem_top, iff_true]
  obtain ⟨y, hyM, hyval⟩ := hF_le x.2
  have hyx : y = x := Subtype.ext hyval
  exact hyx ▸ hyM

/-- Extension-triple companion to **Exercise 9.1** (§9.1, printed p. 80). -/
theorem exercise_9_1_triple {K : Type u} {L : Type v} [Field K] [Field L]
    (eKL : FieldExtensionTriple K L)
    (halg : letI : Algebra K L := eKL.hom.toAlgebra; IsAlgebraicExtension K L) :
    ∃ (F : Type v) (_ : Field F) (eLF : FieldExtensionTriple L F),
      IsGarlingNormalClosureTriple eKL eLF := by
  let _ : Algebra K L := eKL.hom.toAlgebra
  obtain ⟨F, instFieldF, instAlgKF, instAlgLF, instTower, hcl⟩ := exercise_9_1 (K := K) (L := L) halg
  let _ : Field F := instFieldF
  obtain ⟨iLF, hiLF⟩ : ∃ iLF : L →+* F, iLF = @algebraMap L F _ _ instAlgLF := ⟨_, rfl⟩
  have halgL_eq : instAlgLF = iLF.toAlgebra := by
    apply Algebra.algebra_ext
    intro l
    rw [hiLF]
    rfl
  subst halgL_eq
  have halgK_eq : instAlgKF = (iLF.comp eKL.hom).toAlgebra := by
    apply Algebra.algebra_ext
    intro k
    exact @IsScalarTower.algebraMap_apply K L F _ _ _ _ iLF.toAlgebra instAlgKF instTower k
  subst halgK_eq
  exact ⟨F, instFieldF, { hom := iLF, mono := iLF.injective }, hcl⟩

/-- General compositum lemma (proved directly from `Theorem 9.1`, with no algebraicity assumption on
the ambient extension `L : K`): for *any* set `ℱ` of intermediate fields of `L : K` that are normal
over `K`, their supremum `sSup ℱ : IntermediateField K L` is normal over `K`. -/
theorem isGarlingNormal_sSup {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (ℱ : Set (IntermediateField K L)) (hℱ : ∀ N ∈ ℱ, IsGarlingNormal K N) :
    IsGarlingNormal K (sSup ℱ : IntermediateField K L) := by
  let M : IntermediateField K L := sSup ℱ
  let S : Set K[X] :=
    {f : K[X] | ∃ (N : IntermediateField K L) (_ : N ∈ ℱ) (x : N), f = minpoly K x}
  refine (theorem_9_1 K M).mpr ⟨S, ?_, ?_⟩
  · rintro _ ⟨N, hN, x, rfl⟩
    have hspN : GarlingSplitsOver K N (minpoly K x) :=
      ((isGarlingNormal_iff_minpoly_splits K N).mp (hℱ N hN)).2 x
    rw [garlingSplitsOver_iff_splits]
    have hspN' := (garlingSplitsOver_iff_splits K N (minpoly K x)).mp hspN
    have hmap :
        ((minpoly K x).map (algebraMap K N)).map (IntermediateField.inclusion (le_sSup hN)).toRingHom =
          (minpoly K x).map (algebraMap K M) := by
      rw [Polynomial.map_map]; rfl
    rw [← hmap]
    exact hspN'.map _
  · intro M' hspM'
    let M'L : IntermediateField K L := M'.map M.val
    have hℱ_le : ∀ N ∈ ℱ, N ≤ M'L := by
      intro N hN y hyN
      let x : N := ⟨y, hyN⟩
      have hx_int : IsIntegral K x :=
        (isGarlingAlgebraic_iff_isIntegral K x).mp ((hℱ N hN).1 x)
      let yM : M := ⟨y, le_sSup hN hyN⟩
      have hyM_root : Polynomial.aeval yM (minpoly K x) = 0 := by
        apply M.val.injective
        have h1 : (Polynomial.aeval (y : L) (minpoly K x)) = 0 := by
          have h2 := congrArg N.val (minpoly.aeval K x)
          rwa [← Polynomial.aeval_algHom_apply, map_zero] at h2
        exact (Polynomial.aeval_algHom_apply M.val yM (minpoly K x)).symm.trans
          (h1.trans (map_zero M.val).symm)
      have hyM_mem : yM ∈ M' :=
        mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hx_int)
          (hspM' (minpoly K x) ⟨N, hN, x, rfl⟩) hyM_root
      exact ⟨yM, hyM_mem, rfl⟩
    have hM_le : M ≤ M'L := sSup_le hℱ_le
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    obtain ⟨w, hwM', hwval⟩ := hM_le z.2
    have hwz : w = z := Subtype.ext hwval
    exact hwz ▸ hwM'

/-- Unconditional companion to **Exercise 9.2** (§9.1, p. 80): for *any* extension `L : K` (even
without `IsAlgebraicExtension K L`), there is a unique greatest intermediate field `M` of `L : K`
such that `M : K` is normal. -/
theorem exercise_9_2_unconditional (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    ∃! M : IntermediateField K L,
      IsGarlingNormal K M ∧
      ∀ N : IntermediateField K L, IsGarlingNormal K N → N ≤ M := by
  let ℱ : Set (IntermediateField K L) := {N : IntermediateField K L | IsGarlingNormal K N}
  refine ⟨sSup ℱ, ⟨isGarlingNormal_sSup ℱ fun _ hN => hN, fun _ hN => le_sSup hN⟩, ?_⟩
  rintro M' ⟨hM'_norm, hM'_max⟩
  exact le_antisymm (le_sSup hM'_norm) (hM'_max (sSup ℱ) (isGarlingNormal_sSup ℱ fun _ hN => hN))

/-- **Exercise 9.2** (§9.1, printed p. 80 / PDF p. 88):
*"Suppose that `L : K` is algebraic. Show that there is a greatest intermediate field `M` for which
`M : K` is normal."* -/
theorem exercise_9_2 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (_halg : IsAlgebraicExtension K L) :
    (∃ M : IntermediateField K L,
      IsGarlingNormal K M ∧
      ∀ N : IntermediateField K L, IsGarlingNormal K N → N ≤ M) ∧
    (∃! M : IntermediateField K L,
      IsGarlingNormal K M ∧
      ∀ N : IntermediateField K L, IsGarlingNormal K N → N ≤ M) := by
  obtain ⟨M, hM, _⟩ := exercise_9_2_unconditional K L
  exact ⟨⟨M, hM⟩, exercise_9_2_unconditional K L⟩

/-- **Exercise 9.3** (§9.1, printed p. 80 / PDF p. 88):
*"Suppose that `L : K` and that `M₁` and `M₂` are intermediate fields. Show that if `M₁ : K` and
`M₂ : K` are normal then so are `K(M₁, M₂) : K` and `M₁ ∩ M₂ : K`."*

Proved with no algebraicity assumption on `L : K`, covering both the lattice join `M₁ ⊔ M₂` and
`IntermediateField.adjoin K ((M₁ : Set L) ∪ (M₂ : Set L))` for `K(M₁, M₂)`, alongside `M₁ ⊓ M₂`. -/
theorem exercise_9_3 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (M₁ M₂ : IntermediateField K L)
    (h₁ : IsGarlingNormal K M₁) (h₂ : IsGarlingNormal K M₂) :
    IsGarlingNormal K (IntermediateField.adjoin K ((M₁ : Set L) ∪ (M₂ : Set L))) ∧
    IsGarlingNormal K (M₁ ⊔ M₂ : IntermediateField K L) ∧
    IsGarlingNormal K (M₁ ⊓ M₂ : IntermediateField K L) := by
  -- 1. `M₁ ⊔ M₂` and `K(M₁, M₂) = adjoin K (M₁ ∪ M₂)`.
  have hsup_eq_sSup : (M₁ ⊔ M₂ : IntermediateField K L) = sSup ({M₁, M₂} : Set (IntermediateField K L)) := by
    rw [sSup_pair]
  have hnorm_sup : IsGarlingNormal K (M₁ ⊔ M₂ : IntermediateField K L) := by
    rw [hsup_eq_sSup]
    refine isGarlingNormal_sSup {M₁, M₂} ?_
    rintro N (rfl | rfl)
    · exact h₁
    · exact h₂
  have hadj_eq_sup :
      IntermediateField.adjoin K ((M₁ : Set L) ∪ (M₂ : Set L)) = (M₁ ⊔ M₂ : IntermediateField K L) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx₁ | hx₂)
      · exact (le_sup_left : M₁ ≤ M₁ ⊔ M₂) hx₁
      · exact (le_sup_right : M₂ ≤ M₁ ⊔ M₂) hx₂
    · exact sup_le
        (fun x hx₁ => IntermediateField.subset_adjoin K _ (Or.inl hx₁))
        (fun x hx₂ => IntermediateField.subset_adjoin K _ (Or.inr hx₂))
  have hnorm_adj : IsGarlingNormal K (IntermediateField.adjoin K ((M₁ : Set L) ∪ (M₂ : Set L))) :=
    (isGarlingNormal_congr (IntermediateField.equivOfEq hadj_eq_sup)).mpr hnorm_sup
  -- 2. `M₁ ⊓ M₂`.
  have hnorm_inf : IsGarlingNormal K (M₁ ⊓ M₂ : IntermediateField K L) := by
    rw [isGarlingNormal_iff_minpoly_splits]
    obtain ⟨halg₁, hsp₁⟩ := (isGarlingNormal_iff_minpoly_splits K M₁).mp h₁
    obtain ⟨_, hsp₂⟩ := (isGarlingNormal_iff_minpoly_splits K M₂).mp h₂
    let inc₁ : ↥(M₁ ⊓ M₂) →ₐ[K] M₁ := IntermediateField.inclusion inf_le_left
    let inc₂ : ↥(M₁ ⊓ M₂) →ₐ[K] M₂ := IntermediateField.inclusion inf_le_right
    have halg_inf : IsAlgebraicExtension K (M₁ ⊓ M₂ : IntermediateField K L) := by
      intro x
      obtain ⟨p, hp0, hpx⟩ := halg₁ (inc₁ x)
      refine ⟨p, hp0, inc₁.injective ?_⟩
      exact (Polynomial.aeval_algHom_apply inc₁ x p).symm.trans (hpx.trans (map_zero inc₁).symm)
    refine ⟨halg_inf, fun x => ?_⟩
    have hx_int : IsIntegral K x := (isGarlingAlgebraic_iff_isIntegral K x).mp (halg_inf x)
    have hm0 : minpoly K x ≠ 0 := minpoly.ne_zero hx_int
    have hm_eq₁ : minpoly K (inc₁ x) = minpoly K x :=
      minpoly.algHom_eq inc₁ inc₁.injective x
    have hm_eq₂ : minpoly K (inc₂ x) = minpoly K x :=
      minpoly.algHom_eq inc₂ inc₂.injective x
    have hspL₁ : GarlingSplitsOver K M₁ (minpoly K x) := hm_eq₁ ▸ hsp₁ (inc₁ x)
    have hspL₂ : GarlingSplitsOver K M₂ (minpoly K x) := hm_eq₂ ▸ hsp₂ (inc₂ x)
    obtain ⟨n, c, α, hαM₁, hexpL⟩ :=
      (garlingSplitsOver_intermediateField_iff M₁ (minpoly K x)).mp hspL₁
    have hroots : Set.range α = (minpoly K x).rootSet L :=
      (garlingSplitsExplicit_props hm0 hexpL).2.2.2
    have hαM₂ : ∀ j : Fin n, α j ∈ M₂ := by
      intro j
      have hmem : α j ∈ (minpoly K x).rootSet L := hroots ▸ ⟨j, rfl⟩
      exact mem_of_garlingSplitsOver_intermediateField hm0 hspL₂ (Polynomial.mem_rootSet.mp hmem).2
    exact (garlingSplitsOver_intermediateField_iff (M₁ ⊓ M₂) (minpoly K x)).mpr
      ⟨n, c, α, fun j => ⟨hαM₁ j, hαM₂ j⟩, hexpL⟩
  exact ⟨hnorm_adj, hnorm_sup, hnorm_inf⟩

/-! ## §9.2 Monomorphisms and automorphisms (printed pp. 80–81, PDF pp. 88–89) -/

/-- Introductory prose counterexample in §9.2 (printed p. 80 / PDF p. 88):
for `r = 2^{1/3} ∈ ℂ` and `ω = omegaCubeRoot` (the primitive complex cube root of `1`, `ω ≠ 1`),
`ℚ(2^{1/3}, ω) : ℚ` is normal (as the splitting field of `f = x³ - 2 ∈ ℚ[x]`), whereas the
intermediate extension `ℚ(2^{1/3}) : ℚ` is **not** normal because `x³ - 2` is irreducible in
`ℚ[x]`, has the root `2^{1/3}` in `ℚ(2^{1/3})`, and does not split over `ℚ(2^{1/3})` (also recording
that at the trivial root `ω = 1`, `ℚ(2^{1/3}, 1) = ℚ(2^{1/3})` is not normal). -/
theorem section_9_2_cube_root_example :
    let r : ℂ := twoPowInvNat 3
    let ω : ℂ := omegaCubeRoot
    let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({r, ω} : Set ℂ)
    IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 3 - 2) ∧
    IsGarlingNormal ℚ E ∧
    Irreducible (Polynomial.X ^ 3 - 2 : ℚ[X]) ∧
    (∃ α : ℚ⟮r⟯, Polynomial.aeval α (Polynomial.X ^ 3 - 2 : ℚ[X]) = 0) ∧
    ¬ GarlingSplitsOver ℚ ℚ⟮r⟯ (Polynomial.X ^ 3 - 2) ∧
    ¬ IsGarlingNormal ℚ ℚ⟮r⟯ ∧
    ¬ IsGarlingNormal ℚ (IntermediateField.adjoin ℚ ({r, (1 : ℂ)} : Set ℂ)) := by
  intro r ω E
  obtain ⟨_, hω_cube, hω_ne1⟩ := omegaCubeRoot_props
  have hex731 := example_7_3_1 (by decide : Nat.Prime 3) hω_cube hω_ne1
  have hset_comm : ({r, ω} : Set ℂ) = {ω, r} := Set.pair_comm r ω
  have hE_eq : E = IntermediateField.adjoin ℚ ({ω, r} : Set ℂ) := by
    dsimp [E]; rw [hset_comm]
  have hsf_E' : IsGarlingSplittingFieldExtension ℚ
      (IntermediateField.adjoin ℚ ({ω, r} : Set ℂ)) (Polynomial.X ^ 3 - 2) :=
    hex731.2.2.2.2.2.2.2.2.1
  have hsf_E : IsGarlingSplittingFieldExtension ℚ E (Polynomial.X ^ 3 - 2) := hE_eq ▸ hsf_E'
  have hnorm_E : IsGarlingNormal ℚ E :=
    (corollary_1_to_theorem_9_1_iff ℚ E).mpr ⟨Polynomial.X ^ 3 - 2, hsf_E⟩ |>.2
  have hirr : Irreducible (Polynomial.X ^ 3 - 2 : ℚ[X]) := hex731.1
  have hmin_r : minpoly ℚ r = Polynomial.X ^ 3 - 2 := hex731.2.1
  have hfin_r : Module.finrank ℚ ℚ⟮r⟯ = 3 := hex731.2.2.1
  have hfin_E' : Module.finrank ℚ (IntermediateField.adjoin ℚ ({ω, r} : Set ℂ)) = 6 :=
    hex731.2.2.2.2.2.2.2.2.2.1
  have hfin_E : Module.finrank ℚ E = 6 := hE_eq ▸ hfin_E'
  have hr_root : ∃ α : ℚ⟮r⟯, Polynomial.aeval α (Polynomial.X ^ 3 - 2 : ℚ[X]) = 0 := by
    let gen : ℚ⟮r⟯ := IntermediateField.AdjoinSimple.gen ℚ r
    refine ⟨gen, (ℚ⟮r⟯).val.injective ?_⟩
    exact (Polynomial.aeval_algHom_apply (ℚ⟮r⟯).val gen (Polynomial.X ^ 3 - 2 : ℚ[X])).symm.trans
      ((hmin_r ▸ minpoly.aeval ℚ r).trans (map_zero (ℚ⟮r⟯).val).symm)
  have hnot_sp_r : ¬ GarlingSplitsOver ℚ ℚ⟮r⟯ (Polynomial.X ^ 3 - 2) := by
    intro hsp_r
    have hr_in_E : ℚ⟮r⟯ ≤ E :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.subset_adjoin ℚ ({r, ω} : Set ℂ) (Or.inl rfl)))
    let M : IntermediateField ℚ E :=
      { (ℚ⟮r⟯).toSubfield.comap E.val.toRingHom with
        algebraMap_mem' := fun q => (ℚ⟮r⟯).algebraMap_mem q }
    have hM_map : M.map E.val = ℚ⟮r⟯ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hz; exact ⟨⟨z, hr_in_E hz⟩, hz, rfl⟩
    let eMr : M ≃ₐ[ℚ] ℚ⟮r⟯ :=
      (IntermediateField.equivMap M E.val).trans (IntermediateField.equivOfEq hM_map)
    have hsp_M : GarlingSplitsOver ℚ M (Polynomial.X ^ 3 - 2) := by
      rw [garlingSplitsOver_iff_splits]
      have hsp' := (garlingSplitsOver_iff_splits ℚ ℚ⟮r⟯ (Polynomial.X ^ 3 - 2)).mp hsp_r
      have hcomp : eMr.symm.toRingHom.comp (algebraMap ℚ ℚ⟮r⟯) = algebraMap ℚ M :=
        RingHom.ext fun q => eMr.symm.commutes q
      have hmap : ((Polynomial.X ^ 3 - 2 : ℚ[X]).map (algebraMap ℚ ℚ⟮r⟯)).map eMr.symm.toRingHom =
          (Polynomial.X ^ 3 - 2 : ℚ[X]).map (algebraMap ℚ M) := by
        rw [Polynomial.map_map, hcomp]
      rw [← hmap]
      exact hsp'.map eMr.symm.toRingHom
    have hM_top : M = ⊤ := by
      by_contra hne
      exact hsf_E.2 M hne hsp_M
    have hfin_M : Module.finrank ℚ M = 3 := eMr.toLinearEquiv.finrank_eq.trans hfin_r
    have hfin_top : Module.finrank ℚ M = 6 :=
      ((IntermediateField.equivOfEq hM_top).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq.trans hfin_E
    omega
  have hnot_norm_r : ¬ IsGarlingNormal ℚ ℚ⟮r⟯ := by
    intro hnorm
    rcases hnorm.2 (Polynomial.X ^ 3 - 2) hirr with hsp | hno
    · exact hnot_sp_r hsp
    · exact hno hr_root
  have hadj_one : IntermediateField.adjoin ℚ ({r, (1 : ℂ)} : Set ℂ) = ℚ⟮r⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro z (rfl | rfl)
      · exact IntermediateField.mem_adjoin_simple_self ℚ r
      · exact (ℚ⟮r⟯).one_mem
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin ℚ ({r, (1 : ℂ)} : Set ℂ) (Or.inl rfl)
  have hnot_norm_one : ¬ IsGarlingNormal ℚ (IntermediateField.adjoin ℚ ({r, (1 : ℂ)} : Set ℂ)) :=
    fun h => hnot_norm_r ((isGarlingNormal_congr (IntermediateField.equivOfEq hadj_one)).mp h)
  exact ⟨hsf_E, hnorm_E, hirr, hr_root, hnot_sp_r, hnot_norm_r, hnot_norm_one⟩

/-- Helper (`(i) ⟹ (ii) ⟹ (iii)` of `Theorem 9.2` and `Exercise 9.7`, with **no** finiteness or
`L : K` normality assumption): for *any* algebraic extension `M : K` inside `L : K`, if `M : K` is
normal then every `K`-fixing automorphism `σ : L ≃ₐ[K] L` satisfies `σ(M) ⊆ M`, and if every
`σ : L ≃ₐ[K] L` satisfies `σ(M) ⊆ M` then every `σ : L ≃ₐ[K] L` satisfies `σ(M) = M`. -/
theorem normal_intermediateField_imp_aut_subset_and_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] (M : IntermediateField K L) :
    (IsGarlingNormal K M → ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ∧
    ((∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) →
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) := by
  refine ⟨?_, ?_⟩
  · intro hnormM σ
    rintro _ ⟨x, hxM, rfl⟩
    obtain ⟨halgM, hminM⟩ := (isGarlingNormal_iff_minpoly_splits K M).mp hnormM
    let xM : M := ⟨x, hxM⟩
    have hx_int : IsIntegral K xM := (isGarlingAlgebraic_iff_isIntegral K xM).mp (halgM xM)
    let m : K[X] := minpoly K xM
    have hm_x : Polynomial.aeval x m = 0 := by
      have h := congrArg M.val (minpoly.aeval K xM)
      rwa [← Polynomial.aeval_algHom_apply, map_zero] at h
    have hm_σx : Polynomial.aeval (σ x) m = 0 := by
      change Polynomial.aeval (σ.toAlgHom x) m = 0
      rw [Polynomial.aeval_algHom_apply σ.toAlgHom x m, hm_x, map_zero]
    exact mem_of_garlingSplitsOver_intermediateField (minpoly.ne_zero hx_int) (hminM xM) hm_σx
  · intro hsub σ
    apply Set.Subset.antisymm (hsub σ)
    intro x hxM
    refine ⟨σ.symm x, hsub σ.symm ⟨x, hxM, rfl⟩, σ.apply_symm_apply x⟩

/-- **Theorem 9.2** (§9.2, printed p. 81 / PDF p. 89):
*"Suppose that `L : K` is a finite normal extension and that `M` is an intermediate field. The
following are equivalent:
(i) `M : K` is normal;
(ii) if `σ` is an automorphism of `L` which fixes `K` then `σ(M) ⊆ M`;
(iii) if `σ` is an automorphsim [sic] of `L` which fixes `K` then `σ(M) = M`."*

Proved step-by-step following Garling's p. 81 proof via `Corollary 1` to `Theorem 9.1`,
`Corollary 1` to `Theorem 7.4`, and `Corollary 1` to `Theorem 7.5` (with zero separability
assumption). -/
theorem theorem_9_2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (hnorm : IsGarlingNormal K L) (M : IntermediateField K L) :
    (IsGarlingNormal K M ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ∧
    ((∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) ∧
    (IsGarlingNormal K M ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) := by
  obtain ⟨h12, h23⟩ := normal_intermediateField_imp_aut_subset_and_eq M
  have h31 : (∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) → IsGarlingNormal K M := by
    intro h3
    -- By Corollary 1 to Theorem 9.1, `L : K` is a splitting field extension for some `g ∈ K[X]`.
    obtain ⟨g, hsf_g⟩ := (corollary_1_to_theorem_9_1 hfin).mp hnorm
    obtain ⟨halgL, hminL⟩ := (isGarlingNormal_iff_minpoly_splits K L).mp hnorm
    have halgM : IsAlgebraicExtension K M :=
      (tower_algebraic_of_top_algebraic (K := K) (L := M) (F := L) halgL).1
    rw [isGarlingNormal_iff_minpoly_splits]
    refine ⟨halgM, fun αM => ?_⟩
    let α : L := αM.1
    have hαM : α ∈ M := αM.2
    have hmin_eq : minpoly K αM = minpoly K α :=
      (minpoly.algHom_eq M.val M.val.injective αM).symm
    rw [hmin_eq]
    let m : K[X] := minpoly K α
    have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halgL α)
    have hm_irr : Irreducible m := minpoly.irreducible hα_int
    have hm_monic : m.Monic := minpoly.monic hα_int
    obtain ⟨d, cm, βm, hexp_mL⟩ := hminL α
    have hm_roots : Set.range βm = m.rootSet L :=
      (garlingSplitsExplicit_props hm_irr.ne_zero hexp_mL).2.2.2
    refine (garlingSplitsOver_intermediateField_iff M m).mpr ⟨d, cm, βm, fun r => ?_, hexp_mL⟩
    -- Let `β = βm r` be any root of `m` in `L`; construct `σ : L ≃ₐ[K] L` sending `α ↦ β`.
    let β : L := βm r
    have hβ_root : Polynomial.aeval β m = 0 :=
      (Polynomial.mem_rootSet.mp (hm_roots ▸ ⟨r, rfl⟩)).2
    have hβ_alg : IsGarlingAlgebraic K β := ⟨m, hm_irr.ne_zero, hβ_root⟩
    have hm_β : minpoly K β = m :=
      (minpoly.eq_of_irreducible_of_monic hm_irr hβ_root hm_monic).symm
    let Kα : IntermediateField K L := IntermediateField.adjoin K ({α} : Set L)
    let Kβ : IntermediateField K L := IntermediateField.adjoin K ({β} : Set L)
    let genα : Kα := IntermediateField.AdjoinSimple.gen K α
    let genβ : Kβ := IntermediateField.AdjoinSimple.gen K β
    have hadj_α : IntermediateField.adjoin K ({genα} : Set Kα) = ⊤ := by
      ext x; simp only [IntermediateField.mem_top, iff_true]
      let L0 : IntermediateField K L := (IntermediateField.adjoin K ({genα} : Set Kα)).map Kα.val
      have hmem : α ∈ L0 := ⟨genα, IntermediateField.mem_adjoin_simple_self K genα, rfl⟩
      obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
      exact (Kα.val.injective hyx) ▸ hy
    have hadj_β : IntermediateField.adjoin K ({genβ} : Set Kβ) = ⊤ := by
      ext x; simp only [IntermediateField.mem_top, iff_true]
      let L0 : IntermediateField K L := (IntermediateField.adjoin K ({genβ} : Set Kβ)).map Kβ.val
      have hmem : β ∈ L0 := ⟨genβ, IntermediateField.mem_adjoin_simple_self K genβ, rfl⟩
      obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
      exact (Kβ.val.injective hyx) ▸ hy
    have hgenα_alg : IsGarlingAlgebraic K genα :=
      ⟨m, hm_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kα.val genα m).symm.trans (minpoly.aeval K α))⟩
    have hgenβ_alg : IsGarlingAlgebraic K genβ :=
      ⟨m, hm_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kβ.val genβ m).symm.trans hβ_root)⟩
    have hmin_genα : minpoly K genα = m :=
      (minpoly.algHom_eq Kα.val Kα.val.injective genα).symm
    have hmin_genβ : minpoly K genβ = m :=
      (minpoly.algHom_eq Kβ.val Kβ.val.injective genβ).symm.trans hm_β
    have hm_map :
        garlingMapPoly (RingEquiv.refl K).toRingHom (minpoly K genα) = minpoly K genβ := by
      simp [hmin_genα, hmin_genβ]
    -- By Corollary 1 to Theorem 7.4, `j : K(α) ≃+* K(β)` sending `α ↦ β` and fixing `K`.
    obtain ⟨j, ⟨hj_gen, hj_fix⟩, _⟩ :=
      (corollary_1_to_theorem_7_4_equiv hadj_α hgenα_alg hadj_β hgenβ_alg (RingEquiv.refl K)).2 hm_map
    let gα : Kα[X] := g.map (algebraMap K Kα)
    let gβ : Kβ[X] := g.map (algebraMap K Kβ)
    have hj_gα : garlingMapPoly j.toRingHom gα = gβ := by
      have hcomp : j.toRingHom.comp (algebraMap K Kα) = algebraMap K Kβ :=
        RingHom.ext fun k => by simpa using hj_fix k
      change (g.map (algebraMap K Kα)).map j.toRingHom = g.map (algebraMap K Kβ)
      rw [Polynomial.map_map, hcomp]
    have hsf_KαL : IsGarlingSplittingFieldExtension Kα L gα := by
      refine ⟨?_, fun N hNne hspN => hNne ?_⟩
      · rw [garlingSplitsOver_iff_splits]
        have hmap : gα.map (algebraMap Kα L) = g.map (algebraMap K L) := by
          dsimp [gα]; rw [Polynomial.map_map]; rfl
        rw [hmap]
        exact (garlingSplitsOver_iff_splits K L g).mp hsf_g.1
      · let NK : IntermediateField K L := N.restrictScalars K
        have hspNK : GarlingSplitsOver K NK g := by
          rw [garlingSplitsOver_iff_splits]
          have hmap : g.map (algebraMap K NK) = gα.map (algebraMap Kα N) := by
            dsimp [gα]; rw [Polynomial.map_map]; rfl
          rw [hmap]
          exact (garlingSplitsOver_iff_splits Kα N gα).mp hspN
        have hNK_top : NK = ⊤ := by
          by_contra hne
          exact hsf_g.2 NK hne hspNK
        ext z
        simp only [IntermediateField.mem_top, iff_true]
        have hz : z ∈ NK := hNK_top ▸ IntermediateField.mem_top
        exact hz
    have hsf_KβL : IsGarlingSplittingFieldExtension Kβ L (garlingMapPoly j.toRingHom gα) := by
      rw [hj_gα]
      refine ⟨?_, fun N hNne hspN => hNne ?_⟩
      · rw [garlingSplitsOver_iff_splits]
        have hmap : gβ.map (algebraMap Kβ L) = g.map (algebraMap K L) := by
          dsimp [gβ]; rw [Polynomial.map_map]; rfl
        rw [hmap]
        exact (garlingSplitsOver_iff_splits K L g).mp hsf_g.1
      · let NK : IntermediateField K L := N.restrictScalars K
        have hspNK : GarlingSplitsOver K NK g := by
          rw [garlingSplitsOver_iff_splits]
          have hmap : g.map (algebraMap K NK) = gβ.map (algebraMap Kβ N) := by
            dsimp [gβ]; rw [Polynomial.map_map]; rfl
          rw [hmap]
          exact (garlingSplitsOver_iff_splits Kβ N gβ).mp hspN
        have hNK_top : NK = ⊤ := by
          by_contra hne
          exact hsf_g.2 NK hne hspNK
        ext z
        simp only [IntermediateField.mem_top, iff_true]
        have hz : z ∈ NK := hNK_top ▸ IntermediateField.mem_top
        exact hz
    -- By Corollary 1 to Theorem 7.5, `j` extends to an isomorphism `σ₀ : L →+* L`.
    have hj_iso : IsRingIsomorphism j.toRingHom := j.bijective
    obtain ⟨σ₀, hσ₀_iso, hσ₀_ext⟩ :=
      corollary_1_to_theorem_7_5 hj_iso gα hsf_KαL hsf_KβL
    let σEquiv : L ≃+* L := RingEquiv.ofBijective σ₀ hσ₀_iso
    have hσ_fixK : ∀ k : K, σEquiv (algebraMap K L k) = algebraMap K L k := by
      intro k
      have hk : algebraMap K L k = algebraMap Kα L (algebraMap K Kα k) := rfl
      rw [hk]
      change σ₀ (algebraMap Kα L (algebraMap K Kα k)) = algebraMap K L k
      rw [hσ₀_ext (algebraMap K Kα k)]
      have hj_k : j.toRingHom (algebraMap K Kα k) = algebraMap K Kβ k := by simpa using hj_fix k
      rw [hj_k]
      rfl
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := σEquiv) hσ_fixK
    have hσα : σ α = β := by
      have hα_val : α = algebraMap Kα L genα := rfl
      rw [hα_val]
      change σ₀ (algebraMap Kα L genα) = β
      have hj_g : j.toRingHom genα = genβ := hj_gen
      rw [hσ₀_ext genα, hj_g]
      rfl
    have hβ_mem : β ∈ (σ : L → L) '' (M : Set L) := ⟨α, hαM, hσα⟩
    rwa [h3 σ] at hβ_mem
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h σ => (h σ).subset⟩, ⟨fun h => h23 (h12 h), h31⟩⟩

/-- Helper equivalence between `L ≃ₐ[K] L` and Chapter 4's `σ : L →+* L` satisfying
`IsFieldAutomorphism σ` and `FixesBaseField K σ`. -/
theorem forall_algEquiv_iff_isFieldAutomorphism {K L : Type*} [Field K] [Field L] [Algebra K L]
    (P : (L → L) → Prop) :
    (∀ σ : L ≃ₐ[K] L, P σ) ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ → P σ := by
  constructor
  · intro h σ hAut hFix
    let e : L ≃+* L := RingEquiv.ofBijective σ hAut
    let σAlg : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := e) hFix
    exact h σAlg
  · intro h σ
    exact h σ.toRingHom σ.bijective σ.commutes

/-- Chapter 4 vocabulary (`IsFieldAutomorphism` + `FixesBaseField`) companion to **Theorem 9.2**
(§9.2, printed p. 81). -/
theorem theorem_9_2_garling {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (hnorm : IsGarlingNormal K L) (M : IntermediateField K L) :
    (IsGarlingNormal K M ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ∧
    ((∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) = (M : Set L)) ∧
    (IsGarlingNormal K M ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) = (M : Set L)) := by
  have h := theorem_9_2 hfin hnorm M
  have eSub := forall_algEquiv_iff_isFieldAutomorphism (K := K) (L := L)
    (fun f => f '' (M : Set L) ⊆ (M : Set L))
  have eEq := forall_algEquiv_iff_isFieldAutomorphism (K := K) (L := L)
    (fun f => f '' (M : Set L) = (M : Set L))
  exact ⟨h.1.trans eSub, eSub.symm.trans (h.2.1.trans eEq), h.2.2.trans eEq⟩

/-- **Exercise 9.4** (§9.2, printed p. 81 / PDF p. 89):
*"Suppose that `N : L` and `N' : L` are two normal closures of `L : K`. Show that there is an
isomorphism `j` of `N` onto `N'` such that `j(l) = l` for `l ∈ L`."*

Proved across arbitrary universes `{K : Type u} {L : Type v} {N : Type w} {N' : Type*}` via
Chapter 8's `GarlingAlgClosure N'`, `Theorem 8.3`, and `Exercise 9.3` (`ImN ⊓ ImN'` is normal over
`K`, forcing `ImN = ImN'` by normal-closure minimality of both `N` and `N'`). -/
theorem exercise_9_4 {K : Type u} {L : Type v} {N : Type w} {N' : Type*}
    [Field K] [Field L] [Field N] [Field N']
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    [Algebra L N'] [Algebra K N'] [IsScalarTower K L N']
    (hN : IsGarlingNormalClosure K L N)
    (hN' : IsGarlingNormalClosure K L N') :
    ∃ j : N →+* N', IsRingIsomorphism j ∧ ∀ l : L, j (algebraMap L N l) = algebraMap L N' l := by
  obtain ⟨N'Bar, instFieldBar, instAlgN'Bar, hclBar⟩ := theorem_8_2 N'
  let _ : Field N'Bar := instFieldBar
  let _ : Algebra N' N'Bar := instAlgN'Bar
  let _ : Algebra L N'Bar := ((algebraMap N' N'Bar).comp (algebraMap L N')).toAlgebra
  let _ : Algebra K N'Bar := ((algebraMap L N'Bar).comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower L N' N'Bar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower K L N'Bar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower K N' N'Bar := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap N' N'Bar (algebraMap L N' (algebraMap K L k)) =
      algebraMap N' N'Bar (algebraMap K N' k)
    rw [← IsScalarTower.algebraMap_apply K L N']
  -- `N : L` is algebraic since `N : K` is normal; extend `algebraMap L N'Bar` via Theorem 8.3.
  have halgLN : IsAlgebraicExtension L N := (tower_algebraic_of_top_algebraic hN.2.1.1).2
  let iL : L →+* N'Bar := algebraMap L N'Bar
  obtain ⟨θ, hθ_mono, hθ_L⟩ := theorem_8_3 (L := N) iL.injective halgLN hclBar.2
  let θAlgL : N →ₐ[L] N'Bar := ⟨θ, hθ_L⟩
  have hθ_K : ∀ k : K, θ (algebraMap K N k) = algebraMap K N'Bar k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K L N, hθ_L (algebraMap K L k)]
    rfl
  let θAlgK : N →ₐ[K] N'Bar := ⟨θ, hθ_K⟩
  let ImN : IntermediateField L N'Bar := θAlgL.fieldRange
  let iN' : N' →ₐ[L] N'Bar := IsScalarTower.toAlgHom L N' N'Bar
  let ImN' : IntermediateField L N'Bar := iN'.fieldRange
  -- `N ≃ ImN` and `N' ≃ ImN'` over `L` and `K`.
  let eN_K : N ≃ₐ[K] ImN.restrictScalars K := AlgEquiv.ofInjectiveField θAlgK
  let eN'_K : N' ≃ₐ[K] ImN'.restrictScalars K :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K N' N'Bar)
  have hImN_norm : IsGarlingNormal K (ImN.restrictScalars K) :=
    (isGarlingNormal_congr eN_K).mp hN.2.1
  have hImN'_norm : IsGarlingNormal K (ImN'.restrictScalars K) :=
    (isGarlingNormal_congr eN'_K).mp hN'.2.1
  -- By Exercise 9.3, `(ImN ⊓ ImN').restrictScalars K` is normal over `K`.
  let InfK : IntermediateField K N'Bar := ImN.restrictScalars K ⊓ ImN'.restrictScalars K
  have hInf_norm : IsGarlingNormal K InfK :=
    (exercise_9_3 (ImN.restrictScalars K) (ImN'.restrictScalars K) hImN_norm hImN'_norm).2.2
  -- Pull `ImN ⊓ ImN'` back to `IntermediateField L N` and `IntermediateField L N'`.
  let M_N : IntermediateField L N := (ImN ⊓ ImN').comap θAlgL
  have hM_N_map : M_N.map θAlgL = ImN ⊓ ImN' := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨⟨x, rfl⟩, hz'⟩; exact ⟨x, ⟨⟨x, rfl⟩, hz'⟩, rfl⟩
  let eMN_K : M_N ≃ₐ[K] InfK :=
    AlgEquiv.ofRingEquiv
      (f := ((IntermediateField.equivMap M_N θAlgL).trans
        (IntermediateField.equivOfEq hM_N_map)).toRingEquiv)
      fun k => Subtype.ext (hθ_K k)
  have hMN_top : M_N = ⊤ := hN.2.2 M_N ((isGarlingNormal_congr eMN_K).mpr hInf_norm)
  have hImN_le_ImN' : ImN ≤ ImN' := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ M_N := hMN_top ▸ IntermediateField.mem_top
    exact hx.2
  let M_N' : IntermediateField L N' := (ImN ⊓ ImN').comap iN'
  have hM_N'_map : M_N'.map iN' = ImN ⊓ ImN' := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨hz, ⟨x, rfl⟩⟩; exact ⟨x, ⟨hz, ⟨x, rfl⟩⟩, rfl⟩
  let eMN'_K : M_N' ≃ₐ[K] InfK :=
    AlgEquiv.ofRingEquiv
      (f := ((IntermediateField.equivMap M_N' iN').trans
        (IntermediateField.equivOfEq hM_N'_map)).toRingEquiv)
      fun k => Subtype.ext (IsScalarTower.algebraMap_apply K N' N'Bar k).symm
  have hMN'_top : M_N' = ⊤ := hN'.2.2 M_N' ((isGarlingNormal_congr eMN'_K).mpr hInf_norm)
  have hImN'_le_ImN : ImN' ≤ ImN := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ M_N' := hMN'_top ▸ IntermediateField.mem_top
    exact hx.1
  have hIm_eq : ImN = ImN' := le_antisymm hImN_le_ImN' hImN'_le_ImN
  let eL : N ≃ₐ[L] N' :=
    ((AlgEquiv.ofInjectiveField θAlgL).trans (IntermediateField.equivOfEq hIm_eq)).trans
      (AlgEquiv.ofInjectiveField iN').symm
  exact ⟨eL.toRingHom, eL.bijective, eL.commutes⟩

/-- `RingEquiv` companion to **Exercise 9.4** (§9.2, printed p. 81). -/
theorem exercise_9_4_ringEquiv {K : Type u} {L : Type v} {N : Type w} {N' : Type*}
    [Field K] [Field L] [Field N] [Field N']
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    [Algebra L N'] [Algebra K N'] [IsScalarTower K L N']
    (hN : IsGarlingNormalClosure K L N)
    (hN' : IsGarlingNormalClosure K L N') :
    ∃ j : N ≃+* N', ∀ l : L, j (algebraMap L N l) = algebraMap L N' l := by
  obtain ⟨j, hj_bij, hj_comm⟩ := exercise_9_4 hN hN'
  exact ⟨RingEquiv.ofBijective j hj_bij, hj_comm⟩

/-- `AlgEquiv` (`N ≃ₐ[L] N'`) companion to **Exercise 9.4** (§9.2, printed p. 81). -/
theorem exercise_9_4_algEquiv {K : Type u} {L : Type v} {N : Type w} {N' : Type*}
    [Field K] [Field L] [Field N] [Field N']
    [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
    [Algebra L N'] [Algebra K N'] [IsScalarTower K L N']
    (hN : IsGarlingNormalClosure K L N)
    (hN' : IsGarlingNormalClosure K L N') :
    Nonempty (N ≃ₐ[L] N') := by
  obtain ⟨j, hj_comm⟩ := exercise_9_4_ringEquiv hN hN'
  exact ⟨AlgEquiv.ofRingEquiv (f := j) hj_comm⟩

/-- `FieldExtensionTriple` companion to **Exercise 9.4** (§9.2, printed p. 81; §4.2, p. 40):
for any extension `(i_KL, K, L)` and any two normal closures `(i_LN, L, N)` and `(i_LN', L, N')`,
there is a ring isomorphism `j : N ≃+* N'` satisfying `j (i_LN l) = i_LN' l` for all `l ∈ L`. -/
theorem exercise_9_4_triple {K : Type u} {L : Type v} {N : Type w} {N' : Type*}
    [Field K] [Field L] [Field N] [Field N']
    (eKL : FieldExtensionTriple K L)
    (eLN : FieldExtensionTriple L N) (eLN' : FieldExtensionTriple L N')
    (hN : IsGarlingNormalClosureTriple eKL eLN)
    (hN' : IsGarlingNormalClosureTriple eKL eLN') :
    ∃ j : N ≃+* N', ∀ l : L, j (eLN.hom l) = eLN'.hom l := by
  let _ : Algebra K L := eKL.hom.toAlgebra
  let _ : Algebra L N := eLN.hom.toAlgebra
  let _ : Algebra K N := (eLN.hom.comp eKL.hom).toAlgebra
  have _ : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra L N' := eLN'.hom.toAlgebra
  let _ : Algebra K N' := (eLN'.hom.comp eKL.hom).toAlgebra
  have _ : IsScalarTower K L N' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exercise_9_4_ringEquiv hN hN'

/-- **Exercise 9.5** (§9.2, printed p. 81 / PDF p. 89):
*"Suppose that `L : K` is a finite normal extension and that `f` is an irreducible polynomial in
`K[x]`. Suppose that `g` and `h` are irreducible monic factors of `f` in `L[x]`. Show that there is
an automorphism `σ` of `L` which fixes `K` such that `σ(g) = h`."*

Proved in full generality (characteristic-free, whether or not `f` is monic or has roots in `L`) via
`Corollary 1` to `Theorem 9.1`, `Theorem 7.3`, `Corollary 1` to `Theorem 7.4`, `Corollary 1` to
`Theorem 7.5`, and `Theorem 9.2`. -/
theorem exercise_9_5 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (hnorm : IsGarlingNormal K L)
    {f : K[X]} (hf : Irreducible f)
    {g h : L[X]} (hg_irr : Irreducible g) (hg_monic : g.Monic) (hg_dvd : g ∣ f.map (algebraMap K L))
    (hh_irr : Irreducible h) (hh_monic : h.Monic) (hh_dvd : h ∣ f.map (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, garlingMapPoly σ.toRingHom g = h := by
  classical
  -- 1. Express `L : K` as a splitting field extension for a non-zero `p ∈ K[X]`.
  obtain ⟨p₀, hsf_p₀⟩ := (corollary_1_to_theorem_9_1 hfin).mp hnorm
  let p : K[X] := if p₀ = 0 then 1 else p₀
  have hp0 : p ≠ 0 := by
    by_cases h0 : p₀ = 0 <;> simp [p, h0]
  have hsf_p : IsGarlingSplittingFieldExtension K L p := by
    by_cases h0 : p₀ = 0
    · simp only [p, h0, ↓reduceIte]
      have htop : (⊥ : IntermediateField K L) = ⊤ :=
        (isGarlingSplittingFieldExtension_zero_iff K L).mp (h0 ▸ hsf_p₀)
      refine ⟨⟨0, 1, Fin.elim0, by simp [GarlingSplitsExplicit]⟩, fun M hMne _ => hMne ?_⟩
      exact top_unique (htop ▸ bot_le)
    · simpa [p, h0] using hsf_p₀
  -- 2. Construct a splitting field `E : L` for `P = f * p ∈ K[X]` via Theorem 7.3.
  let P : K[X] := f * p
  have hP0 : P ≠ 0 := mul_ne_zero hf.ne_zero hp0
  let PL : L[X] := P.map (algebraMap K L)
  obtain ⟨E, instFieldE, instAlgLE, hsfLE, _⟩ := theorem_7_3_natDegree PL
  let _ : Field E := instFieldE
  let _ : Algebra L E := instAlgLE
  let _ : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Show `E : K` is a splitting field extension for `P`, hence finite and normal over `K`.
  have hsfKE : IsGarlingSplittingFieldExtension K E P := by
    have hP_spE : GarlingSplitsOver K E P := by
      rw [garlingSplitsOver_iff_splits, IsScalarTower.algebraMap_eq K L E, ← Polynomial.map_map]
      exact (garlingSplitsOver_iff_splits L E PL).mp hsfLE.1
    refine ⟨hP_spE, fun M₀ hM₀_ne hspM₀ => hM₀_ne ?_⟩
    have hp_spM₀ : GarlingSplitsOver K M₀ p :=
      ((garlingSplitsOver_mul_iff hf.ne_zero hp0).mp hspM₀).2
    -- Since `p` splits over `L` and over `M₀`, all roots of `p` in `L` map into `M₀`, so `L ⊆ M₀`.
    let iLE : L →ₐ[K] E := IsScalarTower.toAlgHom K L E
    let M₀_L : IntermediateField K L := M₀.comap iLE
    obtain ⟨np, cp, rp, hexp_pL⟩ := hsf_p.1
    have hrp_roots : Set.range rp = p.rootSet L :=
      (garlingSplitsExplicit_props hp0 hexp_pL).2.2.2
    have hsp_M₀_L : GarlingSplitsOver K M₀_L p := by
      refine (garlingSplitsOver_intermediateField_iff M₀_L p).mpr ⟨np, cp, rp, fun j => ?_, hexp_pL⟩
      have hmemL : rp j ∈ p.rootSet L := hrp_roots ▸ ⟨j, rfl⟩
      have haevE : Polynomial.aeval (iLE (rp j)) p = 0 := by
        rw [Polynomial.aeval_algHom_apply, (Polynomial.mem_rootSet.mp hmemL).2, map_zero]
      exact mem_of_garlingSplitsOver_intermediateField hp0 hp_spM₀ haevE
    have hM₀_L_top : M₀_L = ⊤ := by
      by_contra hne
      exact hsf_p.2 M₀_L hne hsp_M₀_L
    have hL_in_M₀ : ∀ l : L, algebraMap L E l ∈ M₀ := fun l => by
      have hl : l ∈ M₀_L := hM₀_L_top ▸ IntermediateField.mem_top
      exact hl
    let M₀_over_L : IntermediateField L E :=
      { M₀.toSubfield with algebraMap_mem' := hL_in_M₀ }
    have hPL_sp : GarlingSplitsOver L M₀_over_L PL := by
      rw [garlingSplitsOver_iff_splits]
      have hmap : PL.map (algebraMap L M₀_over_L) = P.map (algebraMap K M₀) := by
        dsimp [PL]; rw [Polynomial.map_map]; rfl
      rw [hmap]
      exact (garlingSplitsOver_iff_splits K M₀ P).mp hspM₀
    have htop_L : M₀_over_L = ⊤ := by
      by_contra hne
      exact hsfLE.2 M₀_over_L hne hPL_sp
    ext z
    simp only [IntermediateField.mem_top, iff_true]
    have hz : z ∈ M₀_over_L := htop_L ▸ IntermediateField.mem_top
    exact hz
  have hfinKE : IsFiniteExtension K E := (corollary_to_theorem_7_1 hsfKE).1
  have hnormKE : IsGarlingNormal K E :=
    (corollary_1_to_theorem_9_1 hfinKE).mpr ⟨P, hsfKE⟩
  -- 3. `g` and `h` divide `PL`, so both split over `E`; pick roots `α, β ∈ E` of `g, h`.
  have hPL_ne0 : PL ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hP0
  have hPL_splits : (PL.map (algebraMap L E)).Splits :=
    (garlingSplitsOver_iff_splits L E PL).mp hsfLE.1
  have hfL_dvd_PL : f.map (algebraMap K L) ∣ PL := by
    dsimp [PL, P]
    rw [Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hg_spE : GarlingSplitsOver L E g := by
    rw [garlingSplitsOver_iff_splits]
    exact hPL_splits.of_dvd
      ((Polynomial.map_ne_zero_iff (algebraMap L E).injective).mpr hPL_ne0)
      (Polynomial.map_dvd (algebraMap L E) (hg_dvd.trans hfL_dvd_PL))
  have hh_spE : GarlingSplitsOver L E h := by
    rw [garlingSplitsOver_iff_splits]
    exact hPL_splits.of_dvd
      ((Polynomial.map_ne_zero_iff (algebraMap L E).injective).mpr hPL_ne0)
      (Polynomial.map_dvd (algebraMap L E) (hh_dvd.trans hfL_dvd_PL))
  obtain ⟨ng, cg, αg, hexp_g⟩ := hg_spE
  obtain ⟨_, _, hng_deg, hαg_roots⟩ := garlingSplitsExplicit_props hg_irr.ne_zero hexp_g
  have hng_pos : 0 < ng := by
    rw [hng_deg, garlingDegree]
    exact natDegree_pos_of_irreducible hg_irr
  let α : E := αg ⟨0, hng_pos⟩
  have hα_root_g : Polynomial.aeval α g = 0 :=
    (Polynomial.mem_rootSet.mp (hαg_roots ▸ ⟨⟨0, hng_pos⟩, rfl⟩)).2
  obtain ⟨nh, ch, βh, hexp_h⟩ := hh_spE
  obtain ⟨_, _, hnh_deg, hβh_roots⟩ := garlingSplitsExplicit_props hh_irr.ne_zero hexp_h
  have hnh_pos : 0 < nh := by
    rw [hnh_deg, garlingDegree]
    exact natDegree_pos_of_irreducible hh_irr
  let β : E := βh ⟨0, hnh_pos⟩
  have hβ_root_h : Polynomial.aeval β h = 0 :=
    (Polynomial.mem_rootSet.mp (hβh_roots ▸ ⟨⟨0, hnh_pos⟩, rfl⟩)).2
  have hminL_α : minpoly L α = g :=
    (minpoly.eq_of_irreducible_of_monic hg_irr hα_root_g hg_monic).symm
  have hminL_β : minpoly L β = h :=
    (minpoly.eq_of_irreducible_of_monic hh_irr hβ_root_h hh_monic).symm
  -- 4. Both `α` and `β` have minimal polynomial `C f.leadingCoeff⁻¹ * f` over `K`.
  have hα_root_f : Polynomial.aeval α f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap L α f]
    obtain ⟨qg, hqg⟩ := hg_dvd
    rw [hqg, map_mul, hα_root_g, zero_mul]
  have hβ_root_f : Polynomial.aeval β f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap L β f]
    obtain ⟨qh, hqh⟩ := hh_dvd
    rw [hqh, map_mul, hβ_root_h, zero_mul]
  let f₀ : K[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hlc_ne0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf.ne_zero
  have hf₀_monic : f₀.Monic := by
    dsimp [f₀]
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc_ne0]
  have hf₀_irr : Irreducible f₀ := by
    have hunit : IsUnit (Polynomial.C f.leadingCoeff⁻¹ : K[X]) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc_ne0)).map Polynomial.C
    exact (associated_unit_mul_left f _ hunit).symm.irreducible hf
  have hα_root_f₀ : Polynomial.aeval α f₀ = 0 := by
    dsimp [f₀]; rw [map_mul, hα_root_f, mul_zero]
  have hβ_root_f₀ : Polynomial.aeval β f₀ = 0 := by
    dsimp [f₀]; rw [map_mul, hβ_root_f, mul_zero]
  have hminK_α : minpoly K α = f₀ :=
    (minpoly.eq_of_irreducible_of_monic hf₀_irr hα_root_f₀ hf₀_monic).symm
  have hminK_β : minpoly K β = f₀ :=
    (minpoly.eq_of_irreducible_of_monic hf₀_irr hβ_root_f₀ hf₀_monic).symm
  -- 5. By Corollary 1 to Theorem 7.4 and Corollary 1 to Theorem 7.5, obtain `τ : E ≃ₐ[K] E`
  -- sending `α ↦ β`.
  let Kα : IntermediateField K E := IntermediateField.adjoin K ({α} : Set E)
  let Kβ : IntermediateField K E := IntermediateField.adjoin K ({β} : Set E)
  let genα : Kα := IntermediateField.AdjoinSimple.gen K α
  let genβ : Kβ := IntermediateField.AdjoinSimple.gen K β
  have hadj_α : IntermediateField.adjoin K ({genα} : Set Kα) = ⊤ := by
    ext x; simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K E := (IntermediateField.adjoin K ({genα} : Set Kα)).map Kα.val
    have hmem : α ∈ L0 := ⟨genα, IntermediateField.mem_adjoin_simple_self K genα, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
    exact (Kα.val.injective hyx) ▸ hy
  have hadj_β : IntermediateField.adjoin K ({genβ} : Set Kβ) = ⊤ := by
    ext x; simp only [IntermediateField.mem_top, iff_true]
    let L0 : IntermediateField K E := (IntermediateField.adjoin K ({genβ} : Set Kβ)).map Kβ.val
    have hmem : β ∈ L0 := ⟨genβ, IntermediateField.mem_adjoin_simple_self K genβ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hmem)) x.2
    exact (Kβ.val.injective hyx) ▸ hy
  have hgenα_alg : IsGarlingAlgebraic K genα :=
    ⟨f₀, hf₀_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kα.val genα f₀).symm.trans hα_root_f₀)⟩
  have hgenβ_alg : IsGarlingAlgebraic K genβ :=
    ⟨f₀, hf₀_irr.ne_zero, Subtype.ext ((Polynomial.aeval_algHom_apply Kβ.val genβ f₀).symm.trans hβ_root_f₀)⟩
  have hmin_genα : minpoly K genα = f₀ :=
    (minpoly.algHom_eq Kα.val Kα.val.injective genα).symm.trans hminK_α
  have hmin_genβ : minpoly K genβ = f₀ :=
    (minpoly.algHom_eq Kβ.val Kβ.val.injective genβ).symm.trans hminK_β
  have hm_map :
      garlingMapPoly (RingEquiv.refl K).toRingHom (minpoly K genα) = minpoly K genβ := by
    simp [hmin_genα, hmin_genβ]
  obtain ⟨τ₀, ⟨hτ₀_gen, hτ₀_fix⟩, _⟩ :=
    (corollary_1_to_theorem_7_4_equiv hadj_α hgenα_alg hadj_β hgenβ_alg (RingEquiv.refl K)).2 hm_map
  let Pα : Kα[X] := P.map (algebraMap K Kα)
  let Pβ : Kβ[X] := P.map (algebraMap K Kβ)
  have hτ₀_Pα : garlingMapPoly τ₀.toRingHom Pα = Pβ := by
    have hcomp : τ₀.toRingHom.comp (algebraMap K Kα) = algebraMap K Kβ :=
      RingHom.ext fun k => by simpa using hτ₀_fix k
    change (P.map (algebraMap K Kα)).map τ₀.toRingHom = P.map (algebraMap K Kβ)
    rw [Polynomial.map_map, hcomp]
  have hsf_KαE : IsGarlingSplittingFieldExtension Kα E Pα := by
    refine ⟨?_, fun N hNne hspN => hNne ?_⟩
    · rw [garlingSplitsOver_iff_splits]
      have hmap : Pα.map (algebraMap Kα E) = P.map (algebraMap K E) := by
        dsimp [Pα]; rw [Polynomial.map_map]; rfl
      rw [hmap]
      exact (garlingSplitsOver_iff_splits K E P).mp hsfKE.1
    · let NK : IntermediateField K E := N.restrictScalars K
      have hspNK : GarlingSplitsOver K NK P := by
        rw [garlingSplitsOver_iff_splits]
        have hmap : P.map (algebraMap K NK) = Pα.map (algebraMap Kα N) := by
          dsimp [Pα]; rw [Polynomial.map_map]; rfl
        rw [hmap]
        exact (garlingSplitsOver_iff_splits Kα N Pα).mp hspN
      have hNK_top : NK = ⊤ := by
        by_contra hne
        exact hsfKE.2 NK hne hspNK
      ext z; simp only [IntermediateField.mem_top, iff_true]
      have hz : z ∈ NK := hNK_top ▸ IntermediateField.mem_top
      exact hz
  have hsf_KβE : IsGarlingSplittingFieldExtension Kβ E (garlingMapPoly τ₀.toRingHom Pα) := by
    rw [hτ₀_Pα]
    refine ⟨?_, fun N hNne hspN => hNne ?_⟩
    · rw [garlingSplitsOver_iff_splits]
      have hmap : Pβ.map (algebraMap Kβ E) = P.map (algebraMap K E) := by
        dsimp [Pβ]; rw [Polynomial.map_map]; rfl
      rw [hmap]
      exact (garlingSplitsOver_iff_splits K E P).mp hsfKE.1
    · let NK : IntermediateField K E := N.restrictScalars K
      have hspNK : GarlingSplitsOver K NK P := by
        rw [garlingSplitsOver_iff_splits]
        have hmap : P.map (algebraMap K NK) = Pβ.map (algebraMap Kβ N) := by
          dsimp [Pβ]; rw [Polynomial.map_map]; rfl
        rw [hmap]
        exact (garlingSplitsOver_iff_splits Kβ N Pβ).mp hspN
      have hNK_top : NK = ⊤ := by
        by_contra hne
        exact hsfKE.2 NK hne hspNK
      ext z; simp only [IntermediateField.mem_top, iff_true]
      have hz : z ∈ NK := hNK_top ▸ IntermediateField.mem_top
      exact hz
  have hτ₀_iso : IsRingIsomorphism τ₀.toRingHom := τ₀.bijective
  obtain ⟨τ₁, hτ₁_iso, hτ₁_ext⟩ :=
    corollary_1_to_theorem_7_5 hτ₀_iso Pα hsf_KαE hsf_KβE
  let τEquiv : E ≃+* E := RingEquiv.ofBijective τ₁ hτ₁_iso
  have hτ_fixK : ∀ k : K, τEquiv (algebraMap K E k) = algebraMap K E k := by
    intro k
    have hk : algebraMap K E k = algebraMap Kα E (algebraMap K Kα k) := rfl
    rw [hk]
    change τ₁ (algebraMap Kα E (algebraMap K Kα k)) = algebraMap K E k
    rw [hτ₁_ext (algebraMap K Kα k)]
    have h1 : τ₀.toRingHom (algebraMap K Kα k) = algebraMap K Kβ k := by simpa using hτ₀_fix k
    rw [h1]
    rfl
  let τ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τEquiv) hτ_fixK
  have hτα : τ α = β := by
    have hα_val : α = algebraMap Kα E genα := rfl
    rw [hα_val]
    change τ₁ (algebraMap Kα E genα) = β
    have hτ₀_g : τ₀.toRingHom genα = genβ := hτ₀_gen
    rw [hτ₁_ext genα, hτ₀_g]
    rfl
  -- 6. By Theorem 9.2 `(i) ⟹ (iii)`, `τ` restricts to `σ : L ≃ₐ[K] L`, and `σ(g) = h`.
  let iLE : L →ₐ[K] E := IsScalarTower.toAlgHom K L E
  let LE : IntermediateField K E := iLE.fieldRange
  let eLE : L ≃ₐ[K] LE := AlgEquiv.ofInjectiveField iLE
  have hLE_norm : IsGarlingNormal K LE := (isGarlingNormal_congr eLE).mp hnorm
  have hτ_LE : (τ : E → E) '' (LE : Set E) = (LE : Set E) :=
    (theorem_9_2 hfinKE hnormKE LE).2.2.mp hLE_norm τ
  let restrictLE : LE →ₐ[K] LE :=
    { toFun := fun x => ⟨τ x.1, by
        have hmem : τ x.1 ∈ (τ : E → E) '' (LE : Set E) := ⟨x.1, x.2, rfl⟩
        rwa [hτ_LE] at hmem⟩
      map_one' := Subtype.ext τ.map_one
      map_mul' := fun x y => Subtype.ext (τ.map_mul x.1 y.1)
      map_zero' := Subtype.ext τ.map_zero
      map_add' := fun x y => Subtype.ext (τ.map_add x.1 y.1)
      commutes' := fun k => Subtype.ext (τ.commutes k) }
  have hrest_bij : Function.Bijective restrictLE := by
    refine ⟨fun x y hxy => Subtype.ext (τ.injective (congrArg Subtype.val hxy)), fun y => ?_⟩
    have hy : y.1 ∈ (LE : Set E) := y.2
    rw [← hτ_LE] at hy
    obtain ⟨x, hxLE, hτx⟩ := hy
    exact ⟨⟨x, hxLE⟩, Subtype.ext hτx⟩
  let σ : L ≃ₐ[K] L :=
    (eLE.trans (AlgEquiv.ofBijective restrictLE hrest_bij)).trans eLE.symm
  have hσ_comm : ∀ x : L, algebraMap L E (σ x) = τ (algebraMap L E x) := by
    intro x
    have h1 : eLE (σ x) = AlgEquiv.ofBijective restrictLE hrest_bij (eLE x) := by
      simp [σ]
    exact congrArg Subtype.val h1
  refine ⟨σ, ?_⟩
  let g' : L[X] := garlingMapPoly σ.toRingHom g
  have hg'_monic : g'.Monic := hg_monic.map σ.toRingHom
  have hg'_irr : Irreducible g' := by
    have heq : g' = Polynomial.mapEquiv σ.toRingEquiv g := rfl
    rw [heq]
    exact hg_irr.map (Polynomial.mapEquiv σ.toRingEquiv)
  have hg'_β : Polynomial.aeval β g' = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hmap : g'.map (algebraMap L E) = g.map (τ.toRingHom.comp (algebraMap L E)) := by
      dsimp [g', garlingMapPoly]
      rw [Polynomial.map_map]
      congr 1
      ext x
      exact hσ_comm x
    have hτα' : τ.toRingHom α = β := hτα
    rw [hmap, Polynomial.eval_map, ← hτα', ← Polynomial.hom_eval₂ g (algebraMap L E) τ.toRingHom α,
      ← Polynomial.aeval_def, hα_root_g, map_zero]
  exact (minpoly.eq_of_irreducible_of_monic hg'_irr hg'_β hg'_monic).trans hminL_β

/-- Chapter 3/4 vocabulary (`IsGarlingIrreducible`, `IsFieldAutomorphism`, `FixesBaseField`)
companion to **Exercise 9.5** (§9.2, printed p. 81). -/
theorem exercise_9_5_garling {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hfin : IsFiniteExtension K L) (hnorm : IsGarlingNormal K L)
    {f : K[X]} (hf : IsGarlingIrreducible f)
    {g h : L[X]} (hg_irr : IsGarlingIrreducible g) (hg_monic : g.Monic)
    (hg_dvd : g ∣ f.map (algebraMap K L))
    (hh_irr : IsGarlingIrreducible h) (hh_monic : h.Monic)
    (hh_dvd : h ∣ f.map (algebraMap K L)) :
    ∃ σ : L →+* L,
      IsFieldAutomorphism σ ∧ FixesBaseField K σ ∧ garlingMapPoly σ g = h := by
  obtain ⟨σ, hσ⟩ := exercise_9_5 hfin hnorm
    ((isGarlingIrreducible_iff f).mp hf)
    ((isGarlingIrreducible_iff g).mp hg_irr) hg_monic hg_dvd
    ((isGarlingIrreducible_iff h).mp hh_irr) hh_monic hh_dvd
  exact ⟨σ.toRingHom, σ.bijective, σ.commutes, hσ⟩

/-- **Exercise 9.6** (§9.2, printed p. 81 / PDF p. 89 — note that OCR `garling1986_pages.txt`
strips the overbar on `L̄`, verified on the 200 DPI render `page-089.png`):
*"Suppose that `L : K` is algebraic. Show that the following are equivalent:
(i) `L : K` is normal;
(ii) if `j` is any monomorphism from `L` to `L̄` which fixes `K` then `j(L) ⊆ L`;
(iii) if `j` is any monomorphism from `L` to `L̄` which fixes `K` then `j(L) = L`."*

Proved across arbitrary universes `{K : Type u} {L : Type v} {LBar : Type w}` for **any** algebraic
closure `LBar : L` (`IsGarlingAlgebraicClosure L LBar`), using `Theorem 4.8` for `(ii) ⟹ (iii)` and
`Theorem 7.4` + `Theorem 8.3` for `(iii) ⟹ (i)`. -/
theorem exercise_9_6 {K : Type u} {L : Type v} {LBar : Type w}
    [Field K] [Field L] [Field LBar]
    [Algebra K L] [Algebra L LBar] [Algebra K LBar] [IsScalarTower K L LBar]
    (halg : IsAlgebraicExtension K L)
    (hcl : IsGarlingAlgebraicClosure L LBar) :
    (IsGarlingNormal K L ↔
      ∀ j : L →ₐ[K] LBar, Set.range j ⊆ Set.range (algebraMap L LBar)) ∧
    ((∀ j : L →ₐ[K] LBar, Set.range j ⊆ Set.range (algebraMap L LBar)) ↔
      ∀ j : L →ₐ[K] LBar, Set.range j = Set.range (algebraMap L LBar)) ∧
    (IsGarlingNormal K L ↔
      ∀ j : L →ₐ[K] LBar, Set.range j = Set.range (algebraMap L LBar)) := by
  -- `(i) ⟹ (ii)`:
  have h12 :
      IsGarlingNormal K L →
        ∀ j : L →ₐ[K] LBar, Set.range j ⊆ Set.range (algebraMap L LBar) := by
    intro hnorm j
    rintro _ ⟨α, rfl⟩
    obtain ⟨_, hmin⟩ := (isGarlingNormal_iff_minpoly_splits K L).mp hnorm
    have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp (halg α)
    let m : K[X] := minpoly K α
    obtain ⟨n, c, β, hexp⟩ := hmin α
    obtain ⟨hc_eq, _, _, _⟩ := garlingSplitsExplicit_props (minpoly.ne_zero hα_int) hexp
    have hc1 : c = 1 := hc_eq.trans (minpoly.monic hα_int).leadingCoeff
    have hmap_LBar :
        (m.map (algebraMap K L)).map (algebraMap L LBar) = m.map (algebraMap K LBar) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L LBar]
    have hfac_LBar :
        m.map (algebraMap K LBar) =
          ∏ r : Fin n, (Polynomial.X - Polynomial.C (algebraMap L LBar (β r))) := by
      rw [← hmap_LBar, hexp, hc1]
      simp [Polynomial.map_prod]
    have hev0 : (m.map (algebraMap K LBar)).eval (j α) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply j α m,
        minpoly.aeval K α, map_zero]
    rw [hfac_LBar, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev0
    obtain ⟨r, _, hr⟩ := hev0
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hr
    exact ⟨β r, hr.symm⟩
  -- `(ii) ⟹ (iii)` via Theorem 4.8 (`theorem_4_8`):
  have h23 :
      (∀ j : L →ₐ[K] LBar, Set.range j ⊆ Set.range (algebraMap L LBar)) →
        ∀ j : L →ₐ[K] LBar, Set.range j = Set.range (algebraMap L LBar) := by
    intro h2 j
    have hsub := h2 j
    apply Set.Subset.antisymm hsub
    have hinj : Function.Injective (algebraMap L LBar) := (algebraMap L LBar).injective
    choose τfun hτfun using fun x : L => hsub ⟨x, rfl⟩
    let τ : L →+* L :=
      { toFun := τfun
        map_one' := hinj ((hτfun 1).trans (j.map_one.trans (algebraMap L LBar).map_one.symm))
        map_mul' := fun x y => hinj ((hτfun (x * y)).trans
          ((j.map_mul x y).trans ((congrArg₂ (· * ·) (hτfun x).symm (hτfun y).symm).trans
            ((algebraMap L LBar).map_mul _ _).symm)))
        map_zero' := hinj ((hτfun 0).trans (j.map_zero.trans (algebraMap L LBar).map_zero.symm))
        map_add' := fun x y => hinj ((hτfun (x + y)).trans
          ((j.map_add x y).trans ((congrArg₂ (· + ·) (hτfun x).symm (hτfun y).symm).trans
            ((algebraMap L LBar).map_add _ _).symm))) }
    have hτ_fix : FixesBaseField K τ := fun k => hinj <|
      (hτfun (algebraMap K L k)).trans
        ((j.commutes k).trans (IsScalarTower.algebraMap_apply K L LBar k))
    have hτ_surj : Function.Surjective τ := theorem_4_8 halg τ.injective hτ_fix
    rintro _ ⟨x, rfl⟩
    obtain ⟨x₀, rfl⟩ := hτ_surj x
    exact ⟨x₀, (hτfun x₀).symm⟩
  -- `(iii) ⟹ (i)` via Theorem 7.4 (`theorem_7_4_adjoin`) and Theorem 8.3 (`theorem_8_3`):
  have h31 :
      (∀ j : L →ₐ[K] LBar, Set.range j = Set.range (algebraMap L LBar)) →
        IsGarlingNormal K L := by
    intro h3
    rw [isGarlingNormal_iff_minpoly_splits]
    refine ⟨halg, fun α => ?_⟩
    have hα_alg : IsGarlingAlgebraic K α := halg α
    have hα_int : IsIntegral K α := (isGarlingAlgebraic_iff_isIntegral K α).mp hα_alg
    let m : K[X] := minpoly K α
    have hm_monic : m.Monic := minpoly.monic hα_int
    have hm_ne0 : m ≠ 0 := minpoly.ne_zero hα_int
    -- Since `LBar` is algebraically closed (`hcl.2`), `m` splits over `LBar`.
    have hm_spBar : GarlingSplitsOver K LBar m := by
      rw [garlingSplitsOver_iff_splits]
      have hcl' := (garlingSplitsOver_iff_splits LBar LBar (m.map (algebraMap K LBar))).mp
        (hcl.2 (m.map (algebraMap K LBar)))
      simpa [Algebra.algebraMap_self, Polynomial.map_id] using hcl'
    obtain ⟨n, c, γ, hexp_Bar⟩ := hm_spBar
    obtain ⟨hc_eq, _, _, hγ_roots⟩ := garlingSplitsExplicit_props hm_ne0 hexp_Bar
    have hc1 : c = 1 := hc_eq.trans hm_monic.leadingCoeff
    -- Show each root `γ r ∈ LBar` lies in `Set.range (algebraMap L LBar)`.
    have hγ_in_L : ∀ r : Fin n, γ r ∈ Set.range (algebraMap L LBar) := by
      intro r
      have hmem : γ r ∈ m.rootSet LBar := hγ_roots ▸ ⟨r, rfl⟩
      have hev : (garlingMapPoly (algebraMap K LBar) m).eval (γ r) = 0 := by
        rw [garlingMapPoly_apply, Polynomial.eval_map, ← Polynomial.aeval_def]
        exact (Polynomial.mem_rootSet.mp hmem).2
      obtain ⟨j₀, hj₀_mono, hj₀_gen, hj₀_fix⟩ :=
        (theorem_7_4_adjoin hα_alg (algebraMap K LBar).injective (γ r)).1.mpr hev
      let Kα : IntermediateField K L := IntermediateField.adjoin K ({α} : Set L)
      have halg_KαL : IsAlgebraicExtension Kα L :=
        (tower_algebraic_of_top_algebraic (K := K) (L := Kα) (F := L) halg).2
      obtain ⟨j, _, hj_ext⟩ := theorem_8_3 (L := L) hj₀_mono halg_KαL hcl.2
      have hj_fixK : ∀ k : K, j (algebraMap K L k) = algebraMap K LBar k := fun k => by
        have hk : algebraMap K L k = algebraMap Kα L (algebraMap K Kα k) := rfl
        rw [hk, hj_ext (algebraMap K Kα k), hj₀_fix k]
      let jAlg : L →ₐ[K] LBar := ⟨j, hj_fixK⟩
      have hjα : jAlg α = γ r := by
        have hα_val : α = algebraMap Kα L (IntermediateField.AdjoinSimple.gen K α) := rfl
        change j α = γ r
        rw [hα_val, hj_ext (IntermediateField.AdjoinSimple.gen K α), hj₀_gen]
      rw [← h3 jAlg]
      exact ⟨α, hjα⟩
    choose β hβ using hγ_in_L
    refine ⟨n, 1, β, ?_⟩
    unfold GarlingSplitsExplicit
    apply Polynomial.map_injective (algebraMap L LBar) (algebraMap L LBar).injective
    have hmap : (m.map (algebraMap K L)).map (algebraMap L LBar) = m.map (algebraMap K LBar) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L LBar]
    rw [hmap, hexp_Bar, hc1]
    simp [Polynomial.map_prod, hβ]
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h j => (h j).subset⟩, ⟨fun h => h23 (h12 h), h31⟩⟩

/-- Canonical `GarlingAlgClosure L` + `IsRingMonomorphism` specialization of **Exercise 9.6**
(§9.2, printed p. 81). -/
theorem exercise_9_6_garling {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (halg : IsAlgebraicExtension K L) :
    let LBar := GarlingAlgClosure L
    (IsGarlingNormal K L ↔
      ∀ j : L →+* LBar, IsRingMonomorphism j →
        (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
        Set.range j ⊆ Set.range (algebraMap L LBar)) ∧
    ((∀ j : L →+* LBar, IsRingMonomorphism j →
        (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
        Set.range j ⊆ Set.range (algebraMap L LBar)) ↔
      ∀ j : L →+* LBar, IsRingMonomorphism j →
        (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
        Set.range j = Set.range (algebraMap L LBar)) ∧
    (IsGarlingNormal K L ↔
      ∀ j : L →+* LBar, IsRingMonomorphism j →
        (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
        Set.range j = Set.range (algebraMap L LBar)) := by
  intro LBar
  obtain ⟨LBar₀, instField₀, instAlg₀, hcl₀⟩ := theorem_8_2 L
  let _ : Field LBar₀ := instField₀
  let _ : Algebra L LBar₀ := instAlg₀
  let _ : Algebra K LBar₀ := ((algebraMap L LBar₀).comp (algebraMap K L)).toAlgebra
  have _ : IsScalarTower K L LBar₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcl : IsGarlingAlgebraicClosure L LBar := garlingAlgClosure_isGarlingAlgebraicClosure L
  obtain ⟨eBar⟩ := theorem_8_4_algEquiv hcl hcl₀
  have h := exercise_9_6 (K := K) (L := L) (LBar := LBar₀) halg hcl₀
  have eSub :
      (∀ j : L →ₐ[K] LBar₀, Set.range j ⊆ Set.range (algebraMap L LBar₀)) ↔
        ∀ j : L →+* LBar, IsRingMonomorphism j →
          (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
          Set.range j ⊆ Set.range (algebraMap L LBar) := by
    constructor
    · intro H j _ hfix
      let j₀ : L →ₐ[K] LBar₀ :=
        { toRingHom := eBar.toRingHom.comp j
          commutes' := fun k => by
            change eBar (j (algebraMap K L k)) = algebraMap L LBar₀ (algebraMap K L k)
            rw [hfix k]
            exact eBar.commutes (algebraMap K L k) }
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := H j₀ ⟨x, rfl⟩
      refine ⟨y, eBar.injective ?_⟩
      rw [eBar.commutes y]
      exact hy
    · intro H j₀
      let j : L →+* LBar := eBar.symm.toRingHom.comp j₀.toRingHom
      have hfix : ∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k) := fun k => by
        change eBar.symm (j₀ (algebraMap K L k)) = algebraMap L LBar (algebraMap K L k)
        rw [j₀.commutes k]
        exact eBar.symm.commutes (algebraMap K L k)
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := H j j.injective hfix ⟨x, rfl⟩
      refine ⟨y, ?_⟩
      have h1 := congrArg eBar hy
      rw [eBar.commutes y] at h1
      simpa [j] using h1
  have eEq :
      (∀ j : L →ₐ[K] LBar₀, Set.range j = Set.range (algebraMap L LBar₀)) ↔
        ∀ j : L →+* LBar, IsRingMonomorphism j →
          (∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k)) →
          Set.range j = Set.range (algebraMap L LBar) := by
    constructor
    · intro H j _ hfix
      let j₀ : L →ₐ[K] LBar₀ :=
        { toRingHom := eBar.toRingHom.comp j
          commutes' := fun k => by
            change eBar (j (algebraMap K L k)) = algebraMap L LBar₀ (algebraMap K L k)
            rw [hfix k]
            exact eBar.commutes (algebraMap K L k) }
      have hj₀_eq := H j₀
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := hj₀_eq.subset ⟨x, rfl⟩
        exact ⟨y, eBar.injective ((eBar.commutes y).trans hy)⟩
      · rintro ⟨y, rfl⟩
        have hmem : algebraMap L LBar₀ y ∈ Set.range j₀ := hj₀_eq.symm ▸ ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := hmem
        exact ⟨x, eBar.injective (hx.trans (eBar.commutes y).symm)⟩
    · intro H j₀
      let j : L →+* LBar := eBar.symm.toRingHom.comp j₀.toRingHom
      have hfix : ∀ k : K, j (algebraMap K L k) = algebraMap L LBar (algebraMap K L k) := fun k => by
        change eBar.symm (j₀ (algebraMap K L k)) = algebraMap L LBar (algebraMap K L k)
        rw [j₀.commutes k]
        exact eBar.symm.commutes (algebraMap K L k)
      have hj_eq := H j j.injective hfix
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := hj_eq.subset ⟨x, rfl⟩
        have h1 := congrArg eBar hy
        rw [eBar.commutes y] at h1
        exact ⟨y, by simpa [j] using h1⟩
      · rintro ⟨y, rfl⟩
        have hmem : algebraMap L LBar y ∈ Set.range j := hj_eq.symm ▸ ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := hmem
        have h1 := congrArg eBar hx
        rw [eBar.commutes y] at h1
        exact ⟨x, by simpa [j] using h1⟩
  exact ⟨h.1.trans eSub, eSub.symm.trans (h.2.1.trans eEq), h.2.2.trans eEq⟩

/-- Ambient-subfield `L ⊆ L̄` (`L : IntermediateField K LBar`) companion to **Exercise 9.6**
(§9.2, printed p. 81), where `j(L) ⊆ L` and `j(L) = L` are literal subset inclusion and equality
in `LBar`. -/
theorem exercise_9_6_subfield {K : Type u} {LBar : Type v} [Field K] [Field LBar] [Algebra K LBar]
    (L : IntermediateField K LBar) (halg : IsAlgebraicExtension K L)
    (hcl : IsGarlingAlgebraicClosure L LBar) :
    (IsGarlingNormal K L ↔ ∀ j : L →ₐ[K] LBar, Set.range j ⊆ (L : Set LBar)) ∧
    ((∀ j : L →ₐ[K] LBar, Set.range j ⊆ (L : Set LBar)) ↔
      ∀ j : L →ₐ[K] LBar, Set.range j = (L : Set LBar)) ∧
    (IsGarlingNormal K L ↔ ∀ j : L →ₐ[K] LBar, Set.range j = (L : Set LBar)) := by
  have hrange : Set.range (algebraMap L LBar) = (L : Set LBar) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simpa only [hrange] using exercise_9_6 (K := K) (L := L) (LBar := LBar) halg hcl

/-- **Exercise 9.7** (§9.2, printed p. 81 / PDF p. 89):
*"Show that the condition that `L : K` is finite can be dropped from Theorem 9.2. (Use the previous
exercise and Theorem 8.3.)"*

Proved for **arbitrary** (possibly infinite, characteristic-free) normal extensions `L : K`
following Garling's parenthetical hint: uses `Exercise 9.6` on `L̄ = GarlingAlgClosure L` (which is
also an algebraic closure of `M` by Chapter 8's `exercise_8_8_tower_iff`) together with
`Theorem 8.3`. -/
theorem exercise_9_7 {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hnorm : IsGarlingNormal K L) (M : IntermediateField K L) :
    (IsGarlingNormal K M ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ∧
    ((∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) ∧
    (IsGarlingNormal K M ↔
      ∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) := by
  obtain ⟨h12, h23⟩ := normal_intermediateField_imp_aut_subset_and_eq M
  have h31 : (∀ σ : L ≃ₐ[K] L, (σ : L → L) '' (M : Set L) = (M : Set L)) → IsGarlingNormal K M := by
    intro h3
    obtain ⟨halgM, halgML⟩ := tower_algebraic_of_top_algebraic (K := K) (L := M) (F := L) hnorm.1
    obtain ⟨LBar, instFieldBar, instAlgLBar, hclL⟩ := theorem_8_2 L
    let _ : Field LBar := instFieldBar
    let _ : Algebra L LBar := instAlgLBar
    let _ : Algebra K LBar := ((algebraMap L LBar).comp (algebraMap K L)).toAlgebra
    have _ : IsScalarTower K L LBar := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- By Chapter 8 (`exercise_8_8_tower_iff`), `LBar` is also an algebraic closure of `M`.
    have hclM : IsGarlingAlgebraicClosure M LBar :=
      (exercise_8_8_tower_iff (K := M) (L := L) (M := LBar) halgML).mp hclL
    -- Apply Exercise 9.6 `(ii) ⟹ (i)` to `M : K` with algebraic closure `LBar : M`.
    refine (exercise_9_6 (K := K) (L := M) (LBar := LBar) halgM hclM).1.mpr ?_
    intro jM
    rintro _ ⟨xM, rfl⟩
    -- Extend `jM : M →+* LBar` to `j : L →+* LBar` via Theorem 8.3 (`theorem_8_3`).
    obtain ⟨j, _, hj_ext⟩ := theorem_8_3 (L := L) jM.injective halgML hclL.2
    have hj_fixK : ∀ k : K, j (algebraMap K L k) = algebraMap K LBar k := fun k => by
      have hk : algebraMap K L k = algebraMap M L (algebraMap K M k) := rfl
      rw [hk, hj_ext (algebraMap K M k)]
      exact jM.commutes k
    let jAlg : L →ₐ[K] LBar := ⟨j, hj_fixK⟩
    -- By Exercise 9.6 `(i) ⟹ (iii)` on `L : K`, `Set.range jAlg = Set.range (algebraMap L LBar)`.
    have hrange_eq : Set.range jAlg = Set.range (algebraMap L LBar) :=
      (exercise_9_6 (K := K) (L := L) (LBar := LBar) hnorm.1 hclL).2.2.mp hnorm jAlg
    have hinj : Function.Injective (algebraMap L LBar) := (algebraMap L LBar).injective
    choose σfun hσfun using fun y : L => hrange_eq.subset ⟨y, rfl⟩
    let σHom : L →ₐ[K] L :=
      { toFun := σfun
        map_one' := hinj ((hσfun 1).trans (jAlg.map_one.trans (algebraMap L LBar).map_one.symm))
        map_mul' := fun a b => hinj ((hσfun (a * b)).trans
          ((jAlg.map_mul a b).trans ((congrArg₂ (· * ·) (hσfun a).symm (hσfun b).symm).trans
            ((algebraMap L LBar).map_mul _ _).symm)))
        map_zero' := hinj ((hσfun 0).trans (jAlg.map_zero.trans (algebraMap L LBar).map_zero.symm))
        map_add' := fun a b => hinj ((hσfun (a + b)).trans
          ((jAlg.map_add a b).trans ((congrArg₂ (· + ·) (hσfun a).symm (hσfun b).symm).trans
            ((algebraMap L LBar).map_add _ _).symm)))
        commutes' := fun k => hinj <|
          (hσfun (algebraMap K L k)).trans
            ((jAlg.commutes k).trans (IsScalarTower.algebraMap_apply K L LBar k)) }
    have hσ_bij : Function.Bijective σHom := by
      refine ⟨σHom.toRingHom.injective, fun y => ?_⟩
      have hy : algebraMap L LBar y ∈ Set.range jAlg := hrange_eq.symm ▸ ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hy
      exact ⟨z, hinj ((hσfun z).trans hz)⟩
    let σ : L ≃ₐ[K] L := AlgEquiv.ofBijective σHom hσ_bij
    have hσx_mem : σ xM.1 ∈ M := by
      have hmem : σ xM.1 ∈ (σ : L → L) '' (M : Set L) := ⟨xM.1, xM.2, rfl⟩
      rwa [h3 σ] at hmem
    refine ⟨⟨σ xM.1, hσx_mem⟩, ?_⟩
    change algebraMap L LBar (σfun xM.1) = jM xM
    rw [hσfun xM.1]
    exact hj_ext xM
  exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, fun h σ => (h σ).subset⟩, ⟨fun h => h23 (h12 h), h31⟩⟩

/-- Chapter 4 vocabulary (`IsFieldAutomorphism` + `FixesBaseField`) companion to **Exercise 9.7**
(§9.2, printed p. 81). -/
theorem exercise_9_7_garling {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hnorm : IsGarlingNormal K L) (M : IntermediateField K L) :
    (IsGarlingNormal K M ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ∧
    ((∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) ⊆ (M : Set L)) ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) = (M : Set L)) ∧
    (IsGarlingNormal K M ↔
      ∀ σ : L →+* L, IsFieldAutomorphism σ → FixesBaseField K σ →
        (σ : L → L) '' (M : Set L) = (M : Set L)) := by
  have h := exercise_9_7 hnorm M
  have eSub := forall_algEquiv_iff_isFieldAutomorphism (K := K) (L := L)
    (fun f => f '' (M : Set L) ⊆ (M : Set L))
  have eEq := forall_algEquiv_iff_isFieldAutomorphism (K := K) (L := L)
    (fun f => f '' (M : Set L) = (M : Set L))
  exact ⟨h.1.trans eSub, eSub.symm.trans (h.2.1.trans eEq), h.2.2.trans eEq⟩

end Garling.Chapter09
